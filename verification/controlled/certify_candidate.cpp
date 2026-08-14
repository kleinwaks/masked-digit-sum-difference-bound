#include "pressure.hpp"

#include <cfloat>
#include <cfenv>
#include <filesystem>
#include <iostream>
#include <sstream>
#include <unordered_map>

using namespace pressure;
namespace {

double upmul(double a,double b){return std::nextafter(a*b,std::numeric_limits<double>::infinity());}
double upadd(double a,double b){return std::nextafter(a+b,std::numeric_limits<double>::infinity());}
double downmul(double a,double b){return std::nextafter(a*b,0.0);}

struct Config{Candidate c;int frontier=8,plus_depth=8192;double x=0;std::string xhex;};
Config read_config(const std::string&path){std::ifstream f(path);if(!f)throw std::runtime_error("cannot open candidate config");Config z;std::string key;while(f>>key){if(key=="version"){std::string v;f>>v;}else if(key=="B")f>>z.c.B;else if(key=="q")f>>z.c.q;else if(key=="frontier")f>>z.frontier;else if(key=="plus_depth")f>>z.plus_depth;else if(key=="x"){f>>z.xhex;z.x=std::stod(z.xhex);}else if(key=="generators"){int g;std::string line;std::getline(f,line);std::istringstream s(line);while(s>>g)z.c.gens.push_back(g);}else throw std::runtime_error("unknown config key "+key);}if(z.c.B<=0||z.c.q<=z.c.B||z.c.gens.empty()||!(z.x>0&&z.x<1))throw std::runtime_error("incomplete config");return z;}

struct UpPowers{double x;int limit;std::vector<double>small;std::unordered_map<int,double>large;UpPowers(double xx,int n):x(xx),limit(n),small(n){small[0]=1;for(int i=1;i<n;i++)small[i]=upmul(small[i-1],x);}double get(int n){if(n<limit)return small[n];auto it=large.find(n);if(it!=large.end())return it->second;double a=x,r=1;int k=n;while(k){if(k&1)r=upmul(r,a);k>>=1;if(k)a=upmul(a,a);}large[n]=r;return r;}};
struct DownPowers{double x;int limit;std::vector<double>small;DownPowers(double xx,int n):x(xx),limit(n),small(n){small[0]=1;for(int i=1;i<n;i++)small[i]=downmul(small[i-1],x);}double get(int n)const{if(n<limit)return small[n];double a=x,r=1;int k=n;while(k){if(k&1)r=downmul(r,a);k>>=1;if(k)a=downmul(a,a);}return r;}};

struct Scaled{double mant=0;long long exponent=0;};
Scaled plus_upper(const Data&D,double x,int K){UpPowers pw(x,4*D.B+D.Q+10);std::unordered_map<int,std::vector<std::pair<int,double>>>kernel;kernel.reserve(2*K+8);auto row_for=[&](int st)->const std::vector<std::pair<int,double>>&{auto found=kernel.find(st);if(found!=kernel.end())return found->second;std::map<int,double>agg;for(int y=0;y<D.Q;y++){int inc,ns;if(!plus_transition(D,st,y,inc,ns))continue;double z=pw.get(inc);auto it=agg.find(ns);if(it==agg.end())agg[ns]=z;else it->second=upadd(it->second,z);}std::vector<std::pair<int,double>>edges(agg.begin(),agg.end());return kernel.emplace(st,std::move(edges)).first->second;};std::map<int,double>cur,nxt;cur[NEG_INF]=1;long long exponent=0;
  for(int k=0;k<K;k++){nxt.clear();for(auto [st,w]:cur)for(auto [ns,tw]:row_for(st)){double z=upmul(w,tw);auto it=nxt.find(ns);if(it==nxt.end())nxt[ns]=z;else it->second=upadd(it->second,z);}double high=0;for(auto [st,w]:nxt)high=std::max(high,w);if(!(high>0))throw std::runtime_error("empty plus DP");int e=0;std::frexp(high,&e);for(auto&it:nxt)it.second=std::nextafter(std::ldexp(it.second,-e),std::numeric_limits<double>::infinity());exponent+=e;cur.swap(nxt);if((k+1)%512==0)std::cout<<"plus_cert_depth="<<(k+1)<<'/'<<K<<" states="<<cur.size()<<'\n';}
  double row=0;for(auto [st,w]:cur){int c1,c0;plus_norm(st,c1,c0);if(c0<INF)row=upadd(row,upmul(w,pw.get(c0)));if(c1<INF)row=upadd(row,upmul(w,pw.get(c1)));}int e=0;double mant=std::frexp(row,&e);return {std::nextafter(mant,std::numeric_limits<double>::infinity()),exponent+e};
}

Scaled decimal_power_lower(long long numerator,long long scale,int K){double exactish=(double)numerator/(double)scale;double p=std::nextafter(exactish,0.0),mant=1;long long exponent=0;for(int k=0;k<K;k++){mant=downmul(mant,p);int e=0;double m=std::frexp(mant,&e);mant=std::nextafter(m,0.0);exponent+=e;}return {mant,exponent};}
bool less_scaled(const Scaled&a,const Scaled&b){return a.exponent!=b.exponent?a.exponent<b.exponent:a.mant<b.mant;}

double difference_raw(const Data&D,const std::vector<int>&states,const std::vector<int>&idx,const std::vector<double>&v,double x){DownPowers pw(x,D.max_state+2*D.B+10);double raw=1e300;
#pragma omp parallel for schedule(static) reduction(min:raw)
  for(int i=0;i<(int)states.size();i++){double y=0;for(int r=0;r<D.Q;r++){int a,n;if(!diff_transition(D,states[i],r,a,n))continue;int z=D.slot(n);if(z<0||z>=D.slots)continue;int j=idx[z];if(j>=0)y+=pw.get(a)*v[j];}raw=std::min(raw,y/v[i]);}return raw;
}

bool verify_difference(const Data&D,const std::vector<int>&states,const std::vector<int>&idx,const std::vector<double>&v,double x,long long cnum,long long scale,double gamma){DownPowers pw(x,D.max_state+2*D.B+10);double cbin=std::nextafter((double)cnum/(double)scale,std::numeric_limits<double>::infinity());std::atomic<bool>pass{true};
#pragma omp parallel for schedule(static)
  for(int i=0;i<(int)states.size();i++){double y=0;for(int r=0;r<D.Q;r++){int a,n;if(!diff_transition(D,states[i],r,a,n))continue;int z=D.slot(n);if(z<0||z>=D.slots)continue;int j=idx[z];if(j>=0)y+=pw.get(a)*v[j];}double rhs=std::nextafter(cbin*v[i],std::numeric_limits<double>::infinity());rhs=std::nextafter(rhs*(1+gamma),std::numeric_limits<double>::infinity());if(!(y>rhs))pass=false;}return pass;
}

} // namespace

int main(int argc,char**argv){try{std::cout.setf(std::ios::unitbuf);if(argc<4||argc>5){std::cerr<<"usage: certify_candidate CANDIDATE.cfg PF_VECTOR.hex CONSTANTS.json [THREADS]\n";return 2;}static_assert(std::numeric_limits<double>::is_iec559,"binary64 required");static_assert(FLT_EVAL_METHOD==0,"excess-precision evaluation is unsupported");if(std::fegetround()!=FE_TONEAREST)throw std::runtime_error("round-to-nearest mode required");int threads=argc==5?std::stoi(argv[4]):20;omp_set_num_threads(threads);Config cfg=read_config(argv[1]);Data d(cfg.c);auto states=frontier(d,cfg.frontier,false);auto idx=make_index(d,states);std::ifstream f(argv[2]);if(!f)throw std::runtime_error("cannot open PF vector");std::vector<double>v;v.reserve(states.size());for(int expected:states){int st;std::string word;if(!(f>>st>>word)||st!=expected)throw std::runtime_error("PF vector state mismatch");double z=std::stod(word);if(!(z>0&&std::isfinite(z)))throw std::runtime_error("invalid PF entry");v.push_back(z);}std::string extra;if(f>>extra)throw std::runtime_error("extra PF data");
  constexpr long long SCALE=1000000;double eps=std::numeric_limits<double>::epsilon(),gamma=4.0*d.Q*eps;double raw=difference_raw(d,states,idx,v,cfg.x);long long cnum=(long long)std::floor(raw/(1+gamma)*SCALE)-2;while(!verify_difference(d,states,idx,v,cfg.x,cnum,SCALE,gamma))cnum--;
  Scaled row=plus_upper(d,cfg.x,cfg.plus_depth);long double logrow=std::log((long double)row.mant)+(long double)row.exponent*std::log(2.0L);long double root=std::exp(logrow/cfg.plus_depth);long long pnum=(long long)std::ceil(root*SCALE)+2;while(!less_scaled(row,decimal_power_lower(pnum,SCALE,cfg.plus_depth)))pnum++;
  long double residual=std::log(2.0L)/(cfg.plus_depth*std::log((long double)d.Q));std::ofstream out(argv[3]);if(!out)throw std::runtime_error("cannot write constants");out<<"{\n  \"version\": \"final-carry-certificate-0.1.0\",\n  \"B\": "<<d.B<<", \"q\": "<<d.Q<<",\n  \"x_hex\": \""<<cfg.xhex<<"\",\n  \"frontier\": "<<cfg.frontier<<", \"states\": "<<states.size()<<",\n  \"plus_depth\": "<<cfg.plus_depth<<",\n  \"scale\": "<<SCALE<<",\n  \"difference_lower_num\": "<<cnum<<",\n  \"plus_upper_num\": "<<pnum<<",\n  \"sum_pressure_theta_uncertainty_at_most\": "<<std::setprecision(17)<<(double)residual<<"\n}\n";
  std::cout<<std::setprecision(17)<<"CERTIFIED difference_rho>"<<(double)cnum/SCALE<<" plus_pressure<log("<<(double)pnum/SCALE<<") residual_theta<="<<(double)residual<<'\n';
}catch(const std::exception&e){std::cerr<<"ERROR: "<<e.what()<<'\n';return 1;}}
