#pragma once

#include <algorithm>
#include <atomic>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <numeric>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>
#include <omp.h>

namespace pressure {

constexpr int INF=1000000000;
constexpr int POS_INF=1000000001;
constexpr int NEG_INF=-1000000001;

struct Candidate {
  uint64_t id=0;
  int family=0,B=0,q=0;
  std::vector<int> gens;
};

struct Data {
  int B=0,Q=0,max_state=0,slots=0;
  std::vector<int>A,N,mask,cost;
  std::vector<unsigned char>sum;

  explicit Data(const Candidate&c):B(c.B),Q(c.q),max_state(std::max(1000000,40*c.B)),slots(2*max_state+3),A(Q+1,INF),N(Q+1,INF),cost(B+1,INF),sum(2*B+1){
    if(B<=0||Q<=B||c.gens.empty())throw std::runtime_error("invalid candidate dimensions");
    std::vector<unsigned char>in(B+1);in[0]=1;
    for(int n=0;n<=B;n++)if(in[n])for(int g:c.gens)if(g>0&&n+g<=B)in[n+g]=1;
    for(int n=0;n<=B;n++)if(in[n])mask.push_back(n);
    if(mask.empty()||mask.back()!=B)throw std::runtime_error("B is not in generated mask");
    cost[0]=0;
    for(int a:mask)for(int b:mask){sum[a+b]=1;int d=std::abs(a-b);cost[d]=std::min(cost[d],a+b);}
    for(int r=0;r<=Q;r++){if(r<=B)A[r]=cost[r];int d=Q-r;if(d>=0&&d<=B)N[r]=cost[d];}
  }

  int slot(int s)const {if(s==NEG_INF)return 2*max_state+1;if(s==POS_INF)return 2*max_state+2;return s+max_state;}
  int state(int z)const {if(z==2*max_state+1)return NEG_INF;if(z==2*max_state+2)return POS_INF;return z-max_state;}
};

inline void diff_norm(int s,int&u0,int&u1){
  if(s==POS_INF){u0=0;u1=INF;}else if(s==NEG_INF){u0=INF;u1=0;}
  else if(s>=0){u0=0;u1=s;}else{u0=-s;u1=0;}
}

inline bool diff_transition(const Data&d,int s,int r,int&add,int&next){
  int u0,u1;diff_norm(s,u0,u1);auto p=[](int a,int b){return a>=INF||b>=INF?INF:a+b;};
  int v0=std::min(p(u0,d.A[r]),p(u1,d.A[r+1]));
  int v1=std::min(p(u0,d.N[r]),p(u1,d.N[r+1]));
  if(v0>=INF&&v1>=INF)return false;
  if(v1>=INF){add=v0;next=POS_INF;}else if(v0>=INF){add=v1;next=NEG_INF;}
  else{add=std::min(v0,v1);next=v1-v0;}return true;
}

inline void plus_norm(int d,int&c1,int&c0){
  if(d==NEG_INF){c1=INF;c0=0;}else if(d==POS_INF){c1=0;c0=INF;}
  else if(d>=0){c1=0;c0=d;}else{c1=-d;c0=0;}
}

inline bool plus_transition(const Data&D,int d,int y,int&inc,int&nd){
  int c1,c0;plus_norm(d,c1,c0);int n1=INF,n0=INF,s;
  if(c1<INF){s=y+D.Q-1;if(s<=2*D.B&&D.sum[s])n1=std::min(n1,c1+s);s=y-1;if(s>=0&&s<=2*D.B&&D.sum[s])n0=std::min(n0,c1+s);}
  if(c0<INF){s=y+D.Q;if(s<=2*D.B&&D.sum[s])n1=std::min(n1,c0+s);s=y;if(y<=2*D.B&&D.sum[s])n0=std::min(n0,c0+s);}
  if(n1>=INF&&n0>=INF)return false;
  if(n1>=INF){inc=n0;nd=NEG_INF;}else if(n0>=INF){inc=n1;nd=POS_INF;}
  else{inc=std::min(n1,n0);nd=n0-n1;}return true;
}

inline std::vector<int> frontier(const Data&d,int depth,bool quiet=true){
  int nt=omp_get_max_threads();std::vector<int>cur{POS_INF};
  for(int dep=1;dep<=depth;dep++){
    std::vector<std::vector<unsigned char>>hit(nt,std::vector<unsigned char>(d.slots));long long outside=0;
#pragma omp parallel reduction(+:outside)
    {int tid=omp_get_thread_num();
#pragma omp for schedule(static)
      for(int i=0;i<(int)cur.size();i++)for(int r=0;r<d.Q;r++){int a,n;if(!diff_transition(d,cur[i],r,a,n))continue;int z=d.slot(n);if(z<0||z>=d.slots)outside++;else hit[tid][z]=1;}}
    if(outside)throw std::runtime_error("state bound too small");
    std::vector<int>nxt;for(int z=0;z<d.slots;z++){bool h=false;for(int t=0;t<nt;t++)h|=hit[t][z];if(h)nxt.push_back(d.state(z));}
    cur.swap(nxt);if(!quiet)std::cerr<<"F"<<dep<<'='<<cur.size()<<'\n';
  }return cur;
}

inline std::vector<int> make_index(const Data&d,const std::vector<int>&states){
  std::vector<int>idx(d.slots,-1);for(int i=0;i<(int)states.size();i++){int z=d.slot(states[i]);if(z<0||z>=d.slots)throw std::runtime_error("bad state index");idx[z]=i;}return idx;
}

inline void load_seed(const std::string&path,const Data&d,const std::vector<int>&idx,std::vector<double>&v){
  if(path.empty())return;
  std::ifstream f(path);if(!f)throw std::runtime_error("cannot open seed vector "+path);int st;std::string word;
  while(f>>st>>word){int z=d.slot(st);if(z>=0&&z<d.slots&&idx[z]>=0){double x=std::stod(word);if(x>0&&std::isfinite(x))v[idx[z]]=x;}}
}

inline void save_vector(const std::string&path,const std::vector<int>&states,const std::vector<double>&v){
  std::ofstream f(path);if(!f)throw std::runtime_error("cannot write vector");
  for(size_t i=0;i<states.size();i++)f<<states[i]<<' '<<std::hexfloat<<v[i]<<'\n';
}

inline double plus_block_root(const Data&D,double x,int K){
  const int cache_limit=4*D.B+D.Q+10;std::vector<long double>xp(cache_limit);xp[0]=1;for(int i=1;i<cache_limit;i++)xp[i]=xp[i-1]*(long double)x;
  auto power=[&](int n){return n<cache_limit?xp[n]:std::exp((long double)n*std::log((long double)x));};
  std::unordered_map<int,std::vector<std::pair<int,long double>>>kernel;kernel.reserve(2*K+8);
  auto row_for=[&](int st)->const std::vector<std::pair<int,long double>>&{auto it=kernel.find(st);if(it!=kernel.end())return it->second;std::map<int,long double>agg;for(int y=0;y<D.Q;y++){int inc,ns;if(plus_transition(D,st,y,inc,ns))agg[ns]+=power(inc);}std::vector<std::pair<int,long double>>edges(agg.begin(),agg.end());return kernel.emplace(st,std::move(edges)).first->second;};
  std::map<int,long double>cur,nxt;cur[NEG_INF]=1;long double log_scale=0;
  for(int k=0;k<K;k++){nxt.clear();for(auto [st,w]:cur)for(auto [ns,tw]:row_for(st))nxt[ns]+=w*tw;long double scale=0;for(auto [st,w]:nxt)scale=std::max(scale,w);if(!(scale>0))throw std::runtime_error("empty plus automaton");for(auto&it:nxt)it.second/=scale;log_scale+=std::log(scale);cur.swap(nxt);}
  long double row=0;for(auto [st,w]:cur){int c1,c0;plus_norm(st,c1,c0);if(c0<INF)row+=w*power(c0);if(c1<INF)row+=w*power(c1);}
  return (double)std::exp((log_scale+std::log(row))/K);
}

inline double direct_one_root(const Data&d,double x){
  long double z=0;for(int r=0;r<d.Q;r++){int a,n;if(diff_transition(d,POS_INF,r,a,n))z+=std::pow((long double)x,a);}return (double)z;
}

inline double direct_block_root(const Data&d,double x,int K,bool quiet=true){
  if(K<=0)return 0;
  const int nt=omp_get_max_threads();
  std::vector<double>cur(d.slots),next(d.slots);std::vector<int>active{d.slot(POS_INF)},next_active;cur[d.slot(POS_INF)]=1;
  std::vector<std::vector<double>>local(nt,std::vector<double>(d.slots));
  std::vector<double>xp((size_t)(4*d.B+K*d.Q+10));xp[0]=1;for(size_t i=1;i<xp.size();i++)xp[i]=xp[i-1]*x;
  for(int dep=1;dep<=K;dep++){std::atomic<bool>outside{false};
#pragma omp parallel
    {int tid=omp_get_thread_num();auto&out=local[tid];
#pragma omp for schedule(static)
      for(int ii=0;ii<(int)active.size();ii++){int z=active[ii],s=d.state(z);double base=cur[z];for(int r=0;r<d.Q;r++){int a,n;if(!diff_transition(d,s,r,a,n))continue;int nz=d.slot(n);if(nz<0||nz>=d.slots){outside=true;continue;}out[nz]+=base*xp[a];}}}
    if(outside)throw std::runtime_error("state bound too small in direct block");
    next_active.clear();
    for(int z=0;z<d.slots;z++){double value=0;for(int t=0;t<nt;t++){value+=local[t][z];local[t][z]=0;}if(value>0){next[z]=value;next_active.push_back(z);}}
    for(int z:active)cur[z]=0;
    cur.swap(next);active.swap(next_active);if(!quiet)std::cerr<<"Z"<<dep<<" states="<<active.size()<<'\n';
  }
  long double total=0;for(int z:active)total+=cur[z];return (double)std::pow(total,1.0L/K);
}

struct Eval {double x=0,lambda=0,rho_lo=0,rho_hi=0,direct_root=0,plus_root=0,theta=-1e100;int states=0;};

inline Eval spectral_eval(const Data&d,const std::vector<int>&states,const std::vector<int>&idx,std::vector<double>&v,double x,int iterations,int plus_depth){
  std::vector<double>w((size_t)(4*d.B+10));w[0]=1;for(size_t i=1;i<w.size();i++)w[i]=w[i-1]*x;
  std::vector<double>y(states.size());double mn=0,mx=0;
  for(int it=0;it<iterations;it++){mn=1e300;mx=0;
#pragma omp parallel for schedule(static) reduction(min:mn) reduction(max:mx)
    for(int i=0;i<(int)states.size();i++){double z=0;for(int r=0;r<d.Q;r++){int a,n;if(!diff_transition(d,states[i],r,a,n))continue;int sl=d.slot(n);if(sl<0||sl>=d.slots)continue;int j=idx[sl];if(j>=0)z+=w[a]*v[j];}y[i]=z;double rr=v[i]>0?z/v[i]:0;mn=std::min(mn,rr);mx=std::max(mx,rr);}
    if(!(mn>0)||!std::isfinite(mx))return Eval{x,-std::log(x),0,mx,0,0,-1e100,(int)states.size()};
    double scale=std::sqrt(mn*mx);for(size_t i=0;i<v.size();i++)v[i]=y[i]/scale;
  }
  double pr=plus_block_root(d,x,plus_depth);return Eval{x,-std::log(x),mn,mx,0,pr,1+std::log(mn/pr)/std::log((double)d.Q),(int)states.size()};
}

inline Eval one_block_eval(const Data&d,double x){
  double dr=direct_one_root(d,x),pr=plus_block_root(d,x,1);return Eval{x,-std::log(x),0,0,dr,pr,1+std::log(dr/pr)/std::log((double)d.Q),0};
}

} // namespace pressure
