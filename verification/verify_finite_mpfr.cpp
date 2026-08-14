#include <algorithm>
#include <cstdlib>
#include <cstdint>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>
#include <mpfr.h>

namespace {
constexpr int B=17032;
constexpr int Q=2*B+1;
constexpr int GENS[]={1518,1524,1587,2024,2032,2116};
constexpr unsigned long N=10000000000000UL;
constexpr const char* X_DECIMAL="0.9996789017186568";
constexpr const char* TARGET="1.19102809";
constexpr mpfr_prec_t PREC=512;
constexpr int INF=1000000000;

struct R{mpfr_t v;R(){mpfr_init2(v,PREC);}~R(){mpfr_clear(v);}R(const R&)=delete;R&operator=(const R&)=delete;};
[[noreturn]]void fail(const std::string&s){throw std::runtime_error(s);}void require(bool b,const std::string&s){if(!b)fail(s);}
void show(const char*name,mpfr_srcptr z){std::cout<<name;mpfr_out_str(stdout,10,70,z,MPFR_RNDN);std::cout<<'\n';}

void pow_bounds(mpfr_ptr lo,mpfr_ptr hi,mpfr_srcptr xlo,mpfr_srcptr xhi,unsigned long e){
  mpfr_pow_ui(lo,xlo,e,MPFR_RNDD);mpfr_pow_ui(hi,xhi,e,MPFR_RNDU);
}
}

int main(){try{
  std::vector<unsigned char> reachable(B+1);reachable[0]=1;
  for(int n=0;n<=B;++n)if(reachable[n])for(int g:GENS)if(n+g<=B)reachable[n+g]=1;
  std::vector<int>M;for(int n=0;n<=B;++n)if(reachable[n])M.push_back(n);
  std::vector<int>cost(B+1,INF);cost[0]=0;std::vector<unsigned char>sum_present(2*B+1);
  for(int a:M)for(int b:M){sum_present[a+b]=1;int d=std::abs(a-b);cost[d]=std::min(cost[d],a+b);}
  require(M.size()==3121&&M.front()==0&&M.back()==B,"mask mismatch");
  require(std::count(sum_present.begin(),sum_present.end(),1)==18730,"sum support mismatch");
  int dsize=1;for(int d=1;d<=B;++d)if(cost[d]<INF)dsize+=2;require(dsize==32369,"difference support mismatch");

  R xlo,xhi;require(mpfr_set_str(xlo.v,X_DECIMAL,10,MPFR_RNDD)==0,"x parse");require(mpfr_set_str(xhi.v,X_DECIMAL,10,MPFR_RNDU)==0,"x parse");
  R pmlo,pmhi,tlo,thi;mpfr_set_zero(pmlo.v,0);mpfr_set_zero(pmhi.v,0);
  for(int d=0;d<=B;++d)if(cost[d]<INF){pow_bounds(tlo.v,thi.v,xlo.v,xhi.v,(unsigned long)cost[d]);if(d==0){mpfr_add(pmlo.v,pmlo.v,tlo.v,MPFR_RNDD);mpfr_add(pmhi.v,pmhi.v,thi.v,MPFR_RNDU);}else{mpfr_mul_ui(tlo.v,tlo.v,2,MPFR_RNDD);mpfr_mul_ui(thi.v,thi.v,2,MPFR_RNDU);mpfr_add(pmlo.v,pmlo.v,tlo.v,MPFR_RNDD);mpfr_add(pmhi.v,pmhi.v,thi.v,MPFR_RNDU);}}

  std::vector<unsigned long>counts(B+1);unsigned long used=0;std::uint64_t total_cost=0;
  R plo,phi,nplo,nphi,flo,fhi;
  for(int d=1;d<=B;++d)if(cost[d]<INF){
    pow_bounds(tlo.v,thi.v,xlo.v,xhi.v,(unsigned long)cost[d]);
    mpfr_div(plo.v,tlo.v,pmhi.v,MPFR_RNDD);mpfr_div(phi.v,thi.v,pmlo.v,MPFR_RNDU);
    mpfr_mul_ui(nplo.v,plo.v,N,MPFR_RNDD);mpfr_mul_ui(nphi.v,phi.v,N,MPFR_RNDU);
    mpfr_floor(flo.v,nplo.v);mpfr_floor(fhi.v,nphi.v);
    unsigned long a=mpfr_get_ui(flo.v,MPFR_RNDN),b=mpfr_get_ui(fhi.v,MPFR_RNDN);
    require(a==b,"insufficient precision to determine a type count");counts[d]=a;
    require(a<=N/2&&used<=N/2-a,"type counts exceed N");used+=a;
    total_cost+=2ULL*(std::uint64_t)a*(std::uint64_t)cost[d];
  }
  unsigned long n0=N-2*used;require(total_cost%2==0,"odd total cost");std::uint64_t L=total_cost/2;
  require(n0==14962802398UL&&L==51500691976683641ULL,"finite type data mismatch");
  require(2*L<=std::numeric_limits<unsigned long>::max(),"unsigned long is too narrow for the MPFR multiplier");

  // Exact lower-count formula: D_lower=N!/(n0! product_{d>0} n_d!^2).
  R arg,logDlo,denomhi,lg,twolg;mpfr_set_ui(arg.v,N+1,MPFR_RNDN);mpfr_lngamma(logDlo.v,arg.v,MPFR_RNDD);mpfr_set_zero(denomhi.v,0);
  mpfr_set_ui(arg.v,n0+1,MPFR_RNDN);mpfr_lngamma(lg.v,arg.v,MPFR_RNDU);mpfr_add(denomhi.v,denomhi.v,lg.v,MPFR_RNDU);
  for(int d=1;d<=B;++d)if(counts[d]){mpfr_set_ui(arg.v,counts[d]+1,MPFR_RNDN);mpfr_lngamma(lg.v,arg.v,MPFR_RNDU);mpfr_mul_ui(twolg.v,lg.v,2,MPFR_RNDU);mpfr_add(denomhi.v,denomhi.v,twolg.v,MPFR_RNDU);}
  mpfr_sub(logDlo.v,logDlo.v,denomhi.v,MPFR_RNDD);

  // |U+U| <= P_+(x)^N x^{-2L}.
  R pphi,logpphi,logxlo,neglogxhi,logSuphi,part1,part2;mpfr_set_zero(pphi.v,0);
  for(int s=0;s<=2*B;++s)if(sum_present[s]){mpfr_pow_ui(thi.v,xhi.v,(unsigned long)s,MPFR_RNDU);mpfr_add(pphi.v,pphi.v,thi.v,MPFR_RNDU);}
  mpfr_log(logpphi.v,pphi.v,MPFR_RNDU);mpfr_mul_ui(part1.v,logpphi.v,N,MPFR_RNDU);
  mpfr_log(logxlo.v,xlo.v,MPFR_RNDD);mpfr_neg(neglogxhi.v,logxlo.v,MPFR_RNDU);mpfr_mul_ui(part2.v,neglogxhi.v,(unsigned long)(2*L),MPFR_RNDU);mpfr_add(logSuphi.v,part1.v,part2.v,MPFR_RNDU);

  // The GHR lemma requires |V-V|<2 max(V)+1.  The generic estimate for U
  // is only non-strict, |U-U|<=2 max(U)+1.  Taking V=2U makes it strict and
  // gives the certified denominator 4 max(U)+1 < 2 Q^N.
  R qv,two,logqhi,log2hi,logdenhi,numerlo,ratiolo,thetalo,targethi;
  mpfr_set_ui(qv.v,Q,MPFR_RNDN);mpfr_log(logqhi.v,qv.v,MPFR_RNDU);mpfr_mul_ui(logdenhi.v,logqhi.v,N,MPFR_RNDU);
  mpfr_set_ui(two.v,2,MPFR_RNDN);mpfr_log(log2hi.v,two.v,MPFR_RNDU);mpfr_add(logdenhi.v,logdenhi.v,log2hi.v,MPFR_RNDU);
  mpfr_sub(numerlo.v,logDlo.v,logSuphi.v,MPFR_RNDD);require(mpfr_sgn(numerlo.v)>0,"finite ratio is not positive");mpfr_div(ratiolo.v,numerlo.v,logdenhi.v,MPFR_RNDD);mpfr_add_ui(thetalo.v,ratiolo.v,1,MPFR_RNDD);
  require(mpfr_set_str(targethi.v,TARGET,10,MPFR_RNDU)==0,"target parse");require(mpfr_cmp(thetalo.v,targethi.v)>0,"finite bound misses target");

  std::cout<<"FINITE CONSTRUCTION CERTIFICATE\nB="<<B<<" base="<<Q<<" depth="<<N<<" n0="<<n0<<" L="<<L<<'\n';
  show("log |U-U| lower = ",logDlo.v);show("log |U+U| upper = ",logSuphi.v);show("log denominator upper = ",logdenhi.v);show("theta finite lower = ",thetalo.v);
  std::cout<<"PASS: the explicit finite set V=2U proves C_3a > "<<TARGET<<'\n';
  return 0;
}catch(const std::exception&e){std::cerr<<"FAIL: "<<e.what()<<'\n';return 1;}}
