/-!
# The computational kernel of the controlled-carry certificate

This module contains the purely computational part of the verification of the two large
numerical facts of Section 4.3 of `masked_digit_bound.tex`:

* the difference-side Collatz--Wielandt certificate `ρ(T_{x,F}) > 582.117820`;
* the sum-side Collatz--Wielandt certificate `𝒫₊(x) ≤ log 79.428331`.

It uses no `Mathlib`, so that it can be compiled to native code (`precompileModules`) and
evaluated at a realistic speed by `native_decide`; all mathematical statements *about* these
definitions live in `RequestProject.CertWeights`, `RequestProject.CertDiff` and
`RequestProject.CertSum`.

Everything here is exact integer arithmetic.  Real numbers enter only in the companion
files, through the two weight tables `wt` (a lower bound for `x ^ a`) and `wtU` (an upper
bound); all intermediate values stay below `2 ^ 63`.

Tables are threaded through the hot loops as explicit arguments, and every table is bound by
a `let` before entering a loop, so that it is computed exactly once.
-/

namespace CertKernel

/-! ## Two tabulation combinators -/

/-- `tabArr f n` is the array `#[f 0, …, f (n-1)]`. -/
def tabArr {α : Type _} (f : Nat → α) (n : Nat) : Array α :=
  (List.range n).foldl (fun a j => a.push (f j)) #[]

/-- `iterF f a₀ n` is the `n`-th iterate `f^[n] a₀`. -/
def iterF {α : Type _} (f : α → α) (a0 : α) : Nat → α
  | 0 => a0
  | n + 1 => f (iterF f a0 n)

/-- `iterArr f d a₀ n` tabulates the iterates `f^[i] a₀` for `i ≤ n`; the table is built
incrementally, each entry from its predecessor. -/
def iterArr {α : Type _} (f : α → α) (dflt : α) (a0 : α) : Nat → Array α
  | 0 => #[a0]
  | n + 1 =>
      let a := iterArr f dflt a0 n
      a.push (f (a.getD n dflt))

/-- `allB p n` tests `p i` for all `i < n`. -/
def allB (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => p n && allB p n

/-! ## Basic constants -/

/-- The largest mask digit `B = 26972`. -/
@[inline] def B : Nat := 26972

/-- The base `q = 27022`. -/
@[inline] def Q : Nat := 27022

/-- The sentinel standing for `+∞` in the integer cost arithmetic. -/
@[inline] def INF : Nat := 1000000000

/-- The binary exponent of the fixed-point scale used for the row sums. -/
@[inline] def EE : Nat := 19

/-- The numerator of the fugacity `x = XN / 2 ^ 52 = 0x1.ffde827adc0fep-1`. -/
@[inline] def XN : Nat := 4502448908984447

/-- The six semigroup generators. -/
def gensL : List Nat := [1971, 2016, 2100, 2628, 2688, 2800]

/-- The truncation parameter of the difference-side automaton. -/
@[inline] def DELD : Nat := 32000

/-- The number of difference-side states. -/
@[inline] def NSD : Nat := 64003

/-- The difference-side state with `u₀ = +∞`, `u₁ = 0`. -/
@[inline] def NIDXD : Nat := 64001

/-- The difference-side state with `u₀ = 0`, `u₁ = +∞`. -/
@[inline] def PIDXD : Nat := 64002

/-- The truncation parameter of the sum-side automaton. -/
@[inline] def DELS : Nat := 60000

/-- The number of sum-side states. -/
@[inline] def NSS : Nat := 120001

/-- The size of the two weight tables. -/
@[inline] def WSZ : Nat := 131072

/-! ## The mask -/

/-- One step of the dynamic program computing membership in the numerical semigroup;
this is the `semiStep` of `RequestProject.Computable` with the generator list of the
certificate. -/
def maskStep (prev : Array Bool) (j : Nat) : Array Bool :=
  prev.push (gensL.any fun g => 0 < g && g ≤ j + 1 && prev.getD (j + 1 - g) false)

/-- The membership table of the mask `M = ⟨gensL⟩ ∩ [0, B]`. -/
def maskArr : Array Bool := (List.range B).foldl maskStep #[true]

/-- The mask, as an increasing list. -/
def maskListOf (mA : Array Bool) : List Nat :=
  (List.range (B + 1)).filter fun v => mA.getD v false

/-- The mask, as an increasing list. -/
def maskList : List Nat := maskListOf maskArr

/-! ## The minimal witness costs `κ` -/

/-- Scans the mask for the least `b` with `b, b + d ∈ M`; returns the cost `2b + d` and the
witness `b`, or `(INF, 0)` if there is none. -/
def kapScan (mA : Array Bool) (d : Nat) : List Nat → Nat × Nat
  | [] => (INF, 0)
  | b :: bs =>
      if B < b + d then (INF, 0)
      else if mA.getD (b + d) false then (2 * b + d, b) else kapScan mA d bs

/-- The witness costs `κ(d)`, `0 ≤ d ≤ B` (`INF` when `d ∉ M - M`). -/
def kapArr : Array Nat :=
  let mA := maskArr
  let ml := maskListOf mA
  tabArr (fun d => (kapScan mA d ml).1) (B + 1)

/-- The witnesses realizing `κ(d)`. -/
def witArr : Array Nat :=
  let mA := maskArr
  let ml := maskListOf mA
  tabArr (fun d => (kapScan mA d ml).2) (B + 1)

/-- `A⁺_r = w(r)`, for `0 ≤ r ≤ Q + 1`. -/
def ApA : Array Nat :=
  let kA := kapArr
  tabArr (fun r => if r ≤ B then kA.getD r INF else INF) (Q + 2)

/-- `A⁻_r = w(r - Q) = w(Q - r)`, for `0 ≤ r ≤ Q + 1`. -/
def AmA : Array Nat :=
  let kA := kapArr
  tabArr (fun r => if r ≤ Q && Q - r ≤ B then kA.getD (Q - r) INF else INF) (Q + 2)

/-- The check that the recorded difference cost is realized by a genuine pair of mask
elements: for every `d ≤ B` with a finite entry, `witArr[d]` and `witArr[d] + d` lie in the
mask and `kapArr[d] = 2 * witArr[d] + d`. -/
def kapCheck (_ : Unit) : Bool :=
  let mA := maskArr
  let kA := kapArr
  let wA := witArr
  allB (fun d =>
    let k := kA.getD d INF
    let b := wA.getD d 0
    (k == INF) ||
      (mA.getD b false && (b + d ≤ B) && mA.getD (b + d) false && (k == 2 * b + d))) (B + 1)

/-! ## The sum support -/

/-- The membership table of the sum support `S = M + M ⊆ [0, 2B]`. -/
def sumArr : Array Bool :=
  let ml := maskList
  ml.foldl (fun a b => ml.foldl (fun a c => a.set! (b + c) true) a)
    (Array.replicate (2 * B + 1) false)

/-- The check that `sumArr` contains every sum of two mask elements. -/
def sumCheck (_ : Unit) : Bool :=
  let ml := maskList
  let sA := sumArr
  ml.all fun b => ml.all fun c => sA.getD (b + c) false

/-- `B⁺_i = scost(i - 1)`, the cost of the sum digit `i - 1`. -/
def BpA : Array Nat :=
  let sA := sumArr
  tabArr (fun i => if 1 ≤ i && i - 1 ≤ 2 * B && sA.getD (i - 1) false then i - 1 else INF)
    (Q + 2)

/-- `B⁻_i = scost(i - 1 + Q)`, the cost of the sum digit `i - 1 + Q`.  The index shift is
performed as `i + Q - 1`, which is exact in `Nat` for every `i` (including `i = 0`, where the
sum digit is `Q - 1`). -/
def BqA : Array Nat :=
  let sA := sumArr
  tabArr
    (fun i =>
      let v := i + Q - 1
      if v ≤ 2 * B && sA.getD v false then v else INF) (Q + 2)

/-! ## The weight tables -/

/-- `ceilShift p sh` is `⌈p / 2 ^ sh⌉`, computed without ever forming `2 ^ sh`. -/
def ceilShift (p sh : Nat) : Nat :=
  let c := p >>> sh
  if c <<< sh == p then c else c + 1

/-- One step of the lower weight recursion. -/
def wtStep (p : Nat × Nat) : Nat × Nat :=
  let t := p.1 * XN
  let m1 := t >>> 52
  if 2 ^ 63 ≤ m1 then (m1, p.2) else (t >>> 51, p.2 + 1)

/-- One step of the upper weight recursion. -/
def wtStepU (p : Nat × Nat) : Nat × Nat :=
  let t := p.1 * XN
  let m1 := ceilShift t 52
  if 2 ^ 63 ≤ m1 then (m1, p.2) else (ceilShift t 51, p.2 + 1)

/-- The lower weight table: `wt a = (m, e)` with `m * 2 ^ (-e) ≤ x ^ a`. -/
def wt (a : Nat) : Nat × Nat := iterF wtStep (2 ^ 63, 63) a

/-- The upper weight table: `wtU a = (m, e)` with `x ^ a ≤ m * 2 ^ (-e)`. -/
def wtU (a : Nat) : Nat × Nat := iterF wtStepU (2 ^ 63, 63) a

/-- The lower weight table, tabulated. -/
def wtArr : Array (Nat × Nat) := iterArr wtStep (0, 0) (2 ^ 63, 63) WSZ

/-- The upper weight table, tabulated. -/
def wtArrU : Array (Nat × Nat) := iterArr wtStepU (0, 0) (2 ^ 63, 63) WSZ

/-- The 32-bit mantissas of the lower weight table. -/
def m32L : Array Nat :=
  let W := wtArr
  tabArr (fun a => (W.getD a (0, 0)).1 >>> 32) (WSZ + 1)

/-- The exponents of the lower weight table, shifted by 32. -/
def e32L : Array Nat :=
  let W := wtArr
  tabArr (fun a => (W.getD a (0, 0)).2 - 32) (WSZ + 1)

/-- The 32-bit mantissas of the upper weight table, rounded up. -/
def m32U : Array Nat :=
  let W := wtArrU
  tabArr (fun a => ((W.getD a (0, 0)).1 >>> 32) + 1) (WSZ + 1)

/-- The exponents of the upper weight table, shifted by 32. -/
def e32U : Array Nat :=
  let W := wtArrU
  tabArr (fun a => (W.getD a (0, 0)).2 - 32) (WSZ + 1)

/-! ## The certificate vectors -/

/-- Parses a whitespace-separated list of decimal natural numbers. -/
def parseAux (bs : ByteArray) (i : Nat) (cur : Nat) (started : Bool) (acc : Array Nat) :
    Array Nat :=
  if h : i < bs.size then
    let c := bs[i]
    if 48 ≤ c.toNat && c.toNat ≤ 57 then
      parseAux bs (i + 1) (cur * 10 + (c.toNat - 48)) true acc
    else if started then parseAux bs (i + 1) 0 false (acc.push cur)
    else parseAux bs (i + 1) 0 false acc
  else if started then acc.push cur else acc
  termination_by bs.size - i
  decreasing_by all_goals omega

/-- Parses a whitespace-separated list of decimal natural numbers. -/
def parseVec (s : String) : Array Nat := parseAux s.toUTF8 0 0 false #[]

/-- The difference-side certificate vector, read from the certificate data. -/
def diffV : Array Nat := parseVec (include_str "../certificate/diff_vector.txt")

/-- The sum-side certificate vector, read from the certificate data. -/
def sumV : Array Nat := parseVec (include_str "../certificate/sum_vector.txt")

/-! ## The difference-side automaton -/

/-- The normalized cost `u₀` of the difference-side state `s`. -/
def du0 (s : Nat) : Nat :=
  if s ≤ 2 * DELD then (if DELD ≤ s then 0 else DELD - s)
  else if s == NIDXD then INF else 0

/-- The normalized cost `u₁` of the difference-side state `s`. -/
def du1 (s : Nat) : Nat :=
  if s ≤ 2 * DELD then (if DELD ≤ s then s - DELD else 0)
  else if s == NIDXD then 0 else INF

/-- The new cost of the carry-`0` representative. -/
def dv0 (Ap : Array Nat) (u0 u1 r : Nat) : Nat :=
  min (u0 + Ap.getD r INF) (u1 + Ap.getD (r + 1) INF)

/-- The new cost of the carry-`1` representative. -/
def dv1 (Am : Array Nat) (u0 u1 r : Nat) : Nat :=
  min (u0 + Am.getD r INF) (u1 + Am.getD (r + 1) INF)

/-- The cost increment `a(δ, r)` of the difference-side automaton. -/
def dcost (Ap Am : Array Nat) (u0 u1 r : Nat) : Nat := min (dv0 Ap u0 u1 r) (dv1 Am u0 u1 r)

/-- The successor state of the difference-side automaton. -/
def dnext (Ap Am : Array Nat) (u0 u1 r : Nat) : Nat :=
  let v0 := dv0 Ap u0 u1 r
  let v1 := dv1 Am u0 u1 r
  if INF ≤ v0 then NIDXD
  else if INF ≤ v1 then PIDXD
  else if v0 ≤ v1 then (if DELD < v1 - v0 then PIDXD else DELD + (v1 - v0))
  else (if DELD < v0 - v1 then NIDXD else DELD - (v0 - v1))

/-- One term of the difference-side row sum, a lower bound for `2^EE · x^a · V(Φ(s,r))`. -/
def dterm (Ap Am m32 e32 V : Array Nat) (u0 u1 r : Nat) : Nat :=
  let a := dcost Ap Am u0 u1 r
  if INF ≤ a then 0
  else (m32.getD a 0 * V.getD (dnext Ap Am u0 u1 r) 0) >>> (e32.getD a 0 - EE)

/-- The difference-side row sum, accumulated over the digits `r < n`. -/
def drowAux (Ap Am m32 e32 V : Array Nat) (u0 u1 : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | r + 1, acc => drowAux Ap Am m32 e32 V u0 u1 r (acc + dterm Ap Am m32 e32 V u0 u1 r)

/-- The difference-side row sum over all canonical digits. -/
def drow (Ap Am m32 e32 V : Array Nat) (s : Nat) : Nat :=
  drowAux Ap Am m32 e32 V (du0 s) (du1 s) Q 0

/-- The numerator of the certified difference-side ratio `582.117820`. -/
@[inline] def cNum : Nat := 582117820

/-- The denominator of the certified difference-side ratio `582.117820`. -/
@[inline] def cDen : Nat := 1000000

/-- The Collatz--Wielandt test at one difference-side state. -/
def dtest (Ap Am m32 e32 V : Array Nat) (s : Nat) : Bool :=
  cNum * ((V.getD s 0) <<< EE) ≤ cDen * drow Ap Am m32 e32 V s

/-! ## The sum-side automaton -/

/-- The normalized cost `u₀` of the sum-side state `s`. -/
def su0 (s : Nat) : Nat := if DELS ≤ s then 0 else DELS - s

/-- The normalized cost `u₁` of the sum-side state `s`. -/
def su1 (s : Nat) : Nat := if DELS ≤ s then s - DELS else 0

/-- The new cost of the outgoing-carry-`0` state. -/
def sv0 (Bp : Array Nat) (u0 u1 r : Nat) : Nat :=
  min (u0 + Bp.getD (r + 1) INF) (u1 + Bp.getD r INF)

/-- The new cost of the outgoing-carry-`1` state. -/
def sv1 (Bq : Array Nat) (u0 u1 r : Nat) : Nat :=
  min (u0 + Bq.getD (r + 1) INF) (u1 + Bq.getD r INF)

/-- The cost increment of the sum-side automaton. -/
def scostN (Bp Bq : Array Nat) (u0 u1 r : Nat) : Nat := min (sv0 Bp u0 u1 r) (sv1 Bq u0 u1 r)

/-- The successor state of the sum-side automaton. -/
def snext (Bp Bq : Array Nat) (u0 u1 r : Nat) : Nat :=
  let v0 := sv0 Bp u0 u1 r
  let v1 := sv1 Bq u0 u1 r
  if INF ≤ v0 then 0
  else if INF ≤ v1 then 2 * DELS
  else if v0 ≤ v1 then (if DELS < v1 - v0 then 2 * DELS else DELS + (v1 - v0))
  else (if DELS < v0 - v1 then 0 else DELS - (v0 - v1))

/-- One term of the sum-side row sum, an upper bound for `2^EE · x^a · V(Φ(s,r))`. -/
def sterm (Bp Bq m32 e32 V : Array Nat) (u0 u1 r : Nat) : Nat :=
  let a := scostN Bp Bq u0 u1 r
  if INF ≤ a then 0
  else if WSZ ≤ a then (V.getD (snext Bp Bq u0 u1 r) 0) <<< EE
  else ceilShift (m32.getD a 0 * V.getD (snext Bp Bq u0 u1 r) 0) (e32.getD a 0 - EE)

/-- The sum-side row sum, accumulated over the digits `r < n`. -/
def srowAux (Bp Bq m32 e32 V : Array Nat) (u0 u1 : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | r + 1, acc => srowAux Bp Bq m32 e32 V u0 u1 r (acc + sterm Bp Bq m32 e32 V u0 u1 r)

/-- The sum-side row sum over all canonical digits. -/
def srow (Bp Bq m32 e32 V : Array Nat) (s : Nat) : Nat :=
  srowAux Bp Bq m32 e32 V (su0 s) (su1 s) Q 0

/-- The numerator of the certified sum-side ratio `79.428331`. -/
@[inline] def pNum : Nat := 79428331

/-- The denominator of the certified sum-side ratio `79.428331`. -/
@[inline] def pDen : Nat := 1000000

/-- The Collatz--Wielandt test at one sum-side state. -/
def stest (Bp Bq m32 e32 V : Array Nat) (s : Nat) : Bool :=
  pDen * srow Bp Bq m32 e32 V s ≤ pNum * ((V.getD s 0) <<< EE)

/-! ## The top-level checks -/

/-- The difference-side Collatz--Wielandt check over all states. -/
def diffCheck (_ : Unit) : Bool :=
  let Ap := ApA
  let Am := AmA
  let m32 := m32L
  let e32 := e32L
  let V := diffV
  allB (dtest Ap Am m32 e32 V) NSD

/-- The sum-side Collatz--Wielandt check over all states. -/
def sumRowCheck (_ : Unit) : Bool :=
  let Bp := BpA
  let Bq := BqA
  let m32 := m32U
  let e32 := e32U
  let V := sumV
  allB (stest Bp Bq m32 e32 V) NSS

/-- Positivity of the difference-side certificate vector. -/
def diffVPos (_ : Unit) : Bool :=
  let V := diffV
  allB (fun i => 0 < V.getD i 0) NSD

/-- Positivity of the sum-side certificate vector. -/
def sumVPos (_ : Unit) : Bool :=
  let V := sumV
  allB (fun i => 0 < V.getD i 0) NSS

end CertKernel
