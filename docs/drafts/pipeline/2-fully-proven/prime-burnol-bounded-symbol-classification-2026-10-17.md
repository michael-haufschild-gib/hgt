# Prime Burnol eigenoperators: bounded analytic symbol classification

- **ID:** prime-burnol-bounded-symbol-classification-2026-10-17
- **Stage:** 2-fully-proven (paper); formalization pending
- **Type:** THEOREM (paper)
- **Source:** whole local Lean corpus; prospective contribution after candidate 5; uncounted
- **Statement:** bounded operators preserving every actual-prime Burnol eigenline are exactly the operators induced by bounded holomorphic symbols on the right half-plane, with equality of operator and symbol norms.

## Goal and exact natural class

Let H=L²((0,∞),dt), and e_z(t)=t exp(-z t) for Re(z)>0. Actual critical prime
atoms are nonzero multiples of e_log(p). Classify every bounded complex-linear
operator T on H satisfying T(e_log(p))=a_p e_log(p) for every actual prime p.
The proposed conclusion is a unique bounded holomorphic function phi on
Re(z)>0 such that T(e_z)=phi(z)e_z for every z there. Conversely, every such
phi should give one bounded operator, with norm sup |phi|. Symbols are
identified by their values on the half-plane, not by arbitrary values outside it.

This is a positive classification of admissible prime-coordinate actions in
the literal Burnol Hilbert space. It joins the actual-prime source and aperture
route, the Carlson/Blaschke uniqueness mechanism, and Hardy/Pick kernel
positivity. Prime-feature density alone, a necessary boundedness estimate,
or a theorem assuming a cubic Gram positivity certificate will not qualify.
All density, necessity, sufficiency, uniqueness and norm statements count once.

## Initial mechanism audit

1. The literal pairing A_f(z)=<f,e_z> is holomorphic on Re(z)>0 and uniformly
   bounded on each smaller half-plane Re(z)>=delta>0. This follows from
   Cauchy-Schwarz and the integrability of t^k exp(-delta*t), using actual L²
   representatives. Its Gram is <e_z,e_w>=2/(conj(z)+w)^3. The full family
   is total because it includes an existing dense integer-depth Burnol family.
2. A holomorphic function bounded on every smaller right half-plane and
   vanishing at every log(p) is zero. Compose with log(xi+m), where integer
   m>1 is fixed. The resulting function is bounded on Re(xi)>0 and vanishes
   at p-m. Removing finitely many primes and shifting nodes preserves the
   divergence of reciprocal node sums. The corpus half-plane Carlson theorem
   gives zero on an open logarithmic image; analytic continuation gives zero
   on the original half-plane. No prime-density approximation or numerical
   experiment is needed.
3. Fix g=e_1. For each f in H the analytic determinant
   <f,T e_z><g,e_z>-<g,T e_z><f,e_z> vanishes at every log(p), and is bounded
   on smaller half-planes. Step 2 makes it identically zero. Since
   <g,e_z>=2/(1+z)^3 never vanishes, phi(z)=<g,T e_z>/<g,e_z> is holomorphic,
   and testing all f gives T e_z=phi(z)e_z. Nonzero e_z implies |phi(z)|<=||T||.
   The same scalar uniqueness argument proves totality of the prime family.
4. Conversely, a holomorphic symbol bounded by M has a positive first-order
   Pick defect kernel after the Cayley transform. Multiplying that kernel by
   two positive Cauchy kernels gives positivity of
   (M²-conj(phi(z))*phi(w))*2/(conj(z)+w)^3. This is precisely
   ||sum c_z phi(z)e_z||² <= M² ||sum c_z e_z||². It makes the finite-span
   operator well-defined and bounded; dense extension constructs T on H.
   Positivity must be derived from holomorphy and the scalar bound, not assumed.
   The Hardy multiplier construction supplies this forward Pick implication;
   check conjugations against the corpus inner-product convention.
5. Totality gives uniqueness, and Step 3 plus Step 4 gives exact norm equality.
   Addition and composition then agree with symbol addition and multiplication.
   The existing aperture shift has symbol exp(-h*z), giving a literal anchor.

## Initial corpus audit and obligations discharged below

- `HTGeometry/BurnolDepthCompletion.lean` proves integer-depth totality and
  the two-clock graph/vertical-relation classification. It does not classify
  all bounded actual-prime eigenoperators.
- `HTGeometry/BurnolHalfLineWeightedShift.lean` constructs the literal
  weighted aperture shifts. `BurnolValuationCayleyFrame.lean` supplies an
  important unbounded valuation obstruction, not a general positive symbol class.
- `RHTower/PrimeBlindCarlsonThreshold.lean` contains
  `eqOn_zero_of_halfPlane_zeros` and an explicit shifted reciprocal-sum proof.
  The logarithmic-node consequence still needs a complete source-level audit.
- `HTGeometry/HardyShiftCommutant.lean` classifies the ordinary Hardy shift
  commutant. Its Hardy carrier is different from the cubic Burnol carrier.
- `HTGeometry/HardyDiskMultiplier.lean`, `PSDKernelOperations.lean`, and
  `CaratheodoryNevanlinnaPick.lean` contain bounded multiplication and kernel
  product/congruence tools. The exact forward cubic defect proof is open.
- `HTGeometry/BochnerLaplaceHolomorphy.lean` provides interior holomorphy
  from absolute convergence at a smaller frequency. Check its measurability
  interface for restricted-measure L² representatives before use.
- `RHTower/PrimeBurnolFiniteOffDiagonalFaithfulness.lean` proves the literal
  complex Cauchy-cubic Gram, with every entry nonzero.
- `RHTower/RoutePPrimitiveBurnolApertureIntertwinerRigidity.lean` rules out
  primitive-to-strict-right-Xi landing under one aperture commutation relation
  on all functions. That is not this bounded Hilbert-space classification.
- Whole-corpus cached hybrid search `bounded operator diagonal actual prime
  Laplace feature eigenvectors analytic multiplier commutant Blaschke uniqueness`
  completed without partial results: 73,109 inventoried files, 1,082,200
  declarations; compiler evidence mixed/stale. Ranked hits mostly concerned
  orthogonal diagonal operators and did not settle novelty. Exhaustive source
  search found no Burnol commutant or Bergman-named declaration; broader
  multiplier-name hits require further relevance filtering. No external
  novelty claim is made.

## Gates

- [x] 0 → 1: exact actual parameter class, source-pure mechanism and count boundary.
- [x] 1 → 2: dependency-closed paper proof; conjugation, uniqueness and converse audited.
- [ ] 2 → 3: exact Lean result; targeted single-job builds, axioms, wiring, index and lint.

## Failure and positive survivor discipline

If arbitrary H-infinity symbols fail, identify the exact stronger kernel class
and determine whether it has a nontrivial intrinsic analytic characterization.
Do not retire the route at a necessary obstruction. If the intended theorem
is already present or merely a routine bridge, do not count it.

## Log

- 2026-10-17: independent candidate recorded while candidate 5's literal
  completion leaves are being checked. No Lean code written for this candidate.
  Verified total remains 4/100. Frontier map remains read-only.

## Dependency-closed paper proof and stronger intrinsic criterion

The following closes the mathematical proof, subject to formalization of the
exact literal carriers. Let P={z in C: Re(z)>0}, H=L²((0,∞),dt), and
e_z(t)=t exp(-z*t). Inner products are conjugate-linear in their first entry.

**[PROVED HERE] Scalar prime-log uniqueness.** Suppose h is holomorphic on P,
bounded on every set Re(z)>=delta>0, and h(log(p))=0 for all primes p.
Set G(xi)=h(log(xi+2)) on Re(xi)>0, using the principal complex logarithm.
Since Re(xi+2)>2, this logarithm is holomorphic and its real part is
log|xi+2|>log(2)>0. The assumed bound at delta=log(2) bounds G. For
N={n in N: n>=2 and n+2 is prime}, G(n)=0. The sum of 1/n on N diverges:
otherwise comparison 1/(n+2)<=1/n for n>=2, addition of the finitely many
discarded terms and `summable_nat_add_iff` would contradict the existing
`not_summable_one_div_on_primes`. Apply
`PrimeBlindCarlson.eqOn_zero_of_halfPlane_zeros` to G. It follows that
h(log(r+2))=0 for every real r>0. These zeros have an accumulation point
inside the connected domain P, so analytic uniqueness makes h identically
zero on P. This argument uses actual primes, not an assumed node-divergence
or density certificate.

**[PROVED HERE] Literal analytic feature and totality.** For Re(z)>0,
e_z is square-integrable, with
`<e_w,e_z>=2/(z+conj(w))^3` and `||e_z||²=1/(4 Re(z)^3)`.
These follow by the existing complex monomial Laplace integral at degree 2.
For f in H, A_f(z)=<f,e_z> is the Laplace transform of t*conj(f(t)).
Cauchy-Schwarz makes this absolutely integrable at every positive real
frequency. The Bochner Laplace holomorphy proof then gives holomorphy on P;
an indicator of (0,∞) supplies a globally measurable representative if its
API requires one. On Re(z)>=delta, Cauchy-Schwarz gives
`|A_f(z)|<=||f||/(2*delta^(3/2))`.
The family e_(n+1) is the existing ell=1 Burnol depth family and is total.
If f is orthogonal to every e_log(p), scalar prime-log uniqueness applied
to A_f makes it zero on P, hence on all e_(n+1); therefore f=0. Thus the
actual-prime feature span is also dense in H.

**[PROVED HERE] Necessity and uniqueness of the symbol.** Let T be bounded
and T e_log(p)=a_p e_log(p) for all primes. Put g=e_1. For every f in H,

`D_f(z)=<f,T e_z><g,e_z>-<g,T e_z><f,e_z>`.

The adjoint identity writes <f,T e_z>=<T* f,e_z>, so all four factors are
holomorphic and bounded on smaller half-planes. Every D_f vanishes at the
actual prime logarithms. Scalar uniqueness makes D_f zero on P. Since
`<g,e_z>=2/(1+z)^3` never vanishes there, define

`phi(z)=<g,T e_z>/<g,e_z>`.

Then <f,T e_z>=phi(z)<f,e_z> for every f; nondegeneracy gives
T e_z=phi(z)e_z. The nonzero norm of e_z gives |phi(z)|<=||T||, and phi
is holomorphic. In particular phi(log(p))=a_p. Any other bounded holomorphic
symbol agreeing on the primes equals phi by scalar uniqueness. Totality
of e_z makes an operator with this full feature action unique.

**[PROVED HERE] Sufficiency without a positivity premise.** Let phi be
holomorphic on P and |phi|<=M, where M>=0. Pull it to the unit disk by
cayley(u)=(1+u)/(1-u). The actual `hardyMul` construction in
`HTGeometry/HardyDiskMultiplier.lean`
has operator norm at most M, and
`adjoint_hardyMul_hardyKernel` gives its adjoint eigenvectors. For any finite
disk points u_i and coefficients c_i, apply this contraction bound to
v=sum conj(c_i)*k_(u_i). The difference
M²||v||²-||M_phi* v||² is nonnegative and expands to the Pick kernel

`(M²-phi(cayley(u))*conj(phi(cayley(v))))/(1-u*conj(v))`.

Thus its positivity is a consequence of holomorphy and the scalar bound.
The Cayley identity, with u=(z-1)/(z+1), is

`1-u*conj(v)=2*(z+conj(w))/((z+1)*(conj(w)+1))`.

Diagonal congruence therefore proves positivity on P of
`P_phi(z,w)=(M²-phi(z)*conj(phi(w)))/(z+conj(w))`.
The Cauchy kernel C(z,w)=1/(z+conj(w)) is positive by the same transformation
of the Szego Gram (or directly by the exponential-feature integral).
Schur multiplication now makes `2*P_phi*C*C` positive. This is exactly

`(M²-phi(z)*conj(phi(w)))*<e_w,e_z>`.

Expanding finite sums gives
`||sum c_z*phi(z)*e_z||² <= M² ||sum c_z*e_z||²`.
In particular the assignment on finite combinations is well-defined even
without assuming linear independence. `LinearMap.extendOfNorm`, applied
to the dense feature synthesis map, extends it to T on H with ||T||<=M.
Its action on every e_z is prescribed. The construction also covers M=0,
when phi and T are zero. Necessity proves the reverse bound at each z,
so `||T||=sup_(z in P)|phi(z)|`. Addition and multiplication of symbols
give addition and composition of operators by totality. The existing
weighted aperture shift corresponds to phi(z)=exp(-h*z).

**[PROVED HERE] Infinite prime cubic/linear Pick equivalence.** For arbitrary
a:Primes->C and M>=0, define, for k=1 and k=3,

`K_k(p,q)=(M²-a_p*conj(a_q))/(log(p)+log(q))^k`.

Positivity here means positivity for every finite collection of actual
prime nodes and every coefficient vector. K_3 is positive iff there is a
bounded T, ||T||<=M, with T e_log(p)=a_p e_log(p): use the exact cubic Gram,
the finite-sum bound and the prime-span density proved above. Such a T has
the bounded analytic symbol phi by necessity; the preceding first-order
Pick argument makes K_1 positive. Conversely, K_1 positive implies K_3
positive by Schur multiplication by the square of the positive Cauchy
kernel. Hence K_1 and K_3 define exactly the same infinite-prime contraction
data, with the same optimal M. The bounded-symbol existence statement is
equivalent as well. This is an infinite actual-prime rigidity result; no
equivalence is claimed for an arbitrary finite subset of primes.

The literal critical prime atoms have multiplier
`c_p=2*(log p)^2/sqrt(p)>0` relative to e_log(p). Nonzero diagonal congruence
transfers these statements to the corpus's actual critical prime Gram and
`primeLogCriticalLaplaceFeatureL2`, without changing the operator or its norm.

## Adversarial and novelty re-audit

- The prime vectors are not orthogonal. No orthogonal-diagonal multiplier
  theorem is used: cubic Gram domination is derived and then shown equivalent
  to a first-order analytic interpolation law on the full prime set.
- The input class is all bounded operators preserving the actual prime
  eigenlines, or equivalently all scalar prime data passing the full cubic
  positivity condition. There is no RH, source-admission, missing graph core,
  analytic-symbol existence or first-order positivity premise in necessity.
- Boundedness only at the positive real nodes would not suffice; the theorem
  derives a holomorphic symbol bounded on the entire right half-plane.
- Existing depth completeness, two-prime graph saturation and valuation
  Cayley obstructions classify particular prescribed actions. The proposed
  result classifies all bounded prime-eigenline actions and supplies their
  complete analytic parameter space.
- A fresh whole-corpus query for prime logarithms, cubic Cauchy/Pick kernels
  and bounded interpolation completed with `partial=false` over 73,112 files.
  All 20 candidate and 20 source-argument entries were inspected. The relevant
  hits were ordinary Nevanlinna-Pick interpolation and the existing unbounded
  critical cubic Gram on coefficient l²; neither gives this literal Burnol
  eigenoperator or infinite-prime cubic/linear equivalence. Symbol-reference
  searches also checked all files using `burnolRateFeature` or
  `burnolDepthFeatureL2`. No corpus duplicate was found. External priority
  remains unaudited by user instruction.
- The scalar uniqueness, prime density, symbol classification, norm identity
  and cubic/linear equivalence are one contribution. None is counted yet.

The paper proof is dependency-closed. Formalizing the stated actual-prime
classification remains required. The card moved to stage 2 while candidate 5's
local verification was complete and concurrent global umbrella wiring was
still being integrated. No part of this contribution is counted yet.
