# Arithmetic secular signs classify every finite-prime gap

- **ID:** ACP-FINITE-PRIME-GAP-CRITERION
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** arithmetic-counting-finite-prime-secular-gap.md
- **Sources:** finite-prime spectral mass, actual conductor coordinates, full resolvent limit, finite Hermitian reciprocal criterion, universal dyadic ceiling
- **Statement:** Every finite-prime hyperplane gap is characterized by its arithmetic secular signs below the dyadic ceiling. The positive greatest gap is attained and decreases under inclusion of flipped-prime sets.

## Exact statement

For a finite prime set F, let c_F be its product harmonic density and
`Phi_F(s)=-1/s+sum_(m>=2) w_F(m)/(D_m-s)` its normalized secular function.
Write `g0=2 log 2`. For every real g, including nonpositive values,

`HasHyperplaneGap(omega_F,g) iff g<=g0 and
  forall s, 0<s<g implies Phi_F(s)<=0`.

Define `delta_F=sup {g:HasHyperplaneGap(omega_F,g)}`. Then

1. delta_F is attained, and `HasHyperplaneGap(omega_F,g) iff g<=delta_F`;
2. `0<g0*c_F^2<=delta_F<=g0`;
3. `F subset G` implies `w_F(m)<=w_G(m)` for every conductor, hence
   `Phi_F(s)<=Phi_G(s)` for `0<s<g0`, and `delta_G<=delta_F`.

The empty set is included. The supremum is bounded and nonempty, so no
default value of the real supremum enters the assertions.

## Closed proof

### 1. Exact finite constraint

At a positive horizon, multiplication by omega_F is an isometry because
omega_F(n)^2=1. It identifies the harmonic constraint on x with the
orthogonal complement of the normalized vector
`v_(F,N)(n)=omega_F(n)/(sqrt(n)*sqrt(H_N))`. Its Euclidean squared norm is
one. The atomic prime quadratic form equals the actual matrix quadratic
form, using extension by zero outside the horizon.

Fix `0<s<g0`. The actual ground energy tends to gamma, its squared
constraint coordinate tends to c_F^2>0, and the spectral count below any
fixed intermediate energy `gamma+t`, s<t<g0, is eventually one. Thus the
shifted diagonal has exactly one negative direction, the ground coefficient
is nonzero, and all other directions are positive. The already proved
finite Hermitian criterion identifies the constrained lower energy bound
at gamma+s with `R_(F,N)(s)<=0`, exactly.

### 2. Necessity of the secular signs

Every sign gauge has gap at most g0. Suppose g is a gap and 0<s<g.
Use epsilon=(g-s)/2 in its defining eventual bound. For all sufficiently
large horizons this implies the constrained energy bound at gamma+s,
hence R_(F,N)(s)<=0 by step 1. The full actual resolvent tends to
c_F^2 Phi_F(s), so Phi_F(s)>0 would give an eventually positive reading,
a contradiction. Consequently Phi_F(s)<=0.

### 3. Sufficiency, including the endpoint

For g<=0 use the unconditional zero gap and downward closure. For g>0
and each epsilon>0 choose `max(0,g-epsilon)<s<t<g`. Strict increase gives
`Phi_F(s)<Phi_F(t)<=0`. Since c_F^2>0, the full resolvent is eventually
strictly negative at s. Step 1 gives the actual constrained bound at s;
the inequality s>g-epsilon gives exactly the requested gap g.

Strict negativity is essential here. Mere convergence to a nonpositive
number would not imply an eventual finite sign. The extra test value t
supplies strictness without assuming a uniform horizon in s.

### 4. Attainment

The set of gaps contains zero and is bounded above by g0. Its supremum
delta_F is therefore finite and at most g0. For each 0<s<delta_F,
the definition of supremum supplies an actual gap g>s. Necessity gives
Phi_F(s)<=0. Sufficiency then proves that delta_F itself is a gap.
Downward closure classifies every smaller real value. The existing exact
harmonic-density bound g0*c_F^2 is a gap and is strictly positive, proving
the stated quantitative lower bound.

### 5. Inclusion of prime sets

The normalized weight is `4^omega(m)/phi(m)` on F-supported positive
conductors and zero otherwise. Every F-supported conductor is also
G-supported when F is a subset of G. Thus w_F<=w_G pointwise. The positive
denominator bound D_m-s>=g0-s and established summability permit comparison
of the whole tails, giving Phi_F<=Phi_G. Apply the exact criterion to the
attained gap delta_G: its secular inequalities also hold for F. Therefore
delta_G<=delta_F.

## Scope and audit

The new endpoint concerns the actual finite prime matrices and their
uniform limiting hyperplane gaps. No spectral or analytic input is left
as an assumption. The order comparison does not claim strict decrease,
prime-exhaustion collapse, a decay rate, or complete Weil positivity.
Those require separate proofs. Classical one-negative-direction linear
algebra and Euler products remain reusable background, not novelty claims.

Canonical source: `formal/GaloisForLFunctions/ArithmeticCountingPositivity/TheFinitePrimeSecularSignsDetermineTheGap.lean`.

- `finiteFlip_hasHyperplaneGap_iff_secular`
- `isGreatest_finiteFlip_hyperplaneGap`
- `finiteFlip_hasHyperplaneGap_iff_le_greatestGap`
- `finiteFlipGreatestGap_bounds`
- `finiteFlipGreatestGap_pos`
- `finiteFlipSpectralWeight_mono`
- `finiteFlipSecular_mono`
- `finiteFlipGreatestGap_antitone`

Scratch 39652 and canonical check 43495 both exited zero without diagnostics.
All eight transitive audits use only `propext`, `Classical.choice`, and
`Quot.sound`. Exact commands, source hash and actual output are in the
adjacent `-audit.txt`. The umbrella is wired but was not compiled.

- [x] Dependency-complete paper proof.
- [x] Eight Lean endpoints and transitive axiom audit.
- [x] Canonical audit, umbrella wiring, durable evidence and cleanup.
