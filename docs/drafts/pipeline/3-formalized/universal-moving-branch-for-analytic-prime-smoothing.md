# Universal moving branch for analytic prime smoothing

- **ID:** B130-analytic-prime-smoothing-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM — Lean
- **Source:** [Quadratic residue scaling](../3-formalized/quadratic-residue-collapse-with-a-nonpolynomial-joint-limit.md).

## Target

Let `Φ` be analytic on a disc of radius greater than one, with
`Φ(0)=1`, `Φ(1)=-1`, and `|Φ(x)|=1` for real `0≤x≤1`.
Write `Φ(z)-1=Σ_{k≥1}a_k z^k`, and let `m` be the first nonzero
coefficient index. For the actual prime phases `v_p(t)=Φ(p^(-t))`,
the exact small-parameter branch law is

`U(t,s)=A_t(s)(s-(1-mt))^(-a_m)`, `A_t(1-mt)≠0`.

The phase condition forces `a_m` to be nonzero and purely imaginary.
Consequently no such nonconstant smoothing family has an actual joint
holomorphic endpoint regularization. The universal scaling
profile is

`U(t,1+tw)/t² → ζ(2)exp(-Σ_{k≥1}a_k log(w+k))`, `Re w>-m`.

## Paper proof

Choose an intermediate closed disc of radius greater than one inside
the analytic domain. Put `F=Φ-1`. Analyticity there and `F(1)=-2`
exclude the zero germ at zero. Its first nonzero Taylor order is
`m≥1`, with the exact factorization `F(z)=z^m G(z)`, where `G` is
analytic on the same disc and `G(0)≠0`. For real `0<x≤1`,

`0=|1+x^mG(x)|²-1=x^m[2Re G(x)+x^m|G(x)|²]`.

Divide by `x^m` and let `x→0⁺`. Thus `G(0)=ib` for a real
`b≠0`. The analytic removable quotient `(G(z)-G(0))/z` is bounded
on the complex unit disc. Consequently, uniformly for `|z|≤1`,

`|Φ(z)-1|≤C|z|^m`,
`|Φ(z)-1-ibz^m|≤C'|z|^(m+1)`.

These estimates derive both the first coefficient and the next-order
prime saving from the defining phase conditions.

**Actual interior fibres.** Substitution `z=p^(-t)` gives absolute
prime-deviation summability on `Re s>1-mt`. On a sufficiently small
complex parameter disc about each real `t>0`, the same estimate is
normal and summable below one. The canonical Euler logarithm therefore
produces an actual joint pole germ with nonzero residue. On
`Re s>max(1/2,1-mt)`, the fibre is `ζ(s)exp(H(t,s))`; all zero
multiplicities there equal those of ζ.

**Moving branch.** Write `P(s)=Σ_p p^(-s)`,
`D_v(s)=Σ_p[-log(1-v_p p^(-s))-v_p p^(-s)]`, and
`Z(s)=(s-1)ζ(s)`, extended by `Z(1)=1`. The prime-logarithm germ is
`P(s)=-log(s-1)+E(s)`, with `E` analytic at one and `E(1)=-D_+(1)`.
The next-order estimate makes

`R_t(s)=Σ_p[Φ(p^(-t))-1-ibp^(-mt)]p^(-s)`

analytic on `Re s>1-(m+1)t`. The higher prime powers are analytic
on `Re s>1/2`. Thus, on the right of `s₀=1-mt`,

`H(t,s)=-ib log(s-s₀)+ib E(s+mt)+R_t(s)+D_v(t)(s)-D_+(s)`.

For small `t>0` the last four terms are analytic near `s₀` and
`Z(s₀)≠0`. Hence `U(t,s)=A_t(s)exp(-ib log(s-s₀))` with an
analytic nonzero factor. Along
`x_n=exp(-2πn/|b|)` and `y_n=exp(-(2πn+π)/|b|)`, its values at
`s₀+x_n` and `s₀+y_n` tend respectively to `A_t(s₀)` and
`-A_t(s₀)`. No continuous extension exists there.

A joint endpoint germ would give a continuous spectral slice at this
point for sufficiently small positive `t`. Agreement merely for nearby
real spectral values greater than one forces agreement throughout the
connected intersection of its spectral disc with
`Re s>max(1/2,1-mt)`, by analytic uniqueness. This contradicts the
moving branch, without any assumed complex Euler agreement.

**Full scaling profile.** Taylor convergence on a disc larger than one
gives `Σ_k |a_k|(1+k)<∞`, `a_k=0` for `k<m`, and `Σ_{k≥m}a_k=-2`.
Absolute Fubini summation therefore gives

`Σ_p[Φ(p^(-t))-1]p^(-s)=Σ_{k≥m}a_k P(s+kt)`

when `t≥0` and `Re s+mt>1`. At `s=1+tw`, `t>0`, this equals

`2log t-Σ_{k≥m}a_k log(w+k)+Σ_{k≥m}a_k E(1+t(w+k))`.

For compact `K⊂{Re w>-m}`, the shifts lie in a fixed sector strictly
inside `Re(s-1)>0`. The analytic germ bounds `E` close to one; away
from that germ, the real prime sum bounds `P` and the principal
logarithm grows at most linearly in `k`. Thus
`|E(1+t(w+k))|≤C_K+k` for `w∈K`, `0≤t≤1`, `k≥m`.
Weighted absolute summability gives locally uniform convergence of the
last sum to `2D_+(1)`.

The higher prime powers have the common bound `2p^(-2c)` on every
closed half-plane `Re s≥c>1/2`. As `t→0⁺`, they converge jointly to
the constant phase `-1` values, because `Φ(1)=-1`. The identity
`exp(D_-(1)+D_+(1))=ζ(2)` then gives exactly the stated limit `Q`.
The logarithm series converges normally on `Re w>-m`, so `Q` is
analytic and nonzero there; in particular `U(t,1)/t²→Q(0)≠0`.

Separating `k=m` gives `Q(w)=(w+m)^(-ib)B(w)`, with `B` analytic
and nonzero near `-m`. The same two sequences exclude a continuous
extension there and exclude agreement with every polynomial.

## Significance and formal status

The branch location and exponent are determined by the first nonzero
jet of the smoothing profile. Exact quadratic residue collapse is
universal in this class, but its full profile retains an oscillatory
branch. No nonconstant profile in the stated class supplies an actual
joint endpoint specialization.

The positive survivor is the exact universal quadratic profile, together
with actual interior pole germs and preservation of every zeta-zero
multiplicity on the stated half-plane.

Lean namespace: `GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations`.

- `AnalyticSmoothingJet.lean`: `analyticPhase_first_jet`,
  `summable_smoothingTaylorCoefficient_weight`.
- `AnalyticPrimeSmoothing.lean`: `analyticSmoothing_interior_poles`;
  prime decay and the analytic next-order remainder are derived.
- `AnalyticSmoothingBranch.lean`: `analyticSmoothing_branch_rigidity`,
  `analyticSmoothing_no_joint_endpoint_regularization`,
  `analyticSmoothing_isozeric_halfplane`.
- `AnalyticSmoothingScaling.lean`: `analyticSmoothing_universal_quadratic_profile`,
  `tendsto_analyticSmoothing_residue_zero`.

All four new modules and the reused `QuadraticResidueScaling.lean`
passed final direct Lean checks without warnings. Capstone transitive
axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
The new modules are imported by the arithmetic-weight umbrella.

Corpus search found the individual Taylor, analytic-order, and
prime-logarithm ingredients, but no theorem for this smoothing class.
No external novelty claim. B130 remains open.
