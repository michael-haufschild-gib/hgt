# Joint gauge germs have a normal Euler factorization

- **ID:** B130-joint-Euler-normal-form
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Complex normal prime summability](../3-formalized/joint-gauge-germs-force-complex-normal-summability.md) and [linear tangent realization](../3-formalized/admissible-gauge-tangents-are-isozeric-directions.md).

## Target

For uniformly bounded holomorphic prime coordinates `u_p(z)` on a common
disk, with `u_p(0)=1` and actual unit gauge phases on its real diameter,
prove that a jointly holomorphic actual pole regularization exists iff

`Σ_p p^(-σ) sup_{|z|≤r}|u_p(z)-1| < ∞`

for some `r>0` and `1/2<σ<1`.

Construct a normally convergent Euler logarithm difference `H(z,s)`,
jointly holomorphic on a smaller parameter disk times `Re s>σ`, with
`H(0,s)=0`. Every given regularization germ must equal `Z(s)exp(H(z,s))`;
on real parameters, `ζ(s)exp(H(t,s))` must agree with the actual gauge
fibre for `Re s>1`.

## Paper proof

1. Necessity is `joint_gauge_complex_normal_summability`, after shrinking
   the common radius to the Euler agreement neighborhood. It derives the
   central residue from `u_p(0)=1`.
2. For sufficiency, let `b_p=sup_{|z|≤r}|u_p(z)-1|`, with the weighted
   sum finite at `σ∈(1/2,1)`. Cauchy's uniform derivative estimate permits
   a smaller disk on which every `|u_p(z)|≤5/4`. For `Re s>σ`, write
   `d_p(s)=exp(-s log p)`; then `|d_p(s)|≤p^(-σ)≤3/4`.
3. Both `1-d_p` and `1-u_p d_p` lie in the logarithm's slit plane.
   The logarithm is 16-Lipschitz on the disk of radius `15/16` about one.
   Consequently the jointly holomorphic terms
   `L_p(z,s)=log(1-d_p(s))-log(1-u_p(z)d_p(s))` satisfy
   `|L_p(z,s)|≤16 b_p p^(-σ)` on the full product domain. The sum `H=ΣL_p`
   is normally convergent and jointly holomorphic there. Also `H(0,s)=0`.
4. In `Re s>1`, the convergent twisted and untwisted Euler logarithms
   differ term by term by `L_p`. Exponentiating yields
   `ζ(s)exp(H(t,s))=F_{x(t)}(s)` for every real parameter in the disk.
   Hence `W(z,s)=Z(s)exp(H(z,s))` is an actual joint regularization.
5. For uniqueness, choose a product disk on which a given germ `U` and
   `W` are analytic. For each real parameter, the one-variable identity
   theorem extends Euler agreement across the spectral disk. For each
   fixed spectral point, the real parameter interval is an accumulation
   set, so the parameter identity theorem gives `U=W` on the product
   disk. Thus every given joint germ has the same normal form.

## Lean theorem

[`JointEulerFactorization.lean`](../../../../formal/GaloisForLFunctions/ArithmeticWeightTheory/GaugeDeformations/JointEulerFactorization.lean)
formalizes the complete statement:

- `joint_pole_regularization_iff_normal_summability`: exact nonlinear equivalence.
- `exists_jointEuler_normal_form`: one summable majorant on the whole product domain, with joint analyticity of `H` and `Z exp(H)`.
- `jointGaugeRegularization_eq_gaugeFibre`: agreement throughout the complex Euler half-plane.
- `jointDeformationExponent_zero`: `H(0,s)=0` for every `s`.
- `joint_pole_germ_normal_form`: every given joint pole germ is the canonical normal form.

The existing logarithm estimate and product normal-series lemma in
`JointTangentRealization.lean` are now public and reused. Both changed
modules passed final direct Lean checks without warnings. All five
capstone axiom audits contain only `propext`, `Classical.choice`, and
`Quot.sound`.

## Corpus boundary

`JointTangentRealization` constructs the joint logarithm for linear phases
and supplies the logarithm difference bound and two-variable normal-series
lemma. The new result is the arbitrary nonlinear equivalence and the
unique joint normal form. No external novelty claim.

This classifies actual analytic gauge specialization. It supplies neither
a purity family nor B130's arithmetic Stepanov estimate.

[Interior pole persistence and sharp boundary — formalized](bounded-analytic-gauge-paths-preserve-interior-poles.md).
