# Xi--Hurwitz constraint-orientation product law

- **ID:** `xi-hurwitz-constraint-orientation-product-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / RH-EQUIVALENT VALUE LAW
- **Scientific status:** `[PROVED IN LEAN] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`

## Main law

Let `Z_Xi` be the actual divisor support of the completed Xi function and put

\[
  q(\rho)=\exp(-2\pi i\rho),
  \qquad
  H_\rho(a)=\widetilde\zeta(\rho,a).
\]

Then the complete Xi-indexed Hurwitz family is unconditionally differentially free,

\[
  (H_\rho)_{\rho\in Z_\Xi}
  \text{ is differentially algebraically independent over }\mathbb C(a),
\]

and the same character value that classifies this differential matroid carries an exact RH
orientation:

\[
  \mathrm{RH}
  \quad\Longleftrightarrow\quad
  q(\rho)=-\exp(2\pi\operatorname{Im}\rho)
  \quad\text{for every }\rho\in Z_\Xi.
\]

Equivalently, RH says that the character image of the Xi divisor lies on the negative real ray.
The modulus identity

\[
  |q(s)|=\exp(2\pi\operatorname{Im}s)
\]

is unconditional, so RH is exactly the missing orientation, not an amplitude condition.

This orientation has a canonical scalar compression.  Put

\[
  D(\rho)=\frac{\operatorname{Im}(q(\rho))^2}{|q(\rho)|^2}
          =\sin^2(2\pi\operatorname{Re}\rho),
  \qquad
  w(\rho)=\frac{\operatorname{ord}_\rho\Xi}
  {|\rho-\tfrac12|^2},
\]

and

\[
  \mathcal E_\Xi=\sum_{\rho\in Z_\Xi}w(\rho)D(\rho).
\]

The series is absolutely convergent, every summand is nonnegative, and

\[
  \mathrm{RH}\iff\mathcal E_\Xi=0,
  \qquad
  \neg\mathrm{RH}\iff\mathcal E_\Xi>0
  \iff \exists\rho\in Z_\Xi:\operatorname{Re}\rho\ne\tfrac12.
\]

Any such witness supplies the quantitative lower bound

\[
  \frac{\operatorname{ord}_\rho\Xi}{|\rho-\tfrac12|^2}
  \sin^2(2\pi\operatorname{Re}\rho)\le \mathcal E_\Xi.
\]

The strengthened formal capstone is `xi_hurwitz_scalar_constraint_orientation_product_law` in
`formal/GaloisForLFunctions/RHTower/XiHurwitzOrientationEnergy.lean`.

## Why this is a coupling theorem

The character `q` is not an auxiliary reparameterization introduced only for RH.

1. For every finite nonintegral exponent family, equality of `q` values is exactly equality modulo
   `ℤ`, and these fibers are exactly the dependent blocks of the Hurwitz differential matroid.
2. On the Xi divisor, `q` is injective because every zero lies in the open critical strip.
3. Functional-equation reflection `s -> 1-conj(s)` becomes complex conjugation of `q(s)`.
4. RH is therefore exactly conjugation-fixity of the complete character image; the open-strip
   condition selects the negative, rather than positive, real ray.
5. The modulus of `q` records zero height, so the RH chamber has the exact value
   `q(ρ)=-exp(2π Im ρ)`, not merely an unspecified real sign.

Thus one value controls both axes: its equality fibers determine the differential constraints, and
its conjugation orientation determines RH.

## Positive Vandermonde chamber

The additive-saturation proof of Hurwitz differential independence separates monodromy labels by
Vandermonde matrices in the values `q(ρ)`.  Unconditionally those matrices are nonsingular.  Under
RH, if `ρ_0,...,ρ_{n-1}` are ordered by increasing imaginary part, then

\[
  r_j=-q(\rho_j)=\exp(2\pi\operatorname{Im}\rho_j)
\]

is a strictly increasing positive real sequence and

\[
  \det(r_j^i)_{0\le i,j<n}
  =\prod_{i<j}(r_j-r_i)>0.
\]

This is formalized as `xiHurwitzMonodromy_vandermonde_det_pos_real_of_rh`.  It upgrades the exact
separator used by the HGT proof from nonzero over `ℂ` to a canonical positive real chamber under
RH.

## Positivity compression and concrete witnesses

The character defect vanishes at a zero exactly when the centered reciprocal-square spectral
coordinate

\[
  \lambda_\rho=-(\rho-\tfrac12)^{-2}
\]

is real.  Consequently \(\mathcal E_\Xi=0\) discharges the existing RH hypotheses of the complete
central trace--Hankel cone, all leading central Hankel determinants, and the full square-summable
Xi Weil polarization.  Classical logic gives three equivalent witness-existence statements:

\[
\begin{aligned}
  \mathcal E_\Xi>0
  &\iff \exists p\in\mathbb R[X]:
       \operatorname{Re}\mathcal Q_\Xi(p)<0,\\
  &\iff \exists n:\det H_n\le 0,\\
  &\iff \exists F:\ \|F\|_{\Xi,2}<\infty\ \text{ and }\
       \operatorname{Re}[F,F]_\Xi<0.
\end{aligned}
\]

These existential equivalences do not compute a witness from the scalar value.  The constructive
local statement is sharper: given an explicit off-line divisor point `ρ`, the function
`xiHurwitzExplicitWeilSignTest ρ` is an explicit conjugate-pair sign test, is square-summable, and
has strictly negative Weil square; the same `ρ` supplies its displayed positive lower bound for
\(\mathcal E_\Xi\).  These results are proved in
`XiHurwitzOrientationEnergyConsumers.lean`.

## Canonical Hilbert negative sector

On the multiplicity-exact Xi zero-copy space define the signed coordinate

\[
  v_\Xi(\rho,j)=
  \frac{\operatorname{Im}q(\rho)}
  {|q(\rho)|\,|\rho-\tfrac12|}.
\]

This is an actual \(\ell^2\) vector and Lean proves the exact norm identity

\[
  \|v_\Xi\|_2^2=\mathcal E_\Xi.
\]

Let \(J\) be the unconditional unitary involution induced by critical-line reflection on the same
zero-copy Hilbert space, and put

\[
  \mathcal W(v)=\operatorname{Re}\langle Jv,v\rangle.
\]

Functional-equation reflection conjugates the Hurwitz character, hence

\[
  Jv_\Xi=-v_\Xi,
  \qquad
  \mathcal W(v_\Xi)=-\|v_\Xi\|_2^2=-\mathcal E_\Xi.
\]

Therefore the complete Weil positivity criterion compresses to one canonical HGT-derived vector:

\[
  \mathrm{RH}
  \iff \mathcal W(v_\Xi)\ge0
  \iff \mathcal W(F)\ge0\ \text{for every square-summable }F.
\]

This is unconditional.  The closure relation is now also unconditional: normalized regular
Cauchy vectors in the analytically continued prime--Gamma domain exhaust each exact multiplicity
fiber, and the fiber expansion sums to `v_Xi`.  Consequently

\[
v_\Xi\in\overline{\operatorname{span}
  (\text{continued prime--Gamma Cauchy vectors})}.
\]

There is therefore a sequence of finite algebraic source vectors `V_n` with

\[
V_n\to v_\Xi,
\qquad
\mathcal W(V_n)\to-\mathcal E_\Xi.
\]

The sole remaining mathematical input on this chain is source positivity.  It is enough to prove
eventual nonnegativity along this one approximating sequence; positivity of the entire
square-summable Weil domain is not an input.

This last shrink is formalized as an exact criterion: the sequence may be chosen unconditionally
so that RH is equivalent to eventual nonnegativity of its Weil values.  Thus the open value problem
is countable and cofinal, rather than universal over the continued Cauchy source domain.

## Lean theorem chain

- `monoScalar_feReflection`
- `openCriticalStrip_monoScalar_conj_fixed_iff`
- `monoScalar_norm_eq_height`
- `monoScalar_eq_neg_height_of_re_eq_half`
- `xiHurwitzMonodromyCharacter_injective`
- `xi_zero_hurwitz_differentialIndependent_all`
- `riemannHypothesis_iff_xiHurwitzNegativeCharacterChamber`
- `riemannHypothesis_iff_xiHurwitzMonodromyCharacter_eq_neg_height`
- `xiHurwitzMonodromy_vandermonde_det_pos_real_of_rh`
- `xi_hurwitz_constraint_orientation_product_law`
- `xiHurwitzOrientationDefect_eq_sin_sq`
- `xiHurwitzOrientationEnergyTerm_summable`
- `riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero`
- `xiHurwitzOrientationEnergy_pos_iff_exists_offCriticalZero`
- `xiHurwitzOrientationEnergy_pos_iff_exists_traceHankel_negative`
- `xiHurwitzOrientationEnergy_pos_iff_exists_hankelDet_nonpos`
- `xiHurwitzOrientationEnergy_pos_iff_exists_weil_negativeSquare`
- `xiHurwitz_offCritical_constructive_energy_weil_witness`
- `xi_hurwitz_scalar_constraint_orientation_product_law`
- `norm_sq_xiHurwitzOrientationVector`
- `riemannHypothesis_iff_xiHurwitzOrientationVector_eq_zero`
- `xiWeilLineConjLp_xiHurwitzOrientationVector`
- `xiWeilHilbertQuadratic_xiHurwitzOrientationVector`
- `riemannHypothesis_iff_xiHurwitzOrientationVector_weil_nonneg`
- `xiHurwitzOrientationVector_weil_nonneg_iff_fullWeil_nonneg`
- `riemannHypothesis_of_cauchyCore_nonneg_of_orientationVector_mem`
- `xiHurwitzOrientationVector_mem_continuedCauchyHilbertSubspace`
- `exists_continuedCauchyCore_tendsto_xiHurwitzOrientationVector`
- `xiHurwitzOrientationEnergy_continuedCauchy_reconstruction`
- `exists_continuedCauchyCore_weil_negative_of_orientationEnergy_pos`
- `exists_continuedCauchyCore_close_weil_lt_neg_half_energy`
- `riemannHypothesis_of_cauchyCore_nonnegative`
- `xiWeilHilbertQuadratic_nonneg_of_riemannHypothesis`
- `exists_continuedCauchyCore_sequence_eventually_nonnegative_iff_riemannHypothesis`

## RH leverage

The prior Xi-zero corollary was only a rigidity endpoint: it said that distinct zeros generate no
Hurwitz differential relation.  The present theorem adds an RH-equivalent orientation on the exact
same monodromy values and ties it to the Vandermonde separator already used by the proof.

- **Structural RH leverage:** 93/100.  The trace-class scalar is now the norm square of a canonical
  HGT-derived vector in the existing Xi Hilbert carrier; that vector spans an exact negative Weil
  sector, and positivity on it is equivalent to full Weil positivity and RH.
- **Direct proof closure:** 82/100.  The Hilbert-closure/value-relation face is discharged.  The
  source-to-RH passage is reduced to a sign theorem for finite continued prime--Gamma Cauchy
  values along one approximating sequence.  That sign theorem is not proved.
- **Positive remaining problem:** derive the negative-real/positive-Vandermonde character chamber
  from source-defined Euler--Gamma constraints, without assuming zero locations.  This is a precise
  value target rather than an untyped zero-to-function bridge.

## Novelty boundary

The parent literature separately contains spectral-variable differential transcendence, Lerch
monodromy, complex-order polygamma functions, positive-integer Hurwitz algebras, and
spectral-variable universality.  No located source identifies the Hurwitz shift differential
matroid with `ℂ/ℤ`, indexes its complete free family by the actual Xi divisor, or proves the exact
RH character law, scalar orientation energy, and its simultaneous trace--Hankel/Weil witness
dichotomy.  Detailed references and distinctions are recorded in
`hurwitz-nonintegral-residue-partition-differential-matroid-law.md`.  Scientific novelty remains
provisional pending independent specialist review.

## Verification

- The exact module compiles with the repository Lean toolchain.
- The capstone uses the concrete continued Hurwitz function and concrete upper-end meromorphic
  differential field over `ℂ(a)`.
- No `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration occurs in the theorem
  chain.
- Axiom and lint audits are required after each subsequent edit before publication promotion.
