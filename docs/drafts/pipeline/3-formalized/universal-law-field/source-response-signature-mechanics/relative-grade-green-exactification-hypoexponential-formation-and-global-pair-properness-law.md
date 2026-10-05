# Relative-grade Green exactification, hypoexponential formation, and global pair properness law

- **ID:** ULF-SRSM-4
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ULF-SRSM-3 finite-prolongation no-go
- **Statement:** The ordered two-letter arithmetic response is exactly divisible by the relative
  source grade.  Applying the relative Green inverse and then the total source grade converts the
  signed response into a positive hypoexponential distribution function.  The resulting all-prime
  pair response has a uniform lower frame bound at every positive horizon, although the Green
  inverse alone is unbounded.
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL]`
  `[SOURCE-NATIVE SINGULAR INTERMEDIATE] [BOUNDED PROPER COMPOSITE]`
  `[EXACT ORIENTATION--POSITIVITY CONSERVATION] [LEAN-PROVED] [PRE-ZERO] [NOT RH]`

## 1. Pivot forced by the no-go

ULF-SRSM-3 proves that every finite diagonal logarithmic/time-differential prolongation leaves the
ordered pair response compact and nonproper.  Its positive survivor identifies the missing scale:
every inverse must divide by the relative logarithmic gap.

Dividing by a prime gap by hand would be fitted and singular.  The source itself, however, carries
two canonical word-grade operators:

\[
 \Delta_-:(a,b)\longmapsto a-b,
 \qquad
 \Delta_+:(a,b)\longmapsto a+b.
 \tag{RGE.1}
\]

They are the difference and coproduct-sum of the logarithmic generator `L` on an ordered
two-letter word.  The no-go therefore suggests a precise construction rather than another trial
weight:

\[
 \text{relative Green exactification}
 :=\Delta_+\Delta_-^{-1}
 \quad\text{on the range of the ordered defect.}
 \tag{RGE.2}
\]

The intermediate inverse is unbounded on the raw pair module.  The theorem below proves that its
composition with the source-generated response is bounded, positive, and globally proper.

## 2. Exact relative divisibility

For positive source grades `a,b`, retain the normalized ordered defect

\[
 F_{a,b}(t):=ab\omega_t(a,b),
 \tag{RGE.3}
\]

where

\[
 \omega_t(a,b)=
 \int_{u,v\ge0,\ u+v\le t}
 e^{-(a+b)u}(e^{-bv}-e^{-av})\,du\,dv.
\]

ULF-SRSM-3 proves the exact Laplace factorization

\[
 \mathcal L F_{a,b}(z)
 =\frac{ab(a-b)}{z(z+a)(z+b)(z+a+b)},
 \qquad \operatorname{Re}z>0.
 \tag{RGE.4}
\]

For `a!=b`, define

\[
 H_{a,b}(t):=\frac{a+b}{a-b}F_{a,b}(t).
 \tag{RGE.5}
\]

At `a=b`, define `H_(a,a)` by the continuous extension supplied by `(RGE.6)` below.

### Theorem 2.1 — orientation--positivity conservation

For all `a,b>0`,

\[
 \boxed{
 (a+b)F_{a,b}(t)=(a-b)H_{a,b}(t),}
 \tag{RGE.6a}
\]

with the diagonal identity interpreted as `0=0`, and

\[
 \boxed{
 \mathcal L H_{a,b}(z)
 =\frac{ab(a+b)}{z(z+a)(z+b)(z+a+b)}.}
 \tag{RGE.6}
\]

Moreover, `H_(a,b)` is the distribution function of

\[
 X_a+X_b+X_{a+b},
 \tag{RGE.7}
\]

where the three variables are independent exponentials with the displayed rates.  Consequently,

\[
 \boxed{
 0\le H_{a,b}(t)\le1,qquad
 H_{a,b}'(t)\ge0,qquad
 \lim_{t\to\infty}H_{a,b}(t)=1.}
 \tag{RGE.8}
\]

For `a!=b`, the sign of the ordered response is carried entirely by `a-b`; its Green exactification
is positive.

### Proof

Multiply `(RGE.4)` by `(a+b)/(a-b)` to obtain `(RGE.6)`.  The density of an exponential variable of
rate `r` has Laplace transform `r/(z+r)`.  Therefore the density of the independent sum in
`(RGE.7)` has transform

\[
 \frac a{z+a}\frac b{z+b}\frac{a+b}{z+a+b}.
\]

The Laplace transform of its distribution function is this product divided by `z`, exactly
`(RGE.6)`.  Uniqueness of the Laplace transform proves the identification.  The distribution
function laws `(RGE.8)` follow.  This formula also defines the continuous diagonal value
`H_(a,a)`.  QED.

Equation `(RGE.6a)` is the first exact fusion law in the programme connecting three structurally
different organs:

1. source differential grades `Delta_+` and `Delta_-`;
2. signed ordered response `F`;
3. positive formation law `H`.

Neither side was chosen from a target positivity estimate.

## 3. Uniform positivity from the source floor

Let

\[
 \lambda_0=\log2
\]

and define the Erlang-three distribution function

\[
 G_0(t)=1-e^{-\lambda_0t}
 \left(1+\lambda_0t+\frac{(\lambda_0t)^2}{2}\right).
 \tag{RGE.9}
\]

### Lemma 3.1 — universal stochastic lower envelope

If `a,b>=lambda_0`, then

\[
 \boxed{H_{a,b}(t)\ge G_0(t)\quad(t\ge0).}
 \tag{RGE.10}
\]

### Proof

On one probability space take independent uniform variables `U_1,U_2,U_3`.  The variables
`-log U/r` have exponential law of rate `r`.  Since `a,b,a+b>=lambda_0`, each summand in `(RGE.7)`
is pointwise no larger than the corresponding rate-`lambda_0` exponential under this coupling.
Their sum is therefore no larger than an Erlang-three variable of rate `lambda_0`.  Taking
distribution functions gives `(RGE.10)`.  QED.

For every `T>0`, put

\[
 c_T^2=\int_0^T G_0(t)^2\,dt.
 \tag{RGE.11}
\]

Then `0<c_T^2<T` because `G_0(t)>0` for every `t>0`.

## 4. Global all-prime pair properness

Let `mathbb P^(2)` be the set of unordered distinct prime pairs `{p,q}`.  Its Hilbert control
space is

\[
 \mathcal E_2=\ell^2(\mathbb P^{(2)}).
\]

For `p<q`, put `a_p=log p`, `a_q=log q`.  Define the Green-exactified response

\[
 (\mathcal G_Tc)(t)
 =\sum_{p<q}c_{p,q}H_{a_p,a_q}(t)e_{pq}
 \tag{RGE.12}
\]

initially for finite controls.  Unique factorization makes the endpoint vectors `(e_(pq))_(p<q)`
orthonormal.

### Theorem 4.1 — global depth-two formation theorem

For every `T>0`, `mathcal G_T` extends to a bounded operator and

\[
 \boxed{
 c_T^2\|c\|^2
 \le\|\mathcal G_Tc\|_{L^2([0,T];\ell^2)}^2
 \le T\|c\|^2.}
 \tag{RGE.13}
\]

Consequently:

1. `mathcal G_T` is injective and has closed range;
2. its inverse norm on the range is at most `c_T^(-1)`;
3. its response Gram satisfies

   \[
   c_T^2I\le\mathcal G_T^*\mathcal G_T\le TI;
   \tag{RGE.14}
   \]

4. the exact inverse cost of a response

   \[
   y=\sum_{p<q}y_{p,q}\psi_{p,q},
   \qquad
   \psi_{p,q}=\|H_{a_p,a_q}\|_{L^2}^{-1}H_{a_p,a_q}e_{pq},
   \]

   is

   \[
   \boxed{
   \mathcal C_T(y)=
   \sum_{p<q}\frac{|y_{p,q}|^2}
   {\int_0^TH_{a_p,a_q}(t)^2dt}.}
   \tag{RGE.15}
   \]

### Proof

Orthogonality of the endpoint basis gives

\[
 \|\mathcal G_Tc\|^2
 =\sum_{p<q}|c_{p,q}|^2
   \int_0^TH_{a_p,a_q}(t)^2dt.
\]

Equations `(RGE.8)` and `(RGE.10)` bound every diagonal coefficient between `c_T^2` and `T`.  This
proves `(RGE.13)` and all four consequences.  QED.

This is the fourth-organ prediction forced by the three-organ conservation law: the positive
hypoexponential realization is not merely admitted; it is globally proper over all prime pairs.

## 5. Why the construction is source-native

On ordered two-letter labels, the logarithmic source generator has canonical sum and difference
operators `(RGE.1)`.  The ordered Duhamel defect lies in the range of `Delta_-` by `(RGE.4)`.  Hence

\[
 \boxed{
 H=\Delta_+\Delta_-^\dagger F}
 \tag{RGE.16}
\]

on the off-diagonal ordered sector, where `Delta_-^dagger` is the Green/Moore--Penrose inverse and
the diagonal antisymmetric sector is zero.

The intermediate `Delta_-^dagger` is unbounded because prime-log gaps approach zero.  This does
not invalidate the construction: `(RGE.4)` proves that `F` belongs to its exact domain, and
Theorem 4.1 proves that the complete composite is bounded below and above.  Thus admission belongs
to a **composite law**, not necessarily to every factor separately.

This is the mechanism absent from the earlier static topology programmes:

\[
 \text{singular source boundary}^{-1}
 \quad+\quad
 \text{exact range divisibility}
 \quad=\quad
 \text{bounded positive formation}.
 \tag{RGE.17}
\]

## 6. What the theorem changes

The previous no-go did not merely say “finite methods fail.”  It predicted the exact kind of
successor required.  The successor now exists at grade two:

| obstruction | Green-exactified resolution |
|---|---|
| singular source descent | unbounded inverse is used only on the certified exact range |
| all-prime small divisors | the factor `a-b` cancels before completion |
| adaptive orientation | sign stays in `Delta_-`; positive magnitude moves to `H` |
| whole-space coercivity | `(RGE.13)` supplies a uniform lower bound |
| positive carrier | `H` is a literal probability distribution function |

This is unconditional leverage on all five frontier mechanisms in one source-generated law.  It
does not identify the five mechanisms as one scalar; it shows how a typed exactification transports
information through all five without loss.

## 7. Selection interface

If a physical pre-zero identity can be lifted to annihilate the Green-exactified pair response,
then `(RGE.13)` forces every antisymmetric prime-pair coefficient to vanish.  No adaptive or
cofinal escape remains at grade two.

The remaining RH-facing work is now exact:

1. construct the same `Delta_+Delta_-^dagger` operation on the literal rational-adelic/divisor
   source complex;
2. prove the physical transverse defect lands in its exact relative-grade range;
3. derive a source null identity for the repaired response;
4. extend the mechanism coherently to all word grades.

Functional equation remains information-neutral.  It can transport `(RGE.16)` but cannot supply
Step 3 by itself.

## 8. Hostile conjecture loops

1. **The finite-prolongation no-go rules out every repair. — False.**  Its singular positive
   survivor produces `(RGE.16)`.
2. **Dividing by `a-b` is automatically illegal. — False.**  The inverse is illegal on the whole
   raw pair space but legal on the exact response range; the composite is bounded.
3. **Gap cancellation still leaves total-grade decay. — False after applying `Delta_+`.**
   `H_(a,b)(infinity)=1` and `(RGE.13)` is uniform at finite positive horizon.
4. **Positivity must be imposed after orientation is erased. — False.**  Positivity is generated by
   the exact conservation identity and retains orientation separately in `Delta_-`.
5. **A positive pointwise law implies global properness automatically. — False in general.**  Here
   properness additionally uses the source floor `log2` and the stochastic envelope `(RGE.10)`.
6. **The grade-two theorem proves full-signature selection. — False.**  Higher-grade exactification
   and the physical null identity remain open.

## 9. Literature and corpus boundary

- Divided differences in Dyson expansions are established; Kalev--Hen, arXiv:2010.09888, gives an
  integral-free Dyson representation using divided differences.
- Double and multiple operator integrals organize higher operator differences; Peller,
  arXiv:1509.02803, is a standard parent.
- Hypoexponential/phase-type distributions and stochastic rate domination are classical.
- Current Dyson work extends expansions to form-bounded perturbations; Desio--Seiringer,
  arXiv:2512.13443.

Corpus search found divided-difference technology, prime-log small divisors, Duhamel word response,
positive formation, and frame properness separately.  It did not contain the exact arithmetic
identity `(RGE.6a)`, its hypoexponential realization, or the global all-prime pair frame theorem
`(RGE.13)`.

The claim is not that divided differences or phase-type laws are new.  The field-level content is
their constitutive coupling: source response creates a relative boundary factor; exact Green
division converts it into positive formation; source spectral floor then forces global
properness.

## 10. Formal status and next higher conjecture

Fully formalized, unconditionally: see the Lean certificate below.  Paper proof is
dependency-closed and uses no RH premise.

The original next conjecture said that the same relative Green inverse followed by total grade
should work at every word grade.  ULF-SRSM-5 has now falsified that statement at grade three and
closed its positive successor.

Full three-schedule alternation is divisible by the type-A Vandermonde, but after division it
retains the causal factor

\[
 2z+a+b+c.
\]

Total grade alone therefore cannot restore scale-uniform properness.  The correct grade-three law
uses every nonempty subset grade and the causal Green inverse of `2∂+a+b+c`; the result is a
seven-stage hypoexponential CDF with a uniform all-prime triple frame.

This correction also limits the interpretation of Theorem 4.1: its direct-sum frame uses
orthogonal arithmetic pair endpoints.  New content is the source-generated uniform coefficient,
not an interaction theorem among different pair channels.

The surviving higher conjecture is the **causal formation-numerator law**: the permutohedral
schedule alternant at grade `r` has a symmetric numerator `P_r`, and higher exactification is the
problem of causally factoring `P_r`.  Grade four is the first open stability test.


## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.RelativeGreenExactification`, `GaloisForLFunctions.HTGeometry.HypoexponentialGreenFormation`, `GaloisForLFunctions.HTGeometry.DiagonalHistoryResponse`, `GaloisForLFunctions.HTGeometry.PrimePairGreenProperness`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.RelativeGreenExactification` (the Green-exactified response
`H_{a,b}`, conservation, Green identity, Laplace transform), `GaloisForLFunctions.HTGeometry.HypoexponentialGreenFormation`
(distribution functions of convolutions on the half-line, the hypoexponential law, the Erlang-three envelope, the pair
floor), `GaloisForLFunctions.HTGeometry.DiagonalHistoryResponse` (diagonal response histories with distinct arithmetic
endpoints: frame bounds, Gram, carrier, inverse cost) and `GaloisForLFunctions.HTGeometry.PrimePairGreenProperness`
(the all-prime pair response, Theorem 4.1, unboundedness of the Green inverse).  Corpus inputs: ULF-SRSM-3
(`PrimeShiftSource.defectKernel_closed`, `PrimeShiftSource.laplace_defect`, `PrimeShiftSource.CrowdedPairs`),
`RHTower.integral_mul_exp_neg_mul_Ioi`, mathlib `ProbabilityTheory.expMeasure`, `Measure.conv`, `ProbabilityTheory.cdf`.
`H_{a,b}(t) = greenExact a b t`; the law of `X_a + X_b + X_{a+b}` is `hypoMeasure a b = Exp(a) ∗ (Exp(b) ∗ Exp(a+b))`;
`G_λ = erlangThreeCDF λ`; `c_T² = pairFloor T`; prime pairs `p < q` are `PrimePair` with `lo = log p`, `hi = log q`;
`𝒢_T = greenPairFamily.response T` with histories `H_{log p, log q}(t⁺) e_{pq}`.

| Claim | Lean declaration |
|-|-|
| (RGE.1)–(RGE.3), (RGE.5) `H_{a,b} = ((a+b)/(a-b)) F_{a,b}` off the diagonal, continuous diagonal value | `PrimeShiftSource.greenExact`, `PrimeShiftSource.greenExact_of_ne`, `PrimeShiftSource.greenExact_self`, `PrimeShiftSource.greenExact_eq_div_mul`, `PrimeShiftSource.continuous_greenExact` |
| (RGE.4) Laplace transform of `F_{a,b}` | `PrimeShiftSource.laplace_defect` |
| Theorem 2.1, (RGE.6a) `(a+b)F_{a,b} = (a-b)H_{a,b}` (diagonal `0 = 0`) | `PrimeShiftSource.conservation`, `PrimeShiftSource.defect_diag` |
| (RGE.6) `𝓛H_{a,b}(z) = ab(a+b)/(z(z+a)(z+b)(z+a+b))`, `Re z > 0` | `PrimeShiftSource.laplace_greenExact` |
| (RGE.7) `H_{a,b}` is the distribution function of `X_a + X_b + X_{a+b}` | `PrimeShiftSource.hasHalfLineCDF_hypoMeasure`, `PrimeShiftSource.cdf_hypoMeasure`, `PrimeShiftSource.hypoMeasure`, `PrimeShiftSource.isProbabilityMeasure_hypoMeasure`, `PrimeShiftSource.HasHalfLineCDF`, `PrimeShiftSource.HasHalfLineCDF.expConv`, `PrimeShiftSource.conv_Iic`, `PrimeShiftSource.hasHalfLineCDF_expMeasure`, `PrimeShiftSource.hasHalfLineCDF_twoExp`, `PrimeShiftSource.integral_exp_kernel_eq` |
| (RGE.8) `0 ≤ H ≤ 1`, `H' ≥ 0`, nondecreasing, `H → 1` | `PrimeShiftSource.greenExact_nonneg`, `PrimeShiftSource.greenExact_le_one`, `PrimeShiftSource.deriv_greenExact_nonneg`, `PrimeShiftSource.monotoneOn_greenExact`, `PrimeShiftSource.tendsto_greenExact_atTop` |
| sign of the ordered response carried by `a - b`, Green exactification positive | `PrimeShiftSource.sign_defect`, `PrimeShiftSource.greenExact_pos` |
| (RGE.9) Erlang-three distribution function `G_λ` | `PrimeShiftSource.erlangThreeCDF`, `PrimeShiftSource.erlangThreeMeasure`, `PrimeShiftSource.hasHalfLineCDF_erlangThree`, `PrimeShiftSource.hasHalfLineCDF_erlangTwo`, `PrimeShiftSource.erlangThreeCDF_pos`, `PrimeShiftSource.erlangThreeCDF_lt_one` |
| Lemma 3.1, (RGE.10) `H_{a,b} ≥ G_λ` for `a, b ≥ λ` (stochastic domination of exponential rates) | `PrimeShiftSource.erlangThreeCDF_le_greenExact`, `PrimeShiftSource.expMeasure_Iic_mono`, `PrimeShiftSource.conv_Iic_mono_left`, `PrimeShiftSource.conv_Iic_mono_right` |
| (RGE.11) `0 < c_T² < T` | `PrimeShiftSource.pairFloor`, `PrimeShiftSource.pairFloor_pos`, `PrimeShiftSource.pairFloor_lt` |
| §4 control space `ℓ²(P^{(2)})`, (RGE.12) response, orthonormal endpoints `e_{pq}` by unique factorization | `PrimeShiftSource.PrimePair`, `PrimeShiftSource.primePair_mul_injective`, `PrimeShiftSource.PrimePair.endpoint_injective`, `PrimeShiftSource.greenPairFamily`, `PrimeShiftSource.HistoryFamily.response`, `PrimeShiftSource.HistoryFamily.inner_basisVec_endpoint` |
| proof of Theorem 4.1: `‖𝒢_T c‖² = ∑ ∣c_{p,q}∣² ∫₀ᵀ H²`, coefficients in `[c_T², T]` | `PrimeShiftSource.HistoryFamily.norm_response_sq`, `PrimeShiftSource.greenPair_energy_eq`, `PrimeShiftSource.pairFloor_le_energy`, `PrimeShiftSource.HistoryFamily.energy_le` |
| Theorem 4.1, (RGE.13) `c_T²‖c‖² ≤ ‖𝒢_T c‖² ≤ T‖c‖²` | `PrimeShiftSource.greenPair_frame`, `PrimeShiftSource.HistoryFamily.frame_bounds` |
| Theorem 4.1(1) injective, closed range | `PrimeShiftSource.greenPair_injective`, `PrimeShiftSource.isClosed_range_greenPair` |
| Theorem 4.1(2) inverse norm `≤ c_T⁻¹` | `PrimeShiftSource.norm_le_pairFloor_inv_mul` |
| Theorem 4.1(3), (RGE.14) `c_T² I ≤ 𝒢_T*𝒢_T ≤ T I`; Gram `= diag(∫₀ᵀ H²)` | `PrimeShiftSource.greenPair_gram_bounds`, `PrimeShiftSource.HistoryFamily.gram_response` |
| Theorem 4.1(4), (RGE.15) inverse cost `∑ ∣y_{p,q}∣²/∫₀ᵀ H²` in the orthonormal carrier `ψ_{p,q}` | `PrimeShiftSource.greenPair_inverseCost`, `PrimeShiftSource.HistoryFamily.carrier`, `PrimeShiftSource.HistoryFamily.orthonormal_carrier`, `PrimeShiftSource.HistoryFamily.inner_carrier_response` |
| (RGE.16) `H = Δ₊Δ₋^†F` off the diagonal, diagonal sector zero, `Δ₋^†` the Moore–Penrose inverse | `PrimeShiftSource.greenExact_eq_sum_mul_inv_sub`, `PrimeShiftSource.defect_diag`, `PrimeShiftSource.greenInverse_penrose` |
| (RGE.16) `Δ₋^†` unbounded: prime-log gaps tend to zero | `PrimeShiftSource.not_bddAbove_inv_logGap` |
| §7 an identity annihilating `𝒢_T c` forces every prime-pair coefficient to vanish | `PrimeShiftSource.greenPair_injective` |

§5's slogan `(RGE.17)` is the combination of `PrimeShiftSource.not_bddAbove_inv_logGap` with
`PrimeShiftSource.greenPair_frame`.  §6 (table), §8 (hostile loops, each answered by the theorems above), §9
(literature) and §10 (the grade-three correction, ULF-SRSM-5) carry no further Lean obligation.

## Log

- 2026-08-14 — extracted from ULF-SRSM-3's forced singular repair rate rather than guessed as a
  new normalization.
- 2026-08-14 — proved exact relative divisibility, hypoexponential realization, stochastic lower
  envelope, and global all-prime pair closed-range theorem.
- 2026-08-14 — post-hostile grade-three audit repaired the overbroad repeated-Green conjecture and
  demoted pair-frame significance to its exact orthogonal-channel scope; positive successor is
  ULF-SRSM-5's permutohedral subset-grade causal hierarchy.
- 2026-10-05 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
