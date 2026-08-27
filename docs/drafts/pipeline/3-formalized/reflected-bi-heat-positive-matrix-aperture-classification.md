# Reflected bi-heat positive matrix aperture classification

- **ID:** RBH-MAP
- **Stage:** 3-formalized
- **Type:** CROSS-APERTURE MATRIX CLASSIFICATION / NO-GO WITH POSITIVE SURVIVOR
- **Parent:** RBH
- **Lean module:** `GaloisForLFunctions.RHTower.ReflectedBiHeatPositiveMatrixApertureClassification`
- **Frontier-map policy:** read only

## Result

For every actual Xi divisor `ρ` and every aperture `x>0`, the exact
multiplicity-leading norms are

`Lρ(x)=|Aρ| x^((Re ρ-1)/2)` and `Rρ(x)=|Aρ| x^(-Re ρ/2)`,

where `Aρ` is the common nonzero multiplicity-leading coefficient.  For finitely
many apertures `xᵢ>1` and a real matrix `M` whose entries are nonnegative and at
least one of which is positive, set

`E_L(ρ)=Σᵢⱼ Mᵢⱼ Lρ(xᵢ)Lρ(xⱼ)`,
`E_R(ρ)=Σᵢⱼ Mᵢⱼ Rρ(xᵢ)Rρ(xⱼ)`.

The formalized classification is

- `Re ρ>1/2  → E_L(ρ)>E_R(ρ)`;
- `Re ρ<1/2  → E_L(ρ)<E_R(ρ)`;
- `E_L(ρ)=E_R(ρ) ↔ Re ρ=1/2`;
- universal balance on Xi divisor support is equivalent to RH.

No symmetry of `M` is required.  A single positive entry suffices.

## Paper proof

The arbitrary-aperture jet formulas follow from the corpus identity for the
first nonzero derivative and `|x^z|=x^(Re z)` for `x>0`.  Since `Aρ≠0`, its norm
is strictly positive.  At every base `x>1`, strict monotonicity of real powers
turns the scale-order identity

`leftOrder(ρ)-rightOrder(ρ)=Re ρ-1/2`

into a strict pointwise norm ordering.  If positive vectors `aᵢ<bᵢ`, then
`aᵢaⱼ<bᵢbⱼ`; multiplication by nonnegative `Mᵢⱼ` preserves weak order and one
positive entry makes the finite double sum strict.  Apply this in each half
strip.  Equality therefore excludes both open half-strips and is equivalent to
the wall.  Quantifying over Xi divisor support gives RH by the corpus endpoint.

Dependency-closed; no analytic or asymptotic premise remains.

## Lean theorems

- `reflectedBiHeatLeftLeadingJetNorm_eq`
- `reflectedBiHeatRightLeadingJetNorm_eq`
- `reflectedBiHeatRightLeadingJetNorm_lt_left`
- `reflectedBiHeatLeftLeadingJetNorm_lt_right`
- `reflectedBiHeatLeadingJetNorms_eq_iff`
- `finite_positiveMatrix_selfInteraction_lt`
- `reflectedBiHeatMatrixApertureGap_eq_sub`
- `reflectedBiHeatMatrixApertureGap_pos_of_re_gt_half`
- `reflectedBiHeatMatrixApertureGap_neg_of_re_lt_half`
- `reflectedBiHeatMatrixApertureEnergies_eq_iff`
- `riemannHypothesis_iff_reflectedBiHeatPositiveMatrixApertureEnergy_eq`

## No-go and positive survivor

**No-go.** Finite entrywise-nonnegative cross-aperture quadratic mixing cannot
produce RBH balance.  Every term has the same strict orientation off the wall,
so cancellation is impossible.

**Positive survivor.** The aggregate gap has an exact, coefficient-independent
orientation law: its sign is the sign of `Re ρ-1/2`.  It is therefore a robust
multi-aperture RH receiver and horizontal-side detector, strictly stronger than
the earlier single-aperture equality criterion.

Surviving producer space must violate at least one closed hypothesis: signed or
complex oriented couplings, an infinite/singular interaction, nonlinear
cross-channel dynamics not reducible to positive norm products, or a global
source law that forces balance independently of Xi support.

## Novelty audit (through 2026-08-27)

Corpus searches for reflected bi-heat cross-channel, Hermitian/quadratic,
matrix, and multi-aperture reporters found no theorem with this statement.
Primary-source searches located heat-flow and Xi functional-equation work,
including Löffler, *Deformations of Xi(s)=Xi(1-s) and the heat equation*
([arXiv:1510.03416](https://arxiv.org/abs/1510.03416)); D. H. J. Polymath,
*Effective approximation of heat flow evolution of the Riemann xi function*
([arXiv:1904.12438](https://arxiv.org/abs/1904.12438)); Dimitrov, *Lee-Yang
measures and wave functions* ([arXiv:1311.0596](https://arxiv.org/abs/1311.0596));
and Patkowski, *On a Bessel function series related to the Riemann xi function*
([arXiv:2303.16423](https://arxiv.org/abs/2303.16423)).  None states the
multiplicity-leading, finite positive-matrix cross-aperture sign classification.

Novelty priority remains provisional pending expert/database review; theorem
itself is unconditional and formally checked.

## Verification

- Direct `lake env lean` check: passed.
- Targeted module build: passed.
- Axiom audit: all eleven exported theorems use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Umbrella import: wired; full umbrella build intentionally not run.
