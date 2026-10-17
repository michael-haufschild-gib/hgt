import GaloisForLFunctions.RHTower.CHMDStationaryNodalDecompositionAndPrimeShiftPositivity
import GaloisForLFunctions.RHTower.CHMDExactParityBoundStateDimensionAndShiftedThetaOrthogonality

/-!
# Eigenvector Cardinal Readouts, Four-Term Nodal Edge Decomposition, and Spectral Projection of `sourceEnergy`

This module unifies the stationary/prime-shift nodal decomposition of
`CHMDStationaryNodalDecompositionAndPrimeShiftPositivity` with the cardinal/shifted-theta pairing
laws of `CHMDExactParityBoundStateDimensionAndShiftedThetaOrthogonality`:

1. **Four-Term ($2 \times 2$) Archimedean/Prime $\times$ Envelope/Nodal Decomposition of Edge Energy**:
   For every $p \in \mathrm{SourceGraph}$, the total jump energy $\|p.\mathrm{val}.\mathrm{snd}\|^2$
   splits into a $2 \times 2$ matrix of four nonnegative quantities:
   $$\|p.\mathrm{val}.\mathrm{snd}\|^2
     = \|(\operatorname{fullGroundEquiv}(\operatorname{absGraph} p)).\mathrm{val}.\mathrm{snd}\|^2
       - 4\,\langle (\operatorname{fullGroundEquiv}(\operatorname{posGraph} p)).\mathrm{val}.\mathrm{snd},
           (\operatorname{fullGroundEquiv}(\operatorname{negGraph} p)).\mathrm{val}.\mathrm{snd}\rangle_{\mathbb{R}}
       + \|\operatorname{primeDifference}((\operatorname{absGraph} p).\mathrm{val}.\mathrm{fst})\|^2
       + 4\,\langle \operatorname{primeShiftOperator}((\operatorname{posGraph} p).\mathrm{val}.\mathrm{fst}),
           (\operatorname{negGraph} p).\mathrm{val}.\mathrm{fst}\rangle_{\mathbb{R}},$$
   with row sums $\|(\operatorname{absGraph} p).\mathrm{val}.\mathrm{snd}\|^2 \ge 0$ and
   $-4\,\operatorname{sourcePair}(\operatorname{posGraph} p, \operatorname{negGraph} p) \ge 0$, and
   column sums $\|(\operatorname{fullGroundEquiv} p).\mathrm{val}.\mathrm{snd}\|^2 \ge 0$ and
   $\|\operatorname{primeDifference}(p.\mathrm{val}.\mathrm{fst})\|^2 \ge 0$.
   For every eigenvector $\operatorname{resolvent} w = \mu \cdot w$ ($\mu > 0$) with
   $p = \operatorname{rieszLift} w$, this yields the exact spectral-gap / nodal-deficit identity:
   $$\frac{1 - \mu}{\mu}\,\|p.\mathrm{val}.\mathrm{fst}\|^2
     = \|(\operatorname{absGraph} p).\mathrm{val}.\mathrm{snd}\|^2
       - 4\,\operatorname{sourcePair}(\operatorname{posGraph} p, \operatorname{negGraph} p).$$

2. **Primitive Ground Subtraction `primGraph` and the Odd-to-Even Primitive Contraction Bridge**:
   Subtracting the ground component $2\langle q.\mathrm{fst}, \operatorname{oneL}\rangle\,\operatorname{constantLift} 1$
   defines $\operatorname{primGraph} q \in \mathrm{SourceGraph}$, which preserves the edge coordinate
   $(\operatorname{primGraph} q).\mathrm{snd} = q.\mathrm{snd}$, projects the source coordinate onto
   $(\mathbb{R} \cdot \operatorname{oneL})^\perp$, and satisfies
   $\operatorname{sourceEnergy}(\operatorname{primGraph} q) = \operatorname{weilForm} q$ on the even
   sector.

3. **Mass-Space Fourier/Cosine Readouts and Eigenvector Cardinal & Translated-Cardinal Pairing Laws**:
   Every eigenvector $\operatorname{resolvent} w = \mu \cdot w$ satisfies explicit pairing identities
   against `CardinalGraphFrame a`, the translated cardinal frames `exists_translatedCardinalFrame`,
   and the odd polar family `oddPolarVectorAt a ha`. Moreover, every translated cardinal frame
   vanishes at both polar points $\pm i/2$ and is orthogonal in `MassSpace` to both `oneL` and
   `tanhL`. Every threshold eigenvector at $\mu = 1/2$ is orthogonal to both `oneL` and `tanhL` and
   has vanishing Fourier readout at every $\Xi$-zero.

4. **Exact Finite-Family Eigenvector Projection Decomposition of `sourcePair` and `sourceEnergy`**:
   For any finite orthonormal family $\{w_i\}_{i=1}^m$ of eigenvectors
   $\operatorname{resolvent} w_i = \mu_i \cdot w_i$ ($\mu_i \ne 0$), lifting via
   $e_i = \mu_i^{-1}\,\operatorname{rieszLift} w_i \in \mathrm{SourceGraph}$ splits every
   $q \in \mathrm{SourceGraph}$ into $q = q_{\mathrm{proj}} + q_{\mathrm{rem}}$ with
   $q_{\mathrm{rem}}.\mathrm{fst} \perp \operatorname{span}\{w_i\}$ and
   $$\operatorname{sourceEnergy}(q)
     = -\sum_{i=1}^m \frac{2\mu_i - 1}{\mu_i}\,\langle w_i, q.\mathrm{val}.\mathrm{fst}\rangle_{\mathbb{R}}^2
       + \operatorname{sourceEnergy}(q_{\mathrm{rem}}).$$
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace BigOperators ComplexConjugate
noncomputable section

namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump CHMDTranslation ThetaSourceWard

/-! ## Section 1: Four-Term ($2 \times 2$) Archimedean/Prime $\times$ Envelope/Nodal Decomposition of Edge Energy -/

theorem primeDiagonal_sub_primeShift_eq_primeGenerator :
    primeDiagonalOperator - primeShiftOperator = primeGenerator := by
  unfold primeShiftOperator
  abel

theorem inner_primeDiagonal_sub_primeShift (u v : MassSpace) :
    ⟪primeDiagonalOperator u, v⟫_ℝ - ⟪primeShiftOperator u, v⟫_ℝ =
      ⟪primeDifference u, primeDifference v⟫_ℝ := by
  rw [← inner_sub_left, ← sub_apply,
    primeDiagonal_sub_primeShift_eq_primeGenerator, inner_primeGenerator]

theorem inner_primeDiagonal_sub_primeShift_self (u : MassSpace) :
    ⟪primeDiagonalOperator u, u⟫_ℝ - ⟪primeShiftOperator u, u⟫_ℝ =
      ‖primeDifference u‖ ^ 2 := by
  rw [inner_primeDiagonal_sub_primeShift, real_inner_self_eq_norm_sq]

theorem inner_primeDiagonal_sub_primeShift_self_nonneg (u : MassSpace) :
    0 ≤ ⟪primeDiagonalOperator u, u⟫_ℝ - ⟪primeShiftOperator u, u⟫_ℝ := by
  rw [inner_primeDiagonal_sub_primeShift_self]
  exact sq_nonneg _

/-- **Bilinear Relationship Between Stationary Edge Pairing and Archimedean Edge Pairing**:
for all `p, q : SourceGraph`,
`⟪(graphArchEquiv p).val.snd, (graphArchEquiv q).val.snd⟫_ℝ = ⟪(fullGroundEquiv p).val.snd, (fullGroundEquiv q).val.snd⟫_ℝ + ⟪groundPotentialOperator p.val.fst, q.val.fst⟫_ℝ`. -/
theorem inner_graphArchEquiv_snd_eq_fullGroundEquiv_add_groundPotential (p q : SourceGraph) :
    ⟪(graphArchEquiv p).val.snd, (graphArchEquiv q).val.snd⟫_ℝ =
      ⟪(fullGroundEquiv p).val.snd, (fullGroundEquiv q).val.snd⟫_ℝ +
        ⟪groundPotentialOperator p.val.fst, q.val.fst⟫_ℝ := by
  have h := archGround_inner_decomposition (graphArchEquiv p) (graphArchEquiv q)
  have hp : archSourceMap (graphArchEquiv p) = p.val.fst := graphArchEquiv_source p
  have hq : archSourceMap (graphArchEquiv q) = q.val.fst := graphArchEquiv_source q
  have hp' : (graphArchEquiv p).val.fst = p.val.fst := graphArchEquiv_source p
  have hq' : (graphArchEquiv q).val.fst = q.val.fst := graphArchEquiv_source q
  have hfp : (fullGroundEquiv p).val.fst = p.val.fst := fullGroundEquiv_source p
  have hfq : (fullGroundEquiv q).val.fst = q.val.fst := fullGroundEquiv_source q
  change ⟪graphArchEquiv p, graphArchEquiv q⟫_ℝ =
    ⟪fullGroundEquiv p, fullGroundEquiv q⟫_ℝ +
      ⟪groundPotentialOperator (archSourceMap (graphArchEquiv p)),
        archSourceMap (graphArchEquiv q)⟫_ℝ at h
  rw [hp, hq, Submodule.coe_inner, WithLp.prod_inner_apply,
    Submodule.coe_inner, WithLp.prod_inner_apply] at h
  change ⟪(graphArchEquiv p).val.fst, (graphArchEquiv q).val.fst⟫_ℝ +
      ⟪(graphArchEquiv p).val.snd, (graphArchEquiv q).val.snd⟫_ℝ =
    (⟪(fullGroundEquiv p).val.fst, (fullGroundEquiv q).val.fst⟫_ℝ +
      ⟪(fullGroundEquiv p).val.snd, (fullGroundEquiv q).val.snd⟫_ℝ) +
      ⟪groundPotentialOperator p.val.fst, q.val.fst⟫_ℝ at h
  rw [hp', hq', hfp, hfq] at h
  linarith

/-- **Bilinear Edge Decomposition into Archimedean and Prime Jump Pairings**:
for all `p, q : SourceGraph`,
`⟪p.val.snd, q.val.snd⟫_ℝ = ⟪(graphArchEquiv p).val.snd, (graphArchEquiv q).val.snd⟫_ℝ + ⟪primeDifference p.val.fst, primeDifference q.val.fst⟫_ℝ`. -/
theorem inner_snd_eq_arch_add_primeDifference (p q : SourceGraph) :
    ⟪p.val.snd, q.val.snd⟫_ℝ =
      ⟪(graphArchEquiv p).val.snd, (graphArchEquiv q).val.snd⟫_ℝ +
        ⟪primeDifference p.val.fst, primeDifference q.val.fst⟫_ℝ := by
  have h1 := sourcePair_eq_stationary_sub_arch_sub_primeShift p q
  change ⟪p.val.snd, q.val.snd⟫_ℝ - ⟪p.val.fst, q.val.fst⟫_ℝ = _ at h1
  have h2 := inner_graphArchEquiv_snd_eq_fullGroundEquiv_add_groundPotential p q
  have h3 := congrArg (fun T : MassSpace →L[ℝ] MassSpace => ⟪T p.val.fst, q.val.fst⟫_ℝ)
    sub_groundPotentialOperator_eq
  change ⟪p.val.fst - groundPotentialOperator p.val.fst, q.val.fst⟫_ℝ =
    ⟪primeDiagonalOperator p.val.fst + archDiagonalOperator p.val.fst, q.val.fst⟫_ℝ at h3
  rw [inner_sub_left, inner_add_left, inner_archDiagonalOperator] at h3
  have h4 := inner_primeDiagonal_sub_primeShift p.val.fst q.val.fst
  linarith

theorem inner_snd_eq_arch_add_primeDiagonal_sub_primeShift (p q : SourceGraph) :
    ⟪p.val.snd, q.val.snd⟫_ℝ =
      ⟪(graphArchEquiv p).val.snd, (graphArchEquiv q).val.snd⟫_ℝ +
        ⟪primeDiagonalOperator p.val.fst, q.val.fst⟫_ℝ -
        ⟪primeShiftOperator p.val.fst, q.val.fst⟫_ℝ := by
  rw [inner_snd_eq_arch_add_primeDifference, ← inner_primeDiagonal_sub_primeShift]
  ring

/-- **Total Edge Norm Decomposition into Archimedean and Prime Jump Energies**:
for every `p : SourceGraph`,
`‖p.val.snd‖ ^ 2 = ‖(graphArchEquiv p).val.snd‖ ^ 2 + ‖primeDifference p.val.fst‖ ^ 2`. -/
theorem norm_snd_sq_eq_arch_add_prime_norm_sq (p : SourceGraph) :
    ‖p.val.snd‖ ^ 2 =
      ‖(graphArchEquiv p).val.snd‖ ^ 2 + ‖primeDifference p.val.fst‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_snd_eq_arch_add_primeDifference,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

theorem norm_snd_sq_eq_arch_add_primeDiagonal_sub_primeShift (p : SourceGraph) :
    ‖p.val.snd‖ ^ 2 =
      ‖(graphArchEquiv p).val.snd‖ ^ 2 +
        ⟪primeDiagonalOperator p.val.fst, p.val.fst⟫_ℝ -
        ⟪primeShiftOperator p.val.fst, p.val.fst⟫_ℝ := by
  rw [norm_snd_sq_eq_arch_add_prime_norm_sq, ← inner_primeDiagonal_sub_primeShift_self]
  ring

/-- **Prime Jump Energy Nodal Decomposition**:
for every `p : SourceGraph`,
`‖primeDifference p.val.fst‖ ^ 2 = ‖primeDifference (absGraph p).val.fst‖ ^ 2 + 4 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ`. -/
theorem norm_primeDifference_sq_eq_absGraph_add_four_primeShift_cross (p : SourceGraph) :
    ‖primeDifference p.val.fst‖ ^ 2 =
      ‖primeDifference (absGraph p).val.fst‖ ^ 2 +
        4 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  rw [← inner_primeDiagonal_sub_primeShift_self, ← inner_primeDiagonal_sub_primeShift_self,
    inner_primeDiagonalOperator_absGraph_self, inner_primeShiftOperator_absGraph_self_eq]
  ring

/-- **Stationary Edge Norm Nodal Decomposition**:
for every `p : SourceGraph`,
`‖(fullGroundEquiv p).val.snd‖ ^ 2 = ‖(fullGroundEquiv (absGraph p)).val.snd‖ ^ 2 - 4 * ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ`. -/
theorem norm_fullGroundEquiv_snd_sq_eq_absGraph_sub_four_cross (p : SourceGraph) :
    ‖(fullGroundEquiv p).val.snd‖ ^ 2 =
      ‖(fullGroundEquiv (absGraph p)).val.snd‖ ^ 2 -
        4 * ⟪(fullGroundEquiv (posGraph p)).val.snd,
          (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ := by
  have hsub : (fullGroundEquiv p).val.snd =
      (fullGroundEquiv (posGraph p)).val.snd - (fullGroundEquiv (negGraph p)).val.snd :=
    congrArg (fun q : stationaryGroundGraph => q.val.snd)
      (fullGroundEquiv_posGraph_sub_negGraph p).symm
  have hadd : (fullGroundEquiv (absGraph p)).val.snd =
      (fullGroundEquiv (posGraph p)).val.snd + (fullGroundEquiv (negGraph p)).val.snd :=
    congrArg (fun q : stationaryGroundGraph => q.val.snd)
      (fullGroundEquiv_posGraph_add_negGraph p).symm
  rw [hsub, hadd, norm_sub_sq_real, norm_add_sq_real]
  ring

/-- **Archimedean Jump Energy Nodal Decomposition**:
for every `p : SourceGraph`,
`‖(graphArchEquiv p).val.snd‖ ^ 2 = ‖(graphArchEquiv (absGraph p)).val.snd‖ ^ 2 - 4 * ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ`. -/
theorem norm_graphArchEquiv_snd_sq_eq_absGraph_sub_four_cross (p : SourceGraph) :
    ‖(graphArchEquiv p).val.snd‖ ^ 2 =
      ‖(graphArchEquiv (absGraph p)).val.snd‖ ^ 2 -
        4 * ⟪(fullGroundEquiv (posGraph p)).val.snd,
          (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ := by
  have h1 := inner_graphArchEquiv_snd_eq_fullGroundEquiv_add_groundPotential p p
  have h2 := inner_graphArchEquiv_snd_eq_fullGroundEquiv_add_groundPotential (absGraph p) (absGraph p)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h1 h2
  rw [inner_groundPotentialOperator_absGraph_self] at h2
  have h3 := norm_fullGroundEquiv_snd_sq_eq_absGraph_sub_four_cross p
  linarith

/-- **Total Edge Norm Nodal Decomposition**:
for every `p : SourceGraph`,
`‖p.val.snd‖ ^ 2 = ‖(absGraph p).val.snd‖ ^ 2 - 4 * sourcePair (posGraph p) (negGraph p)`. -/
theorem norm_snd_sq_eq_absGraph_snd_sub_four_sourcePair (p : SourceGraph) :
    ‖p.val.snd‖ ^ 2 =
      ‖(absGraph p).val.snd‖ ^ 2 - 4 * sourcePair (posGraph p) (negGraph p) := by
  have h1 : sourceEnergy p = ‖p.val.snd‖ ^ 2 - ‖p.val.fst‖ ^ 2 := rfl
  have h2 : sourceEnergy (absGraph p) =
      ‖(absGraph p).val.snd‖ ^ 2 - ‖(absGraph p).val.fst‖ ^ 2 := rfl
  have h3 := sourceEnergy_absGraph_eq p
  rw [h1, h2, norm_absGraph_fst_sq] at h3
  linarith

/-- **Four-Term ($2 \times 2$) Archimedean/Prime $\times$ Envelope/Nodal Decomposition of `‖p.val.snd‖ ^ 2`**:
every one of the four summands on the right-hand side is nonnegative, and the archimedean cross
term `-4 * ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ` is
strictly positive whenever `p` changes sign (`posGraph p ≠ 0 ∧ negGraph p ≠ 0`). -/
theorem norm_snd_sq_eq_four_term_nodal_decomposition (p : SourceGraph) :
    ‖p.val.snd‖ ^ 2 =
      ‖(graphArchEquiv (absGraph p)).val.snd‖ ^ 2 -
        4 * ⟪(fullGroundEquiv (posGraph p)).val.snd,
          (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ +
        ‖primeDifference (absGraph p).val.fst‖ ^ 2 +
        4 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  rw [norm_snd_sq_eq_arch_add_prime_norm_sq,
    norm_graphArchEquiv_snd_sq_eq_absGraph_sub_four_cross,
    norm_primeDifference_sq_eq_absGraph_add_four_primeShift_cross]
  ring

/-- **Eigenvector Edge-Norm Identity**:
for every eigenvector `resolvent w = μ • w` with `μ ≠ 0`, the Riesz lift `p = rieszLift w` satisfies
`‖(rieszLift w).val.snd‖ ^ 2 = ((1 - μ) / μ) * ‖(rieszLift w).val.fst‖ ^ 2`. -/
theorem norm_rieszLift_snd_sq_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace}
    (heig : resolvent w = μ • w) :
    ‖(rieszLift w).val.snd‖ ^ 2 = ((1 - μ) / μ) * ‖(rieszLift w).val.fst‖ ^ 2 := by
  have h1 : sourceEnergy (rieszLift w) =
      ‖(rieszLift w).val.snd‖ ^ 2 - ‖(rieszLift w).val.fst‖ ^ 2 := rfl
  have h2 := sourceEnergy_rieszLift w
  have hfst : (rieszLift w).val.fst = μ • w := heig
  have hinner : ⟪w, resolvent w⟫_ℝ = μ * ‖w‖ ^ 2 := by
    rw [heig, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have h3 : ‖(rieszLift w).val.fst‖ ^ 2 = μ ^ 2 * ‖w‖ ^ 2 := by
    rw [hfst, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have h4 : ‖resolvent w‖ ^ 2 = ‖(rieszLift w).val.fst‖ ^ 2 := rfl
  rw [hinner, h4] at h2
  have h5 : μ * ‖w‖ ^ 2 = (1 / μ) * ‖(rieszLift w).val.fst‖ ^ 2 := by
    rw [h3]
    field_simp [hμ]
  rw [h5, h1] at h2
  have h6 : (1 / μ) * ‖(rieszLift w).val.fst‖ ^ 2 - ‖(rieszLift w).val.fst‖ ^ 2 =
      ((1 - μ) / μ) * ‖(rieszLift w).val.fst‖ ^ 2 := by
    field_simp [hμ]
  linarith

/-- **Exact Spectral-Gap / Nodal-Deficit Identity for Resolvent Eigenvectors**:
for every eigenvector `resolvent w = μ • w` with `μ ≠ 0`,
`((1 - μ) / μ) * ‖(rieszLift w).val.fst‖ ^ 2 = ‖(absGraph (rieszLift w)).val.snd‖ ^ 2 - 4 * sourcePair (posGraph (rieszLift w)) (negGraph (rieszLift w))`. -/
theorem spectral_gap_mul_norm_sq_eq_absGraph_snd_sub_four_cross {μ : ℝ} (hμ : μ ≠ 0)
    {w : MassSpace} (heig : resolvent w = μ • w) :
    ((1 - μ) / μ) * ‖(rieszLift w).val.fst‖ ^ 2 =
      ‖(absGraph (rieszLift w)).val.snd‖ ^ 2 -
        4 * sourcePair (posGraph (rieszLift w)) (negGraph (rieszLift w)) := by
  rw [← norm_rieszLift_snd_sq_of_eigenvector hμ heig,
    norm_snd_sq_eq_absGraph_snd_sub_four_sourcePair]

/-- **Quantitative Nodal Lower Bound on the Spectral Gap of Any Nonzero Primitive Eigenvector**:
for every nonzero primitive eigenvector `resolvent w = μ • w` (`μ > 0`, `w ≠ 0`, `⟪w, oneL⟫_ℝ = 0`),
with `p = rieszLift w`,
`0 < -4 * ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ ≤ -4 * sourcePair (posGraph p) (negGraph p) ≤ ((1 - μ) / μ) * ‖p.val.fst‖ ^ 2`. -/
theorem spectral_gap_nodal_lower_bound_of_primitive_eigenvector {μ : ℝ} (hμ : 0 < μ)
    {w : MassSpace} (hw0 : w ≠ 0) (hprim : ⟪w, oneL⟫_ℝ = 0) (heig : resolvent w = μ • w) :
    0 < -4 * ⟪(fullGroundEquiv (posGraph (rieszLift w))).val.snd,
        (fullGroundEquiv (negGraph (rieszLift w))).val.snd⟫_ℝ ∧
      -4 * ⟪(fullGroundEquiv (posGraph (rieszLift w))).val.snd,
        (fullGroundEquiv (negGraph (rieszLift w))).val.snd⟫_ℝ ≤
        -4 * sourcePair (posGraph (rieszLift w)) (negGraph (rieszLift w)) ∧
      -4 * sourcePair (posGraph (rieszLift w)) (negGraph (rieszLift w)) ≤
        ((1 - μ) / μ) * ‖(rieszLift w).val.fst‖ ^ 2 := by
  set p := rieszLift w
  have hp_fst : p.val.fst = μ • w := heig
  have hp0 : p ≠ 0 := by
    intro h
    have hf : p.val.fst = 0 := by rw [h]; rfl
    rw [hp_fst, smul_eq_zero] at hf
    exact hw0 (hf.resolve_left hμ.ne')
  have hp_prim : ⟪p.val.fst, oneL⟫_ℝ = 0 := by
    rw [hp_fst, real_inner_smul_left, hprim, mul_zero]
  obtain ⟨hpos_ne, hneg_ne⟩ := posGraph_ne_zero_and_negGraph_ne_zero_of_primitive hp0 hp_prim
  have harch_neg :
      ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ < 0 :=
    inner_fullGroundEquiv_posGraph_negGraph_snd_neg_of_ne_zero hpos_ne hneg_ne
  have hle_stat := sourcePair_posGraph_negGraph_le_stationary p
  have hgap := spectral_gap_mul_norm_sq_eq_absGraph_snd_sub_four_cross hμ.ne' heig
  have habs_nn : 0 ≤ ‖(absGraph p).val.snd‖ ^ 2 := sq_nonneg _
  refine ⟨by linarith, by linarith, by linarith⟩

/-! ## Section 2: Primitive Ground Subtraction `primGraph` and the Odd-to-Even Primitive Contraction Bridge -/

/-- Primitive ground projection on `SourceGraph`: subtracts the ground-state component along
`constantLift 1` (remembering that `‖oneL‖ ^ 2 = 1 / 2`). -/
def primGraph (q : SourceGraph) : SourceGraph :=
  q - (2 * ⟪q.val.fst, oneL⟫_ℝ) • constantLift 1

theorem primGraph_fst (q : SourceGraph) :
    (primGraph q).val.fst = q.val.fst - (2 * ⟪q.val.fst, oneL⟫_ℝ) • oneL := by
  change q.val.fst - (2 * ⟪q.val.fst, oneL⟫_ℝ) • (constantLift 1).val.fst = _
  have h1 : (constantLift 1).val.fst = oneL := by
    simpa using constantLift_fst_eq_smul_oneL 1
  rw [h1]

theorem primGraph_snd (q : SourceGraph) :
    (primGraph q).val.snd = q.val.snd := by
  change q.val.snd - (2 * ⟪q.val.fst, oneL⟫_ℝ) • (constantLift 1).val.snd = q.val.snd
  rw [constantLift_edge, smul_zero, sub_zero]

theorem inner_primGraph_oneL (q : SourceGraph) :
    ⟪(primGraph q).val.fst, oneL⟫_ℝ = 0 := by
  rw [primGraph_fst, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, norm_oneL_sq]
  ring

theorem inner_oneL_tanhL_eq_zero : ⟪oneL, tanhL⟫_ℝ = 0 := by
  have h := reflectMass.inner_map_map oneL tanhL
  rw [reflectMass_oneL, reflectMass_tanhL, inner_neg_right] at h
  linarith

theorem inner_primGraph_tanhL (q : SourceGraph) :
    ⟪(primGraph q).val.fst, tanhL⟫_ℝ = ⟪q.val.fst, tanhL⟫_ℝ := by
  rw [primGraph_fst, inner_sub_left, real_inner_smul_left, inner_oneL_tanhL_eq_zero,
    mul_zero, sub_zero]

theorem norm_primGraph_fst_sq (q : SourceGraph) :
    ‖(primGraph q).val.fst‖ ^ 2 = ‖q.val.fst‖ ^ 2 - 2 * ⟪q.val.fst, oneL⟫_ℝ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, primGraph_fst, inner_sub_left, inner_sub_right,
    inner_sub_right, real_inner_smul_left, real_inner_smul_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_comm oneL q.val.fst,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_oneL_sq]
  ring

theorem two_mul_inner_oneL_sq_le_norm_sq (u : MassSpace) :
    2 * ⟪u, oneL⟫_ℝ ^ 2 ≤ ‖u‖ ^ 2 := by
  have h1 : ‖u - (2 * ⟪u, oneL⟫_ℝ) • oneL‖ ^ 2 = ‖u‖ ^ 2 - 2 * ⟪u, oneL⟫_ℝ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_comm oneL u,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_oneL_sq]
    ring
  have h2 : 0 ≤ ‖u - (2 * ⟪u, oneL⟫_ℝ) • oneL‖ ^ 2 := sq_nonneg _
  linarith

theorem sourceEnergy_primGraph (q : SourceGraph) :
    sourceEnergy (primGraph q) = sourceEnergy q + 2 * ⟪q.val.fst, oneL⟫_ℝ ^ 2 := by
  change ‖(primGraph q).val.snd‖ ^ 2 - ‖(primGraph q).val.fst‖ ^ 2 =
    (‖q.val.snd‖ ^ 2 - ‖q.val.fst‖ ^ 2) + 2 * ⟪q.val.fst, oneL⟫_ℝ ^ 2
  rw [primGraph_snd, norm_primGraph_fst_sq]
  ring

theorem sourceEnergy_primGraph_eq_weilForm_of_even {q : SourceGraph}
    (hq : q.val.fst ∈ evenSector) :
    sourceEnergy (primGraph q) = weilForm q := by
  have htanh : ⟪q.val.fst, tanhL⟫_ℝ = 0 := inner_tanhL_eq_zero_of_even (mem_evenSector.mp hq)
  unfold weilForm
  rw [sourceEnergy_primGraph, htanh]
  ring

theorem primGraph_fst_mem_evenSector_of_even {q : SourceGraph}
    (hq : q.val.fst ∈ evenSector) :
    (primGraph q).val.fst ∈ evenSector := by
  rw [primGraph_fst]
  exact evenSector.sub_mem hq (evenSector.smul_mem _ (mem_evenSector.mpr reflectMass_oneL))

theorem sourceEnergy_primGraph_absGraph_add_norm_sq (p : SourceGraph) :
    sourceEnergy (primGraph (absGraph p)) + ‖(primGraph (absGraph p)).val.fst‖ ^ 2 =
      ‖p.val.snd‖ ^ 2 + 4 * sourcePair (posGraph p) (negGraph p) := by
  change (‖(primGraph (absGraph p)).val.snd‖ ^ 2 - ‖(primGraph (absGraph p)).val.fst‖ ^ 2) +
    ‖(primGraph (absGraph p)).val.fst‖ ^ 2 = _
  rw [sub_add_cancel, primGraph_snd, norm_snd_sq_eq_absGraph_snd_sub_four_sourcePair p]
  ring

/-! ## Section 3: Mass-Space Fourier/Cosine Readouts and Eigenvector Cardinal & Translated-Cardinal Pairing Laws -/

/-- Literal Fourier readout on `MassSpace`. -/
def massFourierReadout (w : MassSpace) (z : ℂ) : ℂ :=
  paperFT (fun x => (phiDoobTest w x : ℂ)) z

/-- Literal cosine readout on `MassSpace`. -/
def massCosineReadout (w : MassSpace) (z : ℂ) : ℂ :=
  ∫ x, (phiDoobTest w x : ℂ) * Complex.cos (z * x)

/-- Phase-shifted cosine readout on `MassSpace`. -/
def massShiftedCosineReadout (w : MassSpace) (z : ℂ) (t : ℝ) : ℂ :=
  (exp (-(I * z) * (t : ℂ)) * massFourierReadout w z +
    exp ((I * z) * (t : ℂ)) * massFourierReadout w (-z)) / 2

theorem graphFourierReadout_eq_massFourierReadout (p : SourceGraph) (z : ℂ) :
    graphFourierReadout p z = massFourierReadout p.val.fst z := rfl

theorem graphCosineReadout_eq_massCosineReadout (p : SourceGraph) (z : ℂ) :
    graphCosineReadout p z = massCosineReadout p.val.fst z :=
  graphCosineReadout_eq_integral p z

theorem shiftedCosineReadout_eq_massShiftedCosineReadout (p : SourceGraph) (z : ℂ) (t : ℝ) :
    shiftedCosineReadout p z t = massShiftedCosineReadout p.val.fst z t := rfl

theorem massFourierReadout_smul (c : ℝ) (w : MassSpace) (z : ℂ) :
    massFourierReadout (c • w) z = (c : ℂ) * massFourierReadout w z := by
  unfold massFourierReadout paperFT
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [volume_absolutelyContinuous_mass.ae_eq (Lp.coeFn_smul c w)] with x hx
  simp only [phiDoobTest, hx, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

theorem massCosineReadout_smul (c : ℝ) (w : MassSpace) (z : ℂ) :
    massCosineReadout (c • w) z = (c : ℂ) * massCosineReadout w z := by
  unfold massCosineReadout
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [volume_absolutelyContinuous_mass.ae_eq (Lp.coeFn_smul c w)] with x hx
  simp only [phiDoobTest, hx, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

theorem massShiftedCosineReadout_smul (c : ℝ) (w : MassSpace) (z : ℂ) (t : ℝ) :
    massShiftedCosineReadout (c • w) z t = (c : ℂ) * massShiftedCosineReadout w z t := by
  unfold massShiftedCosineReadout
  rw [massFourierReadout_smul, massFourierReadout_smul]
  ring

theorem graphFourierReadout_rieszLift_of_eigenvector {μ : ℝ} {w : MassSpace}
    (heig : resolvent w = μ • w) (z : ℂ) :
    graphFourierReadout (rieszLift w) z = (μ : ℂ) * massFourierReadout w z := by
  rw [graphFourierReadout_eq_massFourierReadout]
  change massFourierReadout (resolvent w) z = _
  rw [heig, massFourierReadout_smul]

theorem graphCosineReadout_rieszLift_of_eigenvector {μ : ℝ} {w : MassSpace}
    (heig : resolvent w = μ • w) (z : ℂ) :
    graphCosineReadout (rieszLift w) z = (μ : ℂ) * massCosineReadout w z := by
  rw [graphCosineReadout_eq_massCosineReadout]
  change massCosineReadout (resolvent w) z = _
  rw [heig, massCosineReadout_smul]

theorem shiftedCosineReadout_rieszLift_of_eigenvector {μ : ℝ} {w : MassSpace}
    (heig : resolvent w = μ • w) (z : ℂ) (t : ℝ) :
    shiftedCosineReadout (rieszLift w) z t = (μ : ℂ) * massShiftedCosineReadout w z t := by
  rw [shiftedCosineReadout_eq_massShiftedCosineReadout]
  change massShiftedCosineReadout (resolvent w) z t = _
  rw [heig, massShiftedCosineReadout_smul]

/-- **Universal Cardinal Real-Vector Pairing for Resolvent Eigenvectors**:
for every eigenvector `resolvent w = μ • w`, every `a` with `0 < a.re` and `XiC a = 0`, and every
`F : CardinalGraphFrame a`,
`(1 - 2 * μ) * ⟪w, F.reVector.val.fst⟫_ℝ = μ * cardinalOrbitMass a * (massCosineReadout w a).re`. -/
theorem eigenvector_cardinal_re_pairing {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) {μ : ℝ} {w : MassSpace} (heig : resolvent w = μ • w) :
    (1 - 2 * μ) * ⟪w, F.reVector.val.fst⟫_ℝ =
      μ * cardinalOrbitMass a * (massCosineReadout w a).re := by
  have h1 := sourcePair_rieszLift_of_eigenvector heig F.reVector
  have h2 := F.pair_re ha hz (rieszLift w)
  rw [graphCosineReadout_rieszLift_of_eigenvector heig] at h2
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h2
  linarith

/-- **Universal Cardinal Imaginary-Vector Pairing for Resolvent Eigenvectors**:
for every eigenvector `resolvent w = μ • w`, every `a` with `0 < a.re` and `XiC a = 0`, and every
`F : CardinalGraphFrame a`,
`(1 - 2 * μ) * ⟪w, F.imVector.val.fst⟫_ℝ = μ * cardinalOrbitMass a * (massCosineReadout w a).im`. -/
theorem eigenvector_cardinal_im_pairing {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) {μ : ℝ} {w : MassSpace} (heig : resolvent w = μ • w) :
    (1 - 2 * μ) * ⟪w, F.imVector.val.fst⟫_ℝ =
      μ * cardinalOrbitMass a * (massCosineReadout w a).im := by
  have h1 := sourcePair_rieszLift_of_eigenvector heig F.imVector
  have h2 := F.pair_im ha hz (rieszLift w)
  rw [graphCosineReadout_rieszLift_of_eigenvector heig] at h2
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at h2
  linarith

/-- Every translated cardinal source `u` or `v` from `exists_translatedCardinalFrame` vanishes at
both polar points `±I/2` and is orthogonal in `MassSpace` to both `oneL` and `tanhL`. -/
theorem translatedCardinal_polar_and_moments_zero {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0)
    (t : ℝ) {u v : SourceGraph}
    (hus : u.val.fst =ᵐ[massMeasure] phiDoobInv (translate (fun x => (divisorCardinalSource a x).re) t))
    (hvs : v.val.fst =ᵐ[massMeasure] phiDoobInv (translate (fun x => (divisorCardinalSource a x).im) t)) :
    (graphFourierReadout u (I / 2) = 0 ∧ graphFourierReadout u (-I / 2) = 0) ∧
    (graphFourierReadout v (I / 2) = 0 ∧ graphFourierReadout v (-I / 2) = 0) ∧
    (⟪u.val.fst, oneL⟫_ℝ = 0 ∧ ⟪u.val.fst, tanhL⟫_ℝ = 0) ∧
    (⟪v.val.fst, oneL⟫_ℝ = 0 ∧ ⟪v.val.fst, tanhL⟫_ℝ = 0) := by
  have hr : (fun x => ((divisorCardinalSource a x).re : ℂ)) =
      fun x => (cardinalRealSource a 1 x : ℂ) := by
    funext x; simp [cardinalRealSource]
  have hi : (fun x => ((divisorCardinalSource a x).im : ℂ)) =
      fun x => (cardinalRealSource a (-I) x : ℂ) := by
    funext x; simp [cardinalRealSource, Complex.mul_re]
  obtain ⟨hpr1, hpr2⟩ := cardinalRealSource_poles ha hz 1
  obtain ⟨hpi1, hpi2⟩ := cardinalRealSource_poles ha hz (-I)
  have hu1 : graphFourierReadout u (I / 2) = 0 := by
    rw [graphFourierReadout_of_source hus, paperFT_translate_real, hr, hpr1, mul_zero]
  have hu2 : graphFourierReadout u (-I / 2) = 0 := by
    rw [graphFourierReadout_of_source hus, paperFT_translate_real, hr, hpr2, mul_zero]
  have hv1 : graphFourierReadout v (I / 2) = 0 := by
    rw [graphFourierReadout_of_source hvs, paperFT_translate_real, hi, hpi1, mul_zero]
  have hv2 : graphFourierReadout v (-I / 2) = 0 := by
    rw [graphFourierReadout_of_source hvs, paperFT_translate_real, hi, hpi2, mul_zero]
  have hu_one : ⟪u.val.fst, oneL⟫_ℝ = 0 := by
    rw [← polarCosine_oneL, polarCosine_eq_half_fourier, hu1, hu2]
    norm_num
  have hu_tanh : ⟪u.val.fst, tanhL⟫_ℝ = 0 := by
    rw [← polarSine_tanhL, polarSine, hu1, hu2]
    norm_num
  have hv_one : ⟪v.val.fst, oneL⟫_ℝ = 0 := by
    rw [← polarCosine_oneL, polarCosine_eq_half_fourier, hv1, hv2]
    norm_num
  have hv_tanh : ⟪v.val.fst, tanhL⟫_ℝ = 0 := by
    rw [← polarSine_tanhL, polarSine, hv1, hv2]
    norm_num
  exact ⟨⟨hu1, hu2⟩, ⟨hv1, hv2⟩, ⟨hu_one, hu_tanh⟩, ⟨hv_one, hv_tanh⟩⟩

/-- **Translated Cardinal Eigenvector Pairing Law**:
for every `a` with `0 < a.re` and `XiC a = 0` and every `|t| ≤ CHMDThetaTranslate.radius`, there
exist `u, v : SourceGraph` orthogonal to both `oneL` and `tanhL` such that for every eigenvector
`resolvent w = μ • w`,
`(1 - 2 * μ) * ⟪w, u.val.fst⟫_ℝ = μ * cardinalOrbitMass a * (massShiftedCosineReadout w a t).re`
and
`(1 - 2 * μ) * ⟪w, v.val.fst⟫_ℝ = μ * cardinalOrbitMass a * (massShiftedCosineReadout w a t).im`. -/
theorem exists_translatedCardinalFrame_eigenvector_pairing {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0)
    (t : ℝ) (ht : |t| ≤ CHMDThetaTranslate.radius) :
    ∃ u v : SourceGraph,
      u.val.fst =ᵐ[massMeasure] phiDoobInv (translate (fun x => (divisorCardinalSource a x).re) t) ∧
      v.val.fst =ᵐ[massMeasure] phiDoobInv (translate (fun x => (divisorCardinalSource a x).im) t) ∧
      ⟪u.val.fst, oneL⟫_ℝ = 0 ∧ ⟪u.val.fst, tanhL⟫_ℝ = 0 ∧
      ⟪v.val.fst, oneL⟫_ℝ = 0 ∧ ⟪v.val.fst, tanhL⟫_ℝ = 0 ∧
      (∀ {μ : ℝ} {w : MassSpace}, resolvent w = μ • w →
        (1 - 2 * μ) * ⟪w, u.val.fst⟫_ℝ =
          μ * cardinalOrbitMass a * (massShiftedCosineReadout w a t).re ∧
        (1 - 2 * μ) * ⟪w, v.val.fst⟫_ℝ =
          μ * cardinalOrbitMass a * (massShiftedCosineReadout w a t).im) := by
  obtain ⟨u, v, hus, hvs, hu_pair, hv_pair⟩ := exists_translatedCardinalFrame ha hz t ht
  obtain ⟨_, _, ⟨hu_one, hu_tanh⟩, ⟨hv_one, hv_tanh⟩⟩ :=
    translatedCardinal_polar_and_moments_zero ha hz t hus hvs
  refine ⟨u, v, hus, hvs, hu_one, hu_tanh, hv_one, hv_tanh, fun {μ w} heig => ?_⟩
  have h1u := sourcePair_rieszLift_of_eigenvector heig u
  have h2u := hu_pair (rieszLift w)
  rw [shiftedCosineReadout_rieszLift_of_eigenvector heig] at h2u
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h2u
  have h1v := sourcePair_rieszLift_of_eigenvector heig v
  have h2v := hv_pair (rieszLift w)
  rw [shiftedCosineReadout_rieszLift_of_eigenvector heig] at h2v
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at h2v
  exact ⟨by linarith, by linarith⟩

/-- **Shifted-Theta Pairing Law for Odd Resolvent Eigenvectors**:
for every odd eigenvector `w ∈ oddSector` (`resolvent w = μ • w`) and every admissible shift `a`,
`(2 * μ - 1) * ⟪w, (lift a ha).val.fst⟫_ℝ = -μ * sinh(a / 2) * ⟪w, tanhL⟫_ℝ`. -/
theorem odd_eigenvector_thetaTranslate_pairing (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|))
    {μ : ℝ} {w : MassSpace} (hodd : w ∈ oddSector) (heig : resolvent w = μ • w) :
    (2 * μ - 1) * ⟪w, (CHMDThetaTranslate.lift a ha).val.fst⟫_ℝ =
      -μ * Real.sinh (a / 2) * ⟪w, tanhL⟫_ℝ := by
  have h1 := eigenvector_thetaTranslate_pairing a ha heig
  rw [inner_oneL_eq_zero_of_odd hodd] at h1
  linarith

/-- **Threshold Eigenvector Vanishing Theorem (`μ = 1/2`)**:
every threshold eigenvector `resolvent w = (1/2) • w` is orthogonal to both `oneL` and `tanhL`
and has vanishing Fourier readout `massFourierReadout w a = 0` at every `XiC` zero `a`. -/
theorem threshold_eigenvector_polar_and_spectral_zero {w : MassSpace}
    (heig : resolvent w = (1 / 2 : ℝ) • w) :
    ⟪w, oneL⟫_ℝ = 0 ∧ ⟪w, tanhL⟫_ℝ = 0 ∧ ∀ a : ℂ, XiC a = 0 → massFourierReadout w a = 0 := by
  have hrad : rieszLift w ∈ signedRadical := by
    intro q
    have h := sourcePair_rieszLift_of_eigenvector heig q
    linarith
  have hone : ⟪w, oneL⟫_ℝ = 0 := by
    have h0 := eigenvector_thetaTranslate_pairing 0
      (CHMDThetaTranslate.small_shift (by simp [CHMDThetaTranslate.radius_pos.le])) heig
    simp only [zero_div, Real.cosh_zero, Real.sinh_zero, mul_one, mul_zero] at h0
    linarith
  have htanh : ⟪w, tanhL⟫_ℝ = 0 := by
    have h := eigenvector_oddPolarVectorAt_pairing CHMDThetaTranslate.radius_pos.ne'
      (CHMDThetaTranslate.small_shift (by rw [abs_of_pos CHMDThetaTranslate.radius_pos])) heig
    linarith
  refine ⟨hone, htanh, fun a hz => ?_⟩
  have hf := radical_graphFourierReadout_zero hrad hz
  rw [graphFourierReadout_rieszLift_of_eigenvector heig] at hf
  exact (mul_eq_zero.mp hf).resolve_left (by norm_num)

/-! ## Section 4: Exact Finite-Family Eigenvector Projection Decomposition of `sourcePair` and `sourceEnergy` -/

/-- Normalized Riesz lift `e_i = (μ_i)⁻¹ • rieszLift (w_i)` of an eigenvector `w_i`, chosen so that
`(eigenGraphLift μ w i).val.fst = w i`. -/
def eigenGraphLift {m : ℕ} (μ : Fin m → ℝ) (w : Fin m → MassSpace) (i : Fin m) : SourceGraph :=
  (μ i)⁻¹ • rieszLift (w i)

/-- Finite-family eigenvector graph projection `∑_i ⟪w_i, q.val.fst⟫ • eigenGraphLift μ w i`. -/
def eigenGraphProj {m : ℕ} (μ : Fin m → ℝ) (w : Fin m → MassSpace) (q : SourceGraph) : SourceGraph :=
  ∑ i, ⟪w i, q.val.fst⟫_ℝ • eigenGraphLift μ w i

/-- Remainder `q - eigenGraphProj μ w q` after subtracting the finite-family eigenvector projection. -/
def eigenGraphRem {m : ℕ} (μ : Fin m → ℝ) (w : Fin m → MassSpace) (q : SourceGraph) : SourceGraph :=
  q - eigenGraphProj μ w q

theorem eigenGraphLift_fst {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (hμ : ∀ i, μ i ≠ 0) (heig : ∀ i, resolvent (w i) = μ i • w i) (i : Fin m) :
    (eigenGraphLift μ w i).val.fst = w i := by
  change (μ i)⁻¹ • (rieszLift (w i)).val.fst = w i
  have h : (rieszLift (w i)).val.fst = μ i • w i := heig i
  rw [h, inv_smul_smul₀ (hμ i)]

theorem sourcePair_eigenGraphLift_left {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (heig : ∀ i, resolvent (w i) = μ i • w i) (i : Fin m) (q : SourceGraph) :
    sourcePair (eigenGraphLift μ w i) q = ((1 - 2 * μ i) / μ i) * ⟪w i, q.val.fst⟫_ℝ := by
  unfold eigenGraphLift
  rw [sourcePair_smul_left, sourcePair_rieszLift_of_eigenvector (heig i)]
  ring

theorem eigenGraphProj_fst {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (hμ : ∀ i, μ i ≠ 0) (heig : ∀ i, resolvent (w i) = μ i • w i) (q : SourceGraph) :
    (eigenGraphProj μ w q).val.fst = ∑ i, ⟪w i, q.val.fst⟫_ℝ • w i := by
  change sourceMap (∑ i, ⟪w i, q.val.fst⟫_ℝ • eigenGraphLift μ w i) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  change ⟪w i, q.val.fst⟫_ℝ • (eigenGraphLift μ w i).val.fst = _
  rw [eigenGraphLift_fst hμ heig i]

theorem inner_eigenGraphRem_fst {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (hμ : ∀ i, μ i ≠ 0) (hw : Orthonormal ℝ w) (heig : ∀ i, resolvent (w i) = μ i • w i)
    (q : SourceGraph) (i : Fin m) :
    ⟪w i, (eigenGraphRem μ w q).val.fst⟫_ℝ = 0 := by
  change ⟪w i, q.val.fst - (eigenGraphProj μ w q).val.fst⟫_ℝ = 0
  rw [eigenGraphProj_fst hμ heig, inner_sub_right, hw.inner_right_fintype]
  ring

theorem sourcePair_eigenGraphLift_eigenGraphRem {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (hμ : ∀ i, μ i ≠ 0) (hw : Orthonormal ℝ w) (heig : ∀ i, resolvent (w i) = μ i • w i)
    (q : SourceGraph) (i : Fin m) :
    sourcePair (eigenGraphLift μ w i) (eigenGraphRem μ w q) = 0 := by
  rw [sourcePair_eigenGraphLift_left heig, inner_eigenGraphRem_fst hμ hw heig, mul_zero]

theorem sourcePair_eigenGraphProj_eigenGraphRem {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (hμ : ∀ i, μ i ≠ 0) (hw : Orthonormal ℝ w) (heig : ∀ i, resolvent (w i) = μ i • w i)
    (p q : SourceGraph) :
    sourcePair (eigenGraphProj μ w p) (eigenGraphRem μ w q) = 0 := by
  unfold eigenGraphProj
  rw [sourcePair_sum_left]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [sourcePair_smul_left, sourcePair_eigenGraphLift_eigenGraphRem hμ hw heig, mul_zero]

theorem sourcePair_eigenGraphProj_left {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (heig : ∀ i, resolvent (w i) = μ i • w i) (p q : SourceGraph) :
    sourcePair (eigenGraphProj μ w p) q =
      -∑ i, ((2 * μ i - 1) / μ i) * ⟪w i, p.val.fst⟫_ℝ * ⟪w i, q.val.fst⟫_ℝ := by
  unfold eigenGraphProj
  rw [sourcePair_sum_left, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sourcePair_smul_left, sourcePair_eigenGraphLift_left heig]
  ring

/-- **Exact Finite-Family Eigenvector Projection Decomposition of `sourcePair`**:
for any orthonormal family of eigenvectors `resolvent (w i) = μ i • w i` (`μ i ≠ 0`) and any
`p, q : SourceGraph`,
`sourcePair p q = -∑ i, ((2 * μ i - 1) / μ i) * ⟪w i, p.val.fst⟫_ℝ * ⟪w i, q.val.fst⟫_ℝ + sourcePair (eigenGraphRem μ w p) (eigenGraphRem μ w q)`. -/
theorem sourcePair_eq_neg_sum_eigen_add_rem {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (hμ : ∀ i, μ i ≠ 0) (hw : Orthonormal ℝ w) (heig : ∀ i, resolvent (w i) = μ i • w i)
    (p q : SourceGraph) :
    sourcePair p q =
      (-∑ i, ((2 * μ i - 1) / μ i) * ⟪w i, p.val.fst⟫_ℝ * ⟪w i, q.val.fst⟫_ℝ) +
        sourcePair (eigenGraphRem μ w p) (eigenGraphRem μ w q) := by
  have hp : p = eigenGraphProj μ w p + eigenGraphRem μ w p := (add_sub_cancel _ _).symm
  have hq : q = eigenGraphProj μ w q + eigenGraphRem μ w q := (add_sub_cancel _ _).symm
  conv_lhs => rw [hp]
  rw [sourcePair_add_left, sourcePair_eigenGraphProj_left heig]
  conv_lhs => rhs; rw [hq]
  rw [sourcePair_symm (eigenGraphRem μ w p), sourcePair_add_left,
    sourcePair_eigenGraphProj_eigenGraphRem hμ hw heig, zero_add,
    sourcePair_symm (eigenGraphRem μ w q)]

/-- **Exact Finite-Family Eigenvector Projection Decomposition of `sourceEnergy`**:
for any orthonormal family of eigenvectors `resolvent (w i) = μ i • w i` (`μ i ≠ 0`) and any
`q : SourceGraph`,
`sourceEnergy q = -∑ i, ((2 * μ i - 1) / μ i) * ⟪w i, q.val.fst⟫_ℝ ^ 2 + sourceEnergy (eigenGraphRem μ w q)`. -/
theorem sourceEnergy_eq_neg_sum_eigen_add_rem {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (hμ : ∀ i, μ i ≠ 0) (hw : Orthonormal ℝ w) (heig : ∀ i, resolvent (w i) = μ i • w i)
    (q : SourceGraph) :
    sourceEnergy q =
      (-∑ i, ((2 * μ i - 1) / μ i) * ⟪w i, q.val.fst⟫_ℝ ^ 2) +
        sourceEnergy (eigenGraphRem μ w q) := by
  rw [← sourcePair_self, ← sourcePair_self (eigenGraphRem μ w q),
    sourcePair_eq_neg_sum_eigen_add_rem hμ hw heig]
  congr 2
  exact Finset.sum_congr rfl fun i _ => by ring

end RHTower.CHMDPolar
