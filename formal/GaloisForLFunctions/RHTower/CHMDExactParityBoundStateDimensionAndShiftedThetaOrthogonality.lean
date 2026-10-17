import GaloisForLFunctions.RHTower.CHMDBeurlingDenyNodalDecompositionAndParityBoundStateSpaces
import GaloisForLFunctions.RHTower.CHMDCompactOrbitInertia
import GaloisForLFunctions.RHTower.CHMDTranslatedCardinalDetection

/-!
# Exact Parity Bound-State Dimension Formulas and Shifted-Theta Orthogonality

This module establishes the unconditional lower Birman–Schwinger bounds in both parity sectors of
`boundStateSpace` using the multiplicity-exact cardinal frames `CardinalGraphFrame` and their
small-shift translations `exists_translatedCardinalFrame`, and combines them with the upper bounds
from `CHMDBeurlingDenyNodalDecompositionAndParityBoundStateSpaces` to prove the exact dimension
identities:
- `Module.finrank ℝ oddBoundStateSpace = quarterZeros.ncard`,
- `Module.finrank ℝ evenBoundStateSpace = quarterZeros.ncard + 1`,
- `Module.finrank ℝ boundStateSpace = 2 * quarterZeros.ncard + 1`,
- `Module.finrank ℝ evenBoundStateSpace = Module.finrank ℝ oddBoundStateSpace + 1`,
- `offLineZeros.Finite ↔ quarterZeros.Finite ↔ FiniteDimensional ℝ oddBoundStateSpace ↔ FiniteDimensional ℝ evenBoundStateSpace ↔ FiniteDimensional ℝ boundStateSpace`,
together with the universal shifted-theta pairing law for eigenvectors of `resolvent`.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace BigOperators ComplexConjugate
noncomputable section

namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump CHMDTranslation

/-! ## Section 1: Universal Shifted-Theta Pairing Law and Orthogonality for Primitive Eigenvectors -/

theorem polarCosine_oneL (q : SourceGraph) :
    polarCosine q = ⟪q.val.fst, oneL⟫_ℝ := by
  have h1 := sourcePair_ground_eq_polarCosine q
  have h2 := sourcePair_ground q
  have h3 : (constantLift 1).val.fst = oneL := by
    simpa using constantLift_fst_eq_smul_oneL 1
  rw [h3, real_inner_comm] at h2
  linarith

theorem polarSine_tanhL (q : SourceGraph) :
    polarSine q = ⟪q.val.fst, tanhL⟫_ℝ := by
  have h1 := sourcePair_oddPolarVector q
  have h2 : oddPolarVector =
      oddPolarVectorAt CHMDThetaTranslate.radius
        (CHMDThetaTranslate.small_shift (by rw [abs_of_pos CHMDThetaTranslate.radius_pos])) := rfl
  rw [h2, sourcePair_oddPolarVectorAt_eq_inner_tanhL
    CHMDThetaTranslate.radius_pos.ne'
    (CHMDThetaTranslate.small_shift (by rw [abs_of_pos CHMDThetaTranslate.radius_pos])),
    real_inner_comm] at h1
  exact h1.symm

theorem thetaTranslate_mem_fullSpectralNullspace (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    CHMDThetaTranslate.lift a ha ∈ fullSpectralNullspace := by
  intro z hz
  rw [thetaTranslate_fourier a ha z, hz, mul_zero]

theorem polarCosine_thetaTranslate (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    polarCosine (CHMDThetaTranslate.lift a ha) = Real.cosh (a / 2) / 2 := by
  rw [polarCosine_eq_half_fourier, thetaTranslate_fourier_plus_pole,
    thetaTranslate_fourier_minus_pole]
  simp only [Complex.ofReal_re]
  rw [Real.cosh_eq]
  ring

theorem polarSine_thetaTranslate (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    polarSine (CHMDThetaTranslate.lift a ha) = Real.sinh (a / 2) / 2 := by
  rw [polarSine, thetaTranslate_fourier_plus_pole, thetaTranslate_fourier_minus_pole]
  simp only [Complex.ofReal_re]
  rw [Real.sinh_eq]
  ring

/-- **Universal Shifted-Theta Pairing Identity on `SourceGraph`**:
for every admissible shift `a` (`1 < 2 * exp(-2|a|)`) and every `q : SourceGraph`,
`sourcePair (lift a ha) q = -cosh(a / 2) * ⟪q.val.fst, oneL⟫_ℝ + sinh(a / 2) * ⟪q.val.fst, tanhL⟫_ℝ`. -/
theorem sourcePair_thetaTranslate (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) (q : SourceGraph) :
    sourcePair (CHMDThetaTranslate.lift a ha) q =
      -Real.cosh (a / 2) * ⟪q.val.fst, oneL⟫_ℝ + Real.sinh (a / 2) * ⟪q.val.fst, tanhL⟫_ℝ := by
  rw [full_nullspace_pair (thetaTranslate_mem_fullSpectralNullspace a ha) q,
    polarCosine_thetaTranslate a ha, polarSine_thetaTranslate a ha,
    polarCosine_oneL q, polarSine_tanhL q]
  ring

/-- **Universal Shifted-Theta Eigenvector Pairing Law**:
for every eigenvector `resolvent w = μ • w` and every admissible shift `a`,
`(2 * μ - 1) * ⟪w, (lift a ha).val.fst⟫_ℝ = μ * cosh(a / 2) * ⟪w, oneL⟫_ℝ - μ * sinh(a / 2) * ⟪w, tanhL⟫_ℝ`. -/
theorem eigenvector_thetaTranslate_pairing (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|))
    {μ : ℝ} {w : MassSpace} (heig : resolvent w = μ • w) :
    (2 * μ - 1) * ⟪w, (CHMDThetaTranslate.lift a ha).val.fst⟫_ℝ =
      μ * Real.cosh (a / 2) * ⟪w, oneL⟫_ℝ - μ * Real.sinh (a / 2) * ⟪w, tanhL⟫_ℝ := by
  have h1 := sourcePair_rieszLift_of_eigenvector heig (CHMDThetaTranslate.lift a ha)
  have h2 := sourcePair_thetaTranslate a ha (rieszLift w)
  have hfst : (rieszLift w).val.fst = μ • w := heig
  rw [sourcePair_symm] at h1
  rw [h1, hfst, real_inner_smul_left, real_inner_smul_left] at h2
  linarith

/-- Every primitive eigenvector `w` of `resolvent` with eigenvalue `μ ≠ 1/2` is orthogonal to the
symmetrized theta translate `(lift a ha + lift (-a) (neg_admissible ha)).val.fst` for every
admissible shift `a`. -/
theorem inner_symmThetaTranslate_eq_zero_of_primitive_eigenvector
    (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|))
    {μ : ℝ} (hμ : μ ≠ 1 / 2) {w : MassSpace} (hprim : ⟪w, oneL⟫_ℝ = 0)
    (heig : resolvent w = μ • w) :
    ⟪w, (CHMDThetaTranslate.lift a ha +
      CHMDThetaTranslate.lift (-a) (CHMDThetaTranslate.neg_admissible ha)).val.fst⟫_ℝ = 0 := by
  have h1 := eigenvector_thetaTranslate_pairing a ha heig
  have h2 := eigenvector_thetaTranslate_pairing (-a) (CHMDThetaTranslate.neg_admissible ha) heig
  rw [hprim, mul_zero, zero_sub] at h1 h2
  have hsinh : Real.sinh (-a / 2) = -Real.sinh (a / 2) := by
    rw [show -a / 2 = -(a / 2) by ring, Real.sinh_neg]
  rw [hsinh] at h2
  have hsum : (2 * μ - 1) *
      (⟪w, (CHMDThetaTranslate.lift a ha).val.fst⟫_ℝ +
        ⟪w, (CHMDThetaTranslate.lift (-a) (CHMDThetaTranslate.neg_admissible ha)).val.fst⟫_ℝ) = 0 := by
    linarith
  have hne : 2 * μ - 1 ≠ 0 := by intro h; apply hμ; linarith
  have h0 := (mul_eq_zero.mp hsum).resolve_left hne
  change ⟪w, (CHMDThetaTranslate.lift a ha).val.fst +
    (CHMDThetaTranslate.lift (-a) (CHMDThetaTranslate.neg_admissible ha)).val.fst⟫_ℝ = 0
  rwa [inner_add_right]

/-- Every even primitive eigenvector `w` of `resolvent` with eigenvalue `μ ≠ 1/2` is orthogonal to
every admissible theta translate `(lift a ha).val.fst`. -/
theorem inner_thetaTranslate_eq_zero_of_even_primitive_eigenvector
    (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|))
    {μ : ℝ} (hμ : μ ≠ 1 / 2) {w : MassSpace} (heven : reflectMass w = w)
    (hprim : ⟪w, oneL⟫_ℝ = 0) (heig : resolvent w = μ • w) :
    ⟪w, (CHMDThetaTranslate.lift a ha).val.fst⟫_ℝ = 0 := by
  have htanh : ⟪w, tanhL⟫_ℝ = 0 := by
    have h := reflectMass.inner_map_map w tanhL
    rw [heven, reflectMass_tanhL, inner_neg_right] at h
    linarith
  have h1 := eigenvector_thetaTranslate_pairing a ha heig
  rw [hprim, htanh, mul_zero, mul_zero, sub_zero] at h1
  have hne : 2 * μ - 1 ≠ 0 := by intro h; apply hμ; linarith
  exact (mul_eq_zero.mp h1).resolve_left hne

/-! ## Section 2: Quarter-Zero Orbit Separation and Exact Even Bound-State Dimension -/

theorem gammaOf_re (ρ : ℂ) : (gammaOf ρ).re = ρ.im := by
  unfold gammaOf
  simp [div_I]

theorem gammaOf_im (ρ : ℂ) : (gammaOf ρ).im = 1 / 2 - ρ.re := by
  unfold gammaOf
  simp [div_I]

theorem gammaOf_inj : Function.Injective gammaOf := by
  intro ρ σ h
  unfold gammaOf at h
  exact sub_left_injective ((div_left_inj' I_ne_zero).mp h)

theorem XiC_gammaOf_of_quarterZeros {ρ : ℂ} (hρ : ρ ∈ quarterZeros) :
    XiC (gammaOf ρ) = 0 :=
  CHMDStage16.XiC_gammaOf_eq_zero ⟨ρ, hρ.1⟩

theorem im_gammaOf_neg_of_quarterZeros {ρ : ℂ} (hρ : ρ ∈ quarterZeros) :
    (gammaOf ρ).im < 0 := by
  rw [gammaOf_im]
  linarith [hρ.2.1]

theorem im_gammaOf_ne_zero_of_quarterZeros {ρ : ℂ} (hρ : ρ ∈ quarterZeros) :
    (gammaOf ρ).im ≠ 0 :=
  (im_gammaOf_neg_of_quarterZeros hρ).ne

theorem re_gammaOf_pos_of_quarterZeros {ρ : ℂ} (hρ : ρ ∈ quarterZeros) :
    0 < (gammaOf ρ).re := by
  have hne : (gammaOf ρ).re ≠ 0 :=
    re_ne_zero_of_XiC_eq_zero (XiC_gammaOf_of_quarterZeros hρ)
  have hge : 0 ≤ (gammaOf ρ).re := by
    rw [gammaOf_re]
    exact hρ.2.2
  exact lt_of_le_of_ne hge hne.symm

/-- Distinct elements of `quarterZeros` have disjoint 4-element `cardinalOrbit`s. -/
theorem gammaOf_notMem_cardinalOrbit_of_ne {ρ σ : ℂ}
    (hρ : ρ ∈ quarterZeros) (hσ : σ ∈ quarterZeros) (hne : σ ≠ ρ) :
    gammaOf σ ∉ cardinalOrbit (gammaOf ρ) := by
  have hre_ρ := re_gammaOf_pos_of_quarterZeros hρ
  have him_ρ := im_gammaOf_neg_of_quarterZeros hρ
  have hre_σ := re_gammaOf_pos_of_quarterZeros hσ
  have him_σ := im_gammaOf_neg_of_quarterZeros hσ
  rintro (h | h | h | h)
  · exact hne (gammaOf_inj h)
  · have := congrArg Complex.re h
    simp only [Complex.neg_re] at this
    linarith
  · have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith
  · have := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.conj_re] at this
    linarith

/-- For every `a` with `0 < a.re` and `XiC a = 0`, the imaginary cardinal source `F.imVector` is
even (`reflectGraph F.imVector = F.imVector`). -/
theorem reflectGraph_imVector {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) :
    reflectGraph F.imVector = F.imVector := by
  apply reflectGraph_eq_self_of_even
  rw [Lp.ext_iff]
  obtain ⟨_, _, _, he, _⟩ := divisorCardinalSource_regularity ha hz
  have hcomp := measurePreserving_neg_mass.quasiMeasurePreserving.ae F.im_source
  filter_upwards [reflectMass_coeFn F.imVector.val.fst, F.im_source, hcomp] with x hx1 hx2 hx3
  rw [hx1, hx2, hx3]
  simp only [phiDoobInv, he x, WeilExcess.riemannKernelReal_neg]

theorem imVector_fst_mem_evenSector {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) :
    F.imVector.val.fst ∈ evenSector := by
  rw [mem_evenSector, ← reflectGraph_fst, reflectGraph_imVector F ha hz]

theorem inner_imVector_oneL {a : ℂ} (F : CardinalGraphFrame a) :
    ⟪F.imVector.val.fst, oneL⟫_ℝ = 0 := by
  have h1 := F.im_primitive
  rw [sourcePair_ground_eq_polarCosine, polarCosine_oneL] at h1
  linarith

/-- Orthogonal decomposition of `boundStateSpace` implies that an even vector orthogonal to
`evenBoundStateSpace` is orthogonal to all of `boundStateSpace`. -/
theorem mem_orthogonal_boundStateSpace_of_even {w : MassSpace} (hwE : w ∈ evenSector)
    (h : w ∈ evenBoundStateSpaceᗮ) : w ∈ boundStateSpaceᗮ := by
  rw [boundStateSpace_eq_sup_even_odd]
  intro u hu
  rw [Submodule.mem_sup] at hu
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := hu
  rw [inner_add_left, h u₁ hu₁, zero_add]
  have hu₂O : u₂ ∈ oddSector := oddBoundStateSpace_le_oddSector hu₂
  have h_orth := reflectMass.inner_map_map u₂ w
  rw [mem_oddSector.mp hu₂O, mem_evenSector.mp hwE, inner_neg_left] at h_orth
  linarith

/-- Orthogonal decomposition of `boundStateSpace` implies that an odd vector orthogonal to
`oddBoundStateSpace` is orthogonal to all of `boundStateSpace`. -/
theorem mem_orthogonal_boundStateSpace_of_odd {w : MassSpace} (hwO : w ∈ oddSector)
    (h : w ∈ oddBoundStateSpaceᗮ) : w ∈ boundStateSpaceᗮ := by
  rw [boundStateSpace_eq_sup_even_odd]
  intro u hu
  rw [Submodule.mem_sup] at hu
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := hu
  rw [inner_add_left, h u₂ hu₂, add_zero]
  have hu₁E : u₁ ∈ evenSector := evenBoundStateSpace_le_evenSector hu₁
  have h_orth := reflectMass.inner_map_map u₁ w
  rw [mem_evenSector.mp hu₁E, mem_oddSector.mp hwO, inner_neg_right] at h_orth
  linarith

theorem sourcePair_smul_right (c : ℝ) (p q : SourceGraph) :
    sourcePair p (c • q) = c * sourcePair p q := by
  rw [sourcePair_symm, sourcePair_smul_left, sourcePair_symm q p]

theorem sourcePair_neg_left (p q : SourceGraph) :
    sourcePair (-p) q = -sourcePair p q := by
  rw [← neg_one_smul ℝ p, sourcePair_smul_left, neg_one_mul]

theorem sourcePair_reflectGraph (p q : SourceGraph) :
    sourcePair (reflectGraph p) (reflectGraph q) = sourcePair p q := by
  rw [sourcePair_eq_graph_inner, sourcePair_eq_graph_inner,
    ← reflectGraphₗᵢ_apply, ← reflectGraphₗᵢ_apply, reflectGraphₗᵢ.inner_map_map,
    reflectGraphₗᵢ_apply, reflectGraphₗᵢ_apply]
  change _ - 2 * ⟪reflectMass p.val.fst, reflectMass q.val.fst⟫_ℝ = _
  rw [reflectMass.inner_map_map]
  rfl

theorem sourcePair_sum_left {ι : Type*} (s : Finset ι) (f : ι → SourceGraph) (q : SourceGraph) :
    sourcePair (∑ i ∈ s, f i) q = ∑ i ∈ s, sourcePair (f i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sourcePair]
  | @insert a s ha ih => rw [Finset.sum_insert ha, sourcePair_add_left, ih, Finset.sum_insert ha]

theorem sourcePair_sum_right {ι : Type*} (p : SourceGraph) (s : Finset ι) (f : ι → SourceGraph) :
    sourcePair p (∑ i ∈ s, f i) = ∑ i ∈ s, sourcePair p (f i) := by
  rw [sourcePair_symm, sourcePair_sum_left]
  exact Finset.sum_congr rfl fun i _ => sourcePair_symm (f i) p

theorem sum_sourceEnergy_diagonal {k : ℕ} (p : Fin k → SourceGraph) (d : Fin k → ℝ)
    (hdiag : ∀ i j, sourcePair (p i) (p j) = if i = j then d i else 0) (c : Fin k → ℝ) :
    sourceEnergy (∑ i, c i • p i) = ∑ i, c i ^ 2 * d i := by
  rw [← sourcePair_self, sourcePair_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sourcePair_smul_left, sourcePair_sum_right]
  have hsum : (∑ x, sourcePair (p i) (c x • p x)) = c i * d i := by
    rw [Finset.sum_eq_single i]
    · rw [sourcePair_smul_right, hdiag i i, if_pos rfl]
    · intro j _ hji
      rw [sourcePair_smul_right, hdiag i j, if_neg (Ne.symm hji), mul_zero]
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  rw [hsum]
  ring

theorem sum_sq_mul_neg_of_pos {k : ℕ} {m : Fin k → ℝ} (hm : ∀ i, 0 < m i)
    {c : Fin k → ℝ} (hc : c ≠ 0) :
    (∑ i, c i ^ 2 * -m i) < 0 := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hc
  have hsum_pos : 0 < ∑ i, c i ^ 2 * m i := by
    have hle : c i₀ ^ 2 * m i₀ ≤ ∑ i, c i ^ 2 * m i :=
      Finset.single_le_sum (fun i _ => mul_nonneg (sq_nonneg (c i)) (hm i).le) (Finset.mem_univ i₀)
    have hpos : 0 < c i₀ ^ 2 * m i₀ := mul_pos (sq_pos_of_ne_zero hi₀) (hm i₀)
    linarith
  have heq : (∑ i, c i ^ 2 * -m i) = -∑ i, c i ^ 2 * m i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

/-- **Unconditional Even Birman–Schwinger Lower Bound**:
if `evenBoundStateSpace` is finite-dimensional, then for every injection of `Fin k` into
`quarterZeros`, `k + 1 ≤ finrank ℝ evenBoundStateSpace`. -/
theorem card_add_one_le_finrank_evenBoundStateSpace [FiniteDimensional ℝ evenBoundStateSpace]
    {k : ℕ} (ρ : Fin k → ℂ) (hρ : ∀ i, ρ i ∈ quarterZeros) (hinj : Function.Injective ρ) :
    k + 1 ≤ Module.finrank ℝ evenBoundStateSpace := by
  classical
  let a : Fin k → ℂ := fun i => gammaOf (ρ i)
  have ha : ∀ i, 0 < (a i).re := fun i => re_gammaOf_pos_of_quarterZeros (hρ i)
  have hz : ∀ i, XiC (a i) = 0 := fun i => XiC_gammaOf_of_quarterZeros (hρ i)
  have hi : ∀ i, (a i).im ≠ 0 := fun i => im_gammaOf_ne_zero_of_quarterZeros (hρ i)
  have ho : ∀ i j, i ≠ j → a j ∉ cardinalOrbit (a i) :=
    fun i j hij => gammaOf_notMem_cardinalOrbit_of_ne (hρ i) (hρ j) (fun h => hij (hinj h).symm)
  let F : ∀ i, CardinalGraphFrame (a i) :=
    fun i => Classical.choice (exists_cardinalGraphFrame (ha i) (hz i))
  let p : Fin k → SourceGraph := fun i => (F i).imVector
  have hdiag : ∀ i j, sourcePair (p i) (p j) =
      if i = j then -cardinalPositiveMass (a i) else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, sourcePair_self, (F i).im_energy,
        ← cardinalPositiveMass_eq_negative (ha i) (hi i)]
    · rw [if_neg hij, (F j).pair_im (ha j) (hz j),
        ((F i).readouts_outside_orbit (ha i) (hz i) (hz j) (ho i j hij)).2,
        Complex.zero_im, mul_zero]
  haveI : IsClosed (evenBoundStateSpace : Set MassSpace) :=
    Submodule.closed_of_finiteDimensional evenBoundStateSpace
  haveI : CompleteSpace evenBoundStateSpace := IsClosed.completeSpace_coe
  let ℓ : evenBoundStateSpace →ₗ[ℝ] ℝ :=
    { toFun := fun u => ⟪(u : MassSpace), oneL⟫_ℝ
      map_add' := fun u v => by simp [inner_add_left]
      map_smul' := fun r u => by simp [real_inner_smul_left] }
  let P := evenBoundStateSpace.orthogonalProjectionOnto
  let Φ₀ : (Fin k → ℝ) →ₗ[ℝ] evenBoundStateSpace :=
    { toFun := fun c => P (∑ i, c i • (p i).val.fst)
      map_add' := fun c d => by simp [Finset.sum_add_distrib, add_smul, map_add]
      map_smul' := fun r c => by simp [Finset.smul_sum, smul_smul, map_smul] }
  have hΦ₀_ker : ∀ c, Φ₀ c ∈ LinearMap.ker ℓ := by
    intro c
    rw [LinearMap.mem_ker]
    change ⟪(P (∑ i, c i • (p i).val.fst) : MassSpace), oneL⟫_ℝ = 0
    have horth : (∑ i, c i • (p i).val.fst) - (P (∑ i, c i • (p i).val.fst) : MassSpace) ∈
        evenBoundStateSpaceᗮ :=
      Submodule.sub_starProjection_mem_orthogonal (∑ i, c i • (p i).val.fst)
    have h0 := horth oneL oneL_mem_evenBoundStateSpace
    rw [real_inner_comm, inner_sub_left] at h0
    have hsum0 : ⟪∑ i, c i • (p i).val.fst, oneL⟫_ℝ = 0 := by
      rw [sum_inner]
      exact Finset.sum_eq_zero fun i _ => by
        rw [real_inner_smul_left, inner_imVector_oneL (F i), mul_zero]
    linarith
  let Φ : (Fin k → ℝ) →ₗ[ℝ] LinearMap.ker ℓ := LinearMap.codRestrict (LinearMap.ker ℓ) Φ₀ hΦ₀_ker
  have hinjΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    by_contra hc0
    rw [LinearMap.mem_ker, Subtype.ext_iff] at hc
    change P (∑ i, c i • (p i).val.fst) = 0 at hc
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff] at hc
    set q := ∑ i, c i • p i
    have hq_fst : q.val.fst = ∑ i, c i • (p i).val.fst :=
      map_sum sourceMap (fun i => c i • p i) Finset.univ
    have hq_even : q.val.fst ∈ evenSector := by
      rw [hq_fst]
      exact Submodule.sum_mem _ fun i _ =>
        evenSector.smul_mem _ (imVector_fst_mem_evenSector (F i) (ha i) (hz i))
    have hq_orth : q.val.fst ∈ boundStateSpaceᗮ :=
      mem_orthogonal_boundStateSpace_of_even hq_even (by rwa [hq_fst])
    have hE : sourceEnergy q < 0 := by
      rw [sum_sourceEnergy_diagonal p _ hdiag c]
      exact sum_sq_mul_neg_of_pos (fun i => cardinalPositiveMass_pos_of_zero (hz i)) hc0
    exact fst_notMem_orthogonal_of_energy_neg hE hq_orth
  have hk_le : k ≤ Module.finrank ℝ (LinearMap.ker ℓ) := by
    have h := LinearMap.finrank_le_finrank_of_injective hinjΦ
    rwa [Module.finrank_fin_fun] at h
  have hrange : Module.finrank ℝ (LinearMap.range ℓ) = 1 := by
    have hle : Module.finrank ℝ (LinearMap.range ℓ) ≤ 1 := by
      calc Module.finrank ℝ (LinearMap.range ℓ) ≤ Module.finrank ℝ ℝ := Submodule.finrank_le _
        _ = 1 := Module.finrank_self ℝ
    have hpos : 0 < Module.finrank ℝ (LinearMap.range ℓ) := by
      rw [Module.finrank_pos_iff]
      refine ⟨⟨⟨ℓ ⟨oneL, oneL_mem_evenBoundStateSpace⟩, LinearMap.mem_range_self ℓ _⟩, 0, ?_⟩⟩
      intro h0
      have h1 : ⟪oneL, oneL⟫_ℝ = 0 := congrArg Subtype.val h0
      rw [real_inner_self_eq_norm_sq, norm_oneL_sq] at h1
      linarith
    omega
  have hrn := LinearMap.finrank_range_add_finrank_ker ℓ
  omega

/-! ## Section 3: Odd Translated Cardinal Negative Modes and Exact Parity Bound-State Dimensions -/

theorem graphFourierReadout_reflectGraph (p : SourceGraph) (z : ℂ) :
    graphFourierReadout (reflectGraph p) z = graphFourierReadout p (-z) := by
  rw [graphFourierReadout, graphFourierReadout, ← paperFT_comp_neg]
  unfold paperFT
  apply integral_congr_ae
  filter_upwards [volume_absolutelyContinuous_mass.ae_eq (reflectMass_coeFn p.val.fst)] with x hx
  change ((phiDoobTest (reflectMass p.val.fst) x : ℝ) : ℂ) * _ = _
  rw [phiDoobTest, hx, phiDoobTest, WeilExcess.riemannKernelReal_neg]

theorem graphFourierReadout_neg_of_odd {p : SourceGraph} (hp : reflectGraph p = -p)
    {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    graphFourierReadout p (-z) = -graphFourierReadout p z := by
  rw [← graphFourierReadout_reflectGraph, hp, ← neg_one_smul ℝ p,
    graphFourierReadout_smul (-1) p hz]
  push_cast
  ring

theorem shiftedCosineReadout_of_odd {p : SourceGraph} (hp : reflectGraph p = -p)
    {z : ℂ} (hz : |z.im| ≤ 1 / 2) (t : ℝ) :
    shiftedCosineReadout p z t =
      -((exp ((I * z) * (t : ℂ)) - exp (-(I * z) * (t : ℂ))) / 2) *
        graphFourierReadout p z := by
  unfold shiftedCosineReadout
  rw [graphFourierReadout_neg_of_odd hp hz]
  ring

/-- Odd projection of a graph vector `q : SourceGraph`. -/
def oddGraphPart (q : SourceGraph) : SourceGraph :=
  (1 / 2 : ℝ) • (q - reflectGraph q)

theorem reflectGraph_oddGraphPart (q : SourceGraph) :
    reflectGraph (oddGraphPart q) = -oddGraphPart q := by
  unfold oddGraphPart
  rw [reflectGraph_smul, reflectGraph_sub, reflectGraph_reflectGraph]
  module

theorem oddGraphPart_fst_mem_oddSector (q : SourceGraph) :
    (oddGraphPart q).val.fst ∈ oddSector := by
  rw [mem_oddSector, ← reflectGraph_fst, reflectGraph_oddGraphPart]
  rfl

theorem sourcePair_odd_oddGraphPart {p : SourceGraph} (hp : reflectGraph p = -p) (q : SourceGraph) :
    sourcePair p (oddGraphPart q) = sourcePair p q := by
  have hr : sourcePair p (reflectGraph q) = -sourcePair p q := by
    have h1 := sourcePair_reflectGraph p (reflectGraph q)
    rw [reflectGraph_reflectGraph, hp, sourcePair_neg_left] at h1
    linarith
  unfold oddGraphPart
  rw [sourcePair_smul_right, sourcePair_sub_right, hr]
  ring

theorem graphFourierReadout_oddGraphPart (q : SourceGraph) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    graphFourierReadout (oddGraphPart q) z =
      (graphFourierReadout q z - graphFourierReadout q (-z)) / 2 := by
  unfold oddGraphPart
  rw [graphFourierReadout_smul _ _ hz, graphFourierReadout_sub _ _ hz,
    graphFourierReadout_reflectGraph]
  push_cast
  ring

theorem shiftedCosineReadout_oddGraphPart (q : SourceGraph) {z : ℂ} (hz : |z.im| ≤ 1 / 2) (t : ℝ) :
    shiftedCosineReadout (oddGraphPart q) z t =
      -((exp ((I * z) * (t : ℂ)) - exp (-(I * z) * (t : ℂ))) / 2) *
        ((graphFourierReadout q z - graphFourierReadout q (-z)) / 2) := by
  rw [shiftedCosineReadout_of_odd (reflectGraph_oddGraphPart q) hz,
    graphFourierReadout_oddGraphPart q hz]

theorem cardinalOrbitValue_neg (a c z : ℂ) :
    cardinalOrbitValue a c (-z) = cardinalOrbitValue a c z := by
  unfold cardinalOrbitValue
  rw [unsignedOrbitIndicator_neg, map_neg, unsignedOrbitIndicator_neg]

theorem exp_sub_exp_neg_div_two_ne_zero {a : ℂ} (hi : a.im ≠ 0) {t : ℝ} (ht : 0 < t) :
    (exp ((I * a) * (t : ℂ)) - exp (-(I * a) * (t : ℂ))) / 2 ≠ 0 := by
  intro h
  have hsub : exp ((I * a) * (t : ℂ)) = exp (-(I * a) * (t : ℂ)) :=
    sub_eq_zero.mp ((div_eq_zero_iff.mp h).resolve_right two_ne_zero)
  have hnorm := congrArg Norm.norm hsub
  rw [neg_mul, Complex.norm_exp, Complex.norm_exp, Real.exp_eq_exp] at hnorm
  have hre : ((I * a) * (t : ℂ)).re = -a.im * t := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [Complex.neg_re, hre] at hnorm
  have : a.im * t = 0 := by linarith
  exact mul_ne_zero hi ht.ne' this

/-- For every nonreal Xi zero `a` with `0 < a.re`, there exists an explicit odd graph vector `w`
whose `sourcePair` against any odd graph vector `p` is supported on `cardinalOrbit a`, and whose
self-pairing is `-cardinalOrbitMass a / 2 < 0`. -/
theorem exists_odd_translated_cardinal_negative_mode {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0)
    (hi : a.im ≠ 0) :
    ∃ w : SourceGraph,
      reflectGraph w = -w ∧
      sourceEnergy w = -(cardinalOrbitMass a / 2) ∧
      (∀ z : ℂ, XiC z = 0 → z ∉ cardinalOrbit a →
        shiftedCosineReadout w z CHMDThetaTranslate.radius = 0) ∧
      (∀ p : SourceGraph, reflectGraph p = -p →
        (∀ z : ℂ, XiC z = 0 → z ∈ cardinalOrbit a →
          shiftedCosineReadout p z CHMDThetaTranslate.radius = 0) →
        sourcePair p w = 0) := by
  set t := CHMDThetaTranslate.radius
  have ht_pos : 0 < t := CHMDThetaTranslate.radius_pos
  have ht_le : |t| ≤ CHMDThetaTranslate.radius := by rw [abs_of_pos ht_pos]
  obtain ⟨u, v, hus, hvs, hu_pair, hv_pair⟩ := exists_translatedCardinalFrame ha hz t ht_le
  set uO := oddGraphPart u
  set vO := oddGraphPart v
  have hu_ft : ∀ z : ℂ, XiC z = 0 →
      graphFourierReadout u z = exp ((I * z) * (t : ℂ)) * cardinalOrbitValue a 1 z := by
    intro z hzero
    rw [graphFourierReadout_of_source hus, paperFT_translate_real]
    have h1 : (fun x => ((divisorCardinalSource a x).re : ℂ)) =
        (fun x => (cardinalRealSource a 1 x : ℂ)) := by
      funext x; simp [cardinalRealSource]
    rw [h1, cardinalRealSource_paperFT ha hz 1 hzero, mul_assoc]
  have hv_ft : ∀ z : ℂ, XiC z = 0 →
      graphFourierReadout v z = exp ((I * z) * (t : ℂ)) * cardinalOrbitValue a (-I) z := by
    intro z hzero
    rw [graphFourierReadout_of_source hvs, paperFT_translate_real]
    have h1 : (fun x => ((divisorCardinalSource a x).im : ℂ)) =
        (fun x => (cardinalRealSource a (-I) x : ℂ)) := by
      funext x; simp [cardinalRealSource, Complex.mul_re]
    rw [h1, cardinalRealSource_paperFT ha hz (-I) hzero, mul_assoc]
  let δ : ℂ → ℂ := fun z => (exp ((I * z) * (t : ℂ)) - exp (-(I * z) * (t : ℂ))) / 2
  have huO_shift : ∀ z : ℂ, XiC z = 0 →
      shiftedCosineReadout uO z t = -δ z ^ 2 * cardinalOrbitValue a 1 z := by
    intro z hzero
    have hstrip := (abs_im_lt_half_of_XiC_eq_zero hzero).le
    have hzn : XiC (-z) = 0 := by rw [XiC_even, hzero]
    rw [shiftedCosineReadout_oddGraphPart u hstrip t, hu_ft z hzero, hu_ft (-z) hzn,
      cardinalOrbitValue_neg]
    dsimp [δ]
    ring
  have hvO_shift : ∀ z : ℂ, XiC z = 0 →
      shiftedCosineReadout vO z t = -δ z ^ 2 * cardinalOrbitValue a (-I) z := by
    intro z hzero
    have hstrip := (abs_im_lt_half_of_XiC_eq_zero hzero).le
    have hzn : XiC (-z) = 0 := by rw [XiC_even, hzero]
    rw [shiftedCosineReadout_oddGraphPart v hstrip t, hv_ft z hzero, hv_ft (-z) hzn,
      cardinalOrbitValue_neg]
    dsimp [δ]
    ring
  have hδa_ne : δ a ≠ 0 := exp_sub_exp_neg_div_two_ne_zero hi ht_pos
  set lam : ℂ := (δ a)⁻¹
  set w : SourceGraph := lam.re • uO - lam.im • vO
  have hw_odd : reflectGraph w = -w := by
    dsimp [w]
    rw [reflectGraph_sub, reflectGraph_smul, reflectGraph_smul,
      reflectGraph_oddGraphPart, reflectGraph_oddGraphPart]
    module
  have hshift_add : ∀ (p q : SourceGraph) (z : ℂ), |z.im| ≤ 1 / 2 →
      shiftedCosineReadout (p + q) z t =
        shiftedCosineReadout p z t + shiftedCosineReadout q z t := by
    intro p q z hst
    have hstn : |(-z).im| ≤ 1 / 2 := by simpa using hst
    unfold shiftedCosineReadout
    rw [graphFourierReadout_add p q hst, graphFourierReadout_add p q hstn]
    ring
  have hshift_sub : ∀ (p q : SourceGraph) (z : ℂ), |z.im| ≤ 1 / 2 →
      shiftedCosineReadout (p - q) z t =
        shiftedCosineReadout p z t - shiftedCosineReadout q z t := by
    intro p q z hst
    have hstn : |(-z).im| ≤ 1 / 2 := by simpa using hst
    unfold shiftedCosineReadout
    rw [graphFourierReadout_sub p q hst, graphFourierReadout_sub p q hstn]
    ring
  have hshift_smul : ∀ (r : ℝ) (p : SourceGraph) (z : ℂ), |z.im| ≤ 1 / 2 →
      shiftedCosineReadout (r • p) z t = (r : ℂ) * shiftedCosineReadout p z t := by
    intro r p z hst
    have hstn : |(-z).im| ≤ 1 / 2 := by simpa using hst
    unfold shiftedCosineReadout
    rw [graphFourierReadout_smul r p hst, graphFourierReadout_smul r p hstn]
    ring
  have hw_shift_out : ∀ z : ℂ, XiC z = 0 → z ∉ cardinalOrbit a →
      shiftedCosineReadout w z t = 0 := by
    intro z hzero ho
    have hst := (abs_im_lt_half_of_XiC_eq_zero hzero).le
    dsimp [w]
    rw [hshift_sub _ _ _ hst, hshift_smul _ _ _ hst, hshift_smul _ _ _ hst,
      huO_shift z hzero, hvO_shift z hzero,
      cardinalOrbitValue_eq_zero ho, cardinalOrbitValue_eq_zero ho]
    simp
  have hw_pair_odd : ∀ p : SourceGraph, reflectGraph p = -p →
      sourcePair p w =
        cardinalOrbitMass a * (lam * shiftedCosineReadout p a t).re := by
    intro p hp
    dsimp [w]
    rw [sourcePair_sub_right, sourcePair_smul_right, sourcePair_smul_right,
      sourcePair_odd_oddGraphPart hp u, sourcePair_odd_oddGraphPart hp v,
      hu_pair p, hv_pair p, Complex.mul_re]
    ring
  refine ⟨w, hw_odd, ?_, hw_shift_out, ?_⟩
  · have hst_a := (abs_im_lt_half_of_XiC_eq_zero hz).le
    have hval1 : cardinalOrbitValue a 1 a = 1 / 2 := by
      have hA : unsignedOrbitIndicator a a = 1 := by simp [unsignedOrbitIndicator]
      have hB : unsignedOrbitIndicator a (conj a) = 0 := by
        simpa [hA] using unsignedOrbitIndicators_disjoint ha hi a
      simp [cardinalOrbitValue, hA, hB]
    have hvalI : cardinalOrbitValue a (-I) a = -I / 2 := by
      have hA : unsignedOrbitIndicator a a = 1 := by simp [unsignedOrbitIndicator]
      have hB : unsignedOrbitIndicator a (conj a) = 0 := by
        simpa [hA] using unsignedOrbitIndicators_disjoint ha hi a
      simp [cardinalOrbitValue, hA, hB]
    have hw_shift_a : shiftedCosineReadout w a t = -(1 / 2 : ℂ) * lam * δ a ^ 2 := by
      dsimp [w]
      rw [hshift_sub _ _ _ hst_a, hshift_smul _ _ _ hst_a, hshift_smul _ _ _ hst_a,
        huO_shift a hz, hvO_shift a hz, hval1, hvalI]
      have hlam_eq : (lam.re : ℂ) + (lam.im : ℂ) * I = lam := Complex.re_add_im lam
      linear_combination -(1 / 2 : ℂ) * δ a ^ 2 * hlam_eq
    rw [← sourcePair_self, hw_pair_odd w hw_odd, hw_shift_a]
    have hprod : lam * (-(1 / 2 : ℂ) * lam * δ a ^ 2) = -(1 / 2 : ℂ) := by
      have h1 : lam * δ a = 1 := inv_mul_cancel₀ hδa_ne
      calc lam * (-(1 / 2 : ℂ) * lam * δ a ^ 2)
          = -(1 / 2 : ℂ) * (lam * δ a) ^ 2 := by ring
        _ = -(1 / 2 : ℂ) := by rw [h1]; ring
    rw [hprod]
    norm_num
    ring
  · intro p hp hzero_a
    rw [hw_pair_odd p hp, hzero_a a hz (by simp [cardinalOrbit])]
    simp

/-- **Unconditional Odd Birman–Schwinger Lower Bound**:
if `oddBoundStateSpace` is finite-dimensional, then for every injection of `Fin k` into
`quarterZeros`, `k ≤ finrank ℝ oddBoundStateSpace`. -/
theorem card_le_finrank_oddBoundStateSpace [FiniteDimensional ℝ oddBoundStateSpace]
    {k : ℕ} (ρ : Fin k → ℂ) (hρ : ∀ i, ρ i ∈ quarterZeros) (hinj : Function.Injective ρ) :
    k ≤ Module.finrank ℝ oddBoundStateSpace := by
  classical
  let a : Fin k → ℂ := fun i => gammaOf (ρ i)
  have ha : ∀ i, 0 < (a i).re := fun i => re_gammaOf_pos_of_quarterZeros (hρ i)
  have hz : ∀ i, XiC (a i) = 0 := fun i => XiC_gammaOf_of_quarterZeros (hρ i)
  have hi : ∀ i, (a i).im ≠ 0 := fun i => im_gammaOf_ne_zero_of_quarterZeros (hρ i)
  have ho : ∀ i j, i ≠ j → a j ∉ cardinalOrbit (a i) :=
    fun i j hij => gammaOf_notMem_cardinalOrbit_of_ne (hρ i) (hρ j) (fun h => hij (hinj h).symm)
  choose w hw_odd hw_energy hw_out hw_pair using
    fun i => exists_odd_translated_cardinal_negative_mode (ha i) (hz i) (hi i)
  have hdiag : ∀ i j, sourcePair (w i) (w j) =
      if i = j then -(cardinalOrbitMass (a i) / 2) else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, sourcePair_self, hw_energy i]
    · rw [if_neg hij]
      refine hw_pair j (w i) (hw_odd i) fun z hzero hmem => ?_
      refine hw_out i z hzero fun hmem_i => ?_
      have horb : a j ∈ cardinalOrbit (a i) := by
        rcases hmem with rfl | rfl | rfl | rfl
        · exact hmem_i
        · simpa using cardinalOrbit_neg_mem hmem_i
        · rcases hmem_i with h | h | h | h
          · exact Or.inr (Or.inr (Or.inl (by simpa using congrArg conj h)))
          · exact Or.inr (Or.inr (Or.inr (by simpa using congrArg conj h)))
          · exact Or.inl (by simpa using congrArg conj h)
          · exact Or.inr (Or.inl (by simpa using congrArg conj h))
        · rcases hmem_i with h | h | h | h
          · exact Or.inr (Or.inr (Or.inr (by simpa using congrArg (fun x => -conj x) h)))
          · exact Or.inr (Or.inr (Or.inl (by simpa using congrArg (fun x => -conj x) h)))
          · exact Or.inr (Or.inl (by simpa using congrArg (fun x => -conj x) h))
          · exact Or.inl (by simpa using congrArg (fun x => -conj x) h)
      exact ho i j hij horb
  haveI : IsClosed (oddBoundStateSpace : Set MassSpace) :=
    Submodule.closed_of_finiteDimensional oddBoundStateSpace
  haveI : CompleteSpace oddBoundStateSpace := IsClosed.completeSpace_coe
  let P := oddBoundStateSpace.orthogonalProjectionOnto
  let Φ : (Fin k → ℝ) →ₗ[ℝ] oddBoundStateSpace :=
    { toFun := fun c => P (∑ i, c i • (w i).val.fst)
      map_add' := fun c d => by simp [Finset.sum_add_distrib, add_smul, map_add]
      map_smul' := fun r c => by simp [Finset.smul_sum, smul_smul, map_smul] }
  have hinjΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    by_contra hc0
    rw [LinearMap.mem_ker] at hc
    change P (∑ i, c i • (w i).val.fst) = 0 at hc
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff] at hc
    set q := ∑ i, c i • w i
    have hq_fst : q.val.fst = ∑ i, c i • (w i).val.fst :=
      map_sum sourceMap (fun i => c i • w i) Finset.univ
    have hq_odd : q.val.fst ∈ oddSector := by
      rw [hq_fst]
      exact Submodule.sum_mem _ fun i _ =>
        oddSector.smul_mem _ (by rw [mem_oddSector, ← reflectGraph_fst, hw_odd i]; rfl)
    have hq_orth : q.val.fst ∈ boundStateSpaceᗮ :=
      mem_orthogonal_boundStateSpace_of_odd hq_odd (by rwa [hq_fst])
    have hE : sourceEnergy q < 0 := by
      rw [sum_sourceEnergy_diagonal w _ hdiag c]
      exact sum_sq_mul_neg_of_pos
        (fun i => half_pos (cardinalOrbitMass_pos (ha i) (hz i))) hc0
    exact fst_notMem_orthogonal_of_energy_neg hE hq_orth
  have h := LinearMap.finrank_le_finrank_of_injective hinjΦ
  rwa [Module.finrank_fin_fun] at h

/-! ## Section 4: Finiteness Equivalences and Exact Dimension Formulas -/

theorem offLineZeros_subset_four_images :
    offLineZeros ⊆ quarterZeros ∪ (conj '' quarterZeros) ∪
      (reflect '' quarterZeros) ∪ ((fun σ => reflect (conj σ)) '' quarterZeros) := by
  intro ρ hρ
  obtain ⟨σ, hσ, rfl | rfl | rfl | rfl⟩ := exists_quarter_of_offLine hρ
  · exact Or.inl (Or.inl (Or.inl hσ))
  · exact Or.inl (Or.inl (Or.inr ⟨σ, hσ, rfl⟩))
  · exact Or.inl (Or.inr ⟨σ, hσ, rfl⟩)
  · exact Or.inr ⟨σ, hσ, rfl⟩

theorem offLineZeros_finite_iff_quarterZeros_finite :
    offLineZeros.Finite ↔ quarterZeros.Finite := by
  constructor
  · exact fun h => h.subset quarterZeros_subset_offLine
  · intro h
    exact (((h.union (h.image _)).union (h.image _)).union (h.image _)).subset
      offLineZeros_subset_four_images

theorem quarterZeros_finite_of_finiteDimensional_oddBoundStateSpace
    [FiniteDimensional ℝ oddBoundStateSpace] : quarterZeros.Finite := by
  by_contra hinf
  obtain ⟨t, htb, htc⟩ := Set.Infinite.exists_subset_card_eq hinf
    (Module.finrank ℝ oddBoundStateSpace + 1)
  let e := t.equivFin
  let ρ : Fin t.card → ℂ := fun i => (e.symm i).1
  have hρ : ∀ i, ρ i ∈ quarterZeros := fun i => htb (e.symm i).2
  have hinj : Function.Injective ρ := fun i j h => e.symm.injective (Subtype.ext h)
  have hle := card_le_finrank_oddBoundStateSpace ρ hρ hinj
  omega

theorem quarterZeros_finite_of_finiteDimensional_evenBoundStateSpace
    [FiniteDimensional ℝ evenBoundStateSpace] : quarterZeros.Finite := by
  by_contra hinf
  obtain ⟨t, htb, htc⟩ := Set.Infinite.exists_subset_card_eq hinf
    (Module.finrank ℝ evenBoundStateSpace)
  let e := t.equivFin
  let ρ : Fin t.card → ℂ := fun i => (e.symm i).1
  have hρ : ∀ i, ρ i ∈ quarterZeros := fun i => htb (e.symm i).2
  have hinj : Function.Injective ρ := fun i j h => e.symm.injective (Subtype.ext h)
  have hle := card_add_one_le_finrank_evenBoundStateSpace ρ hρ hinj
  omega

theorem offLineZeros_finite_iff_finiteDimensional_oddBoundStateSpace :
    offLineZeros.Finite ↔ FiniteDimensional ℝ oddBoundStateSpace :=
  ⟨finiteDimensional_oddBoundStateSpace, fun _ =>
    offLineZeros_finite_iff_quarterZeros_finite.mpr
      quarterZeros_finite_of_finiteDimensional_oddBoundStateSpace⟩

theorem offLineZeros_finite_iff_finiteDimensional_evenBoundStateSpace :
    offLineZeros.Finite ↔ FiniteDimensional ℝ evenBoundStateSpace :=
  ⟨finiteDimensional_evenBoundStateSpace, fun _ =>
    offLineZeros_finite_iff_quarterZeros_finite.mpr
      quarterZeros_finite_of_finiteDimensional_evenBoundStateSpace⟩

theorem offLineZeros_finite_iff_finiteDimensional_boundStateSpace :
    offLineZeros.Finite ↔ FiniteDimensional ℝ boundStateSpace :=
  ⟨finiteDimensional_boundStateSpace, fun _ => by
    haveI : FiniteDimensional ℝ oddBoundStateSpace :=
      Submodule.finiteDimensional_of_le oddBoundStateSpace_le_boundStateSpace
    exact offLineZeros_finite_iff_finiteDimensional_oddBoundStateSpace.mpr inferInstance⟩

/-- **Exact Dimension of `oddBoundStateSpace`**:
when `offLineZeros` is finite, `finrank ℝ oddBoundStateSpace = #(quarterZeros)`. -/
theorem finrank_oddBoundStateSpace_eq (hfin : offLineZeros.Finite) :
    Module.finrank ℝ oddBoundStateSpace = quarterZeros.ncard := by
  haveI : FiniteDimensional ℝ oddBoundStateSpace := finiteDimensional_oddBoundStateSpace hfin
  refine le_antisymm (finrank_oddBoundStateSpace_le hfin) ?_
  let t := quarterFinset hfin
  let e := t.equivFin
  let ρ : Fin t.card → ℂ := fun i => (e.symm i).1
  have hρ : ∀ i, ρ i ∈ quarterZeros := fun i => (mem_quarterFinset hfin).mp (e.symm i).2
  have hinj : Function.Injective ρ := fun i j h => e.symm.injective (Subtype.ext h)
  have hle := card_le_finrank_oddBoundStateSpace ρ hρ hinj
  rwa [card_quarterFinset hfin] at hle

/-- **Exact Dimension of `evenBoundStateSpace`**:
when `offLineZeros` is finite, `finrank ℝ evenBoundStateSpace = #(quarterZeros) + 1`. -/
theorem finrank_evenBoundStateSpace_eq (hfin : offLineZeros.Finite) :
    Module.finrank ℝ evenBoundStateSpace = quarterZeros.ncard + 1 := by
  haveI : FiniteDimensional ℝ evenBoundStateSpace := finiteDimensional_evenBoundStateSpace hfin
  refine le_antisymm (finrank_evenBoundStateSpace_le hfin) ?_
  let t := quarterFinset hfin
  let e := t.equivFin
  let ρ : Fin t.card → ℂ := fun i => (e.symm i).1
  have hρ : ∀ i, ρ i ∈ quarterZeros := fun i => (mem_quarterFinset hfin).mp (e.symm i).2
  have hinj : Function.Injective ρ := fun i j h => e.symm.injective (Subtype.ext h)
  have hle := card_add_one_le_finrank_evenBoundStateSpace ρ hρ hinj
  rwa [card_quarterFinset hfin] at hle

/-- **Exact Dimension of `boundStateSpace`**:
when `offLineZeros` is finite, `finrank ℝ boundStateSpace = 2 * #(quarterZeros) + 1`. -/
theorem finrank_boundStateSpace_eq (hfin : offLineZeros.Finite) :
    Module.finrank ℝ boundStateSpace = 2 * quarterZeros.ncard + 1 := by
  rw [finrank_boundStateSpace_eq_add_parity hfin, finrank_evenBoundStateSpace_eq hfin,
    finrank_oddBoundStateSpace_eq hfin]
  omega

/-- **Exact Parity Balance Law**:
when `offLineZeros` is finite, `finrank ℝ evenBoundStateSpace = finrank ℝ oddBoundStateSpace + 1`. -/
theorem finrank_evenBoundStateSpace_eq_finrank_oddBoundStateSpace_add_one
    (hfin : offLineZeros.Finite) :
    Module.finrank ℝ evenBoundStateSpace = Module.finrank ℝ oddBoundStateSpace + 1 := by
  rw [finrank_evenBoundStateSpace_eq hfin, finrank_oddBoundStateSpace_eq hfin]

/-- **Unconditional Parity Bound-State Subspace Equivalence**:
`oddBoundStateSpace = ⊥` if and only if `evenBoundStateSpace = ℝ ∙ oneL`
(and both are equivalent to `RiemannHypothesis`). -/
theorem oddBoundStateSpace_eq_bot_iff_evenBoundStateSpace_eq_span_oneL :
    oddBoundStateSpace = ⊥ ↔ evenBoundStateSpace = Submodule.span ℝ {oneL} := by
  rw [← riemannHypothesis_iff_oddBoundStateSpace_eq_bot,
    ← riemannHypothesis_iff_evenBoundStateSpace_eq_span_oneL]

end RHTower.CHMDPolar
