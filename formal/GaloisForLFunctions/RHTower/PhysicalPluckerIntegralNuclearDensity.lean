import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPhysicalPluckerOrdinaryDeterminant
import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPhysicalOverlapPluckerFaithfulness
import GaloisForLFunctions.HTGeometry.FramePurificationPartialTrace
import GaloisForLFunctions.HTGeometry.WeightedOrbitSelectionLaw
import GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearDefect
import GaloisForLFunctions.HTGeometry.GradedRowSynthesis
import GaloisForLFunctions.RHTower.ThetaSurvivalRelativeCurvaturePrimeLift

/-!
# The normalized physical-overlap Plücker density

The physical-overlap Plücker operator `A = ∑_{z,s} c_{z,s} |v_{z,s}⟩⟨v_{z,s}|` on
`H = ℓ²(ℕ_depth × ℕ_primeIndex)` has trace `τ`, the total source mass of its rank-one expansion.
Its normalization `T = A/τ` is the frame operator of the rays `α_{z,s} = √(c_{z,s}/τ) v_{z,s}`,
`∑ ‖α‖² = 1`:

* **Theorem POINH-A.**  `T` is positive, compact, Schatten-one and faithful, with
  `Tr T = ‖T‖₁ = 1` and `0 < ‖T‖ < 1`;
* **(POINH.7)** `Tr T² = ∑_{i,k} |⟨α_i, α_k⟩|²` and
  `1 - Tr T² = ∑_{i,k} (‖α_i‖² ‖α_k‖² - |⟨α_i, α_k⟩|²) > 0`;
* **(POINH.8)–(POINH.9)** the purification `Ψ = ∑ δ_i ⊗ α_i` is a unit vector whose partial
  trace over the source record is `T`;
* **(POINH.14)** the signed wall `T_t = sign(t) T`;
* **(§2)** prime mixing inside every packet: the cross-prime block of each local spectral block is
  nonzero, and some source ray has nonzero components on both adjacent primes.
-/

open Filter Topology
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry

/-- The ray index `(z, s)` of the physical source expansion. -/
abbrev PluckerRayIndex : Type := (ℕ × ℕ) × Fin 6

/-- The total source mass `τ = Tr A`. -/
abbrev pluckerTraceMass : ℝ := gammaSewnCriticalPhysicalPluckerNuclearTraceMass

theorem pluckerTraceMass_pos : 0 < pluckerTraceMass := by
  have h := gammaSewnCriticalPhysicalPluckerSourceTrace_pos
  rw [gammaSewnCriticalPhysicalPluckerSourceTrace_eq_nuclearTraceMass] at h
  exact_mod_cast h

/-- The ray weight `c_{z,s} = b_z π_z(s)`. -/
def pluckerRayWeight (i : PluckerRayIndex) : ℝ :=
  gammaSewnCriticalAdjacentPrime_PluckerBlockWeight i.1 *
    gammaSewnCriticalAdjacentPrime_PluckerProbability i.1 i.2

theorem pluckerRayWeight_pos (i : PluckerRayIndex) : 0 < pluckerRayWeight i :=
  mul_pos (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos i.1)
    (gammaSewnCriticalAdjacentPrime_PluckerProbability_pos i.1 i.2)

/-- **(POINH.5).**  The normalized ray `α_{z,s} = √(c_{z,s}/τ) v_{z,s}`. -/
def normalizedPluckerRay (i : PluckerRayIndex) : GammaSewnCriticalPhysicalPluckerHilbert :=
  ((Real.sqrt (pluckerRayWeight i / pluckerTraceMass) : ℝ) : ℂ) •
    gammaSewnCriticalPhysicalPluckerCenteredVector i.1 i.2

theorem norm_sq_normalizedPluckerRay (i : PluckerRayIndex) :
    ‖normalizedPluckerRay i‖ ^ 2 = pluckerRayWeight i *
      ‖gammaSewnCriticalPhysicalPluckerCenteredVector i.1 i.2‖ ^ 2 / pluckerTraceMass := by
  rw [normalizedPluckerRay, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt (div_nonneg (pluckerRayWeight_pos i).le pluckerTraceMass_pos.le)]
  ring

theorem hasSum_norm_sq_normalizedPluckerRay :
    HasSum (fun i => ‖normalizedPluckerRay i‖ ^ 2) 1 := by
  have hsum : Summable fun i : PluckerRayIndex => pluckerRayWeight i *
      ‖gammaSewnCriticalPhysicalPluckerCenteredVector i.1 i.2‖ ^ 2 :=
    summable_norm_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm.congr fun i =>
      norm_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm i
  have h := hsum.hasSum.div_const pluckerTraceMass
  simp_rw [← norm_sq_normalizedPluckerRay] at h
  have hτ : (∑' i : PluckerRayIndex, pluckerRayWeight i *
      ‖gammaSewnCriticalPhysicalPluckerCenteredVector i.1 i.2‖ ^ 2) = pluckerTraceMass := rfl
  rwa [hτ, div_self pluckerTraceMass_pos.ne'] at h

theorem summable_norm_sq_normalizedPluckerRay :
    Summable fun i => ‖normalizedPluckerRay i‖ ^ 2 :=
  hasSum_norm_sq_normalizedPluckerRay.summable

/-- **(POINH.4).**  The normalized density `T = A/τ`. -/
def normalizedPhysicalPluckerOperator :
    GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ] GammaSewnCriticalPhysicalPluckerHilbert :=
  ((pluckerTraceMass⁻¹ : ℝ) : ℂ) • gammaSewnCriticalPhysicalPluckerSpectralOperator

theorem rankOne_normalizedPluckerRay (i : PluckerRayIndex) :
    rankOne ℂ (normalizedPluckerRay i) (normalizedPluckerRay i) =
      ((pluckerTraceMass⁻¹ : ℝ) : ℂ) • gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm i := by
  have hc : 0 ≤ pluckerRayWeight i / pluckerTraceMass :=
    div_nonneg (pluckerRayWeight_pos i).le pluckerTraceMass_pos.le
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [normalizedPluckerRay, gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm,
    FunLike.coe_smul, Pi.smul_apply, rankOne_apply, inner_smul_left,
    Complex.conj_ofReal, smul_smul]
  congr 1
  have hs : ((Real.sqrt (pluckerRayWeight i / pluckerTraceMass) : ℝ) : ℂ) *
      ((Real.sqrt (pluckerRayWeight i / pluckerTraceMass) : ℝ) : ℂ) =
        ((pluckerTraceMass⁻¹ : ℝ) : ℂ) * ((gammaSewnCriticalAdjacentPrime_PluckerBlockWeight i.1 *
          gammaSewnCriticalAdjacentPrime_PluckerProbability i.1 i.2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc, ← Complex.ofReal_mul, pluckerRayWeight]
    congr 1
    ring
  linear_combination ⟪gammaSewnCriticalPhysicalPluckerCenteredVector i.1 i.2, x⟫_ℂ * hs

/-- `T` is the frame operator `∑ |α_i⟩⟨α_i|`. -/
theorem normalizedPhysicalPluckerOperator_eq_frameOperator :
    normalizedPhysicalPluckerOperator = frameOperator normalizedPluckerRay := by
  rw [frameOperator, normalizedPhysicalPluckerOperator, gammaSewnCriticalPhysicalPluckerSpectralOperator]
  simp_rw [rankOne_normalizedPluckerRay]
  rw [Summable.tsum_const_smul _ summable_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm]

/-- The synthesis `W e_i = α_i`. -/
def pluckerRaySynthesis :
    lp (fun _ : PluckerRayIndex => ℂ) 2 →L[ℂ] GammaSewnCriticalPhysicalPluckerHilbert :=
  squareSummableSynthesis normalizedPluckerRay summable_norm_sq_normalizedPluckerRay

theorem normalizedPhysicalPluckerOperator_eq_leftGram :
    normalizedPhysicalPluckerOperator =
      pluckerRaySynthesis ∘L adjoint pluckerRaySynthesis := by
  rw [normalizedPhysicalPluckerOperator_eq_frameOperator,
    frameOperator_eq_leftGram summable_norm_sq_normalizedPluckerRay]
  rfl

/-! ## Theorem POINH-A -/

theorem normalizedPhysicalPluckerOperator_isPositive :
    normalizedPhysicalPluckerOperator.IsPositive := by
  rw [normalizedPhysicalPluckerOperator_eq_leftGram]
  exact isPositive_self_comp_adjoint _

theorem normalizedPhysicalPluckerOperator_memSchattenClass_one :
    MemSchattenClass 1 normalizedPhysicalPluckerOperator := by
  rw [normalizedPhysicalPluckerOperator_eq_frameOperator]
  exact frameOperator_memSchattenClass_one summable_norm_sq_normalizedPluckerRay

theorem normalizedPhysicalPluckerOperator_isCompact :
    IsCompactOperator normalizedPhysicalPluckerOperator :=
  normalizedPhysicalPluckerOperator_memSchattenClass_one.isCompactOperator one_pos

theorem normalizedPhysicalPluckerOperator_injective :
    Function.Injective normalizedPhysicalPluckerOperator := by
  intro x y hxy
  apply gammaSewnCriticalPhysicalPluckerSpectralOperator_injective
  have hc : ((pluckerTraceMass⁻¹ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (inv_ne_zero pluckerTraceMass_pos.ne')
  exact smul_right_injective _ hc hxy

theorem opTrace_normalizedPhysicalPluckerOperator :
    opTrace normalizedPhysicalPluckerOperator = 1 := by
  rw [normalizedPhysicalPluckerOperator, opTrace_smul]
  change ((pluckerTraceMass⁻¹ : ℝ) : ℂ) * gammaSewnCriticalPhysicalPluckerSourceTrace = 1
  rw [gammaSewnCriticalPhysicalPluckerSourceTrace_eq_nuclearTraceMass, ← Complex.ofReal_mul,
    inv_mul_cancel₀ pluckerTraceMass_pos.ne', Complex.ofReal_one]

theorem traceNorm_normalizedPhysicalPluckerOperator :
    traceNorm GammaSewnCriticalPhysicalPluckerHilbert normalizedPhysicalPluckerOperator = 1 := by
  have h := traceNorm_eq_re_opTrace_of_isPositive
    normalizedPhysicalPluckerOperator_memSchattenClass_one
    normalizedPhysicalPluckerOperator_isPositive
  rw [h, opTrace_normalizedPhysicalPluckerOperator, Complex.one_re]

theorem not_finiteDimensional_pluckerHilbert :
    ¬ FiniteDimensional ℂ GammaSewnCriticalPhysicalPluckerHilbert :=
  not_finiteDimensional_lp (I := ℕ × ℕ) (H := ℂ)

/-! ## (POINH.7): the source-dispersion identity -/

/-- The Gram determinant `‖a‖²‖b‖² - |⟨a,b⟩|² = ‖a ∧ b‖²`. -/
def gramDeterminant (a b : GammaSewnCriticalPhysicalPluckerHilbert) : ℝ :=
  ‖a‖ ^ 2 * ‖b‖ ^ 2 - ‖⟪a, b⟫_ℂ‖ ^ 2

theorem gramDeterminant_nonneg (a b : GammaSewnCriticalPhysicalPluckerHilbert) :
    0 ≤ gramDeterminant a b := by
  rw [gramDeterminant, sub_nonneg, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm a b) 2

/-- The matrix entries of the right Gram `W*W` are `⟨α_i, α_k⟩`. -/
theorem rightGram_entry (i k : PluckerRayIndex) :
    ((adjoint pluckerRaySynthesis ∘L pluckerRaySynthesis) (lp.single 2 k 1) : _ → ℂ) i =
      ⟪normalizedPluckerRay i, normalizedPluckerRay k⟫_ℂ := by
  have h := inner_single_rightGram_single summable_norm_sq_normalizedPluckerRay i k
  rw [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] at h
  exact h

/-- **(POINH.7), first identity.**  `Tr T² = ∑_k ∑_i |⟨α_i, α_k⟩|²`. -/
theorem opTrace_normalizedPhysicalPluckerOperator_sq :
    opTrace (normalizedPhysicalPluckerOperator ∘L normalizedPhysicalPluckerOperator) =
      ((∑' k, ∑' i, ‖⟪normalizedPluckerRay i, normalizedPluckerRay k⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  set W := pluckerRaySynthesis
  have hW : IsHilbertSchmidt W := squareSummableSynthesis_isHilbertSchmidt _
  set G := adjoint W ∘L W
  have hG : IsHilbertSchmidt G := hW.comp_left (adjoint W)
  have hB : IsHilbertSchmidt (adjoint W ∘L (W ∘L adjoint W)) :=
    (hW.adjoint.comp_left W).comp_left (adjoint W)
  rw [normalizedPhysicalPluckerOperator_eq_leftGram]
  have hcyc : opTrace ((W ∘L adjoint W) ∘L (W ∘L adjoint W)) = opTrace (G ∘L G) := by
    rw [show (W ∘L adjoint W) ∘L (W ∘L adjoint W) = W ∘L (adjoint W ∘L (W ∘L adjoint W)) by
      simp only [comp_assoc], opTrace_comp_comm hW hB]
    simp only [G, comp_assoc]
  rw [hcyc]
  have hGsa : adjoint G = G := by simp [G, adjoint_comp]
  rw [show G ∘L G = adjoint G ∘L G by rw [hGsa], opTrace_adjoint_comp_self,
    hsInner_self_eq_ofReal_hsNormSq', hsNormSq_eq hG (HilbertSchmidt.lpBasis PluckerRayIndex)]
  congr 1
  refine tsum_congr fun k => ?_
  rw [HilbertSchmidt.lpBasis_apply]
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (G (lp.single 2 k 1))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [h]
  exact tsum_congr fun i => by rw [rightGram_entry]


/-- The real number `Tr T² = ∑_k ∑_i |⟨α_i, α_k⟩|²`. -/
def pluckerPurity : ℝ :=
  ∑' k, ∑' i, ‖⟪normalizedPluckerRay i, normalizedPluckerRay k⟫_ℂ‖ ^ 2

theorem norm_inner_sq_le (i k : PluckerRayIndex) :
    ‖⟪normalizedPluckerRay i, normalizedPluckerRay k⟫_ℂ‖ ^ 2 ≤
      ‖normalizedPluckerRay i‖ ^ 2 * ‖normalizedPluckerRay k‖ ^ 2 := by
  have h := gramDeterminant_nonneg (normalizedPluckerRay i) (normalizedPluckerRay k)
  rw [gramDeterminant] at h
  linarith

theorem summable_inner_sq (k : PluckerRayIndex) :
    Summable fun i => ‖⟪normalizedPluckerRay i, normalizedPluckerRay k⟫_ℂ‖ ^ 2 :=
  (summable_norm_sq_normalizedPluckerRay.mul_right (‖normalizedPluckerRay k‖ ^ 2)).of_nonneg_of_le
    (fun _ => sq_nonneg _) fun i => norm_inner_sq_le i k

theorem tsum_inner_sq_le (k : PluckerRayIndex) :
    ∑' i, ‖⟪normalizedPluckerRay i, normalizedPluckerRay k⟫_ℂ‖ ^ 2 ≤ ‖normalizedPluckerRay k‖ ^ 2 := by
  calc ∑' i, ‖⟪normalizedPluckerRay i, normalizedPluckerRay k⟫_ℂ‖ ^ 2
      ≤ ∑' i, ‖normalizedPluckerRay i‖ ^ 2 * ‖normalizedPluckerRay k‖ ^ 2 :=
        (summable_inner_sq k).tsum_le_tsum (fun i => norm_inner_sq_le i k)
          (summable_norm_sq_normalizedPluckerRay.mul_right _)
    _ = ‖normalizedPluckerRay k‖ ^ 2 := by
        rw [tsum_mul_right, hasSum_norm_sq_normalizedPluckerRay.tsum_eq, one_mul]

theorem summable_tsum_inner_sq :
    Summable fun k => ∑' i, ‖⟪normalizedPluckerRay i, normalizedPluckerRay k⟫_ℂ‖ ^ 2 :=
  summable_norm_sq_normalizedPluckerRay.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => sq_nonneg _)
    tsum_inner_sq_le

theorem tsum_gramDeterminant_eq (k : PluckerRayIndex) :
    ∑' i, gramDeterminant (normalizedPluckerRay i) (normalizedPluckerRay k) =
      ‖normalizedPluckerRay k‖ ^ 2 -
        ∑' i, ‖⟪normalizedPluckerRay i, normalizedPluckerRay k⟫_ℂ‖ ^ 2 := by
  simp only [gramDeterminant]
  rw [(summable_norm_sq_normalizedPluckerRay.mul_right _).tsum_sub (summable_inner_sq k),
    tsum_mul_right, hasSum_norm_sq_normalizedPluckerRay.tsum_eq, one_mul]

/-- **(POINH.7).**  `1 - Tr T² = ∑_k ∑_i ‖α_i ∧ α_k‖²`. -/
theorem one_sub_pluckerPurity :
    1 - pluckerPurity = ∑' k, ∑' i,
      gramDeterminant (normalizedPluckerRay i) (normalizedPluckerRay k) := by
  simp_rw [tsum_gramDeterminant_eq]
  rw [summable_norm_sq_normalizedPluckerRay.tsum_sub summable_tsum_inner_sq,
    hasSum_norm_sq_normalizedPluckerRay.tsum_eq, pluckerPurity]

/-- Some two source rays are not collinear: otherwise `T` would have rank at most one, which an
injective operator on the infinite-dimensional carrier cannot. -/
theorem exists_gramDeterminant_pos :
    ∃ i k, 0 < gramDeterminant (normalizedPluckerRay i) (normalizedPluckerRay k) := by
  by_contra hall
  push Not at hall
  have hzero : ∀ i k, gramDeterminant (normalizedPluckerRay i) (normalizedPluckerRay k) = 0 :=
    fun i k => le_antisymm (hall i k) (gramDeterminant_nonneg _ _)
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, normalizedPluckerRay i₀ ≠ 0 := by
    by_contra h
    push Not at h
    have := hasSum_norm_sq_normalizedPluckerRay.tsum_eq
    simp [h] at this
  set u := normalizedPluckerRay i₀
  have hcol : ∀ i, ∃ c : ℂ, normalizedPluckerRay i = c • u := fun i => by
    by_cases hi : normalizedPluckerRay i = 0
    · exact ⟨0, by rw [hi, zero_smul]⟩
    have h := hzero i₀ i
    rw [gramDeterminant, sub_eq_zero, ← mul_pow] at h
    have h' : ‖⟪u, normalizedPluckerRay i⟫_ℂ‖ = ‖u‖ * ‖normalizedPluckerRay i‖ :=
      ((sq_eq_sq₀ (by positivity) (norm_nonneg _)).1 h).symm
    obtain ⟨r, -, hr⟩ := (norm_inner_eq_norm_iff hi₀ hi).1 h'
    exact ⟨r, hr⟩
  set L : Submodule ℂ GammaSewnCriticalPhysicalPluckerHilbert := ℂ ∙ u
  haveI : FiniteDimensional ℂ L := FiniteDimensional.span_singleton ℂ u
  have hrange : ∀ x, normalizedPhysicalPluckerOperator x ∈ L := fun x => by
    rw [← Submodule.orthogonal_orthogonal L]
    refine (Submodule.mem_orthogonal _ _).2 fun y hy => ?_
    have hyu : ⟪y, u⟫_ℂ = 0 := (Submodule.mem_orthogonal_singleton_iff_inner_left).1 hy
    rw [normalizedPhysicalPluckerOperator_eq_frameOperator,
      frameOperator_apply summable_norm_sq_normalizedPluckerRay]
    have hsum : Summable fun i => ⟪normalizedPluckerRay i, x⟫_ℂ • normalizedPluckerRay i :=
      (Summable.of_norm (summable_norm_rankOne_frame summable_norm_sq_normalizedPluckerRay)).mapL
        (ContinuousLinearMap.apply ℂ _ x)
    have hmap : ⟪y, ∑' i, ⟪normalizedPluckerRay i, x⟫_ℂ • normalizedPluckerRay i⟫_ℂ =
        ∑' i, ⟪y, ⟪normalizedPluckerRay i, x⟫_ℂ • normalizedPluckerRay i⟫_ℂ :=
      (innerSL ℂ y).map_tsum hsum
    rw [hmap]
    refine (tsum_congr fun i => ?_).trans tsum_zero
    obtain ⟨c, hc⟩ := hcol i
    rw [inner_smul_right, hc, inner_smul_right, hyu, mul_zero, mul_zero]
  apply not_finiteDimensional_pluckerHilbert
  exact Module.Finite.of_injective
    ((normalizedPhysicalPluckerOperator : _ →ₗ[ℂ] _).codRestrict L hrange)
    (fun x y hxy => normalizedPhysicalPluckerOperator_injective (by
      simpa using congrArg Subtype.val hxy))

/-- **(POINH.7), strictness.**  `Tr T² < 1`. -/
theorem pluckerPurity_lt_one : pluckerPurity < 1 := by
  obtain ⟨i, k, hik⟩ := exists_gramDeterminant_pos
  have hsumk : ∀ k, Summable fun i =>
      gramDeterminant (normalizedPluckerRay i) (normalizedPluckerRay k) := fun k =>
    (summable_norm_sq_normalizedPluckerRay.mul_right _).sub (summable_inner_sq k)
  have hpos_inner : ∀ k, 0 ≤ ∑' i, gramDeterminant (normalizedPluckerRay i) (normalizedPluckerRay k) :=
    fun k => tsum_nonneg fun i => gramDeterminant_nonneg _ _
  have hk : 0 < ∑' i, gramDeterminant (normalizedPluckerRay i) (normalizedPluckerRay k) :=
    (hsumk k).tsum_pos (fun i => gramDeterminant_nonneg _ _) i hik
  have houter : Summable fun k =>
      ∑' i, gramDeterminant (normalizedPluckerRay i) (normalizedPluckerRay k) := by
    refine summable_norm_sq_normalizedPluckerRay.of_nonneg_of_le hpos_inner fun k => ?_
    rw [tsum_gramDeterminant_eq]
    exact sub_le_self _ (tsum_nonneg fun _ => sq_nonneg _)
  have := houter.tsum_pos hpos_inner k hk
  rw [← one_sub_pluckerPurity] at this
  linarith

theorem pluckerPurity_nonneg : 0 ≤ pluckerPurity :=
  tsum_nonneg fun _ => tsum_nonneg fun _ => sq_nonneg _

/-- **Theorem POINH-A, norm.**  `0 < ‖T‖ < 1`, since `‖T‖² = ‖T²‖ ≤ Tr T² < 1`. -/
theorem norm_normalizedPhysicalPluckerOperator_lt_one :
    0 < ‖normalizedPhysicalPluckerOperator‖ ∧ ‖normalizedPhysicalPluckerOperator‖ < 1 := by
  have hT0 : normalizedPhysicalPluckerOperator ≠ 0 := fun h => by
    have := opTrace_normalizedPhysicalPluckerOperator
    rw [h] at this
    simp [ContinuousLinearMap.opTrace] at this
  refine ⟨norm_pos_iff.2 hT0, ?_⟩
  have hsa : adjoint normalizedPhysicalPluckerOperator = normalizedPhysicalPluckerOperator :=
    normalizedPhysicalPluckerOperator_isPositive.isSelfAdjoint.adjoint_eq
  have hsq : ‖normalizedPhysicalPluckerOperator‖ * ‖normalizedPhysicalPluckerOperator‖ =
      ‖normalizedPhysicalPluckerOperator ∘L normalizedPhysicalPluckerOperator‖ := by
    rw [← ContinuousLinearMap.norm_adjoint_comp_self normalizedPhysicalPluckerOperator, hsa]
  have hW : IsHilbertSchmidt pluckerRaySynthesis := squareSummableSynthesis_isHilbertSchmidt _
  have hmem : MemSchattenClass 1
      (normalizedPhysicalPluckerOperator ∘L normalizedPhysicalPluckerOperator) := by
    rw [normalizedPhysicalPluckerOperator_eq_leftGram, comp_assoc]
    exact memSchattenClass_one_comp hW
      ((hW.adjoint.comp_left pluckerRaySynthesis).comp_left (adjoint pluckerRaySynthesis) |>
        fun h => by simpa only [comp_assoc] using h)
  have hpos : (normalizedPhysicalPluckerOperator ∘L normalizedPhysicalPluckerOperator).IsPositive := by
    rw [show normalizedPhysicalPluckerOperator ∘L normalizedPhysicalPluckerOperator =
      adjoint normalizedPhysicalPluckerOperator ∘L normalizedPhysicalPluckerOperator by rw [hsa]]
    exact isPositive_adjoint_comp_self _
  have htr := traceNorm_eq_re_opTrace_of_isPositive hmem hpos
  rw [opTrace_normalizedPhysicalPluckerOperator_sq, Complex.ofReal_re] at htr
  have hle := norm_le_traceNorm_of_memSchattenClass_one hmem
  rw [htr] at hle
  have hlt : ‖normalizedPhysicalPluckerOperator‖ * ‖normalizedPhysicalPluckerOperator‖ < 1 := by
    rw [hsq]
    exact hle.trans_lt pluckerPurity_lt_one
  nlinarith [norm_nonneg normalizedPhysicalPluckerOperator]

/-! ## (POINH.8)–(POINH.9): purification -/

/-- The canonical source purification `Ψ = ∑ δ_i ⊗ α_i`. -/
def pluckerPurification : lp (fun _ : PluckerRayIndex => GammaSewnCriticalPhysicalPluckerHilbert) 2 :=
  framePurification normalizedPluckerRay summable_norm_sq_normalizedPluckerRay

theorem norm_pluckerPurification : ‖pluckerPurification‖ = 1 := by
  have h : ‖pluckerPurification‖ ^ 2 = 1 := by
    rw [pluckerPurification, norm_sq_framePurification summable_norm_sq_normalizedPluckerRay,
      hasSum_norm_sq_normalizedPluckerRay.tsum_eq]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

/-- **(POINH.9).**  Closing the source record of `|Ψ⟩⟨Ψ|` gives `T`. -/
theorem pluckerPurification_isPartialTrace :
    IsPartialTrace (rankOne ℂ pluckerPurification pluckerPurification)
      normalizedPhysicalPluckerOperator := by
  rw [normalizedPhysicalPluckerOperator_eq_frameOperator]
  exact frameOperator_isPartialTrace summable_norm_sq_normalizedPluckerRay

/-! ## (POINH.14): the signed wall -/

/-- `T_t = sign(t) T`. -/
def signedPhysicalPluckerWall (t : ℝ) :
    GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ] GammaSewnCriticalPhysicalPluckerHilbert :=
  (Real.sign t : ℂ) • normalizedPhysicalPluckerOperator

theorem signedPhysicalPluckerWall_neg (t : ℝ) :
    signedPhysicalPluckerWall (-t) = -signedPhysicalPluckerWall t := by
  rw [signedPhysicalPluckerWall, signedPhysicalPluckerWall, Real.sign_neg, Complex.ofReal_neg,
    neg_smul]

theorem opTrace_signedPhysicalPluckerWall (t : ℝ) :
    opTrace (signedPhysicalPluckerWall t) = Real.sign t := by
  rw [signedPhysicalPluckerWall, opTrace_smul, opTrace_normalizedPhysicalPluckerOperator, mul_one]

theorem traceNorm_signedPhysicalPluckerWall (t : ℝ) :
    traceNorm GammaSewnCriticalPhysicalPluckerHilbert (signedPhysicalPluckerWall t) =
      |Real.sign t| := by
  rw [signedPhysicalPluckerWall, traceNorm_smul, traceNorm_normalizedPhysicalPluckerOperator,
    mul_one, Complex.norm_real, Real.norm_eq_abs]

/-! ## §2: prime mixing inside every packet -/

/-- **§2.**  The cross-prime `2 × 2` block of every local spectral block is nonzero. -/
theorem exists_crossPrime_spectralBlock_ne_zero (z : ℕ × ℕ) :
    ∃ i j : Fin 4, (i : ℕ) < 2 ∧ 2 ≤ (j : ℕ) ∧
      gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z i j ≠ 0 := by
  by_contra hall
  push Not at hall
  set M := gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z
  have hsymm : ∀ i j, M i j = M j i := fun i j => by
    simp only [M, gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_eq_centered]
    exact Finset.sum_congr rfl fun s _ => by ring
  set k := gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector z
  set kp : Fin 4 → ℝ := ![k 0, k 1, 0, 0]
  have hk0 : M.mulVec k = 0 := by
    rw [gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_mulVec_eq_zero_iff_smul_kernel]
    exact ⟨1, by rw [one_smul]⟩
  have ek : ∀ a, (M.mulVec k) a = M a 0 * k 0 + M a 1 * k 1 + M a 2 * k 2 + M a 3 * k 3 := by
    intro a
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  have ekp : ∀ a, (M.mulVec kp) a = M a 0 * k 0 + M a 1 * k 1 := by
    intro a
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, kp]
  have hkp : M.mulVec kp = 0 := by
    funext a
    rw [ekp, Pi.zero_apply]
    by_cases ha : (a : ℕ) < 2
    · have h := congrFun hk0 a
      rw [ek, Pi.zero_apply, hall a 2 ha (by decide), hall a 3 ha (by decide)] at h
      linarith
    · rw [hsymm a 0, hsymm a 1, hall 0 a (by decide) (by omega), hall 1 a (by decide) (by omega)]
      ring
  obtain ⟨c, hc⟩ :=
    (gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_mulVec_eq_zero_iff_smul_kernel z kp).1 hkp
  have h2 := congrFun hc 2
  have h0 := congrFun hc 0
  simp only [kp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Matrix.cons_val_zero,
    Pi.smul_apply, smul_eq_mul] at h2 h0
  have hc0 : c = 0 := (mul_eq_zero.1 h2.symm).resolve_right
    (gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector_apply_ne_zero z 2)
  rw [hc0, zero_mul] at h0
  exact gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector_apply_ne_zero z 0 h0

/-- **§2, ray form.**  In every packet some source ray has nonzero components on both adjacent
primes. -/
theorem exists_crossPrime_ray (z : ℕ × ℕ) :
    ∃ s : Fin 6, ∃ i j : Fin 4, (i : ℕ) < 2 ∧ 2 ≤ (j : ℕ) ∧
      gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s i ≠ 0 ∧
        gammaSewnCriticalAdjacentPrime_PluckerCenteredNodeFeature z s j ≠ 0 := by
  obtain ⟨i, j, hi, hj, hne⟩ := exists_crossPrime_spectralBlock_ne_zero z
  rw [gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_eq_centered] at hne
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  refine ⟨s, i, j, hi, hj, fun h => hs ?_, fun h => hs ?_⟩ <;> simp [h]

end RHTower.HedenmalmThetaSource
