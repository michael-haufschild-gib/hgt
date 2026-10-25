import GaloisForLFunctions.BezoutValuationIncidence.TheActualEndpointVaughanGramHasRankTwo

/-!
The endpoint harmonic mass parametrizes every finite moving Vaughan Gram limit.
Adding this nonnegative smooth outer product to the actual rank-two Gram gives
rank three at positive mass and rank two at zero mass.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- The scalar harmonic mass carrying the interaction of the endpoint horizon and cutoffs. -/
def pmPronicVaughanHalfHarmonicMass (U V T : ℕ) : ℝ :=
  (subHalfZetaCoeff (1 / 2) * deningerHarmonicPartial U * deningerHarmonicPartial V) ^ 2 *
    (∑ n ∈ Icc 1 T, 1 / ((n : ℝ) + 1))

/-- The candidate endpoint limit matrix for a prescribed finite harmonic mass. -/
def pmPronicVaughanHalfLimitRay (ℓ : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  pmPronicVaughanHalfLimitGram +
    Matrix.vecMulVec (fun i => ℓ * pmPronicVaughanSmoothSigns i) pmPronicVaughanSmoothSigns

/-- Every actual endpoint harmonic mass is nonnegative. -/
theorem pmPronicVaughanHalfHarmonicMass_nonneg (U V T : ℕ) :
    0 ≤ pmPronicVaughanHalfHarmonicMass U V T := by
  unfold pmPronicVaughanHalfHarmonicMass
  positivity

/-- The fourth limiting source row vanishes, so its limiting Gram row is zero. -/
theorem pmPronicVaughanHalfLimitGram_large (j : Fin 5) :
    pmPronicVaughanHalfLimitGram 3 j = 0 := by
  simp [pmPronicVaughanHalfLimitGram, pmPronicVaughanLimitGram, pmPronicVaughanLimitFrame]

/-- The fourth diagonal of the limit ray reads its scalar parameter exactly. -/
theorem pmPronicVaughanHalfLimitRay_large_diag (ℓ : ℝ) :
    pmPronicVaughanHalfLimitRay ℓ 3 3 = ℓ := by
  simp [pmPronicVaughanHalfLimitRay, Matrix.vecMulVec_apply,
    pmPronicVaughanHalfLimitGram_large, pmPronicVaughanSmoothSigns]

/-- A finite harmonic-mass limit gives the corresponding actual endpoint Gram limit. -/
theorem tendsto_pmPronicVaughanCentredGram_half_of_harmonic_mass
    {H U V : ℕ → ℕ} (hH : Tendsto H atTop atTop)
    (hU : Tendsto U atTop atTop) (hV : Tendsto V atTop atTop) {ℓ : ℝ}
    (hℓ : Tendsto (fun t => pmPronicVaughanHalfHarmonicMass (U t) (V t) (H t))
      atTop (𝓝 ℓ)) (i j : Fin 5) :
    Tendsto (fun t => pmPronicVaughanCentredGram (1 / 2) (U t) (V t) (H t) i j)
      atTop (𝓝 (pmPronicVaughanHalfLimitRay ℓ i j)) := by
  have hr : Tendsto (fun t => pmPronicVaughanCentredGram (1 / 2) (U t) (V t) (H t) i j -
      pmPronicVaughanHalfHarmonicMass (U t) (V t) (H t) *
        pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j)
      atTop (𝓝 (pmPronicVaughanHalfLimitGram i j)) := by
    convert tendsto_pmPronicVaughanCentredGram_half_sub_harmonic hH hU hV i j using 1
    funext t
    dsimp only [pmPronicVaughanHalfHarmonicMass]
    ring
  change Tendsto _ atTop (𝓝 (pmPronicVaughanHalfLimitGram i j +
    ℓ * pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j))
  simpa only [sub_add_cancel] using hr.add
    ((hℓ.mul_const (pmPronicVaughanSmoothSigns i)).mul_const (pmPronicVaughanSmoothSigns j))

/-- The fourth centered diagonal differs from its harmonic mass by a term tending to zero. -/
theorem tendsto_pmPronicVaughanCentredGram_half_large_sub_harmonicMass
    {H U V : ℕ → ℕ} (hH : Tendsto H atTop atTop)
    (hU : Tendsto U atTop atTop) (hV : Tendsto V atTop atTop) :
    Tendsto (fun t => pmPronicVaughanCentredGram (1 / 2) (U t) (V t) (H t) 3 3 -
      pmPronicVaughanHalfHarmonicMass (U t) (V t) (H t)) atTop (𝓝 0) := by
  simpa only [pmPronicVaughanSmoothSigns, Matrix.cons_val_succ, Matrix.cons_val_zero,
    mul_one, pmPronicVaughanHalfLimitGram_large, pmPronicVaughanHalfHarmonicMass] using
    tendsto_pmPronicVaughanCentredGram_half_sub_harmonic hH hU hV 3 3

/-- The fourth diagonal tends to positive infinity exactly when the harmonic mass does. -/
theorem tendsto_pmPronicVaughanCentredGram_half_large_atTop_iff
    {H U V : ℕ → ℕ} (hH : Tendsto H atTop atTop)
    (hU : Tendsto U atTop atTop) (hV : Tendsto V atTop atTop) :
    Tendsto (fun t => pmPronicVaughanCentredGram (1 / 2) (U t) (V t) (H t) 3 3) atTop atTop ↔
      Tendsto (fun t => pmPronicVaughanHalfHarmonicMass (U t) (V t) (H t)) atTop atTop := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
    (tendsto_pmPronicVaughanCentredGram_half_large_sub_harmonicMass hH hU hV) 1 zero_lt_one
  have herr : ∀ᶠ t : ℕ in atTop,
      |pmPronicVaughanCentredGram (1 / 2) (U t) (V t) (H t) 3 3 -
        pmPronicVaughanHalfHarmonicMass (U t) (V t) (H t)| < 1 := by
    filter_upwards [eventually_ge_atTop N] with t ht
    simpa only [Real.dist_eq, sub_zero] using hN t ht
  constructor
  · intro hG
    apply tendsto_atTop.2
    intro B
    filter_upwards [hG.eventually_ge_atTop (B + 1), herr] with t hGt ht
    have h := (abs_lt.mp ht).2
    linarith only [h, hGt]
  · intro hm
    apply tendsto_atTop.2
    intro B
    filter_upwards [hm.eventually_ge_atTop (B + 1), herr] with t hmt ht
    have h := (abs_lt.mp ht).1
    linarith only [h, hmt]

/-- Any finite moving endpoint Gram limit forces convergence of its nonnegative harmonic mass. -/
theorem pmPronicVaughanCentredGram_half_limit_forces_harmonic_mass
    {H U V : ℕ → ℕ} (hH : Tendsto H atTop atTop)
    (hU : Tendsto U atTop atTop) (hV : Tendsto V atTop atTop)
    {L : Matrix (Fin 5) (Fin 5) ℝ}
    (hL : ∀ i j, Tendsto (fun t =>
      pmPronicVaughanCentredGram (1 / 2) (U t) (V t) (H t) i j) atTop (𝓝 (L i j))) :
    0 ≤ L 3 3 ∧
      Tendsto (fun t => pmPronicVaughanHalfHarmonicMass (U t) (V t) (H t)) atTop (𝓝 (L 3 3)) ∧
        L = pmPronicVaughanHalfLimitRay (L 3 3) := by
  have hr := tendsto_pmPronicVaughanCentredGram_half_large_sub_harmonicMass hH hU hV
  have hm : Tendsto (fun t => pmPronicVaughanHalfHarmonicMass (U t) (V t) (H t))
      atTop (𝓝 (L 3 3)) := by
    simpa only [sub_sub_cancel, sub_zero] using (hL 3 3).sub hr
  refine ⟨ge_of_tendsto hm (Eventually.of_forall fun t =>
    pmPronicVaughanHalfHarmonicMass_nonneg _ _ _), hm, ?_⟩
  funext i j
  exact tendsto_nhds_unique (hL i j)
    (tendsto_pmPronicVaughanCentredGram_half_of_harmonic_mass hH hU hV hm i j)

/-- Finite endpoint matrix limits are exactly the limits of their scalar harmonic mass. -/
theorem tendsto_pmPronicVaughanCentredGram_half_iff_harmonic_mass
    {H U V : ℕ → ℕ} (hH : Tendsto H atTop atTop)
    (hU : Tendsto U atTop atTop) (hV : Tendsto V atTop atTop)
    (L : Matrix (Fin 5) (Fin 5) ℝ) :
    (∀ i j, Tendsto (fun t => pmPronicVaughanCentredGram (1 / 2) (U t) (V t) (H t) i j)
      atTop (𝓝 (L i j))) ↔
      ∃ ℓ : ℝ, 0 ≤ ℓ ∧
        Tendsto (fun t => pmPronicVaughanHalfHarmonicMass (U t) (V t) (H t)) atTop (𝓝 ℓ) ∧
          L = pmPronicVaughanHalfLimitRay ℓ := by
  constructor
  · intro hL
    exact ⟨L 3 3, pmPronicVaughanCentredGram_half_limit_forces_harmonic_mass hH hU hV hL⟩
  · rintro ⟨ℓ, _hℓ0, hℓ, rfl⟩ i j
    exact tendsto_pmPronicVaughanCentredGram_half_of_harmonic_mass hH hU hV hℓ i j

/-- Zero harmonic mass leaves the rank-two infinite Gram. -/
theorem pmPronicVaughanHalfLimitRay_zero :
    pmPronicVaughanHalfLimitRay 0 = pmPronicVaughanHalfLimitGram := by
  ext i j
  simp only [pmPronicVaughanHalfLimitRay, Matrix.add_apply, Matrix.vecMulVec_apply,
    zero_mul, add_zero]

/-- A positive harmonic mass supplies exactly one new direction to the rank-two endpoint Gram. -/
theorem rank_pmPronicVaughanHalfLimitRay_of_pos {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Matrix.rank (pmPronicVaughanHalfLimitRay ℓ) = 3 := by
  have hupper : Matrix.rank (pmPronicVaughanHalfLimitRay ℓ) ≤ 3 := by
    have h := HTGeometry.rank_add_le_rank_add_rank pmPronicVaughanHalfLimitGram
      (Matrix.vecMulVec (fun i => ℓ * pmPronicVaughanSmoothSigns i) pmPronicVaughanSmoothSigns)
    rw [rank_pmPronicVaughanHalfLimitGram] at h
    exact h.trans (by
      have h₁ := Matrix.rank_vecMulVec_le
        (fun i => ℓ * pmPronicVaughanSmoothSigns i) pmPronicVaughanSmoothSigns
      omega)
  let e : Fin 3 → Fin 5 := ![0, 4, 3]
  have hdet : (Matrix.submatrix (pmPronicVaughanHalfLimitRay ℓ) e e).det =
      ℓ * (pmPronicVaughanHalfLimitGram 0 0 * pmPronicVaughanHalfLimitGram 4 4 -
        pmPronicVaughanHalfLimitGram 0 4 ^ 2) := by
    rw [Matrix.det_fin_three]
    change pmPronicVaughanHalfLimitRay ℓ 0 0 * pmPronicVaughanHalfLimitRay ℓ 4 4 *
        pmPronicVaughanHalfLimitRay ℓ 3 3 -
      pmPronicVaughanHalfLimitRay ℓ 0 0 * pmPronicVaughanHalfLimitRay ℓ 4 3 *
        pmPronicVaughanHalfLimitRay ℓ 3 4 -
      pmPronicVaughanHalfLimitRay ℓ 0 4 * pmPronicVaughanHalfLimitRay ℓ 4 0 *
        pmPronicVaughanHalfLimitRay ℓ 3 3 +
      pmPronicVaughanHalfLimitRay ℓ 0 4 * pmPronicVaughanHalfLimitRay ℓ 4 3 *
        pmPronicVaughanHalfLimitRay ℓ 3 0 +
      pmPronicVaughanHalfLimitRay ℓ 0 3 * pmPronicVaughanHalfLimitRay ℓ 4 0 *
        pmPronicVaughanHalfLimitRay ℓ 3 4 -
      pmPronicVaughanHalfLimitRay ℓ 0 3 * pmPronicVaughanHalfLimitRay ℓ 4 4 *
        pmPronicVaughanHalfLimitRay ℓ 3 0 = _
    simp only [pmPronicVaughanHalfLimitRay, Matrix.add_apply, Matrix.vecMulVec_apply,
      pmPronicVaughanSmoothSigns, mul_zero, zero_mul, mul_one, add_zero,
      pmPronicVaughanHalfLimitGram_large,
      pmPronicVaughanHalfLimitGram_symm 0 3, pmPronicVaughanHalfLimitGram_symm 4 3,
      pmPronicVaughanHalfLimitGram_symm 4 0]
    ring
  have hdet0 : 0 < (Matrix.submatrix (pmPronicVaughanHalfLimitRay ℓ) e e).det := by
    rw [hdet]
    exact mul_pos hℓ ((by norm_num : (0 : ℝ) < 1 / 62208).trans_le
      pmPronicVaughanHalfLimitGram_prefix_pole_minor_lower)
  have hu : IsUnit (Matrix.submatrix (pmPronicVaughanHalfLimitRay ℓ) e e) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet0.ne')
  have hr := Matrix.rank_of_isUnit _ hu
  have hle := Matrix.rank_submatrix_le (pmPronicVaughanHalfLimitRay ℓ) e e
  simp only [Fintype.card_fin] at hr
  omega

/-- The nonnegative endpoint limit ray has rank two at its origin and rank three everywhere else. -/
theorem rank_pmPronicVaughanHalfLimitRay {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    Matrix.rank (pmPronicVaughanHalfLimitRay ℓ) = if ℓ = 0 then 2 else 3 := by
  by_cases hz : ℓ = 0
  · subst ℓ
    rw [if_pos rfl, pmPronicVaughanHalfLimitRay_zero, rank_pmPronicVaughanHalfLimitGram]
  · rw [if_neg hz]
    exact rank_pmPronicVaughanHalfLimitRay_of_pos (lt_of_le_of_ne hℓ (Ne.symm hz))

#print axioms pmPronicVaughanHalfHarmonicMass_nonneg
#print axioms pmPronicVaughanHalfLimitGram_large
#print axioms pmPronicVaughanHalfLimitRay_large_diag
#print axioms tendsto_pmPronicVaughanCentredGram_half_large_sub_harmonicMass
#print axioms tendsto_pmPronicVaughanCentredGram_half_large_atTop_iff
#print axioms tendsto_pmPronicVaughanCentredGram_half_of_harmonic_mass
#print axioms pmPronicVaughanCentredGram_half_limit_forces_harmonic_mass
#print axioms tendsto_pmPronicVaughanCentredGram_half_iff_harmonic_mass
#print axioms pmPronicVaughanHalfLimitRay_zero
#print axioms rank_pmPronicVaughanHalfLimitRay_of_pos
#print axioms rank_pmPronicVaughanHalfLimitRay
end GaloisForLFunctions.BezoutValuationIncidence
