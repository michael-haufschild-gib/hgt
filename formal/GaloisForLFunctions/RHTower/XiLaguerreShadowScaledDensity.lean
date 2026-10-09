import GaloisForLFunctions.RHTower.XiLaguerreShadowDensity
import GaloisForLFunctions.RHTower.XiSliceCoeffDensity

/-!
# The `κ`-dilated shadow of the off-line zeros

For `κ ≥ 0` the dilated shadow `S_κ = {x : ∃ ζ, Ξ(ζ) = 0, (Re ζ − x)² < κ² (Im ζ)²}` is the
union of the intervals `(Re ζ − κ|Im ζ|, Re ζ + κ|Im ζ|)`; `κ = 1` is the shadow `S` of
`XiLaguerreShadowDensity`.  Off `S_κ` every zero copy satisfies the cone condition
`κ² (Re ρ − ½)² ≤ (Im ρ − t)²` (`cone_of_not_mem_xiShadowScaled`).  Each conjugate pair of off-line
zeros is counted once, the interval around `Im ρ` has radius `κ(Re ρ − ½) ≤ κ/2`, and

  `vol(S_κ ∩ [0, V]) ≤ 2κ Σ_{0 ≤ Im ρ ≤ V + κ/2} m(ρ)(Re ρ − ½)`
  (`volume_xiShadowScaled_inter_Icc_le_offLineMoment`).

An off-line moment bound `Σ m(ρ)(Re ρ − ½) ≤ μ V` gives `vol(S_κ ∩ [0, V]) ≤ 2κμV + κ²μ` for all
large `V` (`eventually_volume_xiShadowScaled_inter_Icc_le_of_moment`).
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower.DeBruijn

noncomputable section

/-- The `κ`-dilated shadow of the zeros of `Ξ`. -/
def xiShadowScaled (κ : ℝ) : Set ℝ :=
  {x | ∃ ζ : ℂ, riemannHeat 0 ζ = 0 ∧ (ζ.re - x) ^ 2 < κ ^ 2 * ζ.im ^ 2}

/-- **The cone condition off the dilated shadow.** -/
theorem cone_of_not_mem_xiShadowScaled {κ t : ℝ} (ht : t ∉ xiShadowScaled κ) (q : XiZeroCopy) :
    κ ^ 2 * ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ ((q.1 : ℂ).im - t) ^ 2 := by
  by_contra hlt
  rw [not_le] at hlt
  apply ht
  have hq : xi (q.1 : ℂ) = 0 := xi_eq_zero_of_mem_divisor_support q.1
  refine ⟨-I * ((q.1 : ℂ) - 1 / 2), ?_, ?_⟩
  · rw [riemannHeat_zero]
    convert hq using 1
    congr 1
    ring_nf
    rw [I_sq]
    ring
  · have hre : (-I * ((q.1 : ℂ) - 1 / 2)).re = (q.1 : ℂ).im := by simp
    have him : (-I * ((q.1 : ℂ) - 1 / 2)).im = 1 / 2 - (q.1 : ℂ).re := by simp
    rw [hre, him]
    nlinarith [hlt]

/-- Every point of the dilated shadow in `[0, V]` lies in the interval
`(Im ρ − κ(Re ρ − ½), Im ρ + κ(Re ρ − ½))` of a zero `ρ` of `ξ` with `½ < Re ρ < 1`,
`0 ≤ Im ρ ≤ V + κ/2`. -/
theorem exists_boxZero_of_mem_xiShadowScaled {κ V x : ℝ} (hκ : 0 ≤ κ)
    (hx : x ∈ xiShadowScaled κ ∩ Icc 0 V) :
    ∃ ρ ∈ boxFinsetLe (V + κ / 2),
      x ∈ Ioo (ρ.im - κ * (ρ.re - 1 / 2)) (ρ.im + κ * (ρ.re - 1 / 2)) := by
  obtain ⟨⟨ζ, hζ, hlt⟩, hx0, hxV⟩ := hx
  -- reflect to `Re ζ ≥ 0`
  obtain ⟨ζ₁, hζ₁, hlt₁, hre₁⟩ : ∃ ζ₁ : ℂ, riemannHeat 0 ζ₁ = 0 ∧
      (ζ₁.re - x) ^ 2 < κ ^ 2 * ζ₁.im ^ 2 ∧ 0 ≤ ζ₁.re := by
    by_cases h : 0 ≤ ζ.re
    · exact ⟨ζ, hζ, hlt, h⟩
    · rw [not_le] at h
      refine ⟨-(starRingEnd ℂ ζ), ?_, ?_, ?_⟩
      · rw [riemannHeat_neg le_rfl, riemannHeat_conj le_rfl, hζ, map_zero]
      · simp only [Complex.neg_re, Complex.conj_re, Complex.neg_im, Complex.conj_im, neg_neg]
        have : (-ζ.re - x) ^ 2 ≤ (ζ.re - x) ^ 2 := by nlinarith
        linarith
      · simp only [Complex.neg_re, Complex.conj_re]
        linarith
  -- conjugate to `Im ζ < 0`
  obtain ⟨ζ₂, hζ₂, hlt₂, hre₂, him₂⟩ : ∃ ζ₂ : ℂ, riemannHeat 0 ζ₂ = 0 ∧
      (ζ₂.re - x) ^ 2 < κ ^ 2 * ζ₂.im ^ 2 ∧ 0 ≤ ζ₂.re ∧ ζ₂.im < 0 := by
    have hne : ζ₁.im ≠ 0 := by
      intro h
      rw [h] at hlt₁
      nlinarith [sq_nonneg (ζ₁.re - x)]
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨ζ₁, hζ₁, hlt₁, hre₁, h⟩
    · refine ⟨starRingEnd ℂ ζ₁, ?_, ?_, ?_, ?_⟩
      · rw [riemannHeat_conj le_rfl, hζ₁, map_zero]
      · simpa using hlt₁
      · simpa using hre₁
      · simp only [Complex.conj_im]
        linarith
  have him2 : ζ₂.im ^ 2 ≤ 1 / 4 := by
    have h0 : cosTransform riemannKernelReal ζ₂ = 0 := by
      rw [cosTransform_riemannKernel, ← riemannHeat_zero]; exact hζ₂
    exact riemannKernel_zeros_im_sq_le ζ₂ h0
  have him2' : -(1 / 2) ≤ ζ₂.im := by nlinarith
  -- `|Re ζ − x| < κ (−Im ζ)`
  have hrad : 0 ≤ κ * -ζ₂.im := mul_nonneg hκ (by linarith)
  have hsq : (ζ₂.re - x) ^ 2 < (κ * -ζ₂.im) ^ 2 := by nlinarith
  have h' := abs_lt.mp (abs_lt_of_sq_lt_sq hsq hrad)
  have hρ : xi (1 / 2 + I * ζ₂) = 0 := by rw [← riemannHeat_zero]; exact hζ₂
  have hρre : (1 / 2 + I * ζ₂).re = 1 / 2 - ζ₂.im := by simp; ring
  have hρim : (1 / 2 + I * ζ₂).im = ζ₂.re := by simp
  have hκhalf : κ * -ζ₂.im ≤ κ / 2 := by nlinarith
  refine ⟨1 / 2 + I * ζ₂, ?_, ?_⟩
  · rw [mem_boxFinsetLe]
    refine ⟨by rw [hρre]; linarith, ?_, by rw [hρim]; exact hre₂, ?_, hρ⟩
    · by_contra hge
      exact xi_ne_zero_of_one_le_re (not_lt.mp hge) hρ
    · rw [hρim]
      linarith [h'.1, h'.2]
  · rw [hρre, hρim, show 1 / 2 - ζ₂.im - 1 / 2 = -ζ₂.im by ring]
    constructor <;> linarith [h'.1, h'.2]

/-- **The dilated shadow against the off-line first moment.**
`vol(S_κ ∩ [0, V]) ≤ 2κ Σ_{0 ≤ Im ρ ≤ V + κ/2} m(ρ)(Re ρ − ½)`. -/
theorem volume_xiShadowScaled_inter_Icc_le_offLineMoment {κ : ℝ} (hκ : 0 ≤ κ) (V : ℝ) :
    volume (xiShadowScaled κ ∩ Icc 0 V) ≤ ENNReal.ofReal (2 * κ * offLineMoment (V + κ / 2)) := by
  classical
  set B := boxFinsetLe (V + κ / 2)
  have hsub : xiShadowScaled κ ∩ Icc 0 V ⊆
      ⋃ ρ ∈ B, Ioo (ρ.im - κ * (ρ.re - 1 / 2)) (ρ.im + κ * (ρ.re - 1 / 2)) := by
    intro x hx
    obtain ⟨ρ, hρ, hxρ⟩ := exists_boxZero_of_mem_xiShadowScaled hκ hx
    exact mem_iUnion₂.mpr ⟨ρ, hρ, hxρ⟩
  have hB : ∀ ρ ∈ B, 1 / 2 < ρ.re ∧ xi ρ = 0 := by
    intro ρ hρ
    rw [mem_boxFinsetLe] at hρ
    exact ⟨hρ.1, hρ.2.2.2.2⟩
  calc volume (xiShadowScaled κ ∩ Icc 0 V)
      ≤ volume (⋃ ρ ∈ B, Ioo (ρ.im - κ * (ρ.re - 1 / 2)) (ρ.im + κ * (ρ.re - 1 / 2))) :=
        measure_mono hsub
    _ ≤ ∑ ρ ∈ B, volume (Ioo (ρ.im - κ * (ρ.re - 1 / 2)) (ρ.im + κ * (ρ.re - 1 / 2))) :=
        measure_biUnion_finset_le _ _
    _ = ∑ ρ ∈ B, ENNReal.ofReal (2 * κ * (ρ.re - 1 / 2)) := by
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [Real.volume_Ioo]
        congr 1
        ring
    _ = ENNReal.ofReal (∑ ρ ∈ B, 2 * κ * (ρ.re - 1 / 2)) :=
        (ENNReal.ofReal_sum_of_nonneg fun ρ hρ => by
          have := (hB ρ hρ).1
          have : 0 ≤ ρ.re - 1 / 2 := by linarith
          positivity).symm
    _ ≤ ENNReal.ofReal (2 * κ * offLineMoment (V + κ / 2)) := by
        apply ENNReal.ofReal_le_ofReal
        unfold offLineMoment
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun ρ hρ => ?_
        have h1 := one_le_toNat_analyticOrderAt_xi (hB ρ hρ).2
        have h1' : (1 : ℝ) ≤ ((analyticOrderAt xi ρ).toNat : ℝ) := by exact_mod_cast h1
        have hpos : 0 ≤ ρ.re - 1 / 2 := by linarith [(hB ρ hρ).1]
        have h2κ : 0 ≤ 2 * κ := by linarith
        have := mul_le_mul_of_nonneg_left
          (le_mul_of_one_le_left hpos h1' : ρ.re - 1 / 2 ≤ _) h2κ
        linarith

/-- From an off-line moment bound `Σ m(ρ)(Re ρ − ½) ≤ μ V`, for all large `V` the dilated shadow
occupies at most `2κμV + κ²μ` of `[0, V]`. -/
theorem eventually_volume_xiShadowScaled_inter_Icc_le_of_moment {κ μ : ℝ} (hκ : 0 ≤ κ)
    (hmom : ∀ᶠ V in atTop, offLineMoment V ≤ μ * V) :
    ∀ᶠ V in atTop, volume (xiShadowScaled κ ∩ Icc 0 V) ≤
      ENNReal.ofReal (2 * κ * μ * V + κ ^ 2 * μ) := by
  have h := (tendsto_atTop_add_const_right atTop (κ / 2 : ℝ) tendsto_id).eventually hmom
  filter_upwards [h] with V hV
  refine (volume_xiShadowScaled_inter_Icc_le_offLineMoment hκ V).trans
    (ENNReal.ofReal_le_ofReal ?_)
  simp only [id] at hV
  have h2κ : 0 ≤ 2 * κ := by linarith
  have := mul_le_mul_of_nonneg_left hV h2κ
  nlinarith

end

end RHTower.DeBruijn
