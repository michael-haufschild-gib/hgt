import GaloisForLFunctions.RHTower.WallBlockAssemblyTools

/-!
# The forced profile on either frequency ray

Past the threshold the profile is the propagated datum plus the moving tail, and the moving tail is
the four block averages of the two-fold expansion.  Collecting the five estimates gives, on each ray,

`‖u‖²_{L²(ray)} ≤ C(‖c‖² + X²‖g‖²₂)`,

one power of the threshold squared and nothing more.  The two rays differ only in which region and
which signed base point the same estimates are instantiated at.

Where each power of the threshold comes from: the propagated datum contributes `X²` through
`(1+X)^{2p}X^{1−2σ} ≤ 4^pX²`; the threshold vector contributes `X` through the same identity with one
power of `X` to spare; the two boundary terms and the remainder contribute none at all.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- Squaring an estimate on the square root. -/
theorem le_rpow_two_of_rpow_half_le {a b : ℝ≥0∞} (h : a ^ ((1 : ℝ) / 2) ≤ b) :
    a ≤ b ^ (2 : ℝ) := by
  calc a = (a ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) := by
        rw [← ENNReal.rpow_mul]
        norm_num
    _ ≤ b ^ (2 : ℝ) := ENNReal.rpow_le_rpow h (by norm_num)

/-- The composition constant of the ray estimate, as a single real. -/
theorem ofReal_ray_combination {a b₁ b₂ b₃ b₄ : ℝ} (ha : 0 ≤ a) (h₁ : 0 ≤ b₁) (h₂ : 0 ≤ b₂)
    (h₃ : 0 ≤ b₃) (h₄ : 0 ≤ b₄) :
    (4 : ℝ≥0∞) * (ENNReal.ofReal a + 16 * (ENNReal.ofReal b₁ + ENNReal.ofReal b₂
        + ENNReal.ofReal b₃ + ENNReal.ofReal b₄))
      = ENNReal.ofReal (4 * (a + 16 * (b₁ + b₂ + b₃ + b₄))) := by
  have e1 : ENNReal.ofReal b₁ + ENNReal.ofReal b₂ + ENNReal.ofReal b₃ + ENNReal.ofReal b₄
      = ENNReal.ofReal (b₁ + b₂ + b₃ + b₄) := by
    rw [← ENNReal.ofReal_add h₁ h₂, ← ENNReal.ofReal_add (by linarith) h₃,
      ← ENNReal.ofReal_add (by linarith) h₄]
  rw [e1, show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by simp,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
    ← ENNReal.ofReal_add ha (by positivity),
    show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

set_option maxHeartbeats 1000000 in
/-- **The forced profile on the outward ray.** -/
theorem exists_bound_lintegral_sq_forcedProfile_ray
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0) (hT : IsSelfAdjoint T)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y : ℝ), 1 < Y → ∀ (g : ℝ → X) (c : X) (m : ℝ),
      MemLp g 2 (volume : Measure ℝ) → StronglyMeasurable g →
      (∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) →
      (∀ t : ℝ, Y ≤ |t| → ∀ L ∈ Icc m (m + 1), 1 ≤ wallFloor T σ t + L) →
      (∫⁻ x in Ioi Y, ‖forcedProfile E T (blockSource g m) c σ x‖ₑ ^ 2)
        ≤ ENNReal.ofReal (C * (‖c‖ ^ 2 + Y ^ 2 * ∫ L : ℝ, ‖g L‖ ^ 2)) := by
  obtain ⟨Cd, hCd, hdatum⟩ := lintegral_sq_ray_thresholdDatum_le (T := T) hT hE hσ0 hσ1
  obtain ⟨K₂, hK₂, hb₂⟩ := exists_bound_stripPropagatorInv_line (T := T) hT hE hσ0 hσ1
  obtain ⟨Cp, hCp, hprop⟩ := exists_bound_lintegral_sq_ray_stripPropagator (T := T) hT hE hσ0 hσ1
  obtain ⟨Cr, hCr, hrem⟩ :=
    exists_bound_lintegral_sq_tailRemainder (T := T) (E := E) hT hE hσ0 hσ1 one_pos
  set p : ℝ := 1 / 2 + σ with hpdef
  set C₃ : ℝ := Cp * (K₂ * (4 + Real.pi)) ^ 2 * 4 ^ p with hC₃def
  have hC₃ : 0 ≤ C₃ := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    rw [hC₃def]
    positivity
  refine ⟨4 * (Cd + 16 * ((2 * Real.pi) + (3 + Real.pi) ^ 2 + C₃ + Cr)), by positivity, ?_⟩
  intro Y hY1 g c m hg2 hgm hsupp hfloor
  have hY : (1 : ℝ) ≤ Y := hY1.le
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le zero_lt_one hY
  have hYabs : |Y| = Y := abs_of_pos hY0
  have hg1 : Integrable g := integrable_zeroExtension hg2 hsupp
  have hgI : IntegrableOn g (Icc m (m + 1)) := hg1.integrableOn
  have hsqint : Integrable (fun L : ℝ => ‖g L‖ ^ 2) (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq_norm hg2.aestronglyMeasurable).mp hg2
  set N : ℝ := ∫ L : ℝ, ‖g L‖ ^ 2 with hNdef
  have hN0 : 0 ≤ N := integral_nonneg fun _ => by positivity
  set N₁ : ℝ := ∫ L in Icc m (m + 1), ‖g L‖ with hN₁def
  have hN₁0 : 0 ≤ N₁ := integral_nonneg fun _ => norm_nonneg _
  have hN₁sq : N₁ ^ 2 ≤ N := sq_integral_norm_block_le hg2 hsupp
  set S : ℝ := ‖c‖ ^ 2 + Y ^ 2 * N with hSdef
  have hS0 : 0 ≤ S := by positivity
  have hYsq : (1 : ℝ) ≤ Y ^ 2 := by nlinarith
  have hNY : N ≤ Y ^ 2 * N := by nlinarith
  have hNS : N ≤ S := by
    rw [hSdef]
    nlinarith [sq_nonneg ‖c‖]
  -- floors
  have hmmem : m ∈ Icc m (m + 1) := ⟨le_rfl, by linarith⟩
  have hfl : ∀ x ∈ Ioi Y, ∀ L ∈ Icc m (m + 1), 1 ≤ wallFloor T σ x + L := by
    intro x hx L hL
    have hx0 : (0 : ℝ) < x := lt_trans hY0 hx
    exact hfloor x (by rw [abs_of_pos hx0]; exact (mem_Ioi.mp hx).le) L hL
  have hflY : ∀ L ∈ Icc m (m + 1), 1 ≤ wallFloor T σ Y + L :=
    fun L hL => hfloor Y (by rw [hYabs]) L hL
  -- the five estimates
  have hA₁ : (∫⁻ x in Ioi Y, ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
      (thresholdDatum E T (blockSource g m) c σ Y)‖ₑ ^ 2) ≤ ENNReal.ofReal (Cd * S) :=
    hdatum Y hY g c m hg2 hsupp
  have hB₁ : (∫⁻ x in Ioi Y, ‖firstBoundary T g σ x‖ₑ ^ 2)
      ≤ ENNReal.ofReal ((2 * Real.pi) * S) := by
    have hfb : ∀ x ∈ Ioi Y, (1 : ℝ) - m ≤ wallFloor T σ x := by
      intro x hx
      have := hfl x hx m hmmem
      linarith
    have h := lintegral_sq_firstBoundary_le (T := T) (μ₀ := 1) (m := m) measurableSet_Ioi
      hσ0 hσ1 one_pos hg2 hgm hsupp hfb
    rw [lintegral_sq_indicator_eq measurableSet_Ioi, div_one] at h
    have hEnn : (0 : ℝ) ≤ (2 * Real.pi) * N := by positivity
    refine (le_rpow_two_of_rpow_half_le h).trans ?_
    have hval : (ENNReal.ofReal (Real.sqrt ((2 * Real.pi) * N))) ^ (2 : ℝ)
        = ENNReal.ofReal ((2 * Real.pi) * N) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num), Real.rpow_two,
        Real.sq_sqrt hEnn]
    rw [hval]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_pos])
  have hB₂ : (∫⁻ x in Ioi Y, ‖secondBoundary T g m σ x‖ₑ ^ 2)
      ≤ ENNReal.ofReal ((3 + Real.pi) ^ 2 * S) := by
    have h := lintegral_sq_secondBoundary_le (T := T) hσ0 hσ1 one_pos hY hgI hfl
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hcoef : ((1 : ℝ)⁻¹) ^ 3 * (3 + Real.pi) = 3 + Real.pi := by norm_num
    rw [hcoef, ← hN₁def, mul_pow]
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    nlinarith [hN₁sq, hNS, sq_nonneg (3 + Real.pi)]
  have hB₃ : (∫⁻ x in Ioi Y, ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
      (thresholdVector E T g m σ Y)‖ₑ ^ 2) ≤ ENNReal.ofReal (C₃ * S) := by
    have hTV : ‖thresholdVector E T g m σ Y‖
        ≤ (K₂ * (1 + |Y|) ^ p) * (4 + Real.pi) * N₁ :=
      norm_thresholdVector_le (E := E) hσ0 hσ1 hb₂ hK₂.le hgI (by rw [hYabs]; exact hY) hflY
    have hTV0 : 0 ≤ ‖thresholdVector E T g m σ Y‖ := norm_nonneg _
    refine (hprop Y hY0 _).trans (ENNReal.ofReal_le_ofReal ?_)
    have hbnd : ‖thresholdVector E T g m σ Y‖ ^ 2
        ≤ ((K₂ * (4 + Real.pi)) ^ 2 * N₁ ^ 2) * ((1 + Y) ^ p) ^ 2 := by
      rw [hYabs] at hTV
      have := pow_le_pow_left₀ hTV0 hTV 2
      calc ‖thresholdVector E T g m σ Y‖ ^ 2
          ≤ ((K₂ * (1 + Y) ^ p) * (4 + Real.pi) * N₁) ^ 2 := this
        _ = ((K₂ * (4 + Real.pi)) ^ 2 * N₁ ^ 2) * ((1 + Y) ^ p) ^ 2 := by ring
    have hexp3 : ((1 + Y) ^ p) ^ 2 * Y ^ (-(2 * σ)) ≤ 4 ^ p * Y ^ 2 := by
      have h1 : ((1 + Y) ^ p) ^ 2 = (1 + Y) ^ (2 * p) := by
        rw [← Real.rpow_natCast ((1 + Y) ^ p) 2, ← Real.rpow_mul (by linarith)]
        ring_nf
      have h2 : Y ^ (-(2 * σ)) ≤ Y ^ (1 - 2 * σ) :=
        Real.rpow_le_rpow_of_exponent_le hY (by linarith)
      rw [h1]
      calc (1 + Y) ^ (2 * p) * Y ^ (-(2 * σ))
          ≤ (1 + Y) ^ (2 * p) * Y ^ (1 - 2 * σ) :=
            mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (by linarith) _)
        _ ≤ 4 ^ p * Y ^ 2 := thresholdExponent_le hσ0 hY
    have hpow0 : 0 < Y ^ (-(2 * σ)) := Real.rpow_pos_of_pos hY0 _
    have hcoef0 : 0 ≤ (K₂ * (4 + Real.pi)) ^ 2 * N₁ ^ 2 := by positivity
    calc Cp * ‖thresholdVector E T g m σ Y‖ ^ 2 * Y ^ (-(2 * σ))
        ≤ Cp * (((K₂ * (4 + Real.pi)) ^ 2 * N₁ ^ 2) * ((1 + Y) ^ p) ^ 2) * Y ^ (-(2 * σ)) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbnd hCp) hpow0.le
      _ = ((K₂ * (4 + Real.pi)) ^ 2 * N₁ ^ 2) * (Cp * (((1 + Y) ^ p) ^ 2 * Y ^ (-(2 * σ)))) := by
          ring
      _ ≤ ((K₂ * (4 + Real.pi)) ^ 2 * N₁ ^ 2) * (Cp * (4 ^ p * Y ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hcoef0
          exact mul_le_mul_of_nonneg_left hexp3 hCp
      _ = C₃ * (N₁ ^ 2 * Y ^ 2) := by rw [hC₃def]; ring
      _ ≤ C₃ * S := by
          refine mul_le_mul_of_nonneg_left ?_ hC₃
          have hY2 : (0 : ℝ) ≤ Y ^ 2 := sq_nonneg Y
          nlinarith [hN₁sq, sq_nonneg ‖c‖]
  have hB₄ : (∫⁻ x in Ioi Y, ‖tailRemainder E T g m σ Y x‖ₑ ^ 2) ≤ ENNReal.ofReal (Cr * S) := by
    have hNe : (∫⁻ L in Icc m (m + 1), ‖g L‖ₑ) ^ 2 ≤ ENNReal.ofReal N := by
      refine (sq_lintegral_enorm_block_le hgI.aestronglyMeasurable.enorm).trans ?_
      refine (setLIntegral_le_lintegral _ _).trans (le_of_eq ?_)
      rw [hNdef]
      exact lintegral_enorm_sq_eq_ofReal_integral hsqint
    refine (hrem m Y hY g hgI hfl).trans ?_
    refine le_trans (mul_le_mul' le_rfl hNe) ?_
    rw [← ENNReal.ofReal_mul hCr]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hNS hCr)
  -- composition
  have hsplit := lintegral_sq_forcedProfile_ray_le (T := T) hEdiff hE hEne hσ0 hσ1 hgI c (Y := Y)
  have hmov := lintegral_sq_movingTail_le (T := T) hEdiff hE hEne hT hσ0 hσ1 hgI hsupp hY
    one_pos hflY
  refine hsplit.trans ?_
  refine le_trans (mul_le_mul' le_rfl (add_le_add hA₁ (hmov.trans
    (mul_le_mul' le_rfl (add_le_add (add_le_add (add_le_add hB₁ hB₂) hB₃) hB₄))))) ?_
  rw [ofReal_ray_combination (a := Cd * S) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

set_option maxHeartbeats 1000000 in
/-- **The forced profile on the inward ray.** -/
theorem exists_bound_lintegral_sq_forcedProfile_negRay
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0) (hT : IsSelfAdjoint T)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y : ℝ), 1 < Y → ∀ (g : ℝ → X) (c : X) (m : ℝ),
      MemLp g 2 (volume : Measure ℝ) → StronglyMeasurable g →
      (∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) →
      (∀ t : ℝ, Y ≤ |t| → ∀ L ∈ Icc m (m + 1), 1 ≤ wallFloor T σ t + L) →
      (∫⁻ x in Iio (-Y), ‖forcedProfile E T (blockSource g m) c σ x‖ₑ ^ 2)
        ≤ ENNReal.ofReal (C * (‖c‖ ^ 2 + Y ^ 2 * ∫ L : ℝ, ‖g L‖ ^ 2)) := by
  obtain ⟨Cd, hCd, hdatum⟩ := lintegral_sq_negRay_thresholdDatum_le (T := T) hT hE hσ0 hσ1
  obtain ⟨K₂, hK₂, hb₂⟩ := exists_bound_stripPropagatorInv_line (T := T) hT hE hσ0 hσ1
  obtain ⟨Cp, hCp, hprop⟩ :=
    exists_bound_lintegral_sq_negRay_stripPropagator (T := T) hT hE hσ0 hσ1
  obtain ⟨Cr, hCr, hrem⟩ :=
    exists_bound_lintegral_sq_negRay_tailRemainder (T := T) (E := E) hT hE hσ0 hσ1 one_pos
  set p : ℝ := 1 / 2 + σ with hpdef
  set C₃ : ℝ := Cp * (K₂ * (4 + Real.pi)) ^ 2 * 4 ^ p with hC₃def
  have hC₃ : 0 ≤ C₃ := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    rw [hC₃def]
    positivity
  refine ⟨4 * (Cd + 16 * ((2 * Real.pi) + (3 + Real.pi) ^ 2 + C₃ + Cr)), by positivity, ?_⟩
  intro Y hY1 g c m hg2 hgm hsupp hfloor
  have hY : (1 : ℝ) ≤ Y := hY1.le
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le zero_lt_one hY
  have hYabs : |(-Y)| = Y := by rw [abs_neg, abs_of_pos hY0]
  have hg1 : Integrable g := integrable_zeroExtension hg2 hsupp
  have hgI : IntegrableOn g (Icc m (m + 1)) := hg1.integrableOn
  have hsqint : Integrable (fun L : ℝ => ‖g L‖ ^ 2) (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq_norm hg2.aestronglyMeasurable).mp hg2
  set N : ℝ := ∫ L : ℝ, ‖g L‖ ^ 2 with hNdef
  have hN0 : 0 ≤ N := integral_nonneg fun _ => by positivity
  set N₁ : ℝ := ∫ L in Icc m (m + 1), ‖g L‖ with hN₁def
  have hN₁0 : 0 ≤ N₁ := integral_nonneg fun _ => norm_nonneg _
  have hN₁sq : N₁ ^ 2 ≤ N := sq_integral_norm_block_le hg2 hsupp
  set S : ℝ := ‖c‖ ^ 2 + Y ^ 2 * N with hSdef
  have hS0 : 0 ≤ S := by positivity
  have hYsq : (1 : ℝ) ≤ Y ^ 2 := by nlinarith
  have hNY : N ≤ Y ^ 2 * N := by nlinarith
  have hNS : N ≤ S := by
    rw [hSdef]
    nlinarith [sq_nonneg ‖c‖]
  -- floors
  have hmmem : m ∈ Icc m (m + 1) := ⟨le_rfl, by linarith⟩
  have habsx : ∀ x ∈ Iio (-Y), |x| = -x := fun x hx => abs_of_neg (by
    have := mem_Iio.mp hx; linarith)
  have hxA : ∀ x ∈ Iio (-Y), Y ≤ |x| := by
    intro x hx
    rw [habsx x hx]
    have := mem_Iio.mp hx
    linarith
  have hfl : ∀ x ∈ Iio (-Y), ∀ L ∈ Icc m (m + 1), 1 ≤ wallFloor T σ x + L :=
    fun x hx L hL => hfloor x (hxA x hx) L hL
  have hflY : ∀ L ∈ Icc m (m + 1), 1 ≤ wallFloor T σ (-Y) + L :=
    fun L hL => hfloor (-Y) (by rw [hYabs]) L hL
  -- the five estimates
  have hA₁ : (∫⁻ x in Iio (-Y), ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
      (thresholdDatum E T (blockSource g m) c σ (-Y))‖ₑ ^ 2) ≤ ENNReal.ofReal (Cd * S) :=
    hdatum Y hY g c m hg2 hsupp
  have hB₁ : (∫⁻ x in Iio (-Y), ‖firstBoundary T g σ x‖ₑ ^ 2)
      ≤ ENNReal.ofReal ((2 * Real.pi) * S) := by
    have hfb : ∀ x ∈ Iio (-Y), (1 : ℝ) - m ≤ wallFloor T σ x := by
      intro x hx
      have := hfl x hx m hmmem
      linarith
    have h := lintegral_sq_firstBoundary_le (T := T) (μ₀ := 1) (m := m) measurableSet_Iio
      hσ0 hσ1 one_pos hg2 hgm hsupp hfb
    rw [lintegral_sq_indicator_eq measurableSet_Iio, div_one] at h
    have hEnn : (0 : ℝ) ≤ (2 * Real.pi) * N := by positivity
    refine (le_rpow_two_of_rpow_half_le h).trans ?_
    have hval : (ENNReal.ofReal (Real.sqrt ((2 * Real.pi) * N))) ^ (2 : ℝ)
        = ENNReal.ofReal ((2 * Real.pi) * N) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num), Real.rpow_two,
        Real.sq_sqrt hEnn]
    rw [hval]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_pos])
  have hB₂ : (∫⁻ x in Iio (-Y), ‖secondBoundary T g m σ x‖ₑ ^ 2)
      ≤ ENNReal.ofReal ((3 + Real.pi) ^ 2 * S) := by
    have h := lintegral_sq_negRay_secondBoundary_le (T := T) hσ0 hσ1 one_pos hY hgI hfl
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hcoef : ((1 : ℝ)⁻¹) ^ 3 * (3 + Real.pi) = 3 + Real.pi := by norm_num
    rw [hcoef, ← hN₁def, mul_pow]
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    nlinarith [hN₁sq, hNS, sq_nonneg (3 + Real.pi)]
  have hB₃ : (∫⁻ x in Iio (-Y), ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
      (thresholdVector E T g m σ (-Y))‖ₑ ^ 2) ≤ ENNReal.ofReal (C₃ * S) := by
    have hTV : ‖thresholdVector E T g m σ (-Y)‖
        ≤ (K₂ * (1 + |(-Y)|) ^ p) * (4 + Real.pi) * N₁ :=
      norm_thresholdVector_le (E := E) hσ0 hσ1 hb₂ hK₂.le hgI (by rw [hYabs]; exact hY) hflY
    have hTV0 : 0 ≤ ‖thresholdVector E T g m σ (-Y)‖ := norm_nonneg _
    refine (hprop Y hY0 _).trans (ENNReal.ofReal_le_ofReal ?_)
    have hbnd : ‖thresholdVector E T g m σ (-Y)‖ ^ 2
        ≤ ((K₂ * (4 + Real.pi)) ^ 2 * N₁ ^ 2) * ((1 + Y) ^ p) ^ 2 := by
      rw [hYabs] at hTV
      have := pow_le_pow_left₀ hTV0 hTV 2
      calc ‖thresholdVector E T g m σ (-Y)‖ ^ 2
          ≤ ((K₂ * (1 + Y) ^ p) * (4 + Real.pi) * N₁) ^ 2 := this
        _ = ((K₂ * (4 + Real.pi)) ^ 2 * N₁ ^ 2) * ((1 + Y) ^ p) ^ 2 := by ring
    have hexp3 : ((1 + Y) ^ p) ^ 2 * Y ^ (-(2 * σ)) ≤ 4 ^ p * Y ^ 2 := by
      have h1 : ((1 + Y) ^ p) ^ 2 = (1 + Y) ^ (2 * p) := by
        rw [← Real.rpow_natCast ((1 + Y) ^ p) 2, ← Real.rpow_mul (by linarith)]
        ring_nf
      have h2 : Y ^ (-(2 * σ)) ≤ Y ^ (1 - 2 * σ) :=
        Real.rpow_le_rpow_of_exponent_le hY (by linarith)
      rw [h1]
      calc (1 + Y) ^ (2 * p) * Y ^ (-(2 * σ))
          ≤ (1 + Y) ^ (2 * p) * Y ^ (1 - 2 * σ) :=
            mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (by linarith) _)
        _ ≤ 4 ^ p * Y ^ 2 := thresholdExponent_le hσ0 hY
    have hpow0 : 0 < Y ^ (-(2 * σ)) := Real.rpow_pos_of_pos hY0 _
    have hcoef0 : 0 ≤ (K₂ * (4 + Real.pi)) ^ 2 * N₁ ^ 2 := by positivity
    calc Cp * ‖thresholdVector E T g m σ (-Y)‖ ^ 2 * Y ^ (-(2 * σ))
        ≤ Cp * (((K₂ * (4 + Real.pi)) ^ 2 * N₁ ^ 2) * ((1 + Y) ^ p) ^ 2) * Y ^ (-(2 * σ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbnd hCp) hpow0.le
      _ = ((K₂ * (4 + Real.pi)) ^ 2 * N₁ ^ 2) * (Cp * (((1 + Y) ^ p) ^ 2 * Y ^ (-(2 * σ)))) := by
          ring
      _ ≤ ((K₂ * (4 + Real.pi)) ^ 2 * N₁ ^ 2) * (Cp * (4 ^ p * Y ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hcoef0
          exact mul_le_mul_of_nonneg_left hexp3 hCp
      _ = C₃ * (N₁ ^ 2 * Y ^ 2) := by rw [hC₃def]; ring
      _ ≤ C₃ * S := by
          refine mul_le_mul_of_nonneg_left ?_ hC₃
          have hY2 : (0 : ℝ) ≤ Y ^ 2 := sq_nonneg Y
          nlinarith [hN₁sq, sq_nonneg ‖c‖]
  have hB₄ : (∫⁻ x in Iio (-Y), ‖tailRemainder E T g m σ (-Y) x‖ₑ ^ 2)
      ≤ ENNReal.ofReal (Cr * S) := by
    have hNe : (∫⁻ L in Icc m (m + 1), ‖g L‖ₑ) ^ 2 ≤ ENNReal.ofReal N := by
      refine (sq_lintegral_enorm_block_le hgI.aestronglyMeasurable.enorm).trans ?_
      refine (setLIntegral_le_lintegral _ _).trans (le_of_eq ?_)
      rw [hNdef]
      exact lintegral_enorm_sq_eq_ofReal_integral hsqint
    refine (hrem m Y hY1 g hgI hfloor).trans ?_
    refine le_trans (mul_le_mul' le_rfl hNe) ?_
    rw [← ENNReal.ofReal_mul hCr]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hNS hCr)
  -- composition
  have hsplit := lintegral_sq_forcedProfile_negRay_le (T := T) hEdiff hE hEne hσ0 hσ1 hgI c
    (Y := Y)
  have hmov := lintegral_sq_movingTail_region_le (T := T) hEdiff hE hEne hT hσ0 hσ1
    measurableSet_Iio hgI hsupp (by rw [hYabs]; exact hY) one_pos hflY
    (fun x hx => le_trans hY (hxA x hx))
    (fun x hx L hL => hfl x hx L hL)
    (fun x hx L hL t ht => by
      have hxle : x ≤ -Y := (mem_Iio.mp hx).le
      have htmem : t ∈ Icc x (-Y) := by rwa [uIcc_of_ge hxle] at ht
      have ht0 : t < 0 := lt_of_le_of_lt htmem.2 (by linarith)
      exact hfloor t (by rw [abs_of_neg ht0]; linarith [htmem.2]) L hL)
  refine hsplit.trans ?_
  refine le_trans (mul_le_mul' le_rfl (add_le_add hA₁ (hmov.trans
    (mul_le_mul' le_rfl (add_le_add (add_le_add (add_le_add hB₁ hB₂) hB₃) hB₄))))) ?_
  rw [ofReal_ray_combination (a := Cd * S) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

end GaloisForLFunctions.RHTower
