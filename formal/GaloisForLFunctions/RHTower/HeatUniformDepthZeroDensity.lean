import GaloisForLFunctions.RHTower.HeatZeroDisplacement
import GaloisForLFunctions.RHTower.DeBruijnNonrealCountAntitone
import GaloisForLFunctions.RHTower.XiLocalZeroDensity

/-!
# Heat counting uniformly over shrinking depths

The depth, height, and heat time may vary together. Absolute constants
count every dyadic family of Xi zero copies of depth at least `d` by
`log X` times the nonreal heat count whenever `t log X ≤ c d²`.
Multiplicity is retained through the local Xi count on each fibre.
-/

open Complex Metric Filter Set
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

/-- The inverse-logarithmic heat-count comparison has constants and a height
threshold independent of the positive depth. -/
theorem exists_card_deep_le_heat_count_at_uniform_depth_scale :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ X₀ : ℝ, 4096 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → ∀ d : ℝ, 0 < d → d ≤ 1 / 2 →
        ∀ t : ℝ, 0 < t → t * Real.log X ≤ c * d ^ 2 →
          ∀ F : Finset XiZeroCopy,
            (∀ q ∈ F, X ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ 2 * X ∧
              d ≤ |(q.1 : ℂ).re - 1 / 2|) →
            (F.card : ℝ) ≤ C * Real.log X * nonrealZeroCount t := by
  classical
  obtain ⟨c, hc, X₁, hX₁, hpersist⟩ :=
    exists_nonreal_riemannHeat_zero_at_uniform_depth_scale
  obtain ⟨C, hC, hloc⟩ := exists_card_near_xi_zeros_le
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hloc
  refine ⟨c / 2, 2 * C, by positivity, by positivity, ?_⟩
  refine ⟨max (max X₁ (T₀ + 1)) (4096 + Real.exp 20), ?_, ?_⟩
  · have h := le_max_right (max X₁ (T₀ + 1)) (4096 + Real.exp 20)
    linarith only [h, Real.exp_pos 20]
  intro X hX₀ d hd hd2 t ht htX F hF
  have hX1 : X₁ ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans hX₀)
  have hXT : T₀ + 1 ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans hX₀)
  have hXE : 4096 + Real.exp 20 ≤ X := (le_max_right _ _).trans hX₀
  have hX : 4096 ≤ X := by linarith only [hXE, Real.exp_pos 20]
  have hL : 20 ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 20) (show Real.exp 20 ≤ X by linarith only [hXE])
    simpa only [Real.log_exp] using h
  have hlogHeight {y : ℝ} (hy : 0 < y) (hyX : y ≤ X ^ 2) :
      Real.log y ≤ 2 * Real.log X := by
    have h := Real.log_le_log hy hyX
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hnear : ∀ q ∈ F, ∃ w : ℂ, riemannHeat t w = 0 ∧ w.im ≠ 0 ∧
      |w.re - (q.1 : ℂ).im| ≤ 1 := by
    intro q hq
    obtain ⟨hqX, hq2X, hqδ⟩ := hF q hq
    have hρ : xi (q.1 : ℂ) = 0 := xi_eq_zero_of_mem_divisor_support q.1
    have hre1 : (q.1 : ℂ).re < 1 := by
      by_contra h
      exact xi_ne_zero_of_one_le_re (not_lt.mp h) hρ
    have hre0 : 0 < (q.1 : ℂ).re := by
      by_contra h
      have h1 : xi (1 - (q.1 : ℂ)) = 0 := by rw [xi_one_sub, hρ]
      exact xi_ne_zero_of_one_le_re
        (by simp only [Complex.sub_re, Complex.one_re]; linarith only [not_lt.mp h]) h1
    let z : ℂ := ((q.1 : ℂ) - 1 / 2) * (-I)
    have hzre : z.re = (q.1 : ℂ).im := by dsimp [z]; simp
    have hzim : z.im = -((q.1 : ℂ).re - 1 / 2) := by dsimp [z]; simp
    have hdepth : |z.im| ≤ 1 / 2 := by
      rw [hzim, abs_neg]
      exact abs_le.mpr ⟨by linarith only [hre0], by linarith only [hre1]⟩
    have hz0 : riemannHeat 0 z = 0 := by
      have hpoint : (1 / 2 : ℂ) + I * z = (q.1 : ℂ) := by
        dsimp [z]
        ring_nf
        rw [I_sq]
        ring
      rw [riemannHeat_zero, hpoint, hρ]
    have hlog : Real.log (q.1 : ℂ).im ≤ 2 * Real.log X :=
      hlogHeight (by linarith only [hqX, hX])
        (by nlinarith only [hq2X, hX])
    have htq : t * Real.log (q.1 : ℂ).im ≤ c * d ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hlog ht.le
      nlinarith only [h, htX]
    obtain ⟨w, hw, hwim, hdist⟩ := hpersist (q.1 : ℂ).im (hX1.trans hqX)
      d hd hd2 t ht htq z hzre (by simpa only [hzim, abs_neg] using hqδ) hdepth hz0
    refine ⟨w, hw, hwim, ?_⟩
    have h := Complex.abs_re_le_norm (w - z)
    rw [Complex.sub_re, hzre] at h
    linarith only [h, hdist, hd2]
  choose! W hW using hnear
  let S : Finset ℂ := F.image W
  have hS : ∀ w ∈ S, riemannHeat t w = 0 ∧ w.im ≠ 0 := by
    intro w hw
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨(hW q hq).1, (hW q hq).2.1⟩
  have hScard : (S.card : ℝ) ≤ nonrealZeroCount t := by
    have h : S.card ≤ nonrealZeroCount t := by
      rw [nonrealZeroCount_eq ht, Finset.card_eq_sum_ones]
      calc
        _ ≤ ∑ w ∈ S, zeroMult (riemannHeat t) w :=
          Finset.sum_le_sum fun w hw => one_le_zeroMult_riemannHeat ht.le (hS w hw).1
        _ ≤ _ := Finset.sum_le_sum_of_subset fun w hw => by
          rw [Set.Finite.mem_toFinset]
          exact hS w hw
    exact_mod_cast h
  have hclose : ∀ q ∈ F, |(q.1 : ℂ).im - (W q).re| ≤ 1 := by
    intro q hq
    simpa only [abs_sub_comm] using (hW q hq).2.2
  have hfib : ∀ w ∈ S, ((F.filter fun q => W q = w).card : ℝ) ≤ 2 * C * Real.log X := by
    intro w hw
    obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hq0X, hq02X, _⟩ := hF q₀ hq₀
    have hc0 := abs_le.mp (hclose q₀ hq₀)
    have hwre1 : X - 1 ≤ (W q₀).re := by linarith only [hc0.2, hq0X]
    have hwre2 : (W q₀).re ≤ 2 * X + 1 := by linarith only [hc0.1, hq02X]
    have hcount := hT₀ (W q₀).re (by linarith only [hXT, hwre1])
      (F.filter fun q => W q = W q₀) fun q hq => by
        obtain ⟨hqF, hqw⟩ := Finset.mem_filter.mp hq
        rw [← hqw]
        exact hclose q hqF
    have hlog : Real.log (W q₀).re ≤ 2 * Real.log X :=
      hlogHeight (by linarith only [hwre1, hX])
        (by nlinarith only [hwre2, hX])
    calc
      _ ≤ C * Real.log (W q₀).re := hcount
      _ ≤ C * (2 * Real.log X) := mul_le_mul_of_nonneg_left hlog hC.le
      _ = _ := by ring
  have hFcard : (F.card : ℝ) ≤ 2 * C * Real.log X * S.card := by
    have h := Finset.card_eq_sum_card_image W F
    have heq : (F.card : ℝ) = ∑ w ∈ S, ((F.filter fun q => W q = w).card : ℝ) := by
      exact_mod_cast h
    rw [heq]
    calc
      _ ≤ ∑ _w ∈ S, 2 * C * Real.log X := Finset.sum_le_sum hfib
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hL0 : 0 ≤ Real.log X := by linarith only [hL]
  have hCL : 0 ≤ 2 * C * Real.log X := by positivity
  exact hFcard.trans (mul_le_mul_of_nonneg_left hScard hCL)

end

end RHTower.DeBruijn
