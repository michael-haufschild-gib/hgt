import GaloisForLFunctions.BiScaleUncertainty.PairedCollarCapacity

/-!
# Exact support of a capped block disk

A block split into low and high coordinates retains its whole Euclidean ball.
Only its low-coordinate radius is capped. The support is continuous in both
weights and the cap, is attained, and has a closed formula without division by
vanishing weight norms.
-/

set_option autoImplicit false
open Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

/-- A fixed compact parameter interval represents every nonnegative low radius
below the cap. The high radius uses the remaining unit-sphere budget. -/
def cappedBlockSupport (L H t : ℝ) : ℝ :=
  sSup ((fun s : ℝ => L * (t * s) + H * Real.sqrt (1 - (t * s) ^ 2)) '' Icc 0 1)

theorem continuous_cappedBlockSupport :
    Continuous (fun p : ℝ × ℝ × ℝ => cappedBlockSupport p.1 p.2.1 p.2.2) := by
  apply isCompact_Icc.continuous_sSup
  fun_prop

theorem cappedBlockSupport_attained (L H t : ℝ) :
    ∃ s ∈ Icc (0 : ℝ) 1,
      cappedBlockSupport L H t = L * (t * s) + H * Real.sqrt (1 - (t * s) ^ 2) ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
        L * (t * q) + H * Real.sqrt (1 - (t * q) ^ 2) ≤ cappedBlockSupport L H t := by
  obtain ⟨s, hs, he, hmax⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_sSup_image_eq_and_ge ⟨0, by simp⟩
    (by fun_prop : Continuous (fun s : ℝ =>
      L * (t * s) + H * Real.sqrt (1 - (t * s) ^ 2))).continuousOn
  exact ⟨s, hs, he, fun q hq => (hmax q hq).trans_eq he.symm⟩

theorem cappedBlockSupport_upper (L H t B : ℝ)
    (h : ∀ s ∈ Icc (0 : ℝ) 1,
      L * (t * s) + H * Real.sqrt (1 - (t * s) ^ 2) ≤ B) :
    cappedBlockSupport L H t ≤ B := by
  obtain ⟨s, hs, he, _⟩ := cappedBlockSupport_attained L H t
  rw [he]
  exact h s hs

theorem cappedBlockSupport_lower (L H t s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    L * (t * s) + H * Real.sqrt (1 - (t * s) ^ 2) ≤ cappedBlockSupport L H t := by
  obtain ⟨_, _, _, h⟩ := cappedBlockSupport_attained L H t
  exact h s hs

/-- Exact upper support for a point of the capped disk. -/
theorem cappedBlockSupport_bound {L H t x z : ℝ} (hH : 0 ≤ H)
    (ht : t ∈ Icc (0 : ℝ) 1) (hx : 0 ≤ x) (hxt : x ≤ t)
    (hdisk : x ^ 2 + z ^ 2 ≤ 1) :
    L * x + H * z ≤ cappedBlockSupport L H t := by
  have hz : z ≤ Real.sqrt (1 - x ^ 2) := Real.le_sqrt_of_sq_le (by linarith)
  have hrad := mul_le_mul_of_nonneg_left hz hH
  by_cases ht0 : t = 0
  · have hx0 : x = 0 := by linarith
    have h := cappedBlockSupport_lower L H t 0 (by simp)
    simpa [ht0, hx0] using (show L * x + H * z ≤
      L * (t * 0) + H * Real.sqrt (1 - (t * 0) ^ 2) from by
        simpa [ht0, hx0] using hrad) |>.trans h
  · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hq : x / t ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hx ht.1, (div_le_one htp).2 hxt⟩
    have h := cappedBlockSupport_lower L H t (x / t) hq
    rw [mul_div_cancel₀ _ ht0] at h
    linarith

/-- The capped support is genuinely attained in the two-coordinate disk. -/
theorem cappedBlockSupport_disk_attained (L H : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ x z : ℝ, 0 ≤ x ∧ x ≤ t ∧ 0 ≤ z ∧ x ^ 2 + z ^ 2 = 1 ∧
      L * x + H * z = cappedBlockSupport L H t := by
  obtain ⟨s, hs, he, _⟩ := cappedBlockSupport_attained L H t
  have hx : 0 ≤ t * s := mul_nonneg ht.1 hs.1
  have hxt : t * s ≤ t := mul_le_of_le_one_right ht.1 hs.2
  have hx1 : t * s ≤ 1 := hxt.trans ht.2
  have hsq : 0 ≤ 1 - (t * s) ^ 2 := by nlinarith
  exact ⟨t * s, Real.sqrt (1 - (t * s) ^ 2), hx, hxt, Real.sqrt_nonneg _,
    by nlinarith [Real.sq_sqrt hsq], he.symm⟩

theorem cappedBlockSupport_nonneg {L H t : ℝ} (hH : 0 ≤ H) :
    0 ≤ cappedBlockSupport L H t := by
  have h := cappedBlockSupport_lower L H t 0 (by simp)
  simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, Real.sqrt_one,
    mul_one, zero_add] at h
  exact hH.trans h

theorem cappedBlockSupport_le_norm (L H : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    cappedBlockSupport L H t ≤ Real.sqrt (L ^ 2 + H ^ 2) := by
  obtain ⟨x, z, _, _, _, hsq, he⟩ := cappedBlockSupport_disk_attained L H ht
  have h := sphere_weighted_sum_le_sqrt_mul ({()} : Finset Unit) L (fun _ => H)
    (fun _ => z) x 1 (by norm_num) (by simpa using hsq.le)
  simpa only [Finset.sum_singleton, mul_one, he] using h

/-- Increasing the low cap can only increase support. -/
theorem cappedBlockSupport_mono {L H t v : ℝ} (hH : 0 ≤ H)
    (ht : t ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) (htv : t ≤ v) :
    cappedBlockSupport L H t ≤ cappedBlockSupport L H v := by
  obtain ⟨x, z, hx, hxt, _, hsq, he⟩ := cappedBlockSupport_disk_attained L H ht
  rw [← he]
  exact cappedBlockSupport_bound hH hv hx (hxt.trans htv) hsq.le

/-- If the uncapped optimal direction fits, the cap causes no loss. -/
theorem cappedBlockSupport_eq_norm {L H t : ℝ} (hL : 0 ≤ L) (hH : 0 ≤ H)
    (ht : t ∈ Icc (0 : ℝ) 1) (hfit : L ≤ t * Real.sqrt (L ^ 2 + H ^ 2)) :
    cappedBlockSupport L H t = Real.sqrt (L ^ 2 + H ^ 2) := by
  apply le_antisymm (cappedBlockSupport_le_norm L H ht)
  let D := Real.sqrt (L ^ 2 + H ^ 2)
  have hDsq : D ^ 2 = L ^ 2 + H ^ 2 := Real.sq_sqrt (by positivity)
  by_cases hD0 : D = 0
  · change D ≤ cappedBlockSupport L H t
    rw [hD0]
    exact cappedBlockSupport_nonneg hH
  have hDp : 0 < D := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hD0)
  have hnorm : (L / D) ^ 2 + (H / D) ^ 2 = 1 := by
    rw [div_pow, div_pow, ← add_div, ← hDsq, div_self (pow_ne_zero _ hD0)]
  have h := cappedBlockSupport_bound (L := L) hH ht (div_nonneg hL hDp.le)
    ((div_le_iff₀ hDp).2 hfit) hnorm.le
  have he : L * (L / D) + H * (H / D) = D := by
    calc
      _ = (L ^ 2 + H ^ 2) / D := by ring
      _ = D := by rw [← hDsq]; field_simp
  rw [he] at h
  exact h

/-- When the cap binds, the optimum sits at its endpoint. -/
theorem cappedBlockSupport_eq_boundary {L H t : ℝ} (hL : 0 ≤ L) (hH : 0 ≤ H)
    (ht : t ∈ Icc (0 : ℝ) 1) (hbind : t * Real.sqrt (L ^ 2 + H ^ 2) < L) :
    cappedBlockSupport L H t = L * t + H * Real.sqrt (1 - t ^ 2) := by
  have ht1 : t < 1 := by
    have hLD : L ≤ Real.sqrt (L ^ 2 + H ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg H])
    by_contra hn
    have he : t = 1 := le_antisymm ht.2 (le_of_not_gt hn)
    simp only [he, one_mul] at hbind
    linarith
  let b := Real.sqrt (1 - t ^ 2)
  have hpos : 0 < 1 - t ^ 2 := by nlinarith [ht.1]
  have hb : 0 < b := Real.sqrt_pos.2 hpos
  have hbsq : b ^ 2 = 1 - t ^ 2 := Real.sq_sqrt hpos.le
  have hDsq := Real.sq_sqrt (show 0 ≤ L ^ 2 + H ^ 2 by positivity)
  have horder : H * t ≤ L * b := by
    have htD : 0 ≤ t * Real.sqrt (L ^ 2 + H ^ 2) :=
      mul_nonneg ht.1 (Real.sqrt_nonneg _)
    have hprod := mul_nonneg (sub_nonneg.mpr hbind.le)
      (add_nonneg hL htD)
    have hLs := sq_nonneg L
    have hts := sq_nonneg t
    nlinarith [mul_nonneg hL hb.le, mul_nonneg hH ht.1]
  apply le_antisymm
  · obtain ⟨x, z, hx, hxt, hz, hsq, he⟩ := cappedBlockSupport_disk_attained L H ht
    rw [← he]
    have htan : t * x + b * z ≤ 1 := by
      nlinarith [sq_nonneg (x - t), sq_nonneg (z - b)]
    have h₁ := mul_nonneg (sub_nonneg.mpr horder) (sub_nonneg.mpr hxt)
    have h₂ := mul_nonneg hH (sub_nonneg.mpr htan)
    have hscaled : b * (L * x + H * z) ≤ b * (L * t + H * b) := by
      nlinarith
    exact (mul_le_mul_iff_right₀ hb).1 hscaled
  · simpa only [mul_one] using cappedBlockSupport_lower L H t 1 (by simp)

/-- Division-free formula, valid also for zero low or high weight. -/
theorem cappedBlockSupport_formula {L H t : ℝ} (hL : 0 ≤ L) (hH : 0 ≤ H)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    cappedBlockSupport L H t =
      if L ≤ t * Real.sqrt (L ^ 2 + H ^ 2) then Real.sqrt (L ^ 2 + H ^ 2)
      else L * t + H * Real.sqrt (1 - t ^ 2) := by
  split_ifs with h
  · exact cappedBlockSupport_eq_norm hL hH ht h
  · exact cappedBlockSupport_eq_boundary hL hH ht (lt_of_not_ge h)

end
end GaloisForLFunctions.BiScaleUncertainty
