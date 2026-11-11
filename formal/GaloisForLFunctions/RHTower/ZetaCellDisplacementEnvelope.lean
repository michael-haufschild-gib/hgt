import GaloisForLFunctions.RHTower.ZetaUnitCellSquareMass
import GaloisForLFunctions.RHTower.ZetaResidueSmallDisplacements

/-!
# Local displacement bounds from zeta cell masses

Area mean value bounds the pole-cleared zeta function on a small disc
by one cell's square mass. Two height factors and the disc Lipschitz
estimate turn this into a local displacement bound for `ζ(s)/s`.
-/

noncomputable section

open Complex Metric Set

namespace RHTower

/-- A nearby cell's square mass controls the normalized zeta function on
a small disc around the critical line. -/
theorem norm_zeta_div_le_unitCellSquareMass {r : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4)
    {n : ℕ} (hn : 8 ≤ n) {s z : ℂ} (hs : s.re = 1 / 2)
    (him : |s.im - n| ≤ 1) (hz : z ∈ ball s (r / 2)) :
    ‖riemannZeta z / z‖ ≤ 8 / (Real.sqrt Real.pi * r) *
      (Real.sqrt (zetaUnitCellSquareMass r n) / (n : ℝ) ^ 2) := by
  have hnR : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith only [hnR]
  have hzdist := mem_ball_iff_norm.mp hz
  have hzre := abs_lt.mp ((abs_re_le_norm (z - s)).trans_lt hzdist)
  have hzim := abs_lt.mp ((abs_im_le_norm (z - s)).trans_lt hzdist)
  simp only [Complex.sub_re, hs] at hzre
  simp only [Complex.sub_im] at hzim
  have hs0 := abs_le.mp him
  have hzre0 : 0 < z.re := by linarith only [hzre.1, hr4]
  have hzre1 : z.re < 1 := by linarith only [hzre.2, hr4]
  have hz0 : z ≠ 0 := by intro h; simpa only [h, zero_re, lt_self_iff_false] using hzre0
  have hz1 : z ≠ 1 := by intro h; simpa only [h, one_re, lt_self_iff_false] using hzre1
  have hzheight : (n : ℝ) / 2 ≤ z.im := by linarith only [hzim.1, hs0.1, hnR, hr4]
  have hzn : (n : ℝ) / 2 ≤ ‖z‖ :=
    hzheight.trans ((le_abs_self z.im).trans (abs_im_le_norm z))
  have hzn1 : (n : ℝ) / 2 ≤ ‖z - 1‖ := by
    have h := abs_im_le_norm (z - 1)
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at h
    exact hzheight.trans ((le_abs_self z.im).trans h)
  have hmass := normSq_mul_area_le_box differentiable_zetaEntire
    (z := z) (r := r / 2) (a := 1 / 2 - r) (b := 5 / 2)
    (c := (n : ℝ) - 3) (d := (n : ℝ) + 4) (by positivity)
    (by linarith only [hzre.1]) (by linarith only [hzre.2, hr4])
    (by linarith only [hzim.1, hs0.1, hr4]) (by linarith only [hzim.2, hs0.2, hr4])
  change Real.pi * (r / 2) ^ 2 * ‖zetaEntire z‖ ^ 2 ≤ zetaUnitCellSquareMass r n at hmass
  let Φ := zetaUnitCellSquareMass r n
  have hΦ : 0 ≤ Φ := zetaUnitCellSquareMass_nonneg hr.le _
  let D := Real.sqrt Real.pi * (r / 2)
  have hD : 0 < D := mul_pos (Real.sqrt_pos.2 Real.pi_pos) (half_pos hr)
  have hsq : (D * ‖zetaEntire z‖) ^ 2 ≤ (Real.sqrt Φ) ^ 2 := by
    rw [Real.sq_sqrt hΦ]
    calc
      (D * ‖zetaEntire z‖) ^ 2 = Real.pi * (r / 2) ^ 2 * ‖zetaEntire z‖ ^ 2 := by
        dsimp [D]
        rw [mul_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]
      _ ≤ Φ := hmass
  have hroot : D * ‖zetaEntire z‖ ≤ Real.sqrt Φ :=
    (sq_le_sq₀ (mul_nonneg hD.le (norm_nonneg _)) (Real.sqrt_nonneg _)).mp hsq
  have hF : ‖zetaEntire z‖ ≤ Real.sqrt Φ / D :=
    (le_div_iff₀ hD).mpr (by simpa only [mul_comm] using hroot)
  have hden : (n : ℝ) ^ 2 / 4 ≤ ‖z - 1‖ * ‖z‖ := by
    calc (n : ℝ) ^ 2 / 4 = ((n : ℝ) / 2) * ((n : ℝ) / 2) := by ring
      _ ≤ ‖z - 1‖ * ‖z‖ := mul_le_mul hzn1 hzn (by positivity) (norm_nonneg _)
  calc
    ‖riemannZeta z / z‖ = ‖zetaEntire z‖ / (‖z - 1‖ * ‖z‖) := by
      rw [zetaEntire_eq hz1, norm_mul, norm_div]
      field_simp [norm_ne_zero_iff.mpr hz0, norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz1)]
    _ ≤ (Real.sqrt Φ / D) / (‖z - 1‖ * ‖z‖) :=
      div_le_div_of_nonneg_right hF (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ (Real.sqrt Φ / D) / ((n : ℝ) ^ 2 / 4) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = 8 / (Real.sqrt Real.pi * r) * (Real.sqrt Φ / (n : ℝ) ^ 2) := by
      dsimp [D]
      field_simp <;> ring

/-- A small displacement to a zeta zero is paid by the normalized square
root of the surrounding cell mass. -/
theorem norm_zeta_div_le_displacement_unitCellSquareMass
    {r : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4)
    {n : ℕ} (hn : 8 ≤ n) {s η : ℂ} (hs : s.re = 1 / 2)
    (him : |s.im - n| ≤ 1) (hη : ‖η‖ < r / 4) (hzero : riemannZeta (s + η) = 0) :
    ‖riemannZeta s / s‖ ≤ 32 / (Real.sqrt Real.pi * r ^ 2) *
      (Real.sqrt (zetaUnitCellSquareMass r n) / (n : ℝ) ^ 2) * ‖η‖ := by
  let A := 8 / (Real.sqrt Real.pi * r) *
    (Real.sqrt (zetaUnitCellSquareMass r n) / (n : ℝ) ^ 2)
  have hbound : ∀ z ∈ ball s (r / 2), ‖riemannZeta z / z‖ ≤ A :=
    fun z hz => norm_zeta_div_le_unitCellSquareMass hr hr4 hn hs him hz
  have hdiff : DifferentiableOn ℂ (fun z => riemannZeta z / z) (ball s (r / 2)) := by
    intro z hz
    have h := abs_lt.mp ((abs_re_le_norm (z - s)).trans_lt (mem_ball_iff_norm.mp hz))
    simp only [Complex.sub_re, hs] at h
    have hz0 : z ≠ 0 := by intro heq; rw [heq, zero_re] at h; linarith only [h.1, hr4]
    have hz1 : z ≠ 1 := by intro heq; rw [heq, one_re] at h; linarith only [h.2, hr4]
    exact ((differentiableAt_riemannZeta hz1).div differentiableAt_id hz0).differentiableWithinAt
  have h := Bottcher.norm_sub_le_of_bounded_on_ball (half_pos hr) hdiff hbound
    (z := s) (w := s + η) (mem_ball_self (by positivity)) (by
      rw [mem_ball_iff_norm, add_sub_cancel_left]
      simpa only [div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hη)
  rw [hzero, zero_div, sub_zero, show s - (s + η) = -η by ring, norm_neg] at h
  calc
    ‖riemannZeta s / s‖ ≤ (2 * A / (r / 2)) * ‖η‖ := h
    _ = 32 / (Real.sqrt Real.pi * r ^ 2) *
        (Real.sqrt (zetaUnitCellSquareMass r n) / (n : ℝ) ^ 2) * ‖η‖ := by
      dsimp [A]
      field_simp <;> ring

private theorem abs_height_sub_floor_natAbs_le_one (t : ℝ) :
    |(|t|) - (⌊t⌋.natAbs : ℝ)| ≤ 1 := by
  have hcast : (⌊t⌋.natAbs : ℝ) = |(⌊t⌋ : ℝ)| := by
    cases ⌊t⌋ with
    | ofNat n => simp
    | negSucc n =>
      simp
      rw [abs_of_nonpos (by linarith only [Nat.cast_nonneg (α := ℝ) n])]
      ring
  have hnear : |t - (⌊t⌋ : ℝ)| ≤ 1 := abs_le.mpr
    ⟨by linarith only [Int.floor_le t], by linarith only [Int.lt_floor_add_one t]⟩
  have h := abs_norm_sub_norm_le t (⌊t⌋ : ℝ)
  simp only [Real.norm_eq_abs] at h
  rw [← hcast] at h
  exact h.trans hnear

/-- On the critical line, small displacements to zeta zeros are controlled
by a cell sequence with every prescribed moment strictly above one. -/
theorem exists_summable_zeta_displacement_cell_envelope {q : ℝ}
    (hq1 : 1 < q) (hq2 : q < 2) :
    ∃ δ > 0, ∃ v : ℤ → ℝ, (∀ k, 0 ≤ v k) ∧ Summable (fun k => v k ^ q) ∧
      ∀ s η : ℂ, s.re = 1 / 2 → ‖η‖ < δ → riemannZeta (s + η) = 0 →
        ‖riemannZeta s / s‖ ≤ v ⌊s.im⌋ * ‖η‖ := by
  have hq : 0 < q := zero_lt_one.trans hq1
  obtain ⟨r, hr, hr4, hmoment⟩ := exists_summable_zetaUnitCellEnvelope_rpow hq1 hq2
  obtain ⟨r₀, hr₀, C, hC, hsmall⟩ :=
    exists_zeta_residue_displacement_bound (ε := 1 / 6) (by norm_num)
  let D := 32 / (Real.sqrt Real.pi * r ^ 2)
  have hD : 0 < D := by
    dsimp [D]
    exact div_pos (by norm_num)
      (mul_pos (Real.sqrt_pos.2 Real.pi_pos) (sq_pos_of_pos hr))
  let lo : ℕ → ℝ := fun n => 64 * C / ((n : ℝ) + 1) ^ 2
  let hi : ℕ → ℝ := fun n => D * (Real.sqrt (zetaUnitCellSquareMass r n) / (n : ℝ) ^ 2)
  let v₀ : ℕ → ℝ := fun n => max (lo n) (hi n)
  let v : ℤ → ℝ := fun k => v₀ k.natAbs
  have hlo : ∀ n, 0 ≤ lo n := fun n => by dsimp [lo]; positivity
  have hhi : ∀ n, 0 ≤ hi n := fun n => by dsimp [hi]; positivity
  have hloSum : Summable (fun n => lo n ^ q) := by
    have hp := Real.summable_one_div_nat_rpow.mpr (by linarith only [hq1] : 1 < 2 * q)
    have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 * q)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hp
    refine (hs.mul_left ((64 * C) ^ q)).congr fun n => ?_
    dsimp [lo]
    rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity)]
    ring
  have hhiSum : Summable (fun n => hi n ^ q) := by
    refine (hmoment.mul_left (D ^ q)).congr fun n => ?_
    dsimp [hi]
    rw [Real.mul_rpow hD.le (by positivity)]
  have hv₀ : Summable (fun n => v₀ n ^ q) := by
    refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg
      ((hlo n).trans (le_max_left _ _)) _) ?_ (hloSum.add hhiSum)
    intro n
    rcases le_total (lo n) (hi n) with h | h
    · rw [show v₀ n = hi n from max_eq_right h]
      exact le_add_of_nonneg_left (Real.rpow_nonneg (hlo n) q)
    · rw [show v₀ n = lo n from max_eq_left h]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (hhi n) q)
  have hv : Summable (fun k => v k ^ q) := by
    refine Summable.of_nat_of_neg ?_ ?_ <;> simpa [v] using hv₀
  refine ⟨min (r / 4) r₀, lt_min (by positivity) hr₀, v,
    (fun k => (hlo _).trans (le_max_left _ _)), hv, fun s η hs hη hzero => ?_⟩
  have hηr : ‖η‖ < r / 4 := hη.trans_le (min_le_left _ _)
  have hη₀ : ‖η‖ < r₀ := hη.trans_le (min_le_right _ _)
  let n := ⌊s.im⌋.natAbs
  have hnear : |(|s.im|) - (n : ℝ)| ≤ 1 := abs_height_sub_floor_natAbs_le_one s.im
  by_cases hn : n < 8
  · have hnR : (n : ℝ) < 8 := by exact_mod_cast hn
    have hn7 : (n : ℝ) ≤ 7 := by exact_mod_cast (show n ≤ 7 by omega)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hsq : ((n : ℝ) + 1) ^ 2 ≤ 64 := by nlinarith only [hn7, hn0]
    have hClo : C ≤ lo n := by
      apply (le_div_iff₀ (by positivity : 0 < ((n : ℝ) + 1) ^ 2)).mpr
      have hmul := mul_le_mul_of_nonneg_left hsq hC.le
      simpa only [mul_comm] using hmul
    have hpow : 1 ≤ (1 + |s.im|) ^ (5 / 6 - (1 / 6 : ℝ)) :=
      Real.one_le_rpow (le_add_of_nonneg_right (abs_nonneg _)) (by norm_num)
    calc
      ‖riemannZeta s / s‖ ≤ C * ‖η‖ / (1 + |s.im|) ^ (5 / 6 - (1 / 6 : ℝ)) :=
        hsmall s η hs hη₀ hzero
      _ ≤ C * ‖η‖ := div_le_self (mul_nonneg hC.le (norm_nonneg _)) hpow
      _ ≤ v ⌊s.im⌋ * ‖η‖ := mul_le_mul_of_nonneg_right
        (hClo.trans (le_max_left _ _)) (norm_nonneg _)
  have hn8 : 8 ≤ n := le_of_not_gt hn
  have hb : ‖riemannZeta s / s‖ ≤ hi n * ‖η‖ := by
    by_cases him : 0 ≤ s.im
    · rw [abs_of_nonneg him] at hnear
      exact norm_zeta_div_le_displacement_unitCellSquareMass hr hr4 hn8 hs hnear hηr hzero
    · have hneg : s.im < 0 := lt_of_not_ge him
      have hcs : ((starRingEnd ℂ) s).re = 1 / 2 := by simpa only [conj_re] using hs
      have hcn : |((starRingEnd ℂ) s).im - (n : ℝ)| ≤ 1 := by
        simpa only [conj_im, abs_of_neg hneg] using hnear
      have hcη : ‖(starRingEnd ℂ) η‖ < r / 4 := by simpa only [norm_conj] using hηr
      have hczero : riemannZeta ((starRingEnd ℂ) s + (starRingEnd ℂ) η) = 0 := by
        rw [← map_add, riemannZeta_conj, hzero, map_zero]
      have h := norm_zeta_div_le_displacement_unitCellSquareMass hr hr4 hn8 hcs hcn hcη hczero
      simpa only [norm_div, riemannZeta_conj, norm_conj] using h
  exact hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

end RHTower
