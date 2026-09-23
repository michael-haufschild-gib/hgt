import GaloisForLFunctions.HTGeometry.DigammaSecondOrderVertical

/-!
# The digamma logarithmic asymptotic on the whole right half plane

The unit-shift defect of `ψ(z) − log z + 1/(2z)` is an elementary function of `1/z` vanishing to
third order, and this is already available for every point of the right half plane of modulus at
least two.  Telescoping it along the integer shift orbit — where the modulus can only grow, and
grows at least like `(‖z‖ + n)/√2` — turns the third-order defect into a second-order remainder:

`ψ(z) = log z − 1/(2z) + O(‖z‖⁻²)`,   `Re z > 0`, `‖z‖ ≥ 2`,

with an absolute constant.  The vertical form of this estimate keeps the height, not the modulus, in
the denominator; on a ray through a nonreal direction the height and the modulus are comparable but
not equal, so the modulus form is the one an oblique asymptotic needs.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-! ## The modulus along the integer shift orbit -/

/-- In the closed right half plane the squared modulus grows at least by the square of the shift. -/
theorem norm_sq_add_nat_ge {z : ℂ} (hre : 0 ≤ z.re) (n : ℕ) :
    ‖z‖ ^ (2 : ℕ) + (n : ℝ) ^ (2 : ℕ) ≤ ‖z + (n : ℂ)‖ ^ (2 : ℕ) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, add_zero]
  nlinarith [Nat.cast_nonneg (α := ℝ) n, hre]

theorem norm_add_nat_ge_self {z : ℂ} (hre : 0 ≤ z.re) (n : ℕ) : ‖z‖ ≤ ‖z + (n : ℂ)‖ := by
  have h := norm_sq_add_nat_ge hre n
  have hn : (0 : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) := sq_nonneg _
  nlinarith [norm_nonneg z, norm_nonneg (z + (n : ℂ))]

theorem norm_add_nat_ge_re {z : ℂ} (n : ℕ) : z.re + (n : ℝ) ≤ ‖z + (n : ℂ)‖ := by
  have hre : (z + (n : ℂ)).re = z.re + n := by simp
  calc z.re + (n : ℝ) = (z + (n : ℂ)).re := hre.symm
    _ ≤ ‖z + (n : ℂ)‖ := Complex.re_le_norm _

/-- The shifted modulus is at least `(‖z‖ + n)/√2`, in squared form. -/
theorem sq_norm_add_nat_ge_half {z : ℂ} (hre : 0 ≤ z.re) (n : ℕ) :
    (‖z‖ + (n : ℝ)) ^ (2 : ℕ) ≤ 2 * ‖z + (n : ℂ)‖ ^ (2 : ℕ) := by
  have h := norm_sq_add_nat_ge hre n
  nlinarith [sq_nonneg (‖z‖ - (n : ℝ))]

/-! ## The shifted inverse-square sum -/

theorem norm_pos_of_re_pos {z : ℂ} (hre : 0 < z.re) : (0 : ℝ) < ‖z‖ := by
  refine norm_pos_iff.mpr fun h => ?_
  rw [h] at hre
  simp at hre

theorem norm_add_nat_pos {z : ℂ} (hre : 0 < z.re) (n : ℕ) : (0 : ℝ) < ‖z + (n : ℂ)‖ := by
  have hgt : (0 : ℝ) < z.re + (n : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  exact lt_of_lt_of_le hgt (norm_add_nat_ge_re n)

theorem summable_inv_norm_sq_add_nat {z : ℂ} (hre : 0 < z.re) :
    Summable (fun n : ℕ => 1 / ‖z + (n : ℂ)‖ ^ (2 : ℕ)) := by
  have hzpos : (0 : ℝ) < ‖z‖ := norm_pos_of_re_pos hre
  have hmaj : Summable (fun n : ℕ => 2 / (‖z‖ + (n : ℝ)) ^ (2 : ℕ)) :=
    ((summable_inv_sq_shift hzpos).mul_left 2).congr fun n => by rw [mul_one_div]
  refine hmaj.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · positivity
  · have hpos : (0 : ℝ) < ‖z + (n : ℂ)‖ := norm_add_nat_pos hre n
    have hsq := sq_norm_add_nat_ge_half (le_of_lt hre) n
    have hzn : (0 : ℝ) < (‖z‖ + (n : ℝ)) ^ (2 : ℕ) := by positivity
    rw [div_le_div_iff₀ (by positivity) hzn]
    linarith

/-- **The shifted inverse-square sum decays like `1/‖z‖`.** -/
theorem tsum_inv_norm_sq_add_nat_le {z : ℂ} (hre : 0 < z.re) (hz : 2 ≤ ‖z‖) :
    ∑' n : ℕ, 1 / ‖z + (n : ℂ)‖ ^ (2 : ℕ) ≤ 3 / ‖z‖ := by
  have hzpos : (0 : ℝ) < ‖z‖ := by linarith
  set a : ℝ := ‖z‖ with ha
  -- the majorant on the shifted line
  have hmajle : ∀ n : ℕ, 1 / ‖z + (n : ℂ)‖ ^ (2 : ℕ) ≤ 2 / (a + (n : ℝ)) ^ (2 : ℕ) := by
    intro n
    have hpos : (0 : ℝ) < ‖z + (n : ℂ)‖ := norm_add_nat_pos hre n
    have hsq := sq_norm_add_nat_ge_half (le_of_lt hre) n
    have hzn : (0 : ℝ) < (a + (n : ℝ)) ^ (2 : ℕ) := by positivity
    rw [div_le_div_iff₀ (by positivity) hzn]
    linarith
  have hmajsum : Summable (fun n : ℕ => 2 / (a + (n : ℝ)) ^ (2 : ℕ)) :=
    ((summable_inv_sq_shift hzpos).mul_left 2).congr fun n => by rw [mul_one_div]
  -- the exact bound for the shifted inverse squares
  have hhead : ∑' n : ℕ, 1 / (a + (n : ℝ)) ^ (2 : ℕ) ≤ 1 / a ^ (2 : ℕ) + 1 / a := by
    have hsum := summable_inv_sq_shift hzpos
    rw [← hsum.sum_add_tsum_nat_add 1]
    have hzero : ∑ n ∈ Finset.range 1, 1 / (a + (n : ℝ)) ^ (2 : ℕ) = 1 / a ^ (2 : ℕ) := by simp
    have htail : ∑' n : ℕ, 1 / (a + ((n + 1 : ℕ) : ℝ)) ^ (2 : ℕ) ≤ 1 / a := by
      have hmaj := hasSum_one_div_shift_mul_succ hzpos
      have hle : ∀ n : ℕ, 1 / (a + ((n + 1 : ℕ) : ℝ)) ^ (2 : ℕ) ≤ 1 / ((a + n) * (a + n + 1)) := by
        intro n
        have hp1 : (0 : ℝ) < a + (n : ℝ) := by positivity
        have hcast : a + ((n + 1 : ℕ) : ℝ) = a + (n : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have hsummable : Summable (fun n : ℕ => 1 / (a + ((n + 1 : ℕ) : ℝ)) ^ (2 : ℕ)) := by
        refine hmaj.summable.of_nonneg_of_le (fun n => by positivity) hle
      calc ∑' n : ℕ, 1 / (a + ((n + 1 : ℕ) : ℝ)) ^ (2 : ℕ)
          ≤ ∑' n : ℕ, 1 / ((a + n) * (a + n + 1)) := hsummable.tsum_le_tsum hle hmaj.summable
        _ = 1 / a := hmaj.tsum_eq
    rw [hzero]
    linarith
  have hsummable : Summable (fun n : ℕ => 1 / ‖z + (n : ℂ)‖ ^ (2 : ℕ)) := summable_inv_norm_sq_add_nat hre
  calc ∑' n : ℕ, 1 / ‖z + (n : ℂ)‖ ^ (2 : ℕ)
      ≤ ∑' n : ℕ, 2 / (a + (n : ℝ)) ^ (2 : ℕ) := hsummable.tsum_le_tsum hmajle hmajsum
    _ = 2 * ∑' n : ℕ, 1 / (a + (n : ℝ)) ^ (2 : ℕ) := by
        rw [← tsum_mul_left]
        exact tsum_congr fun n => by rw [mul_one_div]
    _ ≤ 2 * (1 / a ^ (2 : ℕ) + 1 / a) := by linarith
    _ ≤ 3 / a := by
        have h2 : 2 / a ^ (2 : ℕ) ≤ 1 / a := by
          rw [div_le_div_iff₀ (by positivity) hzpos]
          nlinarith
        have hexp : 2 * (1 / a ^ (2 : ℕ) + 1 / a) = 2 / a ^ (2 : ℕ) + 2 / a := by ring
        have hsum3 : (1 : ℝ) / a + 2 / a = 3 / a := by ring
        linarith

/-! ## The half-plane asymptotic -/

/-- **The second-order digamma asymptotic on the right half plane.**  With an absolute constant,
`ψ(z) = log z − 1/(2z) + O(‖z‖⁻²)` for every `z` of positive real part and modulus at least two. -/
theorem norm_digamma_sub_log_add_half_inv_le_of_re_pos {z : ℂ} (hre : 0 < z.re) (hz : 2 ≤ ‖z‖) :
    ‖Complex.digamma z - Complex.log z + 1 / (2 * z)‖ ≤ 5 / ‖z‖ ^ (2 : ℕ) := by
  have hzpos : (0 : ℝ) < ‖z‖ := by linarith
  set R : ℂ → ℂ := fun w => Complex.digamma w - Complex.log w + 1 / (2 * w) with hR
  set E : ℂ → ℂ := fun w => 1 / w - Complex.log (1 + 1 / w) - 1 / (2 * w * (w + 1)) with hE
  have hshiftre : ∀ n : ℕ, (0 : ℝ) < (z + (n : ℂ)).re := by
    intro n
    have : (z + (n : ℂ)).re = z.re + n := by simp
    rw [this]
    positivity
  have hshiftnorm : ∀ n : ℕ, (2 : ℝ) ≤ ‖z + (n : ℂ)‖ :=
    fun n => le_trans hz (norm_add_nat_ge_self (le_of_lt hre) n)
  set f : ℕ → ℂ := fun n => R (z + (n : ℂ)) with hf
  set g : ℕ → ℂ := fun n => E (z + (n : ℂ)) with hg
  have hstep : ∀ n : ℕ, f (n + 1) - f n = g n := by
    intro n
    have hcast : z + ((n + 1 : ℕ) : ℂ) = (z + (n : ℂ)) + 1 := by push_cast; ring
    show R (z + ((n + 1 : ℕ) : ℂ)) - R (z + (n : ℂ)) = E (z + (n : ℂ))
    rw [hcast]
    exact digamma_second_defect (hshiftre n) (hshiftnorm n)
  have hmaj : ∀ n : ℕ, ‖g n‖ ≤ (5 / 3 / ‖z‖) * (1 / ‖z + (n : ℂ)‖ ^ (2 : ℕ)) := by
    intro n
    have hbase := norm_digamma_second_defect_le (hshiftre n) (hshiftnorm n)
    have hnpos : (0 : ℝ) < ‖z + (n : ℂ)‖ := by linarith [hshiftnorm n]
    have hge : ‖z‖ ≤ ‖z + (n : ℂ)‖ := norm_add_nat_ge_self (le_of_lt hre) n
    refine le_trans hbase ?_
    rw [div_le_iff₀ (by positivity)]
    have hkey : (5 / 3 / ‖z‖) * (1 / ‖z + (n : ℂ)‖ ^ (2 : ℕ)) * ‖z + (n : ℂ)‖ ^ (3 : ℕ)
        = (5 / 3) * (‖z + (n : ℂ)‖ / ‖z‖) := by
      field_simp
    rw [hkey]
    have hone : (1 : ℝ) ≤ ‖z + (n : ℂ)‖ / ‖z‖ := (one_le_div hzpos).mpr hge
    linarith
  have hsummableNorm : Summable (fun n : ℕ => ‖g n‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) hmaj ?_
    exact (summable_inv_norm_sq_add_nat hre).mul_left (5 / 3 / ‖z‖)
  have hsummable : Summable g := hsummableNorm.of_norm
  have hvanish : Tendsto f atTop (nhds 0) := by
    have hdig : Tendsto (fun n : ℕ => Complex.digamma (z + (n : ℂ)) - Complex.log (z + (n : ℂ)))
        atTop (nhds 0) := tendsto_digamma_sub_log_horizontal hre
    have hinv : Tendsto (fun n : ℕ => 1 / (2 * (z + (n : ℂ)))) atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
        (g := fun n : ℕ => 1 / (2 * (z.re + (n : ℝ)))) ?_
      · have hpos : (0 : ℝ) < z.re + (n : ℝ) := by
          have := Nat.cast_nonneg (α := ℝ) n
          linarith
        have hge : z.re + (n : ℝ) ≤ ‖z + (n : ℂ)‖ := norm_add_nat_ge_re n
        rw [norm_div, norm_one, norm_mul, show ‖(2 : ℂ)‖ = 2 from by norm_num]
        rw [div_le_div_iff₀ (by have := norm_add_nat_pos hre n; linarith) (by linarith : (0:ℝ) < 2 * (z.re + (n : ℝ)))]
        nlinarith
      · have hdiv : Tendsto (fun n : ℕ => 2 * (z.re + (n : ℝ))) atTop atTop :=
          Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2)
            (Filter.tendsto_atTop_add_const_left atTop z.re tendsto_natCast_atTop_atTop)
        exact Tendsto.congr (fun n => by simp [one_div]) hdiv.inv_tendsto_atTop
    have := hdig.add hinv
    rw [add_zero] at this
    exact this.congr fun n => by rw [hf, hR]
  have hpartial : ∀ N : ℕ, ∑ n ∈ Finset.range N, g n = f N - f 0 := by
    intro N
    rw [Finset.sum_congr rfl (fun n _ => (hstep n).symm)]
    exact Finset.sum_range_sub f N
  have htend : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, g n) atTop (nhds (0 - f 0)) := by
    refine Tendsto.congr (fun N => (hpartial N).symm) ?_
    exact hvanish.sub tendsto_const_nhds
  have hsum : ∑' n : ℕ, g n = -f 0 := by
    have hgs := hsummable.hasSum_iff_tendsto_nat.mpr (by simpa using htend)
    exact hgs.tsum_eq
  have hf0 : f 0 = R z := by rw [hf]; norm_num
  have hnorm : ‖R z‖ ≤ ∑' n : ℕ, ‖g n‖ := by
    have : ‖(-f 0 : ℂ)‖ ≤ ∑' n : ℕ, ‖g n‖ := by
      rw [← hsum]
      exact norm_tsum_le_tsum_norm hsummableNorm
    rwa [norm_neg, hf0] at this
  refine le_trans hnorm ?_
  have hbound : ∑' n : ℕ, ‖g n‖
      ≤ (5 / 3 / ‖z‖) * ∑' n : ℕ, 1 / ‖z + (n : ℂ)‖ ^ (2 : ℕ) := by
    rw [← tsum_mul_left]
    exact hsummableNorm.tsum_le_tsum hmaj
      ((summable_inv_norm_sq_add_nat hre).mul_left (5 / 3 / ‖z‖))
  refine le_trans hbound ?_
  have htail := tsum_inv_norm_sq_add_nat_le hre hz
  have hfac : (0 : ℝ) ≤ 5 / 3 / ‖z‖ := by positivity
  calc (5 / 3 / ‖z‖) * ∑' n : ℕ, 1 / ‖z + (n : ℂ)‖ ^ (2 : ℕ)
      ≤ (5 / 3 / ‖z‖) * (3 / ‖z‖) := mul_le_mul_of_nonneg_left htail hfac
    _ = 5 / ‖z‖ ^ (2 : ℕ) := by field_simp

/-- **The first-order digamma asymptotic on the right half plane.** -/
theorem norm_digamma_sub_log_le_of_re_pos {z : ℂ} (hre : 0 < z.re) (hz : 2 ≤ ‖z‖) :
    ‖Complex.digamma z - Complex.log z‖ ≤ 3 / ‖z‖ := by
  have hzpos : (0 : ℝ) < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
  have hsecond := norm_digamma_sub_log_add_half_inv_le_of_re_pos hre hz
  have hhalf : ‖1 / (2 * z)‖ = 1 / (2 * ‖z‖) := by
    rw [norm_div, norm_one, norm_mul, show ‖(2 : ℂ)‖ = 2 from by norm_num]
  have hsplit : Complex.digamma z - Complex.log z
      = (Complex.digamma z - Complex.log z + 1 / (2 * z)) - 1 / (2 * z) := by ring
  rw [hsplit]
  refine le_trans (norm_sub_le _ _) ?_
  rw [hhalf]
  have hsq : 5 / ‖z‖ ^ (2 : ℕ) ≤ 5 / (2 * ‖z‖) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have : 5 / (2 * ‖z‖) + 1 / (2 * ‖z‖) = 3 / ‖z‖ := by field_simp; ring
  linarith

end

end GaloisForLFunctions.HTGeometry
