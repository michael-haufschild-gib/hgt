import GaloisForLFunctions.RHTower.LiClockPairedEtaFirstPrefixGammaBounds
import GaloisForLFunctions.RHTower.LiClockCentralTraceSineGrowth

/-!
# Exact full-completion leading asymptotic

The literal Gamma and dyadic completion retains its entire source after the
first Gamma atom is split off. Square-summable source rescaling gives a complete
two-rate remainder envelope at every complex clock. The full kernel and every
regular central contour have normalized leading coefficient exactly `1/5`.
-/

open Complex Filter Topology Set GaloisForLFunctions
namespace RHTower
noncomputable section

private theorem rescaled_hyperbolic_envelope {α : Type*} (β : α → ℂ)
    (hs : Summable (fun q => ‖β q‖ ^ 2)) {c : ℝ} (hc : 0 < c)
    (hb : ∀ q, c * ‖β q‖ ≤ 1) (t : ℂ) :
    ‖∑' q : α, β q * Complex.sinh (t * β q)‖ ≤
      c * (∑' q : α, ‖β q‖ ^ 2) * Real.sinh (‖t‖ / c) := by
  let q : α → ℂ := fun a => (c : ℂ) * β a
  have hn (a : α) : ‖q a‖ = c * ‖β a‖ := by
    simp only [q, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  have hq : Summable (fun a : α => ‖q a‖ ^ 2) :=
    (hs.mul_left (c ^ 2)).congr (fun a => by rw [hn]; ring)
  have hq1 (a : α) : ‖q a‖ ≤ 1 := by rw [hn]; exact hb a
  have ht : ‖t / (c : ℂ)‖ ≤ ‖t‖ / c := by
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    rfl
  have hh := norm_liClockCompletionHyperbolic_tsum_le q hq hq1 (t / (c : ℂ)) ht
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have heq : (∑' a : α, β a * Complex.sinh (t * β a)) =
      (1 / (c : ℂ)) * ∑' a : α, q a * Complex.sinh ((t / (c : ℂ)) * q a) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro a
    have hp : (t / (c : ℂ)) * q a = t * β a := by dsimp only [q]; field_simp
    rw [hp]
    dsimp only [q]
    field_simp
  have hmass : (∑' a : α, ‖q a‖ ^ 2) = c ^ 2 * ∑' a : α, ‖β a‖ ^ 2 := by
    rw [← tsum_mul_left]
    exact tsum_congr (fun a => by rw [hn]; ring)
  rw [heq, norm_mul]
  have hnorm : ‖(1 / (c : ℂ))‖ = 1 / c := by
    simp only [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  rw [hnorm]
  rw [hmass] at hh
  have hh2 := mul_le_mul_of_nonneg_left hh (one_div_nonneg.mpr hc.le)
  calc
    _ ≤ (1 / c) * (c ^ 2 * (∑' a : α, ‖β a‖ ^ 2) * Real.sinh (‖t‖ / c)) := hh2
    _ = _ := by field_simp [hc.ne']

private theorem gamma_norm (n : ℕ) :
    ‖(liClockPairedEtaGammaReciprocal n : ℂ)‖ = liClockPairedEtaGammaReciprocal n := by
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (liClockPairedEtaGammaReciprocal_nonneg n)]

private theorem gamma_square_summable :
    Summable (fun n : ℕ => ‖(liClockPairedEtaGammaReciprocal n : ℂ)‖ ^ 2) :=
  summable_liClockPairedEtaGammaReciprocal_square.congr (fun n => by rw [gamma_norm])

private theorem gamma_square_mass :
    (∑' n : ℕ, ‖(liClockPairedEtaGammaReciprocal n : ℂ)‖ ^ 2) =
      liClockPairedEtaFirstPrefixGammaSquareMass := by
  unfold liClockPairedEtaFirstPrefixGammaSquareMass
  apply tsum_congr
  intro n
  rw [gamma_norm]
  unfold liClockPairedEtaGammaReciprocal
  rw [inv_pow, inv_eq_one_div]

private theorem gamma_tail_square_mass :
    (∑' n : ℕ, ‖(liClockPairedEtaGammaReciprocal (n + 1) : ℂ)‖ ^ 2) =
      liClockPairedEtaFirstPrefixGammaSquareMass - 4 / 25 := by
  have hh := gamma_square_summable.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hh
  rw [gamma_square_mass] at hh
  have hz : ‖(liClockPairedEtaGammaReciprocal 0 : ℂ)‖ ^ 2 = 4 / 25 := by
    rw [gamma_norm]
    norm_num [liClockPairedEtaGammaReciprocal]
  rw [hz] at hh
  linarith

private theorem gamma_tail_le (n : ℕ) :
    liClockPairedEtaGammaReciprocal (n + 1) ≤ 2 / 9 := by
  unfold liClockPairedEtaGammaReciprocal
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  calc
    _ ≤ (9 / 2 : ℝ)⁻¹ := (inv_le_inv₀ (by positivity) (by norm_num)).2 (by
      push_cast
      linarith)
    _ = _ := by norm_num

private theorem norm_gamma_tail_le (t : ℂ) :
    ‖∑' n : ℕ, (liClockPairedEtaGammaReciprocal (n + 1) : ℂ) *
      Complex.sinh (t * (liClockPairedEtaGammaReciprocal (n + 1) : ℂ))‖ ≤
      (9 / 2) * (liClockPairedEtaFirstPrefixGammaSquareMass - 4 / 25) *
        Real.sinh ((2 / 9) * ‖t‖) := by
  have hs : Summable (fun n : ℕ => ‖(liClockPairedEtaGammaReciprocal (n + 1) : ℂ)‖ ^ 2) :=
    (summable_nat_add_iff 1).2 gamma_square_summable
  have hb (n : ℕ) : (9 / 2) * ‖(liClockPairedEtaGammaReciprocal (n + 1) : ℂ)‖ ≤ 1 := by
    rw [gamma_norm]
    nlinarith [gamma_tail_le n]
  have hh := rescaled_hyperbolic_envelope
    (fun n : ℕ => (liClockPairedEtaGammaReciprocal (n + 1) : ℂ)) hs
    (c := 9 / 2) (by norm_num) hb t
  rw [gamma_tail_square_mass] at hh
  convert hh using 1
  congr 1
  ring

private theorem norm_dyadic_packet_le (t : ℂ) :
    ‖∑' k : ℤ, liClockPairedEtaDyadicReciprocal k *
      Complex.sinh (t * liClockPairedEtaDyadicReciprocal k)‖ ≤
      (3 / 8) * Real.sinh (‖t‖ / 8) := by
  have hb (k : ℤ) : (8 : ℝ) * ‖liClockPairedEtaDyadicReciprocal k‖ ≤ 1 := by
    nlinarith [liClockPairedEtaDyadicReciprocal_norm_sq_le_one_sixtyfourth k,
      norm_nonneg (liClockPairedEtaDyadicReciprocal k)]
  have hh := rescaled_hyperbolic_envelope liClockPairedEtaDyadicReciprocal
    summable_liClockPairedEtaDyadicReciprocal_norm_sq (c := 8) (by norm_num) hb t
  calc
    _ ≤ 8 * (∑' k : ℤ, ‖liClockPairedEtaDyadicReciprocal k‖ ^ 2) *
        Real.sinh (‖t‖ / 8) := hh
    _ ≤ (3 / 8) * Real.sinh (‖t‖ / 8) := by
      apply mul_le_mul_of_nonneg_right _ (Real.sinh_nonneg_iff.mpr (by positivity))
      nlinarith [liClockPairedEtaDyadicReciprocal_square_mass_le]

/-- Complete remainder after the first Gamma atom, retaining the full Gamma tail
and both signs of every nonzero dyadic source index. -/
theorem norm_liClockPairedEtaCompletionKernel_sub_firstGamma_le (t : ℂ) :
    ‖liClockPairedEtaCompletionKernel t - (2 / 5 : ℂ) * Complex.sinh ((2 / 5 : ℂ) * t)‖ ≤
      (9 / 2) * (liClockPairedEtaFirstPrefixGammaSquareMass - 4 / 25) *
        Real.sinh ((2 / 9) * ‖t‖) + (3 / 8) * Real.sinh (‖t‖ / 8) := by
  have hs := (summable_norm_liClockPairedEtaCompletionKernel_gamma t).of_norm
  have hh := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hh
  have hz : (liClockPairedEtaGammaReciprocal 0 : ℂ) *
      Complex.sinh (t * (liClockPairedEtaGammaReciprocal 0 : ℂ)) =
      (2 / 5 : ℂ) * Complex.sinh ((2 / 5 : ℂ) * t) := by
    norm_num [liClockPairedEtaGammaReciprocal]
    congr 1
    ring
  rw [hz] at hh
  have heq : liClockPairedEtaCompletionKernel t -
      (2 / 5 : ℂ) * Complex.sinh ((2 / 5 : ℂ) * t) =
      (∑' n : ℕ, (liClockPairedEtaGammaReciprocal (n + 1) : ℂ) *
        Complex.sinh (t * (liClockPairedEtaGammaReciprocal (n + 1) : ℂ))) +
      ∑' k : ℤ, liClockPairedEtaDyadicReciprocal k *
        Complex.sinh (t * liClockPairedEtaDyadicReciprocal k) := by
    unfold liClockPairedEtaCompletionKernel
    rw [← hh]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add (norm_gamma_tail_le t) (norm_dyadic_packet_le t))

/-- The exact complete remainder envelope holds for the literal completion contour
at every regular central radius and every complex clock. -/
theorem norm_liClockPairedEtaCompletionClockResponse_sub_firstGamma_le {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1 / 2) (t : ℂ) :
    ‖liClockPairedEtaCompletionClockResponse r t -
      (2 / 5 : ℂ) * Complex.sinh ((2 / 5 : ℂ) * t)‖ ≤
      (9 / 2) * (liClockPairedEtaFirstPrefixGammaSquareMass - 4 / 25) *
        Real.sinh ((2 / 9) * ‖t‖) + (3 / 8) * Real.sinh (‖t‖ / 8) := by
  rw [liClockPairedEtaCompletionClockResponse_eq_kernel hr hrhalf]
  exact norm_liClockPairedEtaCompletionKernel_sub_firstGamma_le t

private theorem exp_neg_mul_sinh_tendsto_zero {a b : ℝ} (hb : 0 < b) (hba : b < a) :
    Tendsto (fun t : ℝ => Real.exp (-a * t) * Real.sinh (b * t)) atTop (𝓝 0) := by
  have hd : Tendsto (fun t : ℝ => Real.exp (-(a - b) * t)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (sub_pos.mpr hba))
  have hh := hd.mul (liClock_exp_neg_mul_sinh_tendsto hb)
  convert hh using 1
  · funext t
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  · norm_num

private theorem completion_remainder_exp_neg_mul_tendsto_zero :
    Tendsto (fun t : ℝ => (Real.exp (-(2 / 5) * t) : ℂ) *
      (liClockPairedEtaCompletionKernel (t : ℂ) -
        (2 / 5 : ℂ) * Complex.sinh ((2 / 5 : ℂ) * (t : ℂ)))) atTop (𝓝 0) := by
  have hgamma := exp_neg_mul_sinh_tendsto_zero (a := 2 / 5) (b := 2 / 9)
    (by norm_num) (by norm_num)
  have hdyad := exp_neg_mul_sinh_tendsto_zero (a := 2 / 5) (b := 1 / 8)
    (by norm_num) (by norm_num)
  have hlimit := (hgamma.const_mul ((9 / 2) *
    (liClockPairedEtaFirstPrefixGammaSquareMass - 4 / 25))).add (hdyad.const_mul (3 / 8))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ (by simpa using hlimit)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have hh := norm_liClockPairedEtaCompletionKernel_sub_firstGamma_le (t : ℂ)
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht] at hh
  rw [show t / 8 = (1 / 8 : ℝ) * t by ring] at hh
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  convert mul_le_mul_of_nonneg_left hh (Real.exp_pos (-(2 / 5) * t)).le using 1 <;>
    first | rfl | ring

/-- The full actual completion kernel has leading coefficient exactly `1/5`.
Every source atom is retained in the exponentially smaller complete remainder. -/
theorem liClockPairedEtaCompletionKernel_exp_neg_mul_tendsto :
    Tendsto (fun t : ℝ => (Real.exp (-(2 / 5) * t) : ℂ) *
      liClockPairedEtaCompletionKernel (t : ℂ)) atTop (𝓝 (1 / 5 : ℂ)) := by
  have hsinh := liClock_exp_neg_mul_complex_sinh_ofReal_tendsto (by norm_num : (0 : ℝ) < 2 / 5)
  have hh := completion_remainder_exp_neg_mul_tendsto_zero.add (hsinh.const_mul (2 / 5 : ℂ))
  convert hh using 1
  · funext t
    push_cast
    ring
  · norm_num

/-- The literal completion contour has the same exact complex leading coefficient
for every regular central radius. -/
theorem liClockPairedEtaCompletionClockResponse_exp_neg_mul_tendsto {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1 / 2) :
    Tendsto (fun t : ℝ => (Real.exp (-(2 / 5) * t) : ℂ) *
      liClockPairedEtaCompletionClockResponse r (t : ℂ)) atTop (𝓝 (1 / 5 : ℂ)) := by
  simpa only [liClockPairedEtaCompletionClockResponse_eq_kernel hr hrhalf] using
    liClockPairedEtaCompletionKernel_exp_neg_mul_tendsto

/-- The real literal completion clock escapes to plus infinity at every regular
central radius, with no arithmetic or zero-location premise. -/
theorem liClockPairedEtaCompletionClockResponse_re_tendsto_atTop {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1 / 2) :
    Tendsto (fun t : ℝ => (liClockPairedEtaCompletionClockResponse r (t : ℂ)).re)
      atTop atTop := by
  have hf := liClockPairedEtaCompletionClockResponse_exp_neg_mul_tendsto hr hrhalf
  have hre : Tendsto (fun t : ℝ => Real.exp (-(2 / 5) * t) *
      (liClockPairedEtaCompletionClockResponse r (t : ℂ)).re) atTop (𝓝 (1 / 5 : ℝ)) := by
    have h := (Complex.continuous_re.tendsto (1 / 5 : ℂ)).comp hf
    simp only [Function.comp_def, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at h
    norm_num at h
    simpa only [neg_mul] using h
  have he : Tendsto (fun t : ℝ => Real.exp ((2 / 5) * t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2 / 5))
  have hm := hre.pos_mul_atTop (by norm_num) he
  convert hm using 1
  funext t
  have hexp : Real.exp (-(2 / 5) * t) * Real.exp ((2 / 5) * t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  calc
    (liClockPairedEtaCompletionClockResponse r (t : ℂ)).re =
        (liClockPairedEtaCompletionClockResponse r (t : ℂ)).re * 1 := by ring
    _ = (liClockPairedEtaCompletionClockResponse r (t : ℂ)).re *
        (Real.exp (-(2 / 5) * t) * Real.exp ((2 / 5) * t)) := by rw [hexp]
    _ = _ := by ring

end
end RHTower
