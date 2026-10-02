import GaloisForLFunctions.RHTower.ChiDualSpatialTransitionBound

/-!
# Complete dual-block decay outside the spatial saddle window

The actual amplitude variation gives the nonstationary gain on either side
of the saddle. The complete Poisson remainder and actual chi normalization
then give uniform exterior decay on the same schedule as the interior profile.
-/

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower


/-- Outside either endpoint by h, the literal first spatial mode retains
the full nonstationary gain, with its actual amplitude and variation. -/
theorem exists_chiDualSpatial_first_mode_exterior_bound (c : ℂ) (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Metric.closedBall c r, ∀ N : ℝ, 50 ≤ N →
      ∀ a : ℝ, 0 < a → N ≤ 2 * Real.pi * a ∧ 2 * Real.pi * a ≤ 2 * N →
      ∀ h l u : ℝ, 0 < h → N / 5 - 1 / 2 ≤ l → u ≤ 6 * N / 25 + 1 / 2 → l ≤ u →
      u ≤ a - h ∨ a + h ≤ l →
      ‖∫ x in l..u, chiDualSpatialSlowAmplitude s N x *
        Complex.exp (I * (chiDualSpatialPhase (2 * Real.pi * a) (-(2 * Real.pi)) x : ℂ))‖ ≤
          C * N ^ (s.re - 1) * (a / h) := by
  obtain ⟨C, hC, hj⟩ := exists_chiDualSpatialSlowJets_bound c r
  refine ⟨16 * C, by positivity, ?_⟩
  intro s hs N hN a ha ht h l u hh hl hu hlu hside
  have hN0 : 0 < N := by linarith only [hN]
  have hlen : u - l ≤ N := by linarith only [hl, hu, hN]
  let U := C * N ^ (s.re - 1)
  have hU : 0 ≤ U := mul_nonneg hC.le (Real.rpow_nonneg hN0.le _)
  have hxx (x : ℝ) (hx : x ∈ Icc l u) :
      N / 5 - 1 / 2 ≤ x ∧ x ≤ 6 * N / 25 + 1 / 2 :=
    ⟨hl.trans hx.1, hx.2.trans hu⟩
  have hxdata (x : ℝ) (hx : x ∈ Icc l u) :
      0 < x ∧ x / N ∈ Icc (1 / 6 : ℝ) (1 / 3) := by
    obtain ⟨hx0, hxlo, hxhi, _, _⟩ := chiDual_spatial_block_ratio_bounds hN ht (hxx x hx)
    refine ⟨hx0, ?_, ?_⟩
    · apply (le_div_iff₀ hN0).mpr
      linarith only [hxlo, hN0]
    · apply (div_le_iff₀ hN0).mpr
      linarith only [hxhi, hN0]
  obtain ⟨_, hllo, _, _, _⟩ := chiDual_spatial_block_ratio_bounds hN ht (hxx l ⟨le_rfl, hlu⟩)
  obtain ⟨_, _, huhi, _, _⟩ := chiDual_spatial_block_ratio_bounds hN ht (hxx u ⟨hlu, le_rfl⟩)
  have hlcomp : a / 2 ≤ l := by
    nlinarith only [hllo, ht.2, ha, mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) ha.le]
  have hucomp : u ≤ 2 * a := by
    nlinarith only [huhi, ht.1, mul_nonneg (sub_nonneg.mpr Real.pi_lt_four.le) ha.le]
  have hdom : uIcc l u ⊆ Ioi (0 : ℝ) := by
    intro x hx
    rw [uIcc_of_le hlu] at hx
    exact (hxdata x hx).1
  have hA1 := (continuousOn_chiDualSpatialSlowJets s hN0).2.1.mono hdom
  have hderiv (x : ℝ) (hx : x ∈ Icc l u) : ‖chiDualSpatialSlowFirst s N x‖ ≤ U / N :=
    (hj s hs N hN0 x (hxdata x hx).2).2.1
  have hvar : (∫ x in l..u, ‖chiDualSpatialSlowFirst s N x‖) ≤ U := by
    have hi := intervalIntegral.integral_mono_on hlu hA1.intervalIntegrable.norm
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => U / N) volume l u) hderiv
    have he : (∫ x in l..u, (U / N : ℝ)) = (U / N) * (u - l) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [he] at hi
    calc
      _ ≤ (U / N) * (u - l) := hi
      _ ≤ (U / N) * N := mul_le_mul_of_nonneg_left hlen (div_nonneg hU hN0.le)
      _ = U := div_mul_cancel₀ _ hN0.ne'
  have hv : ∀ x ∈ uIcc l u, HasDerivAt (chiDualSpatialSlowAmplitude s N)
      (chiDualSpatialSlowFirst s N x) x := by
    intro x hx
    exact hasDerivAt_chiDualSpatialSlowAmplitude s hN0 (hdom hx)
  have hb := norm_integral_complexAmplitude_mul_spatial_exterior_le ha hh hlcomp hlu hucomp
    hside hv hA1.intervalIntegrable
  let E : ℂ := Complex.exp (I * (chiDualSpatialPhase (2 * Real.pi * a) (-(2 * Real.pi)) a : ℂ))
  have hE : ‖E‖ = 1 := Complex.norm_exp_I_mul_ofReal _
  have hphase (x : ℝ) :
      Complex.exp (I * (chiDualSpatialPhase (2 * Real.pi * a) (-(2 * Real.pi)) x : ℂ)) =
        bourgainOscillation (-chiDualSpatialSaddlePhase a x) * E := by
    dsimp only [bourgainOscillation, E]
    rw [← Complex.exp_add, ← mul_add, ← Complex.ofReal_add]
    have he := chiDualSpatialPhase_sub_saddle a x
    have hp : chiDualSpatialPhase (2 * Real.pi * a) (-(2 * Real.pi)) x =
        -chiDualSpatialSaddlePhase a x +
          chiDualSpatialPhase (2 * Real.pi * a) (-(2 * Real.pi)) a := by linarith only [he]
    rw [hp]
  have hi : (∫ x in l..u, chiDualSpatialSlowAmplitude s N x *
      Complex.exp (I * (chiDualSpatialPhase (2 * Real.pi * a) (-(2 * Real.pi)) x : ℂ))) =
      (∫ x in l..u, chiDualSpatialSlowAmplitude s N x *
        bourgainOscillation (-chiDualSpatialSaddlePhase a x)) * E := by
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    rw [hphase]
    ring
  rw [hi, norm_mul, hE, mul_one]
  calc
    _ ≤ (8 * a / (Real.pi * h)) * (‖chiDualSpatialSlowAmplitude s N u‖ +
        ∫ x in l..u, ‖chiDualSpatialSlowFirst s N x‖) := hb
    _ ≤ (8 * a / (Real.pi * h)) * (U + U) := mul_le_mul_of_nonneg_left
      (add_le_add (hj s hs N hN0 u (hxdata u ⟨hlu, le_rfl⟩).2).1 hvar) (by positivity)
    _ ≤ (8 * a / (1 * h)) * (U + U) := by
      gcongr
      linarith only [Real.pi_gt_three]
    _ = _ := by dsimp only [U]; ring

/-- The complete literal block is small outside either stationary endpoint.
The estimate includes every discarded-at-leading-order Fourier mode. -/
theorem exists_chiDual_integer_block_exterior_error (c : ℂ) (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Metric.closedBall c r, ∀ N : ℝ, 50 ≤ N →
      ∀ a : ℝ, 0 < a → N ≤ 2 * Real.pi * a ∧ 2 * Real.pi * a ≤ 2 * N →
      ∀ h : ℝ, 0 < h → ∀ A B : ℕ,
      N / 5 ≤ (A : ℝ) → (B : ℝ) ≤ 6 * N / 25 → A ≤ B →
      (B : ℝ) + 1 / 2 ≤ a - h ∨ a + h ≤ (A : ℝ) - 1 / 2 →
      ‖∑ n ∈ Finset.Icc A B, smoothAFECutoff ((n : ℝ) / N) *
        zetaChiDualInteriorAtom s n (2 * Real.pi * a)‖ ≤
        C * N ^ (s.re - 1) * ‖zetaChi (s + ((2 * Real.pi * a : ℝ) : ℂ) * I)‖ * (1 + a / h) := by
  obtain ⟨C₀, hC₀, herr⟩ := exists_chiDual_integer_block_single_mode_error c r
  obtain ⟨C₁, hC₁, hext⟩ := exists_chiDualSpatial_first_mode_exterior_bound c r
  refine ⟨C₀ + C₁, add_pos hC₀ hC₁, ?_⟩
  intro s hs N hN a ha ht h hh A B hA hB hAB hside
  have hN0 : 0 < N := by linarith only [hN]
  have hab : (A : ℝ) - 1 / 2 ≤ (B : ℝ) + 1 / 2 := by
    have hABR : (A : ℝ) ≤ B := by exact_mod_cast hAB
    linarith only [hABR]
  let q : ℂ := zetaChi (s + ((2 * Real.pi * a : ℝ) : ℂ) * I)
  let S : ℂ := ∑ n ∈ Finset.Icc A B, smoothAFECutoff ((n : ℝ) / N) *
    zetaChiDualInteriorAtom s n (2 * Real.pi * a)
  let J : ℂ := ∫ x in ((A : ℝ) - 1 / 2)..((B : ℝ) + 1 / 2), chiDualSpatialSlowAmplitude s N x *
    Complex.exp (I * (chiDualSpatialPhase (2 * Real.pi * a) (-(2 * Real.pi)) x : ℂ))
  have h0 : ‖S - q * J‖ ≤ C₀ * N ^ (s.re - 1) * ‖q‖ :=
    herr s hs N hN (2 * Real.pi * a) ht A B hA hB hAB
  have h1 : ‖J‖ ≤ C₁ * N ^ (s.re - 1) * (a / h) :=
    hext s hs N hN a ha ht h ((A : ℝ) - 1 / 2) ((B : ℝ) + 1 / 2) hh
      (by linarith only [hA]) (by linarith only [hB]) hab hside
  change ‖S‖ ≤ _
  calc
    _ = ‖(S - q * J) + q * J‖ := by rw [sub_add_cancel]
    _ ≤ ‖S - q * J‖ + ‖q * J‖ := norm_add_le _ _
    _ ≤ C₀ * N ^ (s.re - 1) * ‖q‖ + ‖q‖ * (C₁ * N ^ (s.re - 1) * (a / h)) := by
      rw [norm_mul]
      exact add_le_add h0 (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
    _ = (N ^ (s.re - 1) * ‖q‖) * (C₀ + C₁ * (a / h)) := by ring
    _ ≤ (N ^ (s.re - 1) * ‖q‖) * ((C₀ + C₁) * (1 + a / h)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith only [hC₁, mul_nonneg hC₀.le (div_nonneg ha.le hh.le)]
    _ = _ := by dsimp only [q]; ring


/-- Outside the two transition bands, the complete literal dual block tends
to zero at rate O(1/m) on the polynomial conductor schedule, uniformly over
all points of each fixed right-strip disc. -/
theorem exists_chiDual_integer_block_exterior_decay
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop, ∀ s ∈ Metric.closedBall c r,
      ∀ a : ℝ, 0 < a → (m : ℝ) ^ 10 ≤ 2 * Real.pi * a ∧ 2 * Real.pi * a ≤ 2 * (m : ℝ) ^ 10 →
      ∀ A B : ℕ, (m : ℝ) ^ 10 / 5 ≤ A → (B : ℝ) ≤ 6 * (m : ℝ) ^ 10 / 25 → A ≤ B →
      (B : ℝ) + 1 / 2 ≤ a - (m : ℝ) ^ 6 ∨ a + (m : ℝ) ^ 6 ≤ (A : ℝ) - 1 / 2 →
      ‖∑ n ∈ Finset.Icc A B, smoothAFECutoff ((n : ℝ) / (m : ℝ) ^ 10) *
          zetaChiDualInteriorAtom s n (2 * Real.pi * a)‖ ≤ C / m := by
  obtain ⟨C₀, hC₀, hext⟩ := exists_chiDual_integer_block_exterior_error c r
  obtain ⟨C₁, hC₁, hrow⟩ := exists_reflectedCompactGaussianRow_disc_bounds c hr hc0 hc1
  refine ⟨2 * C₀ * C₁, by positivity, ?_⟩
  have hp : Tendsto (fun m : ℕ => m ^ 10) atTop atTop := tendsto_pow_atTop (by decide)
  filter_upwards [hp.eventually hrow, eventually_ge_atTop (50 : ℕ)] with m hrowm hm50
  have hmR : (50 : ℝ) ≤ m := by exact_mod_cast hm50
  have hm1 : (1 : ℝ) ≤ m := by linarith only [hmR]
  have hm0 : (0 : ℝ) < m := by linarith only [hmR]
  have hmN : (m : ℝ) ≤ (m : ℝ) ^ 10 := by
    have h9 : (1 : ℝ) ≤ (m : ℝ) ^ 9 := one_le_pow₀ hm1
    nlinarith only [mul_nonneg (sub_nonneg.mpr h9) hm0.le]
  have hN : (50 : ℝ) ≤ (m : ℝ) ^ 10 := hmR.trans hmN
  have hN0 : 0 < (m : ℝ) ^ 10 := by positivity
  norm_num only [Nat.cast_pow] at hrowm
  intro s hs a ha ht A B hA hB hAB hside
  have hahi : a ≤ (m : ℝ) ^ 10 := by
    nlinarith only [ht.2, ha, mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) ha.le]
  have hb := hext s hs ((m : ℝ) ^ 10) hN a ha ht ((m : ℝ) ^ 6) (by positivity)
    A B hA hB hAB hside
  let q : ℂ := zetaChi (s + ((2 * Real.pi * a : ℝ) : ℂ) * I)
  have hrowId : ((m : ℝ) ^ 10) ^ (s.re - 1) * ‖q‖ * Real.sqrt ((m : ℝ) ^ 10) =
      ‖reflectedCompactGaussianRow s ((m : ℝ) ^ 10) (2 * Real.pi * a)‖ := by
    rw [norm_reflectedCompactGaussianRow s hN0 (2 * Real.pi * a)]
    have he : ((m : ℝ) ^ 10) ^ (s.re - 1) * Real.sqrt ((m : ℝ) ^ 10) =
        ((m : ℝ) ^ 10) ^ (s.re - 1 / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN0]
      congr 1
      ring
    calc
      _ = ‖q‖ * (((m : ℝ) ^ 10) ^ (s.re - 1) * Real.sqrt ((m : ℝ) ^ 10)) := by ring
      _ = _ := by rw [he]
  have hsqrt : Real.sqrt ((m : ℝ) ^ 10) = (m : ℝ) ^ 5 := by
    rw [show (m : ℝ) ^ 10 = ((m : ℝ) ^ 5) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hscalar : (1 + a / (m : ℝ) ^ 6) / Real.sqrt ((m : ℝ) ^ 10) ≤ 2 / m := by
    have hquot : a / (m : ℝ) ^ 6 ≤ (m : ℝ) ^ 4 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) ^ 6)).mpr
      calc
        _ ≤ (m : ℝ) ^ 10 := hahi
        _ = _ := by ring
    have h4 : (1 : ℝ) ≤ (m : ℝ) ^ 4 := one_le_pow₀ hm1
    calc
      _ ≤ (2 * (m : ℝ) ^ 4) / Real.sqrt ((m : ℝ) ^ 10) :=
        div_le_div_of_nonneg_right (by linarith only [hquot, h4]) (Real.sqrt_nonneg _)
      _ = _ := by rw [hsqrt]; field_simp
  apply hb.trans
  calc
    _ = C₀ * ‖reflectedCompactGaussianRow s ((m : ℝ) ^ 10) (2 * Real.pi * a)‖ *
        ((1 + a / (m : ℝ) ^ 6) / Real.sqrt ((m : ℝ) ^ 10)) := by
      rw [← hrowId]
      dsimp only [q]
      field_simp
    _ ≤ C₀ * C₁ * (2 / (m : ℝ)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hrowm (2 * Real.pi * a) ht s hs).1 hC₀.le
      · exact hscalar
      · positivity
      · positivity
    _ = _ := by ring

end RHTower
