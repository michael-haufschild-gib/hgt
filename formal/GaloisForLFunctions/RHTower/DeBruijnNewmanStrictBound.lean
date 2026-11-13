import GaloisForLFunctions.RHTower.DeBruijnTopZeroVelocity
import GaloisForLFunctions.RHTower.DeBruijnBarrierZerosSimple
import GaloisForLFunctions.RHTower.KiKimLeeUniformReality
import GaloisForLFunctions.RHTower.FiniteZeroSubquadraticRigidity

/-!
# The de Bruijn–Newman constant is strictly below de Bruijn's bound

In the normalization `H_t(z) = ∫ Φ(x) e^{tx²} e^{izx} dx` (where de Bruijn's bound reads
`Λ ≤ 1/8`), `newmanConstant < 1/8` (`newmanConstant_lt_eighth`); in the standard normalization
this is the Ki–Kim–Lee bound `Λ < 1/2`.

**Proof.** If `Λ = 1/8`, then at every time `s < 1/8` some zero of `H_s` lies on the de Bruijn
barrier `(Im z)² = ¼ − 2s` (otherwise, the nonreal zeros being finite, de Bruijn's theorem restarted
at time `s` gives `Λ < 1/8`: `newmanConstant_le_of_zeros_im_sq_le`). Take barrier zeros `ζ_n` of
`H_{s₀+h_n}`, `h_n → 0`. They stay in a compact box (uniform Ki–Kim–Lee reality), so a subsequence
converges to a barrier zero `z*` of `H_{s₀}`. That zero is simple (`deriv_riemannHeat_ne_zero_of_barrier`)
and has maximal imaginary part, and `H_{s₀}` has a real zero (`exists_riemannHeat_real_zero`, from the
Riemann–Lebesgue lemma and finite-zero Hadamard rigidity). Hence `z*` descends with velocity
`Im(H''/H') ≤ −1/y* − c`, `c > 0` (`im_ratio_le_of_top_zero`), strictly faster than the barrier
`d/dt √(¼ − 2t) = −1/y*`, while the zero motion estimate (`exists_im_zero_le_of_simple_zero`) forces
the nearby `ζ_n` below `y* − h_n/y* − c h_n + O(h_n²)`, contradicting `(Im ζ_n)² = y*² − 2h_n`.

With the Csordas–Smith–Varga simplicity above `Λ`: for `t ≥ 1/8` all zeros of `H_t` are real and
simple (`riemannHeat_zeros_real_simple_of_eighth_le`); under RH this holds for every `t > 0`, so a
multiple zero of `H_t` at any `t > 0` refutes RH (`not_riemannHypothesis_of_multiple_zero`).
-/

open Complex MeasureTheory Filter Topology Set Metric

namespace RHTower.DeBruijn

noncomputable section

/-! ## Decay on the real axis and a real zero -/

/-- **Riemann–Lebesgue.** `H_t(x) → 0` as `|x| → ∞` along the real axis. -/
theorem tendsto_riemannHeat_cocompact (t : ℝ) :
    Tendsto (fun x : ℝ => riemannHeat t x) (cocompact ℝ) (𝓝 0) := by
  have h := Real.tendsto_integral_exp_smul_cocompact (fun v : ℝ => heatWeight t v)
  have hc : (-(1 / (2 * Real.pi)) : ℝ) ≠ 0 := by
    have := Real.pi_pos; exact neg_ne_zero.mpr (by positivity)
  have hφ : Tendsto (Homeomorph.mulLeft₀ _ hc) (cocompact ℝ) (cocompact ℝ) :=
    (Homeomorph.map_cocompact _).le
  refine (h.comp hφ).congr fun x => ?_
  simp only [Function.comp, Homeomorph.coe_mulLeft₀, riemannHeat_eq_expTransform, expTransform]
  congr 1
  funext v
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm]
  congr 1
  congr 1
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp

theorem norm_riemannHeat_le_rpow {t : ℝ} (ht : 0 ≤ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖riemannHeat t z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (3 / 2 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := (riemannKernel_superExp.mul_exp_sq ht).exists_envelope
  refine ⟨3 * C, by positivity, fun z => (hbound z).trans (Real.exp_le_exp.mpr ?_)⟩
  set u := 1 + ‖z‖ with hu
  have hu1 : 1 ≤ u := by simp only [hu]; linarith [norm_nonneg z]
  have hlog : Real.log (2 + ‖z‖) ≤ 3 * u ^ (1 / 2 : ℝ) := by
    have hs : Real.sqrt (1 + u) ≤ 3 / 2 * Real.sqrt u := by
      rw [show (3 / 2 : ℝ) * Real.sqrt u = Real.sqrt ((3 / 2) ^ 2 * u) by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have h1 : Real.log (1 + u) = 2 * Real.log (Real.sqrt (1 + u)) := by
      rw [Real.log_sqrt (by linarith)]; ring
    have h2 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < 1 + u))
    have h3 : 1 ≤ Real.sqrt u := Real.one_le_sqrt.mpr hu1
    rw [show 2 + ‖z‖ = 1 + u by simp only [hu]; ring, h1, ← Real.sqrt_eq_rpow]
    nlinarith
  have hpow : u ^ (3 / 2 : ℝ) = u * u ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
  rw [hpow]
  have : C * u * Real.log (2 + ‖z‖) ≤ C * u * (3 * u ^ (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  linarith

/-- **`H_t` has infinitely many zeros** for every `t > 0`. Otherwise `H_t = P(z) c e^{Bz}` with a
polynomial `P`, which does not tend to `0` along the real axis in the direction of `Re B`. -/
theorem riemannHeat_zeros_infinite {t : ℝ} (ht : 0 < t) :
    {z : ℂ | riemannHeat t z = 0}.Infinite := by
  intro hfin
  obtain ⟨C, hC, hgrow⟩ := norm_riemannHeat_le_rpow ht.le
  obtain ⟨T, m, c, B, hc, hform, -⟩ := exists_finiteDivisorFactor_mul_exp_of_finite_zeroSet
    (differentiable_riemannHeat ht.le) (by norm_num) (by norm_num) hC hgrow hfin
  set R := 1 + ∑ w ∈ T, ‖w‖
  have hlow : ∀ x : ℝ, R ≤ |x| → 0 ≤ B.re * x → ‖c‖ ≤ ‖riemannHeat t x‖ := by
    intro x hx hBx
    rw [hform, norm_mul, norm_mul, Complex.norm_exp]
    have h1 := one_le_norm_finiteDivisorFactor_of_far T m
      (z := (x : ℂ)) (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hx)
    have h2 : 1 ≤ Real.exp (B * x).re := by
      apply Real.one_le_exp
      simpa [Complex.mul_re] using hBx
    calc ‖c‖ = 1 * ‖c‖ * 1 := by ring
      _ ≤ ‖finiteDivisorFactor T m x‖ * ‖c‖ * Real.exp (B * x).re := by gcongr
  have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hdecay := (tendsto_riemannHeat_cocompact t).norm
  rw [norm_zero] at hdecay
  rcases le_or_gt 0 B.re with hB | hB
  · have h := hdecay.mono_left atTop_le_cocompact
    have := ge_of_tendsto h (eventually_ge_atTop R |>.mono fun x hx =>
      hlow x (hx.trans (le_abs_self x)) (by
        have : 0 ≤ x := le_trans (by positivity) hx
        positivity))
    linarith
  · have h := hdecay.mono_left atBot_le_cocompact
    have hR : 0 < R := by positivity
    have := ge_of_tendsto h ((eventually_le_atBot (-R)).mono fun x hx => by
      have hx0 : x < 0 := by linarith
      exact hlow x (by rw [abs_of_neg hx0]; linarith) (by nlinarith))
    linarith

/-- **`H_t` has a real zero** for every `t > 0`: it has infinitely many zeros, and only finitely
many of them are not real. -/
theorem exists_riemannHeat_real_zero {t : ℝ} (ht : 0 < t) : ∃ x : ℝ, riemannHeat t x = 0 := by
  by_contra hno
  simp only [not_exists] at hno
  refine riemannHeat_zeros_infinite ht
    ((riemannHeat_nonreal_zeros_finite ht).subset fun z hz => ⟨hz, fun him => ?_⟩)
  apply hno z.re
  rw [← show (z.re : ℂ) = z from Complex.ext (by simp) (by simp [him])] at hz
  exact hz

/-! ## Restarting de Bruijn's theorem -/

/-- **de Bruijn restarted at time `s`.** If every zero of `H_s` has `(Im z)² ≤ D`, then
`newmanConstant ≤ s + D/2`. -/
theorem newmanConstant_le_of_zeros_im_sq_le {s D : ℝ} (hs : 0 ≤ s) (hD : 0 ≤ D)
    (h : ∀ z, riemannHeat s z = 0 → z.im ^ 2 ≤ D) : newmanConstant ≤ s + D / 2 := by
  rcases eq_or_lt_of_le hD with h0 | hDpos
  · subst h0
    refine (csInf_le realRootedTimes_bddBelow ⟨hs, fun z hz => ?_⟩).trans (by linarith)
    have := h z hz
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg _))
  · refine csInf_le realRootedTimes_bddBelow ⟨by positivity, fun z hz => ?_⟩
    have hk := riemannHeat_kernel s hs
    have hreal := cosTransform_heat_zeros_real hk (D := D) (t := D / 2) h (by linarith)
      (by positivity) z
    apply hreal
    have e : (fun x => riemannKernelReal x * Real.exp (s * x ^ 2) * Real.exp (D / 2 * x ^ 2)) =
        fun x => riemannKernelReal x * Real.exp ((s + D / 2) * x ^ 2) := by
      funext x
      rw [mul_assoc, ← Real.exp_add]
      ring_nf
    rw [e]
    exact hz

/-- If `Λ ≥ 1/8`, then at every time `0 < s < 1/8` some zero of `H_s` lies on the barrier
`(Im z)² = ¼ − 2s`. -/
theorem exists_barrier_zero_of_eighth_le {s : ℝ} (hs : 0 < s) (hs8 : s < 1 / 8)
    (hΛ : 1 / 8 ≤ newmanConstant) :
    ∃ ζ : ℂ, riemannHeat s ζ = 0 ∧ 1 / 4 - 2 * s ≤ ζ.im ^ 2 := by
  by_contra hno
  simp only [not_exists, not_and, not_le] at hno
  set F := {z : ℂ | riemannHeat s z = 0 ∧ z.im ≠ 0}
  have hF : F.Finite := riemannHeat_nonreal_zeros_finite hs
  obtain ⟨D, hD0, hDlt, hDz⟩ : ∃ D : ℝ, 0 ≤ D ∧ D < 1 / 4 - 2 * s ∧
      ∀ z, riemannHeat s z = 0 → z.im ^ 2 ≤ D := by
    rcases F.eq_empty_or_nonempty with hE | hne
    · refine ⟨0, le_rfl, by linarith, fun z hz => ?_⟩
      by_cases him : z.im = 0
      · rw [him]; simp
      · have hzF : z ∈ F := ⟨hz, him⟩
        rw [hE] at hzF
        exact absurd hzF (Set.notMem_empty z)
    · obtain ⟨z₁, hz₁, hmax⟩ := Set.exists_max_image F (fun z => z.im ^ 2) hF hne
      refine ⟨z₁.im ^ 2, sq_nonneg _, hno z₁ hz₁.1, fun z hz => ?_⟩
      by_cases him : z.im = 0
      · rw [him]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        exact sq_nonneg _
      · exact hmax z ⟨hz, him⟩
  have := newmanConstant_le_of_zeros_im_sq_le hs.le hD0 hDz
  linarith

/-- `‖H_{t+h}(z) − H_t(z)‖ ≤ (∫ x² Φ e^{(t+1)x²} e^{|Im z||x|}) h` for `0 ≤ h ≤ 1`. -/
theorem norm_riemannHeat_add_sub_le {t h : ℝ} (ht : 0 ≤ t) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (z : ℂ) :
    ‖riemannHeat (t + h) z - riemannHeat t z‖ ≤
      (∫ x, |x| ^ 2 * ‖heatWeight (t + 1) x‖ * Real.exp (|z.im| * |x|)) * h := by
  have := norm_riemannHeat_time_taylor_le ht (by linarith) (by rw [abs_of_nonneg hh0]; exact hh1)
    1 z
  simpa [abs_of_nonneg hh0] using this

/-! ## The top zero leaves the barrier -/

/-- **A barrier zero leaves the barrier.** Let `z*` be a zero of `H_s` (`s > 0`) with `Im z* > 0` on
the barrier `(Im z*)² = ¼ − 2s`. Then for small `h > 0` every zero of `H_{s+h}` near `z*` lies
strictly inside the barrier at time `s + h`. -/
theorem exists_zeros_below_barrier {s : ℝ} (hs : 0 < s) {zs : ℂ} (hz : riemannHeat s zs = 0)
    (hy : 0 < zs.im) (hbar : zs.im ^ 2 = 1 / 4 - 2 * s) :
    ∃ r > 0, ∃ h₁ > 0, ∀ h : ℝ, 0 < h → h ≤ h₁ → ∀ z : ℂ, ‖z - zs‖ ≤ r →
      riemannHeat (s + h) z = 0 → z.im ^ 2 < 1 / 4 - 2 * (s + h) := by
  set y := zs.im
  have hd := deriv_riemannHeat_ne_zero_of_barrier hs hz hbar.ge hy.ne'
  have htop : ∀ ζ, riemannHeat s ζ = 0 → ζ.im ^ 2 ≤ y ^ 2 := fun ζ hζ =>
    (riemannHeat_zeros_im_sq_le hs hζ).trans (max_le hbar.ge (sq_nonneg y))
  obtain ⟨xr, hxr⟩ := exists_riemannHeat_real_zero hs
  have hvel := im_ratio_le_of_top_zero hs.le hz hd hy htop hxr
  set g := 2 * y / ((xr - zs.re) ^ 2 + y ^ 2)
  have hg : 0 < g := by positivity
  obtain ⟨r₀, hr₀, h₀, hh₀, C, hmove⟩ := exists_im_zero_le_of_simple_zero hs hz hd
  set E := 2 * y * |C| + (1 / y + g + |C|) ^ 2 + 1
  have hE : 0 < E := by positivity
  refine ⟨min r₀ (y / 2), lt_min hr₀ (by positivity), min h₀ (min 1 (y * g / E)),
    lt_min hh₀ (lt_min one_pos (by positivity)), fun h hh hh₁ z hzr hz0 => ?_⟩
  have hh0 : h ≤ h₀ := hh₁.trans (min_le_left _ _)
  have hh1 : h ≤ 1 := hh₁.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhE : h ≤ y * g / E := hh₁.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hup := hmove h ⟨hh.le, hh0⟩ z (hzr.trans (min_le_left _ _)) hz0
  have hlow : y / 2 ≤ z.im := by
    have := (Complex.abs_im_le_norm (z - zs)).trans (hzr.trans (min_le_right _ _))
    rw [Complex.sub_im, abs_le] at this
    linarith
  -- the velocity bound
  set v := (deriv (deriv (riemannHeat s)) zs / deriv (riemannHeat s) zs).im
  have hv : v ≤ -(1 / y) - g := by
    have := hvel; simp only [v, g] at this ⊢; linarith [show -1 / y = -(1 / y) by ring]
  have hzim : z.im ≤ y - h / y - g * h + |C| * h ^ 2 := by
    have h1 : h * v ≤ h * (-(1 / y) - g) := mul_le_mul_of_nonneg_left hv hh.le
    have h2 : C * h ^ 2 ≤ |C| * h ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg h)
    have e : h * (-(1 / y) - g) = -(h / y) - g * h := by ring
    linarith
  set a := h / y + g * h - |C| * h ^ 2
  have ha : |a| ≤ h * (1 / y + g + |C|) := by
    have hC0 := abs_nonneg C
    have hq : h ^ 2 ≤ h := by nlinarith
    have hCh : |C| * h ^ 2 ≤ |C| * h := mul_le_mul_of_nonneg_left hq hC0
    have hgh : 0 ≤ g * h := by positivity
    have hhy : 0 ≤ h / y := by positivity
    have hCh2 : 0 ≤ |C| * h ^ 2 := by positivity
    have e : h * (1 / y + g + |C|) = h / y + g * h + |C| * h := by ring
    rw [abs_le, e]
    simp only [a]
    constructor <;> linarith
  have hsq : (y - a) ^ 2 < y ^ 2 - 2 * h := by
    have e : (y - a) ^ 2 = y ^ 2 - 2 * h - 2 * y * g * h + 2 * y * |C| * h ^ 2 + a ^ 2 := by
      simp only [a]; field_simp; ring
    have ha2 : a ^ 2 ≤ h ^ 2 * (1 / y + g + |C|) ^ 2 := by
      calc a ^ 2 = |a| ^ 2 := (sq_abs a).symm
        _ ≤ (h * (1 / y + g + |C|)) ^ 2 := pow_le_pow_left₀ (abs_nonneg a) ha 2
        _ = h ^ 2 * (1 / y + g + |C|) ^ 2 := by ring
    have hEh : h * E ≤ y * g := by
      rw [le_div_iff₀ hE] at hhE; linarith
    have : 2 * y * |C| * h ^ 2 + h ^ 2 * (1 / y + g + |C|) ^ 2 < 2 * y * g * h := by
      have hpos : 0 < h ^ 2 := by positivity
      have : h ^ 2 * E ≤ y * g * h := by nlinarith
      simp only [E] at this
      nlinarith
    linarith
  have hza : z.im ≤ y - a := by simp only [a]; linarith
  have hz0' : 0 ≤ z.im := by linarith
  calc z.im ^ 2 ≤ (y - a) ^ 2 := pow_le_pow_left₀ hz0' hza 2
    _ < y ^ 2 - 2 * h := hsq
    _ = 1 / 4 - 2 * (s + h) := by rw [hbar]; ring

/-! ## The strict bound -/

/-- **The Ki–Kim–Lee bound.** `newmanConstant < 1/8`, i.e. `Λ < 1/2` in the standard normalization. -/
theorem newmanConstant_lt_eighth : newmanConstant < 1 / 8 := by
  by_contra hge
  have hΛ : 1 / 8 ≤ newmanConstant := not_lt.mp hge
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℝ, s₀ = 1 / 16 := ⟨_, rfl⟩
  have hs₀pos : 0 < s₀ := by rw [hs₀]; norm_num
  have hs₀bar : 1 / 4 - 2 * s₀ = 1 / 8 := by rw [hs₀]; norm_num
  obtain ⟨hn, hhn⟩ : ∃ hn : ℕ → ℝ, ∀ n, hn n = 1 / (32 * ((n : ℝ) + 1)) :=
    ⟨fun n => 1 / (32 * ((n : ℝ) + 1)), fun n => rfl⟩
  have hn_pos : ∀ n, 0 < hn n := fun n => by rw [hhn]; positivity
  have hn_le : ∀ n, hn n ≤ 1 / 32 := by
    intro n
    rw [hhn, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hn_lim : Tendsto hn atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => (1 / 32 : ℝ) * (1 / ((n : ℝ) + 1))) atTop
        (𝓝 ((1 / 32) * 0)) := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    rw [hhn]
    field_simp
  have hs8 : ∀ n, s₀ + hn n < 1 / 8 := fun n => by rw [hs₀]; linarith [hn_le n]
  have hbarrier : ∀ n, ∃ ζ : ℂ, riemannHeat (s₀ + hn n) ζ = 0 ∧
      1 / 4 - 2 * (s₀ + hn n) ≤ ζ.im ^ 2 := fun n =>
    exists_barrier_zero_of_eighth_le (s := s₀ + hn n) (by linarith [hn_pos n]) (hs8 n) hΛ
  choose ζ hζ0 hζbar using hbarrier
  -- the barrier zeros stay in a compact box
  obtain ⟨X₀, hX₀⟩ := exists_riemannHeat_zeros_real_uniform (t₀ := s₀) hs₀pos
  have him2 : ∀ n, (ζ n).im ^ 2 ≤ 1 / 4 := fun n =>
    (riemannHeat_zeros_im_sq_le (by linarith [hn_pos n]) (hζ0 n)).trans
      (max_le (by linarith [hn_pos n]) (by norm_num))
  have hbox : ∀ n, ζ n ∈ closedBall (0 : ℂ) (|X₀| + 1) := by
    intro n
    have hne : (ζ n).im ≠ 0 := by
      intro h0
      have := hζbar n
      rw [h0] at this
      linarith [hs8 n]
    have hre : |(ζ n).re| < X₀ := by
      by_contra h
      exact hne (hX₀ (s₀ + hn n) ⟨by linarith [hn_pos n], (hs8 n).le⟩ _ (hζ0 n)
        (not_lt.mp h))
    have him : |(ζ n).im| ≤ 1 / 2 := by
      rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]; linarith [him2 n]
    rw [mem_closedBall, dist_zero_right]
    calc ‖ζ n‖ ≤ |(ζ n).re| + |(ζ n).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ |X₀| + 1 := by linarith [le_abs_self X₀]
  obtain ⟨z₁, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : ℂ) (|X₀| + 1)).tendsto_subseq hbox
  have hhφ : Tendsto (fun n => hn (φ n)) atTop (𝓝 0) := hn_lim.comp hφ.tendsto_atTop
  -- the limit is a zero of `H_{s₀}`
  have hK : ∀ n, ‖riemannHeat (s₀ + hn (φ n)) (ζ (φ n)) - riemannHeat s₀ (ζ (φ n))‖ ≤
      (∫ x, |x| ^ 2 * ‖heatWeight (s₀ + 1) x‖ * Real.exp (1 * |x|)) * hn (φ n) := by
    intro n
    refine (norm_riemannHeat_add_sub_le hs₀pos.le (hn_pos _).le
      (by linarith [hn_le (φ n)]) _).trans (mul_le_mul_of_nonneg_right ?_ (hn_pos _).le)
    refine integral_mono (integrable_pow_mul_heatWeight (by linarith) _ _)
      (integrable_pow_mul_heatWeight (by linarith) _ _) fun x => ?_
    have : |(ζ (φ n)).im| ≤ 1 := by
      have h1 : |(ζ (φ n)).im| ^ 2 ≤ 1 / 4 := by rw [sq_abs]; exact him2 _
      nlinarith [abs_nonneg (ζ (φ n)).im]
    dsimp only
    gcongr
  have hdiff : Tendsto (fun n => riemannHeat (s₀ + hn (φ n)) (ζ (φ n)) -
      riemannHeat s₀ (ζ (φ n))) atTop (𝓝 0) := by
    refine squeeze_zero_norm hK ?_
    have := hhφ.const_mul (∫ x, |x| ^ 2 * ‖heatWeight (s₀ + 1) x‖ * Real.exp (1 * |x|))
    rw [mul_zero] at this
    exact this
  have hcont : Tendsto (fun n => riemannHeat s₀ (ζ (φ n))) atTop (𝓝 (riemannHeat s₀ z₁)) :=
    ((differentiable_riemannHeat hs₀pos.le).continuous.tendsto z₁).comp hlim
  have hz₁ : riemannHeat s₀ z₁ = 0 := by
    have h := hdiff.add hcont
    rw [zero_add] at h
    have h0 : (fun n => riemannHeat (s₀ + hn (φ n)) (ζ (φ n)) - riemannHeat s₀ (ζ (φ n)) +
        riemannHeat s₀ (ζ (φ n))) = fun _ => 0 := by
      funext n; rw [sub_add_cancel, hζ0]
    rw [h0] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  -- the limit is on the barrier
  have hz₁bar : 1 / 4 - 2 * s₀ ≤ z₁.im ^ 2 := by
    have h1 : Tendsto (fun n => 1 / 4 - 2 * (s₀ + hn (φ n))) atTop (𝓝 (1 / 4 - 2 * s₀)) := by
      have := ((hhφ.const_add s₀).const_mul 2).const_sub (1 / 4)
      simpa using this
    have h2 : Tendsto (fun n => (ζ (φ n)).im ^ 2) atTop (𝓝 (z₁.im ^ 2)) :=
      ((Complex.continuous_im.tendsto z₁).comp hlim).pow 2
    exact le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall fun n => hζbar (φ n))
  have hz₁im : z₁.im ≠ 0 := by
    intro h0; rw [h0, hs₀bar] at hz₁bar; norm_num at hz₁bar
  have hz₁eq : z₁.im ^ 2 = 1 / 4 - 2 * s₀ :=
    le_antisymm ((riemannHeat_zeros_im_sq_le hs₀pos hz₁).trans
      (max_le le_rfl (by rw [hs₀bar]; norm_num))) hz₁bar
  -- move to the upper half-plane
  set zs : ℂ := if 0 < z₁.im then z₁ else (starRingEnd ℂ) z₁ with hzs
  set w : ℕ → ℂ := fun n => if 0 < z₁.im then ζ (φ n) else (starRingEnd ℂ) (ζ (φ n)) with hw
  have hzs0 : riemannHeat s₀ zs = 0 := by
    rw [hzs]; split_ifs
    · exact hz₁
    · rw [riemannHeat_conj hs₀pos.le, hz₁, map_zero]
  have hzsy : 0 < zs.im := by
    rw [hzs]; split_ifs with h
    · exact h
    · simp only [Complex.conj_im]
      exact neg_pos.mpr (lt_of_le_of_ne (not_lt.mp h) hz₁im)
  have hzsbar : zs.im ^ 2 = 1 / 4 - 2 * s₀ := by
    rw [hzs]; split_ifs
    · exact hz₁eq
    · rw [Complex.conj_im, neg_sq]; exact hz₁eq
  have hwlim : Tendsto w atTop (𝓝 zs) := by
    rw [hw, hzs]; split_ifs
    · exact hlim
    · exact (Complex.continuous_conj.tendsto z₁).comp hlim
  have hw0 : ∀ n, riemannHeat (s₀ + hn (φ n)) (w n) = 0 := by
    intro n; simp only [hw]; split_ifs
    · exact hζ0 _
    · rw [riemannHeat_conj (by linarith [hn_pos (φ n)]), hζ0, map_zero]
  have hwbar : ∀ n, 1 / 4 - 2 * (s₀ + hn (φ n)) ≤ (w n).im ^ 2 := by
    intro n; simp only [hw]; split_ifs
    · exact hζbar _
    · rw [Complex.conj_im, neg_sq]; exact hζbar _
  -- contradiction with the descent of the top zero
  obtain ⟨r, hr, h₁, hh₁, hbelow⟩ := exists_zeros_below_barrier hs₀pos hzs0 hzsy hzsbar
  have hev1 : ∀ᶠ n in atTop, ‖w n - zs‖ ≤ r := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp hwlim).eventually (eventually_le_nhds hr)
    exact this
  have hev2 : ∀ᶠ n in atTop, hn (φ n) ≤ h₁ := hhφ.eventually (eventually_le_nhds hh₁)
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  have := hbelow (hn (φ n)) (hn_pos _) hn2 (w n) hn1 (hw0 n)
  linarith [hwbar n]

/-- For every `t ≥ 1/8` all zeros of `H_t` are real and simple. -/
theorem riemannHeat_zeros_real_simple_of_eighth_le {t : ℝ} (ht : 1 / 8 ≤ t) {z : ℂ}
    (hz : riemannHeat t z = 0) : z.im = 0 ∧ deriv (riemannHeat t) z ≠ 0 :=
  ⟨riemannHeat_zeros_real ht hz,
    deriv_riemannHeat_ne_zero_of_newmanConstant_lt (newmanConstant_lt_eighth.trans_le ht) hz⟩

/-- **Under the Riemann hypothesis every `H_t`, `t > 0`, has only real simple zeros.** -/
theorem riemannHeat_zeros_real_simple_of_riemannHypothesis (hRH : RiemannHypothesis) {t : ℝ}
    (ht : 0 < t) {z : ℂ} (hz : riemannHeat t z = 0) :
    z.im = 0 ∧ deriv (riemannHeat t) z ≠ 0 := by
  have hΛ := riemannHypothesis_iff_newmanConstant_eq_zero.mp hRH
  have hlt : newmanConstant < t := by rw [hΛ]; exact ht
  exact ⟨((mem_realRootedTimes_iff ht.le).mpr hlt.le).2 z hz,
    deriv_riemannHeat_ne_zero_of_newmanConstant_lt hlt hz⟩

/-- **A falsification criterion.** A multiple zero of `H_t` at a single heat time `t > 0` refutes the
Riemann hypothesis. -/
theorem not_riemannHypothesis_of_multiple_zero {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : riemannHeat t z = 0) (hd : deriv (riemannHeat t) z = 0) : ¬ RiemannHypothesis :=
  fun hRH => (riemannHeat_zeros_real_simple_of_riemannHypothesis hRH ht hz).2 hd

end

end RHTower.DeBruijn
