import GaloisForLFunctions.RHTower.Sieve.UnitBlockFrequencyBounds

/-!
# Interior frequencies of the smoothed unit block

Let `X = t/(2πk)` be the stationary point of the phase `Θ_k(x) = 2πkx − t log x`.  When `X` lies
strictly inside the plateau `(N + ¾, N' + ¼)` of the window `φ`, the coefficient `ubFreq k` is the
model integral, rotated:

`‖ubFreq k − X^{-it}·ubJ(t)‖ ≤ (30/π)(16π/t + 1/(N(k₂ − k)) + 1/(N(k − k₁)))`,

with `k₁ = t/(2π(N' + ¼))`, `k₂ = t/(2π(N + ¾))` (`norm_ubFreq_sub_main_le`).

**Proof.**  The dilated model window `ψ(x/X)` agrees with `φ` on `|x − X| ≤ r`,
`r = min(X/8, X − N − ¾, N' + ¼ − X)`, so `φ(x) − ψ(x/X)` vanishes there; on either side the phase
derivative `2πk(x − X)/x` has modulus at least `2πkr/R` and the first-derivative test applies.
The substitution `x = Xy` turns `∫ψ(x/X) x^{-1} e^{iΘ_k}` into `X^{-it}·ubJ(t)`, because
`Θ_k(Xy) = t(y − log y) − t log X`.
-/

open Complex Set MeasureTheory intervalIntegral
open GaloisForLFunctions.HTGeometry
open scoped Real

namespace RHTower.Sieve

noncomputable section

/-- Shrinking an interval integral to the support of the integrand. -/
theorem intervalIntegral_eq_of_vanish {F : ℝ → ℂ} {L a b R : ℝ} (hLa : L ≤ a) (hab : a ≤ b)
    (hbR : b ≤ R) (hF : ContinuousOn F (Icc L R)) (h1 : ∀ x ∈ Icc L a, F x = 0)
    (h2 : ∀ x ∈ Icc b R, F x = 0) : ∫ x in L..R, F x = ∫ x in a..b, F x := by
  have hint : ∀ u v, L ≤ u → u ≤ v → v ≤ R → IntervalIntegrable F volume u v :=
    fun u v hu huv hv => (hF.mono (Icc_subset_Icc hu hv)).intervalIntegrable_of_Icc huv
  rw [← integral_add_adjacent_intervals (hint L a le_rfl hLa (hab.trans hbR))
    (hint a R hLa (hab.trans hbR) le_rfl), ← integral_add_adjacent_intervals
    (hint a b hLa hab hbR) (hint b R (hLa.trans hab) hbR le_rfl)]
  have z1 : ∫ x in L..a, F x = 0 := by
    rw [integral_congr (g := fun _ => (0 : ℂ)) fun x hx => h1 x (by rwa [uIcc_of_le hLa] at hx)]
    simp
  have z2 : ∫ x in b..R, F x = 0 := by
    rw [integral_congr (g := fun _ => (0 : ℂ)) fun x hx => h2 x (by rwa [uIcc_of_le hbR] at hx)]
    simp
  rw [z1, z2]; ring

/-- The dilated model window `ψ(x/X)`, written as a plateau. -/
def ubModelWindowAt (X x : ℝ) : ℝ := smoothPlateau (3 / 4 * X) (5 / 4 * X) (1 / 8 * X) x

theorem ubModelWindowAt_mul {X : ℝ} (hX : 0 < X) (y : ℝ) :
    ubModelWindowAt X (X * y) = ubModelWindow y := by
  rw [ubModelWindowAt, ubModelWindow, ← smoothPlateau_div X hX, mul_div_cancel_left₀ _ hX.ne']

variable {N N' : ℕ}

/-- **The rotated model integral.**  For `X = t/(2πk) > 0`,
`∫_{3X/4}^{5X/4} ψ(x/X) x^{-1} e^{iΘ_k(x)} dx = e^{-it log X}·ubJ(t)`. -/
theorem integral_ubModelWindowAt_eq {t : ℝ} {k : ℤ} (hk : (0 : ℝ) < k) (ht : 0 < t) :
    ∫ x in (3 / 4 * (t / (2 * π * k)))..(5 / 4 * (t / (2 * π * k))),
        ((ubModelWindowAt (t / (2 * π * k)) x / x : ℝ) : ℂ) * Complex.exp ((ubPhase t k x : ℂ) * I) =
      Complex.exp (((-(t * Real.log (t / (2 * π * k)))) : ℝ) * I) * ubJ t := by
  set X := t / (2 * π * k) with hXdef
  have hX : 0 < X := by positivity
  have h2πk : 2 * π * k * X = t := by rw [hXdef]; field_simp
  have hsub := intervalIntegral.integral_comp_mul_left (a := 3 / 4) (b := 5 / 4)
    (fun x => ((ubModelWindowAt X x / x : ℝ) : ℂ) * Complex.exp ((ubPhase t k x : ℂ) * I))
    hX.ne'
  rw [show X * (3 / 4) = 3 / 4 * X by ring, show X * (5 / 4) = 5 / 4 * X by ring] at hsub
  have hXc : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hX.ne'
  rw [eq_inv_smul_iff₀ (by exact_mod_cast hX.ne' : (X : ℝ) ≠ 0)] at hsub
  rw [← hsub, ubJ, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_smul]
  refine integral_congr fun y hy => ?_
  rw [uIcc_of_le (by norm_num)] at hy
  have hy0 : 0 < y := by linarith [hy.1]
  rw [ubModelWindowAt_mul hX, ubPhase, Real.log_mul hX.ne' hy0.ne', Complex.real_smul]
  have hexp : Complex.exp (((2 * π * k * (X * y) - t * (Real.log X + Real.log y)) : ℝ) * I) =
      Complex.exp (((-(t * Real.log X)) : ℝ) * I) *
        Complex.exp (((t * (y - Real.log y)) : ℝ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    have : 2 * π * k * (X * y) = t * y := by rw [← h2πk]; ring
    rw [this]; push_cast; ring
  rw [hexp]
  have hamp : (X : ℂ) * ((ubModelWindow y / (X * y) : ℝ) : ℂ) = ((ubModelWindow y / y : ℝ) : ℂ) := by
    push_cast; field_simp
  calc (X : ℂ) * (((ubModelWindow y / (X * y) : ℝ) : ℂ) *
        (Complex.exp (((-(t * Real.log X)) : ℝ) * I) *
          Complex.exp (((t * (y - Real.log y)) : ℝ) * I)))
      = Complex.exp (((-(t * Real.log X)) : ℝ) * I) * (((X : ℂ) *
          ((ubModelWindow y / (X * y) : ℝ) : ℂ)) *
          Complex.exp (((t * (y - Real.log y)) : ℝ) * I)) := by ring
    _ = _ := by rw [hamp]

/-- `1/min(a, min(b, c)) ≤ 1/a + 1/b + 1/c` for positive reals. -/
theorem one_div_min3_le {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / min a (min b c) ≤ 1 / a + 1 / b + 1 / c := by
  have h1 : 0 < 1 / a := by positivity
  have h2 : 0 < 1 / b := by positivity
  have h3 : 0 < 1 / c := by positivity
  rcases min_choice a (min b c) with h | h <;> rw [h]
  · linarith
  · rcases min_choice b c with h' | h' <;> rw [h'] <;> linarith

private theorem ub_side_const_le {N N' k r : ℝ} (hN : 0 < N) (hk : 0 < k) (hr : 0 < r)
    (hN'0 : 0 ≤ N') (h3 : N' + 1 ≤ 3 * N) :
    2 * ((4 + 2) / (3 / 4 * N * (2 * π * k * r / (5 / 4 * (N' + 1))))) ≤ 30 / (π * (k * r)) := by
  have hN'1 : 0 < N' + 1 := by linarith
  have e : 2 * ((4 + 2) / (3 / 4 * N * (2 * π * k * r / (5 / 4 * (N' + 1))))) =
      10 * (N' + 1) / (N * (π * (k * r))) := by
    field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 < π * (k * r) := by positivity
  nlinarith

/-- The reciprocal of the window radius `r = min(X/8, X − N − ¾, N' + ¼ − X)`, in frequency
coordinates. -/
private theorem ub_interior_conv {t k X N N' r : ℝ} (hk : 0 < k) (ht : 0 < t) (hN : 0 < N)
    (hkX : k * X = t / (2 * π)) (hXlo : N + 3 / 4 < X) (hXhi : X < N' + 1 / 4)
    (hrdef : r = min (X / 8) (min (X - (N + 3 / 4)) ((N' + 1 / 4) - X))) :
    30 / (π * (k * r)) ≤ (30 / π) * (16 * π / t + 1 / (N * (t / (2 * π * (N + 3 / 4)) - k)) +
        1 / (N * (k - t / (2 * π * (N' + 1 / 4))))) := by
  have hX : 0 < X := by linarith
  have hN'0 : 0 < N' + 1 / 4 := by linarith
  have hN'ne : N' + 1 / 4 ≠ 0 := hN'0.ne'
  have hNe : N + 3 / 4 ≠ 0 := by positivity
  have hN'4 : N' * 4 + 1 ≠ 0 := by intro h; linarith
  have hN4 : N * 4 + 3 ≠ 0 := by intro h; linarith
  have hr : 0 < r := hrdef ▸ lt_min (by positivity) (lt_min (by linarith) (by linarith))
  have hmin := one_div_min3_le (a := X / 8) (b := X - (N + 3 / 4)) (c := (N' + 1 / 4) - X)
    (by positivity) (by linarith) (by linarith)
  rw [← hrdef] at hmin
  have hπ : 0 < π := Real.pi_pos
  have hk2 : k < t / (2 * π * (N + 3 / 4)) := by
    rw [lt_div_iff₀ (by positivity)]
    have : k * (N + 3 / 4) < k * X := mul_lt_mul_of_pos_left hXlo hk
    rw [hkX] at this
    rw [lt_div_iff₀ (by positivity)] at this
    linarith
  have hk1 : t / (2 * π * (N' + 1 / 4)) < k := by
    rw [div_lt_iff₀ (by positivity)]
    have : k * X < k * (N' + 1 / 4) := mul_lt_mul_of_pos_left hXhi hk
    rw [hkX, div_lt_iff₀ (by positivity)] at this
    linarith
  have e0 : 1 / (k * r) = (1 / k) * (1 / r) := by rw [one_div_mul_one_div]
  have e1 : (1 / k) * (1 / (X / 8)) = 16 * π / t := by
    rw [one_div_mul_one_div, show k * (X / 8) = t / (2 * π) / 8 by rw [← hkX]; ring]
    field_simp; norm_num
  have hc2 : (N + 3 / 4) * (t / (2 * π * (N + 3 / 4))) = t / (2 * π) := by field_simp
  have hc1 : (N' + 1 / 4) * (t / (2 * π * (N' + 1 / 4))) = t / (2 * π) := by field_simp
  have e2 : (1 / k) * (1 / (X - (N + 3 / 4))) ≤ 1 / (N * (t / (2 * π * (N + 3 / 4)) - k)) := by
    rw [one_div_mul_one_div]
    have hpos : 0 < t / (2 * π * (N + 3 / 4)) - k := by linarith
    refine one_div_le_one_div_of_le (by positivity) ?_
    have hid : k * (X - (N + 3 / 4)) = (N + 3 / 4) * (t / (2 * π * (N + 3 / 4)) - k) := by
      rw [mul_sub, hkX, mul_sub, hc2]; ring
    rw [hid]
    exact mul_le_mul_of_nonneg_right (by linarith) hpos.le
  have e3 : (1 / k) * (1 / ((N' + 1 / 4) - X)) ≤ 1 / (N * (k - t / (2 * π * (N' + 1 / 4)))) := by
    rw [one_div_mul_one_div]
    have hpos : 0 < k - t / (2 * π * (N' + 1 / 4)) := by linarith
    refine one_div_le_one_div_of_le (by positivity) ?_
    have hid : k * ((N' + 1 / 4) - X) = (N' + 1 / 4) * (k - t / (2 * π * (N' + 1 / 4))) := by
      rw [mul_sub, hkX, mul_sub, hc1]; ring
    rw [hid]
    exact mul_le_mul_of_nonneg_right (by linarith) hpos.le
  have hA : 1 / (k * r) ≤ 16 * π / t + 1 / (N * (t / (2 * π * (N + 3 / 4)) - k)) +
      1 / (N * (k - t / (2 * π * (N' + 1 / 4)))) := by
    rw [e0]
    have hk' : 0 ≤ 1 / k := by positivity
    have := mul_le_mul_of_nonneg_left hmin hk'
    rw [mul_add, mul_add] at this
    linarith
  rw [show 30 / (π * (k * r)) = (30 / π) * (1 / (k * r)) by field_simp]
  exact mul_le_mul_of_nonneg_left hA (by positivity)

/-- **Interior frequencies.**  If `t/(2π(N' + ¼)) < k < t/(2π(N + ¾))`, then
`‖ubFreq k − (t/(2πk))^{-it}·ubJ(t)‖ ≤ (30/π)(16π/t + 1/(N(k₂ − k)) + 1/(N(k − k₁)))`. -/
theorem norm_ubFreq_sub_main_le (hN : 1 ≤ N) (hNN' : N < N') (hN' : N' ≤ 2 * N) {t : ℝ}
    (ht : 0 < t) {k : ℤ} (hk1 : t / (2 * π * ((N' : ℝ) + 1 / 4)) < k)
    (hk2 : (k : ℝ) < t / (2 * π * ((N : ℝ) + 3 / 4))) :
    ‖ubFreq N N' t k - Complex.exp (((-(t * Real.log (t / (2 * π * k)))) : ℝ) * I) * ubJ t‖ ≤
      (30 / π) * (16 * π / t + 1 / (N * (t / (2 * π * ((N : ℝ) + 3 / 4)) - k)) +
        1 / (N * (k - t / (2 * π * ((N' : ℝ) + 1 / 4))))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNN'r : (N : ℝ) + 1 ≤ N' := by exact_mod_cast hNN'
  have hN'2 : (N' : ℝ) ≤ 2 * N := by exact_mod_cast hN'
  have hk0 : (0 : ℝ) < k := lt_trans (by positivity) hk1
  obtain ⟨X, hXdef⟩ : ∃ X, X = t / (2 * π * k) := ⟨_, rfl⟩
  rw [← hXdef]
  have hX : 0 < X := by rw [hXdef]; positivity
  have h2πk : 2 * π * k * X = t := by rw [hXdef]; field_simp
  have hkX : (k : ℝ) * X = t / (2 * π) := by rw [hXdef]; field_simp
  -- position of the stationary point
  have hXlo : (N : ℝ) + 3 / 4 < X := by
    rw [hXdef, lt_div_iff₀ (by positivity)]
    rw [lt_div_iff₀ (by positivity)] at hk2; linarith
  have hXhi : X < (N' : ℝ) + 1 / 4 := by
    rw [hXdef, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hk1; linarith
  obtain ⟨r, hrdef⟩ : ∃ r, r = min (X / 8) (min (X - ((N : ℝ) + 3 / 4)) (((N' : ℝ) + 1 / 4) - X)) :=
    ⟨_, rfl⟩
  have hr : 0 < r := hrdef ▸ lt_min (by positivity) (lt_min (by linarith) (by linarith))
  have hr1 : r ≤ X / 8 := hrdef ▸ min_le_left _ _
  have hr2 : r ≤ X - ((N : ℝ) + 3 / 4) := hrdef ▸ le_trans (min_le_right _ _) (min_le_left _ _)
  have hr3 : r ≤ ((N' : ℝ) + 1 / 4) - X := hrdef ▸ le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 3 / 4 * N := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 5 / 4 * ((N' : ℝ) + 1) := ⟨_, rfl⟩
  have hL0 : 0 < L := by rw [hL]; positivity
  have hLN : L ≤ N := by rw [hL]; linarith
  have hRN' : (N' : ℝ) + 1 ≤ R := by rw [hR]; linarith
  have hLX : L ≤ 3 / 4 * X := by linarith
  have hXR : 5 / 4 * X ≤ R := by linarith
  have hLXr : L ≤ X - r := by linarith
  have hXrR : X + r ≤ R := by linarith
  have hpos : ∀ x ∈ Icc L R, 0 < x := fun x hx => hL0.trans_le hx.1
  -- the two windows
  set φ := ubWindow N N' with hφ
  set ψ := ubModelWindowAt X with hψ
  have hφc : Continuous φ := continuous_ubWindow
  have hψc : Continuous ψ := continuous_smoothPlateau
  have hΘc : ContinuousOn (ubPhase t k) (Icc L R) := fun x hx =>
    (hasDerivAt_ubPhase t k (hpos x hx).ne').continuousAt.continuousWithinAt
  have hEc : ContinuousOn (fun x => Complex.exp ((ubPhase t k x : ℂ) * I)) (Icc L R) :=
    Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hΘc).mul continuousOn_const)
  have hampc : ∀ {g : ℝ → ℝ}, Continuous g →
      ContinuousOn (fun x => ((g x / x : ℝ) : ℂ) * Complex.exp ((ubPhase t k x : ℂ) * I))
        (Icc L R) := fun {g} hg =>
    (Complex.continuous_ofReal.comp_continuousOn (hg.continuousOn.div continuousOn_id
      fun x hx => (hpos x hx).ne')).mul hEc
  -- `ubFreq` over `[L, R]`
  have hi : ubFreq N N' t k =
      ∫ x in L..R, ((φ x / x : ℝ) : ℂ) * Complex.exp ((ubPhase t k x : ℂ) * I) := by
    rw [intervalIntegral_eq_of_vanish hLN (by linarith) hRN' (hampc hφc)
      (fun x hx => by rw [hφ, ubWindow_eq_zero_of_le (by linarith [hx.2])]; simp)
      (fun x hx => by rw [hφ, ubWindow_eq_zero_of_ge (by linarith [hx.1])]; simp)]
    rfl
  -- the main term over `[L, R]`
  have hii : Complex.exp (((-(t * Real.log X)) : ℝ) * I) * ubJ t =
      ∫ x in L..R, ((ψ x / x : ℝ) : ℂ) * Complex.exp ((ubPhase t k x : ℂ) * I) := by
    rw [hXdef, ← integral_ubModelWindowAt_eq hk0 ht, ← hXdef]
    refine (intervalIntegral_eq_of_vanish hLX (by linarith) hXR (hampc hψc) ?_ ?_).symm
    · intro x hx
      rw [hψ, ubModelWindowAt, smoothPlateau_eq_zero_of_le (by positivity) hx.2]; simp
    · intro x hx
      rw [hψ, ubModelWindowAt, smoothPlateau_eq_zero_of_ge (by positivity) hx.1]; simp
  set w : ℝ → ℝ := fun x => φ x - ψ x with hw
  have hwc : Continuous w := hφc.sub hψc
  have hdiff : ubFreq N N' t k - Complex.exp (((-(t * Real.log X)) : ℝ) * I) * ubJ t =
      ∫ x in L..R, ((w x / x : ℝ) : ℂ) * Complex.exp ((ubPhase t k x : ℂ) * I) := by
    rw [hi, hii, ← integral_sub ((hampc hφc).intervalIntegrable_of_Icc (by linarith))
      ((hampc hψc).intervalIntegrable_of_Icc (by linarith))]
    refine integral_congr fun x _ => ?_
    simp only [hw]
    push_cast; ring
  -- `w` vanishes around the stationary point
  have hwzero : ∀ x ∈ Icc (X - r) (X + r), w x = 0 := by
    intro x hx
    have h1 : φ x = 1 := ubWindow_eq_one (by linarith [hx.1]) (by linarith [hx.2])
    have h2 : ψ x = 1 := smoothPlateau_eq_one (by positivity) (by linarith [hx.1])
      (by linarith [hx.2])
    simp only [hw, h1, h2, sub_self]
  have hint : ∀ u v, L ≤ u → u ≤ v → v ≤ R → IntervalIntegrable
      (fun x => ((w x / x : ℝ) : ℂ) * Complex.exp ((ubPhase t k x : ℂ) * I)) volume u v :=
    fun u v hu huv hv => ((hampc hwc).mono (Icc_subset_Icc hu hv)).intervalIntegrable_of_Icc huv
  have hmid : ∫ x in (X - r)..(X + r),
      ((w x / x : ℝ) : ℂ) * Complex.exp ((ubPhase t k x : ℂ) * I) = 0 := by
    rw [integral_congr (g := fun _ => (0 : ℂ)) fun x hx => by
      rw [uIcc_of_le (by linarith)] at hx
      simp [hwzero x hx]]
    simp
  -- the two sides
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = 2 * π * k * r / R := ⟨_, rfl⟩
  have hR0 : 0 < R := by rw [hR]; positivity
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hwd : ∀ x, HasDerivAt w (smoothPlateauDeriv ((N : ℝ) + 1 / 4) ((N' : ℝ) + 3 / 4) (1 / 2) x -
      smoothPlateauDeriv (3 / 4 * X) (5 / 4 * X) (1 / 8 * X) x) x :=
    fun x => (hasDerivAt_ubWindow x).sub (hasDerivAt_smoothPlateau x)
  have hwdc : Continuous fun x =>
      smoothPlateauDeriv ((N : ℝ) + 1 / 4) ((N' : ℝ) + 3 / 4) (1 / 2) x -
        smoothPlateauDeriv (3 / 4 * X) (5 / 4 * X) (1 / 8 * X) x :=
    continuous_smoothPlateauDeriv.sub continuous_smoothPlateauDeriv
  have hw1 : ∀ x, |w x| ≤ 1 := by
    intro x
    have a1 := smoothPlateau_nonneg (a := (N : ℝ) + 1 / 4) (b := (N' : ℝ) + 3 / 4)
      (ℓ := 1 / 2) x
    have a2 := smoothPlateau_le_one (a := (N : ℝ) + 1 / 4) (b := (N' : ℝ) + 3 / 4)
      (ℓ := 1 / 2) x
    have b1 := smoothPlateau_nonneg (a := 3 / 4 * X) (b := 5 / 4 * X) (ℓ := 1 / 8 * X) x
    have b2 := smoothPlateau_le_one (a := 3 / 4 * X) (b := 5 / 4 * X) (ℓ := 1 / 8 * X) x
    simp only [hw, hφ, hψ, ubWindow, ubModelWindowAt]
    rw [abs_le]; constructor <;> linarith
  have hW : ∀ u v, u ≤ v → ∫ x in u..v, |smoothPlateauDeriv ((N : ℝ) + 1 / 4) ((N' : ℝ) + 3 / 4)
      (1 / 2) x - smoothPlateauDeriv (3 / 4 * X) (5 / 4 * X) (1 / 8 * X) x| ≤ 4 := by
    intro u v huv
    have e1 := integral_abs_smoothPlateauDeriv_le (a := (N : ℝ) + 1 / 4) (b := (N' : ℝ) + 3 / 4)
      (ℓ := 1 / 2) (by norm_num) huv
    have e2 := integral_abs_smoothPlateauDeriv_le (a := 3 / 4 * X) (b := 5 / 4 * X)
      (ℓ := 1 / 8 * X) (by positivity) huv
    have hc1 := (continuous_smoothPlateauDeriv (a := (N : ℝ) + 1 / 4) (b := (N' : ℝ) + 3 / 4)
      (ℓ := 1 / 2)).abs
    have hc2 := (continuous_smoothPlateauDeriv (a := 3 / 4 * X) (b := 5 / 4 * X)
      (ℓ := 1 / 8 * X)).abs
    have hi12 : IntervalIntegrable (fun x =>
        |smoothPlateauDeriv ((N : ℝ) + 1 / 4) ((N' : ℝ) + 3 / 4) (1 / 2) x| +
          |smoothPlateauDeriv (3 / 4 * X) (5 / 4 * X) (1 / 8 * X) x|) volume u v :=
      (hc1.add hc2).intervalIntegrable u v
    have hmono := integral_mono_on huv (hwdc.abs.intervalIntegrable (μ := volume) u v)
      hi12 fun x _ => abs_sub _ _
    rw [integral_add (hc1.intervalIntegrable (μ := volume) u v)
      (hc2.intervalIntegrable (μ := volume) u v)] at hmono
    linarith
  have hphase : ∀ x, 0 < x → 2 * π * k - t / x = 2 * π * k * (x - X) / x := by
    intro x hx; rw [← h2πk]; field_simp
  have hleft : ‖∫ x in L..(X - r),
      ((w x / x : ℝ) : ℂ) * Complex.exp ((ubPhase t k x : ℂ) * I)‖ ≤ (4 + 2) / (L * lam) := by
    have hsub : Icc L (X - r) ⊆ Icc L R := Icc_subset_Icc le_rfl (by linarith)
    refine norm_integral_div_self_mul_exp_le (Θ' := fun x => 2 * π * k - t / x)
      (Θ'' := fun x => t / x ^ 2) hL0 hLXr hlam0 (fun x _ => hwd x) hwdc.continuousOn
      (fun x _ => hw1 x) (hW _ _ hLXr) ?_ (hwzero _ ⟨le_rfl, by linarith⟩)
      (fun x hx => hasDerivAt_ubPhase t k (hpos x (hsub hx)).ne')
      (fun x hx => hasDerivAt_ubPhaseDeriv t k (hpos x (hsub hx)).ne')
      (continuousOn_const.div (continuousOn_id.pow 2) fun x hx =>
        pow_ne_zero 2 (hpos x (hsub hx)).ne') (fun x _ => by positivity) fun x hx => ?_
    · have h1 : φ L = 0 := ubWindow_eq_zero_of_le (by linarith)
      have h2 : ψ L = 0 := smoothPlateau_eq_zero_of_le (by positivity) hLX
      simp only [hw, h1, h2, sub_self]
    · have hx0 := hpos x (hsub hx)
      have h3 : 0 < 2 * π * (k : ℝ) := by positivity
      have hval : |2 * π * (k : ℝ) - t / x| = 2 * π * k * (X - x) / x := by
        rw [hphase x hx0, abs_div, abs_of_pos hx0, abs_mul, abs_of_pos h3,
          abs_of_nonpos (by linarith [hx.2] : x - X ≤ 0)]
        ring
      show lam ≤ |2 * π * (k : ℝ) - t / x|
      rw [hval, hlam, div_le_div_iff₀ (by positivity) hx0]
      have h1 : r ≤ X - x := by linarith [hx.2]
      have h2 : x ≤ R := by linarith [hx.2]
      have hp := mul_le_mul h1 h2 hx0.le (by linarith)
      have := mul_le_mul_of_nonneg_left hp h3.le
      linarith
  have hright : ‖∫ x in (X + r)..R,
      ((w x / x : ℝ) : ℂ) * Complex.exp ((ubPhase t k x : ℂ) * I)‖ ≤
        (4 + 2) / ((X + r) * lam) := by
    have hsub : Icc (X + r) R ⊆ Icc L R := Icc_subset_Icc (by linarith) le_rfl
    refine norm_integral_div_self_mul_exp_le (Θ' := fun x => 2 * π * k - t / x)
      (Θ'' := fun x => t / x ^ 2) (by linarith) hXrR hlam0 (fun x _ => hwd x)
      hwdc.continuousOn (fun x _ => hw1 x) (hW _ _ hXrR)
      (hwzero _ ⟨by linarith, le_rfl⟩) ?_
      (fun x hx => hasDerivAt_ubPhase t k (hpos x (hsub hx)).ne')
      (fun x hx => hasDerivAt_ubPhaseDeriv t k (hpos x (hsub hx)).ne')
      (continuousOn_const.div (continuousOn_id.pow 2) fun x hx =>
        pow_ne_zero 2 (hpos x (hsub hx)).ne') (fun x _ => by positivity) fun x hx => ?_
    · have h1 : φ R = 0 := ubWindow_eq_zero_of_ge (by linarith)
      have h2 : ψ R = 0 := smoothPlateau_eq_zero_of_ge (by positivity) hXR
      simp only [hw, h1, h2, sub_self]
    · have hx0 := hpos x (hsub hx)
      have h3 : 0 < 2 * π * (k : ℝ) := by positivity
      have hval : |2 * π * (k : ℝ) - t / x| = 2 * π * k * (x - X) / x := by
        rw [hphase x hx0, abs_div, abs_of_pos hx0, abs_mul, abs_of_pos h3,
          abs_of_nonneg (by linarith [hx.1] : 0 ≤ x - X)]
      show lam ≤ |2 * π * (k : ℝ) - t / x|
      rw [hval, hlam, div_le_div_iff₀ (by positivity) hx0]
      have h1 : r ≤ x - X := by linarith [hx.1]
      have hp := mul_le_mul h1 hx.2 hx0.le (by linarith)
      have := mul_le_mul_of_nonneg_left hp h3.le
      linarith
  -- assemble
  have hsplit : ∫ x in L..R, ((w x / x : ℝ) : ℂ) * Complex.exp ((ubPhase t k x : ℂ) * I) =
      (∫ x in L..(X - r), ((w x / x : ℝ) : ℂ) * Complex.exp ((ubPhase t k x : ℂ) * I)) +
      ∫ x in (X + r)..R, ((w x / x : ℝ) : ℂ) * Complex.exp ((ubPhase t k x : ℂ) * I) := by
    have hXrR' : X - r ≤ R := by linarith only [hXrR, hr]
    have hXrXr : X - r ≤ X + r := by linarith only [hr]
    have hLXr' : L ≤ X + r := by linarith only [hLXr, hr]
    have e1 := integral_add_adjacent_intervals (hint L (X - r) le_rfl hLXr hXrR')
      (hint (X - r) R hLXr hXrR' le_rfl)
    have e2 := integral_add_adjacent_intervals (hint (X - r) (X + r) hLXr hXrXr hXrR)
      (hint (X + r) R hLXr' hXrR le_rfl)
    rw [← e1, ← e2, hmid, zero_add]
  have htot : ‖ubFreq N N' t k - Complex.exp (((-(t * Real.log X)) : ℝ) * I) * ubJ t‖ ≤
      30 / (π * (k * r)) := by
    rw [hdiff, hsplit]
    refine le_trans (norm_add_le _ _) (le_trans (add_le_add hleft hright) ?_)
    have hb1 : (4 + 2) / ((X + r) * lam) ≤ (4 + 2) / (L * lam) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_right (by linarith only [hLXr, hr]) hlam0.le)
    have hb2 : 2 * ((4 + 2) / (L * lam)) ≤ 30 / (π * (k * r)) := by
      rw [hlam, hL, hR]
      exact ub_side_const_le hN0 hk0 hr (Nat.cast_nonneg _) (by linarith only [hN'2, hN1])
    linarith only [hb1, hb2]
  refine le_trans htot ?_
  exact ub_interior_conv hk0 ht hN0 hkX hXlo hXhi hrdef

end

end RHTower.Sieve
