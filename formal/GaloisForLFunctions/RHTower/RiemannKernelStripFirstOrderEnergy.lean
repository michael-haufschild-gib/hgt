import GaloisForLFunctions.RHTower.RiemannKernelStripFirstOrderBounds
import GaloisForLFunctions.HTGeometry.FirstOrderTwoRadiusEnergy

/-!
# Degree-one LP-maximality: the energy argument

Let `a > 0` and let `ψ` solve `ψ′ = a(ψ − F)`, where `F` is the real `Ξ` and
`ψ(x) = ∫Φ(u)e^{ixu}du/(1 − iu/a)`. Assume:
* `ψ` vanishes within distance `1` to the left of every large `x`;
* `ψ` vanishes in `[x − r, x]` whenever the counting function `N` of `Ξ` increases by at least `2`
  on `(x − r, x]`;
* the flat set `{t : N(t+h) = N(t)}` has measure `≤ CT/(1 + h log T)^{24}` in `[T, 2T]`;
* the moments `∫_X^{2X}e^{πy/2}F² ≲ X^{9/2}log X` and `∫_X^{2X}e^{πy}F⁴ ≲ X⁸log⁴X` hold.

Then there is a contradiction (`false_of_firstOrder_data`).

Proof. On each dyadic block `[X, 2X]` take `r_s = 3(log X)^{−3/4}` and `r_l = 1`
(`integral_block_le_explicit`). The two-radius Grönwall bound charges the short gaps `r_s²` and
confines the long gaps to a bad set of measure `≲ X(log X)^{−21/4}`. AM–GM with
`λ = X^{7/2}(log X)^{9/2}` against the fourth moment then gives the block energy
`≲ e^{−δX}X^{9/2}(log X)^{−1/2}`. The Abelian dyadic sum (`sum_dyadic_rpow_mul_exp_le`) bounds the
total by `o(δ^{−9/2})`. Plancherel on the line `Im u = π/4 − δ/2` and the flat theta lower bound
give `≳ δ^{−9/2}`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

namespace RHTower.KernelStrip

/-- One dyadic term against the Gamma integral:
`X^{9/2}e^{−δX} ≤ 2^{9/2}∫_{X/2}^X x^{7/2}e^{−δx/2}dx`. -/
theorem rpow_mul_exp_le_integral {X δ : ℝ} (hX : 0 < X) (hδ : 0 < δ) :
    X ^ (9 / 2 : ℝ) * Real.exp (-(δ * X)) ≤
      2 ^ (9 / 2 : ℝ) * ∫ x in X / 2..X, x ^ (7 / 2 - 1 + 1 : ℝ) * Real.exp (-(δ / 2 * x)) := by
  have hX2 : X / 2 ≤ X := by linarith
  have hlow : ∀ x ∈ Icc (X / 2) X, (X / 2) ^ (7 / 2 : ℝ) * Real.exp (-(δ / 2 * X)) ≤
      x ^ (7 / 2 - 1 + 1 : ℝ) * Real.exp (-(δ / 2 * x)) := by
    intro x hx
    have hx0 : 0 ≤ X / 2 := by positivity
    rw [show (7 / 2 - 1 + 1 : ℝ) = 7 / 2 by norm_num]
    apply mul_le_mul (Real.rpow_le_rpow hx0 hx.1 (by norm_num))
      (Real.exp_le_exp.mpr (by nlinarith [hx.2])) (Real.exp_pos _).le
      (Real.rpow_nonneg (by linarith [hx.1]) _)
  have hint := intervalIntegral.integral_mono_on hX2 (intervalIntegrable_const (μ := volume))
    (((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 7 / 2 - 1 + 1)).mul
      (by fun_prop : Continuous fun x : ℝ => Real.exp (-(δ / 2 * x)))).intervalIntegrable
        (μ := volume) _ _) hlow
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  simp only [Pi.mul_apply] at hint
  have hpow : X ^ (9 / 2 : ℝ) = 2 ^ (9 / 2 : ℝ) * ((X - X / 2) * (X / 2) ^ (7 / 2 : ℝ)) := by
    rw [show X - X / 2 = X / 2 by ring, ← Real.rpow_one_add' (by positivity) (by norm_num),
      show (1 : ℝ) + 7 / 2 = 9 / 2 by norm_num, Real.div_rpow hX.le (by norm_num)]
    field_simp
  have hexp : Real.exp (-(δ * X)) ≤ Real.exp (-(δ / 2 * X)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc X ^ (9 / 2 : ℝ) * Real.exp (-(δ * X))
      ≤ X ^ (9 / 2 : ℝ) * Real.exp (-(δ / 2 * X)) := by gcongr
    _ = 2 ^ (9 / 2 : ℝ) * ((X - X / 2) * ((X / 2) ^ (7 / 2 : ℝ) * Real.exp (-(δ / 2 * X)))) := by
        rw [hpow]; ring
    _ ≤ 2 ^ (9 / 2 : ℝ) * ∫ x in X / 2..X, x ^ (7 / 2 - 1 + 1 : ℝ) * Real.exp (-(δ / 2 * x)) := by
        gcongr

/-- **Abelian dyadic sum.** `Σ_{j<J} (2^jX₀)^{9/2}e^{−δ2^jX₀} ≤ 2^{9/2}Γ(9/2)(2/δ)^{9/2}`. -/
theorem sum_dyadic_rpow_mul_exp_le {X₀ δ : ℝ} (hX₀ : 0 < X₀) (hδ : 0 < δ) (J : ℕ) :
    ∑ j ∈ Finset.range J, (2 ^ j * X₀) ^ (9 / 2 : ℝ) * Real.exp (-(δ * (2 ^ j * X₀))) ≤
      2 ^ (9 / 2 : ℝ) * ((1 / (δ / 2)) ^ (9 / 2 : ℝ) * Real.Gamma (9 / 2)) := by
  set f : ℝ → ℝ := fun x => x ^ (7 / 2 - 1 + 1 : ℝ) * Real.exp (-(δ / 2 * x)) with hf
  set a : ℕ → ℝ := fun k => 2 ^ k * X₀ / 2 with ha
  have hfc : Continuous f := by
    rw [hf]
    exact (Real.continuous_rpow_const (by norm_num)).mul (by fun_prop)
  have hterm : ∀ j : ℕ, (2 ^ j * X₀) ^ (9 / 2 : ℝ) * Real.exp (-(δ * (2 ^ j * X₀))) ≤
      2 ^ (9 / 2 : ℝ) * ∫ x in a j..a (j + 1), f x := by
    intro j
    have h := rpow_mul_exp_le_integral (X := 2 ^ j * X₀) (by positivity) hδ
    have e1 : a j = 2 ^ j * X₀ / 2 := rfl
    have e2 : a (j + 1) = 2 ^ j * X₀ := by simp only [ha]; rw [pow_succ]; ring
    rw [e1, e2]; exact h
  have hsum : ∑ j ∈ Finset.range J, ∫ x in a j..a (j + 1), f x = ∫ x in a 0..a J, f x :=
    intervalIntegral.sum_integral_adjacent_intervals fun k _ => hfc.intervalIntegrable _ _
  have ha0 : 0 ≤ a 0 := by simp only [ha]; positivity
  have haJ : a 0 ≤ a J := by
    simp only [ha]
    have : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
    have : (2 : ℝ) ^ 0 = 1 := pow_zero 2
    nlinarith
  have hf0 : ∀ x, 0 ≤ x → 0 ≤ f x := fun x hx => by
    simp only [hf]; exact mul_nonneg (Real.rpow_nonneg hx _) (Real.exp_pos _).le
  have hInt : IntegrableOn f (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 7 / 2 - 1 + 1) (p := 1)
      (b := δ / 2) (by norm_num) le_rfl (by positivity)
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [hf, Real.rpow_one, neg_mul]
  have hle : ∫ x in a 0..a J, f x ≤ ∫ x in Ioi 0, f x := by
    rw [intervalIntegral.integral_of_le haJ]
    refine setIntegral_mono_set hInt ?_ ?_
    · exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => hf0 x (le_of_lt hx))
    · exact Eventually.of_forall fun x hx => lt_of_le_of_lt ha0 hx.1
  have hG : ∫ x in Ioi 0, f x = (1 / (δ / 2)) ^ (9 / 2 : ℝ) * Real.Gamma (9 / 2) := by
    simp only [hf]
    rw [show (7 / 2 - 1 + 1 : ℝ) = 9 / 2 - 1 by norm_num]
    exact Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) (by positivity)
  calc ∑ j ∈ Finset.range J, (2 ^ j * X₀) ^ (9 / 2 : ℝ) * Real.exp (-(δ * (2 ^ j * X₀)))
      ≤ ∑ j ∈ Finset.range J, 2 ^ (9 / 2 : ℝ) * ∫ x in a j..a (j + 1), f x :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = 2 ^ (9 / 2 : ℝ) * ∫ x in a 0..a J, f x := by rw [← Finset.mul_sum, hsum]
    _ ≤ 2 ^ (9 / 2 : ℝ) * ∫ x in Ioi 0, f x := by gcongr
    _ = _ := by rw [hG]


open GaloisForLFunctions.HTGeometry in
/-- **One dyadic block.** On `[X, 2X]` the first-order preimage `ψ` (with `ψ′ = a(ψ − F)`) has
weighted energy at most `K e^{δ}e^{−δX}(r_s²·M₂ + r_l²((λ/2)·4(r_s+r_l)/r_s·E_b + M₄/(2λ)))`, where
`M₂, M₄` bound the second and fourth moments of `F` on `[X/2, 2X]` and `E_b` bounds the flat mass
of the counting function near the block. -/
theorem integral_block_le {a : ℝ} (ha : 0 < a) {ψ F : ℝ → ℝ} {N : ℝ → ℤ} (hN : Monotone N)
    (hF : Continuous F) (hode : ∀ t, HasDerivAt ψ (a * (ψ t - F t)) t)
    {X rs rl δ lam M2 M4 Eb : ℝ} (hX : 2 ≤ X) (hrs : 0 < rs) (hrsl : rs ≤ rl) (hrl1 : rl ≤ 1)
    (hδ : 0 < δ) (hδ' : δ ≤ π / 2) (hlam : 0 < lam)
    (hlong : ∀ x ∈ Icc X (2 * X), ∃ q ∈ Icc (x - rl) x, ψ q = 0)
    (hshort : ∀ x ∈ Icc X (2 * X), 2 ≤ N x - N (x - rs) → ∃ q ∈ Icc (x - rs) x, ψ q = 0)
    (h2 : ∫ y in X / 2..2 * X, Real.exp (π / 2 * y) * F y ^ 2 ≤ M2)
    (h4 : ∫ y in X / 2..2 * X, Real.exp (π * y) * F y ^ 4 ≤ M4)
    (hE : ∫ t in (X / 2 - rs)..(2 * X + rl),
      {t : ℝ | N (t + rs / 4) = N t}.indicator (fun _ => (1 : ℝ)) t ≤ Eb) :
    ∫ x in X..2 * X, Real.exp ((π / 2 - δ) * x) * ψ x ^ 2 ≤
      a ^ 2 * Real.exp (2 * a) * Real.exp (π / 2) * (Real.exp δ * Real.exp (-(δ * X))) *
        (rs ^ 2 * M2 + rl ^ 2 * (lam / 2 * (4 * (rs + rl) / rs * Eb) + M4 / (2 * lam))) := by
  set β : ℝ := π / 2 - δ with hβ_def
  have hβ : 0 ≤ β := by rw [hβ_def]; linarith
  set E : Set ℝ := {t : ℝ | N (t + rs / 4) = N t} with hE_def
  have hEm : MeasurableSet E := measurableSet_flat hN _
  set m : ℝ → ℝ := fun y => ∫ t in (y - rs)..(y + rl), E.indicator (fun _ => (1 : ℝ)) t with hm
  set B : Set ℝ := {y : ℝ | rs / 4 ≤ m y} with hB_def
  have hBm : MeasurableSet B :=
    (isClosed_le continuous_const (continuous_integral_indicator_window hEm rs rl)).measurableSet
  set G : Set ℝ := {x : ℝ | 2 ≤ N x - N (x - rs)} with hG_def
  have hXY : X ≤ 2 * X := by linarith
  have hGz : ∀ x ∈ Icc X (2 * X), x ∈ G → ∃ q ∈ Icc (x - rs) x, ψ q = 0 :=
    fun x hx hxG => hshort x hx hxG
  have hBc : ∀ x ∈ Icc X (2 * X), x ∉ G → ∀ y ∈ Icc (x - rl) x, y ∈ B := by
    intro x hx hxG y hy
    have hle : N x - N (x - rs) ≤ 1 := by
      simp only [hG_def, Set.mem_setOf_eq, not_le] at hxG; omega
    exact quarter_le_integral_flat hN hrs hle (by linarith [hy.2]) (by linarith [hy.1])
  have hM := integral_exp_mul_sq_le_two_radius (β := β) hode hF hβ hrs.le hrsl hXY hBm hGz hlong hBc
  -- constants
  have hK : a ^ 2 * Real.exp (2 * |a| * rl) * Real.exp (β * rl) ≤
      a ^ 2 * Real.exp (2 * a) * Real.exp (π / 2) := by
    rw [abs_of_pos ha]
    have e1 : Real.exp (2 * a * rl) ≤ Real.exp (2 * a) := Real.exp_le_exp.mpr (by nlinarith)
    have e2 : Real.exp (β * rl) ≤ Real.exp (π / 2) := Real.exp_le_exp.mpr (by
      have : β * rl ≤ β * 1 := mul_le_mul_of_nonneg_left hrl1 hβ
      rw [hβ_def] at this ⊢; nlinarith)
    gcongr
  -- exponential factor on `[X − r_l, 2X]`
  have hexpw : ∀ y, X - rl ≤ y → Real.exp (β * y) ≤
      Real.exp δ * Real.exp (-(δ * X)) * Real.exp (π / 2 * y) := by
    intro y hy
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hβ_def]; nlinarith
  set W : ℝ := Real.exp δ * Real.exp (-(δ * X)) with hW_def
  have hW : 0 < W := by positivity
  have hXl : X / 2 ≤ X - rl := by linarith
  have hc2 : Continuous fun y => Real.exp (π / 2 * y) * F y ^ 2 := by fun_prop
  have hc4 : Continuous fun y => Real.exp (π * y) * F y ^ 4 := by fun_prop
  -- short term
  have hshortI : ∫ y in X - rl..2 * X, Real.exp (β * y) * F y ^ 2 ≤ W * M2 := by
    calc ∫ y in X - rl..2 * X, Real.exp (β * y) * F y ^ 2
        ≤ ∫ y in X - rl..2 * X, W * (Real.exp (π / 2 * y) * F y ^ 2) := by
          refine intervalIntegral.integral_mono_on (by linarith)
            ((by fun_prop : Continuous fun y => Real.exp (β * y) * F y ^ 2).intervalIntegrable _ _)
            ((hc2.const_mul W).intervalIntegrable _ _) fun y hy => ?_
          have := hexpw y hy.1
          calc Real.exp (β * y) * F y ^ 2 ≤ (W * Real.exp (π / 2 * y)) * F y ^ 2 := by
                gcongr
            _ = W * (Real.exp (π / 2 * y) * F y ^ 2) := by ring
      _ = W * ∫ y in X - rl..2 * X, Real.exp (π / 2 * y) * F y ^ 2 :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ W * ∫ y in X / 2..2 * X, Real.exp (π / 2 * y) * F y ^ 2 := by
          gcongr
          exact intervalIntegral.integral_mono_interval hXl (by linarith) le_rfl
            (Eventually.of_forall fun y => by positivity) (hc2.intervalIntegrable _ _)
      _ ≤ W * M2 := by gcongr
  -- long term
  have hBi : ∀ u v, IntervalIntegrable (B.indicator fun _ => (1 : ℝ)) volume u v := fun u v =>
    (intervalIntegrable_const (μ := volume) (c := (1 : ℝ))).mono_fun'
      ((measurable_const.indicator hBm).aestronglyMeasurable)
      (Eventually.of_forall fun t => by
        show ‖B.indicator (fun _ => (1 : ℝ)) t‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) t)]
        exact Set.indicator_le_self' (fun _ _ => zero_le_one) t)
  have hBbad := integral_indicator_bad_le hEm (rl := rl) (X := X / 2) (Y := 2 * X) hrs
    (by linarith) (by linarith)
  have hBmass : ∫ y in X / 2..2 * X, B.indicator (fun _ => (1 : ℝ)) y ≤ 4 * (rs + rl) / rs * Eb := by
    have h1 : rs / 4 * ∫ y in X / 2..2 * X, B.indicator (fun _ => (1 : ℝ)) y ≤ (rs + rl) * Eb := by
      have := mul_le_mul_of_nonneg_left hE (by linarith : (0 : ℝ) ≤ rs + rl)
      exact hBbad.trans this
    rw [show 4 * (rs + rl) / rs * Eb = ((rs + rl) * Eb) / (rs / 4) by field_simp,
      le_div_iff₀ (by positivity)]
    linarith [h1]
  have hlongI : ∫ y in X - rl..2 * X, B.indicator (fun y => Real.exp (β * y) * F y ^ 2) y ≤
      W * (lam / 2 * (4 * (rs + rl) / rs * Eb) + M4 / (2 * lam)) := by
    have hpt : ∀ y ∈ Icc (X - rl) (2 * X), B.indicator (fun y => Real.exp (β * y) * F y ^ 2) y ≤
        W * (lam / 2 * B.indicator (fun _ => (1 : ℝ)) y + (Real.exp (π * y) * F y ^ 4) / (2 * lam)) := by
      intro y hy
      have hle : B.indicator (fun y => Real.exp (β * y) * F y ^ 2) y ≤
          W * B.indicator (fun y => Real.exp (π / 2 * y) * F y ^ 2) y := by
        by_cases hyB : y ∈ B
        · rw [Set.indicator_of_mem hyB, Set.indicator_of_mem hyB]
          have := hexpw y hy.1
          calc Real.exp (β * y) * F y ^ 2 ≤ (W * Real.exp (π / 2 * y)) * F y ^ 2 := by gcongr
            _ = W * (Real.exp (π / 2 * y) * F y ^ 2) := by ring
        · rw [Set.indicator_of_notMem hyB, Set.indicator_of_notMem hyB, mul_zero]
      have ham := indicator_mul_le_amgm (B := B) (H := fun y => Real.exp (π / 2 * y) * F y ^ 2)
        hlam y
      have hsq : (Real.exp (π / 2 * y) * F y ^ 2) ^ 2 = Real.exp (π * y) * F y ^ 4 := by
        rw [mul_pow, ← Real.exp_nat_mul]; congr 1 <;> ring_nf
      simp only [hsq] at ham
      calc B.indicator (fun y => Real.exp (β * y) * F y ^ 2) y
          ≤ W * B.indicator (fun y => Real.exp (π / 2 * y) * F y ^ 2) y := hle
        _ ≤ W * (lam / 2 * B.indicator (fun _ => (1 : ℝ)) y +
              (Real.exp (π * y) * F y ^ 4) / (2 * lam)) := by gcongr
    have hHBi : IntervalIntegrable (B.indicator fun y => Real.exp (β * y) * F y ^ 2) volume
        (X - rl) (2 * X) :=
      ((by fun_prop : Continuous fun y => Real.exp (β * y) * F y ^ 2).intervalIntegrable _ _).mono_fun'
        ((((by fun_prop : Continuous fun y => Real.exp (β * y) * F y ^ 2)).measurable.indicator
          hBm).aestronglyMeasurable)
        (Eventually.of_forall fun t => by
          show ‖B.indicator (fun y => Real.exp (β * y) * F y ^ 2) t‖ ≤ Real.exp (β * t) * F t ^ 2
          rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun y _ => by positivity) t)]
          exact Set.indicator_le_self' (fun y _ => by positivity) t)
    have hR : IntervalIntegrable (fun y => W * (lam / 2 * B.indicator (fun _ => (1 : ℝ)) y +
        (Real.exp (π * y) * F y ^ 4) / (2 * lam))) volume (X - rl) (2 * X) :=
      (((hBi _ _).const_mul _).add ((hc4.div_const _).intervalIntegrable _ _)).const_mul _
    calc ∫ y in X - rl..2 * X, B.indicator (fun y => Real.exp (β * y) * F y ^ 2) y
        ≤ ∫ y in X - rl..2 * X, W * (lam / 2 * B.indicator (fun _ => (1 : ℝ)) y +
            (Real.exp (π * y) * F y ^ 4) / (2 * lam)) :=
          intervalIntegral.integral_mono_on (by linarith) hHBi hR hpt
      _ = W * (lam / 2 * (∫ y in X - rl..2 * X, B.indicator (fun _ => (1 : ℝ)) y) +
            (∫ y in X - rl..2 * X, Real.exp (π * y) * F y ^ 4) / (2 * lam)) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
            ((hBi _ _).const_mul _) ((hc4.div_const _).intervalIntegrable _ _),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
      _ ≤ W * (lam / 2 * (4 * (rs + rl) / rs * Eb) + M4 / (2 * lam)) := by
          have hB1 : ∫ y in X - rl..2 * X, B.indicator (fun _ => (1 : ℝ)) y ≤
              ∫ y in X / 2..2 * X, B.indicator (fun _ => (1 : ℝ)) y :=
            intervalIntegral.integral_mono_interval hXl (by linarith) le_rfl
              (Eventually.of_forall fun y => Set.indicator_nonneg (fun _ _ => zero_le_one) y)
              (hBi _ _)
          have hB4 : ∫ y in X - rl..2 * X, Real.exp (π * y) * F y ^ 4 ≤
              ∫ y in X / 2..2 * X, Real.exp (π * y) * F y ^ 4 :=
            intervalIntegral.integral_mono_interval hXl (by linarith) le_rfl
              (Eventually.of_forall fun y => by positivity) (hc4.intervalIntegrable _ _)
          gcongr
          · exact hB1.trans hBmass
          · exact hB4.trans h4
  have hint0 : 0 ≤ ∫ y in X - rl..2 * X, Real.exp (β * y) * F y ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun y _ => by positivity
  have hint1 : 0 ≤ ∫ y in X - rl..2 * X, B.indicator (fun y => Real.exp (β * y) * F y ^ 2) y :=
    intervalIntegral.integral_nonneg (by linarith) fun y _ =>
      Set.indicator_nonneg (fun y _ => by positivity) y
  calc ∫ x in X..2 * X, Real.exp ((π / 2 - δ) * x) * ψ x ^ 2
      ≤ a ^ 2 * Real.exp (2 * |a| * rl) * Real.exp (β * rl) *
          (rs ^ 2 * (∫ y in X - rl..2 * X, Real.exp (β * y) * F y ^ 2) +
            rl ^ 2 * ∫ y in X - rl..2 * X, B.indicator (fun y => Real.exp (β * y) * F y ^ 2) y) := hM
    _ ≤ a ^ 2 * Real.exp (2 * a) * Real.exp (π / 2) *
          (rs ^ 2 * (W * M2) + rl ^ 2 * (W * (lam / 2 * (4 * (rs + rl) / rs * Eb) +
            M4 / (2 * lam)))) := by
        gcongr
    _ = _ := by rw [hW_def]; ring


open GaloisForLFunctions.HTGeometry in
/-- The flat mass near a block from a large-gap tail bound with exponent `24`. -/
theorem flat_mass_near_block_le {N : ℝ → ℤ} (hN : Monotone N) {C T₀ : ℝ} (hC : 0 ≤ C)
    (hLGT : ∀ T ≥ T₀, ∀ h > 0, volume.real ({t : ℝ | N (t + h) = N t} ∩ Icc T (2 * T)) ≤
      C * T / (1 + h * Real.log T) ^ 24)
    {X h : ℝ} (hX : max 16 (4 * T₀) ≤ X) (hh : 0 < h) :
    ∫ t in (X / 2 - 1)..(2 * X + 1), {t : ℝ | N (t + h) = N t}.indicator (fun _ => (1 : ℝ)) t ≤
      4 * C * X * (2 / (h * Real.log X)) ^ 24 := by
  set E : Set ℝ := {t : ℝ | N (t + h) = N t} with hE_def
  have hEm : MeasurableSet E := measurableSet_flat hN h
  have hX16 : 16 ≤ X := le_trans (le_max_left _ _) hX
  have hXT : 4 * T₀ ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  -- `log T ≥ log X / 2` for `T ≥ X/4`
  have hlogT : ∀ T, X / 4 ≤ T → Real.log X / 2 ≤ Real.log T := by
    intro T hT
    have h4 : Real.log 4 ≤ Real.log X / 2 := by
      have : Real.log 16 ≤ Real.log X := Real.log_le_log (by norm_num) hX16
      have h16 : Real.log 16 = 2 * Real.log 4 := by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith
    have : Real.log (X / 4) ≤ Real.log T := Real.log_le_log (by positivity) hT
    rw [Real.log_div hX0.ne' (by norm_num)] at this
    linarith
  have hterm : ∀ T, X / 4 ≤ T → T₀ ≤ T → volume.real (E ∩ Icc T (2 * T)) ≤
      C * T * (2 / (h * Real.log X)) ^ 24 := by
    intro T hT hT0
    have hb := hLGT T hT0 h hh
    have hlt := hlogT T hT
    have hpos : 0 < h * Real.log X / 2 := by positivity
    have hle : (h * Real.log X / 2) ^ 24 ≤ (1 + h * Real.log T) ^ 24 := by
      apply pow_le_pow_left₀ hpos.le
      nlinarith
    have hT0' : 0 ≤ T := by linarith
    calc volume.real (E ∩ Icc T (2 * T)) ≤ C * T / (1 + h * Real.log T) ^ 24 := hb
      _ ≤ C * T / (h * Real.log X / 2) ^ 24 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) hle
      _ = C * T * (2 / (h * Real.log X)) ^ 24 := by
          rw [div_eq_mul_inv, ← inv_pow, inv_div]
  -- the four dyadic blocks cover `[X/2 − 1, 2X + 1]`
  have hcover : E ∩ Ioc (X / 2 - 1) (2 * X + 1) ⊆
      (E ∩ Icc (X / 4) (2 * (X / 4))) ∪ (E ∩ Icc (X / 2) (2 * (X / 2))) ∪
        (E ∩ Icc X (2 * X)) ∪ (E ∩ Icc (2 * X) (2 * (2 * X))) := by
    intro t ⟨htE, ht⟩
    have h1 : X / 4 ≤ t := by linarith [ht.1]
    have h2 : t ≤ 2 * (2 * X) := by linarith [ht.2]
    by_cases a1 : t ≤ 2 * (X / 4)
    · exact Or.inl (Or.inl (Or.inl ⟨htE, h1, a1⟩))
    by_cases a2 : t ≤ 2 * (X / 2)
    · exact Or.inl (Or.inl (Or.inr ⟨htE, by linarith, a2⟩))
    by_cases a3 : t ≤ 2 * X
    · exact Or.inl (Or.inr ⟨htE, by linarith, a3⟩)
    · exact Or.inr ⟨htE, by linarith, h2⟩
  have hab : X / 2 - 1 ≤ 2 * X + 1 := by linarith
  have hint : ∫ t in (X / 2 - 1)..(2 * X + 1), E.indicator (fun _ => (1 : ℝ)) t =
      volume.real (E ∩ Ioc (X / 2 - 1) (2 * X + 1)) := by
    rw [intervalIntegral.integral_of_le hab, integral_indicator_const _ hEm, smul_eq_mul, mul_one,
      measureReal_restrict_apply hEm]
  rw [hint]
  have hfin : ∀ u v : ℝ, volume (E ∩ Icc u v) ≠ ⊤ := fun u v =>
    measure_ne_top_of_subset Set.inter_subset_right (by simp)
  calc volume.real (E ∩ Ioc (X / 2 - 1) (2 * X + 1))
      ≤ volume.real ((E ∩ Icc (X / 4) (2 * (X / 4))) ∪ (E ∩ Icc (X / 2) (2 * (X / 2))) ∪
          (E ∩ Icc X (2 * X)) ∪ (E ∩ Icc (2 * X) (2 * (2 * X)))) :=
        measureReal_mono hcover (by
          refine measure_union_ne_top (measure_union_ne_top (measure_union_ne_top ?_ ?_) ?_) ?_ <;>
            exact hfin _ _)
    _ ≤ volume.real (E ∩ Icc (X / 4) (2 * (X / 4))) + volume.real (E ∩ Icc (X / 2) (2 * (X / 2))) +
          volume.real (E ∩ Icc X (2 * X)) + volume.real (E ∩ Icc (2 * X) (2 * (2 * X))) := by
        refine (measureReal_union_le _ _).trans ?_
        gcongr
        refine (measureReal_union_le _ _).trans ?_
        gcongr
        exact measureReal_union_le _ _
    _ ≤ C * (X / 4) * (2 / (h * Real.log X)) ^ 24 + C * (X / 2) * (2 / (h * Real.log X)) ^ 24 +
          C * X * (2 / (h * Real.log X)) ^ 24 + C * (2 * X) * (2 / (h * Real.log X)) ^ 24 := by
        gcongr
        · exact hterm _ le_rfl (by linarith)
        · exact hterm _ (by linarith) (by linarith)
        · exact hterm _ (by linarith) (by linarith)
        · exact hterm _ (by linarith) (by linarith)
    _ ≤ 4 * C * X * (2 / (h * Real.log X)) ^ 24 := by
        have : 0 ≤ C * X * (2 / (h * Real.log X)) ^ 24 := by positivity
        nlinarith


/-- The explicit algebra of one block: with `u⁴ = log X`, `r_s = 3/u³`, `h = r_s/4`, `r_l = 1`,
`λ = X^{7/2}u^{18}`, the block bound is at most `X^{9/2}(18C₂ + 2^{28}C(8/3)^{24} + C₄)/u²`. -/
theorem block_algebra {X u C C₂ C₄ : ℝ} (hX : 0 < X) (hu : 2 ≤ u) (hC : 0 ≤ C)
    (hLu : Real.log X = u ^ 4) :
    (3 / u ^ 3) ^ 2 * (2 * C₂ * X ^ (9 / 2 : ℝ) * Real.log X) +
        1 ^ 2 * (X ^ (7 / 2 : ℝ) * u ^ 18 / 2 * (4 * (3 / u ^ 3 + 1) / (3 / u ^ 3) *
          (4 * C * X * (2 / (3 / u ^ 3 / 4 * Real.log X)) ^ 24)) +
          2 * C₄ * X ^ (8 : ℝ) * Real.log X ^ 4 / (2 * (X ^ (7 / 2 : ℝ) * u ^ 18))) ≤
      X ^ (9 / 2 : ℝ) * ((18 * C₂ + 2 ^ 28 * C * (8 / 3) ^ 24 + C₄) / u ^ 2) := by
  have hu0 : 0 < u := by linarith
  have hX72 : 0 < X ^ (7 / 2 : ℝ) := Real.rpow_pos_of_pos hX _
  have hX92 : X ^ (9 / 2 : ℝ) = X ^ (7 / 2 : ℝ) * X := by
    rw [show (9 / 2 : ℝ) = 7 / 2 + 1 by norm_num, Real.rpow_add hX, Real.rpow_one]
  have hX8 : X ^ (8 : ℝ) = X ^ (9 / 2 : ℝ) * X ^ (7 / 2 : ℝ) := by
    rw [← Real.rpow_add hX]; norm_num
  rw [hLu]
  -- term 1
  have t1 : (3 / u ^ 3) ^ 2 * (2 * C₂ * X ^ (9 / 2 : ℝ) * u ^ 4) =
      X ^ (9 / 2 : ℝ) * (18 * C₂ / u ^ 2) := by
    field_simp; ring
  -- term 2
  have h2 : 2 / (3 / u ^ 3 / 4 * u ^ 4) = 8 / (3 * u) := by field_simp; ring
  have hrs : 4 * (3 / u ^ 3 + 1) / (3 / u ^ 3) ≤ 8 * u ^ 3 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (3 : ℝ) ≤ u ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hu 3]
    field_simp
    nlinarith [pow_pos hu0 3]
  have t2 : X ^ (7 / 2 : ℝ) * u ^ 18 / 2 * (4 * (3 / u ^ 3 + 1) / (3 / u ^ 3) *
      (4 * C * X * (2 / (3 / u ^ 3 / 4 * u ^ 4)) ^ 24)) ≤
      X ^ (9 / 2 : ℝ) * (2 ^ 28 * C * (8 / 3) ^ 24 / u ^ 2) := by
    rw [h2]
    have hE0 : 0 ≤ 4 * C * X * (8 / (3 * u)) ^ 24 := by positivity
    calc X ^ (7 / 2 : ℝ) * u ^ 18 / 2 * (4 * (3 / u ^ 3 + 1) / (3 / u ^ 3) *
          (4 * C * X * (8 / (3 * u)) ^ 24))
        ≤ X ^ (7 / 2 : ℝ) * u ^ 18 / 2 * (8 * u ^ 3 / 3 * (4 * C * X * (8 / (3 * u)) ^ 24)) := by
          gcongr
      _ = X ^ (9 / 2 : ℝ) * (16 / 3 * C * (8 / 3) ^ 24 / u ^ 3) := by
          rw [hX92, div_pow, mul_pow]; field_simp; ring
      _ ≤ X ^ (9 / 2 : ℝ) * (2 ^ 28 * C * (8 / 3) ^ 24 / u ^ 2) := by
          gcongr ?_ * ?_
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have : u ^ 2 ≤ u ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
          have h8 : (0 : ℝ) ≤ C * (8 / 3) ^ 24 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left this h8]
  -- term 3
  have t3 : 2 * C₄ * X ^ (8 : ℝ) * (u ^ 4) ^ 4 / (2 * (X ^ (7 / 2 : ℝ) * u ^ 18)) =
      X ^ (9 / 2 : ℝ) * (C₄ / u ^ 2) := by
    rw [hX8]; field_simp
  rw [t1, t3, one_pow, one_mul]
  have : X ^ (9 / 2 : ℝ) * (18 * C₂ / u ^ 2) + (X ^ (9 / 2 : ℝ) * (2 ^ 28 * C * (8 / 3) ^ 24 / u ^ 2) +
      X ^ (9 / 2 : ℝ) * (C₄ / u ^ 2)) =
      X ^ (9 / 2 : ℝ) * ((18 * C₂ + 2 ^ 28 * C * (8 / 3) ^ 24 + C₄) / u ^ 2) := by ring
  linarith [t2]


/-- `u = (log X)^{1/4}` satisfies `u⁴ = log X`. -/
theorem rpow_quarter_pow_four {L : ℝ} (hL : 0 ≤ L) : (L ^ (1 / 4 : ℝ)) ^ 4 = L := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL]; norm_num

/-- **One block, explicit.** For `X ≥ X₃` the dyadic block `[X, 2X]` carries weighted energy at most
`K₁e^{δ}e^{−δX}X^{9/2}·A/u²`, `u = (log X)^{1/4}`. -/
theorem integral_block_le_explicit {a : ℝ} (ha : 0 < a) {ψ F : ℝ → ℝ} {N : ℝ → ℤ}
    (hN : Monotone N) (hF : Continuous F) (hode : ∀ t, HasDerivAt ψ (a * (ψ t - F t)) t)
    {x₀ : ℝ} (hlong : ∀ x ≥ x₀, ∃ q ∈ Icc (x - 1) x, ψ q = 0)
    (hshort : ∀ x ≥ x₀, ∀ r > 0, 2 ≤ N x - N (x - r) → ∃ q ∈ Icc (x - r) x, ψ q = 0)
    {C T₀ : ℝ} (hC : 0 ≤ C) (hLGT : ∀ T ≥ T₀, ∀ h > 0,
      volume.real ({t : ℝ | N (t + h) = N t} ∩ Icc T (2 * T)) ≤ C * T / (1 + h * Real.log T) ^ 24)
    {C₂ : ℝ} (hC₂ : 0 ≤ C₂) (h2 : ∀ X ≥ 2,
      ∫ y in X..2 * X, Real.exp (π / 2 * y) * F y ^ 2 ≤ C₂ * X ^ (9 / 2 : ℝ) * Real.log X)
    {C₄ : ℝ} (hC₄ : 0 ≤ C₄) (h4 : ∀ X ≥ 2,
      ∫ y in X..2 * X, Real.exp (π * y) * F y ^ 4 ≤ C₄ * X ^ (8 : ℝ) * Real.log X ^ 4)
    {X δ : ℝ} (hX : max (max 16 (4 * T₀)) (max x₀ (Real.exp 16)) ≤ X) (hδ : 0 < δ)
    (hδ' : δ ≤ π / 2) :
    ∫ x in X..2 * X, Real.exp ((π / 2 - δ) * x) * ψ x ^ 2 ≤
      a ^ 2 * Real.exp (2 * a) * Real.exp (π / 2) * (Real.exp δ * Real.exp (-(δ * X))) *
        (X ^ (9 / 2 : ℝ) * ((18 * C₂ + 2 ^ 28 * C * (8 / 3) ^ 24 + C₄) /
          (Real.log X ^ (1 / 4 : ℝ)) ^ 2)) := by
  have hX16 : 16 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXx₀ : x₀ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXe : Real.exp 16 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hX0 : 0 < X := by linarith
  have hlog16 : 16 ≤ Real.log X := by
    have := Real.log_le_log (Real.exp_pos 16) hXe; rwa [Real.log_exp] at this
  set u : ℝ := Real.log X ^ (1 / 4 : ℝ) with hu_def
  have hLu : Real.log X = u ^ 4 := (rpow_quarter_pow_four (by linarith)).symm
  have hu2 : 2 ≤ u := by
    by_contra hcon
    push Not at hcon
    have hu0 : 0 ≤ u := Real.rpow_nonneg (by linarith) _
    have : u ^ 4 < 2 ^ 4 := pow_lt_pow_left₀ hcon hu0 (by norm_num)
    rw [← hLu] at this; norm_num at this; linarith
  set rs : ℝ := 3 / u ^ 3 with hrs_def
  have hrs0 : 0 < rs := by positivity
  have hrs1 : rs ≤ 1 := by
    rw [hrs_def, div_le_one (by positivity)]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hu2 3]
  -- moments on `[X/2, 2X]`
  have hX2 : 2 ≤ X / 2 := by linarith
  have hlogle : Real.log (X / 2) ≤ Real.log X := Real.log_le_log (by positivity) (by linarith)
  have hlog0 : 0 ≤ Real.log (X / 2) := Real.log_nonneg (by linarith)
  have hpow92 : (X / 2) ^ (9 / 2 : ℝ) ≤ X ^ (9 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have hpow8 : (X / 2) ^ (8 : ℝ) ≤ X ^ (8 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have hM2 : ∫ y in X / 2..2 * X, Real.exp (π / 2 * y) * F y ^ 2 ≤
      2 * C₂ * X ^ (9 / 2 : ℝ) * Real.log X := by
    have hc : Continuous fun y => Real.exp (π / 2 * y) * F y ^ 2 := by fun_prop
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := X) (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
    have a1 := h2 (X / 2) hX2
    have a2 := h2 X (by linarith)
    rw [show 2 * (X / 2) = X by ring] at a1
    have : C₂ * (X / 2) ^ (9 / 2 : ℝ) * Real.log (X / 2) ≤ C₂ * X ^ (9 / 2 : ℝ) * Real.log X := by
      gcongr
    linarith
  have hM4 : ∫ y in X / 2..2 * X, Real.exp (π * y) * F y ^ 4 ≤
      2 * C₄ * X ^ (8 : ℝ) * Real.log X ^ 4 := by
    have hc : Continuous fun y => Real.exp (π * y) * F y ^ 4 := by fun_prop
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := X) (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
    have a1 := h4 (X / 2) hX2
    have a2 := h4 X (by linarith)
    rw [show 2 * (X / 2) = X by ring] at a1
    have : C₄ * (X / 2) ^ (8 : ℝ) * Real.log (X / 2) ^ 4 ≤ C₄ * X ^ (8 : ℝ) * Real.log X ^ 4 := by
      gcongr
    linarith
  -- flat mass
  have hXT : max 16 (4 * T₀) ≤ X := le_trans (le_max_left _ _) hX
  have hflat := flat_mass_near_block_le hN hC hLGT hXT (h := rs / 4) (by positivity)
  have hEb : ∫ t in (X / 2 - rs)..(2 * X + 1),
      {t : ℝ | N (t + rs / 4) = N t}.indicator (fun _ => (1 : ℝ)) t ≤
      4 * C * X * (2 / (rs / 4 * Real.log X)) ^ 24 := by
    refine le_trans ?_ hflat
    have hEm : MeasurableSet {t : ℝ | N (t + rs / 4) = N t} :=
      GaloisForLFunctions.HTGeometry.measurableSet_flat hN _
    refine intervalIntegral.integral_mono_interval (by linarith) (by linarith) le_rfl
      (Eventually.of_forall fun t => Set.indicator_nonneg (fun _ _ => zero_le_one) t) ?_
    exact (intervalIntegrable_const (μ := volume) (c := (1 : ℝ))).mono_fun'
      ((measurable_const.indicator hEm).aestronglyMeasurable)
      (Eventually.of_forall fun t => by
        show ‖{t : ℝ | N (t + rs / 4) = N t}.indicator (fun _ => (1 : ℝ)) t‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) t)]
        exact Set.indicator_le_self' (fun _ _ => zero_le_one) t)
  -- zeros on the block
  have hlong' : ∀ x ∈ Icc X (2 * X), ∃ q ∈ Icc (x - 1) x, ψ q = 0 :=
    fun x hx => hlong x (le_trans hXx₀ hx.1)
  have hshort' : ∀ x ∈ Icc X (2 * X), 2 ≤ N x - N (x - rs) → ∃ q ∈ Icc (x - rs) x, ψ q = 0 :=
    fun x hx h => hshort x (le_trans hXx₀ hx.1) rs hrs0 h
  have hlam : 0 < X ^ (7 / 2 : ℝ) * u ^ 18 := by
    have := Real.rpow_pos_of_pos hX0 (7 / 2 : ℝ); positivity
  have hB := integral_block_le ha hN hF hode (X := X) (rs := rs) (rl := 1) (δ := δ)
    (lam := X ^ (7 / 2 : ℝ) * u ^ 18) (by linarith) hrs0 hrs1 le_rfl hδ hδ' hlam hlong' hshort'
    hM2 hM4 hEb
  have halg := block_algebra (C₂ := C₂) (C₄ := C₄) hX0 hu2 hC hLu
  rw [hrs_def] at hB
  have hK : 0 ≤ a ^ 2 * Real.exp (2 * a) * Real.exp (π / 2) * (Real.exp δ * Real.exp (-(δ * X))) := by
    positivity
  exact hB.trans (mul_le_mul_of_nonneg_left halg hK)


/-- `δ^{-9/2}` written as `δ⁻¹⁴/√δ`, and `(2/δ)^{9/2} = 2^{9/2}δ⁻¹⁴/√δ`. -/
theorem two_div_rpow_nine_halves {δ : ℝ} (hδ : 0 < δ) :
    (1 / (δ / 2)) ^ (9 / 2 : ℝ) = 2 ^ (9 / 2 : ℝ) * (δ⁻¹ ^ 4 * (1 / Real.sqrt δ)) := by
  rw [show 1 / (δ / 2) = 2 * δ⁻¹ by field_simp, Real.mul_rpow (by norm_num) (by positivity)]
  congr 1
  have h1 : (δ⁻¹) ^ (9 / 2 : ℝ) = (δ⁻¹) ^ (4 : ℝ) * (δ⁻¹) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add (by positivity)]; norm_num
  have h2 : (δ⁻¹) ^ (4 : ℝ) = δ⁻¹ ^ 4 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h3 : (δ⁻¹) ^ (1 / 2 : ℝ) = 1 / Real.sqrt δ := by
    rw [Real.inv_rpow hδ.le, Real.sqrt_eq_rpow]; norm_num
  rw [h1, h2, h3]

/-- **The degree-one contradiction from its analytic inputs.** -/
theorem false_of_firstOrder_data {a : ℝ} (ha : 0 < a) {ψ F : ℝ → ℝ} {N : ℝ → ℤ}
    (hN : Monotone N) (hF : Continuous F) (hode : ∀ t, HasDerivAt ψ (a * (ψ t - F t)) t)
    (hψk : ∀ x, (ψ x : ℂ) = kernelPsi (lorentzOne a) x)
    {x₀ : ℝ} (hlong : ∀ x ≥ x₀, ∃ q ∈ Icc (x - 1) x, ψ q = 0)
    (hshort : ∀ x ≥ x₀, ∀ r > 0, 2 ≤ N x - N (x - r) → ∃ q ∈ Icc (x - r) x, ψ q = 0)
    {C T₀ : ℝ} (hC : 0 ≤ C) (hLGT : ∀ T ≥ T₀, ∀ h > 0,
      volume.real ({t : ℝ | N (t + h) = N t} ∩ Icc T (2 * T)) ≤ C * T / (1 + h * Real.log T) ^ 24)
    {C₂ : ℝ} (hC₂ : 0 ≤ C₂) (h2 : ∀ X ≥ 2,
      ∫ y in X..2 * X, Real.exp (π / 2 * y) * F y ^ 2 ≤ C₂ * X ^ (9 / 2 : ℝ) * Real.log X)
    {C₄ : ℝ} (hC₄ : 0 ≤ C₄) (h4 : ∀ X ≥ 2,
      ∫ y in X..2 * X, Real.exp (π * y) * F y ^ 4 ≤ C₄ * X ^ (8 : ℝ) * Real.log X ^ 4) :
    False := by
  have hpi := Real.pi_pos
  obtain ⟨L₀, hL₀, κ₀, hκ₀, hlow⟩ := exists_integral_norm_sq_shiftedProfile_lorentzOne_ge ha
  obtain ⟨A, hA_def⟩ : ∃ A : ℝ, A = 18 * C₂ + 2 ^ 28 * C * (8 / 3) ^ 24 + C₄ := ⟨_, rfl⟩
  have hA : 0 ≤ A := by rw [hA_def]; positivity
  obtain ⟨K₁, hK₁_def⟩ : ∃ K₁ : ℝ, K₁ = a ^ 2 * Real.exp (2 * a) * Real.exp (π / 2) := ⟨_, rfl⟩
  have hK₁ : 0 < K₁ := by rw [hK₁_def]; positivity
  obtain ⟨Γ₀, hΓ₀_def⟩ : ∃ Γ₀ : ℝ, Γ₀ = 2 ^ (9 / 2 : ℝ) * 2 ^ (9 / 2 : ℝ) * Real.Gamma (9 / 2) :=
    ⟨_, rfl⟩
  have hΓ₀ : 0 < Γ₀ := by
    have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 9 / 2); rw [hΓ₀_def]; positivity
  obtain ⟨ω₀, hω₀_def⟩ : ∃ ω₀ : ℝ, ω₀ = π * L₀ / (K₁ * Real.exp 1 * Γ₀) := ⟨_, rfl⟩
  have hω₀ : 0 < ω₀ := by rw [hω₀_def]; positivity
  obtain ⟨X₃, hX₃_def⟩ : ∃ X₃ : ℝ, X₃ = max (max 16 (4 * T₀)) (max x₀ (Real.exp 16)) := ⟨_, rfl⟩
  obtain ⟨Xs, hXs_def⟩ : ∃ Xs : ℝ, Xs = max X₃ (Real.exp ((A / ω₀) ^ 2)) := ⟨_, rfl⟩
  have hXsX₃ : X₃ ≤ Xs := by rw [hXs_def]; exact le_max_left _ _
  have hXs16 : 16 ≤ Xs := le_trans (by rw [hX₃_def]; exact le_trans (le_max_left _ _) (le_max_left _ _)) hXsX₃
  have hXs0 : 0 < Xs := by linarith
  -- small block constant beyond `Xs`
  have hsmall : ∀ X ≥ Xs, A / (Real.log X ^ (1 / 4 : ℝ)) ^ 2 ≤ ω₀ := by
    intro X hX
    have hXe : Real.exp ((A / ω₀) ^ 2) ≤ X := le_trans (by rw [hXs_def]; exact le_max_right _ _) hX
    have hlog : (A / ω₀) ^ 2 ≤ Real.log X := by
      have := Real.log_le_log (Real.exp_pos _) hXe; rwa [Real.log_exp] at this
    have hL0 : 0 ≤ Real.log X := le_trans (sq_nonneg _) hlog
    have hu2 : (Real.log X ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt (Real.log X) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0, Real.sqrt_eq_rpow]; norm_num
    rw [hu2]
    have hsq : A / ω₀ ≤ Real.sqrt (Real.log X) := by
      rw [show A / ω₀ = Real.sqrt ((A / ω₀) ^ 2) by
        rw [Real.sqrt_sq (div_nonneg hA hω₀.le)]]
      exact Real.sqrt_le_sqrt hlog
    by_cases hA0 : A = 0
    · rw [hA0, zero_div]; exact hω₀.le
    have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    have hs : 0 < Real.sqrt (Real.log X) := lt_of_lt_of_le (by positivity) hsq
    rw [div_le_iff₀ hs]
    rw [div_le_iff₀ hω₀] at hsq
    linarith
  -- integrability of `ψ²`
  have hm0 := lorentzOne_hm ha 0
  have hmb0 := lorentzOne_hmb ha 0
  obtain ⟨g01, g02, -, -⟩ := shiftedProfile_integrability (c := 0) le_rfl (by positivity) hm0 hmb0
  have hψ2 : Integrable fun x => ψ x ^ 2 := by
    refine (integrable_norm_sq_paperFT g01 g02).congr (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [← exp_mul_kernelPsi_eq le_rfl (by positivity) hm0 hmb0 x, ← hψk x]
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  obtain ⟨H, hH_def⟩ : ∃ H : ℝ, H = Real.exp (π / 2 * Xs) * ∫ x, ψ x ^ 2 := ⟨_, rfl⟩
  have hH : 0 ≤ H := by
    have : 0 ≤ ∫ x, ψ x ^ 2 := integral_nonneg fun _ => sq_nonneg _
    rw [hH_def]; positivity
  -- choice of `δ`
  obtain ⟨δ, hδ_def⟩ : ∃ δ : ℝ, δ = min (min 1 κ₀) (π * L₀ / (2 * (H + 1))) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ_def]; positivity
  have hδ1 : δ ≤ 1 := by rw [hδ_def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδκ : δ ≤ κ₀ := by rw [hδ_def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδH : δ ≤ π * L₀ / (2 * (H + 1)) := by rw [hδ_def]; exact min_le_right _ _
  have hδπ : δ ≤ π / 2 := by linarith [Real.pi_gt_three]
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = π / 4 - δ / 2 := ⟨_, rfl⟩
  have h2c : 2 * c = π / 2 - δ := by rw [hc_def]; ring
  have hc0 : 0 ≤ c := by rw [hc_def]; linarith
  have hc : c < π / 4 := by rw [hc_def]; linarith
  have hsin : Real.sin (2 * c) = Real.cos δ := by rw [h2c, Real.sin_pi_div_two_sub]
  have hcos : Real.cos (2 * c) = Real.sin δ := by rw [h2c, Real.cos_pi_div_two_sub]
  have hs : 1 / 2 ≤ Real.sin (2 * c) := by
    rw [hsin]
    have := Real.one_sub_sq_div_two_le_cos (x := δ)
    nlinarith
  have hκpos : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ0 (by linarith [Real.pi_gt_three])
  have hκle : Real.sin δ ≤ δ := Real.sin_le hδ0.le
  have hκ : Real.cos (2 * c) ≤ κ₀ := by rw [hcos]; linarith
  have hm := lorentzOne_hm ha c
  have hmb := lorentzOne_hmb ha c
  obtain ⟨G1, G2, -, -⟩ := shiftedProfile_integrability hc0 hc hm hmb
  -- the weighted energy equals the Plancherel mass
  have hgeq : ∀ x, ‖(Real.exp (c * x) : ℂ) * kernelPsi (lorentzOne a) x‖ ^ 2 =
      Real.exp ((π / 2 - δ) * x) * ψ x ^ 2 := by
    intro x
    rw [← hψk x, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), mul_pow, sq_abs, ← Real.exp_nat_mul, ← h2c]
    congr 2; push_cast; ring
  have hPl := integral_norm_sq_exp_mul_kernelPsi hc0 hc hm hmb
  simp_rw [hgeq] at hPl
  have hwint : Integrable fun x => Real.exp ((π / 2 - δ) * x) * ψ x ^ 2 := by
    refine (integrable_norm_sq_paperFT G1 G2).congr (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [← exp_mul_kernelPsi_eq hc0 hc hm hmb x, hgeq]
  -- upper bound on every finite window
  have hwc : Continuous fun x => Real.exp ((π / 2 - δ) * x) * ψ x ^ 2 := by
    have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun t => (hode t).continuousAt
    fun_prop
  have hblock : ∀ j : ℕ, ∫ x in (2 ^ j * Xs)..(2 * (2 ^ j * Xs)),
      Real.exp ((π / 2 - δ) * x) * ψ x ^ 2 ≤
      K₁ * Real.exp δ * ω₀ * ((2 ^ j * Xs) ^ (9 / 2 : ℝ) * Real.exp (-(δ * (2 ^ j * Xs)))) := by
    intro j
    have hXj : Xs ≤ 2 ^ j * Xs := le_mul_of_one_le_left hXs0.le (one_le_pow₀ (by norm_num))
    have hb := integral_block_le_explicit ha hN hF hode hlong hshort hC hLGT hC₂ h2 hC₄ h4
      (X := 2 ^ j * Xs) (δ := δ) (by rw [← hX₃_def]; exact le_trans hXsX₃ hXj) hδ0 hδπ
    rw [← hA_def, ← hK₁_def] at hb
    have hsm := hsmall (2 ^ j * Xs) hXj
    have hpos : 0 ≤ K₁ * (Real.exp δ * Real.exp (-(δ * (2 ^ j * Xs)))) * (2 ^ j * Xs) ^ (9 / 2 : ℝ) := by
      have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ j * Xs) (9 / 2 : ℝ); positivity
    calc ∫ x in (2 ^ j * Xs)..(2 * (2 ^ j * Xs)), Real.exp ((π / 2 - δ) * x) * ψ x ^ 2
        ≤ K₁ * (Real.exp δ * Real.exp (-(δ * (2 ^ j * Xs)))) * ((2 ^ j * Xs) ^ (9 / 2 : ℝ) *
            (A / (Real.log (2 ^ j * Xs) ^ (1 / 4 : ℝ)) ^ 2)) := hb
      _ ≤ K₁ * (Real.exp δ * Real.exp (-(δ * (2 ^ j * Xs)))) * ((2 ^ j * Xs) ^ (9 / 2 : ℝ) * ω₀) := by
          gcongr
      _ = _ := by ring
  have hsumΓ := fun J => sum_dyadic_rpow_mul_exp_le hXs0 hδ0 J
  have hupper : ∀ J : ℕ, ∫ x in (Xs - J)..(2 ^ J * Xs), Real.exp ((π / 2 - δ) * x) * ψ x ^ 2 ≤
      H + K₁ * Real.exp δ * ω₀ * (2 ^ (9 / 2 : ℝ) * ((1 / (δ / 2)) ^ (9 / 2 : ℝ) *
        Real.Gamma (9 / 2))) := by
    intro J
    have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := Xs) (hwc.intervalIntegrable _ _)
      (hwc.intervalIntegrable _ _)]
    -- head
    have hhead : ∫ x in (Xs - J)..Xs, Real.exp ((π / 2 - δ) * x) * ψ x ^ 2 ≤ H := by
      have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun t => (hode t).continuousAt
      calc ∫ x in (Xs - J)..Xs, Real.exp ((π / 2 - δ) * x) * ψ x ^ 2
          ≤ ∫ x in (Xs - J)..Xs, Real.exp (π / 2 * Xs) * ψ x ^ 2 := by
            refine intervalIntegral.integral_mono_on (by linarith) (hwc.intervalIntegrable _ _)
              ((by fun_prop : Continuous fun x => Real.exp (π / 2 * Xs) * ψ x ^ 2).intervalIntegrable
                _ _) fun x hx => ?_
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            apply Real.exp_le_exp.mpr
            have e1 : (π / 2 - δ) * x ≤ (π / 2 - δ) * Xs :=
              mul_le_mul_of_nonneg_left hx.2 (by linarith)
            nlinarith
        _ = Real.exp (π / 2 * Xs) * ∫ x in (Xs - J)..Xs, ψ x ^ 2 :=
            intervalIntegral.integral_const_mul _ _
        _ ≤ H := by
            rw [hH_def]
            gcongr
            rw [intervalIntegral.integral_of_le (by linarith)]
            exact setIntegral_le_integral hψ2 (Eventually.of_forall fun _ => sq_nonneg _)
    -- dyadic tail
    have htail : ∫ x in Xs..(2 ^ J * Xs), Real.exp ((π / 2 - δ) * x) * ψ x ^ 2 ≤
        K₁ * Real.exp δ * ω₀ * (2 ^ (9 / 2 : ℝ) * ((1 / (δ / 2)) ^ (9 / 2 : ℝ) *
          Real.Gamma (9 / 2))) := by
      have hsum := intervalIntegral.sum_integral_adjacent_intervals
        (a := fun j : ℕ => 2 ^ j * Xs) (n := J) (μ := volume)
        (f := fun x => Real.exp ((π / 2 - δ) * x) * ψ x ^ 2)
        (fun k _ => hwc.intervalIntegrable _ _)
      simp only [pow_zero, one_mul] at hsum
      rw [← hsum]
      have hK : 0 ≤ K₁ * Real.exp δ * ω₀ := by positivity
      calc ∑ k ∈ Finset.range J, ∫ x in (2 ^ k * Xs)..(2 ^ (k + 1) * Xs),
            Real.exp ((π / 2 - δ) * x) * ψ x ^ 2
          ≤ ∑ k ∈ Finset.range J, K₁ * Real.exp δ * ω₀ *
              ((2 ^ k * Xs) ^ (9 / 2 : ℝ) * Real.exp (-(δ * (2 ^ k * Xs)))) := by
            refine Finset.sum_le_sum fun k _ => ?_
            have := hblock k
            rw [show (2 : ℝ) ^ (k + 1) * Xs = 2 * (2 ^ k * Xs) by rw [pow_succ]; ring]
            exact this
        _ = K₁ * Real.exp δ * ω₀ * ∑ k ∈ Finset.range J,
              (2 ^ k * Xs) ^ (9 / 2 : ℝ) * Real.exp (-(δ * (2 ^ k * Xs))) := by
            rw [Finset.mul_sum]
        _ ≤ _ := by gcongr; exact hsumΓ J
    linarith
  have hbot : Tendsto (fun J : ℕ => Xs - J) atTop atBot := by
    refine tendsto_atTop_atBot.2 fun b => ?_
    obtain ⟨N₁, hN₁⟩ := exists_nat_ge (Xs - b)
    exact ⟨N₁, fun n hn => by have : (N₁ : ℝ) ≤ n := Nat.cast_le.2 hn; linarith⟩
  have htop : Tendsto (fun J : ℕ => 2 ^ J * Xs) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const hXs0
  have hlim := MeasureTheory.intervalIntegral_tendsto_integral hwint hbot htop
  have hle := le_of_tendsto' hlim hupper
  -- lower bound
  have hLow := hlow c hc0 hc hs hκ
  rw [hcos] at hLow
  -- assemble
  obtain ⟨Q, hQ_def⟩ : ∃ Q : ℝ, Q = δ⁻¹ ^ 4 * (1 / Real.sqrt δ) := ⟨_, rfl⟩
  have hQκ : Q ≤ (Real.sin δ)⁻¹ ^ 4 * (1 / Real.sqrt (Real.sin δ)) := by
    rw [hQ_def]
    have h1 : δ⁻¹ ≤ (Real.sin δ)⁻¹ := inv_anti₀ hκpos hκle
    have h2 : 1 / Real.sqrt δ ≤ 1 / Real.sqrt (Real.sin δ) :=
      one_div_le_one_div_of_le (Real.sqrt_pos.mpr hκpos) (Real.sqrt_le_sqrt hκle)
    gcongr
  have hQδ : δ⁻¹ ≤ Q := by
    rw [hQ_def]
    have hk1 : 1 ≤ δ⁻¹ := one_le_inv_iff₀.mpr ⟨hδ0, hδ1⟩
    have h1 : δ⁻¹ ≤ δ⁻¹ ^ 4 := by
      calc δ⁻¹ = δ⁻¹ ^ 1 := (pow_one _).symm
        _ ≤ δ⁻¹ ^ 4 := pow_le_pow_right₀ hk1 (by norm_num)
    have h2 : 1 ≤ 1 / Real.sqrt δ := by
      rw [le_div_iff₀ (Real.sqrt_pos.mpr hδ0), one_mul]
      calc Real.sqrt δ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hδ1
        _ = 1 := Real.sqrt_one
    calc δ⁻¹ = δ⁻¹ * 1 := (mul_one _).symm
      _ ≤ δ⁻¹ ^ 4 * (1 / Real.sqrt δ) := mul_le_mul h1 h2 zero_le_one (by positivity)
  have hΓ : 2 ^ (9 / 2 : ℝ) * ((1 / (δ / 2)) ^ (9 / 2 : ℝ) * Real.Gamma (9 / 2)) = Γ₀ * Q := by
    rw [two_div_rpow_nine_halves hδ0, hΓ₀_def, hQ_def]; ring
  rw [hΓ] at hle
  have hexpδ : Real.exp δ ≤ Real.exp 1 := Real.exp_le_exp.mpr hδ1
  have hkey : K₁ * Real.exp δ * ω₀ * (Γ₀ * Q) ≤ π * L₀ * Q := by
    have hQ0 : 0 ≤ Q := by rw [hQ_def]; positivity
    calc K₁ * Real.exp δ * ω₀ * (Γ₀ * Q) ≤ K₁ * Real.exp 1 * ω₀ * (Γ₀ * Q) := by gcongr
      _ = (K₁ * Real.exp 1 * Γ₀ * ω₀) * Q := by ring
      _ = π * L₀ * Q := by
          have hden : K₁ * Real.exp 1 * Γ₀ ≠ 0 := by positivity
          rw [hω₀_def, mul_div_cancel₀ _ hden]
  have hbig : 2 * (H + 1) ≤ π * L₀ * δ⁻¹ := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (H + 1))).1 hδH
    rw [← div_eq_mul_inv, le_div_iff₀ hδ0]; linarith
  have hlowQ : 2 * π * (L₀ * Q) ≤ 2 * π * ∫ u, ‖shiftedProfile (lorentzOne a) c u‖ ^ 2 := by
    have : L₀ * Q ≤ L₀ * ((Real.sin δ)⁻¹ ^ 4 * (1 / Real.sqrt (Real.sin δ))) :=
      mul_le_mul_of_nonneg_left hQκ hL₀.le
    have h' : L₀ * ((Real.sin δ)⁻¹ ^ 4 * (1 / Real.sqrt (Real.sin δ))) ≤
        ∫ u, ‖shiftedProfile (lorentzOne a) c u‖ ^ 2 := by
      rw [← mul_assoc]; exact hLow
    exact mul_le_mul_of_nonneg_left (le_trans this h') (by positivity)
  have hQL : π * L₀ * δ⁻¹ ≤ π * L₀ * Q := mul_le_mul_of_nonneg_left hQδ (by positivity)
  rw [← hPl] at hlowQ
  linarith

end RHTower.KernelStrip
