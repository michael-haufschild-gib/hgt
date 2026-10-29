import GaloisForLFunctions.RHTower.Heat.HeatLocalCofactor

/-!+# Quantitative bounds in a heat window without nonreal zeros

At fixed depth from the real axis, a unit height window either contains
a nonreal heat zero or supplies a polynomial minimum modulus and
logarithmic bounds for the first two logarithmic derivatives.
The constants are uniform as nonnegative heat tends to zero.
-/

open Complex Set Metric Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

private theorem distance_to_heat_zero_ge {t X δ : ℝ} {z : ℂ}
    (hδ : δ ≤ 1) (hzre : z.re = X) (hzδ : δ ≤ |z.im|)
    (hwindow : ∀ ζ : ℂ, riemannHeat t ζ = 0 → |ζ.re - X| ≤ 1 → ζ.im = 0)
    {ζ : ℂ} (hζ : riemannHeat t ζ = 0) : δ ≤ ‖z - ζ‖ := by
  by_cases hnear : |ζ.re - X| ≤ 1
  · have him := hwindow ζ hζ hnear
    have h := Complex.abs_im_le_norm (z - ζ)
    simp only [Complex.sub_im, him, sub_zero] at h
    exact hzδ.trans h
  · have h := Complex.abs_re_le_norm (ζ - z)
    rw [Complex.sub_re, hzre, norm_sub_rev] at h
    exact hδ.trans ((le_of_lt (lt_of_not_ge hnear)).trans h)

private theorem norm_sub_heat_anchor_le {X : ℝ} {z : ℂ}
    (hzre : z.re = X) (hzim : |z.im| ≤ 1 / 2) :
    ‖z - ((X : ℂ) - 16 * I)‖ ≤ 33 / 2 := by
  have hre : (z - ((X : ℂ) - 16 * I)).re = 0 := by simp [hzre]
  have him : (z - ((X : ℂ) - 16 * I)).im = z.im + 16 := by simp
  have h := Complex.norm_le_abs_re_add_abs_im (z - ((X : ℂ) - 16 * I))
  rw [hre, him, abs_zero, zero_add] at h
  have ha := abs_add_le z.im (16 : ℝ)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 16)] at ha
  linarith only [h, ha, hzim]

private theorem exp_degree_lower {d C L : ℝ} {n : ℕ}
    (hd : 0 < d) (hd18 : d ≤ 18) (hn : (n : ℝ) ≤ C * L) :
    Real.exp (-(C * L) * Real.log (18 / d)) ≤ (d / 18) ^ n := by
  have hK : 0 ≤ Real.log (18 / d) := Real.log_nonneg
    ((le_div_iff₀ hd).mpr (by linarith only [hd18]))
  have heq : Real.exp (-(n : ℝ) * Real.log (18 / d)) = (d / 18) ^ n := by
    rw [show -(n : ℝ) * Real.log (18 / d) = (n : ℝ) * (-Real.log (18 / d)) by ring,
      Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by positivity), inv_div]
  refine (Real.exp_le_exp.mpr ?_).trans_eq heq
  nlinarith only [mul_le_mul_of_nonneg_right hn hK]

/-- A unit heat window either contains a nonreal zero or has uniform local
minimum-modulus and logarithmic-derivative bounds at every fixed positive depth. -/
theorem exists_riemannHeat_window_bounds {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∃ X₀ : ℝ, 4096 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 8 → t * Real.log X ≤ 1 →
        ∀ z : ℂ, z.re = X → δ ≤ |z.im| → |z.im| ≤ 1 / 2 →
          (∃ ζ : ℂ, riemannHeat t ζ = 0 ∧ ζ.im ≠ 0 ∧ |ζ.re - X| ≤ 1) ∨
          ((∀ s : ℂ, ‖s - z‖ ≤ δ / 2 →
              ‖xiLine X 16‖ / 8 * Real.exp (-(A * Real.log X)) ≤ ‖riemannHeat t s‖) ∧
            (∀ s : ℂ, ‖s - z‖ ≤ δ / 4 →
              ‖deriv (riemannHeat t) s / riemannHeat t s‖ ≤ B * Real.log X) ∧
            (∀ s : ℂ, ‖s - z‖ ≤ δ / 8 →
              ‖deriv (fun w => deriv (riemannHeat t) w / riemannHeat t w) s‖ ≤
                B * Real.log X)) := by
  classical
  obtain ⟨C, hC, X₁, hX₁, hcofactor⟩ := exists_uniform_riemannHeat_local_cofactor
  let d := δ / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hd18 : d ≤ 18 := by dsimp [d]; linarith only [hδ2]
  let A := C * (1 + Real.log (18 / d))
  have hK : 0 ≤ Real.log (18 / d) := Real.log_nonneg
    ((le_div_iff₀ hd).mpr (by linarith only [hd18]))
  have hA : 0 < A := by dsimp [A]; positivity
  let E := Real.log 32 + 4361 + A
  have hlog32 : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
  have hE : 0 < E := by dsimp [E]; linarith only [hA, hlog32]
  let K := 48 * E / δ
  have hKpos : 0 < K := by dsimp [K]; positivity
  let B := K + (8 / δ) * K
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨A, B, hA, hB, X₁ + 4096 + Real.exp 20, ?_, ?_⟩
  · linarith only [hX₁, Real.exp_pos 20]
  intro X hX₀ t ht ht8 htL z hzre hzδ hzim
  by_cases hzero : ∃ ζ : ℂ, riemannHeat t ζ = 0 ∧ ζ.im ≠ 0 ∧ |ζ.re - X| ≤ 1
  · exact Or.inl hzero
  right
  have hwindow : ∀ ζ : ℂ, riemannHeat t ζ = 0 → |ζ.re - X| ≤ 1 → ζ.im = 0 := by
    intro ζ hζ hζX
    by_contra him
    exact hzero ⟨ζ, hζ, him, hζX⟩
  have hX : 4096 ≤ X := by linarith only [hX₀, hX₁, Real.exp_pos 20]
  have hL : 20 ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 20) (show Real.exp 20 ≤ X by linarith)
    simpa only [Real.log_exp] using h
  have hL0 : 0 ≤ Real.log X := by linarith only [hL]
  obtain ⟨T, m, g, _, _, _, hfac, hcount, _, _, _, hmin⟩ :=
    hcofactor X (by linarith only [hX₀, Real.exp_pos 20]) t ht ht8 htL
  let c : ℂ := (X : ℂ) - 16 * I
  let N := ‖xiLine X 16‖
  have hN : 0 < N := by
    apply norm_pos_iff.mpr
    apply xi_ne_zero_of_one_lt_re
    norm_num [xiLine]
  let m₀ := N / 8 * Real.exp (-(A * Real.log X))
  let M := 4 * N * Real.exp (4096 + 264 * Real.log X)
  have hm₀ : 0 < m₀ := by dsimp [m₀]; positivity
  have hbase : ‖z - c‖ ≤ 33 / 2 := norm_sub_heat_anchor_le hzre hzim
  have hfloor : ∀ s : ℂ, ‖s - z‖ ≤ δ / 2 → m₀ ≤ ‖riemannHeat t s‖ := by
    intro s hs
    have hs17 : ‖s - c‖ ≤ 17 := by
      have htri := norm_sub_le_norm_sub_add_norm_sub s z c
      linarith only [htri, hs, hbase, hδ2]
    have hdist : ∀ a ∈ T, 0 < m a → d ≤ ‖s - c - a‖ := by
      intro a ha hma
      have hroot : riemannHeat t (c + a) = 0 := by
        rw [hfac a]
        have hp : (∏ b ∈ T, (a - b) ^ m b) = 0 := by
          apply Finset.prod_eq_zero ha
          rw [sub_self, zero_pow (Nat.ne_of_gt hma)]
        rw [hp, zero_mul]
      have hsep := distance_to_heat_zero_ge (by linarith only [hδ2]) hzre hzδ hwindow hroot
      have htri := norm_sub_le_norm_sub_add_norm_sub z s (c + a)
      rw [norm_sub_rev z s] at htri
      have hdist : d ≤ ‖s - (c + a)‖ := by dsimp [d]; linarith only [hsep, htri, hs]
      simpa only [sub_add_eq_sub_sub] using hdist
    have h := hmin (s - c) d hs17 hd.le hdist
    have hsc : (X : ℂ) - 16 * I + (s - c) = s := by dsimp [c]; ring
    rw [hsc] at h
    have hp := exp_degree_lower hd hd18 hcount
    have heq : Real.exp (-(A * Real.log X)) =
        Real.exp (-(C * Real.log X) * Real.log (18 / d)) * Real.exp (-(C * Real.log X)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [A]
      ring
    calc
      m₀ = N / 8 *
          (Real.exp (-(C * Real.log X) * Real.log (18 / d)) * Real.exp (-(C * Real.log X))) := by
        rw [← heq]
      _ ≤ N / 8 * ((d / 18) ^ (∑ a ∈ T, m a) * Real.exp (-(C * Real.log X))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le) (by positivity)
      _ = d ^ (∑ a ∈ T, m a) * ‖xiLine X 16‖ /
          (8 * (18 : ℝ) ^ (∑ a ∈ T, m a)) * Real.exp (-(C * Real.log X)) := by
        dsimp [N]
        rw [div_pow]
        ring
      _ ≤ _ := h
  have hfree : ∀ s ∈ ball z (δ / 2), riemannHeat t s ≠ 0 := by
    intro s hs
    exact norm_pos_iff.mp (hm₀.trans_le (hfloor s (mem_ball_iff_norm.mp hs).le))
  have hupper : ∀ s ∈ ball z (δ / 2), ‖riemannHeat t s‖ ≤ M := by
    intro s hs
    have hsz : ‖s - z‖ < δ / 2 := mem_ball_iff_norm.mp hs
    have hre : |s.re - X| ≤ 64 := by
      have h := Complex.abs_re_le_norm (s - z)
      rw [Complex.sub_re, hzre] at h
      linarith only [h, hsz, hδ2]
    have him : |s.im| ≤ 64 := by
      have h := Complex.abs_im_le_norm (s - z)
      rw [Complex.sub_im] at h
      have htri : |s.im| ≤ |s.im - z.im| + |z.im| := by
        simpa only [sub_add_cancel] using abs_add_le (s.im - z.im) z.im
      linarith only [h, hsz, htri, hzim, hδ2]
    have heq : (s.re : ℂ) + I * s.im = s := by
      simpa only [mul_comm I] using Complex.re_add_im s
    have h := norm_riemannHeat_near_le_of_nonneg ht ht8 hX hL htL hre him
    simpa only [heq] using h
  have hratio : M / m₀ = 32 * Real.exp (4096 + (264 + A) * Real.log X) := by
    have heq : M / m₀ = 32 *
        (Real.exp (4096 + 264 * Real.log X) / Real.exp (-(A * Real.log X))) := by
      dsimp [M, m₀]
      field_simp [hN.ne']
      ring
    rw [heq, ← Real.exp_sub]
    congr 2
    ring
  have hlog : Real.log (M / m₀) = Real.log 32 + 4096 + (264 + A) * Real.log X := by
    rw [hratio, Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hEL : Real.log (M / m₀) + 1 ≤ E * Real.log X := by
    have hp := mul_nonneg (show 0 ≤ Real.log X - 1 by linarith only [hL])
      (show 0 ≤ Real.log 32 + 4097 by linarith only [hlog32])
    rw [hlog]
    dsimp [E]
    nlinarith only [hp]
  have hdiff := differentiable_riemannHeat ht
  have hcentre : m₀ ≤ ‖riemannHeat t z‖ := hfloor z (by simp; positivity)
  have hq : ∀ s : ℂ, ‖s - z‖ ≤ δ / 4 →
      ‖deriv (riemannHeat t) s / riemannHeat t s‖ ≤ K * Real.log X := by
    intro s hs
    have h := norm_logDeriv_le (f := riemannHeat t) (c := z) (R := δ / 2)
      (r := 3 * δ / 8) (ρ := δ / 4) (M := M) (m := m₀)
      (by positivity) (by linarith only [hδ]) (by linarith only [hδ])
      hdiff.differentiableOn hfree hupper hm₀ hcentre hs
    have heq : 2 * (Real.log (M / m₀) + 1) * (3 * δ / 8) /
        (δ / 2 - 3 * δ / 8) / (3 * δ / 8 - δ / 4) =
        (48 / δ) * (Real.log (M / m₀) + 1) := by
      field_simp [hδ.ne']
      ring
    rw [heq] at h
    refine h.trans ?_
    have hb := mul_le_mul_of_nonneg_left hEL (show 0 ≤ (48 : ℝ) / δ by positivity)
    dsimp [K]
    convert hb using 1
    ring
  have hq' : ∀ s : ℂ, ‖s - z‖ ≤ δ / 8 →
      ‖deriv (fun w => deriv (riemannHeat t) w / riemannHeat t w) s‖ ≤
        ((8 / δ) * K) * Real.log X := by
    intro s hs
    have hnear : ∀ w ∈ closedBall s (δ / 8), ‖w - z‖ ≤ δ / 4 := by
      intro w hw
      have hws := mem_closedBall_iff_norm.mp hw
      have htri := norm_sub_le_norm_sub_add_norm_sub w s z
      linarith only [hws, hs, htri]
    have han := hdiff.differentiableOn.analyticOnNhd isOpen_univ
    have hqa : AnalyticOnNhd ℂ (fun w => deriv (riemannHeat t) w / riemannHeat t w)
        (closedBall s (δ / 8)) := by
      intro w hw
      have hne : riemannHeat t w ≠ 0 := hfree w
        (mem_ball_iff_norm.mpr (by linarith only [hnear w hw, hδ]))
      exact (han w (mem_univ w)).deriv.div (han w (mem_univ w)) hne
    have hdc : DiffContOnCl ℂ (fun w => deriv (riemannHeat t) w / riemannHeat t w)
        (ball s (δ / 8)) := by
      refine ⟨hqa.differentiableOn.mono ball_subset_closedBall, ?_⟩
      rw [closure_ball s (by positivity : δ / 8 ≠ 0)]
      exact hqa.continuousOn
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      (by positivity : 0 < δ / 8) hdc
      (fun w hw => hq w (hnear w (sphere_subset_closedBall hw)))
    refine hc.trans_eq ?_
    field_simp [hδ.ne']
  have hKB : K ≤ B := by
    have hp : 0 ≤ (8 / δ) * K := by positivity
    dsimp [B]
    linarith only [hp]
  have hK'B : (8 / δ) * K ≤ B := by dsimp [B]; linarith only [hKpos]
  exact ⟨hfloor,
    fun s hs => (hq s hs).trans (mul_le_mul_of_nonneg_right hKB hL0),
    fun s hs => (hq' s hs).trans (mul_le_mul_of_nonneg_right hK'B hL0)⟩

end

end RHTower.DeBruijn
