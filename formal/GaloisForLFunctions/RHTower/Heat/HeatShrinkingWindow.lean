import GaloisForLFunctions.RHTower.Heat.HeatLocalCofactor
import GaloisForLFunctions.HTGeometry.LogDerivativeFactor
import GaloisForLFunctions.HTGeometry.CenteredFactorProduct

/-!
# Uniform centered estimates in shrinking heat windows

A zero-free disk of radius `d` gives a logarithmic slope of size
`log X / d`. Cancelling that slope leaves quadratic error of size
`log X / d²` on a fixed real segment. The finite zero factors retain
this estimate even when the segment crosses other zeros.
-/

open Complex Set Metric Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

private theorem heat_anchor_distance_le {X : ℝ} {z : ℂ}
    (hzre : z.re = X) (hzim : |z.im| ≤ 1 / 2) :
    ‖z - ((X : ℂ) - 16 * I)‖ ≤ 33 / 2 := by
  have hre : (z - ((X : ℂ) - 16 * I)).re = 0 := by simp [hzre]
  have him : (z - ((X : ℂ) - 16 * I)).im = z.im + 16 := by simp
  have h := Complex.norm_le_abs_re_add_abs_im (z - ((X : ℂ) - 16 * I))
  rw [hre, him, abs_zero, zero_add] at h
  have ha := abs_add_le z.im (16 : ℝ)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 16)] at ha
  linarith only [h, ha, hzim]

private theorem degree_floor_le {d C L : ℝ} {n : ℕ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hn : (n : ℝ) ≤ C * L) :
    Real.exp (-(40 * C * L / d)) ≤
      (d / 36) ^ n * Real.exp (-(C * L)) := by
  have hratio : 0 < 36 / d := by positivity
  have hlog0 : 0 ≤ Real.log (36 / d) := Real.log_nonneg
    ((le_div_iff₀ hd).mpr (by linarith only [hd1]))
  have hlog := Real.log_le_sub_one_of_pos hratio
  have hdegree := mul_le_mul_of_nonneg_right hn hlog0
  have hCL := mul_nonneg hC hL
  have hlogmul := mul_le_mul_of_nonneg_left hlog hCL
  have heq : (d / 36) ^ n = Real.exp (-(n : ℝ) * Real.log (36 / d)) := by
    rw [show -(n : ℝ) * Real.log (36 / d) = (n : ℝ) * (-Real.log (36 / d)) by ring,
      Real.exp_nat_mul, Real.exp_neg, Real.exp_log hratio, inv_div]
  rw [heq, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hnonneg : 0 ≤ C * L / d := div_nonneg hCL hd.le
  have hscale : C * L * (36 / d - 1) = 36 * (C * L / d) - C * L := by ring
  rw [hscale] at hlogmul
  have hscale40 : 40 * C * L / d = 40 * (C * L / d) := by ring
  rw [hscale40]
  linarith only [hdegree, hlogmul, hnonneg]

/-- A shrinking disk either contains a heat zero or supplies a uniform slope,
minimum modulus, and centered error on a fixed real interval. -/
theorem exists_riemannHeat_shrinking_window_bounds :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 4096 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 8 → t * Real.log X ≤ 1 →
        ∀ d : ℝ, 0 < d → d ≤ 1 / 2 → ∀ z : ℂ, z.re = X → |z.im| ≤ 1 / 2 →
          (∃ ζ : ℂ, riemannHeat t ζ = 0 ∧ ‖ζ - z‖ ≤ d) ∨
          (∀ s : ℂ, ‖s - z‖ ≤ d / 8 →
            riemannHeat t s ≠ 0 ∧
            ‖deriv (riemannHeat t) s / riemannHeat t s‖ ≤ C * Real.log X / d ∧
            ‖xiLine X 16‖ / 8 * Real.exp (-(C * Real.log X / d)) ≤ ‖riemannHeat t s‖ ∧
            ∀ u : ℝ, |u| ≤ 1 / 32 →
              ‖Complex.exp (-(u : ℂ) * (deriv (riemannHeat t) s / riemannHeat t s)) *
                  riemannHeat t (s + u) / riemannHeat t s - 1‖ ≤
                Real.exp ((C * Real.log X / d ^ 2) * u ^ 2) - 1) := by
  classical
  obtain ⟨C, hC, X₀, hX₀, hcofactor⟩ := exists_uniform_riemannHeat_local_cofactor
  refine ⟨40 * C, by positivity, X₀, hX₀, ?_⟩
  intro X hX t ht ht8 htL d hd hd2 z hzre hzim
  by_cases hzero : ∃ ζ : ℂ, riemannHeat t ζ = 0 ∧ ‖ζ - z‖ ≤ d
  · exact Or.inl hzero
  right
  have hXpos : 1 < X := by linarith only [hX, hX₀]
  have hL : 0 < Real.log X := Real.log_pos hXpos
  have hCL : 0 < C * Real.log X := mul_pos hC hL
  have hd1 : d ≤ 1 := by linarith only [hd2]
  obtain ⟨T₀, m, g, hg, _, hgfree, hfac₀, hcount₀, hgq, hgq', hgmin, _⟩ :=
    hcofactor X hX t ht ht8 htL
  let T := T₀.filter (fun a => 0 < m a)
  have hprod (w : ℂ) : (∏ a ∈ T, (w - a) ^ m a) = ∏ a ∈ T₀, (w - a) ^ m a := by
    dsimp [T]
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun a _ => ?_
    split_ifs with h
    · rfl
    · have hm : m a = 0 := by omega
      simp only [hm, pow_zero]
  have hsum : (∑ a ∈ T, m a) = ∑ a ∈ T₀, m a := by
    dsimp [T]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with h
    · rfl
    · omega
  have hcount : ((∑ a ∈ T, m a : ℕ) : ℝ) ≤ C * Real.log X := by
    simpa only [hsum] using hcount₀
  let c : ℂ := (X : ℂ) - 16 * I
  let f : ℂ → ℂ := fun w => riemannHeat t (c + w)
  have hfac (w : ℂ) : f w = (∏ a ∈ T, (w - a) ^ m a) * g w := by
    rw [hprod]
    exact hfac₀ w
  have hderiv (w : ℂ) : deriv f w = deriv (riemannHeat t) (c + w) := by
    have h := ((differentiable_riemannHeat ht) (c + w)).hasDerivAt.comp w
      ((hasDerivAt_id w).const_add c)
    simpa only [Function.comp_def, mul_one] using h.deriv
  have hbase : ‖z - c‖ ≤ 33 / 2 := heat_anchor_distance_le hzre hzim
  have hroot : ∀ a ∈ T, riemannHeat t (c + a) = 0 := by
    intro a ha
    have hma : 0 < m a := (Finset.mem_filter.mp ha).2
    change f a = 0
    rw [hfac a]
    have hp : (∏ b ∈ T, (a - b) ^ m b) = 0 := by
      apply Finset.prod_eq_zero ha
      rw [sub_self, zero_pow (Nat.ne_of_gt hma)]
    rw [hp, zero_mul]
  intro s hs
  have hs17 : ‖s - c‖ ≤ 17 := by
    have h := norm_sub_le_norm_sub_add_norm_sub s z c
    linarith only [h, hs, hbase, hd2]
  have hsnear : ‖s - c‖ ≤ 33 / 2 + d / 8 := by
    calc
      _ ≤ ‖s - z‖ + ‖z - c‖ := norm_sub_le_norm_sub_add_norm_sub s z c
      _ ≤ d / 8 + 33 / 2 := add_le_add hs hbase
      _ = _ := by ring
  have hsne : riemannHeat t s ≠ 0 := by
    intro h
    exact hzero ⟨s, h, by linarith only [hs, hd]⟩
  have hsc : c + (s - c) = s := by ring
  have hfar : ∀ a ∈ T, d / 2 ≤ ‖s - c - a‖ := by
    intro a ha
    have hsep : d < ‖c + a - z‖ := lt_of_not_ge
      (fun h => hzero ⟨c + a, hroot a ha, h⟩)
    have htri := norm_sub_le_norm_sub_add_norm_sub (c + a) s z
    rw [norm_sub_rev (c + a) s, sub_add_eq_sub_sub] at htri
    linarith only [hsep, htri, hs, hd]
  have hne : ∀ a ∈ T, s - c ≠ a := by
    intro a ha h
    have hsep := hfar a ha
    rw [h, sub_self, norm_zero] at hsep
    linarith only [hsep, hd]
  have hgdiff : Differentiable ℂ g := fun w => (hg w (mem_univ w)).differentiableAt
  have hsplit := logDeriv_of_factor (f := f) (h := g) (U := ball 0 18)
    isOpen_ball hgdiff.differentiableOn
    (fun w hw => hgfree w (by simpa only [sub_zero] using (mem_ball_iff_norm.mp hw).le))
    (fun w _ => hfac w)
    (by simpa only [mem_ball_iff_norm, sub_zero] using (show ‖s - c‖ < 18 by linarith only [hs17])) hne
  rw [logDeriv_apply, logDeriv_apply, hderiv, hsc] at hsplit
  simp only [f, hsc] at hsplit
  change deriv (riemannHeat t) s / riemannHeat t s =
    (∑ a ∈ T, (m a : ℂ) / (s - c - a)) + deriv g (s - c) / g (s - c) at hsplit
  have hq : ‖deriv (riemannHeat t) s / riemannHeat t s‖ ≤ 40 * C * Real.log X / d := by
    rw [hsplit]
    have hp := norm_sum_multiplicity_div_le (m := m) (by positivity : 0 < d / 2) hfar
    rw [← Nat.cast_sum] at hp
    have hp' : ‖∑ a ∈ T, (m a : ℂ) / (s - c - a)‖ ≤ (C * Real.log X) / (d / 2) :=
      hp.trans (div_le_div_of_nonneg_right hcount (by positivity))
    have htri := norm_add_le (∑ a ∈ T, (m a : ℂ) / (s - c - a)) (deriv g (s - c) / g (s - c))
    have hgb := hgq (s - c) hs17
    have hCd : C * Real.log X * d ≤ C * Real.log X := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hd1 hCL.le
    apply (le_div_iff₀ hd).mpr
    have htotal := mul_le_mul_of_nonneg_right (htri.trans (add_le_add hp' hgb)) hd.le
    have he : ((C * Real.log X) / (d / 2) + C * Real.log X) * d =
        2 * (C * Real.log X) + C * Real.log X * d := by field_simp
    rw [he] at htotal
    nlinarith only [htotal, hCd, hCL.le]
  have hfloor : ‖xiLine X 16‖ / 8 * Real.exp (-(40 * C * Real.log X / d)) ≤
      ‖riemannHeat t s‖ := by
    have hp : (d / 2) ^ (∑ a ∈ T, m a) ≤ ‖∏ a ∈ T, (s - c - a) ^ m a‖ := by
      rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_le_prod (fun a _ => by positivity) (fun a ha => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (by positivity) (hfar a ha) _)
    have hgmin' := hgmin (s - c) hs17
    rw [← hsum] at hgmin'
    have hmin := mul_le_mul hp hgmin' (by positivity) (norm_nonneg _)
    rw [← norm_mul, ← hfac, show f (s - c) = riemannHeat t s by simp only [f, hsc]] at hmin
    have he := degree_floor_le hd hd1 hC.le hL.le hcount
    have hpaid := mul_le_mul_of_nonneg_left he (show 0 ≤ ‖xiLine X 16‖ / 8 by positivity)
    refine hpaid.trans ?_
    convert hmin using 1
    rw [show d / 36 = (d / 2) / 18 by ring, div_pow]
    ring
  refine ⟨hsne, hq, hfloor, ?_⟩
  intro u hu
  have hcofree : ∀ w : ℂ, ‖w - (s - c)‖ ≤ 4 * (1 / 32 : ℝ) → g w ≠ 0 := by
    intro w hw
    have htri := norm_le_norm_sub_add w (s - c)
    apply hgfree w
    linarith only [htri, hw, hsnear, hd2]
  have hcoq : ∀ w : ℂ, ‖w - (s - c)‖ ≤ 4 * (1 / 32 : ℝ) →
      ‖deriv (fun v => deriv g v / g v) w‖ ≤ C * Real.log X := by
    intro w hw
    have htri := norm_le_norm_sub_add w (s - c)
    apply hgq' w
    linarith only [htri, hw, hsnear, hd2]
  have herror := norm_centered_factorization_sub_one_le
    (s := s - c) (a := deriv (riemannHeat t) s / riemannHeat t s)
    (by positivity : 0 < d / 2) (by norm_num : (0 : ℝ) < 1 / 32) hCL
    hgdiff hcofree hcoq hfac hfar hsplit hu
  have hshift : f (s - c + u) = riemannHeat t (s + u) := by
    dsimp [f]
    congr 1
    ring
  rw [hshift, show f (s - c) = riemannHeat t s by simp only [f, hsc]] at herror
  refine herror.trans (sub_le_sub_right (Real.exp_le_exp.mpr ?_) 1)
  have hd2one : d ^ 2 ≤ 1 := by nlinarith only [hd1, hd]
  have hCLd : C * Real.log X * d ^ 2 ≤ C * Real.log X := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hd2one hCL.le
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg u)
  apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
  have hnpaid := mul_le_mul_of_nonneg_right hcount (by norm_num : (0 : ℝ) ≤ 8)
  have he : (2 * ((∑ a ∈ T, m a : ℕ) : ℝ) / (d / 2) ^ 2 + C * Real.log X) * d ^ 2 =
      8 * ((∑ a ∈ T, m a : ℕ) : ℝ) + C * Real.log X * d ^ 2 := by
    field_simp
    ring
  rw [he]
  nlinarith only [hnpaid, hCLd, hCL.le]

end

end RHTower.DeBruijn
