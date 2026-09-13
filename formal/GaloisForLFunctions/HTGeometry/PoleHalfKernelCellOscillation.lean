import GaloisForLFunctions.HTGeometry.PoleClearedHalfKernel

/-!
# Upper bounds for the pole-cleared half kernel

The kernel's variation on a positive cell is dominated by an inverse-square-root
difference. Subtracting the old atoms' right-endpoint values yields a finite-packet
absolute-mass bound that retains the baseline exactly.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem poleClearedHalfKernel_sub_upper {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    poleClearedHalfKernel x - poleClearedHalfKernel y ≤
      Real.exp y * (x ^ (-(1 : ℝ) / 2) - y ^ (-(1 : ℝ) / 2)) := by
  let f := fun t => poleClearedHalfKernel t - Real.exp y * t ^ (-(1 : ℝ) / 2)
  have hd : ∀ t ∈ Icc x y, HasDerivAt f
      ((1 / 2 : ℝ) * (Real.exp y - Real.exp t) * t ^ (-(3 : ℝ) / 2)) t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hx ht.1
    have h := (hasDerivAt_poleClearedHalfKernel ht0).sub
      ((Real.hasDerivAt_rpow_const (p := -(1 : ℝ) / 2) (Or.inl ht0.ne')).const_mul (Real.exp y))
    convert h using 1 <;> try rfl
    rw [show -(1 : ℝ) / 2 - 1 = -(3 : ℝ) / 2 by ring]
    ring
  have hmono : MonotoneOn f (Icc x y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc x y)
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Icc x y := interior_subset ht
      rw [(hd t ht').deriv]
      exact mul_nonneg (mul_nonneg (by norm_num)
        (sub_nonneg.mpr (Real.exp_le_exp.mpr ht'.2)))
        (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hx ht'.1)) _)
  have h := hmono (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy
  dsimp [f] at h
  linarith

theorem abs_poleHalfKernel_primitive_le {t : ℝ} (ht : 0 ≤ t) :
    |∫ u in (0 : ℝ)..t, poleHalfKernel u| ≤
      2 * Real.exp t * t ^ ((1 : ℝ) / 2) := by
  have hp : IntervalIntegrable (fun u : ℝ => u ^ (-(1 : ℝ) / 2)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h := intervalIntegral.integral_mono_on_of_le_Ioo ht
    (intervalIntegrable_poleHalfKernel 0 t).abs (hp.const_mul (Real.exp t)) (fun u hu => by
      rw [poleHalfKernel, abs_of_nonneg (mul_nonneg (Real.exp_pos u).le (Real.rpow_nonneg hu.1.le _))]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hu.2.le) (Real.rpow_nonneg hu.1.le _))
  have hi := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := poleHalfKernel) ht
  apply (hi.trans h).trans_eq
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num : -(1 : ℝ) < -1 / 2))]
  norm_num
  ring

theorem abs_poleClearedHalfKernel_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |poleClearedHalfKernel t| ≤ 3 * Real.exp t * t ^ (-(1 : ℝ) / 2) := by
  have hq : t * t ^ (-(1 : ℝ) / 2) = t ^ ((1 : ℝ) / 2) := by
    calc
      t * t ^ (-(1 : ℝ) / 2) = t ^ (1 : ℝ) * t ^ (-(1 : ℝ) / 2) := by
        rw [Real.rpow_one]
      _ = t ^ ((1 : ℝ) / 2) := by rw [← Real.rpow_add ht]; norm_num
  have hk : |poleHalfKernel t| = Real.exp t * t ^ (-(1 : ℝ) / 2) := by
    exact abs_of_nonneg (mul_nonneg (Real.exp_pos t).le (Real.rpow_nonneg ht.le _))
  have hi := abs_poleHalfKernel_primitive_le ht.le
  rw [← hq] at hi
  have h := abs_sub (poleHalfKernel t) (∫ u in (0 : ℝ)..t, poleHalfKernel u)
  rw [hk] at h
  have hm := mul_le_mul_of_nonneg_right ht1
    (show 0 ≤ 2 * Real.exp t * t ^ (-(1 : ℝ) / 2) by positivity)
  dsimp only [poleClearedHalfKernel]
  nlinarith

theorem integral_abs_poleClearedHalfKernel_le {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    (∫ t in (0 : ℝ)..d, |poleClearedHalfKernel t|) ≤
      6 * Real.exp d * d ^ ((1 : ℝ) / 2) := by
  have hp : IntervalIntegrable (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) volume 0 d :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hd.le
    (intervalIntegrable_poleClearedHalfKernel 0 d).abs (hp.const_mul (3 * Real.exp d))
    (fun t ht => (abs_poleClearedHalfKernel_le ht.1 (ht.2.le.trans hd1)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ht.2.le) (by norm_num))
        (Real.rpow_nonneg ht.1.le _)))
  apply h.trans_eq
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num : -(1 : ℝ) < -1 / 2))]
  norm_num
  ring

theorem poleClearedHalfKernel_cell_difference {a d x : ℝ} (ha : 0 < a)
    (hx : x ∈ Ioo 0 d) :
    |poleClearedHalfKernel (x + a) - poleClearedHalfKernel (d + a)| ≤
      Real.exp (d + a) * (a ^ (-(1 : ℝ) / 2) - (d + a) ^ (-(1 : ℝ) / 2)) := by
  have hanti := strictAntiOn_poleClearedHalfKernel.antitoneOn
  have hxa : 0 < x + a := add_pos hx.1 ha
  have hda : 0 < d + a := by linarith [hx.2]
  have hn := hanti hxa hda (by linarith [hx.2] : x + a ≤ d + a)
  rw [abs_of_nonneg (sub_nonneg.mpr hn)]
  have hax := hanti ha hxa (by linarith [hx.1] : a ≤ x + a)
  exact (sub_le_sub_right hax _).trans
    (poleClearedHalfKernel_sub_upper ha (by linarith [hx.1, hx.2]))

theorem intervalIntegrable_poleClearedHalfPacket {ι : Type*}
    (S : Finset ι) (a c : ι → ℝ) (d : ℝ) :
    IntervalIntegrable (fun x => ∑ i ∈ S, c i * poleClearedHalfKernel (x + a i))
      volume 0 d := by
  have heq : (fun x => ∑ i ∈ S, c i * poleClearedHalfKernel (x + a i)) =
      ∑ i ∈ S, (fun x => c i * poleClearedHalfKernel (x + a i)) := by
    funext x
    simp only [Finset.sum_apply]
  rw [heq]
  apply IntervalIntegrable.sum S
  intro i _
  have h := (intervalIntegrable_poleClearedHalfKernel (a i) (d + a i)).comp_add_right (a i)
  have h' : IntervalIntegrable (fun x => poleClearedHalfKernel (x + a i)) volume 0 d := by
    convert h using 1 <;> ring
  exact h'.const_mul (c i)

theorem poleClearedHalfPacket_remainder_mass_upper {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a c : ι → ℝ) {j : ι} (hj : j ∈ S)
    (ha : ∀ i ∈ S.erase j, 0 < a i) (hc : ∀ i ∈ S, 0 ≤ c i) (haj : a j = 0)
    {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    (∫ x in (0 : ℝ)..d,
      |(∑ i ∈ S, c i * poleClearedHalfKernel (x + a i)) -
        ∑ i ∈ S.erase j, c i * poleClearedHalfKernel (d + a i)|) ≤
      6 * c j * Real.exp d * d ^ ((1 : ℝ) / 2) +
        d * ∑ i ∈ S.erase j, c i * Real.exp (d + a i) *
          (a i ^ (-(1 : ℝ) / 2) - (d + a i) ^ (-(1 : ℝ) / 2)) := by
  let B := ∑ i ∈ S.erase j, c i * Real.exp (d + a i) *
    (a i ^ (-(1 : ℝ) / 2) - (d + a i) ^ (-(1 : ℝ) / 2))
  have hp := intervalIntegrable_poleClearedHalfPacket S a c d
  have hmaj : ∀ x ∈ Ioo 0 d,
      |(∑ i ∈ S, c i * poleClearedHalfKernel (x + a i)) -
        ∑ i ∈ S.erase j, c i * poleClearedHalfKernel (d + a i)| ≤
          c j * |poleClearedHalfKernel x| + B := by
    intro x hx
    have heq : (∑ i ∈ S, c i * poleClearedHalfKernel (x + a i)) -
        ∑ i ∈ S.erase j, c i * poleClearedHalfKernel (d + a i) =
      c j * poleClearedHalfKernel x + ∑ i ∈ S.erase j,
        c i * (poleClearedHalfKernel (x + a i) - poleClearedHalfKernel (d + a i)) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_erase_add _ _ hj, haj, add_zero]
      ring
    rw [heq]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_of_nonneg (hc j hj)]
    apply add_le_add le_rfl
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    rw [abs_mul, abs_of_nonneg (hc i (Finset.mem_of_mem_erase hi))]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (poleClearedHalfKernel_cell_difference (ha i hi) hx)
      (hc i (Finset.mem_of_mem_erase hi))
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hd.le
    (hp.sub intervalIntegrable_const).abs
    (((intervalIntegrable_poleClearedHalfKernel 0 d).abs.const_mul (c j)).add
      intervalIntegrable_const) hmaj
  rw [intervalIntegral.integral_add
      ((intervalIntegrable_poleClearedHalfKernel 0 d).abs.const_mul (c j))
      intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul] at h
  have hk := mul_le_mul_of_nonneg_left
    (integral_abs_poleClearedHalfKernel_le hd hd1) (hc j hj)
  dsimp only [B] at h
  nlinarith

end GaloisForLFunctions.HTGeometry

