import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Pole-cleared half-order kernel and absolute cell mass

The difference between `exp(t) * t^(-1/2)` and its primitive is locally integrable.
It is strictly decreasing on the positive ray, as is its remainder after subtracting
`t^(-1/2)`. This forces an absolute-mass lower bound for every positive finite packet
of delayed kernels, independently of the signs of the complete packet values.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

def poleHalfKernel (t : ℝ) : ℝ := Real.exp t * t ^ (-(1 : ℝ) / 2)

def poleClearedHalfKernel (t : ℝ) : ℝ :=
  poleHalfKernel t - ∫ u in (0 : ℝ)..t, poleHalfKernel u

theorem intervalIntegrable_poleHalfKernel (a b : ℝ) :
    IntervalIntegrable poleHalfKernel volume a b := by
  exact (intervalIntegral.intervalIntegrable_rpow' (by norm_num : -(1 : ℝ) < -1 / 2)).continuousOn_mul
    Real.continuous_exp.continuousOn

theorem measurable_poleHalfKernel : Measurable poleHalfKernel := by
  unfold poleHalfKernel
  fun_prop

theorem continuous_poleHalfKernel_primitive :
    Continuous (fun t => ∫ u in (0 : ℝ)..t, poleHalfKernel u) :=
  intervalIntegral.continuous_primitive intervalIntegrable_poleHalfKernel 0

theorem intervalIntegrable_poleClearedHalfKernel (a b : ℝ) :
    IntervalIntegrable poleClearedHalfKernel volume a b :=
  (intervalIntegrable_poleHalfKernel a b).sub
    (continuous_poleHalfKernel_primitive.intervalIntegrable a b)

theorem hasDerivAt_poleHalfKernel {t : ℝ} (ht : 0 < t) :
    HasDerivAt poleHalfKernel
      (poleHalfKernel t - (1 / 2 : ℝ) * Real.exp t * t ^ (-(3 : ℝ) / 2)) t := by
  have h := (Real.hasDerivAt_exp t).mul
    (Real.hasDerivAt_rpow_const (p := -(1 : ℝ) / 2) (Or.inl ht.ne'))
  convert h using 1 <;> try rfl
  dsimp [poleHalfKernel]
  rw [show -(1 : ℝ) / 2 - 1 = -(3 : ℝ) / 2 by ring]
  ring

theorem hasDerivAt_poleClearedHalfKernel {t : ℝ} (ht : 0 < t) :
    HasDerivAt poleClearedHalfKernel
      (-(1 / 2 : ℝ) * Real.exp t * t ^ (-(3 : ℝ) / 2)) t := by
  have hk := hasDerivAt_poleHalfKernel ht
  have hi := intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_poleHalfKernel 0 t)
    measurable_poleHalfKernel.stronglyMeasurable.stronglyMeasurableAtFilter
    hk.continuousAt
  convert hk.sub hi using 1 <;> try rfl
  ring

theorem hasDerivAt_poleClearedHalfKernel_corrected {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun u => poleClearedHalfKernel u + (1 / 2 : ℝ) * Real.exp u * u ^ (-(3 : ℝ) / 2))
      (-(3 / 4 : ℝ) * Real.exp t * t ^ (-(5 : ℝ) / 2)) t := by
  have h := (hasDerivAt_poleClearedHalfKernel ht).add
    (((Real.hasDerivAt_exp t).const_mul (1 / 2 : ℝ)).mul
      (Real.hasDerivAt_rpow_const (p := -(3 : ℝ) / 2) (Or.inl ht.ne')))
  convert h using 1 <;> try rfl
  rw [show -(3 : ℝ) / 2 - 1 = -(5 : ℝ) / 2 by ring]
  ring

theorem strictAntiOn_poleClearedHalfKernel :
    StrictAntiOn poleClearedHalfKernel (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ))
  · intro t ht
    exact (hasDerivAt_poleClearedHalfKernel ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht0 : 0 < t := interior_subset ht
    rw [(hasDerivAt_poleClearedHalfKernel ht0).deriv]
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) (Real.exp_pos t)) (Real.rpow_pos_of_pos ht0 _)

theorem hasDerivAt_poleClearedHalfKernel_regularPart {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => poleClearedHalfKernel u - u ^ (-(1 : ℝ) / 2))
      (-(1 / 2 : ℝ) * (Real.exp t - 1) * t ^ (-(3 : ℝ) / 2)) t := by
  have h := (hasDerivAt_poleClearedHalfKernel ht).sub
    (Real.hasDerivAt_rpow_const (p := -(1 : ℝ) / 2) (Or.inl ht.ne'))
  convert h using 1 <;> try rfl
  rw [show -(1 : ℝ) / 2 - 1 = -(3 : ℝ) / 2 by ring]
  ring

theorem strictAntiOn_poleClearedHalfKernel_regularPart :
    StrictAntiOn (fun u => poleClearedHalfKernel u - u ^ (-(1 : ℝ) / 2)) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ))
  · intro t ht
    exact (hasDerivAt_poleClearedHalfKernel_regularPart ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht0 : 0 < t := interior_subset ht
    rw [(hasDerivAt_poleClearedHalfKernel_regularPart ht0).deriv]
    have he : 0 < Real.exp t - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr ht0)
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) he) (Real.rpow_pos_of_pos ht0 _)

theorem poleClearedHalfKernel_sub_lower {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    x ^ (-(1 : ℝ) / 2) - y ^ (-(1 : ℝ) / 2) ≤
      poleClearedHalfKernel x - poleClearedHalfKernel y := by
  have h := strictAntiOn_poleClearedHalfKernel_regularPart.antitoneOn
    hx (lt_of_lt_of_le hx hxy) hxy
  linarith

theorem poleClearedHalfKernel_upper {t : ℝ} (ht : 1 ≤ t) :
    poleClearedHalfKernel t ≤
      poleClearedHalfKernel 1 + Real.exp 1 / 2 -
        (1 / 2 : ℝ) * Real.exp t * t ^ (-(3 : ℝ) / 2) := by
  have hanti : StrictAntiOn
      (fun u => poleClearedHalfKernel u + (1 / 2 : ℝ) * Real.exp u * u ^ (-(3 : ℝ) / 2))
      (Ioi 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ))
    · intro u hu
      exact (hasDerivAt_poleClearedHalfKernel_corrected hu).continuousAt.continuousWithinAt
    · intro u hu
      have hu0 : 0 < u := interior_subset hu
      rw [(hasDerivAt_poleClearedHalfKernel_corrected hu0).deriv]
      exact mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (by norm_num) (Real.exp_pos u)) (Real.rpow_pos_of_pos hu0 _)
  have h := hanti.antitoneOn (by norm_num : (1 : ℝ) ∈ Ioi 0)
    (show t ∈ Ioi 0 from lt_of_lt_of_le zero_lt_one ht) ht
  simp only [Real.one_rpow, mul_one] at h
  linarith

end GaloisForLFunctions.HTGeometry


open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem halfSingular_absolute_mass_lower {f : ℝ → ℝ} {c d : ℝ} (hd : 0 < d)
    (hf : IntervalIntegrable f volume 0 d)
    (hgap : ∀ x ∈ Ioo 0 (d / 2),
      c * (x ^ (-(1 : ℝ) / 2) - (d - x) ^ (-(1 : ℝ) / 2)) ≤ f x - f (d - x)) :
    c * (4 * (d / 2) ^ ((1 : ℝ) / 2) - 2 * d ^ ((1 : ℝ) / 2)) ≤
      ∫ x in (0 : ℝ)..d, |f x| := by
  have hd0 : 0 ≤ d := hd.le
  have hmid : 0 ≤ d / 2 := by positivity
  have hmid1 : d / 2 ≤ d := by linarith
  have hleft : IntervalIntegrable f volume 0 (d / 2) :=
    hf.mono_set (Set.uIcc_subset_uIcc (by simp) (by simpa [Set.uIcc_of_le hd0] using
      (show d / 2 ∈ Icc 0 d from ⟨hmid, hmid1⟩)))
  have hright : IntervalIntegrable f volume (d / 2) d :=
    hf.mono_set (Set.uIcc_subset_uIcc (by simpa [Set.uIcc_of_le hd0] using
      (show d / 2 ∈ Icc 0 d from ⟨hmid, hmid1⟩)) (by simp))
  have href : IntervalIntegrable (fun x => f (d - x)) volume 0 (d / 2) := by
    convert (hright.comp_sub_left d).symm using 1 <;> ring
  have hp : ∀ a b : ℝ, IntervalIntegrable (fun x : ℝ => x ^ (-(1 : ℝ) / 2)) volume a b :=
    fun _ _ => intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hpr : IntervalIntegrable (fun x : ℝ => (d - x) ^ (-(1 : ℝ) / 2))
      volume 0 (d / 2) := by
    convert ((hp (d / 2) d).comp_sub_left d).symm using 1 <;> ring
  have hle := intervalIntegral.integral_mono_on_of_le_Ioo hmid
    (((hp 0 (d / 2)).sub hpr).const_mul c) (hleft.abs.add href.abs)
    (fun x hx => (hgap x hx).trans (by linarith [le_abs_self (f x), neg_le_abs (f (d - x))]))
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hp 0 (d / 2)) hpr,
    intervalIntegral.integral_add hleft.abs href.abs] at hle
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-(1 : ℝ) / 2)),
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => |f x|)] at hle
  simp only [sub_zero, show d - d / 2 = d / 2 by ring] at hle
  rw [intervalIntegral.integral_add_adjacent_intervals hleft.abs hright.abs] at hle
  rw [integral_rpow (Or.inl (by norm_num : -(1 : ℝ) < -1 / 2)),
    integral_rpow (Or.inl (by norm_num : -(1 : ℝ) < -1 / 2))] at hle
  norm_num at hle
  convert hle using 1
  ring

theorem poleClearedHalfPacket_absolute_mass_lower {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a c : ι → ℝ) {j : ι} (hj : j ∈ S)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hc : ∀ i ∈ S, 0 ≤ c i) (haj : a j = 0)
    {d : ℝ} (hd : 0 < d) :
    c j * (4 * (d / 2) ^ ((1 : ℝ) / 2) - 2 * d ^ ((1 : ℝ) / 2)) ≤
      ∫ x in (0 : ℝ)..d, |∑ i ∈ S, c i * poleClearedHalfKernel (x + a i)| := by
  apply halfSingular_absolute_mass_lower hd
  · have hInt : ∀ i ∈ S,
        IntervalIntegrable (fun x => c i * poleClearedHalfKernel (x + a i)) volume 0 d := by
      intro i _
      have h := (intervalIntegrable_poleClearedHalfKernel (a i) (d + a i)).comp_add_right (a i)
      have h' : IntervalIntegrable (fun x => poleClearedHalfKernel (x + a i)) volume 0 d := by
        convert h using 1 <;> ring
      exact h'.const_mul (c i)
    have heq : (fun x => ∑ i ∈ S, c i * poleClearedHalfKernel (x + a i)) =
        ∑ i ∈ S, (fun x => c i * poleClearedHalfKernel (x + a i)) := by
      funext x
      simp only [Finset.sum_apply]
    rw [heq]
    exact IntervalIntegrable.sum S hInt
  · intro x hx
    have hxy : x ≤ d - x := by linarith [hx.2]
    have hn : ∀ i ∈ S,
        0 ≤ c i * (poleClearedHalfKernel (x + a i) -
          poleClearedHalfKernel (d - x + a i)) := by
      intro i hi
      apply mul_nonneg (hc i hi)
      exact sub_nonneg.mpr (strictAntiOn_poleClearedHalfKernel.antitoneOn
        (show x + a i ∈ Ioi 0 from add_pos_of_pos_of_nonneg hx.1 (ha i hi))
        (show d - x + a i ∈ Ioi 0 from by
          change 0 < d - x + a i
          linarith [ha i hi, hx.1, hx.2])
        (by linarith))
    have hsingle := Finset.single_le_sum hn hj
    have hroot := mul_le_mul_of_nonneg_left (poleClearedHalfKernel_sub_lower hx.1 hxy) (hc j hj)
    rw [haj, add_zero, add_zero] at hsingle
    apply (hroot.trans hsingle).trans_eq
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]

theorem halfSingular_massFactor_lower {d : ℝ} (hd : 0 ≤ d) :
    d ^ ((1 : ℝ) / 2) / 2 ≤
      4 * (d / 2) ^ ((1 : ℝ) / 2) - 2 * d ^ ((1 : ℝ) / 2) := by
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  have ha := Real.sq_sqrt (show 0 ≤ d / 2 by positivity)
  have hb := Real.sq_sqrt hd
  have hs : (5 * Real.sqrt d) ^ 2 ≤ (8 * Real.sqrt (d / 2)) ^ 2 := by nlinarith
  have hle := (sq_le_sq₀ (by positivity : 0 ≤ 5 * Real.sqrt d)
    (by positivity : 0 ≤ 8 * Real.sqrt (d / 2))).mp hs
  linarith

end GaloisForLFunctions.HTGeometry

