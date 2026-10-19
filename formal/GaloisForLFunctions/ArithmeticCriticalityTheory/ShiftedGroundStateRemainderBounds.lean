import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStatePotentialBounds
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateOriginFailure

/-!
# Integral bounds and measurability of the ground remainder of the shifted ground states

For `u` continuous with `|u| ≤ M_u`, Lipschitz constant `L_u` and support in `[−R, R]`, `R ≥ 1`, the
ground remainder `rem_a(t) = 2∫_{x>0} S_a(t,x) dx + ∫_0^t R_a(t,x) dx` of `ω_a` satisfies

    |rem_a(t)| ≤ (2 Φ(0)² (L_u² + 4 M_u²) R + 4 Φ(0)² M_u²) t          (t > 0),
    |rem_a(t)| ≤ 16 Φ(0) M_u² R Φ(t − R − a)                           (t ≥ R + a),

and `t ↦ rem(t)` is measurable for every continuous `ω`, `u`. The same-side jump is supported in
`x ≤ R`; the reflected jump on the collar `0 < x < t` is supported in `x ≤ R` or `x ≥ t − R`, two
intervals of length at most `R`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### Integrals of functions dominated by indicators of bounded intervals -/

theorem integral_Ioi_norm_le_of_le_indicator {f : ℝ → ℝ} {C R : ℝ} (hR : 0 ≤ R)
    (hf : ∀ x, 0 < x → |f x| ≤ C * (if x ≤ R then 1 else 0)) :
    ∫ x in Ioi (0 : ℝ), ‖f x‖ ≤ C * R := by
  have hg0 : IntegrableOn (fun _ : ℝ => C) (Ioc (0 : ℝ) R) := integrableOn_const measure_Ioc_lt_top.ne
  have hg : Integrable ((Ioc (0 : ℝ) R).indicator fun _ => C) (volume.restrict (Ioi 0)) :=
    (hg0.integrable_indicator measurableSet_Ioc).integrableOn
  have hle : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖f x‖ ≤ (Ioc (0 : ℝ) R).indicator (fun _ => C) x :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => by
      have h := hf x hx
      rw [Real.norm_eq_abs, Set.indicator_apply]
      by_cases hxR : x ≤ R
      · rw [if_pos hxR, mul_one] at h
        rw [if_pos ⟨hx, hxR⟩]
        exact h
      · rw [if_neg hxR, mul_zero] at h
        rw [if_neg fun hm => hxR hm.2]
        exact h
  calc ∫ x in Ioi (0 : ℝ), ‖f x‖
      ≤ ∫ x in Ioi (0 : ℝ), (Ioc (0 : ℝ) R).indicator (fun _ => C) x :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) hg hle
    _ = C * R := by
        rw [setIntegral_indicator measurableSet_Ioc, setIntegral_const, smul_eq_mul,
          Set.inter_eq_right.mpr Set.Ioc_subset_Ioi_self, Real.volume_real_Ioc, sub_zero,
          max_eq_left hR, mul_comm]

theorem abs_integral_Ioi_le_of_le_indicator {f : ℝ → ℝ} {C R : ℝ} (hR : 0 ≤ R)
    (hf : ∀ x, 0 < x → |f x| ≤ C * (if x ≤ R then 1 else 0)) :
    |∫ x in Ioi (0 : ℝ), f x| ≤ C * R := by
  have h := norm_integral_le_integral_norm (μ := volume.restrict (Ioi (0 : ℝ))) f
  rw [Real.norm_eq_abs] at h
  exact h.trans (integral_Ioi_norm_le_of_le_indicator hR hf)

theorem abs_integral_Ioo_le_of_le_two_indicators {f : ℝ → ℝ} {C R t : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hf : ∀ x, 0 < x → x < t →
      |f x| ≤ C * ((if x ≤ R then 1 else 0) + (if t - R ≤ x then 1 else 0))) :
    |∫ x in Ioo (0 : ℝ) t, f x| ≤ C * (2 * R) := by
  have hc1 : IntegrableOn (fun _ : ℝ => C) (Ioo (0 : ℝ) t) := integrableOn_const measure_Ioo_lt_top.ne
  have hg1 : IntegrableOn ((Iic R).indicator fun _ => C) (Ioo (0 : ℝ) t) :=
    hc1.indicator measurableSet_Iic
  have hg2 : IntegrableOn ((Ici (t - R)).indicator fun _ => C) (Ioo (0 : ℝ) t) :=
    hc1.indicator measurableSet_Ici
  have hle : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) t)), ‖f x‖ ≤
      (Iic R).indicator (fun _ => C) x + (Ici (t - R)).indicator (fun _ => C) x :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun x hx => by
      have h := hf x hx.1 hx.2
      rw [Real.norm_eq_abs]
      simp only [Set.indicator_apply, mem_Iic, mem_Ici]
      split_ifs at h ⊢ <;> linarith
  have hint : |∫ x in Ioo (0 : ℝ) t, f x| ≤
      ∫ x in Ioo (0 : ℝ) t,
        ((Iic R).indicator (fun _ => C) x + (Ici (t - R)).indicator (fun _ => C) x) := by
    have := norm_integral_le_of_norm_le (hg1.add hg2) hle
    rwa [Real.norm_eq_abs] at this
  refine hint.trans ?_
  rw [integral_add hg1 hg2, setIntegral_indicator measurableSet_Iic,
    setIntegral_indicator measurableSet_Ici, setIntegral_const, setIntegral_const, smul_eq_mul,
    smul_eq_mul]
  have hm1 : volume.real (Ioo (0 : ℝ) t ∩ Iic R) ≤ R := by
    have := measureReal_mono (μ := volume)
      (show Ioo (0 : ℝ) t ∩ Iic R ⊆ Ioc 0 R from fun x hx => ⟨hx.1.1, hx.2⟩) measure_Ioc_lt_top.ne
    rwa [Real.volume_real_Ioc, sub_zero, max_eq_left hR] at this
  have hm2 : volume.real (Ioo (0 : ℝ) t ∩ Ici (t - R)) ≤ R := by
    have := measureReal_mono (μ := volume)
      (show Ioo (0 : ℝ) t ∩ Ici (t - R) ⊆ Icc (t - R) t from fun x hx => ⟨hx.2, hx.1.2.le⟩)
      measure_Icc_lt_top.ne
    rwa [Real.volume_real_Icc, show t - (t - R) = R by ring, max_eq_left hR] at this
  have e1 := mul_le_mul_of_nonneg_right hm1 hC
  have e2 := mul_le_mul_of_nonneg_right hm2 hC
  linarith

/-! ### Bounds on the ground remainder of the shifted ground states -/

/-- Linear bound of the ground remainder of `ω_a` in the shift. -/
theorem abs_groundRemainderShift_shiftedGroundState_le_linear {a R Mu Lu : ℝ} (hR : 1 ≤ R)
    {u : ℝ → ℝ} (hsupp : ∀ x, R < |x| → u x = 0) (hMu : ∀ x, |u x| ≤ Mu)
    (hLu : ∀ x y, |u y - u x| ≤ Lu * |y - x|) {t : ℝ} (ht0 : 0 < t) :
    |groundRemainderShift (shiftedGroundState a) u t| ≤
      (2 * (riemannKernelReal 0 ^ 2 * (Lu ^ 2 + 4 * Mu ^ 2) * R) +
        4 * riemannKernelReal 0 ^ 2 * Mu ^ 2) * t := by
  unfold groundRemainderShift
  have h1 : |∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x| ≤
      riemannKernelReal 0 ^ 2 * (Lu ^ 2 + 4 * Mu ^ 2) * t * R :=
    abs_integral_Ioi_le_of_le_indicator (by linarith) fun x hx =>
      sameSideGroundJump_shiftedGroundState_abs_le_linear hsupp hMu hLu hx ht0
  have h2 : |∫ x in Ioo (0 : ℝ) t, reflectedGroundJump (shiftedGroundState a) u t x| ≤
      4 * riemannKernelReal 0 ^ 2 * Mu ^ 2 * t := by
    have hb : ∀ x ∈ Ioo (0 : ℝ) t, ‖reflectedGroundJump (shiftedGroundState a) u t x‖ ≤
        4 * riemannKernelReal 0 ^ 2 * Mu ^ 2 := fun x _ => by
      rw [Real.norm_eq_abs]
      exact reflectedGroundJump_shiftedGroundState_abs_le hMu t x
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Ioo_lt_top hb
    rwa [Real.norm_eq_abs, Real.volume_real_Ioo, sub_zero, max_eq_left ht0.le] at this
  calc |2 * (∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x) +
        ∫ x in Ioo (0 : ℝ) t, reflectedGroundJump (shiftedGroundState a) u t x|
      ≤ 2 * |∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x| +
        |∫ x in Ioo (0 : ℝ) t, reflectedGroundJump (shiftedGroundState a) u t x| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_two]
    _ ≤ _ := by linarith

/-- Decay bound of the ground remainder of `ω_a` beyond the support. -/
theorem abs_groundRemainderShift_shiftedGroundState_le_decay {a R Mu : ℝ} (ha : 0 < a) (hR : 1 ≤ R)
    {u : ℝ → ℝ} (hsupp : ∀ x, R < |x| → u x = 0) (hMu : ∀ x, |u x| ≤ Mu)
    {t : ℝ} (ht : R + a ≤ t) :
    |groundRemainderShift (shiftedGroundState a) u t| ≤
      16 * riemannKernelReal 0 * Mu ^ 2 * R * riemannKernelReal (t - R - a) := by
  unfold groundRemainderShift
  have hΘ0 := (riemannKernelReal_pos 0).le
  have hK := (riemannKernelReal_pos (t - R - a)).le
  have hC : 0 ≤ 4 * riemannKernelReal 0 * Mu ^ 2 * riemannKernelReal (t - R - a) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hΘ0) (sq_nonneg _)) hK
  have h1 : |∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x| ≤
      4 * riemannKernelReal 0 * Mu ^ 2 * riemannKernelReal (t - R - a) * R :=
    abs_integral_Ioi_le_of_le_indicator (by linarith) fun x hx =>
      sameSideGroundJump_shiftedGroundState_abs_le_decay ha hR hsupp hMu hx ht
  have h2 : |∫ x in Ioo (0 : ℝ) t, reflectedGroundJump (shiftedGroundState a) u t x| ≤
      4 * riemannKernelReal 0 * Mu ^ 2 * riemannKernelReal (t - R - a) * (2 * R) :=
    abs_integral_Ioo_le_of_le_two_indicators hC (by linarith) fun x hx hxt =>
      reflectedGroundJump_shiftedGroundState_abs_le_decay ha hsupp hMu hx hxt ht
  calc |2 * (∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x) +
        ∫ x in Ioo (0 : ℝ) t, reflectedGroundJump (shiftedGroundState a) u t x|
      ≤ 2 * |∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x| +
        |∫ x in Ioo (0 : ℝ) t, reflectedGroundJump (shiftedGroundState a) u t x| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_two]
    _ ≤ _ := by linarith

/-- A function linearly bounded on `(0, ∞)` and `Φ(t − R − a)`-bounded beyond `R + a` is
`Φ(t − R − a)`-bounded on all of `(0, ∞)`. -/
theorem abs_le_decay_of_linear_of_decay {g : ℝ → ℝ} {a R Cl Cd : ℝ} (ha : 0 < a) (hR : 0 ≤ R)
    (hCl : 0 ≤ Cl)
    (hlin : ∀ t, 0 < t → |g t| ≤ Cl * t)
    (hdec : ∀ t, R + a ≤ t → |g t| ≤ Cd * riemannKernelReal (t - R - a)) {t : ℝ} (ht : 0 < t) :
    |g t| ≤ max Cd (Cl * (R + a) / riemannKernelReal (R + a)) * riemannKernelReal (t - R - a) := by
  have hK := (riemannKernelReal_pos (t - R - a)).le
  rcases le_or_gt (R + a) t with h | h
  · exact (hdec t h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hK)
  · have hΦ : riemannKernelReal (R + a) ≤ riemannKernelReal (t - R - a) := by
      have := riemannKernelReal_sub_ge_of_le ht.le h.le
      rwa [← sub_sub] at this
    have hΦpos := riemannKernelReal_pos (R + a)
    calc |g t| ≤ Cl * t := hlin t ht
      _ ≤ Cl * (R + a) := mul_le_mul_of_nonneg_left h.le hCl
      _ = Cl * (R + a) / riemannKernelReal (R + a) * riemannKernelReal (R + a) := by
          field_simp
      _ ≤ Cl * (R + a) / riemannKernelReal (R + a) * riemannKernelReal (t - R - a) :=
          mul_le_mul_of_nonneg_left hΦ (div_nonneg (mul_nonneg hCl (by linarith)) hΦpos.le)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hK

/-! ### Joint continuity and measurability -/

theorem continuous_sameSideGroundJump_uncurry {ω u : ℝ → ℝ} (hω : Continuous ω)
    (hu : Continuous u) : Continuous fun p : ℝ × ℝ => sameSideGroundJump ω u p.1 p.2 := by
  unfold sameSideGroundJump
  have hΘ := continuous_riemannKernelReal
  have h1 : Continuous fun p : ℝ × ℝ => p.2 + p.1 := continuous_snd.add continuous_fst
  exact ((((hΘ.comp continuous_snd).mul (hΘ.comp h1)).mul (hω.comp continuous_snd)).mul
    (hω.comp h1)).mul (((hu.comp continuous_snd).sub (hu.comp h1)).pow 2)

theorem continuous_reflectedGroundJump_uncurry {ω u : ℝ → ℝ} (hω : Continuous ω)
    (hu : Continuous u) : Continuous fun p : ℝ × ℝ => reflectedGroundJump ω u p.1 p.2 := by
  unfold reflectedGroundJump
  have hΘ := continuous_riemannKernelReal
  have h1 : Continuous fun p : ℝ × ℝ => p.1 - p.2 := continuous_fst.sub continuous_snd
  exact ((((hΘ.comp continuous_snd).mul (hΘ.comp h1)).mul (hω.comp continuous_snd)).mul
    (hω.comp h1)).mul (((hu.comp continuous_snd).add (hu.comp h1)).pow 2)

theorem continuous_foldedShiftGenerator_uncurry {ω : ℝ → ℝ} (hω : Continuous ω) :
    Continuous fun p : ℝ × ℝ => foldedShiftGenerator ω p.1 p.2 := by
  unfold foldedShiftGenerator
  have hΘ := continuous_riemannKernelReal
  have h1 : Continuous fun p : ℝ × ℝ => p.2 + p.1 := continuous_snd.add continuous_fst
  have h2 : Continuous fun p : ℝ × ℝ => p.2 - p.1 := continuous_snd.sub continuous_fst
  exact (hΘ.comp continuous_snd).mul
    (((hΘ.comp h1).mul ((hω.comp continuous_snd).sub (hω.comp h1))).add
      ((hΘ.comp h2).mul ((hω.comp continuous_snd).sub (hω.comp h2.abs))))

theorem continuous_groundPotentialDensity_uncurry {ω u : ℝ → ℝ} (hω : Continuous ω)
    (hu : Continuous u) : Continuous fun p : ℝ × ℝ => groundPotentialDensity ω u p.1 p.2 := by
  unfold groundPotentialDensity
  exact (((hu.comp continuous_snd).pow 2).mul (hω.comp continuous_snd)).mul
    (continuous_foldedShiftGenerator_uncurry hω)

/-- The ground remainder is a measurable function of the shift. -/
theorem measurable_groundRemainderShift {ω u : ℝ → ℝ} (hω : Continuous ω) (hu : Continuous u) :
    Measurable (groundRemainderShift ω u) := by
  have hs : Measurable fun t => ∫ x in Ioi (0 : ℝ), sameSideGroundJump ω u t x :=
    ((continuous_sameSideGroundJump_uncurry hω hu).stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioi 0))).measurable
  have hr : Measurable fun t => ∫ x in Ioo (0 : ℝ) t, reflectedGroundJump ω u t x := by
    have hF : Measurable fun p : ℝ × ℝ =>
        if 0 < p.2 ∧ p.2 < p.1 then reflectedGroundJump ω u p.1 p.2 else 0 := by
      refine Measurable.ite ?_ (continuous_reflectedGroundJump_uncurry hω hu).measurable
        measurable_const
      rw [Set.setOf_and]
      exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_fst)
    have h := (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
    have heq : (fun t => ∫ x in Ioo (0 : ℝ) t, reflectedGroundJump ω u t x) =
        fun t => ∫ x, (if 0 < x ∧ x < t then reflectedGroundJump ω u t x else 0) := by
      funext t
      rw [← integral_indicator measurableSet_Ioo]
      congr 1
      funext x
      simp only [Set.indicator_apply, mem_Ioo]
    rw [heq]
    exact h
  show Measurable fun t => 2 * (∫ x in Ioi (0 : ℝ), sameSideGroundJump ω u t x) +
    ∫ x in Ioo (0 : ℝ) t, reflectedGroundJump ω u t x
  exact (hs.const_mul 2).add hr

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
