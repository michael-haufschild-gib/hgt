import GaloisForLFunctions.IncommensurableGaborPinching.CosineKernelNonLatticeFloor
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Additive rigidity of cosine-window kernel zeros

The cosine-window transform satisfies its polynomial closed-form identity at
every frequency, including the removable frequencies. Its zeros obey a
cotangent-line equation whose solution set contains no additive triple.
Compactness therefore supplies a positive triple floor at every fixed
nondegenerate cosine window, including cosine shape parameter four thirds.
-/

noncomputable section

open Real MeasureTheory

namespace GaloisForLFunctions.IncommensurableGaborPinching

/-- The polynomial transform identity holds at every frequency, without dividing by a frequency gap. -/
theorem mtKernelNum_closed_form_global (lam Δ : ℝ) :
    ((Real.pi * Δ) ^ 2 - (Zeta23.ThmD.theta lam) ^ 2) * mtKernelNum lam Δ =
      (Real.pi * Δ) * Real.cos (Zeta23.ThmD.theta lam) * Real.sin (Real.pi * Δ) -
        Zeta23.ThmD.theta lam * Real.sin (Zeta23.ThmD.theta lam) * Real.cos (Real.pi * Δ) := by
  let a := Zeta23.ThmD.theta lam
  let x := Real.pi * Δ
  have harg (v : ℝ) : Real.sqrt 2 * lam * v = 2 * a * v := by
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    dsimp [a, Zeta23.ThmD.theta]
    field_simp
    ring_nf
    rw [hs2]
    ring
  have hd (v : ℝ) : HasDerivAt
      (fun v => x * (Real.cos (2 * a * v) * Real.sin (2 * x * v)) -
        a * (Real.sin (2 * a * v) * Real.cos (2 * x * v)))
      (2 * (x ^ 2 - a ^ 2) * (Real.cos (2 * a * v) * Real.cos (2 * x * v))) v := by
    have ha := (hasDerivAt_id v).const_mul (2 * a)
    have hx := (hasDerivAt_id v).const_mul (2 * x)
    apply (((ha.cos.mul hx.sin).const_mul x).sub ((ha.sin.mul hx.cos).const_mul a)).congr_deriv
    simp only [id_eq]
    ring
  have hc : Continuous (fun v : ℝ =>
      2 * (x ^ 2 - a ^ 2) * (Real.cos (2 * a * v) * Real.cos (2 * x * v))) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -(1 : ℝ) / 2) (b := 1 / 2) (fun v _ => hd v) (hc.intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul] at h
  have hp : (∫ v in (-(1 : ℝ) / 2)..(1 / 2),
      Real.cos (2 * a * v) * Real.cos (2 * x * v)) = mtKernelNum lam Δ := by
    unfold mtKernelNum
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only [Zeta23.ThmD.vStar]
    rw [harg v]
    congr 2
    dsimp [x]
    ring
  rw [hp, show 2 * a * (1 / 2) = a by ring,
    show 2 * x * (1 / 2) = x by ring,
    show 2 * a * (-(1 : ℝ) / 2) = -a by ring,
    show 2 * x * (-(1 : ℝ) / 2) = -x by ring,
    Real.cos_neg, Real.cos_neg, Real.sin_neg, Real.sin_neg] at h
  change (x ^ 2 - a ^ 2) * mtKernelNum lam Δ =
    x * Real.cos a * Real.sin x - a * Real.sin a * Real.cos x
  linarith only [h]

private theorem cotangent_line_no_additive_triple (c x y : ℝ)
    (hx : Real.cos x = c * x * Real.sin x)
    (hy : Real.cos y = c * y * Real.sin y)
    (hxy : Real.cos (x + y) = c * (x + y) * Real.sin (x + y)) : False := by
  have hs (u : ℝ) (hu : Real.cos u = c * u * Real.sin u) : Real.sin u ≠ 0 := by
    intro hzero
    have hcos : Real.cos u = 0 := by simpa only [hzero, mul_zero] using hu
    have hsq := Real.sin_sq_add_cos_sq u
    rw [hzero, hcos] at hsq
    norm_num at hsq
  have heq : (1 + c ^ 2 * (x ^ 2 + x * y + y ^ 2)) * (Real.sin x * Real.sin y) = 0 := by
    rw [Real.cos_add, Real.sin_add, hx, hy] at hxy
    linear_combination -hxy
  have hq : 0 ≤ x ^ 2 + x * y + y ^ 2 := by
    nlinarith only [sq_nonneg (x + y), sq_nonneg x, sq_nonneg y]
  have hp : 0 < 1 + c ^ 2 * (x ^ 2 + x * y + y ^ 2) :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (sq_nonneg c) hq)
  exact (mul_ne_zero hp.ne' (mul_ne_zero (hs x hx) (hs y hy))) heq

private theorem aStar_ne_zero_of_theta_sin {lam : ℝ}
    (hθ : Zeta23.ThmD.theta lam * Real.sin (Zeta23.ThmD.theta lam) ≠ 0) :
    Zeta23.ThmD.aStar lam ≠ 0 := by
  have h := mtKernelNum_closed_form_global lam 0
  have hzero : mtKernelNum lam 0 = Zeta23.ThmD.aStar lam := by
    simp only [mtKernelNum, Zeta23.ThmD.aStar, mul_zero, zero_mul, Real.cos_zero, mul_one]
  rw [hzero] at h
  intro ha
  rw [ha] at h
  simp only [mul_zero, Real.cos_zero, Real.sin_zero, zero_mul, zero_sub, mul_one] at h
  exact hθ (by linarith only [h])

/-- A nondegenerate cosine window has no additive triple of kernel zeros. -/
theorem mtKernel_no_additive_zero_triple {lam : ℝ}
    (hθ : Zeta23.ThmD.theta lam * Real.sin (Zeta23.ThmD.theta lam) ≠ 0) (x y : ℝ) :
    ¬ (mtKernel lam x = 0 ∧ mtKernel lam y = 0 ∧ mtKernel lam (x + y) = 0) := by
  let a := Zeta23.ThmD.theta lam
  let c := Real.cos a / (a * Real.sin a)
  have hA : a * Real.sin a ≠ 0 := hθ
  have hr (u : ℝ) (hu : mtKernel lam u = 0) :
      Real.cos (Real.pi * u) = c * (Real.pi * u) * Real.sin (Real.pi * u) := by
    have hn : mtKernelNum lam u = 0 :=
      (div_eq_zero_iff.mp hu).resolve_right (aStar_ne_zero_of_theta_sin hθ)
    have h := mtKernelNum_closed_form_global lam u
    rw [hn, mul_zero] at h
    have hb : (a * Real.sin a) * Real.cos (Real.pi * u) =
        Real.cos a * (Real.pi * u) * Real.sin (Real.pi * u) := by
      dsimp [a]
      linarith only [h]
    calc
      _ = ((a * Real.sin a) * Real.cos (Real.pi * u)) / (a * Real.sin a) := by
        apply (eq_div_iff hA).mpr
        ring
      _ = (Real.cos a * (Real.pi * u) * Real.sin (Real.pi * u)) / (a * Real.sin a) := by rw [hb]
      _ = _ := by dsimp [c]; ring
  rintro ⟨hx, hy, hxy⟩
  have hz := hr (x + y) hxy
  rw [mul_add] at hz
  exact cotangent_line_no_additive_triple c (Real.pi * x) (Real.pi * y) (hr x hx) (hr y hy) hz

private theorem continuous_mtKernelNum (lam : ℝ) : Continuous (mtKernelNum lam) := by
  unfold mtKernelNum
  apply intervalIntegral.continuous_of_dominated_interval (bound := fun _ => 1)
  · intro Δ
    exact (by unfold Zeta23.ThmD.vStar; fun_prop :
      Continuous (fun v : ℝ => Zeta23.ThmD.vStar lam v * Real.cos (2 * Real.pi * Δ * v))).aestronglyMeasurable.restrict
  · intro Δ
    filter_upwards with v _
    rw [Real.norm_eq_abs, abs_mul]
    unfold Zeta23.ThmD.vStar
    exact (mul_le_mul (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
      (abs_nonneg _) zero_le_one).trans_eq (by ring)
  · exact intervalIntegrable_const
  · filter_upwards with v _
    fun_prop

private def tripleKernelMass (lam : ℝ) (p : ℝ × ℝ) : ℝ :=
  max |mtKernel lam p.1| (max |mtKernel lam p.2| |mtKernel lam (p.1 + p.2)|)

private theorem continuous_tripleKernelMass (lam : ℝ) : Continuous (tripleKernelMass lam) := by
  have hK : Continuous (mtKernel lam) :=
    (continuous_mtKernelNum lam).div_const (Zeta23.ThmD.aStar lam)
  exact (hK.comp continuous_fst).abs.max
    ((hK.comp continuous_snd).abs.max (hK.comp (continuous_fst.add continuous_snd)).abs)

private theorem tripleKernelMass_pos {lam : ℝ}
    (hθ : Zeta23.ThmD.theta lam * Real.sin (Zeta23.ThmD.theta lam) ≠ 0) (p : ℝ × ℝ) :
    0 < tripleKernelMass lam p := by
  by_contra hnot
  have hle : max |mtKernel lam p.1|
      (max |mtKernel lam p.2| |mtKernel lam (p.1 + p.2)|) ≤ 0 := le_of_not_gt hnot
  obtain ⟨h1, h23⟩ := max_le_iff.mp hle
  obtain ⟨h2, h3⟩ := max_le_iff.mp h23
  exact mtKernel_no_additive_zero_triple hθ p.1 p.2
    ⟨abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _)),
      abs_eq_zero.mp (le_antisymm h2 (abs_nonneg _)),
      abs_eq_zero.mp (le_antisymm h3 (abs_nonneg _))⟩

private theorem compact_positive_pair_floor {f : ℝ × ℝ → ℝ} (hc : Continuous f)
    (hp : ∀ p, 0 < f p) {S : ℝ} (hS : 0 ≤ S) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ Set.Icc (-S) S ×ˢ Set.Icc (-S) S, c ≤ f p := by
  have hs : IsCompact (Set.Icc (-S) S ×ˢ Set.Icc (-S) S) :=
    isCompact_Icc.prod isCompact_Icc
  have hne : (Set.Icc (-S) S ×ˢ Set.Icc (-S) S).Nonempty :=
    ⟨(0, 0), ⟨⟨by linarith only [hS], hS⟩, ⟨by linarith only [hS], hS⟩⟩⟩
  obtain ⟨p, _, hmin⟩ := hs.exists_isMinOn (f := f) hne hc.continuousOn
  exact ⟨f p, hp p, fun q hq => hmin hq⟩

/-- Every bounded set of gap pairs has a uniform positive triple floor at a fixed cosine window. -/
theorem mtKernel_compact_triple_floor {lam S : ℝ}
    (hθ : Zeta23.ThmD.theta lam * Real.sin (Zeta23.ThmD.theta lam) ≠ 0) (hS : 0 ≤ S) :
    ∃ c : ℝ, 0 < c ∧ ∀ x y : ℝ, |x| ≤ S → |y| ≤ S →
      c ≤ max |mtKernel lam x| (max |mtKernel lam y| |mtKernel lam (x + y)|) := by
  obtain ⟨c, hc, h⟩ := compact_positive_pair_floor (f := tripleKernelMass lam)
    (continuous_tripleKernelMass lam) (tripleKernelMass_pos hθ) hS
  exact ⟨c, hc, fun x y hx hy => h (x, y) ⟨abs_le.mp hx, abs_le.mp hy⟩⟩

/-- Positive triple floors persist at cosine shape four thirds, on every bounded gap set. -/
theorem mtKernel_fourThirds_triple_floor {S : ℝ} (hS : 0 ≤ S) :
    ∃ c : ℝ, 0 < c ∧ ∀ x y : ℝ, |x| ≤ S → |y| ≤ S →
      c ≤ max |mtKernel (4 / 3) x| (max |mtKernel (4 / 3) y| |mtKernel (4 / 3) (x + y)|) := by
  apply mtKernel_compact_triple_floor _ hS
  have hs : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have ha : 0 < Zeta23.ThmD.theta (4 / 3) := by unfold Zeta23.ThmD.theta; positivity
  have hb : Zeta23.ThmD.theta (4 / 3) < Real.pi := by
    unfold Zeta23.ThmD.theta
    have hh : (4 / 3 : ℝ) / Real.sqrt 2 ≤ 4 / 3 := div_le_self (by norm_num) hs
    linarith only [hh, Real.pi_gt_three]
  exact mul_ne_zero ha.ne' (Real.sin_pos_of_pos_of_lt_pi ha hb).ne'

private theorem mtKernel_boxcar_zero {u : ℝ} (hu : Real.pi * u ≠ 0)
    (hs : Real.sin (Real.pi * u) = 0) : mtKernel 0 u = 0 := by
  have h : (Real.pi * u) ^ 2 * mtKernelNum 0 u = 0 := by
    simpa [Zeta23.ThmD.theta, hs] using mtKernelNum_closed_form_global 0 u
  have hn := (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hu)
  simp only [mtKernel, hn, zero_div]

/-- The boxcar limit has additive kernel-zero triples, so the nondegeneracy condition matters. -/
theorem mtKernel_boxcar_additive_zeros : mtKernel 0 1 = 0 ∧ mtKernel 0 2 = 0 := by
  constructor
  · exact mtKernel_boxcar_zero (by simpa only [mul_one] using Real.pi_pos.ne')
      (by simpa only [mul_one] using Real.sin_pi)
  · apply mtKernel_boxcar_zero (mul_ne_zero Real.pi_pos.ne' (by norm_num))
    rw [mul_comm Real.pi, Real.sin_two_pi]

/-- Additive zero triples occur exactly at degenerate cosine parameters.
For nonzero parameters with zero mean, the normalized kernel is totalized by division by zero. -/
theorem mtKernel_additive_zero_triple_iff (lam : ℝ) :
    (∃ x y : ℝ, mtKernel lam x = 0 ∧ mtKernel lam y = 0 ∧ mtKernel lam (x + y) = 0) ↔
      Zeta23.ThmD.theta lam * Real.sin (Zeta23.ThmD.theta lam) = 0 := by
  constructor
  · rintro ⟨x, y, h⟩
    by_contra hθ
    exact mtKernel_no_additive_zero_triple hθ x y h
  · intro hθ
    by_cases ha : Zeta23.ThmD.theta lam = 0
    · have hlam : lam = 0 := by
        unfold Zeta23.ThmD.theta at ha
        exact (div_eq_zero_iff.mp ha).resolve_right (by positivity)
      subst lam
      refine ⟨1, 1, mtKernel_boxcar_additive_zeros.1, mtKernel_boxcar_additive_zeros.1, ?_⟩
      simpa only [one_add_one_eq_two] using mtKernel_boxcar_additive_zeros.2
    · have hs := (mul_eq_zero.mp hθ).resolve_left ha
      have h := mtKernelNum_closed_form_global lam 0
      have hzero : mtKernelNum lam 0 = Zeta23.ThmD.aStar lam := by
        simp only [mtKernelNum, Zeta23.ThmD.aStar, mul_zero, zero_mul, Real.cos_zero, mul_one]
      rw [hzero] at h
      simp only [mul_zero, zero_mul, Real.cos_zero, Real.sin_zero, hs, mul_one] at h
      have hprod : (Zeta23.ThmD.theta lam) ^ 2 * Zeta23.ThmD.aStar lam = 0 := by
        nlinarith only [h]
      have hA := (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero 2 ha)
      refine ⟨0, 0, ?_, ?_, ?_⟩ <;> simp only [mtKernel, hA, div_zero]

end GaloisForLFunctions.IncommensurableGaborPinching
