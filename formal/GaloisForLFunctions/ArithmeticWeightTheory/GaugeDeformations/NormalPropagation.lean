import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheSlowReturnBoundLivesRightOfTheLine
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

/-!
# From real interval bounds to complex disk bounds

A polynomial harmonic barrier turns a bound on a real diameter into a
geometric-mean bound on a smaller complex disk. A finite three-circle
chain transports this control to zero with a fixed dyadic exponent.
The constants and disk depend only on the geometry and common bound.
-/


open Complex Metric Set
open scoped Topology
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations


private def halfBarrier (z : ℂ) : ℂ := -2 * I * z + z ^ 2

private theorem halfBarrier_re (z : ℂ) :
    (halfBarrier z).re = 2 * z.im + z.re ^ 2 - z.im ^ 2 := by
  simp only [halfBarrier, add_re, mul_re, mul_im, neg_re, neg_im, I_re, I_im, pow_two, re_ofNat, im_ofNat]
  ring

private theorem halfBarrier_boundary {z : ℂ} (hz : ‖z‖ = 1) (hy : 0 ≤ z.im) :
    1 ≤ (halfBarrier z).re := by
  rw [halfBarrier_re]
  have hy1 : z.im ≤ 1 := (le_abs_self _).trans ((abs_im_le_norm z).trans_eq hz)
  have hs : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    simp only [Complex.normSq_apply, hz, one_pow] at h
    nlinarith only [h]
  nlinarith only [hs, mul_nonneg hy (sub_nonneg.mpr hy1)]

private theorem halfBarrier_small {z : ℂ} (hz : ‖z‖ ≤ 1 / 8) :
    (halfBarrier z).re ≤ 1 / 2 := by
  rw [halfBarrier_re]
  have hx := abs_re_le_norm z
  have hy := abs_im_le_norm z
  have hx2 : z.re ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg z.re) (by norm_num : (0 : ℝ) ≤ 1 / 8)).mpr (hx.trans hz)
    simpa only [sq_abs] using h
  nlinarith only [hx2, (le_abs_self z.im).trans (hy.trans hz), sq_nonneg z.im]

private theorem upperHalfDisk_frontier {z : ℂ}
    (hz : z ∈ frontier (closedBall (0 : ℂ) 1 ∩ {w : ℂ | 0 ≤ w.im})) :
    ‖z‖ ≤ 1 ∧ 0 ≤ z.im ∧ (‖z‖ = 1 ∨ z.im = 0) := by
  have hclosed : IsClosed (closedBall (0 : ℂ) 1 ∩ {w : ℂ | 0 ≤ w.im}) :=
    isClosed_closedBall.inter (isClosed_le continuous_const continuous_im)
  have hmem := hclosed.closure_eq ▸ frontier_subset_closure hz
  have hn : ‖z‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hmem.1
  refine ⟨hn, hmem.2, ?_⟩
  by_contra h
  push Not at h
  have ho : IsOpen (ball (0 : ℂ) 1 ∩ {w : ℂ | 0 < w.im}) :=
    isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  have hi : z ∈ interior (closedBall (0 : ℂ) 1 ∩ {w : ℂ | 0 ≤ w.im}) := by
    apply interior_mono (s := ball (0 : ℂ) 1 ∩ {w : ℂ | 0 < w.im}) ?_
      (by rw [ho.interior_eq]; exact ⟨by simpa only [mem_ball, dist_zero_right] using lt_of_le_of_ne hn h.1,
        lt_of_le_of_ne hmem.2 (Ne.symm h.2)⟩)
    exact inter_subset_inter ball_subset_closedBall (fun w (hw : 0 < w.im) => hw.le)
  exact hz.2 hi

/-- A polynomial barrier propagates a real diameter bound into a smaller half-disk. -/
private theorem upperHalfDisk_small {f : ℂ → ℂ} {m M : ℝ}
    (hm : 0 < m) (hmM : m ≤ M)
    (hd : ∀ z : ℂ, ‖z‖ ≤ 1 → DifferentiableAt ℂ f z)
    (hM : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f z‖ ≤ M)
    (hreal : ∀ t : ℝ, |t| ≤ 1 → ‖f (t : ℂ)‖ ≤ m)
    {z : ℂ} (hz : ‖z‖ ≤ 1 / 8) (hy : 0 ≤ z.im) :
    ‖f z‖ ^ 2 ≤ M * m := by
  let A : ℝ := Real.log (M / m)
  have hMp : 0 < M := hm.trans_le hmM
  have hA : 0 ≤ A := Real.log_nonneg ((one_le_div hm).mpr hmM)
  have hexp : Real.exp (-A) = m / M := by
    rw [Real.exp_neg, Real.exp_log (div_pos hMp hm), inv_div]
  let g : ℂ → ℂ := fun w => f w * cexp (-(A : ℂ) * halfBarrier w)
  have hnorm (w : ℂ) : ‖g w‖ = ‖f w‖ * Real.exp (-A * (halfBarrier w).re) := by
    simp only [g, norm_mul, norm_exp, mul_re, neg_re, neg_im, ofReal_re,
      ofReal_im, neg_zero, zero_mul, sub_zero]
  let S : Set ℂ := closedBall 0 1 ∩ {w : ℂ | 0 ≤ w.im}
  have hclosed : IsClosed S :=
    isClosed_closedBall.inter (isClosed_le continuous_const continuous_im)
  have hdg : ∀ w ∈ S, DifferentiableAt ℂ g w := by
    intro w hw
    apply (hd w (by simpa only [mem_closedBall, dist_zero_right] using hw.1)).mul
    apply DifferentiableAt.cexp
    dsimp [halfBarrier]
    fun_prop
  have hbound : ∀ w ∈ frontier S, ‖g w‖ ≤ m := by
    intro w hw
    obtain ⟨hwn, hwy, hedge⟩ := upperHalfDisk_frontier hw
    rw [hnorm]
    rcases hedge with he | he
    · have hq := halfBarrier_boundary he hwy
      calc
        _ ≤ M * Real.exp (-A) := mul_le_mul (hM w hwn)
          (Real.exp_le_exp.mpr (by nlinarith only [hq, hA])) (by positivity) hMp.le
        _ = m := by rw [hexp]; field_simp
    · have hq : 0 ≤ (halfBarrier w).re := by
        rw [halfBarrier_re, he]
        nlinarith only [sq_nonneg w.re]
      have hwre : ‖f w‖ ≤ m := by
        have hw' : (w.re : ℂ) = w := by apply Complex.ext <;> simp [he]
        rw [← hw']
        exact hreal w.re ((abs_re_le_norm w).trans hwn)
      calc
        _ ≤ m * 1 := mul_le_mul hwre
          (by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith only [hq, hA]))
          (by positivity) hm.le
        _ = m := mul_one m
  have hgz : ‖g z‖ ≤ m := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le
      (isBounded_closedBall.subset inter_subset_left)
      (show DiffContOnCl ℂ g S from ⟨fun w hw => (hdg w hw).differentiableWithinAt,
        by rw [hclosed.closure_eq]; exact fun w hw => (hdg w hw).continuousAt.continuousWithinAt⟩)
      hbound
    rw [hclosed.closure_eq]
    exact ⟨by simp only [mem_closedBall, dist_zero_right]; linarith only [hz], hy⟩
  have hsmall : ‖f z‖ * Real.exp (-A / 2) ≤ m := by
    apply le_trans ?_ hgz
    rw [hnorm]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Real.exp_le_exp.mpr (by nlinarith only [halfBarrier_small hz, hA])
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ ‖f z‖ * Real.exp (-A / 2)) hsmall 2
  have he : Real.exp (-A / 2) ^ 2 = m / M := by
    rw [pow_two, ← Real.exp_add, show -A / 2 + -A / 2 = -A by ring, hexp]
  rw [mul_pow, he] at hs
  have hs' := mul_le_mul_of_nonneg_right hs hMp.le
  rw [mul_assoc, div_mul_cancel₀ _ hMp.ne'] at hs'
  have he' : m ^ 2 * M = (M * m) * m := by ring
  rw [he'] at hs'
  exact (mul_le_mul_iff_left₀ hm).mp hs'

/-- Real diameter control gives a geometric-mean bound on the smaller complex disk. -/
theorem unitDisk_small {f : ℂ → ℂ} {m M : ℝ}
    (hm : 0 < m) (hMp : 0 < M)
    (hd : ∀ z : ℂ, ‖z‖ ≤ 1 → DifferentiableAt ℂ f z)
    (hM : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f z‖ ≤ M)
    (hreal : ∀ t : ℝ, |t| ≤ 1 → ‖f (t : ℂ)‖ ≤ m)
    {z : ℂ} (hz : ‖z‖ ≤ 1 / 8) : ‖f z‖ ^ 2 ≤ M * m := by
  by_cases hmM : m ≤ M
  · by_cases hy : 0 ≤ z.im
    · exact upperHalfDisk_small hm hmM hd hM hreal hz hy
    · have h := upperHalfDisk_small (f := fun w => f (-w)) hm hmM
        (fun w hw => (hd (-w) (by simpa only [norm_neg] using hw)).comp w
          differentiableAt_id.neg)
        (fun w hw => hM (-w) (by simpa only [norm_neg] using hw))
        (fun t ht => by simpa only [ofReal_neg] using hreal (-t) (by simpa only [abs_neg] using ht))
        (z := -z) (by simpa only [norm_neg] using hz) (by simp only [neg_im]; linarith only [hy])
      simpa only [neg_neg] using h
  · have hn := hM z (by linarith only [hz])
    have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
    calc ‖f z‖ ^ 2 ≤ M ^ 2 := hs
      _ ≤ M * m := by nlinarith only [hMp, le_of_not_ge hmM]

/-- Scaled diameter propagation, uniform over bounded holomorphic functions. -/
theorem disk_small_of_real_interval {f : ℂ → ℂ} {c r m M : ℝ}
    (hr : 0 < r) (hm : 0 < m) (hMp : 0 < M)
    (hd : ∀ z : ℂ, ‖z - (c : ℂ)‖ ≤ r → DifferentiableAt ℂ f z)
    (hM : ∀ z : ℂ, ‖z - (c : ℂ)‖ ≤ r → ‖f z‖ ≤ M)
    (hreal : ∀ t : ℝ, |t - c| ≤ r → ‖f (t : ℂ)‖ ≤ m)
    {z : ℂ} (hz : ‖z - (c : ℂ)‖ ≤ r / 8) : ‖f z‖ ^ 2 ≤ M * m := by
  have hmap (w : ℂ) (hw : ‖w‖ ≤ 1) : ‖((c : ℂ) + (r : ℂ) * w) - (c : ℂ)‖ ≤ r := by
    rw [add_sub_cancel_left, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith only [hr, hw]
  have h := unitDisk_small (f := fun w => f ((c : ℂ) + (r : ℂ) * w)) hm hMp
    (fun w hw => (hd _ (hmap w hw)).comp w (by fun_prop))
    (fun w hw => hM _ (hmap w hw))
    (fun t ht => by
      have he : (c : ℂ) + (r : ℂ) * (t : ℂ) = ((c + r * t : ℝ) : ℂ) := by push_cast; rfl
      rw [he]
      apply hreal
      rw [add_sub_cancel_left, abs_mul, abs_of_pos hr]
      nlinarith only [hr, ht])
    (z := (z - (c : ℂ)) / (r : ℂ)) (by
      rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hr, div_le_iff₀ hr]
      linarith only [hz])
  have he : (c : ℂ) + (r : ℂ) * ((z - (c : ℂ)) / (r : ℂ)) = z := by
    have hrC : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
    field_simp
    ring
  simpa only [he] using h



/-- A real interval controls a disk about zero by a fixed positive power. -/
theorem exists_disk_power_bound {R c r M : ℝ} (hr : 0 < r) (hM : 0 < M)
    (hfit : |c| + r < R) :
    ∃ (ρ : ℝ) (N : ℕ), 0 < ρ ∧ ρ < R ∧
      ∀ (f : ℂ → ℂ) (m : ℝ), 0 < m →
      DifferentiableOn ℂ f (ball 0 R) →
      (∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ M) →
      (∀ t : ℝ, |t - c| ≤ r → ‖f (t : ℂ)‖ ≤ m) →
      ∀ z : ℂ, ‖z‖ ≤ ρ → ‖f z‖ ≤ M * (m / M) ^ ((1 / 2 : ℝ) ^ (N + 1)) := by
  let ρ := r / 8
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (|c| / ρ)
  have hNp : 0 < (N : ℝ) := (div_nonneg (abs_nonneg _) hρ.le).trans_lt hN
  have hNne : (N : ℝ) ≠ 0 := hNp.ne'
  have hstepbound : |c| / (N : ℝ) ≤ ρ := by
    apply (div_le_iff₀ hNp).mpr
    exact ((div_lt_iff₀ hρ).mp hN).le.trans_eq (mul_comm _ _)
  let q : ℕ → ℂ := fun k => (((1 - (k : ℝ) / (N : ℝ)) * c : ℝ) : ℂ)
  have hq0 : q 0 = (c : ℂ) := by simp [q]
  have hqN : q N = 0 := by
    change (((1 - (N : ℝ) / (N : ℝ)) * c : ℝ) : ℂ) = 0
    rw [div_self hNne, sub_self, zero_mul, Complex.ofReal_zero]
  have hqbound (k : ℕ) (hk : k ≤ N) : ‖q k‖ ≤ |c| := by
    have hfrac : 0 ≤ (k : ℝ) / (N : ℝ) := by positivity
    have hfrac1 : (k : ℝ) / (N : ℝ) ≤ 1 := (div_le_one hNp).mpr (by exact_mod_cast hk)
    simp only [q, norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (sub_nonneg.mpr hfrac1)]
    nlinarith only [abs_nonneg c, hfrac]
  have hstep (k : ℕ) : ‖q (k + 1) - q k‖ ≤ ρ := by
    rw [show q (k + 1) - q k = ((-c / (N : ℝ) : ℝ) : ℂ) by
      dsimp [q]; push_cast; ring]
    simpa only [norm_real, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hNp] using hstepbound
  have hinside (k : ℕ) (hk : k ≤ N) (w : ℂ) (hw : ‖w - q k‖ ≤ 4 * ρ) :
      w ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right]
    have hn : ‖w‖ ≤ ‖w - q k‖ + ‖q k‖ := by
      simpa only [sub_add_cancel] using norm_add_le (w - q k) (q k)
    have hq := hqbound k hk
    dsimp [ρ] at hw
    linarith only [hn, hw, hq, hfit, hr]
  let β : ℝ := (1 / 2 : ℝ) ^ N
  have hβ : 0 < β := by dsimp [β]; positivity
  let α := β / 2
  have hα : 0 < α := by dsimp [α]; positivity
  refine ⟨ρ, N, hρ, ?_, ?_⟩
  · dsimp [ρ]
    linarith only [hfit, abs_nonneg c, hr]
  intro f m hm hd hb hreal z hz
  have hpow : (1 / 2 : ℝ) ^ (N + 1) = α := by
    dsimp [α, β]
    rw [pow_succ]
    ring
  rw [hpow]
  by_cases hmM : m ≤ M
  · let a := (m / M) ^ (1 / 2 : ℝ)
    have ha : 0 < a := Real.rpow_pos_of_pos (div_pos hm hM) _
    have ha1 : a ≤ 1 := Real.rpow_le_one (div_nonneg hm.le hM.le)
      ((div_le_one hM).mpr hmM) (by norm_num)
    have hsmall (w : ℂ) (hw : ‖w - q 0‖ ≤ ρ) : ‖f w‖ ≤ a * M := by
      rw [hq0] at hw
      have hmap (v : ℂ) (hv : ‖v - (c : ℂ)‖ ≤ r) : v ∈ ball (0 : ℂ) R := by
        rw [mem_ball, dist_zero_right]
        have hn : ‖v‖ ≤ ‖v - (c : ℂ)‖ + |c| := by
          simpa only [sub_add_cancel, norm_real, Real.norm_eq_abs] using
            norm_add_le (v - (c : ℂ)) (c : ℂ)
        linarith only [hn, hv, hfit]
      have hh := disk_small_of_real_interval hr hm hM
        (fun v hv => hd.differentiableAt (isOpen_ball.mem_nhds (hmap v hv)))
        (fun v hv => hb v (hmap v hv)) hreal hw
      have ha2 : a ^ 2 = m / M := by
        dsimp only [a]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hm.le hM.le)]
        norm_num
      have he : (a * M) ^ 2 = M * m := by
        rw [mul_pow, ha2]
        field_simp
      have haM : 0 < a * M := mul_pos ha hM
      nlinarith only [hh, he, haM, norm_nonneg (f w)]
    have hchain := GaloisForLFunctions.ArithmeticAuxiliaryDynamics.norm_le_of_chain
      hρ ha ha1 hM hstep
      (fun k hk w hw => hd.differentiableAt (isOpen_ball.mem_nhds (hinside k hk w hw)))
      (fun k hk w hw => hb w (hinside k hk w hw)) hsmall N le_rfl z
      (by simpa only [hqN, sub_zero] using hz)
    have he : a ^ ((1 / 2 : ℝ) ^ N) * M = M * (m / M) ^ α := by
      dsimp only [a]
      rw [← Real.rpow_mul (div_nonneg hm.le hM.le)]
      change (m / M) ^ ((1 / 2 : ℝ) * β) * M = M * (m / M) ^ (β / 2)
      rw [show (1 / 2 : ℝ) * β = β / 2 by ring, mul_comm]
    exact hchain.trans_eq he
  · have hzR : z ∈ ball (0 : ℂ) R := by
      rw [mem_ball, dist_zero_right]
      dsimp [ρ] at hz
      linarith only [hz, hfit, hr, abs_nonneg c]
    have hratio : 1 ≤ m / M := (one_le_div hM).mpr (le_of_not_ge hmM)
    have hp : 1 ≤ (m / M) ^ α := Real.one_le_rpow hratio hα.le
    exact (hb z hzR).trans (by nlinarith only [hp, hM])

#print axioms exists_disk_power_bound

end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
