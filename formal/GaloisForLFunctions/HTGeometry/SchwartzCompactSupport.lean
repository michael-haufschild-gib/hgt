import GaloisForLFunctions.HTGeometry.CutoffProductEstimate
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Smooth compactly supported functions as Schwartz functions

A smooth function with compact support satisfies every Schwartz decay bound, since each weighted
derivative is a continuous function with compact support.  Localising a Schwartz function by the
scaled cutoff therefore produces a Schwartz function supported in `[-2ε, 2ε]`, which is the
localisation used by the structure theorem at a point.
-/

open Set Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem hasCompactSupport_iteratedDeriv_vec {f : ℝ → X} (hf : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n f) := by
  induction n with
  | zero => simpa [iteratedDeriv_zero] using hf
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv

/-- **A smooth compactly supported function is a Schwartz function.** -/
def schwartzOfCompactSupport {f : ℝ → X} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : HasCompactSupport f) : SchwartzMap ℝ X where
  toFun := f
  smooth' := hf
  decay' := by
    intro k n
    have hcontD : Continuous (iteratedDeriv n f) :=
      ContDiff.continuous_iteratedDeriv n hf (by exact_mod_cast le_top)
    have hcont : Continuous (fun x : ℝ => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by
      have h1 : Continuous (fun x : ℝ => ‖x‖ ^ k) := (continuous_norm.pow k)
      have h2 : Continuous (fun x : ℝ => ‖iteratedFDeriv ℝ n f x‖) := by
        have : (fun x : ℝ => ‖iteratedFDeriv ℝ n f x‖)
            = fun x : ℝ => ‖iteratedDeriv n f x‖ := by
          funext x
          rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        rw [this]
        exact hcontD.norm
      exact h1.mul h2
    have hcs : HasCompactSupport (fun x : ℝ => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by
      have hD : HasCompactSupport (iteratedDeriv n f) := hasCompactSupport_iteratedDeriv_vec hsupp n
      refine HasCompactSupport.intro hD.isCompact fun x hx => ?_
      have hzero : iteratedDeriv n f x = 0 := by
        have := Function.notMem_support.mp fun hmem => hx (subset_closure hmem)
        exact this
      have : ‖iteratedFDeriv ℝ n f x‖ = ‖iteratedDeriv n f x‖ :=
        norm_iteratedFDeriv_eq_norm_iteratedDeriv
      rw [this, hzero, norm_zero, mul_zero]
    obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hcont
    refine ⟨C, fun x => ?_⟩
    have := hC x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
    exact this

@[simp] theorem schwartzOfCompactSupport_apply {f : ℝ → X} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : HasCompactSupport f) (x : ℝ) : schwartzOfCompactSupport hf hsupp x = f x := rfl

theorem hasCompactSupport_cutoffScaled {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (cutoffScaled ε) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0:ℝ) (2*ε)) fun x hx => ?_
  refine cutoffScaled_eq_zero hε ?_
  rw [mem_closedBall, Real.dist_eq, sub_zero] at hx
  exact le_of_lt (not_le.mp hx)

/-- The localisation of a Schwartz function at scale `ε`. -/
def cutoffSchwartz (ε : ℝ) (hε : 0 < ε) (φ : SchwartzMap ℝ X) : SchwartzMap ℝ X :=
  schwartzOfCompactSupport
    (f := fun y => cutoffScaled ε y • (φ : ℝ → X) y)
    ((contDiff_cutoffScaled ε).smul φ.smooth')
    ((hasCompactSupport_cutoffScaled hε).smul_right)

@[simp] theorem cutoffSchwartz_apply {ε : ℝ} (hε : 0 < ε) (φ : SchwartzMap ℝ X) (x : ℝ) :
    cutoffSchwartz ε hε φ x = cutoffScaled ε x • φ x := rfl

/-- The seminorm of the localisation is `O(ε)` for every index of order at most `N`. -/
theorem seminorm_cutoffSchwartz_le {φ : SchwartzMap ℝ ℂ} {N : ℕ} {M : ℝ}
    (hvanish : ∀ j, j ≤ N → iteratedDeriv j (φ : ℝ → ℂ) 0 = 0)
    (hM : ∀ t ∈ Icc (-1:ℝ) 1, ‖iteratedDeriv (N+1) (φ : ℝ → ℂ) t‖ ≤ M)
    (k n : ℕ) (hn : n ≤ N) {ε : ℝ} (hε : 0 < ε) (hε1 : 2 * ε ≤ 1) :
    SchwartzMap.seminorm ℂ k n (cutoffSchwartz ε hε φ)
      ≤ ((2:ℝ) ^ k * cutoffProductConst M N n) * ε ^ (k + (N - n + 1)) := by
  have hMnn : 0 ≤ M := by
    have := hM 0 ⟨by norm_num, by norm_num⟩
    exact le_trans (norm_nonneg _) this
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity [cutoffProductConst_nonneg hMnn N n])
    fun x => ?_
  have hfun : ((cutoffSchwartz ε hε φ : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      = fun y => cutoffScaled ε y • (φ : ℝ → ℂ) y := rfl
  rw [hfun, Real.norm_eq_abs]
  exact abs_pow_mul_norm_iteratedFDeriv_cutoff_smul_le φ.smooth' hvanish hM k hn hε hε1 x

/-- The localisation differs from the original only away from the origin. -/
theorem sub_cutoffSchwartz_eq_zero_near {φ : SchwartzMap ℝ ℂ} {ε : ℝ} (hε : 0 < ε) {x : ℝ}
    (hx : |x| ≤ ε) : (φ : ℝ → ℂ) x - (cutoffSchwartz ε hε φ : ℝ → ℂ) x = 0 := by
  have h : (cutoffSchwartz ε hε φ : ℝ → ℂ) x = cutoffScaled ε x • (φ : ℝ → ℂ) x := rfl
  rw [h, cutoffScaled_eq_one hε hx, one_smul, sub_self]

end

end GaloisForLFunctions.HTGeometry
