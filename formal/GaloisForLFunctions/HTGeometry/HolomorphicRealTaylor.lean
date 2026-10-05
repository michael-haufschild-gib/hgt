import Mathlib

/-!
# Real Taylor coefficients of holomorphic functions

* every complex derivative of a function holomorphic on an open set is holomorphic there;
* if `f = Re ∘ h` on an open real set `V` whose image lies in the open set `U` where `h` is
  holomorphic, then `f^{(k)}(x) = Re h^{(k)}(x)` on `V`;
* (Cauchy) if `h` is holomorphic on `B(c, R)` and `0 < r < R`, then `‖h^{(k)}(c)‖ ≤ k! C/r^k`;
* (Weierstrass) a series of holomorphic functions dominated on an open set by a summable sequence
  is holomorphic there and may be differentiated termwise to every order.
-/

open Set Filter Topology Metric

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem differentiableOn_iteratedDeriv_of_isOpen {f : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (k : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv k f) U := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv hU

/-- Real derivatives of the real part of a holomorphic function along the real axis. -/
theorem iteratedDeriv_eq_re_of_differentiableOn {h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hh : DifferentiableOn ℂ h U) {f : ℝ → ℝ} {V : Set ℝ} (hV : IsOpen V)
    (hVU : ∀ y ∈ V, (y : ℂ) ∈ U) (hfV : ∀ y ∈ V, f y = (h y).re) (k : ℕ) {x : ℝ} (hx : x ∈ V) :
    iteratedDeriv k f x = (iteratedDeriv k h x).re := by
  induction k generalizing x with
  | zero => simpa using hfV x hx
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv k f =ᶠ[𝓝 x] fun y => (iteratedDeriv k h y).re :=
      Filter.eventually_of_mem (hV.mem_nhds hx) fun y hy => ih hy
    rw [heq.deriv_eq]
    have hd : DifferentiableAt ℂ (iteratedDeriv k h) (x : ℂ) :=
      (differentiableOn_iteratedDeriv_of_isOpen hh hU k).differentiableAt
        (hU.mem_nhds (hVU x hx))
    rw [hd.hasDerivAt.real_of_complex.deriv, iteratedDeriv_succ]

/-- **Cauchy coefficient bound.**  A function holomorphic on `B(c, R)` has
`‖h^{(k)}(c)‖ ≤ k! C/r^k` for every `0 < r < R` and a constant `C ≥ 0` independent of `k`. -/
theorem exists_norm_iteratedDeriv_le_of_differentiableOn_ball {h : ℂ → ℂ} {c : ℂ} {R r : ℝ}
    (hh : DifferentiableOn ℂ h (ball c R)) (hr : 0 < r) (hrR : r < R) :
    ∃ C, 0 ≤ C ∧ ∀ k : ℕ, ‖iteratedDeriv k h c‖ ≤ k.factorial * C / r ^ k := by
  have hsub : closedBall c r ⊆ ball c R := closedBall_subset_ball hrR
  have hdc : DiffContOnCl ℂ h (ball c r) := hh.diffContOnCl_ball hsub
  obtain ⟨C, hC⟩ := (isCompact_sphere c r).exists_bound_of_continuousOn
    ((hh.mono (sphere_subset_closedBall.trans hsub)).continuousOn)
  refine ⟨max C 0, le_max_right _ _, fun k => ?_⟩
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr hdc
    fun z hz => (hC z hz).trans (le_max_left _ _)

/-- Iterated derivatives of finite sums of holomorphic functions on an open set. -/
theorem iteratedDeriv_finset_sum_of_differentiableOn {ι : Type*} {F : ι → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (S : Finset ι) (hF : ∀ i, DifferentiableOn ℂ (F i) U) (k : ℕ) {z : ℂ}
    (hz : z ∈ U) :
    iteratedDeriv k (fun w => ∑ i ∈ S, F i w) z = ∑ i ∈ S, iteratedDeriv k (F i) z := by
  have h := iteratedDeriv_sum (𝕜 := ℂ) (n := k) (x := z) (f := F) (I := S) fun i _ =>
    ((hF i).contDiffOn hU).contDiffAt (hU.mem_nhds hz)
  rw [← h]
  congr 1
  funext w
  simp

/-- **Weierstrass termwise differentiation.**  Holomorphic `F i` on an open `U`, dominated by a
summable `u`, sum to a holomorphic function whose every derivative is the termwise sum. -/
theorem hasSum_iteratedDeriv_of_summable_bound {ι : Type*} {F : ι → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : ∀ i, DifferentiableOn ℂ (F i) U) {u : ι → ℝ} (hu : Summable u)
    (hFu : ∀ i, ∀ z ∈ U, ‖F i z‖ ≤ u i) :
    DifferentiableOn ℂ (fun z => ∑' i, F i z) U ∧
      ∀ k : ℕ, ∀ z ∈ U, HasSum (fun i => iteratedDeriv k (F i) z)
        (iteratedDeriv k (fun z => ∑' i, F i z) z) := by
  have hdiffS : ∀ k (S : Finset ι),
      DifferentiableOn ℂ (fun z => ∑ i ∈ S, iteratedDeriv k (F i) z) U := fun k S =>
    DifferentiableOn.fun_sum fun i _ => differentiableOn_iteratedDeriv_of_isOpen (hF i) hU k
  have h0 : TendstoLocallyUniformlyOn (fun S z => ∑ i ∈ S, F i z) (fun z => ∑' i, F i z) atTop U :=
    (tendstoUniformlyOn_tsum hu hFu).tendstoLocallyUniformlyOn
  have hk : ∀ k, TendstoLocallyUniformlyOn (fun S z => ∑ i ∈ S, iteratedDeriv k (F i) z)
      (iteratedDeriv k fun z => ∑' i, F i z) atTop U := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      have h := ih.deriv (Eventually.of_forall fun S => hdiffS k S) hU
      rw [iteratedDeriv_succ]
      refine h.congr fun S z hz => ?_
      simp only [Function.comp_apply]
      have e : (fun w => ∑ i ∈ S, iteratedDeriv k (F i) w) =ᶠ[𝓝 z]
          iteratedDeriv k (fun w => ∑ i ∈ S, F i w) :=
        Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw =>
          (iteratedDeriv_finset_sum_of_differentiableOn hU S hF k hw).symm
      rw [e.deriv_eq, ← iteratedDeriv_succ,
        iteratedDeriv_finset_sum_of_differentiableOn hU S hF (k + 1) hz]
  refine ⟨h0.differentiableOn (Eventually.of_forall fun S => by simpa using hdiffS 0 S) hU,
    fun k z hz => (hk k).tendsto_at hz⟩

end GaloisForLFunctions.HTGeometry
