/-
Minimum modulus for zero-free analytic functions, and logarithmic-budget carrier floors.

A zero-free analytic function on a ball has an analytic logarithm (mathlib's continuous branch on
the simply connected ball, upgraded to analytic by exp-injectivity), whose real part is the
log-modulus.  The Borel–Carathéodory theorem applied to the recentered logarithm bounds its full
norm by its real part alone, so a sup bound `M` on the ball and an anchor value `m ≤ ‖f c‖` at the
center force the lower bound `‖f z‖ ≥ m·exp(−2·log(M/m)·r/(R−r))` on every sub-ball: a zero-free
modulus cannot dip below its anchor by more than a fixed power of the sup/anchor ratio.

Applied to the zero-free cofactor of a one-zero factorization of the finite carrier `gN`, this
floors the carrier on any subset of a sub-ball at distance `≥ d` from the zero, with budget scale
`log(M/m)` — logarithmic in the sup/anchor ratio and independent of the carrier length, replacing
linear variation budgets of size `Σ log n · n^{σ}`.
-/
import GaloisForLFunctions.U0.U0KummerBranch
import GaloisForLFunctions.RHTower.ZetaCarrier

open Complex Metric

namespace RHTower

/-- **Minimum modulus of a zero-free function from one anchor and one sup.**  On the ball
`ball c R` a zero-free analytic `f` with `‖f‖ ≤ M` and `m ≤ ‖f c‖` satisfies
`‖f z‖ ≥ m·exp(−2·log(M/m)·r/(R−r))` on `closedBall c r`.  The analytic logarithm exists on the
simply connected ball; its real part is `log ‖f‖`, bounded above by `log M`; Borel–Carathéodory
converts that one-sided real-part bound into a two-sided norm bound for the recentered logarithm,
whose real part controls the dip of `log ‖f‖` below its anchor. -/
theorem norm_lower_bound_of_anchor {f : ℂ → ℂ} {c : ℂ} {R r M m : ℝ}
    (hr : 0 ≤ r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (ball c R))
    (hf0 : ∀ z ∈ ball c R, f z ≠ 0)
    (hsup : ∀ z ∈ ball c R, ‖f z‖ ≤ M)
    (hm : 0 < m) (hmM : m < M)
    (hanc : m ≤ ‖f c‖) :
    ∀ z ∈ closedBall c r,
      m * Real.exp (-(2 * Real.log (M / m) * r / (R - r))) ≤ ‖f z‖ := by
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  have hMpos : 0 < M := lt_trans hm hmM
  have hcball : c ∈ ball c R := mem_ball_self hR
  have hUsc : IsSimplyConnected (ball c R) := by
    haveI : ContractibleSpace (ball c R) := Metric.contractibleSpace_ball hR
    exact SimplyConnectedSpace.ofContractible _
  have h0im : (0 : ℂ) ∉ f '' ball c R := by
    rintro ⟨w, hw, hfw⟩
    exact hf0 w hw hfw
  obtain ⟨L, hLc, hLexp⟩ :=
    Complex.exists_continuousOn_eqOn_exp_comp hUsc isOpen_ball hf.continuousOn h0im
  have hLexp' : ∀ z ∈ ball c R, Complex.exp (L z) = f z := fun z hz => hLexp hz
  have hLan : AnalyticOnNhd ℂ L (ball c R) :=
    U0KummerBranch.analyticOnNhd_of_continuousOn_exp_eq isOpen_ball hLc hf hLexp'
  have hLre : ∀ z ∈ ball c R, (L z).re = Real.log ‖f z‖ := by
    intro z hz
    have h1 : ‖f z‖ = Real.exp (L z).re := by
      rw [← hLexp' z hz, Complex.norm_exp]
    rw [h1, Real.log_exp]
  set A : ℝ := Real.log (M / m) with hA_def
  have hApos : 0 < A := Real.log_pos ((one_lt_div hm).mpr hmM)
  set g : ℂ → ℂ := fun w => L (c + w) - L c with hg_def
  have hmem : ∀ w ∈ ball (0 : ℂ) R, c + w ∈ ball c R := by
    intro w hw
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact mem_ball_zero_iff.mp hw
  have hgdiff : DifferentiableOn ℂ g (ball 0 R) := by
    intro w hw
    have h1 : DifferentiableAt ℂ (fun w : ℂ => L (c + w)) w := by
      have h2 := ((hLan (c + w) (hmem w hw)).differentiableAt).comp w
        ((differentiableAt_const c).add differentiableAt_id)
      simpa [Function.comp] using h2
    exact (h1.sub_const (L c)).differentiableWithinAt
  have hgmaps : Set.MapsTo g (ball 0 R) {z | z.re ≤ A} := by
    intro w hw
    have hcw : c + w ∈ ball c R := hmem w hw
    simp only [Set.mem_setOf_eq, hg_def, Complex.sub_re]
    rw [hLre (c + w) hcw, hLre c hcball]
    have hfcw0 : (0 : ℝ) < ‖f (c + w)‖ := norm_pos_iff.mpr (hf0 _ hcw)
    have l1 : Real.log ‖f (c + w)‖ ≤ Real.log M :=
      Real.log_le_log hfcw0 (hsup _ hcw)
    have l2 : Real.log m ≤ Real.log ‖f c‖ := Real.log_le_log hm hanc
    rw [hA_def, Real.log_div (ne_of_gt hMpos) (ne_of_gt hm)]
    linarith
  have hg0 : g 0 = 0 := by simp [hg_def]
  intro z hz
  have hzr : ‖z - c‖ ≤ r := by
    rw [← dist_eq_norm]
    exact mem_closedBall.mp hz
  have hzball : z ∈ ball c R := by
    rw [mem_ball]
    exact lt_of_le_of_lt (mem_closedBall.mp hz) hrR
  have hwball : z - c ∈ ball (0 : ℂ) R :=
    mem_ball_zero_iff.mpr (lt_of_le_of_lt hzr hrR)
  have hbc := Complex.borelCaratheodory_zero hApos hgdiff hgmaps hR hwball hg0
  have hgz : g (z - c) = L z - L c := by
    rw [hg_def]
    simp [add_sub_cancel]
  have hmono : 2 * A * ‖z - c‖ / (R - ‖z - c‖) ≤ 2 * A * r / (R - r) := by
    apply div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left hzr (by positivity)) (by linarith) (by linarith)
  have h1 : ‖L z - L c‖ ≤ 2 * A * r / (R - r) := by
    rw [← hgz]
    exact le_trans hbc hmono
  have h3 : -(2 * A * r / (R - r)) ≤ (L z).re - (L c).re := by
    have h2 := (abs_le.mp (le_trans (Complex.abs_re_le_norm _) h1)).1
    rwa [Complex.sub_re] at h2
  have h4 := hLre z hzball
  have h5 := hLre c hcball
  have h6 : Real.log m ≤ Real.log ‖f c‖ := Real.log_le_log hm hanc
  have hfz0 : (0 : ℝ) < ‖f z‖ := norm_pos_iff.mpr (hf0 z hzball)
  calc m * Real.exp (-(2 * A * r / (R - r)))
      = Real.exp (Real.log m + -(2 * A * r / (R - r))) := by
        rw [Real.exp_add, Real.exp_log hm]
    _ ≤ Real.exp (Real.log ‖f z‖) := Real.exp_le_exp.mpr (by linarith)
    _ = ‖f z‖ := Real.exp_log hfz0

/-- **Logarithmic-budget carrier floor on a one-zero window.**  If the finite carrier factors as
`gN N z = (z − ρ')·h z` with `h` zero-free on `ball c R`, then an anchor `m ≤ ‖h c‖`, a sup
`‖h‖ ≤ M`, and a distance `d` from the zero floor the carrier on any subset of `closedBall c r`
at `ε < d·m·exp(−2·log(M/m)·r/(R−r))`.  The budget is logarithmic in the sup/anchor ratio and
independent of the carrier length `N`, in contrast to the linear Lipschitz variation budget
`(Σ log n · n^{σ})·R` of the center-spreading route. -/
theorem carrierFloorOn_of_single_zero_anchor {N : ℕ} {ρ' c : ℂ} {h : ℂ → ℂ}
    {R r M m d ε : ℝ}
    (hr : 0 ≤ r) (hrR : r < R)
    (hh : AnalyticOnNhd ℂ h (ball c R))
    (hh0 : ∀ z ∈ ball c R, h z ≠ 0)
    (hfact : ∀ z ∈ ball c R, gN N z = (z - ρ') * h z)
    (hsup : ∀ z ∈ ball c R, ‖h z‖ ≤ M)
    (hm : 0 < m) (hmM : m < M) (hanc : m ≤ ‖h c‖)
    {S : Set ℂ} (hS : S ⊆ closedBall c r)
    (hd : ∀ z ∈ S, d ≤ ‖z - ρ'‖)
    (hε : ε < d * (m * Real.exp (-(2 * Real.log (M / m) * r / (R - r))))) :
    CarrierFloorOn S N ε := by
  intro z hz
  have hzball : z ∈ ball c R :=
    mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp (hS hz)) hrR)
  have hfloor := norm_lower_bound_of_anchor hr hrR hh hh0 hsup hm hmM hanc z (hS hz)
  calc ε < d * (m * Real.exp (-(2 * Real.log (M / m) * r / (R - r)))) := hε
    _ ≤ ‖z - ρ'‖ * ‖h z‖ :=
        mul_le_mul (hd z hz) hfloor (by positivity) (norm_nonneg _)
    _ = ‖gN N z‖ := by rw [hfact z hzball, norm_mul]

end RHTower

namespace RHTower

/-- Maximum principle in sup form: an analytic function on a closed ball is bounded on the
whole ball by its boundary-circle sup. -/
theorem norm_le_on_closedBall_of_sphere {f : ℂ → ℂ} {a : ℂ} {P M : ℝ} (hP : 0 < P)
    (hf : ∀ z ∈ closedBall a P, AnalyticAt ℂ f z)
    (hsp : ∀ z ∈ sphere a P, ‖f z‖ ≤ M) :
    ∀ z ∈ closedBall a P, ‖f z‖ ≤ M := by
  intro z hz
  have hdiffcl : DiffContOnCl ℂ f (ball a P) := by
    constructor
    · intro w hw
      exact (hf w (ball_subset_closedBall hw)).differentiableAt.differentiableWithinAt
    · intro w hw
      rw [closure_ball a hP.ne'] at hw
      exact (hf w hw).continuousAt.continuousWithinAt
  refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdiffcl ?_ ?_
  · intro w hw
    rw [frontier_ball a hP.ne'] at hw
    exact hsp w hw
  · rw [closure_ball a hP.ne']
    exact hz

end RHTower
