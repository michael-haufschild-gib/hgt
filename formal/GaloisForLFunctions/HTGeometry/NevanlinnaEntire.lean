import GaloisForLFunctions.HTGeometry.SecondKindGlobal
import GaloisForLFunctions.HTGeometry.NevanlinnaPluecker

/-!
# The Nevanlinna matrix is entire

The global transfer supplies exactly the two inputs the holomorphy capstone was stated modulo: the
kernel is bounded at every point, and — since the Gronwall bound depends on the base point only
through `‖z‖` — the bound is *uniform* on every ball.

So the four limiting entries are differentiable on every ball, hence entire, and the unimodularity
relation holds at every point of `ℂ`.  The only hypothesis left is boundedness of the kernel at the
single point `0`.
-/

open scoped BigOperators

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The uniform first-kind kernel bound on the ball of radius `r`. -/
noncomputable def ballBoundQ (s : ℕ → ℝ) (S P r : ℝ) : ℝ :=
  Real.sqrt ((2 * S ^ (2 : ℕ) + 1 / momentInner s (monicOrtho s 0) (monicOrtho s 0)) *
    Real.exp (8 * (r * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ)))

/-- The uniform second-kind kernel bound on the ball of radius `r`. -/
noncomputable def ballBoundR (s : ℕ → ℝ) (S P r : ℝ) : ℝ :=
  Real.sqrt (2 * P ^ (2 : ℕ) *
    Real.exp (8 * (r * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ)))

/-- The exponent in the global bound is monotone in the displacement. -/
theorem exp_arg_mono (h : PositiveMomentForm s) {S P r : ℝ} {z : ℂ} (hz : ‖z‖ ≤ r) :
    8 * (‖z - 0‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ)
      ≤ 8 * (r * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ) := by
  have h0 : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) := monicOrtho_inner_self_pos h 0
  have hmul : ‖z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)
      ≤ r * momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    mul_le_mul_of_nonneg_right hz h0.le
  have hsq : (‖z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ)
      ≤ (r * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hmul 2
  rw [sub_zero]
  nlinarith [hsq, mul_nonneg (sq_nonneg S) (sq_nonneg P)]

/-- **The first-kind kernel root is uniformly bounded on every ball.** -/
theorem kernelRoot_le_ballBoundQ (h : PositiveMomentForm s) {S P : ℝ}
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j 0) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j 0) N ≤ P)
    {r : ℝ} {z : ℂ} (hz : ‖z‖ ≤ r) (N : ℕ) :
    kernelRoot s (fun j => monicOrthoC s j z) N ≤ ballBoundQ s S P r := by
  have h0 : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) := monicOrtho_inner_self_pos h 0
  have hcQ : (0:ℝ) ≤ 2 * S ^ (2 : ℕ) + 1 / momentInner s (monicOrtho s 0) (monicOrtho s 0) := by
    have h1 : (0:ℝ) ≤ 1 / momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
      div_nonneg zero_le_one h0.le
    nlinarith [sq_nonneg S]
  rw [ballBoundQ, ← Real.sqrt_sq (kernelRoot_nonneg s (fun j => monicOrthoC s j z) N)]
  refine Real.sqrt_le_sqrt (le_trans (kernelRoot_sq_global h 0 z hS hP N) ?_)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (exp_arg_mono h hz)) hcQ

/-- **The second-kind kernel root is uniformly bounded on every ball.** -/
theorem kernelRoot_le_ballBoundR (h : PositiveMomentForm s) {S P : ℝ}
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j 0) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j 0) N ≤ P)
    {r : ℝ} {z : ℂ} (hz : ‖z‖ ≤ r) (N : ℕ) :
    kernelRoot s (fun j => secondKindC s j z) N ≤ ballBoundR s S P r := by
  have hcR : (0:ℝ) ≤ 2 * P ^ (2 : ℕ) := by positivity
  rw [ballBoundR, ← Real.sqrt_sq (kernelRoot_nonneg s (fun j => secondKindC s j z) N)]
  refine Real.sqrt_le_sqrt (le_trans (secondKind_kernelRoot_sq_global h 0 z hS hP N) ?_)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (exp_arg_mono h hz)) hcR

/-- **The Nevanlinna matrix is entire and unimodular.**  Boundedness of the kernel at the single
point `0` makes all four limiting entries differentiable on the whole plane and forces
`A D - B C = 1` everywhere. -/
theorem nevanlinna_entire_unimodular (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) :
    Differentiable ℂ (nevAinf s) ∧ Differentiable ℂ (nevBinf s) ∧
      Differentiable ℂ (nevCinf s) ∧ Differentiable ℂ (nevDinf s) ∧
      ∀ z, nevAinf s z * nevDinf s z - nevBinf s z * nevCinf s z = 1 := by
  obtain ⟨S, P, hSpos, hPpos, hS, hP⟩ := h0b
  have hb : BoundedKernel s 0 := ⟨S, P, hSpos, hPpos, hS, hP⟩
  have key : ∀ r : ℝ,
      DifferentiableOn ℂ (nevAinf s) (Metric.ball 0 r) ∧
        DifferentiableOn ℂ (nevBinf s) (Metric.ball 0 r) ∧
        DifferentiableOn ℂ (nevCinf s) (Metric.ball 0 r) ∧
        DifferentiableOn ℂ (nevDinf s) (Metric.ball 0 r) ∧
        ∀ z ∈ Metric.ball (0:ℂ) r,
          nevAinf s z * nevDinf s z - nevBinf s z * nevCinf s z = 1 := by
    intro r
    have hnorm : ∀ z ∈ Metric.ball (0:ℂ) r, ‖z‖ ≤ r := by
      intro z hz
      have := Metric.mem_ball.mp hz
      rw [dist_zero_right] at this
      exact this.le
    exact nevanlinna_holomorphic_unimodular h (Metric.ball 0 r) Metric.isOpen_ball hS hP
      (fun z hz N => kernelRoot_le_ballBoundQ h hS hP (hnorm z hz) N)
      (fun z hz N => kernelRoot_le_ballBoundR h hS hP (hnorm z hz) N)
      hb (fun z _ => boundedKernel_global h hb z)
  have hmem : ∀ z : ℂ, z ∈ Metric.ball (0:ℂ) (‖z‖ + 1) := by
    intro z
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  refine ⟨fun z => ?_, fun z => ?_, fun z => ?_, fun z => ?_, fun z => ?_⟩
  · exact ((key (‖z‖ + 1)).1).differentiableAt (Metric.isOpen_ball.mem_nhds (hmem z))
  · exact ((key (‖z‖ + 1)).2.1).differentiableAt (Metric.isOpen_ball.mem_nhds (hmem z))
  · exact ((key (‖z‖ + 1)).2.2.1).differentiableAt (Metric.isOpen_ball.mem_nhds (hmem z))
  · exact ((key (‖z‖ + 1)).2.2.2.1).differentiableAt (Metric.isOpen_ball.mem_nhds (hmem z))
  · exact (key (‖z‖ + 1)).2.2.2.2 z (hmem z)

/-- The good set is closed, discharging the hypothesis of the clopen transfer. -/
theorem isClosed_boundedKernel (h : PositiveMomentForm s) :
    IsClosed {z : ℂ | BoundedKernel s z} := by
  rcases Set.eq_empty_or_nonempty {z : ℂ | BoundedKernel s z} with hempty | ⟨z₀, hz₀⟩
  · rw [hempty]; exact isClosed_empty
  · have huniv : {z : ℂ | BoundedKernel s z} = Set.univ :=
      Set.eq_univ_of_forall fun z => boundedKernel_global h hz₀ z
    rw [huniv]
    exact isClosed_univ

end HTGeometry
