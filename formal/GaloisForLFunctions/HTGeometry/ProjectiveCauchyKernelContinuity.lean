import GaloisForLFunctions.HTGeometry.LinftyKernelControlContinuity
import GaloisForLFunctions.HTGeometry.ProjectiveCauchyDensityControl
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Operator-norm continuity of projective Cauchy-jet controls in their nodes

On a packet of upper-half-plane nodes with a common positive imaginary lower bound, the projective
resolvent varies Lipschitz-continuously in the sup norm on `OnePoint ℝ`.  Taking powers gives every
Cauchy-jet column; finite packet assembly, the continuous inclusion into `L¹`, and continuity of
the `L¹`-kernel pairing then give operator-norm continuity of the actual `L∞` density-control map.

This is the analytic compact-patch continuity required by the uniform finite-probe law.  The proof
uses the explicit universal bound

`‖(t-x)⁻¹ - (t-y)⁻¹‖ ≤ η⁻² ‖x-y‖`

for real `t` and nodes with imaginary part at least `η > 0`; both projective resolvents vanish at
infinity.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter MeasureTheory Topology
open scoped NNReal OnePoint

noncomputable section

/-- Complex nodes whose imaginary part has a fixed positive lower bound. -/
abbrev UpperNodeAtLeast (η : ℝ) := {x : ℂ // η ≤ x.im}

/-- The projective resolvent as a sup-norm continuous function of its parameter. -/
def projectiveResolventContinuousMap (η : ℝ) (hη : 0 < η)
    (x : UpperNodeAtLeast η) : C(OnePoint ℝ, ℂ) :=
  ⟨projectiveCauchyPower x.1 0,
    continuous_projectiveCauchyPower x.1 (ne_of_gt (hη.trans_le x.2)) 0⟩

lemma norm_real_sub_complex_ge_im (t : ℝ) (x : ℂ) :
    |x.im| ≤ ‖(t : ℂ) - x‖ := by
  have him := Complex.abs_im_le_norm ((t : ℂ) - x)
  simpa [Complex.sub_im] using him

/-- Uniform projective resolvent bound on a horizontal upper-half-plane collar. -/
lemma projectiveResolventContinuousMap_pointwise_dist_le
    (η : ℝ) (hη : 0 < η) (x y : UpperNodeAtLeast η) (t : OnePoint ℝ) :
    dist (projectiveResolventContinuousMap η hη x t)
        (projectiveResolventContinuousMap η hη y t) ≤
      η⁻¹ ^ 2 * dist x y := by
  cases t with
  | infty =>
      simp only [projectiveResolventContinuousMap, ContinuousMap.coe_mk,
        projectiveCauchyPower_infty, dist_zero_left]
      positivity
  | coe t =>
      have hxη : η ≤ ‖(t : ℂ) - x.1‖ := by
        exact x.2.trans (le_trans (le_abs_self x.1.im)
          (norm_real_sub_complex_ge_im t x.1))
      have hyη : η ≤ ‖(t : ℂ) - y.1‖ := by
        exact y.2.trans (le_trans (le_abs_self y.1.im)
          (norm_real_sub_complex_ge_im t y.1))
      have hx0 : (t : ℂ) - x.1 ≠ 0 := by
        intro hx
        rw [hx, norm_zero] at hxη
        linarith
      have hy0 : (t : ℂ) - y.1 ≠ 0 := by
        intro hy
        rw [hy, norm_zero] at hyη
        linarith
      rw [dist_eq_norm]
      simp only [projectiveResolventContinuousMap, ContinuousMap.coe_mk,
        projectiveCauchyPower_coe, Nat.zero_add, pow_one]
      rw [inv_sub_inv' hx0 hy0, norm_mul, norm_mul, norm_inv, norm_inv]
      have hxinv : ‖(t : ℂ) - x.1‖⁻¹ ≤ η⁻¹ := inv_le_inv₀ hη hxη
      have hyinv : ‖(t : ℂ) - y.1‖⁻¹ ≤ η⁻¹ := inv_le_inv₀ hη hyη
      have hxy : ‖((t : ℂ) - y.1) - ((t : ℂ) - x.1)‖ = dist x y := by
        simp [dist_eq_norm, norm_sub_rev]
      rw [hxy]
      nlinarith [norm_nonneg (x.1 - y.1), inv_pos.mpr hη]

/-- The complete projective resolvent varies continuously in sup norm with its upper node. -/
theorem continuous_projectiveResolventContinuousMap
    (η : ℝ) (hη : 0 < η) :
    Continuous (projectiveResolventContinuousMap η hη) := by
  let C : ℝ≥0 := ⟨η⁻¹ ^ 2, sq_nonneg η⁻¹⟩
  apply (LipschitzWith.of_dist_le_mul (K := C) ?_).continuous
  intro x y
  rw [dist_eq_norm]
  apply (ContinuousMap.norm_le (mul_nonneg (sq_nonneg η⁻¹) (dist_nonneg))).2
  intro t
  simpa [C, dist_eq_norm] using
    projectiveResolventContinuousMap_pointwise_dist_le η hη x y t

/-- A projective Cauchy power as a sup-norm continuous function on the parameter line. -/
def projectiveCauchyPowerContinuousMap (η : ℝ) (hη : 0 < η) (k : ℕ)
    (x : UpperNodeAtLeast η) : C(OnePoint ℝ, ℂ) :=
  (projectiveResolventContinuousMap η hη x) ^ (k + 1)

@[simp]
theorem projectiveCauchyPowerContinuousMap_apply
    (η : ℝ) (hη : 0 < η) (k : ℕ) (x : UpperNodeAtLeast η) (t : OnePoint ℝ) :
    projectiveCauchyPowerContinuousMap η hη k x t = projectiveCauchyPower x.1 k t := by
  cases t <;> simp [projectiveCauchyPowerContinuousMap, projectiveResolventContinuousMap,
    projectiveCauchyPower]

theorem continuous_projectiveCauchyPowerContinuousMap
    (η : ℝ) (hη : 0 < η) (k : ℕ) :
    Continuous (projectiveCauchyPowerContinuousMap η hη k) := by
  exact (continuous_projectiveResolventContinuousMap η hη).pow (k + 1)

/-- A complete finite projective Cauchy-jet packet as one continuous vector-valued function of the
projective parameter. -/
def projectiveCauchyJetContinuousMap
    {ι : Type*} (η : ℝ) (hη : 0 < η) (n : ι → ℕ)
    (x : ι → UpperNodeAtLeast η) : C(OnePoint ℝ, (Σ i, Fin (n i)) → ℂ) :=
  ⟨fun t s => projectiveCauchyPower (x s.1).1 s.2 t,
    continuous_pi fun s =>
      continuous_projectiveCauchyPower (x s.1).1
        (ne_of_gt (hη.trans_le (x s.1).2)) s.2⟩

@[simp]
theorem projectiveCauchyJetContinuousMap_apply
    {ι : Type*} (η : ℝ) (hη : 0 < η) (n : ι → ℕ)
    (x : ι → UpperNodeAtLeast η) (t : OnePoint ℝ) :
    projectiveCauchyJetContinuousMap η hη n x t =
      projectiveCauchyJetColumn (fun i => (x i).1) n t := by
  rfl

/-- Finite projective Cauchy-jet packets vary continuously in the sup norm with all their nodes. -/
theorem continuous_projectiveCauchyJetContinuousMap
    {ι : Type*} (η : ℝ) (hη : 0 < η) (n : ι → ℕ) :
    Continuous (projectiveCauchyJetContinuousMap η hη n) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply continuous_pi
  intro s
  have hx : Continuous
      (fun p : (ι → UpperNodeAtLeast η) × OnePoint ℝ => p.1 s.1) := by
    fun_prop
  exact continuous_eval.comp
    (((continuous_projectiveCauchyPowerContinuousMap η hη s.2).comp
      hx).prodMk continuous_snd)

/-- The canonical `L¹` class of the finite projective Cauchy-jet kernel. -/
def projectiveCauchyJetLpKernel
    {ι : Type*} [Fintype ι] (η : ℝ) (hη : 0 < η) (n : ι → ℕ)
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu]
    (x : ι → UpperNodeAtLeast η) :
    Lp ((Σ i, Fin (n i)) → ℂ) 1 mu :=
  ContinuousMap.toLp 1 mu ℝ (projectiveCauchyJetContinuousMap η hη n x)

/-- Projective Cauchy-jet kernels vary continuously as genuine `L¹` classes. -/
theorem continuous_projectiveCauchyJetLpKernel
    {ι : Type*} [Fintype ι] (η : ℝ) (hη : 0 < η) (n : ι → ℕ)
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu] :
    Continuous (projectiveCauchyJetLpKernel η hη n mu) := by
  exact (ContinuousMap.toLp 1 mu ℝ).continuous.comp
    (continuous_projectiveCauchyJetContinuousMap η hη n)

/-- The continuous-function `L¹` class is the exact class used by the existing Bochner-control
definition. -/
theorem projectiveCauchyJetLpKernel_eq_memLpToLp
    {ι : Type*} [Fintype ι] (η : ℝ) (hη : 0 < η) (n : ι → ℕ)
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu]
    (x : ι → UpperNodeAtLeast η) :
    projectiveCauchyJetLpKernel η hη n mu x =
      (memLp_projectiveCauchyJetColumn (fun i => (x i).1)
        (fun i => ne_of_gt (hη.trans_le (x i).2)) n mu).toLp
        (projectiveCauchyJetColumn (fun i => (x i).1) n) := by
  apply Lp.ext
  exact (ContinuousMap.coeFn_toLp mu
    (projectiveCauchyJetContinuousMap η hη n x)).trans
      (MemLp.coeFn_toLp _).symm

/-- **Projective Cauchy control continuity.** On a uniformly upper finite node packet, the actual
bounded-density control varies continuously in operator norm with the full node configuration. -/
theorem continuous_projectiveCauchyJetLinftyBochnerControl
    {ι : Type*} [Fintype ι] (η : ℝ) (hη : 0 < η) (n : ι → ℕ)
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu] :
    Continuous (fun x : ι → UpperNodeAtLeast η =>
      linftyBochnerControl mu
        (projectiveCauchyJetColumn (fun i => (x i).1) n)
        (memLp_projectiveCauchyJetColumn (fun i => (x i).1)
          (fun i => ne_of_gt (hη.trans_le (x i).2)) n mu)) := by
  apply continuous_linftyBochnerControl_of_continuous_toLp
  have heq : (fun x : ι → UpperNodeAtLeast η =>
      (memLp_projectiveCauchyJetColumn (fun i => (x i).1)
        (fun i => ne_of_gt (hη.trans_le (x i).2)) n mu).toLp
        (projectiveCauchyJetColumn (fun i => (x i).1) n)) =
      projectiveCauchyJetLpKernel η hη n mu := by
    funext x
    exact (projectiveCauchyJetLpKernel_eq_memLpToLp η hη n mu x).symm
  rw [heq]
  exact continuous_projectiveCauchyJetLpKernel η hη n mu

end

end GaloisForLFunctions.HTGeometry
