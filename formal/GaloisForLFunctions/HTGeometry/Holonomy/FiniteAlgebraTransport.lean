import GaloisForLFunctions.HTGeometry.LinearAlgebra.ScalingNilpotence
import GaloisForLFunctions.HTGeometry.ClockCalibrationHasse

/-!
# Finite algebra transport forces a global clock calibration

Let a graph carry nonnilpotent generators in a finite-dimensional real algebra.
If edge algebra automorphisms transport the generators up to positive scalar
factors, every closed-walk scalar factor is one. Reverse-edge reciprocity is
therefore a consequence, not additional data.

On a connected graph, the existing clock Hasse reconstruction gives a unique
positive calibration after fixing one basepoint. Dividing each generator by
its calibration removes the scalar factors from every edge transport. The
graph itself need not be finite. This is the finite-algebra form of the
no-scalar-monodromy and gauge reconstruction mechanisms in Alexa's Lemma 5.3
and Theorem 4.1.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

variable {V A : Type*} [Ring A] [Algebra ℝ A] [FiniteDimensional ℝ A]
    {G : SimpleGraph V}

/-- Positive edge readings give positive readings on every walk. -/
theorem clockWalkTransport_pos (c : V → V → ℝˣ)
    (hc : ∀ {u v}, G.Adj u v → 0 < (c u v : ℝ))
    {u v : V} (p : G.Walk u v) : 0 < ((clockWalkTransport c p : ℝˣ) : ℝ) := by
  induction p with
  | nil => exact zero_lt_one
  | cons h p ih =>
    change 0 < (c _ _ : ℝ) * ((clockWalkTransport c p : ℝˣ) : ℝ)
    exact mul_pos (hc h) ih

omit [FiniteDimensional ℝ A] in
/-- Operator transport along a walk rescales its generator by the scalar walk reading. -/
theorem clockWalkTransport_algebra (a : V → A) (c : V → V → ℝˣ)
    (t : V → V → (A ≃ₐ[ℝ] A))
    (ht : ∀ {u v}, G.Adj u v → t u v (a v) = (c u v : ℝ) • a u)
    {u v : V} (p : G.Walk u v) :
    clockWalkTransport t p (a v) = ((clockWalkTransport c p : ℝˣ) : ℝ) • a u := by
  induction p with
  | nil => exact (one_smul ℝ _).symm
  | @cons u w v h p ih =>
    change t u w (clockWalkTransport t p (a v)) =
      ((c u w : ℝ) * ((clockWalkTransport c p : ℝˣ) : ℝ)) • a u
    rw [ih, map_smul, ht h, smul_smul, mul_comm]

/-- Finite-dimensionality and nonnilpotent generators force every loop scale to be one. -/
theorem clockCalibrationFlat_of_algebra_transport (a : V → A)
    (ha : ∀ v, ¬ IsNilpotent (a v)) (c : V → V → ℝˣ)
    (hc : ∀ {u v}, G.Adj u v → 0 < (c u v : ℝ))
    (t : V → V → (A ≃ₐ[ℝ] A))
    (ht : ∀ {u v}, G.Adj u v → t u v (a v) = (c u v : ℝ) • a u) :
    ClockCalibrationFlat G c := by
  intro u p
  apply Units.ext
  exact (real_algHom_scale_eq_one_or_nilpotent (clockWalkTransport t p).toAlgHom
    (a u) ((clockWalkTransport c p : ℝˣ) : ℝ) (clockWalkTransport_pos c hc p)
    (clockWalkTransport_algebra a c t ht p)).resolve_right (ha u)

/-- Flatness forces inverse readings on reverse edges, even in a noncommutative group. -/
theorem clockCalibrationReversible_of_flat {B : Type*} [Group B] (c : V → V → B)
    (hf : ClockCalibrationFlat G c) : ClockCalibrationReversible G c := by
  intro u v huv
  have hh := hf u (.cons huv (.cons huv.symm .nil))
  change c u v * (c v u * 1) = 1 at hh
  rw [mul_one] at hh
  calc
    c v u = (c u v)⁻¹ * (c u v * c v u) := by group
    _ = (c u v)⁻¹ := by rw [hh, mul_one]

/-- Compatible positive scales on a connected graph are ratios of global calibrations. -/
theorem clockCalibrationExact_of_algebra_transport (hG : G.Connected) (a : V → A)
    (ha : ∀ v, ¬ IsNilpotent (a v)) (c : V → V → ℝˣ)
    (hc : ∀ {u v}, G.Adj u v → 0 < (c u v : ℝ))
    (t : V → V → (A ≃ₐ[ℝ] A))
    (ht : ∀ {u v}, G.Adj u v → t u v (a v) = (c u v : ℝ) • a u) :
    ClockCalibrationExact G c := by
  have hf := clockCalibrationFlat_of_algebra_transport a ha c hc t ht
  exact clockCalibrationExact_of_flat hG c (clockCalibrationReversible_of_flat c hf) hf

/-- Fixing one basepoint gives a unique positive calibration potential. -/
theorem existsUnique_positiveClockPotential_of_algebra_transport
    (hG : G.Connected) (root : V) (a : V → A)
    (ha : ∀ v, ¬ IsNilpotent (a v)) (c : V → V → ℝˣ)
    (hc : ∀ {u v}, G.Adj u v → 0 < (c u v : ℝ))
    (t : V → V → (A ≃ₐ[ℝ] A))
    (ht : ∀ {u v}, G.Adj u v → t u v (a v) = (c u v : ℝ) • a u) :
    ∃! g : V → ℝˣ, g root = 1 ∧ (∀ v, 0 < (g v : ℝ)) ∧
      ∀ {u v}, G.Adj u v → c u v = (g u)⁻¹ * g v := by
  classical
  have hf := clockCalibrationFlat_of_algebra_transport a ha c hc t ht
  obtain ⟨g, ⟨hgroot, hg⟩, huniq⟩ :=
    (clockCalibrationFlat_iff_existsUnique_normalizedPotential hG c
      (clockCalibrationReversible_of_flat c hf) root).mp hf
  have hgpos (v : V) : 0 < (g v : ℝ) := by
    obtain ⟨p⟩ := hG root v
    have hp := clockWalkTransport_of_exact c g hg p
    rw [hgroot, inv_one, one_mul] at hp
    rw [← hp]
    exact clockWalkTransport_pos c hc p
  exact ⟨g, ⟨hgroot, hgpos, hg⟩, fun h hh => huniq h ⟨hh.1, hh.2.2⟩⟩

omit [FiniteDimensional ℝ A] in
/-- Dividing each generator by its calibration removes every edge rescaling. -/
theorem algebraTransport_normalized (a : V → A) (c : V → V → ℝˣ)
    (t : V → V → (A ≃ₐ[ℝ] A))
    (ht : ∀ {u v}, G.Adj u v → t u v (a v) = (c u v : ℝ) • a u)
    (g : V → ℝˣ) (hg : ∀ {u v}, G.Adj u v → c u v = (g u)⁻¹ * g v)
    {u v : V} (huv : G.Adj u v) :
    t u v (((g v)⁻¹ : ℝˣ) • a v) = ((g u)⁻¹ : ℝˣ) • a u := by
  have hu : (g v)⁻¹ * c u v = (g u)⁻¹ := by
    rw [hg huv, mul_left_comm]
    simp
  have hv := congrArg (fun r : ℝˣ => (r : ℝ)) hu
  change ((g v)⁻¹ : ℝˣ).val * (c u v).val = ((g u)⁻¹ : ℝˣ).val at hv
  change t u v (((g v)⁻¹ : ℝˣ).val • a v) = ((g u)⁻¹ : ℝˣ).val • a u
  rw [map_smul, ht huv, smul_smul, hv]

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.clockCalibrationFlat_of_algebra_transport
#print axioms GaloisForLFunctions.HTGeometry.clockCalibrationReversible_of_flat
#print axioms GaloisForLFunctions.HTGeometry.existsUnique_positiveClockPotential_of_algebra_transport
#print axioms GaloisForLFunctions.HTGeometry.algebraTransport_normalized
