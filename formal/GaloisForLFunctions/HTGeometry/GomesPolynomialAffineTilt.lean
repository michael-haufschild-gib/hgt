import GaloisForLFunctions.HTGeometry.GomesPolynomialGroundTensorGeometry

/-!
# Affine log-tilts of the polynomial tensor sector

The finite sector is stable under every lower-degree perturbation. In particular,
arbitrary affine log-tilts preserve finite mass, Schwartz exponential membership,
and existence of a nonzero ground state. The affine factors themselves need not
have finite mass; their induced action on the finite tensor sector is nevertheless closed.
-/

noncomputable section
open Polynomial MeasureTheory
open scoped Topology NNReal ENNReal SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- A finite polynomial profile necessarily has degree at least two. -/
theorem gomesFinitePolynomialProfile_degree_gt_one (P : GomesFinitePolynomialProfile) :
    1 < P.val.natDegree := by
  have hp := (gomesFinitePolynomialProfiles_mem_iff P.val).mp P.property
  obtain ⟨k, hk⟩ := hp.2.1
  have hkpos : 0 < k := by nlinarith [hp.1]
  have hkone : 1 ≤ k := Nat.succ_le_iff.mpr hkpos
  nlinarith

/-- Arbitrary lower-degree perturbations stay inside the finite tensor sector. -/
def gomesFinitePolynomialPerturb (P : GomesFinitePolynomialProfile)
    (Q : {Q : ℝ[X] // Q.natDegree < P.val.natDegree}) : GomesFinitePolynomialProfile :=
  ⟨P.val + Q.val, by
    rw [gomesFinitePolynomialProfiles_mem_iff,
      natDegree_add_eq_left_of_natDegree_lt Q.property,
      leadingCoeff_add_of_degree_lt' (degree_lt_degree Q.property)]
    exact (gomesFinitePolynomialProfiles_mem_iff P.val).mp P.property⟩

/-- Lower-degree perturbation preserves the degree exactly. -/
theorem gomesFinitePolynomialPerturb_natDegree (P : GomesFinitePolynomialProfile)
    (Q : {Q : ℝ[X] // Q.natDegree < P.val.natDegree}) :
    (gomesFinitePolynomialPerturb P Q).val.natDegree = P.val.natDegree :=
  natDegree_add_eq_left_of_natDegree_lt Q.property

/-- Lower-degree perturbation preserves the leading coefficient exactly. -/
theorem gomesFinitePolynomialPerturb_leadingCoeff (P : GomesFinitePolynomialProfile)
    (Q : {Q : ℝ[X] // Q.natDegree < P.val.natDegree}) :
    (gomesFinitePolynomialPerturb P Q).val.leadingCoeff = P.val.leadingCoeff :=
  leadingCoeff_add_of_degree_lt' (degree_lt_degree Q.property)

/-- An arbitrary affine change in log-density. -/
def gomesPolynomialAffineTilt (H : ℝ[X]) (t c : ℝ) : ℝ[X] := H + (C t * X + C c)

/-- Every affine log-tilt acts on the full finite polynomial sector. -/
def gomesFinitePolynomialTilt (P : GomesFinitePolynomialProfile) (t c : ℝ) :
    GomesFinitePolynomialProfile :=
  gomesFinitePolynomialPerturb P ⟨C t * X + C c, by
    apply lt_of_le_of_lt (natDegree_add_le _ _) (lt_of_le_of_lt _ (gomesFinitePolynomialProfile_degree_gt_one P))
    exact max_le ((natDegree_C_mul_le t X).trans natDegree_X_le) (by rw [natDegree_C]; exact Nat.zero_le _)⟩

/-- Successive affine tilts add their parameters. -/
theorem gomesPolynomialAffineTilt_add (H : ℝ[X]) (s a t b : ℝ) :
    gomesPolynomialAffineTilt (gomesPolynomialAffineTilt H s a) t b =
      gomesPolynomialAffineTilt H (s + t) (a + b) := by
  simp only [gomesPolynomialAffineTilt, map_add]
  ring

/-- Opposite affine tilts undo each other exactly. -/
theorem gomesPolynomialAffineTilt_inverse (H : ℝ[X]) (t c : ℝ) :
    gomesPolynomialAffineTilt (gomesPolynomialAffineTilt H t c) (-t) (-c) = H := by
  rw [gomesPolynomialAffineTilt_add]
  simp only [add_neg_cancel, gomesPolynomialAffineTilt, map_zero, zero_mul, add_zero]

/-- Finite mass is invariant under all affine log-tilts, for every polynomial. -/
theorem gomesPolynomialAffineTilt_finite_iff (H : ℝ[X]) (t c : ℝ) :
    IsFiniteMeasure (gomesDilatonMeasure (gomesPolynomialAffineTilt H t c)) ↔
      IsFiniteMeasure (gomesDilatonMeasure H) := by
  constructor
  · intro h
    have hh := (gomesFinitePolynomialTilt ⟨gomesPolynomialAffineTilt H t c, h⟩ (-t) (-c)).property
    change IsFiniteMeasure (gomesDilatonMeasure
      (gomesPolynomialAffineTilt (gomesPolynomialAffineTilt H t c) (-t) (-c))) at hh
    rwa [gomesPolynomialAffineTilt_inverse] at hh
  · intro h
    exact (gomesFinitePolynomialTilt ⟨H, h⟩ t c).property

/-- The complete pure-exponential Schwartz sector is invariant under affine tilts. -/
theorem gomesPolynomialAffineTilt_schwartz_iff (H : ℝ[X]) (t c : ℝ) :
    (∃ f : 𝓢(ℝ, ℝ), ∀ x, f x = Real.exp ((gomesPolynomialAffineTilt H t c).eval x)) ↔
      ∃ f : 𝓢(ℝ, ℝ), ∀ x, f x = Real.exp (H.eval x) := by
  rw [gomesPolynomialExponential_schwartz_iff, gomesPolynomialExponential_schwartz_iff,
    gomesPolynomialAffineTilt_finite_iff]

/-- Affine tilts preserve existence of nonzero Schwartz ground states without coefficient assumptions. -/
theorem gomesPolynomialAffineTilt_ground_iff (H : ℝ[X]) (t c : ℝ) :
    (∃ ψ : 𝓢(ℝ, ℂ), ψ ≠ 0 ∧ dilatonHamiltonianCLM (gomesPolynomialAffineTilt H t c) ψ = 0) ↔
      ∃ ψ : 𝓢(ℝ, ℂ), ψ ≠ 0 ∧ dilatonHamiltonianCLM H ψ = 0 := by
  rw [gomesPolynomialHamiltonian_nonzero_kernel_iff, gomesPolynomialHamiltonian_nonzero_kernel_iff,
    gomesPolynomialAffineTilt_finite_iff]

/-- The normalization operation yields a probability law after tilt exactly when it did before. -/
theorem gomesPolynomialAffineTilt_probability_iff (H : ℝ[X]) (t c : ℝ) :
    IsProbabilityMeasure (gomesDilatonMassNormalized (gomesPolynomialAffineTilt H t c)) ↔
      IsProbabilityMeasure (gomesDilatonMassNormalized H) := by
  rw [gomesDilatonMassNormalized_probability_iff, gomesDilatonMassNormalized_probability_iff,
    gomesPolynomialAffineTilt_finite_iff]

end GaloisForLFunctions.HTGeometry
