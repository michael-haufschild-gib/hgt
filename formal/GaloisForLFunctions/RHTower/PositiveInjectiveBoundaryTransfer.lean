import GaloisForLFunctions.RHTower.SuzukiStrongResolventLimit
import GaloisForLFunctions.HTGeometry.CfcNormBound

/-!
# Boundary transfer of a positive injective Hilbert operator

For a positive injective bounded operator `B` whose zero lies in its continuous spectrum, the
symbols

`x / (eps + x)` and `1 / (eps + x)`

define the canonical boundary transfer and regularized inverse.  The transfer converges strongly
to the identity but never in operator norm; the inverse has exact norm `1 / eps`.  Applied to a
range vector, the singular inverse recovers its full preimage strongly.

Definitions live at the generic Hilbert-operator level so the real continuous functional calculus
is elaborated once.  Concrete `lp` specializations can use this API without choosing a competing
CFC instance.
-/

open Filter Topology Set
open scoped ContinuousFunctionalCalculus

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- Canonical transfer at a nonnegative spectral boundary. -/
def positiveBoundaryTransfer {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →L[ℂ] H) (eps : ℝ) : H →L[ℂ] H :=
  cfc (fun x : ℝ => x / (eps + x)) B

/-- Canonical regularized inverse at a nonnegative spectral boundary. -/
def positiveBoundaryInverse {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →L[ℂ] H) (eps : ℝ) : H →L[ℂ] H :=
  cfc (fun x : ℝ => 1 / (eps + x)) B

/-- An injective positive boundary transfer converges strongly to the identity. -/
theorem positiveBoundaryTransfer_tendsto_id
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    {B : H →L[ℂ] H} (hsa : IsSelfAdjoint B)
    (hinj : Function.Injective B) {M : ℝ}
    (hspec : spectrum ℝ B ⊆ Set.Icc 0 M) (v : H) :
    Tendsto (fun eps : ℝ => positiveBoundaryTransfer B eps v)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds v) := by
  simpa [positiveBoundaryTransfer] using
    (tendsto_neumannShiftFamily_id hsa hinj (rho := 0) hspec v)

/-- The regularized inverse applied to a range vector is exactly the boundary transfer. -/
theorem positiveBoundaryInverse_apply_operator
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {B : H →L[ℂ] H}
    (hsa : IsSelfAdjoint B) {M : ℝ}
    (hspec : spectrum ℝ B ⊆ Set.Icc 0 M)
    (eps : ℝ) (heps : 0 < eps) (v : H) :
    positiveBoundaryInverse B eps (B v) =
      positiveBoundaryTransfer B eps v := by
  have hden : ∀ x ∈ spectrum ℝ B, eps + x ≠ 0 := by
    intro x hx
    have hx0 := (hspec hx).1
    nlinarith
  have hinv : ContinuousOn (fun x : ℝ => 1 / (eps + x)) (spectrum ℝ B) :=
    ContinuousOn.div continuousOn_const (by fun_prop) hden
  have hmul := cfc_mul (fun x : ℝ => 1 / (eps + x)) (id : ℝ → ℝ)
    B hinv continuousOn_id
  rw [cfc_id ℝ B hsa] at hmul
  change cfc (fun x : ℝ => (1 / (eps + x)) * x) B = _ at hmul
  have hcongr : cfc (fun x : ℝ => (1 / (eps + x)) * x) B =
      positiveBoundaryTransfer B eps := by
    rw [positiveBoundaryTransfer]
    exact cfc_congr fun x hx => by field_simp
  rw [← hcongr, hmul, positiveBoundaryInverse]
  rfl

/-- Strong recovery of every vector from the corresponding boundary-range anomaly. -/
theorem positiveBoundaryInverse_operator_tendsto
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    {B : H →L[ℂ] H} (hsa : IsSelfAdjoint B)
    (hinj : Function.Injective B) {M : ℝ}
    (hspec : spectrum ℝ B ⊆ Set.Icc 0 M) (v : H) :
    Tendsto (fun eps : ℝ => positiveBoundaryInverse B eps (B v))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds v) := by
  refine (positiveBoundaryTransfer_tendsto_id hsa hinj hspec v).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with eps heps
  exact (positiveBoundaryInverse_apply_operator hsa hspec eps heps v).symm

/-- Exact blow-up of the regularized inverse when zero belongs to the real spectrum. -/
theorem norm_positiveBoundaryInverse
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    {B : H →L[ℂ] H} (hsa : IsSelfAdjoint B) {M : ℝ}
    (hspec : spectrum ℝ B ⊆ Set.Icc 0 M)
    (hzero : (0 : ℝ) ∈ spectrum ℝ B)
    (eps : ℝ) (heps : 0 < eps) :
    ‖positiveBoundaryInverse B eps‖ = 1 / eps := by
  have hcont : ContinuousOn (fun x : ℝ => 1 / (eps + x)) (spectrum ℝ B) := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
    intro x hx
    have hx0 := (hspec hx).1
    nlinarith
  apply le_antisymm
  · rw [positiveBoundaryInverse]
    refine norm_cfc_le_of_forall_le _ _ hcont hsa ?_
    intro x hx
    have hx0 := (hspec hx).1
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (by linarith))]
    exact one_div_le_one_div_of_le heps (by linarith)
  · rw [positiveBoundaryInverse]
    have hz := norm_apply_le_norm_cfc (fun x : ℝ => 1 / (eps + x))
      B hzero hcont hsa
    simpa [abs_of_pos heps, one_div] using hz

/-- Difference between transfer and identity as one continuous-functional-calculus symbol. -/
theorem positiveBoundaryTransfer_sub_id_eq_cfc
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {B : H →L[ℂ] H}
    (hsa : IsSelfAdjoint B) {M : ℝ}
    (hspec : spectrum ℝ B ⊆ Set.Icc 0 M)
    (eps : ℝ) (heps : 0 < eps) :
    positiveBoundaryTransfer B eps - ContinuousLinearMap.id ℂ H =
      cfc (fun x : ℝ => x / (eps + x) - 1) B := by
  have hcont : ContinuousOn (fun x : ℝ => x / (eps + x)) (spectrum ℝ B) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro x hx
    have hx0 := (hspec hx).1
    nlinarith
  have hsub := cfc_sub (fun x : ℝ => x / (eps + x))
    (fun _ : ℝ => (1 : ℝ)) B hcont continuousOn_const
  rw [cfc_const 1 B hsa, map_one] at hsub
  exact hsub.symm

/-- Strong convergence is maximally non-uniform when zero belongs to the spectrum. -/
theorem norm_positiveBoundaryTransfer_sub_id
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    {B : H →L[ℂ] H} (hsa : IsSelfAdjoint B) {M : ℝ}
    (hspec : spectrum ℝ B ⊆ Set.Icc 0 M)
    (hzero : (0 : ℝ) ∈ spectrum ℝ B)
    (eps : ℝ) (heps : 0 < eps) :
    ‖positiveBoundaryTransfer B eps - ContinuousLinearMap.id ℂ H‖ = 1 := by
  rw [positiveBoundaryTransfer_sub_id_eq_cfc hsa hspec eps heps]
  have hcont : ContinuousOn (fun x : ℝ => x / (eps + x) - 1)
      (spectrum ℝ B) := by
    refine (ContinuousOn.div (by fun_prop) (by fun_prop) ?_).sub continuousOn_const
    intro x hx
    have hx0 := (hspec hx).1
    nlinarith
  apply le_antisymm
  · refine norm_cfc_le_of_forall_le _ _ hcont hsa ?_
    intro x hx
    have hx0 := (hspec hx).1
    have hden : eps + x ≠ 0 := by nlinarith
    have heq : x / (eps + x) - 1 = -eps / (eps + x) := by
      field_simp
      ring
    rw [Real.norm_eq_abs, heq, abs_div, abs_neg, abs_of_pos heps,
      abs_of_pos (by nlinarith)]
    exact (div_le_one (by nlinarith)).2 (by linarith)
  · have hz := norm_apply_le_norm_cfc
      (fun x : ℝ => x / (eps + x) - 1) B hzero hcont hsa
    norm_num at hz ⊢
    exact hz

end GaloisForLFunctions.RHTower
