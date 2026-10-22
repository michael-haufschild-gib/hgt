import GaloisForLFunctions.RHTower.Suzuki.SuzukiStrongResolventLimit
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

/-- At every positive regularization scale, a nonnegative-spectral boundary transfer is a
contraction. -/
theorem norm_positiveBoundaryTransfer_le_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] {B : H →L[ℂ] H}
    (hsa : IsSelfAdjoint B) {M : ℝ}
    (hspec : spectrum ℝ B ⊆ Set.Icc 0 M)
    (eps : ℝ) (heps : 0 < eps) :
    ‖positiveBoundaryTransfer B eps‖ ≤ 1 := by
  rw [positiveBoundaryTransfer]
  have hcont : ContinuousOn (fun x : ℝ => x / (eps + x)) (spectrum ℝ B) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro x hx
    have hx0 := (hspec hx).1
    nlinarith
  refine norm_cfc_le_of_forall_le _ _ hcont hsa ?_
  intro x hx
  have hx0 := (hspec hx).1
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hx0 (by positivity))]
  exact (div_le_one (by nlinarith)).2 (by linarith)

/-- Positive regularization scale preserves positivity of boundary transfer. -/
theorem positiveBoundaryTransfer_isPositive
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] {B : H →L[ℂ] H}
    (hsa : IsSelfAdjoint B) {M : ℝ}
    (hspec : spectrum ℝ B ⊆ Set.Icc 0 M)
    (eps : ℝ) (heps : 0 < eps) :
    ContinuousLinearMap.IsPositive (positiveBoundaryTransfer B eps) := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).1
  rw [positiveBoundaryTransfer]
  have hcont : ContinuousOn (fun x : ℝ => x / (eps + x)) (spectrum ℝ B) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro x hx
    have hx0 := (hspec hx).1
    nlinarith
  exact (cfc_nonneg_iff _ B hcont hsa).2 fun x hx =>
    div_nonneg (hspec hx).1 (by nlinarith [(hspec hx).1])

/-- Positive regularization scale preserves positivity of regularized boundary inverse. -/
theorem positiveBoundaryInverse_isPositive
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] {B : H →L[ℂ] H}
    (hsa : IsSelfAdjoint B) {M : ℝ}
    (hspec : spectrum ℝ B ⊆ Set.Icc 0 M)
    (eps : ℝ) (heps : 0 < eps) :
    ContinuousLinearMap.IsPositive (positiveBoundaryInverse B eps) := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).1
  rw [positiveBoundaryInverse]
  have hcont : ContinuousOn (fun x : ℝ => 1 / (eps + x)) (spectrum ℝ B) := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
    intro x hx
    have hx0 := (hspec hx).1
    nlinarith
  exact (cfc_nonneg_iff _ B hcont hsa).2 fun x hx =>
    one_div_nonneg.mpr (by nlinarith [(hspec hx).1])

/-- Resolvent defect identity: boundary transfer plus regularization times boundary inverse is the
identity operator. -/
theorem positiveBoundaryTransfer_add_smul_inverse_eq_id
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] {B : H →L[ℂ] H}
    (hsa : IsSelfAdjoint B) {M : ℝ}
    (hspec : spectrum ℝ B ⊆ Set.Icc 0 M)
    (eps : ℝ) (heps : 0 < eps) :
    positiveBoundaryTransfer B eps +
        eps • positiveBoundaryInverse B eps =
      ContinuousLinearMap.id ℂ H := by
  have hinv : ContinuousOn (fun x : ℝ => 1 / (eps + x)) (spectrum ℝ B) := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
    intro x hx
    have hx0 := (hspec hx).1
    nlinarith
  have htrans : ContinuousOn (fun x : ℝ => x / (eps + x)) (spectrum ℝ B) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro x hx
    have hx0 := (hspec hx).1
    nlinarith
  rw [positiveBoundaryTransfer, positiveBoundaryInverse,
    ← cfc_const_mul eps (fun x : ℝ => 1 / (eps + x)) B hinv,
    ← cfc_add B (fun x : ℝ => x / (eps + x))
      (fun x : ℝ => eps * (1 / (eps + x))) htrans (by fun_prop)]
  have hcongr : cfc (fun x : ℝ => x / (eps + x) + eps * (1 / (eps + x))) B =
      cfc (fun _x : ℝ => (1 : ℝ)) B := by
    apply cfc_congr
    intro x hx
    have hx0 := (hspec hx).1
    field_simp
    ring
  rw [hcongr, cfc_const 1 B hsa, map_one]
  rw [ContinuousLinearMap.one_def]

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

/-- A positive boundary transfer cannot have a nonzero eigenvector with superunit eigenvalue.
Its singular capacity growth is therefore rank accumulation, not vector amplification. -/
theorem positiveBoundaryTransfer_eq_smul_imp_eq_zero_of_one_lt_norm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] {B : H →L[ℂ] H}
    (hsa : IsSelfAdjoint B) {M : ℝ}
    (hspec : spectrum ℝ B ⊆ Set.Icc 0 M)
    (eps : ℝ) (heps : 0 < eps) {c : ℂ} (hc : 1 < ‖c‖)
    {v : H} (hv : positiveBoundaryTransfer B eps v = c • v) :
    v = 0 := by
  have hop := norm_positiveBoundaryTransfer_le_one hsa hspec eps heps
  have happ := (positiveBoundaryTransfer B eps).le_opNorm v
  have hcv : ‖c‖ * ‖v‖ ≤ ‖v‖ := calc
    ‖c‖ * ‖v‖ = ‖c • v‖ := (norm_smul c v).symm
    _ = ‖positiveBoundaryTransfer B eps v‖ := congrArg norm hv.symm
    _ ≤ ‖positiveBoundaryTransfer B eps‖ * ‖v‖ := happ
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg v)
    _ = ‖v‖ := one_mul _
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg v]

/-- When zero belongs to the spectrum, the complementary normalized inverse channel has norm one
and likewise cannot have a nonzero superunit eigenvector. -/
theorem positiveBoundaryNormalizedInverse_eq_smul_imp_eq_zero_of_one_lt_norm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] {B : H →L[ℂ] H}
    (hsa : IsSelfAdjoint B) {M : ℝ}
    (hspec : spectrum ℝ B ⊆ Set.Icc 0 M)
    (hzero : (0 : ℝ) ∈ spectrum ℝ B)
    (eps : ℝ) (heps : 0 < eps) {c : ℂ} (hc : 1 < ‖c‖)
    {v : H} (hv : (eps • positiveBoundaryInverse B eps) v = c • v) :
    v = 0 := by
  have hop : ‖eps • positiveBoundaryInverse B eps‖ = 1 := by
    rw [norm_smul, norm_positiveBoundaryInverse hsa hspec hzero eps heps,
      Real.norm_eq_abs, abs_of_pos heps]
    field_simp
  have happ := (eps • positiveBoundaryInverse B eps).le_opNorm v
  have hcv : ‖c‖ * ‖v‖ ≤ ‖v‖ := calc
    ‖c‖ * ‖v‖ = ‖c • v‖ := (norm_smul c v).symm
    _ = ‖(eps • positiveBoundaryInverse B eps) v‖ := congrArg norm hv.symm
    _ ≤ ‖eps • positiveBoundaryInverse B eps‖ * ‖v‖ := happ
    _ = ‖v‖ := by rw [hop, one_mul]
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg v]

/-- Any eigenvalue of the unnormalized regularized inverse on a nonzero vector has norm at most
`1 / eps`.  Thus prescribed amplification forces entry into a quantitatively singular scale. -/
theorem norm_le_one_div_of_positiveBoundaryInverse_eq_smul
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] {B : H →L[ℂ] H}
    (hsa : IsSelfAdjoint B) {M : ℝ}
    (hspec : spectrum ℝ B ⊆ Set.Icc 0 M)
    (hzero : (0 : ℝ) ∈ spectrum ℝ B)
    (eps : ℝ) (heps : 0 < eps) {c : ℂ} {v : H} (hv0 : v ≠ 0)
    (hv : positiveBoundaryInverse B eps v = c • v) :
    ‖c‖ ≤ 1 / eps := by
  have hop := norm_positiveBoundaryInverse hsa hspec hzero eps heps
  have happ := (positiveBoundaryInverse B eps).le_opNorm v
  have hcv : ‖c‖ * ‖v‖ ≤ (1 / eps) * ‖v‖ := calc
    ‖c‖ * ‖v‖ = ‖c • v‖ := (norm_smul c v).symm
    _ = ‖positiveBoundaryInverse B eps v‖ := congrArg norm hv.symm
    _ ≤ ‖positiveBoundaryInverse B eps‖ * ‖v‖ := happ
    _ = (1 / eps) * ‖v‖ := by rw [hop]
  exact le_of_mul_le_mul_right hcv (norm_pos_iff.mpr hv0)

/-- A real eigenvalue `c ≠ 0` of the regularized inverse is equivalent to the original
operator eigenvalue `1 / c - eps` on the same vector.  In particular, large prescribed
resolvent gain selects a rigid positive spectral shell; it need not come from the zero boundary. -/
theorem positiveBoundaryInverse_eq_real_smul_imp_operator_eq_smul
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {B : H →L[ℂ] H}
    (hsa : IsSelfAdjoint B) {M : ℝ}
    (hspec : spectrum ℝ B ⊆ Set.Icc 0 M)
    (eps : ℝ) (heps : 0 < eps) {c : ℝ} (hc : c ≠ 0) {v : H}
    (hv : positiveBoundaryInverse B eps v = (c : ℂ) • v) :
    B v = (((1 / c : ℝ) - eps : ℝ) : ℂ) • v := by
  have hden : ∀ x ∈ spectrum ℝ B, eps + x ≠ 0 := by
    intro x hx
    have hx0 := (hspec hx).1
    nlinarith
  have hshift : ContinuousOn (fun x : ℝ => eps + x) (spectrum ℝ B) := by
    fun_prop
  have hinv : ContinuousOn (fun x : ℝ => 1 / (eps + x)) (spectrum ℝ B) :=
    ContinuousOn.div continuousOn_const (by fun_prop) hden
  have hmul := cfc_mul (fun x : ℝ => eps + x)
    (fun x : ℝ => 1 / (eps + x)) B hshift hinv
  have hone :
      cfc (fun x : ℝ => (eps + x) * (1 / (eps + x))) B =
        cfc (fun _x : ℝ => (1 : ℝ)) B := by
    apply cfc_congr
    intro x hx
    field_simp [hden x hx]
  rw [hone, cfc_const 1 B hsa, map_one] at hmul
  have hshiftCfc := cfc_add B (fun _x : ℝ => eps) (id : ℝ → ℝ)
    continuousOn_const continuousOn_id
  rw [cfc_const eps B hsa, cfc_id ℝ B hsa] at hshiftCfc
  have hshiftCfc' : cfc (fun x : ℝ => eps + x) B =
      (algebraMap ℝ (H →L[ℂ] H)) eps + B := by
    simpa only [id_eq] using hshiftCfc
  change (1 : H →L[ℂ] H) =
    cfc (fun x : ℝ => eps + x) B * positiveBoundaryInverse B eps at hmul
  have happ := congrArg (fun A : H →L[ℂ] H => A v) hmul
  rw [one_apply_eq_self, mul_apply_eq_comp, hv, hshiftCfc', add_apply] at happ
  simp only [map_smul, ContinuousLinearMap.algebraMap_apply] at happ
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have happ' := congrArg (fun x : H => (c : ℂ)⁻¹ • x) happ
  simp only [smul_add, smul_smul] at happ'
  rw [inv_mul_cancel₀ hcC] at happ'
  simp only [one_smul] at happ'
  have hcInv : (c : ℂ)⁻¹ = ((1 / c : ℝ) : ℂ) := by
    rw [one_div]
    exact (Complex.ofReal_inv c).symm
  rw [hcInv] at happ'
  linear_combination (norm := module) (-1 : ℂ) • happ'

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
