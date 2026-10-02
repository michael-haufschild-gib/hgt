import GaloisForLFunctions.RHTower.SoninMixedApertureCurvature
import GaloisForLFunctions.RHTower.SoninApertureWardCurvature
import GaloisForLFunctions.RHTower.SoninBurnolLogShellChannel

/-!
# Coherent Sonin aperture curvature and Ward transgression

The source coefficients are assembled before taking the Gram product. Consequently every
mixed scale and every complex interference term contributes to the aperture curvature.
The full curvature retains the concrete relative ideal, its real trace is minus the
Hilbert--Schmidt energy of the coherent successive-layer transition, and zero trace detects
the entire curvature operator.

Symmetrizing that transition supplies a canonical self-adjoint Ward channel. Its cutoff
commutator energy cancels twice the curvature trace exactly. This finite quadratic identity
does not assert a prime--Gamma completion or a degree-three Hardy-index comparison.
-/

noncomputable section
namespace RHTower
open ContinuousLinearMap
open scoped BigOperators

variable {ι : Type*}

private theorem adjoint_smul_even (z : ℂ) (T : evenSubspace →L[ℂ] evenSubspace) :
    adjoint (z • T) = star z • adjoint T := by
  change star (z • T) = star z • star T
  rw [star_smul]


private theorem adjoint_sum_smul_mul_sum_smul
    (s : Finset ι) (Y : ι → evenSubspace →L[ℂ] evenSubspace) (u : ι → ℂ) :
    adjoint (∑ i ∈ s, u i • Y i) * (∑ j ∈ s, u j • Y j) =
      ∑ i ∈ s, ∑ j ∈ s, (star (u i) * u j) • (adjoint (Y i) * Y j) := by
  rw [adjoint_sum_even, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [adjoint_smul_even, smul_mul_even, mul_smul_even, smul_smul]

/-- Coherent finite source transition through the first lost aperture layer. -/
def soninCoherentApertureLostTransition (s : Finset ι) (a b : ℝ)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) : evenSubspace →L[ℂ] evenSubspace :=
  ∑ i ∈ s, u i • evenSoninApertureLostTransition a b (p i) (hp i)

/-- Coherent coupling of two successive aperture layers, retaining every source phase. -/
def soninCoherentApertureSuccessiveLayerTransition (s : Finset ι) (a b c : ℝ)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) : evenSubspace →L[ℂ] evenSubspace :=
  ∑ i ∈ s, u i • evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i)

/-- Full sesquilinear aperture curvature of a finite source packet. -/
def soninCoherentApertureCurvature (s : Finset ι) (a b c : ℝ)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) : evenSubspace →L[ℂ] evenSubspace :=
  ∑ i ∈ s, ∑ j ∈ s, (star (u i) * u j) •
    evenSoninMixedApertureRestrictionCurvature a b c (p i) (p j) (hp i) (hp j)

/-- The full mixed packet is the curvature of its actual coherent Gram operator. -/
theorem soninCoherentApertureCurvature_eq_compression_sub_self
    (s : Finset ι) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) :
    soninCoherentApertureCurvature s a b c p hp u =
      evenCentralSoninProjection c *
        (adjoint (soninCoherentApertureLostTransition s a b p hp u) *
          soninCoherentApertureLostTransition s a b p hp u) *
        evenCentralSoninProjection c -
      adjoint (soninCoherentApertureLostTransition s a b p hp u) *
        soninCoherentApertureLostTransition s a b p hp u := by
  unfold soninCoherentApertureCurvature soninCoherentApertureLostTransition
  simp only [evenSoninMixedApertureRestrictionCurvature_eq_compression_sub_self hbc,
    evenSoninMixedApertureRestrictionDefect_eq_adjoint_mul hab]
  rw [adjoint_sum_smul_mul_sum_smul]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_even, smul_mul_even,
    smul_sub, Finset.sum_sub_distrib]

/-- The coherent successive transition is the exact boundary of the coherent lost transition. -/
theorem soninCoherentApertureSuccessiveLayerTransition_eq_boundary
    (s : Finset ι) {a b c : ℝ} (hbc : b ≤ c)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) :
    soninCoherentApertureSuccessiveLayerTransition s a b c p hp u =
      soninCoherentApertureLostTransition s a b p hp u *
        (1 - evenCentralSoninProjection c) := by
  simp only [soninCoherentApertureSuccessiveLayerTransition,
    soninCoherentApertureLostTransition,
    evenSoninApertureSuccessiveLayerTransition_eq_boundary hbc,
    Finset.sum_mul, smul_mul_even]

/-- Coherent curvature retains the actual principal-relative ideal at every finite size. -/
theorem soninCoherentApertureCurvature_mem_principalRelativeIdeal
    (s : Finset ι) {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) (hcp : ∀ i ∈ s, c ≤ p i * a) :
    IsSoninPrincipalRelativeIdeal (soninCoherentApertureCurvature s a b c p hp u) := by
  refine IsSoninPrincipalRelativeIdeal.sum s _ fun i hi =>
    IsSoninPrincipalRelativeIdeal.sum s _ fun j hj => ?_
  exact (evenSoninMixedApertureRestrictionCurvature_mem_principalRelativeIdeal
    ha hab hbc (hp i) (hp j) (hcp i hi) (hcp j hj)).smul _

/-- The coherent boundary retains the same concrete ideal, including interference. -/
theorem soninCoherentApertureSuccessiveLayerTransition_mem_principalRelativeIdeal
    (s : Finset ι) {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) (hcp : ∀ i ∈ s, c ≤ p i * a) :
    IsSoninPrincipalRelativeIdeal
      (soninCoherentApertureSuccessiveLayerTransition s a b c p hp u) := by
  refine IsSoninPrincipalRelativeIdeal.sum s _ fun i hi => ?_
  exact (evenSoninApertureSuccessiveLayerTransition_mem_principalRelativeIdeal
    ha (ha.trans_le hab) ((ha.trans_le hab).trans_le hbc)
    hab hbc (hp i) (hcp i hi)).smul _

/-- Coherent source curvature has negative Hilbert--Schmidt Gram energy, with all cross terms. -/
theorem re_opTrace_soninCoherentApertureCurvature
    (s : Finset ι) {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) (hcp : ∀ i ∈ s, c ≤ p i * a) :
    (opTrace (soninCoherentApertureCurvature s a b c p hp u)).re =
      -hsNormSq (soninCoherentApertureSuccessiveLayerTransition s a b c p hp u) := by
  let P := evenCentralSoninProjection c
  let Y := soninCoherentApertureLostTransition s a b p hp u
  have hP : P * P = P :=
    (evenCentralSoninProjection_mul_of_le (a := c) (b := c) le_rfl).1
  have hK := (soninCoherentApertureCurvature_mem_principalRelativeIdeal
    s ha hab hbc p hp u hcp).memSchattenClass_one
  rw [soninCoherentApertureCurvature_eq_compression_sub_self s hab hbc] at hK ⊢
  rw [soninCoherentApertureSuccessiveLayerTransition_eq_boundary s hbc]
  exact re_opTrace_compression_sub_self_eq_neg_hsNormSq P (adjoint Y * Y) Y
    hP (adjoint_evenCentralSoninProjection c) rfl hK

/-- Coherent curvature vanishes exactly when its combined source transition vanishes. -/
theorem soninCoherentApertureCurvature_eq_zero_iff
    (s : Finset ι) {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) (hcp : ∀ i ∈ s, c ≤ p i * a) :
    soninCoherentApertureCurvature s a b c p hp u = 0 ↔
      soninCoherentApertureSuccessiveLayerTransition s a b c p hp u = 0 := by
  let P := evenCentralSoninProjection c
  let Y := soninCoherentApertureLostTransition s a b p hp u
  have hP : P * P = P :=
    (evenCentralSoninProjection_mul_of_le (a := c) (b := c) le_rfl).1
  have hK := (soninCoherentApertureCurvature_mem_principalRelativeIdeal
    s ha hab hbc p hp u hcp).memSchattenClass_one
  rw [soninCoherentApertureCurvature_eq_compression_sub_self s hab hbc] at hK ⊢
  rw [soninCoherentApertureSuccessiveLayerTransition_eq_boundary s hbc]
  exact compression_sub_self_eq_zero_iff_boundary_zero P (adjoint Y * Y) Y
    hP (adjoint_evenCentralSoninProjection c) rfl hK

/-- Zero scalar curvature detects the entire coherent curvature operator. -/
theorem re_opTrace_soninCoherentApertureCurvature_eq_zero_iff
    (s : Finset ι) {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) (hcp : ∀ i ∈ s, c ≤ p i * a) :
    (opTrace (soninCoherentApertureCurvature s a b c p hp u)).re = 0 ↔
      soninCoherentApertureCurvature s a b c p hp u = 0 := by
  let Z := soninCoherentApertureSuccessiveLayerTransition s a b c p hp u
  have hZ := soninCoherentApertureSuccessiveLayerTransition_mem_principalRelativeIdeal
    s ha hab hbc p hp u hcp
  have hHS : Z.IsHilbertSchmidt :=
    isHilbertSchmidt_of_adjoint_mul_self_memSchattenClass_one Z
      (hZ.leftMul (adjoint Z)).memSchattenClass_one
  rw [soninCoherentApertureCurvature_eq_zero_iff s ha hab hbc p hp u hcp,
    re_opTrace_soninCoherentApertureCurvature s ha hab hbc p hp u hcp,
    neg_eq_zero, hsNormSq_eq_zero_iff hHS]

/-- Canonical self-adjoint Ward channel of the coherent source. -/
def soninCoherentApertureWardChannel (s : Finset ι) (a b c : ℝ)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) : evenSubspace →L[ℂ] evenSubspace :=
  soninCoherentApertureSuccessiveLayerTransition s a b c p hp u +
    adjoint (soninCoherentApertureSuccessiveLayerTransition s a b c p hp u)

private theorem crossBoundary_symmetric_of_support
    (E Z : evenSubspace →L[ℂ] evenSubspace) (hE : adjoint E = E)
    (hEZ : E * Z = Z) (hZE : Z * E = 0) :
    crossBoundary E (Z + adjoint Z) = adjoint Z := by
  have hZaE : adjoint Z * E = adjoint Z := by
    have h := congrArg adjoint hEZ
    simpa only [adjoint_mul_clm, hE] using h
  have hEZa : E * adjoint Z = 0 := by
    have h := congrArg adjoint hZE
    simpa only [adjoint_mul_clm, hE, ContinuousLinearMap.adjoint.map_zero] using h
  unfold crossBoundary
  noncomm_ring [hEZ, hZE, hZaE, hEZa]

/-- The coherent Ward channel has exactly the full conjugate boundary transition. -/
theorem crossBoundary_soninCoherentApertureWardChannel
    (s : Finset ι) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) :
    crossBoundary (evenSoninApertureLayer a b)
      (soninCoherentApertureWardChannel s a b c p hp u) =
        adjoint (soninCoherentApertureSuccessiveLayerTransition s a b c p hp u) := by
  let E := evenSoninApertureLayer a b
  let F := evenSoninApertureLayer b c
  let Z := soninCoherentApertureSuccessiveLayerTransition s a b c p hp u
  have hE : E * E = E := evenSoninApertureLayer_mul_self hab
  have hFE : F * E = 0 := (evenSoninApertureLayers_successive_orthogonal hab hbc).2
  dsimp only [E, F] at hE hFE
  have hEZ : E * Z = Z := by
    dsimp only [E, Z, soninCoherentApertureSuccessiveLayerTransition,
      evenSoninApertureSuccessiveLayerTransition]
    simp only [Finset.mul_sum, mul_smul_even, ← mul_assoc, hE]
  have hZE : Z * E = 0 := by
    dsimp only [E, Z, soninCoherentApertureSuccessiveLayerTransition,
      evenSoninApertureSuccessiveLayerTransition]
    simp only [Finset.sum_mul, smul_mul_even, mul_assoc, hFE, mul_zero, smul_zero,
      Finset.sum_const_zero]
  exact crossBoundary_symmetric_of_support E Z (adjoint_evenSoninApertureLayer a b) hEZ hZE

/-- Exact coherent Ward transgression: every source cross term contributes to cancellation. -/
theorem two_mul_re_opTrace_soninCoherentApertureCurvature_add_WardEnergy_eq_zero
    (s : Finset ι) {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) (hcp : ∀ i ∈ s, c ≤ p i * a) :
    2 * (opTrace (soninCoherentApertureCurvature s a b c p hp u)).re +
      hsNormSq (ccmCommutator (soninCoherentApertureWardChannel s a b c p hp u)
        (evenSoninApertureLayer a b)) = 0 := by
  let E := evenSoninApertureLayer a b
  let Z := soninCoherentApertureSuccessiveLayerTransition s a b c p hp u
  let X := soninCoherentApertureWardChannel s a b c p hp u
  have hE : IsIdempotentElem E := evenSoninApertureLayer_mul_self hab
  have hEa : adjoint E = E := adjoint_evenSoninApertureLayer a b
  have hXa : adjoint X = X := by
    dsimp only [X, soninCoherentApertureWardChannel]
    rw [adjoint_add_clm, adjoint_adjoint, add_comm]
  have hZ := soninCoherentApertureSuccessiveLayerTransition_mem_principalRelativeIdeal
    s ha hab hbc p hp u hcp
  have hHS : Z.IsHilbertSchmidt :=
    isHilbertSchmidt_of_adjoint_mul_self_memSchattenClass_one Z
      (hZ.leftMul (adjoint Z)).memSchattenClass_one
  have hcross : crossBoundary E X = adjoint Z :=
    crossBoundary_soninCoherentApertureWardChannel s hab hbc p hp u
  have hcrossHS : (crossBoundary E X).IsHilbertSchmidt := by
    rw [hcross]
    exact hHS.adjoint
  have hward := hsNormSq_commutator_eq_two_mul_crossBoundary_of_selfAdjoint
    E X hE hEa hXa hcrossHS
  rw [hcross, hHS.hsNormSq_adjoint] at hward
  rw [re_opTrace_soninCoherentApertureCurvature s ha hab hbc p hp u hcp]
  change 2 * -hsNormSq Z + hsNormSq (ccmCommutator X E) = 0
  rw [hward]
  ring

end RHTower

end
