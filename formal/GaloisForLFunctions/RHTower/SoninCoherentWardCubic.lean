import GaloisForLFunctions.RHTower.SoninRelativeWardCubic

/-!
# The cubic character of the actual coherent Sonin Ward completion

For every finite complex source packet, let `Y` be its lost aperture transition,
`Z=Y(1-Q_c)` its successive-layer transition, and `W=Y Q_c` its retained transition.
Adding half the canonical Ward commutator Gram to the actual curvature gives
`B=K+(Z†Z+ZZ†)/2`. This retains the concrete relative ideal and has zero complex
trace, but its cubic trace is `-(3/2)||ZZ†W||²_HS`.

The cubic trace vanishes precisely when `Z†W=0`. Positivity of either sign of `B`
requires `Z=0`. All source cross terms remain; the geometric and ideal assumptions
are discharged for the actual Sonin operators. No joint prime--Gamma or RH claim
is made.
-/

noncomputable section
namespace RHTower
open ContinuousLinearMap

variable {ι : Type*}

/-- Coherent transition from the retained final aperture into the first lost layer. -/
def soninCoherentApertureRetainedTransition (s : Finset ι) (a b c : ℝ)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) : evenSubspace →L[ℂ] evenSubspace :=
  soninCoherentApertureLostTransition s a b p hp u * evenCentralSoninProjection c

/-- Actual curvature with half the full symmetric Ward Gram energy added as an operator. -/
def soninCoherentBalancedWardCompletion (s : Finset ι) (a b c : ℝ)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) : evenSubspace →L[ℂ] evenSubspace :=
  let Z := soninCoherentApertureSuccessiveLayerTransition s a b c p hp u
  soninCoherentApertureCurvature s a b c p hp u +
    (1 / 2 : ℂ) • (adjoint Z * Z + Z * adjoint Z)

private theorem coherent_lost_support
    (s : Finset ι) {a b : ℝ} (hab : a ≤ b)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) :
    evenCentralSoninProjection b * soninCoherentApertureLostTransition s a b p hp u = 0 ∧
    soninCoherentApertureLostTransition s a b p hp u * evenCentralSoninProjection b =
      soninCoherentApertureLostTransition s a b p hp u := by
  have hbb := (evenCentralSoninProjection_mul_of_le (a := b) (b := b) le_rfl).1
  have hbE : evenCentralSoninProjection b * evenSoninApertureLayer a b = 0 := by
    rw [evenSoninApertureLayer, mul_sub,
      (evenCentralSoninProjection_mul_of_le hab).1, hbb, sub_self]
  constructor
  · simp only [soninCoherentApertureLostTransition, evenSoninApertureLostTransition,
      Finset.mul_sum, mul_smul_even, ← mul_assoc, hbE, zero_mul, smul_zero,
      Finset.sum_const_zero]
  · simp only [soninCoherentApertureLostTransition, evenSoninApertureLostTransition,
      Finset.sum_mul, smul_mul_even, mul_assoc, hbb]

private theorem split_source_orthogonality
    (Y Q : evenSubspace →L[ℂ] evenSubspace)
    (hYY : Y * Y = 0) (hQY : Q * Y = 0) (hQQ : Q * Q = Q) (hQa : adjoint Q = Q) :
    (Y * (1 - Q)) * (Y * (1 - Q)) = 0 ∧
    (Y * Q) * (Y * (1 - Q)) = 0 ∧
    (Y * Q) * adjoint (Y * (1 - Q)) = 0 := by
  have h₁ : (1 - Q) * Y = Y := by rw [sub_mul, one_mul, hQY, sub_zero]
  have h₂ : Q * (1 - Q) = 0 := by rw [mul_sub, mul_one, hQQ, sub_self]
  constructor
  · calc
      _ = Y * ((1 - Q) * Y) * (1 - Q) := by simp only [mul_assoc]
      _ = 0 := by rw [h₁, hYY, zero_mul]
  constructor
  · calc
      _ = Y * (Q * Y) * (1 - Q) := by simp only [mul_assoc]
      _ = 0 := by rw [hQY, mul_zero, zero_mul]
  · rw [adjoint_mul_clm, adjoint_sub_clm, adjoint_one, hQa]
    calc
      _ = Y * (Q * (1 - Q)) * adjoint Y := by simp only [mul_assoc]
      _ = 0 := by rw [h₂, mul_zero, zero_mul]

/-- Orthogonality of the actual coherent lost and retained source transitions. -/
theorem soninCoherentApertureTransitions_orthogonality
    (s : Finset ι) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) :
    let Z := soninCoherentApertureSuccessiveLayerTransition s a b c p hp u
    let W := soninCoherentApertureRetainedTransition s a b c p hp u
    Z * Z = 0 ∧ W * Z = 0 ∧ W * adjoint Z = 0 := by
  let Y := soninCoherentApertureLostTransition s a b p hp u
  let Q := evenCentralSoninProjection c
  rcases coherent_lost_support s hab p hp u with ⟨hleft, hright⟩
  change evenCentralSoninProjection b * Y = 0 at hleft
  change Y * evenCentralSoninProjection b = Y at hright
  have hYY : Y * Y = 0 := by
    calc
      Y * Y = (Y * evenCentralSoninProjection b) * Y := by rw [hright]
      _ = 0 := by rw [mul_assoc, hleft, mul_zero]
  have hQY : Q * Y = 0 := by
    calc
      _ = (Q * evenCentralSoninProjection b) * Y := by
        rw [(evenCentralSoninProjection_mul_of_le hbc).1]
      _ = 0 := by rw [mul_assoc, hleft, mul_zero]
  rw [soninCoherentApertureSuccessiveLayerTransition_eq_boundary s hbc]
  exact split_source_orthogonality Y Q hYY hQY
    (evenCentralSoninProjection_mul_of_le (a := c) (b := c) le_rfl).1
    (adjoint_evenCentralSoninProjection c)

private theorem gram_sum_defect (Z W : evenSubspace →L[ℂ] evenSubspace) :
    adjoint W * W - adjoint (Z + W) * (Z + W) =
      -(adjoint Z * Z) - (adjoint Z * W + adjoint W * Z) := by
  simp only [adjoint_add_clm, add_mul, mul_add]
  abel

private theorem half_balance (A P V : evenSubspace →L[ℂ] evenSubspace) :
    -A - V + (1 / 2 : ℂ) • (A + P) =
      (1 / 2 : ℂ) • (P - (A + (2 : ℂ) • V)) := by
  module

private theorem balanced_compression_normalForm
    (Y Q : evenSubspace →L[ℂ] evenSubspace) (hQa : adjoint Q = Q) :
    Q * (adjoint Y * Y) * Q - adjoint Y * Y +
      (1 / 2 : ℂ) • (adjoint (Y * (1 - Q)) * (Y * (1 - Q)) +
        (Y * (1 - Q)) * adjoint (Y * (1 - Q))) =
      (1 / 2 : ℂ) • doubledRelativeWard (Y * (1 - Q)) (Y * Q) := by
  let Z := Y * (1 - Q)
  let W := Y * Q
  have hsum : Y = Z + W := by dsimp only [Z, W]; rw [mul_sub, mul_one]; abel
  have hgram : Q * (adjoint Y * Y) * Q = adjoint W * W := by
    dsimp only [W]
    rw [adjoint_mul_clm, hQa]
    simp only [mul_assoc]
  have hdiff : Q * (adjoint Y * Y) * Q - adjoint Y * Y =
      -(adjoint Z * Z) - (adjoint Z * W + adjoint W * Z) := by
    rw [hgram]
    exact (congrArg (fun T => adjoint W * W - T)
      (congrArg (fun T => adjoint T * T) hsum)).trans (gram_sum_defect Z W)
  change _ + (1 / 2 : ℂ) • (adjoint Z * Z + Z * adjoint Z) =
    (1 / 2 : ℂ) • doubledRelativeWard Z W
  simp only [hdiff, doubledRelativeWard]
  exact half_balance _ _ _

/-- Exact three-block normal form of the actual balanced Ward completion. -/
theorem soninCoherentBalancedWardCompletion_eq_half_doubledRelativeWard
    (s : Finset ι) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) :
    soninCoherentBalancedWardCompletion s a b c p hp u =
      (1 / 2 : ℂ) • doubledRelativeWard
        (soninCoherentApertureSuccessiveLayerTransition s a b c p hp u)
        (soninCoherentApertureRetainedTransition s a b c p hp u) := by
  rw [soninCoherentBalancedWardCompletion,
    soninCoherentApertureCurvature_eq_compression_sub_self s hab hbc,
    soninCoherentApertureSuccessiveLayerTransition_eq_boundary s hbc]
  exact balanced_compression_normalForm _ _ (adjoint_evenCentralSoninProjection c)

/-- The cubic character surviving coherent scalar Ward cancellation is an exact negative
Hilbert--Schmidt square. Every source interference term remains in the returning operator. -/
theorem re_opTrace_soninCoherentBalancedWardCompletion_cube
    (s : Finset ι) {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) (hcp : ∀ i ∈ s, c ≤ p i * a) :
    let Z := soninCoherentApertureSuccessiveLayerTransition s a b c p hp u
    let W := soninCoherentApertureRetainedTransition s a b c p hp u
    (opTrace (soninCoherentBalancedWardCompletion s a b c p hp u ^ 3)).re =
      -(3 / 2 : ℝ) * hsNormSq (Z * adjoint Z * W) := by
  dsimp only
  rw [soninCoherentBalancedWardCompletion_eq_half_doubledRelativeWard s hab hbc,
    opTrace_even_smul_pow]
  rcases soninCoherentApertureTransitions_orthogonality s hab hbc p hp u with
    ⟨hZZ, hWZ, hWZa⟩
  have h := re_opTrace_doubledRelativeWard_cube _ _
    (soninCoherentApertureSuccessiveLayerTransition_mem_principalRelativeIdeal
      s ha hab hbc p hp u hcp) hZZ hWZ hWZa
  simp only [Complex.mul_re]
  norm_num
  rw [h]
  ring

/-- The balanced completion retains the exact source ideal, not merely abstract trace class. -/
theorem soninCoherentBalancedWardCompletion_mem_principalRelativeIdeal
    (s : Finset ι) {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) (hcp : ∀ i ∈ s, c ≤ p i * a) :
    IsSoninPrincipalRelativeIdeal (soninCoherentBalancedWardCompletion s a b c p hp u) := by
  rw [soninCoherentBalancedWardCompletion_eq_half_doubledRelativeWard s hab hbc]
  exact (doubledRelativeWard_mem_principalRelativeIdeal _ _
    (soninCoherentApertureSuccessiveLayerTransition_mem_principalRelativeIdeal
      s ha hab hbc p hp u hcp)).smul _

/-- Exact cancellation of the complete complex trace. -/
theorem opTrace_soninCoherentBalancedWardCompletion_eq_zero
    (s : Finset ι) {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) (hcp : ∀ i ∈ s, c ≤ p i * a) :
    opTrace (soninCoherentBalancedWardCompletion s a b c p hp u) = 0 := by
  rw [soninCoherentBalancedWardCompletion_eq_half_doubledRelativeWard s hab hbc,
    opTrace_smul, opTrace_doubledRelativeWard_eq_zero _ _
      (soninCoherentApertureSuccessiveLayerTransition_mem_principalRelativeIdeal
        s ha hab hbc p hp u hcp)
      (soninCoherentApertureTransitions_orthogonality s hab hbc p hp u).2.2, mul_zero]

/-- Zero cubic trace is exactly decoupling of the retained/lost coherent Gram channels. -/
theorem re_opTrace_soninCoherentBalancedWardCompletion_cube_eq_zero_iff
    (s : Finset ι) {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) (hcp : ∀ i ∈ s, c ≤ p i * a) :
    (opTrace (soninCoherentBalancedWardCompletion s a b c p hp u ^ 3)).re = 0 ↔
      adjoint (soninCoherentApertureSuccessiveLayerTransition s a b c p hp u) *
        soninCoherentApertureRetainedTransition s a b c p hp u = 0 := by
  let Z := soninCoherentApertureSuccessiveLayerTransition s a b c p hp u
  let W := soninCoherentApertureRetainedTransition s a b c p hp u
  have hZ := soninCoherentApertureSuccessiveLayerTransition_mem_principalRelativeIdeal
    s ha hab hbc p hp u hcp
  have hT : (Z * adjoint Z * W).IsHilbertSchmidt :=
    isHilbertSchmidt_of_adjoint_mul_self_memSchattenClass_one _
      (((hZ.rightMul (adjoint Z)).rightMul W).leftMul _).memSchattenClass_one
  rw [re_opTrace_soninCoherentBalancedWardCompletion_cube s ha hab hbc p hp u hcp]
  change -(3 / 2 : ℝ) * hsNormSq (Z * adjoint Z * W) = 0 ↔ adjoint Z * W = 0
  rw [mul_eq_zero, hsNormSq_eq_zero_iff hT, relativeWard_return_eq_zero_iff]
  norm_num

private theorem half_add_half (T : evenSubspace →L[ℂ] evenSubspace) :
    (1 / 2 : ℂ) • T + (1 / 2 : ℂ) • T = T := by module

private theorem half_zero :
    (1 / 2 : ℂ) • (0 : evenSubspace →L[ℂ] evenSubspace) = 0 := by module

/-- Positivity of the actual balanced completion is equivalent to lossless source transport. -/
theorem soninCoherentBalancedWardCompletion_isPositive_iff
    (s : Finset ι) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) :
    (soninCoherentBalancedWardCompletion s a b c p hp u).IsPositive ↔
      soninCoherentApertureSuccessiveLayerTransition s a b c p hp u = 0 := by
  let Z := soninCoherentApertureSuccessiveLayerTransition s a b c p hp u
  let W := soninCoherentApertureRetainedTransition s a b c p hp u
  have hnormal := soninCoherentBalancedWardCompletion_eq_half_doubledRelativeWard s hab hbc p hp u
  change soninCoherentBalancedWardCompletion s a b c p hp u = (1 / 2 : ℂ) •
    doubledRelativeWard Z W at hnormal
  rcases soninCoherentApertureTransitions_orthogonality s hab hbc p hp u with
    ⟨hZZ, _, hWZa⟩
  constructor
  · intro hpos
    have hd : (doubledRelativeWard Z W).IsPositive := by
      have h := hpos.add hpos
      rw [hnormal, half_add_half] at h
      exact h
    exact (doubledRelativeWard_isPositive_iff Z W hZZ hWZa).mp hd
  · intro hZ
    change Z = 0 at hZ
    have hd : doubledRelativeWard Z W = 0 := by
      rw [hZ]
      simp [doubledRelativeWard]
    rw [hnormal, hd, half_zero]
    exact ContinuousLinearMap.isPositive_zero

private theorem half_neg (T : evenSubspace →L[ℂ] evenSubspace) :
    -((1 / 2 : ℂ) • T) = (1 / 2 : ℂ) • (-T) := by module

/-- The negative balanced completion is positive only on the same lossless locus.
Thus every nonzero actual lost transition leaves an indefinite operator. -/
theorem neg_soninCoherentBalancedWardCompletion_isPositive_iff
    (s : Finset ι) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) :
    (-soninCoherentBalancedWardCompletion s a b c p hp u).IsPositive ↔
      soninCoherentApertureSuccessiveLayerTransition s a b c p hp u = 0 := by
  let Z := soninCoherentApertureSuccessiveLayerTransition s a b c p hp u
  let W := soninCoherentApertureRetainedTransition s a b c p hp u
  have hnormal : -soninCoherentBalancedWardCompletion s a b c p hp u =
      (1 / 2 : ℂ) • (-doubledRelativeWard Z W) := by
    rw [soninCoherentBalancedWardCompletion_eq_half_doubledRelativeWard s hab hbc, half_neg]
  rcases soninCoherentApertureTransitions_orthogonality s hab hbc p hp u with
    ⟨hZZ, hWZ, _⟩
  constructor
  · intro hpos
    have h := hpos.add hpos
    rw [hnormal, half_add_half] at h
    exact (neg_doubledRelativeWard_isPositive_iff Z W hZZ hWZ).mp h
  · intro hZ
    change Z = 0 at hZ
    have hd : -doubledRelativeWard Z W = 0 := by
      rw [hZ]
      simp [doubledRelativeWard]
    rw [hnormal, hd, half_zero]
    exact ContinuousLinearMap.isPositive_zero

private theorem commutator_of_adjoint_cross
    (E X Z : evenSubspace →L[ℂ] evenSubspace)
    (hE : adjoint E = E) (hX : adjoint X = X) (hcross : crossBoundary E X = adjoint Z) :
    ccmCommutator X E = adjoint Z - Z := by
  have hadj : adjoint (crossBoundary E X) = upperBoundary E X := by
    unfold crossBoundary upperBoundary
    simp only [adjoint_mul_clm, adjoint_sub_clm, adjoint_one, hE, hX, mul_assoc]
  rw [ccmCommutator_eq_crossBoundary_sub_upperBoundary, ← hadj, hcross, adjoint_adjoint]

private theorem ward_difference_gram (Z : evenSubspace →L[ℂ] evenSubspace)
    (hZZ : Z * Z = 0) :
    adjoint (adjoint Z - Z) * (adjoint Z - Z) = adjoint Z * Z + Z * adjoint Z := by
  have hZaZa : adjoint Z * adjoint Z = 0 := by
    simpa only [adjoint_mul_clm, ContinuousLinearMap.adjoint.map_zero] using congrArg adjoint hZZ
  simp only [adjoint_sub_clm, adjoint_adjoint, sub_mul, mul_sub, hZZ, hZaZa]
  abel

/-- The balancing operator is precisely half the Gram operator of the canonical Ward
commutator, not an unrelated positive operator carrying the same scalar trace. -/
theorem soninCoherentBalancedWardCompletion_eq_curvature_add_WardGram
    (s : Finset ι) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) :
    let C := ccmCommutator (soninCoherentApertureWardChannel s a b c p hp u)
      (evenSoninApertureLayer a b)
    soninCoherentBalancedWardCompletion s a b c p hp u =
      soninCoherentApertureCurvature s a b c p hp u + (1 / 2 : ℂ) • (adjoint C * C) := by
  let Z := soninCoherentApertureSuccessiveLayerTransition s a b c p hp u
  let X := soninCoherentApertureWardChannel s a b c p hp u
  let E := evenSoninApertureLayer a b
  have hX : adjoint X = X := by
    dsimp only [X, soninCoherentApertureWardChannel]
    rw [adjoint_add_clm, adjoint_adjoint, add_comm]
  have hC : ccmCommutator X E = adjoint Z - Z :=
    commutator_of_adjoint_cross E X Z (adjoint_evenSoninApertureLayer a b) hX
      (crossBoundary_soninCoherentApertureWardChannel s hab hbc p hp u)
  have hZZ : Z * Z = 0 :=
    (soninCoherentApertureTransitions_orthogonality s hab hbc p hp u).1
  have hGram : adjoint (ccmCommutator X E) * ccmCommutator X E =
      adjoint Z * Z + Z * adjoint Z :=
    (congrArg (fun T => adjoint T * T) hC).trans (ward_difference_gram Z hZZ)
  change _ = _ + (1 / 2 : ℂ) • (adjoint (ccmCommutator X E) * ccmCommutator X E)
  rw [hGram]
  rfl

private theorem adjoint_half_smul (T : evenSubspace →L[ℂ] evenSubspace) :
    adjoint ((1 / 2 : ℂ) • T) = (1 / 2 : ℂ) • adjoint T := by
  change star ((1 / 2 : ℂ) • T) = (1 / 2 : ℂ) • star T
  rw [star_smul]
  norm_num

/-- The actual balanced operator is self-adjoint, so failure of positivity of both signs is
an indefinite Hermitian source defect. -/
theorem adjoint_soninCoherentBalancedWardCompletion
    (s : Finset ι) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (p : ι → ℝ) (hp : ∀ i, 1 < p i) (u : ι → ℂ) :
    adjoint (soninCoherentBalancedWardCompletion s a b c p hp u) =
      soninCoherentBalancedWardCompletion s a b c p hp u := by
  simp only [soninCoherentBalancedWardCompletion,
    soninCoherentApertureCurvature_eq_compression_sub_self s hab hbc,
    adjoint_add_clm, adjoint_sub_clm, adjoint_half_smul,
    adjoint_mul_clm, adjoint_adjoint, adjoint_evenCentralSoninProjection, mul_assoc]

end RHTower

end
