import GaloisForLFunctions.RHTower.SelbergClass.AsymmetricFunctionalEquation
import GaloisForLFunctions.RHTower.SelbergClass.GammaCriticalLine

/-!
# Gamma-pole-free vertical tails for concrete Selberg presentations

Kaczorowski--Perelli's asymmetric functional equation is used on high vertical
contours.  A height must therefore be chosen from the finite Gamma data, not
silently identified with a later contour parameter.  This module proves the
local prerequisite: if
`|(mu j).im| < lambda j * |t|` for every Gamma factor, then the vertical point
`sigma + t I` avoids both Gamma zero sets required by Euler reflection.

The represented continuation additionally has its displayed exceptional point
at `1`.  Thus the sharp direct theorem keeps the exact hypothesis
`selbergVerticalPoint sigma t ≠ 1`.  The finite `gammaTailHeight` corollary
uses a strict height inequality, which forces `t ≠ 0` even in rank zero and
therefore discharges that condition.  No contour shift, residue calculation,
or continuation theorem is asserted here.
-/

open Complex Filter Set
open scoped BigOperators Topology

namespace RHTower

noncomputable section

/-- The point of real part `sigma` and height `t` used on a vertical contour. -/
def selbergVerticalPoint (sigma t : ℝ) : ℂ :=
  (sigma : ℂ) + (t : ℂ) * I

/-- The direct, factorwise Gamma-tail condition at height `t`. -/
def SelbergGammaData.verticalTailCondition (G : SelbergGammaData) (t : ℝ) : Prop :=
  ∀ j : Fin G.rank, |(G.mu j).im| < G.lambda j * |t|

/-- A finite, presentation-dependent sufficient height bound.  The direct
`verticalTailCondition` is sharper than this convenient sum bound. -/
def SelbergGammaData.gammaTailHeight (G : SelbergGammaData) : ℝ :=
  ∑ j ∈ Finset.univ, |(G.mu j).im| / G.lambda j

/-- A height strictly above the finite Gamma-data bound satisfies every
factorwise tail inequality. -/
theorem SelbergGammaData.verticalTailCondition_of_gammaTailHeight_lt_abs
    (G : SelbergGammaData) {t : ℝ} (ht : G.gammaTailHeight < |t|) :
    G.verticalTailCondition t := by
  intro j
  have hterm : |(G.mu j).im| / G.lambda j ≤ G.gammaTailHeight := by
    unfold SelbergGammaData.gammaTailHeight
    exact Finset.single_le_sum (f := fun k => |(G.mu k).im| / G.lambda k) (s := Finset.univ)
      (fun k _ ↦ div_nonneg (abs_nonneg _) (G.lambda_pos k).le) (Finset.mem_univ j)
  have hdiv : |(G.mu j).im| / G.lambda j < |t| := lt_of_le_of_lt hterm ht
  have hmul : |(G.mu j).im| < |t| * G.lambda j :=
    (div_lt_iff₀ (G.lambda_pos j)).mp hdiv
  simpa [mul_comm] using hmul

/-- A strict finite Gamma-tail bound forces a nonzero height, hence excludes
the displayed continuation singularity at `1` on every vertical line. -/
theorem selbergVerticalPoint_ne_one_of_gammaTailHeight_lt_abs
    (G : SelbergGammaData) {sigma t : ℝ} (ht : G.gammaTailHeight < |t|) :
    selbergVerticalPoint sigma t ≠ 1 := by
  intro h
  have him : t = 0 := by
    have him := congrArg Complex.im h
    simpa [selbergVerticalPoint] using him
  rw [him, abs_zero] at ht
  have hnonneg : 0 ≤ G.gammaTailHeight := by
    unfold SelbergGammaData.gammaTailHeight
    exact Finset.sum_nonneg fun j _ ↦ div_nonneg (abs_nonneg _) (G.lambda_pos j).le
  linarith

theorem selbergVerticalPoint_re (sigma t : ℝ) :
    (selbergVerticalPoint sigma t).re = sigma := by
  simp [selbergVerticalPoint]

theorem selbergVerticalPoint_im (sigma t : ℝ) :
    (selbergVerticalPoint sigma t).im = t := by
  simp [selbergVerticalPoint]

/-- Imaginary part of one affine Gamma argument on the vertical point. -/
theorem SelbergGammaData.verticalArgument_im (G : SelbergGammaData)
    (j : Fin G.rank) (sigma t : ℝ) :
    ((G.lambda j : ℂ) * selbergVerticalPoint sigma t + G.mu j).im =
      G.lambda j * t + (G.mu j).im := by
  simp [selbergVerticalPoint, Complex.mul_im]

/-- The direct tail condition makes every affine Gamma argument nonreal. -/
theorem SelbergGammaData.verticalArgument_im_ne_zero_of_tail
    (G : SelbergGammaData) {sigma t : ℝ}
    (htail : G.verticalTailCondition t) (j : Fin G.rank) :
    ((G.lambda j : ℂ) * selbergVerticalPoint sigma t + G.mu j).im ≠ 0 := by
  rw [G.verticalArgument_im]
  intro hzero
  have hlin : G.lambda j * t = -(G.mu j).im := by linarith
  have habs : |G.lambda j * t| = |(G.mu j).im| := by
    rw [hlin, abs_neg]
  rw [abs_mul, abs_of_pos (G.lambda_pos j)] at habs
  linarith [htail j]

/-- A nonreal affine Gamma argument cannot be a nonpositive integer. -/
theorem SelbergGammaData.verticalArgument_ne_neg_nat_of_tail
    (G : SelbergGammaData) {sigma t : ℝ}
    (htail : G.verticalTailCondition t) (j : Fin G.rank) :
    ∀ n : ℕ,
      (G.lambda j : ℂ) * selbergVerticalPoint sigma t + G.mu j ≠ -(n : ℂ) := by
  intro n h
  have him := G.verticalArgument_im_ne_zero_of_tail (sigma := sigma) htail j
  rw [h] at him
  simp at him

/-- Generic affine Gamma analyticity away from its nonpositive-integer poles.
This is the same meromorphic-plus-continuous argument used for the critical
line, stated at an arbitrary point for vertical-tail reuse. -/
theorem SelbergGammaData.analyticAt_gammaAffine_of_ne_neg_nat
    (G : SelbergGammaData) (j : Fin G.rank) (s : ℂ)
    (hnot : ∀ n : ℕ, (G.lambda j : ℂ) * s + G.mu j ≠ -(n : ℂ)) :
    AnalyticAt ℂ (fun z : ℂ ↦ Gamma ((G.lambda j : ℂ) * z + G.mu j)) s := by
  have hmer : MeromorphicAt
      (fun z : ℂ ↦ Gamma ((G.lambda j : ℂ) * z + G.mu j)) s := by
    simpa only [Function.comp_def] using
      (Meromorphic.Gamma ((G.lambda j : ℂ) * s + G.mu j)).comp_analyticAt
        (x := s) (g := fun z : ℂ ↦ (G.lambda j : ℂ) * z + G.mu j) (by fun_prop)
  have hcont : ContinuousAt
      (fun z : ℂ ↦ Gamma ((G.lambda j : ℂ) * z + G.mu j)) s := by
    have hinner : ContinuousAt (fun z : ℂ ↦ (G.lambda j : ℂ) * z + G.mu j) s := by
      fun_prop
    simpa only [Function.comp_def] using
      ContinuousAt.comp (g := Gamma) (f := fun z : ℂ ↦ (G.lambda j : ℂ) * z + G.mu j)
        (x := s) (continuousAt_Gamma _ hnot) hinner
  exact hmer.analyticAt hcont

/-- Every affine Gamma factor is analytic at a vertical point satisfying the
direct tail condition. -/
theorem SelbergGammaData.analyticAt_gammaAffine_verticalTail
    (G : SelbergGammaData) {sigma t : ℝ}
    (htail : G.verticalTailCondition t) (j : Fin G.rank) :
    AnalyticAt ℂ (fun z : ℂ ↦ Gamma ((G.lambda j : ℂ) * z + G.mu j))
      (selbergVerticalPoint sigma t) := by
  exact G.analyticAt_gammaAffine_of_ne_neg_nat j _
    (G.verticalArgument_ne_neg_nat_of_tail htail j)

/-- The Gamma value of a vertical affine argument is nonzero on the tail. -/
theorem SelbergGammaData.gamma_verticalArgument_ne_zero_of_tail
    (G : SelbergGammaData) {sigma t : ℝ}
    (htail : G.verticalTailCondition t) (j : Fin G.rank) :
    Gamma ((G.lambda j : ℂ) * selbergVerticalPoint sigma t + G.mu j) ≠ 0 := by
  exact Gamma_ne_zero (G.verticalArgument_ne_neg_nat_of_tail htail j)

/-- The complementary Gamma argument in Euler reflection is also nonreal on
the same tail. -/
theorem SelbergGammaData.verticalComplementArgument_im_ne_zero_of_tail
    (G : SelbergGammaData) {sigma t : ℝ}
    (htail : G.verticalTailCondition t) (j : Fin G.rank) :
    (1 - (G.lambda j : ℂ) * selbergVerticalPoint sigma t - G.mu j).im ≠ 0 := by
  intro hzero
  have him := G.verticalArgument_im_ne_zero_of_tail (sigma := sigma) htail j
  apply him
  rw [G.verticalArgument_im]
  have hformula :
      (1 - (G.lambda j : ℂ) * selbergVerticalPoint sigma t - G.mu j).im =
        -(G.lambda j * t + (G.mu j).im) := by
    simp [selbergVerticalPoint, Complex.mul_im]
    ring
  rw [hformula] at hzero
  linarith

/-- The complementary Gamma argument avoids all nonpositive integers. -/
theorem SelbergGammaData.verticalComplementArgument_ne_neg_nat_of_tail
    (G : SelbergGammaData) {sigma t : ℝ}
    (htail : G.verticalTailCondition t) (j : Fin G.rank) :
    ∀ n : ℕ,
      1 - (G.lambda j : ℂ) * selbergVerticalPoint sigma t - G.mu j ≠ -(n : ℂ) := by
  intro n h
  have him := G.verticalComplementArgument_im_ne_zero_of_tail (sigma := sigma) htail j
  rw [h] at him
  simp at him

/-- The vertical-tail point lies in the exact Gamma-pole-free locus required
by the asymmetric functional equation. -/
theorem SelbergGammaData.mem_asymmetricPoleFreeSet_verticalTail
    (G : SelbergGammaData) {sigma t : ℝ}
    (htail : G.verticalTailCondition t) :
    selbergVerticalPoint sigma t ∈ G.asymmetricPoleFreeSet := by
  intro j
  constructor
  · exact G.gamma_verticalArgument_ne_zero_of_tail (sigma := sigma) htail j
  · exact Gamma_ne_zero (G.verticalComplementArgument_ne_neg_nat_of_tail (sigma := sigma) htail j)

/-- The whole selected Gamma factor is analytic at a vertical-tail point. -/
theorem SelbergGammaData.analyticAt_gammaFactor_verticalTail
    (G : SelbergGammaData) {sigma t : ℝ}
    (htail : G.verticalTailCondition t) :
    AnalyticAt ℂ G.gammaFactor (selbergVerticalPoint sigma t) := by
  rw [SelbergGammaData.gammaFactor]
  apply AnalyticAt.mul
  · have hQdiff : Differentiable ℂ fun s : ℂ ↦ (G.Q : ℂ) ^ s :=
      differentiable_id.const_cpow (.inl (ofReal_ne_zero.mpr G.Q_pos.ne'))
    have hQanalytic : AnalyticOnNhd ℂ (fun s : ℂ ↦ (G.Q : ℂ) ^ s) univ :=
      analyticOnNhd_univ_iff_differentiable.mpr hQdiff
    exact hQanalytic _ (mem_univ _)
  · exact Finset.univ.analyticAt_prod fun j _ ↦
      G.analyticAt_gammaAffine_verticalTail (sigma := sigma) htail j

/-- Selberg's conjugate reflection sends the vertical line `sigma + t I` to
`(1 - sigma) + t I`; it preserves the height rather than replacing it by a
later contour parameter. -/
theorem selbergVerticalPoint_reflection (sigma t : ℝ) :
    1 - star (selbergVerticalPoint sigma t) = selbergVerticalPoint (1 - sigma) t := by
  apply Complex.ext <;> simp [selbergVerticalPoint]

/-- A positive real part excludes the reflected point from the unique displayed
continuation singularity. -/
theorem selbergVerticalPoint_reflection_ne_one_of_pos {sigma t : ℝ}
    (hsigma : 0 < sigma) :
    1 - star (selbergVerticalPoint sigma t) ≠ 1 := by
  rw [selbergVerticalPoint_reflection]
  intro h
  have hre := congrArg Complex.re h
  simp [selbergVerticalPoint] at hre
  linarith

/-- The completed value is analytic at a vertical-tail point once its exact
displayed singularity is excluded. -/
theorem analyticAt_selbergCompletedValue_verticalTail
    (G : SelbergGammaData) (A : SelbergAnalyticContinuation) {sigma t : ℝ}
    (htail : G.verticalTailCondition t)
    (hpoint : selbergVerticalPoint sigma t ≠ 1) :
    AnalyticAt ℂ (selbergCompletedValue G A) (selbergVerticalPoint sigma t) := by
  unfold selbergCompletedValue
  exact (G.analyticAt_gammaFactor_verticalTail htail).mul
    (A.analyticAt_value_of_ne_one hpoint)

/-- The reflected completed value is analytic under the positive-real-part
vertical-tail hypotheses. -/
theorem analyticAt_selbergCompletedValue_verticalTail_reflection
    (G : SelbergGammaData) (A : SelbergAnalyticContinuation) {sigma t : ℝ}
    (hsigma : 0 < sigma) (htail : G.verticalTailCondition t) :
    AnalyticAt ℂ (selbergCompletedValue G A)
      (1 - star (selbergVerticalPoint sigma t)) := by
  rw [selbergVerticalPoint_reflection]
  have hpoint : selbergVerticalPoint (1 - sigma) t ≠ 1 := by
    rw [← selbergVerticalPoint_reflection]
    exact selbergVerticalPoint_reflection_ne_one_of_pos (t := t) hsigma
  exact analyticAt_selbergCompletedValue_verticalTail G A htail hpoint

/-- The pair-analytic locus of the completed functional equation contains each
vertical-tail point satisfying the exact continuation-pole exclusion. -/
theorem ExtendedSelbergClass.mem_completedFEContourSafeSet_verticalTail
    (F : ExtendedSelbergClass) {sigma t : ℝ}
    (hsigma : 0 < sigma) (hpoint : selbergVerticalPoint sigma t ≠ 1)
    (htail : F.gammaData.verticalTailCondition t) :
    selbergVerticalPoint sigma t ∈ F.completedFEContourSafeSet := by
  constructor
  · exact analyticAt_selbergCompletedValue_verticalTail F.gammaData F.continuation htail hpoint
  · exact analyticAt_selbergCompletedValue_verticalTail_reflection F.gammaData F.continuation
      hsigma htail

/-- Source-contour regularity: a vertical-tail point belongs to the exact
regular set on which the asymmetric Selberg functional equation is pointwise
valid. -/
theorem ExtendedSelbergClass.mem_asymmetricFERegularSet_verticalTail
    (F : ExtendedSelbergClass) {sigma t : ℝ}
    (hsigma : 0 < sigma) (hpoint : selbergVerticalPoint sigma t ≠ 1)
    (htail : F.gammaData.verticalTailCondition t) :
    selbergVerticalPoint sigma t ∈ F.asymmetricFERegularSet := by
  constructor
  · exact F.mem_completedFEContourSafeSet_verticalTail hsigma hpoint htail
  · exact F.gammaData.mem_asymmetricPoleFreeSet_verticalTail htail

/-- A convenient finite Gamma-data height inequality yields the full
asymmetric-functional-equation regularity conclusion without any additional
continuation premise. -/
theorem ExtendedSelbergClass.mem_asymmetricFERegularSet_of_gammaTailHeight_lt_abs
    (F : ExtendedSelbergClass) {sigma t : ℝ}
    (hsigma : 0 < sigma) (ht : F.gammaData.gammaTailHeight < |t|) :
    selbergVerticalPoint sigma t ∈ F.asymmetricFERegularSet := by
  exact F.mem_asymmetricFERegularSet_verticalTail hsigma
    (selbergVerticalPoint_ne_one_of_gammaTailHeight_lt_abs F.gammaData ht)
    (F.gammaData.verticalTailCondition_of_gammaTailHeight_lt_abs ht)

end

end RHTower
