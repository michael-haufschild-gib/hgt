import Mathlib

/-!
# Anisotropic Thurston identifiability kernels

Closed, unconditional algebraic content extracted from arXiv:2609.09236.

This module builds the missing coordinate infrastructure for the paper's twisted Nil and Sol
families, proves their group laws and nonzero-twist equivalences, identifies Nil triangle holonomy
with signed area and a coboundary obstruction, constructs the Sol positive-chamber representative,
records all six curvature fingerprints, and exhibits the exact scale-null direction of the latent
Bernoulli model. Numerical Jacobian witnesses from the paper are deliberately excluded.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Coordinate models and twist group laws -/

/-- Common exponential-coordinate carrier for Nil and Sol. -/
structure ThurstonPoint where
  x : ℝ
  y : ℝ
  z : ℝ
deriving DecidableEq

namespace ThurstonPoint

def zero : ThurstonPoint := ⟨0, 0, 0⟩
def add (p q : ThurstonPoint) : ThurstonPoint := ⟨p.x + q.x, p.y + q.y, p.z + q.z⟩
def scale (c : ℝ) (p : ThurstonPoint) : ThurstonPoint := ⟨c * p.x, c * p.y, c * p.z⟩

@[ext] theorem ext {p q : ThurstonPoint} (hx : p.x = q.x) (hy : p.y = q.y)
    (hz : p.z = q.z) : p = q := by
  cases p
  cases q
  simp_all

end ThurstonPoint

/-- Nil multiplication with twist parameter `tau`. -/
def nilMul (tau : ℝ) (p q : ThurstonPoint) : ThurstonPoint :=
  ⟨p.x + q.x, p.y + q.y,
    p.z + q.z + tau / 2 * (p.x * q.y - p.y * q.x)⟩

/-- Nil inverse; it is independent of the twist parameter. -/
def nilInv (_tau : ℝ) (p : ThurstonPoint) : ThurstonPoint :=
  ⟨-p.x, -p.y, -p.z⟩

@[simp] theorem nilMul_zero_left (tau : ℝ) (p : ThurstonPoint) :
    nilMul tau ThurstonPoint.zero p = p := by
  ext <;> simp [nilMul, ThurstonPoint.zero]

@[simp] theorem nilMul_zero_right (tau : ℝ) (p : ThurstonPoint) :
    nilMul tau p ThurstonPoint.zero = p := by
  ext <;> simp [nilMul, ThurstonPoint.zero]

theorem nilMul_assoc (tau : ℝ) (p q r : ThurstonPoint) :
    nilMul tau (nilMul tau p q) r = nilMul tau p (nilMul tau q r) := by
  ext <;> simp [nilMul] <;> ring

@[simp] theorem nilMul_inv_left (tau : ℝ) (p : ThurstonPoint) :
    nilMul tau (nilInv tau p) p = ThurstonPoint.zero := by
  ext <;> simp only [nilMul, nilInv, ThurstonPoint.zero] <;> ring

@[simp] theorem nilMul_inv_right (tau : ℝ) (p : ThurstonPoint) :
    nilMul tau p (nilInv tau p) = ThurstonPoint.zero := by
  ext <;> simp only [nilMul, nilInv, ThurstonPoint.zero] <;> ring

/-- Scaling by `tau` intertwines the `tau`-twisted Nil law with unit twist. -/
theorem nilScale_intertwines (tau : ℝ) (p q : ThurstonPoint) :
    ThurstonPoint.scale tau (nilMul tau p q) =
      nilMul 1 (ThurstonPoint.scale tau p) (ThurstonPoint.scale tau q) := by
  ext <;> simp [nilMul, ThurstonPoint.scale] <;> ring

@[simp] theorem nilMul_zero_twist (p q : ThurstonPoint) :
    nilMul 0 p q = ThurstonPoint.add p q := by
  ext <;> simp [nilMul, ThurstonPoint.add]

/-- Sol multiplication with anisotropy/twist parameter `tau`. -/
def solMul (tau : ℝ) (p q : ThurstonPoint) : ThurstonPoint :=
  ⟨p.x + Real.exp (-tau * p.z) * q.x,
    p.y + Real.exp (tau * p.z) * q.y, p.z + q.z⟩

/-- Inverse for the `tau`-twisted Sol law. -/
def solInv (tau : ℝ) (p : ThurstonPoint) : ThurstonPoint :=
  ⟨-Real.exp (tau * p.z) * p.x, -Real.exp (-tau * p.z) * p.y, -p.z⟩

@[simp] theorem solMul_zero_left (tau : ℝ) (p : ThurstonPoint) :
    solMul tau ThurstonPoint.zero p = p := by
  ext <;> simp [solMul, ThurstonPoint.zero]

@[simp] theorem solMul_zero_right (tau : ℝ) (p : ThurstonPoint) :
    solMul tau p ThurstonPoint.zero = p := by
  ext <;> simp [solMul, ThurstonPoint.zero]

theorem solMul_assoc (tau : ℝ) (p q r : ThurstonPoint) :
    solMul tau (solMul tau p q) r = solMul tau p (solMul tau q r) := by
  have hx : Real.exp (-tau * (p.z + q.z)) =
      Real.exp (-tau * p.z) * Real.exp (-tau * q.z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hy : Real.exp (tau * (p.z + q.z)) =
      Real.exp (tau * p.z) * Real.exp (tau * q.z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply ThurstonPoint.ext
  · simp only [solMul]
    rw [hx]
    ring
  · simp only [solMul]
    rw [hy]
    ring
  · simp only [solMul]
    ring

@[simp] theorem solMul_inv_left (tau : ℝ) (p : ThurstonPoint) :
    solMul tau (solInv tau p) p = ThurstonPoint.zero := by
  have hx : Real.exp (-tau * -p.z) = Real.exp (tau * p.z) := by
    congr 1
    ring
  have hy : Real.exp (tau * -p.z) = Real.exp (-tau * p.z) := by
    congr 1
    ring
  apply ThurstonPoint.ext
  · simp only [solMul, solInv, ThurstonPoint.zero]
    rw [hx]
    ring
  · simp only [solMul, solInv, ThurstonPoint.zero]
    rw [hy]
    ring
  · simp [solMul, solInv, ThurstonPoint.zero]

@[simp] theorem solMul_inv_right (tau : ℝ) (p : ThurstonPoint) :
    solMul tau p (solInv tau p) = ThurstonPoint.zero := by
  have hneg : Real.exp (-(tau * p.z)) * Real.exp (tau * p.z) = 1 := by
    rw [← Real.exp_add]
    rw [show -(tau * p.z) + tau * p.z = 0 by ring, Real.exp_zero]
  have hpos : Real.exp (tau * p.z) * Real.exp (-(tau * p.z)) = 1 := by
    rw [← Real.exp_add]
    rw [show tau * p.z + -(tau * p.z) = 0 by ring, Real.exp_zero]
  have hsyntax : Real.exp (-tau * p.z) = Real.exp (-(tau * p.z)) := by
    congr 1
    ring
  have hneg' : Real.exp (-tau * p.z) * -Real.exp (tau * p.z) = -1 := by
    rw [mul_neg, hsyntax, hneg]
  have hpos' : Real.exp (tau * p.z) * -Real.exp (-tau * p.z) = -1 := by
    rw [mul_neg, hsyntax, hpos]
  apply ThurstonPoint.ext
  · simp only [solMul, solInv, ThurstonPoint.zero]
    rw [← mul_assoc, hneg']
    ring
  · simp only [solMul, solInv, ThurstonPoint.zero]
    rw [← mul_assoc, hpos']
    ring
  · simp [solMul, solInv, ThurstonPoint.zero]

/-- Scaling by `tau` intertwines the `tau`-twisted Sol law with unit twist. -/
theorem solScale_intertwines (tau : ℝ) (p q : ThurstonPoint) :
    ThurstonPoint.scale tau (solMul tau p q) =
      solMul 1 (ThurstonPoint.scale tau p) (ThurstonPoint.scale tau q) := by
  ext <;> simp [solMul, ThurstonPoint.scale] <;> ring

@[simp] theorem solMul_zero_twist (p q : ThurstonPoint) :
    solMul 0 p q = ThurstonPoint.add p q := by
  ext <;> simp [solMul, ThurstonPoint.add]

/-- Nonzero scalar dilation as an actual equivalence of coordinate spaces. -/
def thurstonScaleEquiv (scale : ℝˣ) : ThurstonPoint ≃ ThurstonPoint where
  toFun := ThurstonPoint.scale scale
  invFun := ThurstonPoint.scale scale⁻¹
  left_inv p := by
    ext <;> simp [ThurstonPoint.scale]
  right_inv p := by
    ext <;> simp [ThurstonPoint.scale]

/-- Every nonzero Nil twist is group-equivalent to unit twist. -/
theorem nilTwist_groupEquiv (scale : ℝˣ) (p q : ThurstonPoint) :
    thurstonScaleEquiv scale (nilMul scale p q) =
      nilMul 1 (thurstonScaleEquiv scale p) (thurstonScaleEquiv scale q) :=
  nilScale_intertwines scale p q

/-- Every nonzero Sol twist is group-equivalent to unit twist. -/
theorem solTwist_groupEquiv (scale : ℝˣ) (p q : ThurstonPoint) :
    thurstonScaleEquiv scale (solMul scale p q) =
      solMul 1 (thurstonScaleEquiv scale p) (thurstonScaleEquiv scale q) :=
  solScale_intertwines scale p q

/-! ## Nil holonomy and the triangle obstruction -/

/-- Alternating Nil connection cochain on a pair of base points. -/
def nilAreaCochain (p q : ThurstonPoint) : ℝ := (p.x * q.y - p.y * q.x) / 2

/-- Vertical residual after removing the Nil connection cochain. -/
def nilVerticalOffset (p q : ThurstonPoint) : ℝ := q.z - p.z - nilAreaCochain p q

/-- Signed base-triangle area, written as cyclic connection sum. -/
def nilTriangleArea (p q r : ThurstonPoint) : ℝ :=
  nilAreaCochain p q + nilAreaCochain q r + nilAreaCochain r p

@[simp] theorem nilAreaCochain_self (p : ThurstonPoint) : nilAreaCochain p p = 0 := by
  simp only [nilAreaCochain]
  ring

theorem nilAreaCochain_antisymm (p q : ThurstonPoint) :
    nilAreaCochain q p = -nilAreaCochain p q := by
  simp [nilAreaCochain]
  ring

/-- Cyclic vertical holonomy is negative signed base area. -/
theorem nilVerticalOffset_cycle (p q r : ThurstonPoint) :
    nilVerticalOffset p q + nilVerticalOffset q r + nilVerticalOffset r p =
      -nilTriangleArea p q r := by
  simp [nilVerticalOffset, nilTriangleArea]
  ring

/-- Three oriented edge values are a vertex-potential coboundary exactly when their sum vanishes. -/
theorem triangleEdgeData_is_coboundary_iff (a b c : ℝ) :
    (∃ r₀ r₁ r₂ : ℝ, a = r₁ - r₀ ∧ b = r₂ - r₁ ∧ c = r₀ - r₂) ↔
      a + b + c = 0 := by
  constructor
  · rintro ⟨r₀, r₁, r₂, rfl, rfl, rfl⟩
    ring
  · intro h
    exact ⟨0, a, a + b, by ring, by ring, by linarith⟩

/-- Nil vertical offsets are exact precisely when their triangle area obstruction vanishes. -/
theorem nilVerticalOffset_is_coboundary_iff (p q r : ThurstonPoint) :
    (∃ r₀ r₁ r₂ : ℝ,
      nilVerticalOffset p q = r₁ - r₀ ∧
      nilVerticalOffset q r = r₂ - r₁ ∧
      nilVerticalOffset r p = r₀ - r₂) ↔
      nilTriangleArea p q r = 0 := by
  rw [triangleEdgeData_is_coboundary_iff, nilVerticalOffset_cycle]
  simp

/-- Translation of the horizontal base coordinates. -/
def nilBaseTranslate (a p : ThurstonPoint) : ThurstonPoint :=
  ⟨a.x + p.x, a.y + p.y, p.z⟩

/-- Potential generated by translating the Nil connection origin. -/
def nilTranslationGauge (a p : ThurstonPoint) : ℝ :=
  (a.x * p.y - a.y * p.x) / 2

/-- Base translation changes the connection cochain by an exact coboundary. -/
theorem nilAreaCochain_translate (a p q : ThurstonPoint) :
    nilAreaCochain (nilBaseTranslate a p) (nilBaseTranslate a q) =
      nilAreaCochain p q + nilTranslationGauge a q - nilTranslationGauge a p := by
  simp [nilAreaCochain, nilBaseTranslate, nilTranslationGauge]
  ring

/-- Consequently, triangle holonomy is invariant under base translation. -/
theorem nilTriangleArea_translate (a p q r : ThurstonPoint) :
    nilTriangleArea (nilBaseTranslate a p) (nilBaseTranslate a q) (nilBaseTranslate a r) =
      nilTriangleArea p q r := by
  simp only [nilTriangleArea, nilAreaCochain_translate]
  ring

/-! ## Sol chamber and curvature fingerprints -/

/-- Paper's positive-orthant representative: negative `z` is repaired by swapping `x,y`. -/
def solCanonicalAnchor (p : ThurstonPoint) : ThurstonPoint :=
  if p.z < 0 then ⟨|p.y|, |p.x|, |p.z|⟩ else ⟨|p.x|, |p.y|, |p.z|⟩

theorem solCanonicalAnchor_nonnegative (p : ThurstonPoint) :
    0 ≤ (solCanonicalAnchor p).x ∧ 0 ≤ (solCanonicalAnchor p).y ∧
      0 ≤ (solCanonicalAnchor p).z := by
  by_cases h : p.z < 0 <;> simp [solCanonicalAnchor, h]

@[simp] theorem solCanonicalAnchor_idempotent (p : ThurstonPoint) :
    solCanonicalAnchor (solCanonicalAnchor p) = solCanonicalAnchor p := by
  have hz : ¬ |p.z| < 0 := not_lt_of_ge (abs_nonneg p.z)
  by_cases h : p.z < 0 <;> ext <;> simp [solCanonicalAnchor, h, hz]

/-- Coordinate squared norm used by all six curvature forms. -/
def coordinateNormSq (p : ThurstonPoint) : ℝ := p.x ^ 2 + p.y ^ 2 + p.z ^ 2

theorem coordinateNormSq_scale (c : ℝ) (p : ThurstonPoint) :
    coordinateNormSq (ThurstonPoint.scale c p) = c ^ 2 * coordinateNormSq p := by
  simp [coordinateNormSq, ThurstonPoint.scale]
  ring

theorem solCanonicalAnchor_normSq (p : ThurstonPoint) :
    coordinateNormSq (solCanonicalAnchor p) = coordinateNormSq p := by
  by_cases h : p.z < 0
  · simp [solCanonicalAnchor, coordinateNormSq, h, sq_abs]
    ring
  · simp [solCanonicalAnchor, coordinateNormSq, h, sq_abs]

def nilSectionalCurvature (u : ThurstonPoint) : ℝ := coordinateNormSq u / 4 - u.z ^ 2
def sl2SectionalCurvature (u : ThurstonPoint) : ℝ := coordinateNormSq u / 4 - 2 * u.z ^ 2
def solSectionalCurvature (u : ThurstonPoint) : ℝ := 2 * u.z ^ 2 - coordinateNormSq u
def hyperbolicPlaneProductCurvature (u : ThurstonPoint) : ℝ := -u.z ^ 2
def hyperbolicThreeCurvature (u : ThurstonPoint) : ℝ := -coordinateNormSq u
def euclideanThreeCurvature (_u : ThurstonPoint) : ℝ := 0

/-- Six curvature values used by the paper to separate Thurston geometries. -/
structure ThurstonCurvatureFingerprint where
  nil : ℝ
  sl2 : ℝ
  sol : ℝ
  hyperbolicPlaneProduct : ℝ
  hyperbolicThree : ℝ
  euclideanThree : ℝ
deriving DecidableEq

@[ext] theorem ThurstonCurvatureFingerprint.ext {a b : ThurstonCurvatureFingerprint}
    (hnil : a.nil = b.nil) (hsl2 : a.sl2 = b.sl2) (hsol : a.sol = b.sol)
    (hproduct : a.hyperbolicPlaneProduct = b.hyperbolicPlaneProduct)
    (hhyperbolic : a.hyperbolicThree = b.hyperbolicThree)
    (heuclidean : a.euclideanThree = b.euclideanThree) : a = b := by
  cases a
  cases b
  simp_all

/-- Curvature fingerprint of one bivector-coordinate triple. -/
def thurstonCurvatureFingerprint (u : ThurstonPoint) : ThurstonCurvatureFingerprint where
  nil := nilSectionalCurvature u
  sl2 := sl2SectionalCurvature u
  sol := solSectionalCurvature u
  hyperbolicPlaneProduct := hyperbolicPlaneProductCurvature u
  hyperbolicThree := hyperbolicThreeCurvature u
  euclideanThree := euclideanThreeCurvature u

/-- Exact identifiability content of the curvature table: it recovers total and vertical squares. -/
theorem thurstonCurvatureFingerprint_eq_iff (u v : ThurstonPoint) :
    thurstonCurvatureFingerprint u = thurstonCurvatureFingerprint v ↔
      coordinateNormSq u = coordinateNormSq v ∧ u.z ^ 2 = v.z ^ 2 := by
  constructor
  · intro h
    have hhyperbolic := congrArg ThurstonCurvatureFingerprint.hyperbolicThree h
    have hproduct := congrArg ThurstonCurvatureFingerprint.hyperbolicPlaneProduct h
    simp only [thurstonCurvatureFingerprint, hyperbolicThreeCurvature] at hhyperbolic
    simp only [thurstonCurvatureFingerprint, hyperbolicPlaneProductCurvature] at hproduct
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hnorm, hz⟩
    apply ThurstonCurvatureFingerprint.ext <;>
      simp [thurstonCurvatureFingerprint, nilSectionalCurvature,
      sl2SectionalCurvature, solSectionalCurvature, hyperbolicPlaneProductCurvature,
      hyperbolicThreeCurvature, euclideanThreeCurvature, hnorm, hz]

/-- Unit bivector data, with normalization packaged instead of passed as a hypothesis. -/
structure UnitThurstonDirection where
  point : ThurstonPoint
  normSq_one : coordinateNormSq point = 1

theorem UnitThurstonDirection.verticalSq_mem_unitInterval (u : UnitThurstonDirection) :
    0 ≤ u.point.z ^ 2 ∧ u.point.z ^ 2 ≤ 1 := by
  constructor
  · positivity
  · have hx : 0 ≤ u.point.x ^ 2 := sq_nonneg _
    have hy : 0 ≤ u.point.y ^ 2 := sq_nonneg _
    have hnorm := u.normSq_one
    rw [coordinateNormSq] at hnorm
    nlinarith

/-- Sharp curvature intervals for all anisotropic fingerprints in the paper. -/
theorem unitCurvatureFingerprint (u : UnitThurstonDirection) :
    (-3 / 4 : ℝ) ≤ nilSectionalCurvature u.point ∧
      nilSectionalCurvature u.point ≤ 1 / 4 ∧
      (-7 / 4 : ℝ) ≤ sl2SectionalCurvature u.point ∧
      sl2SectionalCurvature u.point ≤ 1 / 4 ∧
      (-1 : ℝ) ≤ solSectionalCurvature u.point ∧
      solSectionalCurvature u.point ≤ 1 ∧
      (-1 : ℝ) ≤ hyperbolicPlaneProductCurvature u.point ∧
      hyperbolicPlaneProductCurvature u.point ≤ 0 ∧
      hyperbolicThreeCurvature u.point = -1 ∧
      euclideanThreeCurvature u.point = 0 := by
  have hz := u.verticalSq_mem_unitInterval
  simp only [nilSectionalCurvature, sl2SectionalCurvature, solSectionalCurvature,
    hyperbolicPlaneProductCurvature, hyperbolicThreeCurvature, euclideanThreeCurvature,
    u.normSq_one]
  constructor
  · nlinarith
  · constructor
    · nlinarith
    · constructor
      · nlinarith
      · constructor
        · nlinarith
        · constructor
          · nlinarith
          · constructor
            · nlinarith
            · constructor
              · nlinarith
              · constructor
                · nlinarith
                · exact ⟨trivial, trivial⟩

/-- Exact algebraic differences separating the anisotropic curvature forms. -/
theorem anisotropicCurvature_relations (u : ThurstonPoint) :
    nilSectionalCurvature u - sl2SectionalCurvature u = u.z ^ 2 ∧
      solSectionalCurvature u - hyperbolicThreeCurvature u = 2 * u.z ^ 2 ∧
      hyperbolicPlaneProductCurvature u - hyperbolicThreeCurvature u = u.x ^ 2 + u.y ^ 2 := by
  simp only [nilSectionalCurvature, sl2SectionalCurvature, solSectionalCurvature,
    hyperbolicPlaneProductCurvature, hyperbolicThreeCurvature, coordinateNormSq]
  constructor
  · ring
  · constructor
    · ring
    · ring

/-! ## Twist/temperature confounding and Fisher-null paths -/

/-- Latent edge log-odds depends on twist only through the effective slope `beta/tau`. -/
def twistedLatentLogOdds (alpha beta tau distance : ℝ) : ℝ :=
  alpha - (beta * tau⁻¹) * distance

/-- Simultaneously scaling `beta` and `tau` by a nonzero scalar changes no log-odds. -/
theorem twistedLatentLogOdds_unitScale_invariant
    (alpha beta tau distance : ℝ) (scale : ℝˣ) :
    twistedLatentLogOdds alpha ((scale : ℝ) * beta) ((scale : ℝ) * tau) distance =
      twistedLatentLogOdds alpha beta tau distance := by
  have hslope : ((scale : ℝ) * beta) * ((scale : ℝ) * tau)⁻¹ = beta * tau⁻¹ := by
    rw [mul_inv_rev]
    calc
      (scale : ℝ) * beta * (tau⁻¹ * (scale : ℝ)⁻¹) =
          (scale : ℝ) * (scale : ℝ)⁻¹ * (beta * tau⁻¹) := by ring
      _ = beta * tau⁻¹ := by simp
  unfold twistedLatentLogOdds
  rw [hslope]

/-- Positive scale as a unit, eliminating all nonzero side conditions from theorem APIs. -/
def expScaleUnit (s : ℝ) : ℝˣ := Units.mk0 (Real.exp s) (Real.exp_ne_zero s)

@[simp] theorem coe_expScaleUnit (s : ℝ) : (expScaleUnit s : ℝ) = Real.exp s := rfl

/-- Simultaneous exponential scaling path in the confounded `(beta,tau)` direction. -/
def twistedScaleLogOddsPath (alpha beta tau distance s : ℝ) : ℝ :=
  twistedLatentLogOdds alpha (Real.exp s * beta) (Real.exp s * tau) distance

theorem twistedScaleLogOddsPath_constant (alpha beta tau distance s : ℝ) :
    twistedScaleLogOddsPath alpha beta tau distance s =
      twistedLatentLogOdds alpha beta tau distance :=
  twistedLatentLogOdds_unitScale_invariant alpha beta tau distance (expScaleUnit s)

/-- Exact zero score along the twist/temperature confounding direction. -/
theorem twistedScaleLogOddsPath_hasDerivAt_zero (alpha beta tau distance s : ℝ) :
    HasDerivAt (twistedScaleLogOddsPath alpha beta tau distance) 0 s := by
  have hfun : twistedScaleLogOddsPath alpha beta tau distance =
      fun _ ↦ twistedLatentLogOdds alpha beta tau distance := by
    funext t
    exact twistedScaleLogOddsPath_constant alpha beta tau distance t
  rw [hfun]
  exact hasDerivAt_const s _

/-- Bernoulli edge probability induced by twisted latent log-odds. -/
def twistedEdgeProbability (alpha beta tau distance : ℝ) : ℝ :=
  (1 + Real.exp (-twistedLatentLogOdds alpha beta tau distance))⁻¹

theorem twistedEdgeProbability_mem_unitInterval (alpha beta tau distance : ℝ) :
    0 < twistedEdgeProbability alpha beta tau distance ∧
      twistedEdgeProbability alpha beta tau distance < 1 := by
  constructor
  · simp [twistedEdgeProbability]
    positivity
  · unfold twistedEdgeProbability
    apply inv_lt_one_of_one_lt₀
    have hexp := Real.exp_pos (-twistedLatentLogOdds alpha beta tau distance)
    linarith

/-- Observation probabilities inherit the exact twist/temperature invariance. -/
theorem twistedEdgeProbability_unitScale_invariant
    (alpha beta tau distance : ℝ) (scale : ℝˣ) :
    twistedEdgeProbability alpha ((scale : ℝ) * beta) ((scale : ℝ) * tau) distance =
      twistedEdgeProbability alpha beta tau distance := by
  simp only [twistedEdgeProbability,
    twistedLatentLogOdds_unitScale_invariant alpha beta tau distance scale]

/-- Probability-level confounding path. -/
def twistedScaleProbabilityPath (alpha beta tau distance s : ℝ) : ℝ :=
  twistedEdgeProbability alpha (Real.exp s * beta) (Real.exp s * tau) distance

/-- Exact zero Bernoulli score, hence a Fisher-information null direction. -/
theorem twistedScaleProbabilityPath_hasDerivAt_zero (alpha beta tau distance s : ℝ) :
    HasDerivAt (twistedScaleProbabilityPath alpha beta tau distance) 0 s := by
  have hfun : twistedScaleProbabilityPath alpha beta tau distance =
      fun _ ↦ twistedEdgeProbability alpha beta tau distance := by
    funext t
    exact twistedEdgeProbability_unitScale_invariant alpha beta tau distance (expScaleUnit t)
  rw [hfun]
  exact hasDerivAt_const s _

/-! ## Dimension deficit polynomial -/

/-- Twice `(3n-4) - n(n-1)/2`, avoiding division in the exact dimension polynomial. -/
def twiceLatentDimensionMargin (n : ℤ) : ℤ := 2 * (3 * n - 4) - n * (n - 1)

theorem twiceLatentDimensionMargin_formula (n : ℤ) :
    twiceLatentDimensionMargin n = -n ^ 2 + 7 * n - 8 := by
  simp [twiceLatentDimensionMargin]
  ring

end

end GaloisForLFunctions.HTGeometry
