import GaloisForLFunctions.RHTower.ThetaCuspHawkingSelfDualGeneralMellinVertex
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicPhysicalHorizonIncidence

/-!
# Physical Poincare curvature does not descend to the BM radial variable

For the massless four-dimensional topological black hole, Jevicki--Suzuki's exact
Rindler--AdS/Poincare chart has inverse black-hole radius `rho = r⁻¹` and Poincare radial
coordinate `Z = rho * sigma`. Birmingham--Mokhtari's hypergeometric radial variable is therefore
`z_BM = 1 - rho²`. The physical self-dual AdS curvature coefficient is
`2i/(u-v) = i/Z`.

The sharp descent classification proved here says that a scalar Poincare-radial profile descends
to the BM radial variable on the whole exterior exactly when it is constant on the positive
Poincare radial ray. In particular, neither `1/Z` nor an explicit unequal-charge self-dual
plane-wave vertex descends. The latter has distinct values at `rho=1/2`, `sigma=1,2`, although
both points have the same BM radial coordinate.

Consequently the physical Plebanski deformation cannot be inserted into the BM Green response as
a one-variable radial multiplier. Any complete `++-` source calculation must retain the
hyperbolic coordinate and reconstruct the metric/light-cone operator before projection.

This theorem does not compute the full non-self-dual Einstein source, the negative-helicity leg,
the gauge/boundary completion, or the conserved left-QNM projection.

`[NEW CONSEQUENCE] [PAPER-PROVED] [LEAN-PROVED] [HC94] [RADIAL-PROXY NO-GO]`
-/

open Complex Real Set

namespace RHTower

noncomputable section

/-- Birmingham--Mokhtari radial coordinate in the inverse-radius Rindler chart. -/
def d4BMBlackHoleRadialCoordinateFromRindlerRho (rho : ℝ) : ℝ :=
  1 - rho ^ (2 : ℕ)

/-- Poincare radial coordinate pulled back to the massless topological-black-hole chart. -/
def d4PoincareRadialCoordinateFromBMRindler (rho sigma : ℝ) : ℝ :=
  rho * sigma

/-- Poincare curvature profile `1 / Z`. -/
def d4PoincareInverseRadialProfile (Z : ℝ) : ℝ :=
  1 / Z

/-- Curvature multiplier `1 / Z` pulled back to the BM/Rindler chart. -/
def d4PoincareInverseRadialMultiplierFromBMRindler (rho sigma : ℝ) : ℝ :=
  d4PoincareInverseRadialProfile
    (d4PoincareRadialCoordinateFromBMRindler rho sigma)

/-- Physical AdS self-dual curvature coefficient `2i/(u-v)=i/Z` in the BM/Rindler chart. -/
def d4AdSSelfDualPoincareCurvatureFromBMRindler (rho sigma : ℝ) : ℂ :=
  Complex.I * (d4PoincareInverseRadialMultiplierFromBMRindler rho sigma : ℂ)

/-- Unequal-charge self-dual AdS plane-wave vertex pulled back to the BM/Rindler chart. -/
def d4AdSSelfDualPlaneWaveVertexFromBMRindler
    (rho sigma : ℝ) (p h q k : ℂ) : ℂ :=
  ads4SelfDualPlaneWaveVertex
    (d4AdSSelfDualPoincareCurvatureFromBMRindler rho sigma) p h q k

/-- Hyperbolic rescaling leaves the BM radial coordinate fixed and rescales the Poincare radial
coordinate linearly. -/
theorem d4BMRadialFiber_poincareRadial_hyperbolicRescaling
    (rho sigma lambda : ℝ) :
    d4BMBlackHoleRadialCoordinateFromRindlerRho rho =
        d4BMBlackHoleRadialCoordinateFromRindlerRho rho ∧
      d4PoincareRadialCoordinateFromBMRindler rho (lambda * sigma) =
        lambda * d4PoincareRadialCoordinateFromBMRindler rho sigma := by
  constructor
  · rfl
  · simp [d4PoincareRadialCoordinateFromBMRindler, mul_left_comm]

/-- Sharp descent classification. A scalar Poincare-radial profile descends to a function of the
BM radial coordinate throughout the physical Rindler exterior exactly when it is constant on the
positive Poincare radial ray. -/
theorem exists_d4BMRadialFactor_poincareProfile_iff_constantOnPositive
    {A : Type*} (G : ℝ → A) :
    (∃ F : ℝ → A, ∀ rho sigma : ℝ,
      0 < rho → rho < 1 → 0 < sigma →
        G (d4PoincareRadialCoordinateFromBMRindler rho sigma) =
          F (d4BMBlackHoleRadialCoordinateFromRindlerRho rho)) ↔
      ∃ c : A, ∀ Z : ℝ, 0 < Z → G Z = c := by
  constructor
  · rintro ⟨F, hF⟩
    refine ⟨F (d4BMBlackHoleRadialCoordinateFromRindlerRho (1 / 2)), ?_⟩
    intro Z hZ
    have h := hF (1 / 2) (2 * Z) (by norm_num) (by norm_num)
      (mul_pos (by norm_num) hZ)
    simpa [d4PoincareRadialCoordinateFromBMRindler] using h
  · rintro ⟨c, hc⟩
    refine ⟨fun _ => c, ?_⟩
    intro rho sigma hrho _ hsigma
    exact hc _ (mul_pos hrho hsigma)

/-- At fixed BM radius, the Poincare inverse-radius multiplier changes with the hyperbolic
coordinate. This is the sharp two-point witness. -/
theorem d4PoincareInverseRadialMultiplier_same_BM_radius_ne :
    d4BMBlackHoleRadialCoordinateFromRindlerRho (1 / 2) =
        d4BMBlackHoleRadialCoordinateFromRindlerRho (1 / 2) ∧
      d4PoincareInverseRadialMultiplierFromBMRindler (1 / 2) 1 ≠
        d4PoincareInverseRadialMultiplierFromBMRindler (1 / 2) 2 := by
  constructor
  · rfl
  · norm_num [d4PoincareInverseRadialMultiplierFromBMRindler,
      d4PoincareInverseRadialProfile,
      d4PoincareRadialCoordinateFromBMRindler]

/-- The exact unequal-charge probe `(p,h;q,k)=(0,1;-1,0)` retains the Poincare curvature
multiplier. -/
theorem d4AdSSelfDualPlaneWaveVertexFromBMRindler_probe_eq
    (rho sigma : ℝ) :
    d4AdSSelfDualPlaneWaveVertexFromBMRindler rho sigma 0 1 (-1) 0 =
      (1 / 2 : ℂ) *
        (1 - Complex.I *
          (d4PoincareInverseRadialMultiplierFromBMRindler rho sigma : ℂ)) := by
  simp [d4AdSSelfDualPlaneWaveVertexFromBMRindler, ads4SelfDualPlaneWaveVertex,
    ads4SelfDualKinematicBracket, d4AdSSelfDualPoincareCurvatureFromBMRindler]

/-- At one BM radial fibre, the exact unequal-charge self-dual vertex has two distinct values. -/
theorem d4AdSSelfDualPlaneWaveVertex_same_BM_radius_ne :
    d4AdSSelfDualPlaneWaveVertexFromBMRindler (1 / 2) 1 0 1 (-1) 0 ≠
      d4AdSSelfDualPlaneWaveVertexFromBMRindler (1 / 2) 2 0 1 (-1) 0 := by
  norm_num [d4AdSSelfDualPlaneWaveVertexFromBMRindler,
    ads4SelfDualPlaneWaveVertex, ads4SelfDualKinematicBracket,
    d4AdSSelfDualPoincareCurvatureFromBMRindler,
    d4PoincareInverseRadialMultiplierFromBMRindler,
    d4PoincareInverseRadialProfile, d4PoincareRadialCoordinateFromBMRindler]

/-- The physical Poincare curvature multiplier cannot be a function of the BM radial coordinate
alone on the Rindler-AdS exterior. -/
theorem not_exists_d4BMRadialFactor_poincareInverseRadialMultiplier :
    ¬ ∃ F : ℝ → ℝ, ∀ rho sigma : ℝ,
      0 < rho → rho < 1 → 0 < sigma →
        d4PoincareInverseRadialMultiplierFromBMRindler rho sigma =
          F (d4BMBlackHoleRadialCoordinateFromRindlerRho rho) := by
  intro hfactor
  have hfactor' :
      ∃ F : ℝ → ℝ, ∀ rho sigma : ℝ,
        0 < rho → rho < 1 → 0 < sigma →
          d4PoincareInverseRadialProfile
              (d4PoincareRadialCoordinateFromBMRindler rho sigma) =
            F (d4BMBlackHoleRadialCoordinateFromRindlerRho rho) := by
    rcases hfactor with ⟨F, hF⟩
    refine ⟨F, ?_⟩
    intro rho sigma hrho hrho1 hsigma
    simpa [d4PoincareInverseRadialMultiplierFromBMRindler] using
      hF rho sigma hrho hrho1 hsigma
  have hconstant :=
    (exists_d4BMRadialFactor_poincareProfile_iff_constantOnPositive
      d4PoincareInverseRadialProfile).mp hfactor'
  rcases hconstant with ⟨c, hc⟩
  have h1 := hc 1 (by norm_num)
  have h2 := hc 2 (by norm_num)
  norm_num [d4PoincareInverseRadialProfile] at h1 h2
  linarith

/-- The exact unequal-charge self-dual AdS plane-wave vertex cannot be represented by any scalar
function of the BM radial coordinate alone on the physical Rindler exterior. -/
theorem not_exists_d4BMRadialFactor_ads4SelfDualPlaneWaveVertex_probe :
    ¬ ∃ F : ℝ → ℂ, ∀ rho sigma : ℝ,
      0 < rho → rho < 1 → 0 < sigma →
        d4AdSSelfDualPlaneWaveVertexFromBMRindler rho sigma 0 1 (-1) 0 =
          F (d4BMBlackHoleRadialCoordinateFromRindlerRho rho) := by
  rintro ⟨F, hF⟩
  have h1 := hF (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num)
  have h2 := hF (1 / 2) 2 (by norm_num) (by norm_num) (by norm_num)
  exact d4AdSSelfDualPlaneWaveVertex_same_BM_radius_ne (h1.trans h2.symm)

end

end RHTower
