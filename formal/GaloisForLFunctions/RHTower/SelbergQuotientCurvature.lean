import GaloisForLFunctions.RHTower.SelbergMaassCurvatureDescent

/-!
# The actual positive curvature functional on compact modular orbit fields

The literal range of full integral modular periodization carries the pointwise
order of real fields. Actual measure descent makes the integral of a compact
representative independent of its choice, positive, and linear. This constructs
the unique positive functional with every original compact source pairing and
its original regulator limit. No full quotient mass or spectral bound is claimed.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped MatrixGroups CompactlySupported
namespace GaloisForLFunctions.RHTower.SelbergQuotientCurvature
open SelbergCompactPeriodization SelbergMaassCurvatureMeasure SelbergMaassCurvatureDescent
noncomputable section

/-- Full modular periodization as a linear map on original compact tests. -/
def periodization : C_c(ℍ, ℝ) →ₗ[ℝ] (ℍ → ℝ) where
  toFun g := periodize g
  map_add' g h := by
    funext z
    change (∑' A : SL2Z, (g (A • z) + h (A • z))) = _
    exact (orbit_summable g.hasCompactSupport z).tsum_add (orbit_summable h.hasCompactSupport z)
  map_smul' c g := by
    funext z
    change (∑' A : SL2Z, c * g (A • z)) = c * periodize g z
    exact tsum_mul_left

/-- The literal space of full modular periodizations of compact continuous tests. -/
abbrev OrbitTestSpace := LinearMap.range periodization

/-- Send an original compact test to its actual modular orbit field. -/
def orbitTest (g : C_c(ℍ, ℝ)) : OrbitTestSpace := ⟨periodization g, LinearMap.mem_range_self _ g⟩

/-- Every orbit test carries a compact representative by construction. -/
def representative (F : OrbitTestSpace) : C_c(ℍ, ℝ) := (LinearMap.mem_range.mp F.property).choose

/-- The chosen compact representative reproduces the exact full orbit field. -/
theorem periodize_representative (F : OrbitTestSpace) : periodize (representative F) = (F : ℍ → ℝ) :=
  (LinearMap.mem_range.mp F.property).choose_spec

/-- Orbit tests are continuous on the whole upper half-plane. -/
theorem orbitTest_continuous (F : OrbitTestSpace) : Continuous (F : ℍ → ℝ) := by
  rw [← periodize_representative F]
  exact periodize_continuous _

/-- Orbit tests are exactly invariant under the integral modular action. -/
theorem orbitTest_invariant (F : OrbitTestSpace) (A : SL2Z) (z : ℍ) :
    F.val (A • z) = F.val z := by
  rw [← periodize_representative F, periodize_invariant]

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- The actual curvature value of an orbit test, using a compact representative. -/
def value (F : OrbitTestSpace) : ℝ := ∫ z : ℍ, representative F z ∂curvatureMeasure N f

/-- The value is independent of the chosen compact representative. -/
theorem value_eq (F : OrbitTestSpace) (g : C_c(ℍ, ℝ)) (hg : periodize g = (F : ℍ → ℝ)) :
    value N f F = ∫ z : ℍ, g z ∂curvatureMeasure N f :=
  integral_eq_of_periodize_eq N f (representative F) g ((periodize_representative F).trans hg.symm)

/-- The quotient test value is an actual real linear functional. -/
def functional : OrbitTestSpace →ₗ[ℝ] ℝ where
  toFun := value N f
  map_add' F G := by
    have hsum : periodize (representative F + representative G : C_c(ℍ, ℝ)) = ((F + G : OrbitTestSpace) : ℍ → ℝ) := by
      change periodization (representative F + representative G) = _
      rw [map_add]
      change periodize (representative F) + periodize (representative G) = _
      rw [periodize_representative, periodize_representative]
      rfl
    rw [value_eq N f (F + G) (representative F + representative G) hsum]
    exact integral_add (compact_test_integrable N f _) (compact_test_integrable N f _)
  map_smul' c F := by
    have hmul : periodize (c • representative F : C_c(ℍ, ℝ)) = ((c • F : OrbitTestSpace) : ℍ → ℝ) := by
      change periodization (c • representative F) = _
      rw [map_smul]
      change c • periodize (representative F) = _
      rw [periodize_representative]
      rfl
    rw [value_eq N f (c • F) (c • representative F) hmul]
    exact integral_smul c _

/-- Pointwise order on actual orbit fields makes the descended functional positive. -/
def positiveFunctional : OrbitTestSpace →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk (functional N f) (by
    intro F G hFG
    apply integral_le_of_periodize_le N f
    intro z
    rw [periodize_representative, periodize_representative]
    exact hFG z)

/-- The constructed positive quotient functional agrees with every original compact curvature integral. -/
theorem positiveFunctional_orbitTest (g : C_c(ℍ, ℝ)) :
    positiveFunctional N f (orbitTest g) = ∫ z : ℍ, g z ∂curvatureMeasure N f :=
  value_eq N f (orbitTest g) g rfl

/-- The positive quotient functional is uniquely fixed by the original compact source pairings. -/
theorem positiveFunctional_unique (Q : OrbitTestSpace →ₚ[ℝ] ℝ)
    (hQ : ∀ g : C_c(ℍ, ℝ), Q (orbitTest g) = ∫ z : ℍ, g z ∂curvatureMeasure N f) :
    Q = positiveFunctional N f := by
  ext F
  have hF : orbitTest (representative F) = F := Subtype.ext (periodize_representative F)
  rw [← hF, hQ, positiveFunctional_orbitTest]

/-- The original source determines a unique positive functional on its literal compact orbit-test space. -/
theorem existsUnique_positiveFunctional :
    ∃! Q : OrbitTestSpace →ₚ[ℝ] ℝ, ∀ g : C_c(ℍ, ℝ),
      Q (orbitTest g) = ∫ z : ℍ, g z ∂curvatureMeasure N f := by
  refine ⟨positiveFunctional N f, positiveFunctional_orbitTest N f, ?_⟩
  intro Q hQ
  exact positiveFunctional_unique N f Q hQ

/-- The actual regulator integrals converge to the constructed positive quotient functional. -/
theorem testedCurvature_limit_positiveFunctional (g : C_c(ℍ, ℝ)) :
    Tendsto (fun e : Ioi (0 : ℝ) => SelbergMaassWeakCurvature.testedCurvature N f e
      (SelbergUpperHalfPlaneCompactTests.zeroExtend g)) SelbergMaassRegulatorMass.regulatorAtZero
      (𝓝 (positiveFunctional N f (orbitTest g))) := by
  rw [positiveFunctional_orbitTest]
  exact testedCurvature_limit_integral N f g

end
end GaloisForLFunctions.RHTower.SelbergQuotientCurvature
