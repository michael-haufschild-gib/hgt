import GaloisForLFunctions.HTGeometry.DeterminantLineGraphCapHilbertSum
import GaloisForLFunctions.RHTower.BurnolBaseGraphCapArea
import GaloisForLFunctions.HTGeometry.DeterminantLineBubblingDeckLaw

/-!
# The principal lift of the Burnol base cap holonomy

The literal all-prime Burnol graph cap has determinant-line area `0 ≤ E_base < 1`; by the graph-cap
holonomy theorem its boundary holonomy is `exp(2πi E_base)`, so `E_base` is the canonical principal
real lift of this determinant phase.  Since every bubble degree is a natural number and the area
is additive under degeneration, the Burnol cap cannot shed a positive holomorphic bubble onto a
residual filling of nonnegative area.
-/

set_option autoImplicit false

open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- **The literal Burnol cap carries a canonical principal lift.**  The determinant-line holonomy of
the boundary of the Burnol base graph cap is `exp(2πi E_base)`, `0 ≤ E_base < 1`, and `E_base` is
the unique `x ∈ [0, 1)` with `exp(2πi x) = Hol(∂Γ_{A_base})`. -/
theorem burnolBaseCap_principal_lift :
    edgeHol (sumPol _ _) (sumPol _ _) (graphCapBoundary routePPrimitiveBurnolBaseSynthesis
        routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt) =
      Complex.exp (2 * Real.pi * Complex.I * burnolBaseCapArea) ∧
    0 ≤ burnolBaseCapArea ∧ burnolBaseCapArea < 1 ∧
    ∀ x ∈ Set.Ico (0 : ℝ) 1, Complex.exp (2 * Real.pi * Complex.I * x) =
      edgeHol (sumPol _ _) (sumPol _ _) (graphCapBoundary routePPrimitiveBurnolBaseSynthesis
        routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt) → x = burnolBaseCapArea := by
  obtain ⟨-, -, h0, hlt, hB⟩ := burnolBaseCapArea_lt_one
  have h1 : burnolBaseCapArea < 1 := hlt.trans hB
  exact ⟨edgeHol_graphCapBoundary _, h0, h1, fun x hx hxe =>
    graphCapBoundary_unique_lift _ h1 hx hxe⟩


local instance : MeasurableSpace RoutePPrimitiveIndex := ⊤

local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

/-- The polarization of `ℓ²(primes) ⊕ L²(half line)` carrying the Burnol base cap. -/
abbrev burnolCapPol :=
  sumPol (MeasureTheory.Lp ℂ 2 (MeasureTheory.Measure.count :
    MeasureTheory.Measure RoutePPrimitiveIndex)) routePBurnolHalfLineL2

/-- The literal Burnol base cap as a one-square chain of the restricted Grassmannian of
`ℓ² ⊕ L²(half line)`. -/
def burnolBaseCapChain : GrChain burnolCapPol where
  len := 1
  coeff _ := 1
  sq _ := capSquare isStarProjection_sumPol
    (isHilbertSchmidt_graphBlockOp routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt)
    (sumPol_mul_graphBlockOp routePPrimitiveBurnolBaseSynthesis)
    (graphBlockOp_mul_sumPol routePPrimitiveBurnolBaseSynthesis)

theorem kahlerIntegral_burnolBaseCapChain :
    burnolBaseCapChain.kahlerIntegral = burnolBaseCapArea := by
  unfold GrChain.kahlerIntegral GrChain.kahlerOn
  refine (Fin.sum_univ_one _).trans ?_
  change ((1 : ℤ) : ℝ) * _ = _
  rw [Int.cast_one, one_mul]
  exact integral_graphCapKahler routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt

/-- **No positive bubbling off the Burnol cap.**  If the literal Burnol cap degenerates to a
residual filling `c₁` of nonnegative determinant-line area plus holomorphic sphere bubbles
(`cap ≡ c₁ + Σ_j B_j + ∂R` modulo degenerate squares), then every bubble has degree zero. -/
theorem burnolBaseCap_no_bubbling (c₁ : GrChain burnolCapPol)
    (bubbles : List (HolSphere burnolCapPol)) (R : List (ℤ × GrCube burnolCapPol))
    (hdeg : ∀ S : GrSquare burnolCapPol, ¬ S.IsDegenerate →
      burnolBaseCapChain.mult S = c₁.mult S + (bubbleChain bubbles).mult S +
        (cubeChainBdry R).mult S)
    (hres : 0 ≤ c₁.kahlerIntegral) : ∀ B ∈ bubbles, B.natDegree = 0 := by
  obtain ⟨-, -, -, hlt, hB⟩ := burnolBaseCapArea_lt_one
  have h1 := (GrChain.bubbling_deck_law _ c₁ bubbles R hdeg).1
  rw [kahlerIntegral_burnolBaseCapChain] at h1
  have hsum : ((bubbles.map HolSphere.natDegree).sum : ℝ) < 1 := by linarith
  have h0 : (bubbles.map HolSphere.natDegree).sum = 0 := by
    have : (bubbles.map HolSphere.natDegree).sum < 1 := by exact_mod_cast hsum
    omega
  intro B hB'
  exact List.sum_eq_zero_iff.mp h0 _ (List.mem_map_of_mem hB')

end

end RHTower
