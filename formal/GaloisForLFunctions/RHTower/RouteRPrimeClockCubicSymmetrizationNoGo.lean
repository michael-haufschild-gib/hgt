import GaloisForLFunctions.RHTower.SourceHorizontalWoldPrimeClockCubic
import GaloisForLFunctions.RHTower.RouteRDegreeSixBVGreenPhysicalCyclicDescentWall

/-!
# Route R prime-clock cubic symmetrization no-go

The source-horizontal Wold response is reflection odd.  Its invariant linear
projection vanishes, while its anti-invariant projection merely doubles the
same detector.  The first retained reflection-even quantity is the negative
square, whose limit is the explicit sixth-power horizontal defect.  Landing
that product on the fixed physical cyclic reader is exactly the existing
degree-six wall and is globally equivalent to RH, not a source-derived
annihilation.
-/

open Filter

namespace RHTower

noncomputable section

/-- Invariant linear projection of the reflected cubic pair. -/
def routeRPrimeClockCubicInvariantProjection
    (q : XiZeroCopy) (N : ℕ) : ℝ :=
  sourceZeroHorizontalWoldPrimeClockCubicResponse q N +
    sourceZeroHorizontalWoldPrimeClockCubicResponse
      (xiZeroCopyLineConjEquiv q) N

/-- Anti-invariant linear projection of the reflected cubic pair. -/
def routeRPrimeClockCubicAntiInvariantProjection
    (q : XiZeroCopy) (N : ℕ) : ℝ :=
  sourceZeroHorizontalWoldPrimeClockCubicResponse q N -
    sourceZeroHorizontalWoldPrimeClockCubicResponse
      (xiZeroCopyLineConjEquiv q) N

@[simp] theorem routeRPrimeClockCubicInvariantProjection_eq_zero
    (q : XiZeroCopy) (N : ℕ) :
    routeRPrimeClockCubicInvariantProjection q N = 0 := by
  rw [routeRPrimeClockCubicInvariantProjection,
    sourceZeroHorizontalWoldPrimeClockCubicResponse_reflection]
  ring

theorem routeRPrimeClockCubicAntiInvariantProjection_eq_two_mul
    (q : XiZeroCopy) (N : ℕ) :
    routeRPrimeClockCubicAntiInvariantProjection q N =
      2 * sourceZeroHorizontalWoldPrimeClockCubicResponse q N := by
  rw [routeRPrimeClockCubicAntiInvariantProjection,
    sourceZeroHorizontalWoldPrimeClockCubicResponse_reflection]
  ring

/-- Every invariant linear map from the sign representation to a trivial
real representation is zero. -/
theorem routeR_signInvariantLinearMap_eq_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : ℝ →ₗ[ℝ] V) (hinvariant : ∀ x, L (-x) = L x) :
    L = 0 := by
  apply LinearMap.ext
  intro x
  have hneg : -(L x) = L x := by
    simpa using hinvariant x
  have htwo : (2 : ℝ) • L x = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← hneg]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The reflected product is the negative square at every finite stage. -/
theorem routeRPrimeClockCubic_reflectedProduct_eq_neg_sq
    (q : XiZeroCopy) (N : ℕ) :
    sourceZeroHorizontalWoldPrimeClockCubicResponse q N *
        sourceZeroHorizontalWoldPrimeClockCubicResponse
          (xiZeroCopyLineConjEquiv q) N =
      -(sourceZeroHorizontalWoldPrimeClockCubicResponse q N) ^ 2 := by
  rw [sourceZeroHorizontalWoldPrimeClockCubicResponse_reflection]
  ring

/-- The first non-erasing reflection-even output has the exact sixth-power
horizontal limit. -/
theorem tendsto_routeRPrimeClockCubic_reflectedProduct
    (q : XiZeroCopy) :
    Tendsto (fun N =>
      sourceZeroHorizontalWoldPrimeClockCubicResponse q N *
        sourceZeroHorizontalWoldPrimeClockCubicResponse
          (xiZeroCopyLineConjEquiv q) N) atTop
      (nhds (-((4 / 9 : ℝ) * primeDepthBVWoldXiCenteredRate q.1 ^ 6))) := by
  have h := tendsto_sourceZeroHorizontalWoldPrimeClockCubicResponse q
  have hprod := h.mul h.neg
  convert hprod using 1
  · funext N
    rw [sourceZeroHorizontalWoldPrimeClockCubicResponse_reflection]
  · ring

/-- Multiplicative physical descent of the cubic is the already isolated
degree-six BV--Green cyclic wall. -/
def RouteRPrimeClockCubicMultiplicativePhysicalDescent
    (q : XiZeroCopy) : Prop :=
  RouteRDegreeSixBVGreenPhysicalCyclicDescent q.1

theorem routeRPrimeClockCubicMultiplicativePhysicalDescent_iff_criticalLine
    (q : XiZeroCopy) :
    RouteRPrimeClockCubicMultiplicativePhysicalDescent q ↔
      (q.1 : ℂ).re = 1 / 2 :=
  routeRDegreeSixBVGreenPhysicalCyclicDescent_iff_re_eq_half q.1

/-- Global multiplicative descent is RH-equivalent, so cubic
symmetrization has not supplied an independent producer. -/
theorem forall_routeRPrimeClockCubicMultiplicativePhysicalDescent_iff_rh :
    (∀ q : XiZeroCopy,
      RouteRPrimeClockCubicMultiplicativePhysicalDescent q) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    exact (forall_routeRDegreeSixBVGreenPhysicalCyclicDescent_iff_riemannHypothesis).1
      (fun rho => h ⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩)
  · intro hRH q
    exact (forall_routeRDegreeSixBVGreenPhysicalCyclicDescent_iff_riemannHypothesis).2
      hRH q.1

end

end RHTower
