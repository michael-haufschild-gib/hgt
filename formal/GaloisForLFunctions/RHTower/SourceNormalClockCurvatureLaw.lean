import GaloisForLFunctions.HTGeometry.TraceDerivationCyclicCocycleLaw
import GaloisForLFunctions.RHTower.ArithmeticXiStokesCentralRankPort
import GaloisForLFunctions.RHTower.MobiusThetaPhysicalParacyclicSourceNullHomology
import GaloisForLFunctions.RHTower.RouteRPreDivisorRationalAdelicMultiplierKOneHomology
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Tactic.Ring

/-!
# Source-normal Hochschild clock curvature and logarithmic flatness

This file formalizes the unconditional algebraic core of the Stage-2 card
`source-normal-hochschild-maurer-cartan-clock-curvature-law.md`.

The trace and derivation laws are bundled into data rather than supplied as proof-surrogate
hypotheses.  The resulting theorems show:

* inner corrections change the trace--derivation cocycle by an exact Hochschild coboundary;
* product trace reads one on every normalized representation simplex;
* the finite multiplicative clock satisfies its exact Maurer--Cartan and group-coboundary laws;
* positive characters are globally linearized by the logarithmic clock coordinate;
* the raw square-clock additivity condition forces the neutral radial rate.
-/

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Bundled trace--derivation data and inner-correction rigidity -/

variable {A K : Type*} [NonUnitalRing A] [AddCommGroup K]

/-- A trace and derivation together with their defining laws. -/
structure TraceDerivationDatum (A K : Type*) [NonUnitalRing A] [AddCommGroup K] where
  trace : A →+ K
  derivation : A →+ A
  trace_cyclic : IsAlgebraTrace trace
  derivation_leibniz : IsAlgebraDerivation derivation

/-- Inner derivation `x ↦ h*x - x*h`. -/
def innerDerivation (h : A) : A →+ A where
  toFun x := h * x - x * h
  map_zero' := by simp
  map_add' x y := by
    simp only [mul_add, add_mul, sub_eq_add_neg]
    abel

@[simp]
theorem innerDerivation_apply (h x : A) : innerDerivation h x = h * x - x * h := rfl

/-- Degree-zero trace cochain `x ↦ τ(hx)`. -/
def innerTraceCochain (τ : A →+ K) (h : A) : A →+ K :=
  τ.comp
    { toFun := fun x => h * x
      map_zero' := by simp
      map_add' := by simp [mul_add] }

@[simp]
theorem innerTraceCochain_apply (τ : A →+ K) (h x : A) :
    innerTraceCochain τ h x = τ (h * x) := rfl

/-- Hochschild coboundary convention used by the paper card. -/
def hochschildCoboundaryZero (ψ : A →+ K) (a b : A) : K :=
  ψ (a * b) - ψ (b * a)

/-- **Inner-correction rigidity.**  Correcting a derivation by an inner derivation changes the
trace--derivation cocycle by the negative Hochschild coboundary of `x ↦ τ(hx)`. -/
theorem traceDerivCocycle_innerCorrection
    (datum : TraceDerivationDatum A K) (h a b : A) :
    traceDerivCocycle datum.trace (datum.derivation + innerDerivation h) a b -
        traceDerivCocycle datum.trace datum.derivation a b =
      -hochschildCoboundaryZero (innerTraceCochain datum.trace h) a b := by
  simp only [traceDerivCocycle, AddMonoidHom.add_apply, innerDerivation_apply,
    innerTraceCochain_apply, hochschildCoboundaryZero,
    mul_add, mul_sub, map_add, map_sub]
  rw [datum.trace_cyclic a (h * b)]
  rw [← mul_assoc a b h, datum.trace_cyclic (a * b) h]
  simp only [mul_assoc]
  abel

/-- Inner correction preserves the pairing on every finite Hochschild one-cycle, not only on a
single inverse-unit pair.  A list of pure tensors is a cycle exactly when the sum of its
commutators vanishes. -/
theorem traceDerivCocycle_innerCorrection_finiteCycle
    (datum : TraceDerivationDatum A K) (h : A) (chain : List (A × A))
    (hcycle : (chain.map fun p => p.1 * p.2 - p.2 * p.1).sum = 0) :
    (chain.map fun p =>
      traceDerivCocycle datum.trace (datum.derivation + innerDerivation h) p.1 p.2 -
        traceDerivCocycle datum.trace datum.derivation p.1 p.2).sum = 0 := by
  have hsum :
      (chain.map fun p =>
        traceDerivCocycle datum.trace (datum.derivation + innerDerivation h) p.1 p.2 -
          traceDerivCocycle datum.trace datum.derivation p.1 p.2).sum =
        -innerTraceCochain datum.trace h
          (chain.map fun p => p.1 * p.2 - p.2 * p.1).sum := by
    clear hcycle
    induction chain with
    | nil => simp
    | cons p chain ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [traceDerivCocycle_innerCorrection, ih]
        simp only [hochschildCoboundaryZero, map_add, map_sub]
        abel
  calc
    _ = -innerTraceCochain datum.trace h
        (chain.map fun p => p.1 * p.2 - p.2 * p.1).sum := hsum
    _ = 0 := by rw [hcycle]; simp

/-- Inner correction leaves the trace--derivation pairing unchanged on an inverse unit pair. -/
theorem traceDerivCocycle_innerCorrection_inversePair
    {A₁ K₁ : Type*} [Ring A₁] [AddCommGroup K₁]
    (datum : TraceDerivationDatum A₁ K₁) (h a b : A₁)
    (hab : a * b = 1) (hba : b * a = 1) :
    traceDerivCocycle datum.trace (datum.derivation + innerDerivation h) a b =
      traceDerivCocycle datum.trace datum.derivation a b := by
  have hcob : hochschildCoboundaryZero (innerTraceCochain datum.trace h) a b = 0 := by
    simp [hochschildCoboundaryZero, hab, hba]
  have hdiff := traceDerivCocycle_innerCorrection datum h a b
  rw [hcob, neg_zero, sub_eq_zero] at hdiff
  exact hdiff

/-! ### Literal Kummer prime-period non-erasure -/

open RouteRMultiplierKOne

/-- Existing rational-adelic Kummer trace and coefficient derivation as bundled datum. -/
def kummerTraceDerivationDatum : TraceDerivationDatum KummerGroupRing ℂ where
  trace := kummerGroupRingTrace.toAddHom
  derivation := kummerGroupRingDerivation.toAddHom
  trace_cyclic := kummerGroupRingTrace_isTrace
  derivation_leibniz := kummerGroupRingDerivation_mul

/-- **Literal prime-period non-erasure.**  Every inner correction preserves the nonzero Kummer
period `log p` on the normalized prime inverse pair. -/
theorem kummerPrimePeriod_innerCorrection
    (p : Nat.Primes) (h : KummerGroupRing) :
    traceDerivCocycle kummerTraceDerivationDatum.trace
        (kummerTraceDerivationDatum.derivation + innerDerivation h)
        (MonoidAlgebra.of ℂ CCMRationalAdelicScaling
          (ccmRationalAdelicPrimeScaling p)⁻¹)
        (MonoidAlgebra.of ℂ CCMRationalAdelicScaling
          (ccmRationalAdelicPrimeScaling p)) =
      (Real.log (p : ℝ) : ℂ) := by
  let k := ccmRationalAdelicPrimeScaling p
  have hab :
      MonoidAlgebra.of ℂ CCMRationalAdelicScaling k⁻¹ *
          MonoidAlgebra.of ℂ CCMRationalAdelicScaling k = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hba :
      MonoidAlgebra.of ℂ CCMRationalAdelicScaling k *
          MonoidAlgebra.of ℂ CCMRationalAdelicScaling k⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  rw [traceDerivCocycle_innerCorrection_inversePair kummerTraceDerivationDatum h _ _ hab hba]
  change kummerGroupRingTrace
      (MonoidAlgebra.of ℂ CCMRationalAdelicScaling k⁻¹ *
        kummerGroupRingDerivation
          (MonoidAlgebra.of ℂ CCMRationalAdelicScaling k)) = _
  rw [kummerGroupRingPair_inv_of, ccmRationalAdelicKummerLogWeight_primeScaling]

/-- The inner-corrected Kummer prime period is unconditionally nonzero. -/
theorem kummerPrimePeriod_innerCorrection_ne_zero
    (p : Nat.Primes) (h : KummerGroupRing) :
    traceDerivCocycle kummerTraceDerivationDatum.trace
        (kummerTraceDerivationDatum.derivation + innerDerivation h)
        (MonoidAlgebra.of ℂ CCMRationalAdelicScaling
          (ccmRationalAdelicPrimeScaling p)⁻¹)
        (MonoidAlgebra.of ℂ CCMRationalAdelicScaling
          (ccmRationalAdelicPrimeScaling p)) ≠ 0 := by
  rw [kummerPrimePeriod_innerCorrection p h]
  exact_mod_cast primeLogComplex_ne_zero p

/-! ## Normalized product-trace simplex -/

open scoped TensorProduct

variable {R B G : Type*} [CommRing R] [Ring B] [Algebra R B] [Group G]

/-- A linear trace normalized by `τ(1)=1`. -/
structure NormalizedLinearTrace (R B : Type*) [CommRing R] [Ring B] [Algebra R B] where
  trace : B →ₗ[R] R
  cyclic : ∀ a b : B, trace (a * b) = trace (b * a)
  map_one : trace 1 = 1

/-- Product-trace value of the normalized Hochschild simplex attached to a group representation. -/
theorem normalizedClockSimplex_productTrace
    (τ : NormalizedLinearTrace R B) (u : G →* Bˣ) (g h : G) :
    hochschildDegreeOneProductTrace τ.trace
        (hochschildBoundaryTwoPure (R := R) (u g : B) (u h : B)
          (↑((u (g * h))⁻¹) : B)) = 1 := by
  rw [hochschildDegreeOneProductTrace_boundaryTwoPure τ.trace τ.cyclic]
  have hprod : ((u g : B) * (u h : B)) * (↑((u (g * h))⁻¹) : B) = 1 := by
    change (↑(u g * u h * (u (g * h))⁻¹) : B) = 1
    rw [← u.map_mul]
    simp
  rw [hprod, τ.map_one]

/-! ### Literal rational-adelic multiplier simplex -/

open RouteRMultiplierKOne

/-- The coefficient-at-identity trace pulled back to the exact rational-adelic multiplier algebra
is cyclic and normalized. -/
def rationalAdelicMultiplierNormalizedTrace :
    NormalizedLinearTrace ℂ Mult where
  trace := kummerGroupRingTrace.comp multiplierToKummerGroupRing.toLinearMap
  cyclic a b := by
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul]
    exact kummerGroupRingTrace_isTrace _ _
  map_one := by
    simp [kummerGroupRingTrace]

/-- Literal unit-valued representation `k ↦ dilUnit k` of the rational-adelic scaling group. -/
def rationalAdelicDilUnitRepresentation : CCMRationalAdelicScaling →* Multˣ :=
  (SkewMonoidAlgebra.of MCore CCMRationalAdelicScaling).toHomUnits

@[simp]
theorem rationalAdelicDilUnitRepresentation_apply (k : CCMRationalAdelicScaling) :
    rationalAdelicDilUnitRepresentation k = dilUnit k := rfl

/-- Equation (3.4) on the card's literal `dilUnit` simplex and exact normalized source trace. -/
theorem rationalAdelicDilUnitClockSimplex_productTrace
    (g h : CCMRationalAdelicScaling) :
    hochschildDegreeOneProductTrace rationalAdelicMultiplierNormalizedTrace.trace
        (hochschildBoundaryTwoPure
          (rationalAdelicDilUnitRepresentation g : Mult)
          (rationalAdelicDilUnitRepresentation h : Mult)
          (↑((rationalAdelicDilUnitRepresentation (g * h))⁻¹) : Mult)) = 1 := by
  exact normalizedClockSimplex_productTrace rationalAdelicMultiplierNormalizedTrace
    rationalAdelicDilUnitRepresentation g h

/-- Product trace is not an ordinary Hochschild homology cocycle on the literal source simplex. -/
theorem rationalAdelicDilUnitClockSimplex_productTrace_ne_zero
    (g h : CCMRationalAdelicScaling) :
    hochschildDegreeOneProductTrace rationalAdelicMultiplierNormalizedTrace.trace
        (hochschildBoundaryTwoPure
          (rationalAdelicDilUnitRepresentation g : Mult)
          (rationalAdelicDilUnitRepresentation h : Mult)
          (↑((rationalAdelicDilUnitRepresentation (g * h))⁻¹) : Mult)) ≠ 0 := by
  rw [rationalAdelicDilUnitClockSimplex_productTrace]
  exact one_ne_zero

/-! ## Finite multiplicative clock and ordinary group coboundary -/

variable {F : Type*} [CommRing F]

/-- Raw finite clock coordinate `κ=χ-1`. -/
def finiteClockDefect (χ : G →* Fˣ) (g : G) : F :=
  (χ g : F) - 1

/-- **Finite-clock Maurer--Cartan law.** -/
theorem finiteClockDefect_mul (χ : G →* Fˣ) (g h : G) :
    finiteClockDefect χ (g * h) - finiteClockDefect χ g - finiteClockDefect χ h =
      finiteClockDefect χ g * finiteClockDefect χ h := by
  simp only [finiteClockDefect, map_mul, Units.val_mul]
  ring

/-- Product trace realizes the raw quadratic finite-clock defect as a normalized Hochschild
boundary.  This is the exact coefficient form of equation (3.7) in the paper card. -/
theorem finiteClockDefect_productTrace_boundary
    (τ : NormalizedLinearTrace R B) (u : G →* Bˣ) (χ : G →* Rˣ)
    (g h : G) (c : R) :
    (finiteClockDefect χ (g * h) - finiteClockDefect χ g - finiteClockDefect χ h) * c =
      hochschildDegreeOneProductTrace τ.trace
        ((finiteClockDefect χ g * finiteClockDefect χ h * c) •
          hochschildBoundaryTwoPure (R := R) (u g : B) (u h : B)
            (↑((u (g * h))⁻¹) : B)) := by
  rw [finiteClockDefect_mul, map_smul,
    normalizedClockSimplex_productTrace τ u g h]
  simp

/-- Inhomogeneous ordinary group coboundary of the raw clock coordinate. -/
def finiteClockGroupCoboundary (χ : G →* Fˣ) (g h : G) : F :=
  finiteClockDefect χ h - finiteClockDefect χ (g * h) + finiteClockDefect χ g

/-- Ordinary binary cohomology is blind to the raw quadratic clock term: it is already the
negative coboundary of `κ`. -/
theorem finiteClockGroupCoboundary_eq_neg_mul (χ : G →* Fˣ) (g h : G) :
    finiteClockGroupCoboundary χ g h =
      -(finiteClockDefect χ g * finiteClockDefect χ h) := by
  rw [finiteClockGroupCoboundary]
  have hmc := finiteClockDefect_mul χ g h
  linear_combination -hmc

/-! ## Positive logarithmic coordinate -/

/-- A multiplicative real character whose values are strictly positive. -/
structure PositiveRealCharacter (G : Type*) [Group G] where
  toMonoidHom : G →* ℝ
  positive : ∀ g : G, 0 < toMonoidHom g

instance : CoeFun (PositiveRealCharacter G) (fun _ => G → ℝ) :=
  ⟨fun χ => χ.toMonoidHom⟩

/-- Logarithmic clock coordinate. -/
def logarithmicClock (χ : PositiveRealCharacter G) (g : G) : ℝ :=
  Real.log (χ g)

/-- **Logarithmic flatness.**  Every positive multiplicative clock is additive after applying
`log`, including every off-neutral clock. -/
theorem logarithmicClock_mul (χ : PositiveRealCharacter G) (g h : G) :
    logarithmicClock χ (g * h) = logarithmicClock χ g + logarithmicClock χ h := by
  rw [logarithmicClock, logarithmicClock, logarithmicClock, χ.toMonoidHom.map_mul,
    Real.log_mul (χ.positive g).ne' (χ.positive h).ne']

/-- The formal-group law `X+Y+XY` is globally linearized on `X,Y>-1` by `log(1+X)`. -/
theorem logarithm_linearizes_multiplicativeFormalGroup
    {x y : ℝ} (hx : -1 < x) (hy : -1 < y) :
    Real.log (1 + (x + y + x * y)) = Real.log (1 + x) + Real.log (1 + y) := by
  have hxpos : 0 < 1 + x := by linarith
  have hypos : 0 < 1 + y := by linarith
  rw [show 1 + (x + y + x * y) = (1 + x) * (1 + y) by ring,
    Real.log_mul hxpos.ne' hypos.ne']

/-! ### Formal logarithmic linearization over `ℚ` -/

/-- Multiplicative formal-group coordinate obtained from the formal exponential. -/
def formalMultiplicativeExpCoordinate (a : ℚ) : PowerSeries ℚ :=
  PowerSeries.rescale a (PowerSeries.exp ℚ) - 1

/-- The derivative of the formal logarithm is the inverse of `1+X`, written without choosing an
inverse operation. -/
theorem derivative_formalLog_mul_one_add_X :
    PowerSeries.derivative ℚ (PowerSeries.log ℚ) * (1 + PowerSeries.X) = 1 := by
  rw [PowerSeries.deriv_log, mul_add, mul_one]
  ext n
  cases n with
  | zero => simp
  | succ n => simp [PowerSeries.coeff_mk, pow_succ]

/-- The formal series `log(1+X)` is a left compositional inverse of `exp(X)-1` over `ℚ`. -/
theorem formalLog_subst_exp_sub_one :
    (PowerSeries.log ℚ).subst (PowerSeries.exp ℚ - 1) = PowerSeries.X := by
  let g : PowerSeries ℚ := PowerSeries.exp ℚ - 1
  have hg0 : PowerSeries.constantCoeff g = 0 := by simp [g]
  have hg : PowerSeries.HasSubst g :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hg0
  apply PowerSeries.derivative.ext
  · rw [PowerSeries.derivative_subst ℚ hg, PowerSeries.derivative_X]
    have hdg : PowerSeries.derivative ℚ g = PowerSeries.exp ℚ := by
      simp [g, PowerSeries.derivative_exp]
    have hsubOneAddX :
        ((1 + PowerSeries.X : PowerSeries ℚ).subst g) = PowerSeries.exp ℚ := by
      rw [PowerSeries.subst_add hg, PowerSeries.subst_X hg]
      rw [show (1 : PowerSeries ℚ) = PowerSeries.C 1 by simp, PowerSeries.subst_C]
      simp [g]
    rw [hdg]
    calc
      (PowerSeries.derivative ℚ (PowerSeries.log ℚ)).subst g * PowerSeries.exp ℚ =
          (PowerSeries.derivative ℚ (PowerSeries.log ℚ)).subst g *
            ((1 + PowerSeries.X : PowerSeries ℚ).subst g) := by rw [hsubOneAddX]
      _ = (PowerSeries.derivative ℚ (PowerSeries.log ℚ) *
          (1 + PowerSeries.X)).subst g := by
            rw [PowerSeries.subst_mul hg]
      _ = 1 := by
        rw [derivative_formalLog_mul_one_add_X]
        rw [show (1 : PowerSeries ℚ) = PowerSeries.C 1 by simp, PowerSeries.subst_C]
        simp
  · have hzero := PowerSeries.constantCoeff_subst_eq_zero hg0
        (PowerSeries.log ℚ) PowerSeries.constantCoeff_log
    rw [PowerSeries.constantCoeff_eq]
    simpa [g] using hzero

/-- Exponential coordinates carry addition to the formal group `F(X,Y)=X+Y+XY`. -/
theorem formalMultiplicativeExpCoordinate_groupLaw (a b : ℚ) :
    formalMultiplicativeExpCoordinate a + formalMultiplicativeExpCoordinate b +
        formalMultiplicativeExpCoordinate a * formalMultiplicativeExpCoordinate b =
      formalMultiplicativeExpCoordinate (a + b) := by
  rw [formalMultiplicativeExpCoordinate, formalMultiplicativeExpCoordinate,
    formalMultiplicativeExpCoordinate]
  calc
    _ = PowerSeries.rescale a (PowerSeries.exp ℚ) *
          PowerSeries.rescale b (PowerSeries.exp ℚ) - 1 := by ring
    _ = _ := by rw [PowerSeries.exp_mul_exp_eq_exp_add]

/-- The same formal logarithm reads an exponential coordinate as the additive coordinate `aX`. -/
theorem formalLog_subst_formalMultiplicativeExpCoordinate (a : ℚ) :
    (PowerSeries.log ℚ).subst (formalMultiplicativeExpCoordinate a) =
      a • PowerSeries.X := by
  let q : PowerSeries ℚ := a • PowerSeries.X
  have hq : PowerSeries.HasSubst q := PowerSeries.HasSubst.smul_X' a
  have hg : PowerSeries.HasSubst (PowerSeries.exp ℚ - 1) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    simp
  have hcoord : formalMultiplicativeExpCoordinate a =
      (PowerSeries.exp ℚ - 1).subst q := by
    rw [formalMultiplicativeExpCoordinate, PowerSeries.rescale_eq_subst]
    rw [PowerSeries.subst_sub hq]
    congr 1
    rw [show (1 : PowerSeries ℚ) = PowerSeries.C 1 by simp, PowerSeries.subst_C]
    simp
  rw [hcoord, ← PowerSeries.subst_comp_subst_apply hg hq,
    formalLog_subst_exp_sub_one, PowerSeries.subst_X hq]

/-- Formal counterpart of the global analytic identity: `log(1+X)` linearizes
`F(X,Y)=X+Y+XY` over `ℚ`. -/
theorem formalMultiplicativeLogarithm_linearizes (a b : ℚ) :
    (PowerSeries.log ℚ).subst
        (formalMultiplicativeExpCoordinate a + formalMultiplicativeExpCoordinate b +
          formalMultiplicativeExpCoordinate a * formalMultiplicativeExpCoordinate b) =
      (PowerSeries.log ℚ).subst (formalMultiplicativeExpCoordinate a) +
        (PowerSeries.log ℚ).subst (formalMultiplicativeExpCoordinate b) := by
  rw [formalMultiplicativeExpCoordinate_groupLaw,
    formalLog_subst_formalMultiplicativeExpCoordinate,
    formalLog_subst_formalMultiplicativeExpCoordinate,
    formalLog_subst_formalMultiplicativeExpCoordinate, add_smul]

/-- Exact radial Riemann-chart logarithmic coordinate `log(q^t)=t log q`. -/
theorem logarithmicClock_real_rpow {q : ℝ} (hq : 0 < q) (t : ℝ) :
    Real.log (q ^ t) = t * Real.log q :=
  Real.log_rpow hq t

/-! ## Square-clock rigidity in the raw coordinate -/

/-- Raw real radial clock `κ_t(q)=q^t-1`. -/
def radialClockDefect (q t : ℝ) : ℝ :=
  q ^ t - 1

/-- Hostile boundary for a binary-curvature interpretation.  At every `q>1`, the off-neutral
parameter `t=1` has nonzero raw quadratic defect while its logarithmic square-clock defect is
exactly zero. -/
theorem offNeutral_rawQuadratic_nonzero_logarithmicClock_flat
    {q : ℝ} (hq : 1 < q) :
    radialClockDefect q 1 ^ 2 ≠ 0 ∧
      Real.log ((q ^ 2) ^ (1 : ℝ)) - 2 * Real.log (q ^ (1 : ℝ)) = 0 := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  constructor
  · apply pow_ne_zero
    simpa [radialClockDefect] using sub_ne_zero.mpr (ne_of_gt hq)
  · rw [Real.log_rpow (sq_pos_of_pos hqpos), Real.log_rpow hqpos]
    simp

/-- Exact square-clock Maurer--Cartan identity. -/
theorem radialClockDefect_sq {q : ℝ} (hq : 0 < q) (t : ℝ) :
    radialClockDefect (q ^ 2) t - 2 * radialClockDefect q t =
      radialClockDefect q t ^ 2 := by
  have hpow : (q ^ 2) ^ t = q ^ t * q ^ t := by
    rw [← Real.rpow_two q, ← Real.rpow_mul hq.le]
    rw [show (2 : ℝ) * t = t + t by ring, Real.rpow_add hq]
  rw [radialClockDefect, radialClockDefect, hpow]
  ring

/-- Agreement of the raw finite defect with an additive clock at `q` and `q²` forces the neutral
radial rate. -/
theorem radialClockDefect_additive_sq_iff_neutral
    {q t : ℝ} (hq : 1 < q) :
    radialClockDefect (q ^ 2) t = 2 * radialClockDefect q t ↔ t = 0 := by
  constructor
  · intro hadd
    have hsq := radialClockDefect_sq (lt_trans zero_lt_one hq) t
    rw [hadd, sub_self] at hsq
    have hkappa : radialClockDefect q t = 0 := sq_eq_zero_iff.mp hsq.symm
    have hrpow : q ^ t = 1 := sub_eq_zero.mp hkappa
    have hlog := congrArg Real.log hrpow
    rw [Real.log_rpow (lt_trans zero_lt_one hq), Real.log_one] at hlog
    exact (mul_eq_zero.mp hlog).resolve_right (ne_of_gt (Real.log_pos hq))
  · rintro rfl
    simp [radialClockDefect]

/-! ## Exact Riemann-source instantiation -/

/-- Raw clock coordinate `κ_s(n)=χ_s(n)-1` of the actual Deninger half-density mate gain. -/
def riemannSourceClockDefect (n : ℕ) (s : ℂ) : ℝ :=
  deningerHalfDensityMateGain n s - 1

/-- The actual positive radial source character is the real power with rate `2 Re(s)-1`. -/
theorem deningerHalfDensityMateGain_eq_rpow
    {n : ℕ} (hn : 0 < n) (s : ℂ) :
    deningerHalfDensityMateGain n s = (n : ℝ) ^ (2 * s.re - 1) := by
  rw [deningerHalfDensityMateGain, Real.rpow_def_of_pos (by exact_mod_cast hn)]
  congr 1
  ring

/-- The paper's raw Riemann clock is literally the universal radial clock defect. -/
theorem riemannSourceClockDefect_eq_radialClockDefect
    {n : ℕ} (hn : 0 < n) (s : ℂ) :
    riemannSourceClockDefect n s = radialClockDefect (n : ℝ) (2 * s.re - 1) := by
  rw [riemannSourceClockDefect, radialClockDefect, deningerHalfDensityMateGain_eq_rpow hn]

/-- Exact finite-clock Maurer--Cartan law on the actual positive radial Riemann source. -/
theorem riemannSourceClockDefect_mul
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (s : ℂ) :
    riemannSourceClockDefect (m * n) s - riemannSourceClockDefect m s -
        riemannSourceClockDefect n s =
      riemannSourceClockDefect m s * riemannSourceClockDefect n s := by
  rw [riemannSourceClockDefect, riemannSourceClockDefect,
    riemannSourceClockDefect, deningerHalfDensityMateGain_mul hm hn]
  ring

/-- Exact source realization (4.3): on two ordinary-prime clocks, the actual Riemann quadratic
defect times the leading coefficient is the product trace of the correspondingly scaled literal
`dilUnit` Hochschild boundary. -/
theorem riemannSourceQuadraticClock_productTraceBoundary
    (p q : Nat.Primes) (s : ℂ) (c : ℂ) :
    ((riemannSourceClockDefect ((p : ℕ) * (q : ℕ)) s -
        riemannSourceClockDefect (p : ℕ) s -
        riemannSourceClockDefect (q : ℕ) s : ℝ) : ℂ) * c =
      hochschildDegreeOneProductTrace rationalAdelicMultiplierNormalizedTrace.trace
        ((((riemannSourceClockDefect (p : ℕ) s : ℂ) *
          (riemannSourceClockDefect (q : ℕ) s : ℂ) * c)) •
          hochschildBoundaryTwoPure
            (rationalAdelicDilUnitRepresentation
              (ccmRationalAdelicPrimeScaling p) : Mult)
            (rationalAdelicDilUnitRepresentation
              (ccmRationalAdelicPrimeScaling q) : Mult)
            (↑((rationalAdelicDilUnitRepresentation
              (ccmRationalAdelicPrimeScaling p *
                ccmRationalAdelicPrimeScaling q))⁻¹) : Mult)) := by
  rw [riemannSourceClockDefect_mul p.2.pos q.2.pos]
  rw [map_smul, rationalAdelicDilUnitClockSimplex_productTrace]
  norm_cast
  ring

/-- On an actual ordinary-prime clock, vanishing of the quadratic source coefficient is exactly
the critical-line condition.  This classifies the representative; it does not assert vanishing. -/
theorem riemannSourcePrimeQuadraticClock_eq_zero_iff_re_eq_half
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    (riemannSourceClockDefect (p : ℕ) (rho : ℂ) : ℂ) ^ 2 *
        thetaInternalJetLeadingSourceCoefficient rho = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    have hc := thetaInternalJetLeadingSourceCoefficient_ne_zero rho
    have hsq : (riemannSourceClockDefect (p : ℕ) (rho : ℂ) : ℂ) ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_right hc
    have hkC : (riemannSourceClockDefect (p : ℕ) (rho : ℂ) : ℂ) = 0 :=
      sq_eq_zero_iff.mp hsq
    have hkR : riemannSourceClockDefect (p : ℕ) (rho : ℂ) = 0 :=
      Complex.ofReal_eq_zero.mp hkC
    have hgain : deningerHalfDensityMateGain (p : ℕ) (rho : ℂ) = 1 := by
      exact sub_eq_zero.mp hkR
    exact (deningerHalfDensityMateGain_eq_one_iff_re_eq_half p.2.two_le _).mp hgain
  · intro hline
    have hgain : deningerHalfDensityMateGain (p : ℕ) (rho : ℂ) = 1 :=
      (deningerHalfDensityMateGain_eq_one_iff_re_eq_half p.2.two_le _).mpr hline
    simp [riemannSourceClockDefect, hgain]

/-- The logarithmic coordinate of the actual source character is globally linear and equals
`(2 Re(s)-1) log n`, including off-centre parameters. -/
theorem logarithm_deningerHalfDensityMateGain (n : ℕ) (s : ℂ) :
    Real.log (deningerHalfDensityMateGain n s) =
      (2 * s.re - 1) * Real.log n := by
  simp [deningerHalfDensityMateGain]

/-- Literal physical residue (4.2) on the trace-one ordinary-prime atom. -/
theorem xiPrimeResidue_eq_sourceNormalClockDefect
    (n : ℕ) (rho : XiDivisorSupport) (p : Nat.Primes) :
    ccmRationalAdelicTwoLegCyclicResidue
        ((GaloisForLFunctions.HTGeometry.cyclicParacyclicEquivarianceDefect
          ccmRationalAdelicDegreeOneCyclicRotation
          (sourceDaggerNormalizedDegreeOneRotationLinear n (rho : ℂ))
          (ccmMobiusThetaXiJetTwoLegLanding
            (xiSupportMultiplicity rho) (xiSpectralPointSupport rho)))
          (ccmRationalAdelicOrdinaryPrimeCycleAtom p)) =
      (((deningerHalfDensityMateGain n (rho : ℂ) : ℂ) - 1) *
        thetaInternalJetLeadingSourceCoefficient rho) := by
  rw [GaloisForLFunctions.IrregularStokes.ccmXiPrimeResidue_eq_centralHolonomyDefect]
  rfl

/-! ## Raw-coordinate compatibility -/

/-- Exact Theorem 5.1 of the paper card.  A response family invariant under every declared inner
correction and agreeing with the raw radial clock at `q` and `q²` can be additive at those two
scales only at the neutral parameter. -/
theorem rawClockResponse_compatibility_forces_neutral
    {D H : Type*} (shiftByInner : D → H → D) (response : D → ℝ → ℝ)
    (D₀ : D) {q t c : ℝ} (hq : 1 < q) (hc : c ≠ 0)
    (hinner : ∀ h : H, response (shiftByInner D₀ h) = response D₀)
    (hadd : response D₀ (q ^ 2) = 2 * response D₀ q)
    (hqmatch : response D₀ q = radialClockDefect q t * c)
    (hqsqmatch : response D₀ (q ^ 2) = radialClockDefect (q ^ 2) t * c) :
    t = 0 := by
  have _ := hinner
  have hscaled :
      radialClockDefect (q ^ 2) t * c =
        2 * (radialClockDefect q t * c) := by
    rw [← hqsqmatch, ← hqmatch]
    exact hadd
  have hzero :
      (radialClockDefect (q ^ 2) t - 2 * radialClockDefect q t) * c = 0 := by
    linear_combination hscaled
  have hraw : radialClockDefect (q ^ 2) t = 2 * radialClockDefect q t := by
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp hzero).resolve_right hc
  exact (radialClockDefect_additive_sq_iff_neutral hq).mp hraw

end

end RHTower
