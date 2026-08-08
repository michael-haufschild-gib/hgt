import GaloisForLFunctions.HTGeometry.TraceDerivationCyclicCocycleLaw
import GaloisForLFunctions.RHTower.MobiusThetaPhysicalParacyclicSourceNullHomology
import GaloisForLFunctions.RHTower.RouteRPreDivisorRationalAdelicMultiplierKOneHomology
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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

/-- Exact radial Riemann-chart logarithmic coordinate `log(q^t)=t log q`. -/
theorem logarithmicClock_real_rpow {q : ℝ} (hq : 0 < q) (t : ℝ) :
    Real.log (q ^ t) = t * Real.log q :=
  Real.log_rpow hq t

/-! ## Square-clock rigidity in the raw coordinate -/

/-- Raw real radial clock `κ_t(q)=q^t-1`. -/
def radialClockDefect (q t : ℝ) : ℝ :=
  q ^ t - 1

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

end

end RHTower
