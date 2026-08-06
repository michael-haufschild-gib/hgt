import GaloisForLFunctions.HTGeometry.DoubleSineOrbitResidueObstruction
import GaloisForLFunctions.HTGeometry.DifferentialIndependence
import Mathlib.RingTheory.Derivation.DifferentialRing

/-!
# The cylinder differential and the character obstruction

On the multiplicative cylinder the coordinate `X = exp(2πi z/ω)` is an exponential, so
differentiation in `z` becomes `lam` times the Euler operator `X d/dX`, with `lam = 2πi/ω`.  That
makes `K(X)` a differential field whose constants contain `K`, and it turns a constant-coefficient
differential character of the cotangent model into a constant-coefficient Euler-operator
combination with a proportional top coefficient.

Combining this with the multiplicative-orbit residue obstruction gives the theorem the
several-translation telescoping reduction needs:

```text
σ_q k − k  ≠  ∑ₙ α_n ∂ⁿ b,        b(X) = c (X+1)/(X-1),
```

for every rational `k`, every nonzero finite constant character `α`, every non-torsion `q`, every
nonzero `lam` and every nonzero `c`.  Three equivalent shapes are provided: with the explicit
iterate `cylDeriv^[n]`, with `differentialJet` for the cylinder differential structure, and with
`Finsupp.linearCombination` — the last is exactly the shape produced by the arbitrary-family
Ostrowski criterion of `SourceLogarithmicBoundary`.

Everything is proved over an arbitrary field of characteristic zero, so the base may itself be the
function field of a second cylinder.
-/

open Polynomial
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K]

/-- The cylinder derivation of `K(X)`: the coordinate `X` is an exponential with logarithmic
derivative `lam`, so differentiation is `lam` times the Euler operator `X d/dX`. -/
def cylDeriv (lam : K) (y : RatFunc K) : RatFunc K :=
  algebraMap K (RatFunc K) lam * ratFuncEulerOp y

theorem cylDeriv_add (lam : K) (x y : RatFunc K) :
    cylDeriv lam (x + y) = cylDeriv lam x + cylDeriv lam y := by
  rw [cylDeriv, cylDeriv, cylDeriv, ratFuncEulerOp, ratFuncEulerOp, ratFuncEulerOp, map_add]
  ring

theorem cylDeriv_mul (lam : K) (x y : RatFunc K) :
    cylDeriv lam (x * y) = x * cylDeriv lam y + y * cylDeriv lam x := by
  rw [cylDeriv, cylDeriv, cylDeriv, ratFuncEulerOp, ratFuncEulerOp, ratFuncEulerOp,
    Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

@[simp] theorem cylDeriv_algebraMap (lam a : K) :
    cylDeriv lam (algebraMap K (RatFunc K) a) = 0 := by
  rw [cylDeriv, ratFuncEulerOp, (ratFuncDerivative K).map_algebraMap, mul_zero, mul_zero]

/-- The bundled cylinder derivation. -/
def cylDerivation (lam : K) : Derivation K (RatFunc K) (RatFunc K) :=
  (algebraMap K (RatFunc K) lam * algebraMap (Polynomial K) (RatFunc K) Polynomial.X) •
    ratFuncDerivative K

theorem cylDerivation_apply (lam : K) (y : RatFunc K) :
    cylDerivation lam y = cylDeriv lam y := by
  rw [cylDerivation, Derivation.smul_apply, smul_eq_mul, cylDeriv, ratFuncEulerOp]
  ring

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K]

local instance cylIntAlgebraRatFunc : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _

/-- The cylinder differential structure on `K(X)`. -/
@[reducible] def cylinderDifferential (lam : K) : Differential (RatFunc K) where
  deriv := Derivation.restrictScalars ℤ (cylDerivation lam)

theorem cylinderDifferential_deriv (lam : K) (y : RatFunc K) :
    letI := cylinderDifferential lam
    y′ = cylDeriv lam y := cylDerivation_apply lam y

theorem differentialJet_cylinder (lam : K) (n : ℕ) (y : RatFunc K) :
    letI := cylinderDifferential lam
    differentialJet n y = (cylDeriv lam)^[n] y := by
  letI := cylinderDifferential lam
  induction n generalizing y with
  | zero => simp [differentialJet]
  | succ n ih =>
      rw [differentialJet_succ, ih, Function.iterate_succ_apply']
      exact cylinderDifferential_deriv lam _

theorem algebraMap_ratFunc_eq_polynomialC (x : K) :
    algebraMap K (RatFunc K) x = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C x) := by
  rw [IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K), Polynomial.algebraMap_eq]

theorem cylDeriv_iterate_cotModel (lam c : K) (n : ℕ) :
    (cylDeriv lam)^[n] (cotModel c)
      = algebraMap K (RatFunc K) (lam ^ n) * ratFuncEulerOp^[n] (cotModel c) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, cylDeriv_mul, cylDeriv_algebraMap, mul_zero, add_zero,
        cylDeriv, ← mul_assoc, ← map_mul, Function.iterate_succ_apply']
      ring_nf

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K]

/-- **No nonzero constant differential character of the cotangent model telescopes.**  For a
non-torsion multiplier `q`, a nonzero exponential-coordinate scale `lam` and a nonzero cotangent
coefficient `c`, no finite nonzero constant-coefficient differential character of `b = c(X+1)/(X-1)`
is a `q`-dilation coboundary in `K(X)`. -/
theorem no_constantCharacter_dilationTelescoping [CharZero K]
    (q lam c : K) (hq : q ≠ 0) (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1)
    (hlam : lam ≠ 0) (hc : c ≠ 0)
    (α : ℕ →₀ K) (hα : α ≠ 0) (k : RatFunc K) :
    ratFuncScale q hq k - k
      ≠ ∑ n ∈ α.support, algebraMap K (RatFunc K) (α n) * (cylDeriv lam)^[n] (cotModel c) := by
  classical
  intro heq
  have hne : α.support.Nonempty := Finsupp.support_nonempty_iff.mpr hα
  set r : ℕ := α.support.max' hne with hr
  set a : ℕ → K := fun n => α n * lam ^ n with ha
  have har : a r ≠ 0 :=
    mul_ne_zero (Finsupp.mem_support_iff.mp (Finset.max'_mem _ hne)) (pow_ne_zero _ hlam)
  have hsub : α.support ⊆ Finset.range (r + 1) := by
    intro n hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' _ n hn))
  have hterm : ∀ n : ℕ, algebraMap K (RatFunc K) (α n) * (cylDeriv lam)^[n] (cotModel c)
      = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (a n))
        * ratFuncEulerOp^[n] (cotModel c) := by
    intro n
    rw [cylDeriv_iterate_cotModel, ← mul_assoc, ← map_mul, ← algebraMap_ratFunc_eq_polynomialC]
  have hext : ∑ n ∈ α.support, (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (a n))
        * ratFuncEulerOp^[n] (cotModel c))
      = ∑ n ∈ Finset.range (r + 1), (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (a n))
        * ratFuncEulerOp^[n] (cotModel c)) := by
    refine Finset.sum_subset hsub ?_
    intro n _ hn
    have hzero : α n = 0 := Finsupp.notMem_support_iff.mp hn
    simp [ha, hzero]
  have hsum : ∑ n ∈ α.support, algebraMap K (RatFunc K) (α n) * (cylDeriv lam)^[n] (cotModel c)
      = eulerCombination a r (cotModel c) := by
    rw [eulerCombination, ← hext]
    exact Finset.sum_congr rfl fun n _ => hterm n
  rw [hsum] at heq
  exact not_dilationTelescoped_eulerCombination_cotModel q hq hqtor c hc a r har ⟨k, heq.symm⟩

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K]

/-- The differential-jet form of the character obstruction. -/
theorem no_constantCharacter_dilationTelescoping_jet [CharZero K]
    (q lam c : K) (hq : q ≠ 0) (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1)
    (hlam : lam ≠ 0) (hc : c ≠ 0)
    (α : ℕ →₀ K) (hα : α ≠ 0) (k : RatFunc K) :
    letI := cylinderDifferential lam
    ratFuncScale q hq k - k
      ≠ ∑ n ∈ α.support, algebraMap K (RatFunc K) (α n) * differentialJet n (cotModel c) := by
  letI := cylinderDifferential lam
  have hrw : ∀ n : ℕ, differentialJet n (cotModel c) = (cylDeriv lam)^[n] (cotModel c) :=
    fun n => differentialJet_cylinder lam n (cotModel c)
  simp only [hrw]
  exact no_constantCharacter_dilationTelescoping q lam c hq hqtor hlam hc α hα k

/-- The `Finsupp.linearCombination` form of the character obstruction: the shape produced by the
arbitrary-family Ostrowski criterion. -/
theorem no_constantCharacter_dilationTelescoping_linearCombination [CharZero K]
    (q lam c : K) (hq : q ≠ 0) (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1)
    (hlam : lam ≠ 0) (hc : c ≠ 0)
    (α : ℕ →₀ K) (hα : α ≠ 0) (k : RatFunc K) :
    letI := cylinderDifferential lam
    ratFuncScale q hq k - k
      ≠ Finsupp.linearCombination (RatFunc K)
          (fun n : ℕ => differentialJet n (cotModel c))
          (Finsupp.mapRange (algebraMap K (RatFunc K)) (map_zero _) α) := by
  classical
  letI := cylinderDifferential lam
  have hinj : Function.Injective (algebraMap K (RatFunc K)) :=
    (algebraMap K (RatFunc K)).injective
  have hsupp : (Finsupp.mapRange (algebraMap K (RatFunc K)) (map_zero _) α).support
      = α.support := Finsupp.support_mapRange_of_injective (map_zero _) α hinj
  rw [Finsupp.linearCombination_apply, Finsupp.sum, hsupp]
  simp only [Finsupp.mapRange_apply, smul_eq_mul]
  exact no_constantCharacter_dilationTelescoping_jet q lam c hq hqtor hlam hc α hα k

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The two-cylinder instance -/

/-- **The character obstruction over the second cylinder's function field.**  Instantiating the
base field at `ℂ(u₁)` gives the obstruction in the two-cylinder field `ℂ(u₁)(u₂)`, where the
paired telescoping theorem actually produces its base element.  No specialization of the `u₁`
factor is involved. -/
theorem no_constantCharacter_dilationTelescoping_twoCylinder
    (q lam c : ℂ) (hq : q ≠ 0) (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1)
    (hlam : lam ≠ 0) (hc : c ≠ 0)
    (α : ℕ →₀ ℂ) (hα : α ≠ 0) (k : RatFunc (RatFunc ℂ)) :
    ratFuncScale (algebraMap ℂ (RatFunc ℂ) q) (by simpa using hq) k - k
      ≠ ∑ n ∈ α.support,
          algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ)) (algebraMap ℂ (RatFunc ℂ) (α n))
            * (cylDeriv (algebraMap ℂ (RatFunc ℂ) lam))^[n]
                (cotModel (algebraMap ℂ (RatFunc ℂ) c)) := by
  classical
  have hinj : Function.Injective (algebraMap ℂ (RatFunc ℂ)) :=
    (algebraMap ℂ (RatFunc ℂ)).injective
  set β : ℕ →₀ RatFunc ℂ :=
    Finsupp.mapRange (algebraMap ℂ (RatFunc ℂ)) (map_zero _) α with hβ
  have hsupp : β.support = α.support :=
    Finsupp.support_mapRange_of_injective (map_zero _) α hinj
  have hβne : β ≠ 0 := by
    intro hzero
    apply hα
    have : β.support = (0 : ℕ →₀ RatFunc ℂ).support := by rw [hzero]
    rw [hsupp, Finsupp.support_zero] at this
    exact Finsupp.support_eq_empty.mp this
  have hmain := no_constantCharacter_dilationTelescoping
    (K := RatFunc ℂ) (algebraMap ℂ (RatFunc ℂ) q) (algebraMap ℂ (RatFunc ℂ) lam)
    (algebraMap ℂ (RatFunc ℂ) c) (by simpa using hq)
    (fun n hn hcon => hqtor n hn (hinj (by rw [map_zpow₀, map_one]; exact hcon)))
    (by simpa using hlam) (by simpa using hc) β hβne k
  rw [hsupp] at hmain
  simpa [hβ] using hmain

end

end GaloisForLFunctions.HTGeometry
