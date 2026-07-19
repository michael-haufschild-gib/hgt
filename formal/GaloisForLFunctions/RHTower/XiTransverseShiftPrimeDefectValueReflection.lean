import GaloisForLFunctions.RHTower.XiTransverseShiftDefectDifferentialRank
import GaloisForLFunctions.RHTower.ReflectionDifferenceFaces

/-!
# Value reflection for every integral Xi transverse shift

For every natural shift `a`, the transverse source `Lambda(n)(1-n^{-a})` is exactly the shift
defect of the actual completed logarithmic derivative after subtracting the corresponding
archimedean logarithmic-derivative difference.  This holds on the Euler half-plane and hence as an
upper-end germ.

The correction is rational when `a` is even, as developed by the even-shift telescope module.  No
rationality or differential-algebraicity claim is made here for odd shifts.  The point is the
exact value relation: the arbitrary-family collision matroid already proved for the source
carriers is an actual completed-Xi corrected-defect family law for every integral shift.
-/

namespace RHTower

open Complex Function ArithmeticFunction Filter Set
open scoped Differential LSeries.notation

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- The transverse shift source L-series is the difference of the von Mangoldt L-series at `s`
and `s+a`. -/
theorem LSeries_xiTransverseShiftArithmetic (a : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => xiTransverseShiftArithmetic a n) s =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s -
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s + a) := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let g : ℕ → ℂ := fun n =>
    dirichletShift (a : ℂ) vonMangoldtArithmetic n
  have hf : LSeriesSummable f s := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hsa : 1 < (s + (a : ℂ)).re := by
    have ha : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    norm_num [Complex.add_re]
    linarith
  have hshift : LSeriesSummable g s := by
    rw [show g = fun n => dirichletShift (a : ℂ) vonMangoldtArithmetic n by rfl,
      dirichletShift_LSeriesSummable_iff]
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt hsa
  have hsub := LSeries_sub hf hshift
  rw [show LSeries g s = LSeries f (s + a) by
    exact LSeries_dirichletShift (a : ℂ) s vonMangoldtArithmetic] at hsub
  simpa [f, g, xiTransverseShiftArithmetic,
    xiTransverseShiftFiniteAbscissaSource, vonMangoldtFiniteAbscissaSource,
    vonMangoldtArithmetic] using hsub

/-- Exact archimedean/boundary logarithmic-derivative correction at shift `a`. -/
def xiTransverseShiftArchimedeanCorrection (a : ℕ) (s : ℂ) : ℂ :=
  logDeriv archFactor (s + a) - logDeriv archFactor s

/-- Raw shift-`a` defect of the actual completed logarithmic derivative. -/
def xiTransverseShiftRawLogDerivDefect (a : ℕ) (s : ℂ) : ℂ :=
  logDeriv xi (s + a) - logDeriv xi s

/-- Corrected shift-`a` defect of the actual completed logarithmic derivative. -/
def xiTransverseShiftPrimeDefect (a : ℕ) (s : ℂ) : ℂ :=
  xiTransverseShiftRawLogDerivDefect a s -
    xiTransverseShiftArchimedeanCorrection a s

/-- The archimedean correction is the additive shift defect of the arch-factor logarithmic
derivative. -/
theorem xiTransverseShiftArchimedeanCorrection_eq_forwardDifference
    (a : ℕ) (s : ℂ) :
    xiTransverseShiftArchimedeanCorrection a s =
      forwardDifference (a : ℂ) (logDeriv archFactor) s := by
  rfl

/-- **Completed-prime forward-difference interface.** Every corrected integral Xi shift defect is
the additive shift defect of the completed logarithmic derivative with its archimedean part
removed. -/
theorem xiTransverseShiftPrimeDefect_eq_forwardDifference
    (a : ℕ) (s : ℂ) :
    xiTransverseShiftPrimeDefect a s =
      forwardDifference (a : ℂ)
        (fun z ↦ logDeriv xi z - logDeriv archFactor z) s := by
  simp [xiTransverseShiftPrimeDefect,
    xiTransverseShiftRawLogDerivDefect,
    xiTransverseShiftArchimedeanCorrection,
    forwardDifference]
  ring

/-- **General integral-shift prime exposure.** On the Euler half-plane, the corrected actual
completed-Xi shift defect is exactly the complete transverse prime-source L-series. -/
theorem xiTransverseShiftPrimeDefect_eq_lSeries
    (a : ℕ) {s : ℂ} (hs : 1 < s.re) :
    xiTransverseShiftPrimeDefect a s =
      LSeries (fun n => xiTransverseShiftArithmetic a n) s := by
  have hsa : 1 < (s + (a : ℂ)).re := by
    have ha : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    norm_num [Complex.add_re]
    linarith
  have hsplit := seamFluxCochain_eq_prime_add_archimedean_of_one_lt_re hs
  have hsplitA := seamFluxCochain_eq_prime_add_archimedean_of_one_lt_re hsa
  rw [seamFluxCochain] at hsplit hsplitA
  rw [infinitePrimeFlux_eq_vonMangoldtLSeries hs] at hsplit
  rw [infinitePrimeFlux_eq_vonMangoldtLSeries hsa] at hsplitA
  have hsource := LSeries_xiTransverseShiftArithmetic a hs
  unfold xiTransverseShiftPrimeDefect xiTransverseShiftRawLogDerivDefect
    xiTransverseShiftArchimedeanCorrection
  linear_combination hsplit - hsplitA - hsource

/-! ## General reflection cocycle -/

/-- Reflection about the midpoint `(1-a)/2` of a shift-`a` Xi difference. -/
def xiTransverseShiftReflection (a : ℕ) (s : ℂ) : ℂ :=
  1 - a - s

@[simp]
theorem xiTransverseShiftReflection_involutive (a : ℕ) (s : ℂ) :
    xiTransverseShiftReflection a (xiTransverseShiftReflection a s) = s := by
  simp [xiTransverseShiftReflection]

/-- The raw completed-Xi shift defect is exactly fixed by reflection about `(1-a)/2`. -/
theorem xiTransverseShiftRawLogDerivDefect_reflection (a : ℕ) (s : ℂ) :
    xiTransverseShiftRawLogDerivDefect a (xiTransverseShiftReflection a s) =
      xiTransverseShiftRawLogDerivDefect a s := by
  have hsym : ∀ z : ℂ,
      logDeriv xi (2 * (1 / 2 : ℂ) - z) = (-1 : ℂ) * logDeriv xi z := by
    intro z
    convert logDeriv_xi_reciprocity z using 1 <;> ring_nf
  have h := forwardDifference_signed_reflection
    (f := logDeriv xi) (c := (1 / 2 : ℂ)) (ε := (-1 : ℂ))
    (τ := (a : ℂ)) hsym s
  rw [show 2 * ((1 / 2 : ℂ) - (a : ℂ) / 2) - s =
      xiTransverseShiftReflection a s by
    simp [xiTransverseShiftReflection]
    ring] at h
  simpa [xiTransverseShiftRawLogDerivDefect, forwardDifference] using h

/-- The archimedean reflection defect induced by subtracting the exact shift correction. -/
def xiTransverseShiftReflectionCocycle (a : ℕ) (s : ℂ) : ℂ :=
  xiTransverseShiftArchimedeanCorrection a s -
    xiTransverseShiftArchimedeanCorrection a (xiTransverseShiftReflection a s)

/-- The general reflection cocycle is anti-invariant. -/
theorem xiTransverseShiftReflectionCocycle_reflection (a : ℕ) (s : ℂ) :
    xiTransverseShiftReflectionCocycle a (xiTransverseShiftReflection a s) =
      -xiTransverseShiftReflectionCocycle a s := by
  rw [xiTransverseShiftReflectionCocycle,
    xiTransverseShiftReflectionCocycle,
    xiTransverseShiftReflection_involutive]
  ring

/-- **General integral-shift reflection cocycle.** The corrected prime defect changes under
reflection exactly by the archimedean correction cocycle. -/
theorem xiTransverseShiftPrimeDefect_reflection_cocycle (a : ℕ) (s : ℂ) :
    xiTransverseShiftPrimeDefect a (xiTransverseShiftReflection a s) =
      xiTransverseShiftPrimeDefect a s + xiTransverseShiftReflectionCocycle a s := by
  rw [xiTransverseShiftPrimeDefect, xiTransverseShiftPrimeDefect,
    xiTransverseShiftRawLogDerivDefect_reflection,
    xiTransverseShiftReflectionCocycle]
  ring

/-- Half-cocycle centering of the corrected shift-`a` prime defect. -/
def xiTransverseCenteredShiftPrimeDefect (a : ℕ) (s : ℂ) : ℂ :=
  xiTransverseShiftPrimeDefect a s +
    (1 / 2 : ℂ) * xiTransverseShiftReflectionCocycle a s

/-- **General centered reflection law.** Half-cocycle centering makes every integral-shift prime
defect exactly fixed by reflection about `(1-a)/2`. -/
theorem xiTransverseCenteredShiftPrimeDefect_reflection (a : ℕ) (s : ℂ) :
    xiTransverseCenteredShiftPrimeDefect a (xiTransverseShiftReflection a s) =
      xiTransverseCenteredShiftPrimeDefect a s := by
  rw [xiTransverseCenteredShiftPrimeDefect, xiTransverseCenteredShiftPrimeDefect,
    xiTransverseShiftPrimeDefect_reflection_cocycle,
    xiTransverseShiftReflectionCocycle_reflection]
  ring

/-- Upper-end germ of the actual corrected completed-Xi shift-`a` defect. -/
def xiTransverseShiftPrimeDefectUpperEndGerm (a : ℕ) : Germ upperEndFilter ℂ :=
  ((fun z : ℂ => xiTransverseShiftPrimeDefect a (-Complex.I * z)) :
    Germ upperEndFilter ℂ)

/-- **Arbitrary-shift completed-Xi value reflection.** The analytic carrier of every transverse
source is exactly the corrected shift defect of the actual completed logarithmic derivative, as
an upper-end germ. -/
theorem xiTransverseShiftUpperEndGerm_eq_xiTransverseShiftPrimeDefect (a : ℕ) :
    finiteAbscissaLSeriesToUpperEndGerm
        (xiTransverseShiftFiniteAbscissaSource a) =
      xiTransverseShiftPrimeDefectUpperEndGerm a := by
  apply Germ.coe_eq.mpr
  have hupper : ∀ᶠ z in upperEndFilter, 1 < z.im := by
    rw [upperEndFilter_basis.eventually_iff]
    exact ⟨1, trivial, fun _ hz => hz⟩
  filter_upwards [hupper] with z hz
  have hs : 1 < (-Complex.I * z).re := by
    simpa [Complex.mul_re] using hz
  have h := xiTransverseShiftPrimeDefect_eq_lSeries a hs
  simpa [xiTransverseShiftPrimeDefectUpperEndGerm,
    finiteAbscissaLSeriesToUpperEndGerm,
    xiTransverseShiftArithmetic] using h.symm

end

end RHTower
