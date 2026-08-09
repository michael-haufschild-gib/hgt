import GaloisForLFunctions.RHTower.ArithmeticMixedRateStableQuotient
import GaloisForLFunctions.RHTower.PrimeDepthBVWoldCurvedSourceDifferential

/-!
# The arithmetic three-chart stable boundary class

The one-dimensional degree-two stable-primitive quotient of the radial prime/depth complex carries
one real coordinate.  On the source chart

`ℓ_s(p,m) = (1 − 2 Re s) m log p`

that coordinate is computed by three internally unrelated arithmetic readers:

* the mixed prime/depth Stokes density, i.e. the stable-quotient coordinate itself;
* the negative logarithmic slope of the Sonin relative determinant torsion `τ_r(s) = r^{2 Re s −1}`;
* the normalized Route-R BV--Wold triangle holonomy on the same-prime cells `(2,0), (2,1), (2,2)`.

All three equal `1 − 2 Re s`.  Reflection `s ↦ 1 − conj s` negates the class, which vanishes
exactly on the critical line.  Nothing here forces the class to vanish at a zero of `Ξ`.
-/

namespace RHTower

open Filter Topology GaloisForLFunctions.HTGeometry.Interfinity

noncomputable section

/-! ## The Route-R triangle -/

/-- The same-prime BV--Wold cell mass of the card: `m_e = 2^{-(e+1)}`. -/
theorem primeDepthBVWold_witness_mass (e : ℕ) :
    primeDepthBVFirstTraceDepthWeight ((⟨2, Nat.prime_two⟩ : Nat.Primes), e) =
      (2 : ℝ)⁻¹ ^ (e + 1) := by
  rw [primeDepthBVFirstTraceDepthWeight_eq]
  norm_num
  ring

/-- The same-prime BV--Wold depth clock of the card: `λ_e = (e+1) log 2`. -/
theorem primeDepthBVWold_witness_clock (e : ℕ) :
    xiGammaEulerPrimitivePrimeDepthLogClock ((⟨2, Nat.prime_two⟩ : Nat.Primes), e) =
      (e + 1 : ℕ) * Real.log 2 := by
  rw [xiGammaEulerPrimitivePrimeDepthLogClock_apply]
  norm_num

/-- The oriented triangle defect of the BV--Wold connection on the three same-prime witness
cells. -/
theorem primeDepthBVWold_witness_triangle :
    primeDepthBVWoldConnection primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne +
        primeDepthBVWoldConnection primeDepthBVWoldWitnessOne primeDepthBVWoldWitnessTwo -
      primeDepthBVWoldConnection primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessTwo =
      -Real.log 2 / 8 := by
  have hswap := primeDepthBVWoldConnection_swap primeDepthBVWoldWitnessZero
    primeDepthBVWoldWitnessTwo
  have hcurv := primeDepthBVWoldAdditiveCurvature_witness
  rw [primeDepthBVWoldAdditiveCurvature] at hcurv
  linarith

/-- The Route-R triangle holonomy of the exponentiated BV--Wold transport. -/
def routeRHolonomy (s : ℂ) : ℝ :=
  primeDepthBVWoldTransport (2 * s.re - 1) primeDepthBVWoldWitnessZero
      primeDepthBVWoldWitnessOne *
    primeDepthBVWoldTransport (2 * s.re - 1) primeDepthBVWoldWitnessOne
      primeDepthBVWoldWitnessTwo /
    primeDepthBVWoldTransport (2 * s.re - 1) primeDepthBVWoldWitnessZero
      primeDepthBVWoldWitnessTwo

theorem log_routeRHolonomy (s : ℂ) :
    Real.log (routeRHolonomy s) = (Real.log 2 / 8) * (1 - 2 * s.re) := by
  rw [routeRHolonomy, primeDepthBVWoldTransport, primeDepthBVWoldTransport,
    primeDepthBVWoldTransport, ← Real.exp_add, ← Real.exp_sub, Real.log_exp]
  linear_combination (2 * s.re - 1) * primeDepthBVWold_witness_triangle

/-! ## The Sonin torsion chart -/

/-- The Sonin relative determinant torsion `τ_r(s) = r^{2 Re s − 1}`. -/
def soninTorsion (r : ℝ) (s : ℂ) : ℝ := r ^ (2 * s.re - 1)

theorem log_soninTorsion {r : ℝ} (hr : 0 < r) (s : ℂ) :
    Real.log (soninTorsion r s) = (2 * s.re - 1) * Real.log r :=
  Real.log_rpow hr _

/-! ## The source chart -/

/-- The source chart `ℓ_s(p,m) = (1 − 2 Re s) m log p`. -/
def sourceChart (s : ℂ) : PrimeDepthFunction := linearWitness (1 - 2 * s.re)

theorem sourceChart_apply (s : ℂ) (p : Nat.Primes) (m : ℕ) :
    sourceChart s p m = (1 - 2 * s.re) * m * Real.log (p.1 : ℝ) := rfl

theorem sourceChart_mem (s : ℂ) : sourceChart s ∈ radialSpace := linearWitness_mem _

/-- The stable class of the source chart. -/
def sourceChartClass (s : ℂ) : radialSlice.StableH stableSpace :=
  Submodule.Quotient.mk (radialSlice.dRes ⟨sourceChart s, sourceChart_mem s⟩)

/-! ## The three-chart identity -/

/-- The stable-quotient coordinate of the source chart is the mixed prime/depth Stokes density. -/
theorem mixedRateQuotientEquiv_sourceChartClass (s : ℂ) :
    mixedRateQuotientEquiv (sourceChartClass s) = 1 - 2 * s.re := by
  rw [sourceChartClass, mixedRateQuotientEquiv_apply]
  exact mixedRate_linearWitness _

/-- **Three-chart identity.**  The mixed prime/depth Stokes density, the negative Sonin torsion
slope, and the normalized Route-R BV--Wold triangle holonomy are one and the same real number. -/
theorem arithmetic_three_chart_identity (s : ℂ) {r : ℝ} (hr : 1 < r) :
    mixedRateQuotientEquiv (sourceChartClass s) = 1 - 2 * s.re ∧
      -Real.log (soninTorsion r s) / Real.log r = 1 - 2 * s.re ∧
        (8 / Real.log 2) * Real.log (routeRHolonomy s) = 1 - 2 * s.re := by
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
  have hlogr : Real.log r ≠ 0 := ne_of_gt (Real.log_pos hr)
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  refine ⟨mixedRateQuotientEquiv_sourceChartClass s, ?_, ?_⟩
  · rw [log_soninTorsion hr0]
    field_simp
    ring
  · rw [log_routeRHolonomy]
    field_simp

/-! ## Reflection -/

/-- Reflection in the critical line negates the class. -/
theorem sourceChart_reflection (s : ℂ) :
    (1 : ℝ) - 2 * ((1 : ℂ) - (starRingEnd ℂ) s).re = -(1 - 2 * s.re) := by
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
  ring

theorem mixedRateQuotientEquiv_sourceChartClass_reflection (s : ℂ) :
    mixedRateQuotientEquiv (sourceChartClass ((1 : ℂ) - (starRingEnd ℂ) s)) =
      -mixedRateQuotientEquiv (sourceChartClass s) := by
  rw [mixedRateQuotientEquiv_sourceChartClass, mixedRateQuotientEquiv_sourceChartClass,
    sourceChart_reflection]

/-- The class vanishes exactly on the critical line. -/
theorem mixedRateQuotientEquiv_sourceChartClass_eq_zero_iff (s : ℂ) :
    mixedRateQuotientEquiv (sourceChartClass s) = 0 ↔ s.re = 1 / 2 := by
  rw [mixedRateQuotientEquiv_sourceChartClass]
  constructor <;> intro h <;> linarith

/-- The stable class itself vanishes exactly on the critical line. -/
theorem sourceChartClass_eq_zero_iff (s : ℂ) :
    sourceChartClass s = 0 ↔ s.re = 1 / 2 := by
  rw [← mixedRateQuotientEquiv_sourceChartClass_eq_zero_iff]
  constructor
  · intro h; rw [h, map_zero]
  · intro h; exact mixedRateQuotientEquiv.injective (by rw [h, map_zero])

end

end RHTower
