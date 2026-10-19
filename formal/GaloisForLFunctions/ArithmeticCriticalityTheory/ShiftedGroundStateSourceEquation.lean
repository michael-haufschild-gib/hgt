import GaloisForLFunctions.ArithmeticCriticalityTheory.OddSupersolutionCriterion
import GaloisForLFunctions.RHTower.CHMDOddHarmonicIdentityAndPolarDoobAbsorption

/-!
# The shifted ground states and their exact source equation

The shifted ground state `ω_a(x) = (Φ(x−a) − Φ(x+a)) / Φ(x)` is odd and, for `a > 0`, positive on
`(0,∞)`. Its two-sided (Dirichlet) generator is computed exactly from the pointwise harmonic identity
of Riemann's kernel (`theta_harmonic_identity`) at the three points `x`, `x − a`, `x + a`:

    (𝓛_D ω_a)(x) − Φ(x) cosh(x/2) ω_a(x) = 2 sinh(a/2) sinh(x/2) Φ(x)      for every real x.

So every shifted ground state is an exact strict supersolution of the two-sided generator on the
positive half line, with a source proportional to `sinh(x/2) Φ(x)`. The archimedean diagonal
densities cancel identically in the computation; only the shift differences of the Lévy density
survive.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- The test coordinate of the shifted ground state: `Φ(x−a) − Φ(x+a)`. -/
def shiftDifference (a x : ℝ) : ℝ := riemannKernelReal (x - a) - riemannKernelReal (x + a)

/-- The shifted ground state in Doob coordinates: `ω_a(x) = (Φ(x−a) − Φ(x+a)) / Φ(x)`. -/
def shiftedGroundState (a x : ℝ) : ℝ := shiftDifference a x / riemannKernelReal x

/-- The two-sided (Dirichlet) generator `𝓛_D ω`: archimedean shifts against the Lévy density plus
prime shifts against the von Mangoldt atoms. -/
def twoSidedGenerator (ω : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ t in Ioi (0 : ℝ), archLevyDensity t * twoSidedShiftGenerator ω t x) +
    ∑' n : ℕ, vonMangoldtAtom n * twoSidedShiftGenerator ω (Real.log n) x

theorem shiftDifference_neg (a x : ℝ) : shiftDifference a (-x) = -shiftDifference a x := by
  unfold shiftDifference
  rw [show -x - a = -(x + a) by ring, show -x + a = -(x - a) by ring,
    riemannKernelReal_neg', riemannKernelReal_neg']
  ring

theorem shiftedGroundState_neg (a x : ℝ) : shiftedGroundState a (-x) = -shiftedGroundState a x := by
  unfold shiftedGroundState
  rw [shiftDifference_neg, riemannKernelReal_neg', neg_div]

theorem shiftDifference_pos {a x : ℝ} (ha : 0 < a) (hx : 0 < x) : 0 < shiftDifference a x :=
  riemannKernelReal_sub_pos hx ha

theorem shiftedGroundState_pos {a x : ℝ} (ha : 0 < a) (hx : 0 < x) : 0 < shiftedGroundState a x :=
  div_pos (shiftDifference_pos ha hx) (riemannKernelReal_pos x)

theorem continuous_shiftDifference (a : ℝ) : Continuous (shiftDifference a) :=
  (continuous_riemannKernelReal.comp (continuous_id.sub continuous_const)).sub
    (continuous_riemannKernelReal.comp (continuous_id.add continuous_const))

theorem continuous_shiftedGroundState (a : ℝ) : Continuous (shiftedGroundState a) :=
  (continuous_shiftDifference a).div continuous_riemannKernelReal fun x =>
    (riemannKernelReal_pos x).ne'

theorem riemannKernelReal_mul_shiftedGroundState (a x : ℝ) :
    riemannKernelReal x * shiftedGroundState a x = shiftDifference a x := by
  unfold shiftedGroundState
  rw [mul_div_cancel₀ _ (riemannKernelReal_pos x).ne']

/-- The two-sided shift generator of the shifted ground state in test coordinates. -/
theorem twoSidedShiftGenerator_shiftedGroundState (a t x : ℝ) :
    twoSidedShiftGenerator (shiftedGroundState a) t x =
      shiftDifference a x * (riemannKernelReal (x + t) + riemannKernelReal (x - t)) -
        riemannKernelReal x * (shiftDifference a (x + t) + shiftDifference a (x - t)) := by
  unfold twoSidedShiftGenerator
  have h1 := riemannKernelReal_mul_shiftedGroundState a x
  have h2 := riemannKernelReal_mul_shiftedGroundState a (x + t)
  have h3 := riemannKernelReal_mul_shiftedGroundState a (x - t)
  linear_combination (riemannKernelReal (x + t) + riemannKernelReal (x - t)) * h1 -
    riemannKernelReal x * h2 - riemannKernelReal x * h3

/-- The prime atom of the two-sided generator of `ω_a`, in terms of the symmetric prime shift terms
of `Φ` at `x`, `x − a`, `x + a`. -/
theorem atom_twoSidedShiftGenerator_shiftedGroundState (a x : ℝ) (n : ℕ) :
    vonMangoldtAtom n * twoSidedShiftGenerator (shiftedGroundState a) (Real.log n) x =
      shiftDifference a x *
          (vonMangoldtAtom n *
            (riemannKernelReal (x + Real.log n) + riemannKernelReal (x - Real.log n))) -
        riemannKernelReal x *
          ((vonMangoldtAtom n *
              (riemannKernelReal (x - a + Real.log n) + riemannKernelReal (x - a - Real.log n))) -
            (vonMangoldtAtom n *
              (riemannKernelReal (x + a + Real.log n) + riemannKernelReal (x + a - Real.log n)))) := by
  rw [twoSidedShiftGenerator_shiftedGroundState]
  unfold shiftDifference
  rw [show x + Real.log n - a = x - a + Real.log n by ring,
    show x + Real.log n + a = x + a + Real.log n by ring,
    show x - Real.log n - a = x - a - Real.log n by ring,
    show x - Real.log n + a = x + a - Real.log n by ring]
  ring

/-- The prime part of the two-sided generator of `ω_a`. -/
theorem tsum_atom_twoSidedShiftGenerator_shiftedGroundState (a x : ℝ) :
    (∑' n : ℕ, vonMangoldtAtom n * twoSidedShiftGenerator (shiftedGroundState a) (Real.log n) x) =
      shiftDifference a x * primeKernelSum x -
        riemannKernelReal x * (primeKernelSum (x - a) - primeKernelSum (x + a)) := by
  have hx := summable_primeKernelSum x
  have hxa := summable_primeKernelSum (x - a)
  have hxpa := summable_primeKernelSum (x + a)
  rw [tsum_congr (atom_twoSidedShiftGenerator_shiftedGroundState a x),
    (hx.mul_left _).tsum_sub ((hxa.sub hxpa).mul_left _), tsum_mul_left, tsum_mul_left,
    hxa.tsum_sub hxpa]
  rfl

/-- The archimedean integrand of the two-sided generator of `ω_a` against the symmetrized
archimedean terms of `Φ`; the diagonal densities cancel. -/
theorem archLevy_twoSidedShiftGenerator_shiftedGroundState (a x u : ℝ) :
    archLevyDensity u * twoSidedShiftGenerator (shiftedGroundState a) u x =
      -(shiftDifference a x * symArchTerm x u -
        riemannKernelReal x * (symArchTerm (x - a) u - symArchTerm (x + a) u)) := by
  rw [twoSidedShiftGenerator_shiftedGroundState]
  unfold shiftDifference symArchTerm
  rw [show x + u - a = x - a + u by ring, show x + u + a = x + a + u by ring,
    show x - u - a = x - a - u by ring, show x - u + a = x + a - u by ring]
  ring

/-- The archimedean part of the two-sided generator of `ω_a`. -/
theorem integral_archLevy_twoSidedShiftGenerator_shiftedGroundState (a x : ℝ) :
    (∫ u in Ioi (0 : ℝ), archLevyDensity u * twoSidedShiftGenerator (shiftedGroundState a) u x) =
      -(shiftDifference a x * (∫ u in Ioi (0 : ℝ), symArchTerm x u) -
        riemannKernelReal x *
          ((∫ u in Ioi (0 : ℝ), symArchTerm (x - a) u) - ∫ u in Ioi (0 : ℝ), symArchTerm (x + a) u)) := by
  have hx := integrableOn_symArchTerm x
  have hxa := integrableOn_symArchTerm (x - a)
  have hxpa := integrableOn_symArchTerm (x + a)
  have h1 : (∫ u in Ioi (0 : ℝ), archLevyDensity u * twoSidedShiftGenerator (shiftedGroundState a) u x)
      = ∫ u in Ioi (0 : ℝ), -(shiftDifference a x * symArchTerm x u -
          riemannKernelReal x * (symArchTerm (x - a) u - symArchTerm (x + a) u)) :=
    setIntegral_congr_fun measurableSet_Ioi fun u _ =>
      archLevy_twoSidedShiftGenerator_shiftedGroundState a x u
  have hA : IntegrableOn (fun u => shiftDifference a x * symArchTerm x u) (Ioi 0) :=
    hx.const_mul _
  have hB : IntegrableOn
      (fun u => riemannKernelReal x * (symArchTerm (x - a) u - symArchTerm (x + a) u)) (Ioi 0) :=
    (hxa.sub hxpa).const_mul _
  rw [h1, integral_neg, integral_sub hA hB, integral_const_mul, integral_const_mul,
    integral_sub hxa hxpa]

theorem cosh_half_sub_sub_cosh_half_add (x a : ℝ) :
    Real.cosh ((x - a) / 2) - Real.cosh ((x + a) / 2) =
      -(2 * Real.sinh (x / 2) * Real.sinh (a / 2)) := by
  rw [show (x - a) / 2 = x / 2 - a / 2 by ring, show (x + a) / 2 = x / 2 + a / 2 by ring,
    Real.cosh_sub, Real.cosh_add]
  ring

/-- **Source equation of the shifted ground state.** For every real `a` and `x`,
`(𝓛_D ω_a)(x) − Φ(x) cosh(x/2) ω_a(x) = 2 sinh(a/2) sinh(x/2) Φ(x)`. -/
theorem twoSidedGenerator_shiftedGroundState_sub_potential (a x : ℝ) :
    twoSidedGenerator (shiftedGroundState a) x -
        riemannKernelReal x * Real.cosh (x / 2) * shiftedGroundState a x =
      2 * Real.sinh (a / 2) * Real.sinh (x / 2) * riemannKernelReal x := by
  unfold twoSidedGenerator
  rw [integral_archLevy_twoSidedShiftGenerator_shiftedGroundState,
    tsum_atom_twoSidedShiftGenerator_shiftedGroundState]
  have hPx := theta_harmonic_identity x
  have hPxa := theta_harmonic_identity (x - a)
  have hPxpa := theta_harmonic_identity (x + a)
  have hcosh := cosh_half_sub_sub_cosh_half_add x a
  have hmul : riemannKernelReal x * shiftedGroundState a x =
      riemannKernelReal (x - a) - riemannKernelReal (x + a) :=
    riemannKernelReal_mul_shiftedGroundState a x
  unfold shiftDifference
  linear_combination (riemannKernelReal (x - a) - riemannKernelReal (x + a)) * hPx -
    riemannKernelReal x * hPxa + riemannKernelReal x * hPxpa - riemannKernelReal x * hcosh -
    Real.cosh (x / 2) * hmul

/-- On the positive half line the shifted ground state with `a > 0` is a strict two-sided
supersolution: its source `2 sinh(a/2) sinh(x/2) Φ(x)` is positive. -/
theorem potential_lt_twoSidedGenerator_shiftedGroundState {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    riemannKernelReal x * Real.cosh (x / 2) * shiftedGroundState a x <
      twoSidedGenerator (shiftedGroundState a) x := by
  have h := twoSidedGenerator_shiftedGroundState_sub_potential a x
  have hpos : 0 < 2 * Real.sinh (a / 2) * Real.sinh (x / 2) * riemannKernelReal x := by
    have h1 := Real.sinh_pos_iff.mpr (half_pos ha)
    have h2 := Real.sinh_pos_iff.mpr (half_pos hx)
    have h3 := riemannKernelReal_pos x
    positivity
  linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
