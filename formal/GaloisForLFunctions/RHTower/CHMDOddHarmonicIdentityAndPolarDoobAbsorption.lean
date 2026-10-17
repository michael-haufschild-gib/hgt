import GaloisForLFunctions.RHTower.CHMDThetaHarmonicIdentity
import GaloisForLFunctions.RHTower.CHMDPolarPlane
import GaloisForLFunctions.RHTower.CHMDInfiniteCriticalModes
import GaloisForLFunctions.RHTower.CHMDCriticalBandReduction
import GaloisForLFunctions.RHTower.CHMDReducedSpectralCore
import GaloisForLFunctions.RHTower.ThetaHalfPortStieltjesSpectral
import GaloisForLFunctions.RHTower.WeilPhiDoobArchimedeanJumpAndHalfLineFolding

/-!
# Odd Theta Harmonic Identity, Infinite Odd Critical Multiplicity, and Polar-Doob Collar Absorption

This module resolves the wrong-parity obstruction on the odd sector of the `Θ`-Doob graph
identified in `docs/reports/chmd-revisit.md` (Survivor Candidate 1) and establishes the secondary
odd-sector Doob ground-state formalism around the normalized odd theta shift-difference profile
`m_a(x) := (Θ(x - a) - Θ(x + a)) / (2 sinh(a / 2))`.

## Mathematical Overview

1. **Why the primary even-`Θ` Doob transform has the wrong sign on odd tests**:
   In `CHMDThetaHarmonicIdentity.lean`, the even ground profile `Θ(x) > 0` satisfies the pointwise
   harmonic identity with **negative** pole source `-cosh(x / 2) < 0`. Consequently, factoring an
   odd test as `f(x) = Θ(x) v(x)` (`v` odd) produces:
   - a negative local pole potential `-∫ Θ(x) cosh(x / 2) v(x)² dx < 0`, and
   - on the origin-crossing collar `x ∈ (-t, 0)` (after folding `x ↦ -x` to `(0, t)`), a
     **sum-of-values** `(v(x) + v(t - x))²` rather than a Dirichlet difference square, because
     `Θ` is even while `v` is odd.

2. **Sign flip via simultaneous strict monotonicity on `(0, ∞)` (`oddProfile_harmonic_identity`)**:
   Both `Θ(x)` and `-cosh(x / 2)` are strictly decreasing on `(0, ∞)`. Subtracting the shifted
   harmonic identities at `x - a` and `x + a` and dividing by `2 sinh(a / 2)` shows that for every
   `a > 0`, the odd profile
   $$m_a(x) := \frac{\Theta(x - a) - \Theta(x + a)}{2\sinh(a/2)}$$
   is **strictly positive on `(0, ∞)`** (`oddProfile_pos`) and satisfies the pointwise harmonic
   identity with **positive** pole source `+sinh(x / 2) > 0` on `(0, ∞)`
   (`oddProfile_harmonic_identity`). Subtracting the one-sided theta source identity at `-x` from
   that at `x` likewise cancels all diagonal constants and gives the strictly positive
   antisymmetrized source identity (`theta_odd_source_identity`).

3. **Shift-invariance of the odd polar pairing and infinite odd critical multiplicity**:
   In `SourceGraph`, the normalized odd polar vector
   $$\Psi_a := \frac{\tau_a - \tau_{-a}}{2\sinh(a/2)}$$
   (`oddPolarVectorAt a ha`) has first coordinate `Ψ_a(x) = m_a(x) / Θ(x)` (`oddPolarFunction a x`),
   belongs to `fullSpectralNullspace`, and satisfies the shift-independent pairing identity
   $$\operatorname{sourcePair}(\Psi_a, p) = \operatorname{polarSine}(p)
     = \int_{\mathbb{R}} (\Theta \cdot p_1)(x)\,\sinh(x/2)\,dx$$
   for every nonzero admissible shift `a` (`sourcePair_oddPolarVectorAt`,
   `polarSine_eq_integral_sinh`). Consequently, for any two nonzero admissible shifts `a, b`, the
   odd difference mode `Ω_{a,b} := Ψ_a - Ψ_b` (`oddCritical a b ha hb`) lies in `signedRadical`
   (`oddCritical_mem_signedRadical`), has `sourceEnergy (Ω_{a,b}) = 0` (`oddCritical_sourceEnergy`),
   and satisfies `resolvent (sourceMap Ω_{a,b}) = (1/2) • sourceMap Ω_{a,b}`
   (`oddCritical_resolvent_half`). Using the `e^{2 a x}` cusp hierarchy of `Θ(x - a) / Θ(x)`, we
   prove that `{Ω_{a_{n+1}, a_0}}_{n ∈ ℕ}` is linearly independent in `SourceGraph`
   (`oddCriticalSequence_linearIndependent`), establishing that the odd sector of `signedRadical`
   is infinite-dimensional and that any odd-sector positivity bound must factor through
   `signedRadicalᗮ` (removing the infinite-dimensional critical band at eigenvalue `1/2`).

4. **Secondary odd-sector Doob transform `f(x) = m_a(x) w(x)` (`w` even) and collar absorption**:
   Factoring an odd test function as `f(x) = m_a(x) w(x)` with `w(-x) = w(x)` **even**:
   - turns the ground-state pairing `sourcePair(Ψ_a, p)` at the secondary Doob square
     `u(x) = m_a(x) w(x)² / Θ(x)` into twice the **strictly positive** half-line `sinh(x / 2)`
     potential `2 ∫_{x > 0} m_a(x) sinh(x / 2) w(x)² dx ≥ 0`
     (`sourcePair_oddPolarVectorAt_oddProfileTest_sq`,
     `sourcePair_oddPolarVectorAt_oddProfileTest_sq_nonneg`),
   - turns the pointwise edge polarization into the pure Dirichlet difference square
     `m_a(x) m_a(x + t) (w(x) - w(x + t))²` (`oddProfile_pointwise_jump_sub_mixed`),
   - folds the full-line shift jump onto `(0, ∞)` so that **both** the direct half-line term and the
     reflected collar term on `(0, t)` carry the **same pure Dirichlet difference square**
     `(w(x) - w(y))²` (`integral_oddProfileShiftJump_eq_halfLine_of_even`), and
   - absorbs the negative archimedean collar integral into the positive direct archimedean integral
     via the strictly positive kernel `(ω(s) - ω(2x + s)) m_a(x) m_a(x + s) (w(x) - w(x + s))² ≥ 0`
     on `(0, ∞)²` (`strictAntiOn_archLevyDensity_Ioi`, `absorbedArchIntegrand_nonneg`).
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace BigOperators
noncomputable section

namespace RHTower.CHMDPolar
open CHMDDoobGraph ThetaSourceWard

/-! ## Section 1: Strict Positivity of Odd Theta Shift Differences and the Antisymmetrized Pointwise Theta Source Identity -/

theorem strictAntiOn_riemannKernelReal_Ici : StrictAntiOn riemannKernelReal (Ici (0 : ℝ)) := by
  intro a ha b hb hab
  rw [← thetaCuspFullSource_eq_riemannKernelReal, ← thetaCuspFullSource_eq_riemannKernelReal]
  exact strictAntiOn_thetaCuspFullSource ha hb hab

theorem riemannKernelReal_abs (x : ℝ) : riemannKernelReal |x| = riemannKernelReal x := by
  rcases abs_choice x with h | h <;> rw [h]
  exact WeilExcess.riemannKernelReal_neg x

theorem riemannKernelReal_add_lt_sub {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    riemannKernelReal (x + u) < riemannKernelReal (x - u) := by
  rw [← riemannKernelReal_abs (x - u)]
  apply strictAntiOn_riemannKernelReal_Ici (mem_Ici.mpr (abs_nonneg (x - u)))
    (mem_Ici.mpr (by linarith))
  rw [abs_lt]
  constructor <;> linarith

theorem riemannKernelReal_sub_pos {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    0 < riemannKernelReal (x - u) - riemannKernelReal (x + u) :=
  sub_pos.mpr (riemannKernelReal_add_lt_sub hx hu)

/-- The antisymmetrized archimedean integrand `ω(u) (Θ(x - u) - Θ(x + u))`. -/
def oddArchTerm (x u : ℝ) : ℝ :=
  archLevyDensity u * (riemannKernelReal (x - u) - riemannKernelReal (x + u))

/-- The antisymmetrized polar integrand `2 cosh(u / 2) (Θ(x - u) - Θ(x + u))`. -/
def oddPolarTerm (x u : ℝ) : ℝ :=
  2 * Real.cosh (u / 2) * (riemannKernelReal (x - u) - riemannKernelReal (x + u))

/-- The antisymmetrized prime shift sum `∑_n Λ(n) n^{-1/2} (Θ(x - log n) - Θ(x + log n))`. -/
def oddPrimeKernelSum (x : ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n *
    (riemannKernelReal (x - Real.log n) - riemannKernelReal (x + Real.log n))

theorem oddArchTerm_pos {x u : ℝ} (hx : 0 < x) (hu : 0 < u) : 0 < oddArchTerm x u :=
  mul_pos (archLevyDensity_pos hu) (riemannKernelReal_sub_pos hx hu)

theorem oddPolarTerm_pos {x u : ℝ} (hx : 0 < x) (hu : 0 < u) : 0 < oddPolarTerm x u :=
  mul_pos (by positivity) (riemannKernelReal_sub_pos hx hu)

theorem oddPrimeKernelSum_term_nonneg {x : ℝ} (hx : 0 < x) (n : ℕ) :
    0 ≤ vonMangoldtAtom n *
      (riemannKernelReal (x - Real.log n) - riemannKernelReal (x + Real.log n)) := by
  by_cases hn : 2 ≤ n
  · have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    exact mul_nonneg (vonMangoldtAtom_nonneg n) (riemannKernelReal_sub_pos hx hlog).le
  · unfold vonMangoldtAtom
    rw [if_neg hn, zero_mul]

theorem oddPrimeKernelSum_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ oddPrimeKernelSum x :=
  tsum_nonneg (oddPrimeKernelSum_term_nonneg hx)

theorem integrableOn_oddArchTerm (x : ℝ) : IntegrableOn (oddArchTerm x) (Ioi 0) := by
  have h1 := integrableOn_gammaSourceTerm_real x
  have h2 := integrableOn_gammaSourceTerm_real (-x)
  refine (h1.sub h2).congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp only [Pi.sub_apply, gammaSourceTerm_eq, oddArchTerm, WeilExcess.riemannKernelReal_neg]
  rw [show -x + u = -(x - u) by ring, WeilExcess.riemannKernelReal_neg]
  ring

theorem integrableOn_oddPolarTerm (x : ℝ) : IntegrableOn (oddPolarTerm x) (Ioi 0) := by
  have h1 := (integrable_cosh_mul_theta_shift (-x)).integrableOn (s := Ioi (0 : ℝ))
  have h2 := (integrable_cosh_mul_theta_shift x).integrableOn (s := Ioi (0 : ℝ))
  refine (h1.sub h2).congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp only [Pi.sub_apply, oddPolarTerm]
  rw [show -x + u = -(x - u) by ring, WeilExcess.riemannKernelReal_neg]
  ring

theorem summable_oddPrimeKernelSum (x : ℝ) :
    Summable fun n : ℕ => vonMangoldtAtom n *
      (riemannKernelReal (x - Real.log n) - riemannKernelReal (x + Real.log n)) := by
  refine ((summable_primeShift_left x).sub (summable_primeShift_right x)).congr fun n => ?_
  ring

/-- **The Antisymmetrized (Odd) Pointwise Theta Source Identity**:
subtracting `oneSided_source_equation (-x)` from `oneSided_source_equation x` cancels both the
archimedean constant `-archConstantReal * Θ(x)` and the singular diagonal density `ν(u) Θ(x)`
identically, leaving an identity in which every integrand and summand on `(0, ∞)` is strictly
positive for `x > 0`. -/
theorem theta_odd_source_identity (x : ℝ) :
    (∫ u in Ioi (0 : ℝ), oddArchTerm x u) + oddPrimeKernelSum x =
      2 * x * riemannKernelReal x + ∫ u in Ioi (0 : ℝ), oddPolarTerm x u := by
  have h1 := oneSided_source_equation x
  have h2 := oneSided_source_equation (-x)
  rw [WeilExcess.riemannKernelReal_neg] at h2
  have hgamma : (∫ u in Ioi (0 : ℝ), gammaSourceTerm x u) -
      (∫ u in Ioi (0 : ℝ), gammaSourceTerm (-x) u) = ∫ u in Ioi (0 : ℝ), oddArchTerm x u := by
    rw [← integral_sub (integrableOn_gammaSourceTerm_real x) (integrableOn_gammaSourceTerm_real (-x))]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    simp only [gammaSourceTerm_eq, oddArchTerm, WeilExcess.riemannKernelReal_neg]
    rw [show -x + u = -(x - u) by ring, WeilExcess.riemannKernelReal_neg]
    ring
  have hpolar : (∫ u in Ioi (0 : ℝ), 2 * Real.cosh (u / 2) * riemannKernelReal (-x + u)) -
      (∫ u in Ioi (0 : ℝ), 2 * Real.cosh (u / 2) * riemannKernelReal (x + u)) =
      ∫ u in Ioi (0 : ℝ), oddPolarTerm x u := by
    have h1' := (integrable_cosh_mul_theta_shift (-x)).integrableOn (s := Ioi (0 : ℝ))
    have h2' := (integrable_cosh_mul_theta_shift x).integrableOn (s := Ioi (0 : ℝ))
    rw [← integral_sub h1' h2']
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    simp only [oddPolarTerm]
    rw [show -x + u = -(x - u) by ring, WeilExcess.riemannKernelReal_neg]
    ring
  have hprime : (∑' n : ℕ, vonMangoldtAtom n * riemannKernelReal (-x + Real.log n)) -
      (∑' n : ℕ, vonMangoldtAtom n * riemannKernelReal (x + Real.log n)) = oddPrimeKernelSum x := by
    have hl : (fun n : ℕ => vonMangoldtAtom n * riemannKernelReal (-x + Real.log n)) =
        fun n : ℕ => vonMangoldtAtom n * riemannKernelReal (x - Real.log n) := by
      funext n
      rw [show -x + Real.log n = -(x - Real.log n) by ring, WeilExcess.riemannKernelReal_neg]
    rw [hl, ← (summable_primeShift_left x).tsum_sub (summable_primeShift_right x)]
    unfold oddPrimeKernelSum
    apply tsum_congr
    intro n
    ring
  linarith

/-- The normalized odd theta shift-difference profile
`m_a(x) = (Θ(x - a) - Θ(x + a)) / (2 sinh(a / 2))`. -/
def oddProfile (a x : ℝ) : ℝ :=
  (riemannKernelReal (x - a) - riemannKernelReal (x + a)) / (2 * Real.sinh (a / 2))

theorem continuous_oddProfile (a : ℝ) : Continuous (oddProfile a) := by
  unfold oddProfile
  exact ((continuous_riemannKernelReal.comp (continuous_id.sub continuous_const)).sub
    (continuous_riemannKernelReal.comp (continuous_id.add continuous_const))).div_const _

theorem oddProfile_neg (a x : ℝ) : oddProfile a (-x) = -oddProfile a x := by
  unfold oddProfile
  rw [show -x - a = -(x + a) by ring, show -x + a = -(x - a) by ring,
    WeilExcess.riemannKernelReal_neg, WeilExcess.riemannKernelReal_neg]
  ring

theorem oddProfile_zero (a : ℝ) : oddProfile a 0 = 0 := by
  unfold oddProfile
  rw [zero_sub, zero_add, WeilExcess.riemannKernelReal_neg, sub_self, zero_div]

theorem oddProfile_pos {a x : ℝ} (ha : 0 < a) (hx : 0 < x) : 0 < oddProfile a x :=
  div_pos (riemannKernelReal_sub_pos hx ha)
    (mul_pos (by norm_num) (Real.sinh_pos_iff.mpr (half_pos ha)))

theorem cosh_sub_cosh_div_sinh {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    (Real.cosh ((x - a) / 2) - Real.cosh ((x + a) / 2)) / (2 * Real.sinh (a / 2)) =
      -Real.sinh (x / 2) := by
  have hsh : Real.sinh (a / 2) ≠ 0 := Real.sinh_ne_zero.mpr (div_ne_zero ha (by norm_num))
  rw [show (x - a) / 2 = x / 2 - a / 2 by ring, show (x + a) / 2 = x / 2 + a / 2 by ring,
    Real.cosh_sub, Real.cosh_add]
  field_simp [hsh]
  ring

/-- **The Pointwise Odd Harmonic Identity for `oddProfile a`**:
while `Θ(x) > 0` has negative pole source `-cosh(x / 2) < 0` in `theta_harmonic_identity`,
both `Θ` and `-cosh(· / 2)` are strictly decreasing on `(0, ∞)`, so the odd shift-difference
profile `m_a(x) = oddProfile a x > 0` has **positive** pole source `+sinh(x / 2) > 0` on `(0, ∞)`. -/
theorem oddProfile_harmonic_identity {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    (primeKernelSum (x - a) - primeKernelSum (x + a)) / (2 * Real.sinh (a / 2)) =
      -Real.sinh (x / 2) - 2 * archConstantReal * oddProfile a x +
        (∫ u in Ioi (0 : ℝ),
          (symArchTerm (x - a) u - symArchTerm (x + a) u) / (2 * Real.sinh (a / 2))) := by
  have h1 := theta_harmonic_identity (x - a)
  have h2 := theta_harmonic_identity (x + a)
  have hint : (∫ u in Ioi (0 : ℝ),
      (symArchTerm (x - a) u - symArchTerm (x + a) u) / (2 * Real.sinh (a / 2))) =
      ((∫ u in Ioi (0 : ℝ), symArchTerm (x - a) u) -
        ∫ u in Ioi (0 : ℝ), symArchTerm (x + a) u) / (2 * Real.sinh (a / 2)) := by
    simp_rw [div_eq_mul_inv]
    rw [integral_mul_const, integral_sub (integrableOn_symArchTerm (x - a))
      (integrableOn_symArchTerm (x + a))]
  have hc := cosh_sub_cosh_div_sinh ha x
  unfold oddProfile
  calc
    (primeKernelSum (x - a) - primeKernelSum (x + a)) / (2 * Real.sinh (a / 2)) =
        (Real.cosh ((x - a) / 2) - Real.cosh ((x + a) / 2)) / (2 * Real.sinh (a / 2)) -
          2 * archConstantReal *
            ((riemannKernelReal (x - a) - riemannKernelReal (x + a)) / (2 * Real.sinh (a / 2))) +
          ((∫ u in Ioi (0 : ℝ), symArchTerm (x - a) u) -
            ∫ u in Ioi (0 : ℝ), symArchTerm (x + a) u) / (2 * Real.sinh (a / 2)) := by
      rw [h1, h2]; ring
    _ = -Real.sinh (x / 2) -
          2 * archConstantReal *
            ((riemannKernelReal (x - a) - riemannKernelReal (x + a)) / (2 * Real.sinh (a / 2))) +
          ∫ u in Ioi (0 : ℝ),
            (symArchTerm (x - a) u - symArchTerm (x + a) u) / (2 * Real.sinh (a / 2)) := by
      rw [hc, hint]

/-! ## Section 2: General Admissible Odd Polar Vectors, the Odd Critical Band, and Infinite Odd Critical Multiplicity -/

def oddPolarVectorAt (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) : SourceGraph :=
  (2 * Real.sinh (a / 2))⁻¹ •
    (CHMDThetaTranslate.lift a ha -
      CHMDThetaTranslate.lift (-a) (CHMDThetaTranslate.neg_admissible ha))

def oddPolarFunction (a x : ℝ) : ℝ :=
  (CHMDThetaTranslate.ratio a x - CHMDThetaTranslate.ratio (-a) x) / (2 * Real.sinh (a / 2))

theorem oddPolarFunction_eq_oddProfile_div (a x : ℝ) :
    oddPolarFunction a x = oddProfile a x / riemannKernelReal x := by
  unfold oddPolarFunction oddProfile CHMDThetaTranslate.ratio
  simp only [sub_neg_eq_add]
  ring

theorem oddPolarFunction_neg (a x : ℝ) : oddPolarFunction a (-x) = -oddPolarFunction a x := by
  rw [oddPolarFunction_eq_oddProfile_div, oddPolarFunction_eq_oddProfile_div,
    oddProfile_neg, WeilExcess.riemannKernelReal_neg, neg_div]

theorem oddPolarFunction_pos {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    0 < oddPolarFunction a x := by
  rw [oddPolarFunction_eq_oddProfile_div]
  exact div_pos (oddProfile_pos ha hx) (riemannKernelReal_pos x)

theorem continuous_oddPolarFunction (a : ℝ) : Continuous (oddPolarFunction a) := by
  unfold oddPolarFunction
  exact ((CHMDThetaTranslate.continuous_ratio a).sub
    (CHMDThetaTranslate.continuous_ratio (-a))).div_const _

theorem oddPolarVectorAt_source_ae (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    (oddPolarVectorAt a ha).val.fst =ᵐ[massMeasure] oddPolarFunction a := by
  let A := (CHMDThetaTranslate.lift a ha).val.fst
  let B := (CHMDThetaTranslate.lift (-a) (CHMDThetaTranslate.neg_admissible ha)).val.fst
  let c := (2 * Real.sinh (a / 2))⁻¹
  filter_upwards [CHMDThetaTranslate.lift_source_ae a ha,
    CHMDThetaTranslate.lift_source_ae (-a) (CHMDThetaTranslate.neg_admissible ha),
    Lp.coeFn_sub A B, Lp.coeFn_smul c (A - B)] with x hA hB hsub hsm
  change (c • (A - B)) x = oddPolarFunction a x
  rw [hsm, Pi.smul_apply, hsub, Pi.sub_apply]
  change c * ((CHMDThetaTranslate.lift a ha).val.fst x -
    (CHMDThetaTranslate.lift (-a) (CHMDThetaTranslate.neg_admissible ha)).val.fst x) = _
  rw [hA, hB]
  unfold oddPolarFunction CHMDThetaTranslate.ratio
  ring

theorem oddPolarVectorAt_mem_fullSpectralNullspace (a : ℝ)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    oddPolarVectorAt a ha ∈ fullSpectralNullspace := by
  intro z hz
  have hstrip := (abs_im_lt_half_of_XiC_eq_zero hz).le
  rw [oddPolarVectorAt, graphFourierReadout_smul _ _ hstrip,
    graphFourierReadout_sub _ _ hstrip,
    thetaTranslate_fourier, thetaTranslate_fourier, hz]
  simp

theorem oddPolarVectorAt_fourier_plus_pole {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    graphFourierReadout (oddPolarVectorAt a ha) (I / 2) = -1 / 2 := by
  have hsh : Real.sinh (a / 2) ≠ 0 := Real.sinh_ne_zero.mpr (div_ne_zero hane (by norm_num))
  rw [oddPolarVectorAt, graphFourierReadout_smul _ _ (by norm_num),
    graphFourierReadout_sub _ _ (by norm_num),
    thetaTranslate_fourier_plus_pole, thetaTranslate_fourier_plus_pole]
  have hs : Real.exp (-a / 2) / 2 - Real.exp (a / 2) / 2 = -Real.sinh (a / 2) := by
    rw [Real.sinh_eq, neg_div]
    ring
  simp only [neg_neg, ← Complex.ofReal_sub, hs, ← Complex.ofReal_mul]
  have he : (2 * Real.sinh (a / 2))⁻¹ * (-Real.sinh (a / 2)) = -1 / 2 := by
    field_simp [hsh]
  rw [he]
  norm_num

theorem oddPolarVectorAt_fourier_minus_pole {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    graphFourierReadout (oddPolarVectorAt a ha) (-I / 2) = 1 / 2 := by
  have hsh : Real.sinh (a / 2) ≠ 0 := Real.sinh_ne_zero.mpr (div_ne_zero hane (by norm_num))
  rw [oddPolarVectorAt, graphFourierReadout_smul _ _ (by norm_num),
    graphFourierReadout_sub _ _ (by norm_num),
    thetaTranslate_fourier_minus_pole, thetaTranslate_fourier_minus_pole]
  have hs : Real.exp (a / 2) / 2 - Real.exp (-a / 2) / 2 = Real.sinh (a / 2) := by
    rw [Real.sinh_eq, neg_div]
    ring
  simp only [← Complex.ofReal_sub, hs, ← Complex.ofReal_mul]
  have he : (2 * Real.sinh (a / 2))⁻¹ * Real.sinh (a / 2) = 1 / 2 := by
    field_simp [hsh]
  rw [he]
  norm_num

theorem polarCosine_oddPolarVectorAt {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    polarCosine (oddPolarVectorAt a ha) = 0 := by
  rw [polarCosine_eq_half_fourier, oddPolarVectorAt_fourier_plus_pole hane ha,
    oddPolarVectorAt_fourier_minus_pole hane ha]
  norm_num

theorem polarSine_oddPolarVectorAt {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    polarSine (oddPolarVectorAt a ha) = 1 / 2 := by
  rw [polarSine, oddPolarVectorAt_fourier_plus_pole hane ha,
    oddPolarVectorAt_fourier_minus_pole hane ha]
  norm_num

/-- **Shift-Invariance of the Odd Polar Pairing**:
for every nonzero admissible shift `a`, `sourcePair (oddPolarVectorAt a ha) p = polarSine p`. -/
theorem sourcePair_oddPolarVectorAt {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (p : SourceGraph) :
    sourcePair (oddPolarVectorAt a ha) p = polarSine p := by
  rw [full_nullspace_pair (oddPolarVectorAt_mem_fullSpectralNullspace a ha),
    polarCosine_oddPolarVectorAt hane ha, polarSine_oddPolarVectorAt hane ha]
  ring

theorem sourceEnergy_oddPolarVectorAt {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    sourceEnergy (oddPolarVectorAt a ha) = 1 / 2 := by
  rw [← sourcePair_self, sourcePair_oddPolarVectorAt hane ha,
    polarSine_oddPolarVectorAt hane ha]

/-- The odd critical mode `Ω_{a,b} = Ψ_a - Ψ_b` formed by subtracting two normalized odd polar
vectors at shifts `a` and `b`. -/
def oddCritical (a b : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|))
    (hb : 1 < 2 * Real.exp (-2 * |b|)) : SourceGraph :=
  oddPolarVectorAt a ha - oddPolarVectorAt b hb

/-- **Every difference of normalized odd polar vectors lies in the exact signed radical.** -/
theorem oddCritical_mem_signedRadical {a b : ℝ} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (hb : 1 < 2 * Real.exp (-2 * |b|)) :
    oddCritical a b ha hb ∈ signedRadical := by
  intro q
  rw [oddCritical, sourcePair_sub_left, sourcePair_oddPolarVectorAt ha0 ha,
    sourcePair_oddPolarVectorAt hb0 hb, sub_self]

theorem oddCritical_sourceEnergy {a b : ℝ} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (hb : 1 < 2 * Real.exp (-2 * |b|)) :
    sourceEnergy (oddCritical a b ha hb) = 0 := by
  rw [← sourcePair_self]
  exact oddCritical_mem_signedRadical ha0 hb0 ha hb _

theorem oddCritical_resolvent_half {a b : ℝ} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) (hb : 1 < 2 * Real.exp (-2 * |b|)) :
    resolvent (sourceMap (oddCritical a b ha hb)) =
      (1 / 2 : ℝ) • sourceMap (oddCritical a b ha hb) :=
  (mem_massCriticalSpace _).mp
    (radical_source_mem_massCriticalSpace (oddCritical_mem_signedRadical ha0 hb0 ha hb))

/-! ### Cusp asymptotics and infinite linear independence of the odd critical band -/

theorem oddPolarFunction_normalized_self {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x => oddPolarFunction a x / CHMDThetaTranslate.ratio a x) atTop
      (𝓝 ((2 * Real.sinh (a / 2))⁻¹)) := by
  have hp := CHMDThetaTranslate.theta_ratio_tendsto (a := a) (b := -a) (by linarith)
  have hh := ((tendsto_const_nhds (x := (1 : ℝ))).sub hp).div_const (2 * Real.sinh (a / 2))
  rw [sub_zero, one_div] at hh
  convert hh using 1
  funext x
  unfold oddPolarFunction CHMDThetaTranslate.ratio
  field_simp [(riemannKernelReal_pos x).ne', (riemannKernelReal_pos (x - a)).ne']

theorem oddPolarFunction_normalized_smaller {a b : ℝ} (hb : 0 < b) (hba : b < a) :
    Tendsto (fun x => oddPolarFunction b x / CHMDThetaTranslate.ratio a x) atTop (𝓝 0) := by
  have hp := CHMDThetaTranslate.theta_ratio_tendsto hba
  have hm := CHMDThetaTranslate.theta_ratio_tendsto (a := a) (b := -b) (by linarith)
  have hh := (hp.sub hm).div_const (2 * Real.sinh (b / 2))
  rw [sub_zero, zero_div] at hh
  convert hh using 1
  funext x
  unfold oddPolarFunction CHMDThetaTranslate.ratio
  field_simp [(riemannKernelReal_pos x).ne', (riemannKernelReal_pos (x - a)).ne']

theorem oddPolarFunctions_linearIndependent :
    LinearIndependent ℝ (fun n : ℕ => oddPolarFunction (CHMDThetaTranslate.shifts n)) := by
  classical
  rw [linearIndependent_iff]
  intro d hd
  by_contra hne
  have hs := Finsupp.support_nonempty_iff.mpr hne
  let i := d.support.min' hs
  have hi : i ∈ d.support := Finset.min'_mem _ _
  have hn : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hsh : (2 * Real.sinh (CHMDThetaTranslate.shifts i / 2))⁻¹ ≠ 0 := by
    have := Real.sinh_pos_iff.mpr (half_pos (CHMDThetaTranslate.shifts_pos i))
    positivity
  have ht (j : ℕ) (hj : j ∈ d.support) :
      Tendsto (fun x => d j * (oddPolarFunction (CHMDThetaTranslate.shifts j) x /
        CHMDThetaTranslate.ratio (CHMDThetaTranslate.shifts i) x)) atTop
        (𝓝 (if j = i then d i * (2 * Real.sinh (CHMDThetaTranslate.shifts i / 2))⁻¹ else 0)) := by
    have hij : i ≤ j := Finset.min'_le d.support j hj
    by_cases he : j = i
    · subst j
      simpa using (oddPolarFunction_normalized_self (CHMDThetaTranslate.shifts_pos i)).const_mul (d i)
    · rw [if_neg he]
      have hlt : CHMDThetaTranslate.shifts j < CHMDThetaTranslate.shifts i :=
        CHMDThetaTranslate.shifts_strictAnti (lt_of_le_of_ne hij (Ne.symm he))
      simpa using (oddPolarFunction_normalized_smaller (CHMDThetaTranslate.shifts_pos j) hlt).const_mul (d j)
  have hsum := tendsto_finsetSum d.support ht
  have heq : (∑ j ∈ d.support,
      if j = i then d i * (2 * Real.sinh (CHMDThetaTranslate.shifts i / 2))⁻¹ else 0) =
      d i * (2 * Real.sinh (CHMDThetaTranslate.shifts i / 2))⁻¹ := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [hji]
    · exact fun hh => (hh hi).elim
  rw [heq] at hsum
  have hz (x : ℝ) : ∑ j ∈ d.support,
      d j * (oddPolarFunction (CHMDThetaTranslate.shifts j) x /
        CHMDThetaTranslate.ratio (CHMDThetaTranslate.shifts i) x) = 0 := by
    have hh := congrFun hd x
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hh
    calc
      _ = (∑ j ∈ d.support, d j * oddPolarFunction (CHMDThetaTranslate.shifts j) x) /
            CHMDThetaTranslate.ratio (CHMDThetaTranslate.shifts i) x := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [hh, zero_div]
  have hlim0 := tendsto_nhds_unique hsum (by simp only [hz]; exact tendsto_const_nhds)
  exact hn ((mul_eq_zero.mp hlim0).resolve_right hsh)

def oddCriticalSequence (n : ℕ) : SourceGraph :=
  oddCritical (CHMDThetaTranslate.shifts (n + 1)) (CHMDThetaTranslate.shifts 0)
    (CHMDThetaTranslate.shifts_admissible (n + 1)) (CHMDThetaTranslate.shifts_admissible 0)

theorem oddCriticalSequence_mem_signedRadical (n : ℕ) :
    oddCriticalSequence n ∈ signedRadical :=
  oddCritical_mem_signedRadical (CHMDThetaTranslate.shifts_pos (n + 1)).ne'
    (CHMDThetaTranslate.shifts_pos 0).ne' _ _

theorem oddCriticalSequence_linearIndependent : LinearIndependent ℝ oddCriticalSequence := by
  classical
  rw [linearIndependent_iff']
  intro s c hs i hi
  have hLp : ∑ j ∈ s, c j • (oddCriticalSequence j).val.fst = 0 := by
    have hh := congrArg sourceMap hs
    simp only [map_sum, map_smul, map_zero] at hh
    exact hh
  let f : ℕ → ℝ → ℝ := fun j x =>
    oddPolarFunction (CHMDThetaTranslate.shifts (j + 1)) x -
      oddPolarFunction (CHMDThetaTranslate.shifts 0) x
  have ht (j : ℕ) :
      ((c j • (oddCriticalSequence j).val.fst : Lp ℝ 2 massMeasure) : ℝ → ℝ) =ᵐ[massMeasure]
        fun x => c j * f j x := by
    let A := (oddPolarVectorAt (CHMDThetaTranslate.shifts (j + 1))
      (CHMDThetaTranslate.shifts_admissible (j + 1))).val.fst
    let B := (oddPolarVectorAt (CHMDThetaTranslate.shifts 0)
      (CHMDThetaTranslate.shifts_admissible 0)).val.fst
    filter_upwards [Lp.coeFn_smul (c j) (oddCriticalSequence j).val.fst,
      Lp.coeFn_sub A B,
      oddPolarVectorAt_source_ae (CHMDThetaTranslate.shifts (j + 1))
        (CHMDThetaTranslate.shifts_admissible (j + 1)),
      oddPolarVectorAt_source_ae (CHMDThetaTranslate.shifts 0)
        (CHMDThetaTranslate.shifts_admissible 0)] with x h1 hsub hA hB
    rw [h1, Pi.smul_apply]
    change c j * (A - B) x = c j * f j x
    rw [hsub, Pi.sub_apply, hA, hB]
  have hae : (fun x => ∑ j ∈ s, c j * f j x) =ᵐ[massMeasure] 0 := by
    filter_upwards [Lp.coeFn_finsetSum s (fun j => c j • (oddCriticalSequence j).val.fst),
      ae_all_iff.mpr ht, Lp.coeFn_zero ℝ 2 massMeasure] with x hsum hterm hzero
    rw [hLp] at hsum
    change (∑ j ∈ s, c j * f j x) = 0
    calc
      _ = ∑ j ∈ s, (c j • (oddCriticalSequence j).val.fst : Lp ℝ 2 massMeasure) x :=
        Finset.sum_congr rfl (fun j _ => (hterm j).symm)
      _ = (0 : Lp ℝ 2 massMeasure) x := by simpa only [Finset.sum_apply] using hsum.symm
      _ = 0 := hzero
  have hcont : Continuous (fun x => ∑ j ∈ s, c j * f j x) := by
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul ((continuous_oddPolarFunction _).sub (continuous_oddPolarFunction _))
  have hraw : ∀ x, ∑ j ∈ s, c j * f j x = 0 := by
    have hh : (fun x => ∑ j ∈ s, c j * f j x) = (fun _ : ℝ => (0 : ℝ)) :=
      (hcont.ae_eq_iff_eq (μ := (volume : Measure ℝ)) continuous_const).mp
        (volume_absolutelyContinuous_mass.ae_eq hae)
    exact fun x => congrFun hh x
  -- Rewrite in terms of the linearly independent family `oddPolarFunction ∘ shifts`
  let s' : Finset ℕ := insert 0 (s.image (· + 1))
  let c' : ℕ → ℝ := fun k => if k = 0 then -∑ j ∈ s, c j else if k - 1 ∈ s then c (k - 1) else 0
  have hcomb : ∑ k ∈ s', c' k • oddPolarFunction (CHMDThetaTranslate.shifts k) = 0 := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have h0not : 0 ∉ s.image (· + 1) := by simp
    rw [Finset.sum_insert h0not, Finset.sum_image (fun a _ b _ hab => Nat.succ.inj hab)]
    have h0eq : c' 0 * oddPolarFunction (CHMDThetaTranslate.shifts 0) x =
        (-∑ j ∈ s, c j) * oddPolarFunction (CHMDThetaTranslate.shifts 0) x := by
      simp [c']
    have hsum_eq : ∑ j ∈ s, c' j.succ *
        oddPolarFunction (CHMDThetaTranslate.shifts j.succ) x =
        ∑ j ∈ s, c j * oddPolarFunction (CHMDThetaTranslate.shifts (j + 1)) x := by
      refine Finset.sum_congr rfl fun j hj => by simp [c', hj]
    rw [h0eq, hsum_eq, ← hraw x, neg_mul, Finset.sum_mul]
    simp only [f, mul_sub, Finset.sum_sub_distrib]
    ring
  have hli := (linearIndependent_iff'.mp oddPolarFunctions_linearIndependent) s' c' hcomb (i + 1)
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hi))
  simpa [c', hi] using hli

/-! ## Section 3: Secondary Odd-Sector Doob Ground-State Cancellation, Positive Sinh Potential, and Archimedean Collar Absorption -/

/-- For every graph source `p`, `polarSine p` is the literal full-line `sinh(x / 2)` moment of
`phiDoobTest p.val.fst`. -/
theorem polarSine_eq_integral_sinh (p : SourceGraph) :
    polarSine p = ∫ x : ℝ, phiDoobTest p.val.fst x * Real.sinh (x / 2) := by
  have hp : |(I / 2 : ℂ).im| ≤ 1 / 2 := by norm_num
  have hm : |(-I / 2 : ℂ).im| ≤ 1 / 2 := by norm_num
  have hdiff : (graphFourierReadout p (-I / 2) - graphFourierReadout p (I / 2)) / 2 =
      ((∫ x : ℝ, phiDoobTest p.val.fst x * Real.sinh (x / 2) : ℝ) : ℂ) := by
    unfold graphFourierReadout paperFT
    rw [← integral_sub (integrable_graphFourierReadout_source p hm)
      (integrable_graphFourierReadout_source p hp), ← integral_div, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [] with x
    have he1 : I * (-I / 2 : ℂ) * (x : ℂ) = ((x / 2 : ℝ) : ℂ) := by
      calc I * (-I / 2 : ℂ) * (x : ℂ) = -(I * I) * (x : ℂ) / 2 := by ring
        _ = _ := by rw [I_mul_I]; push_cast; ring
    have he2 : I * (I / 2 : ℂ) * (x : ℂ) = ((-x / 2 : ℝ) : ℂ) := by
      calc I * (I / 2 : ℂ) * (x : ℂ) = (I * I) * (x : ℂ) / 2 := by ring
        _ = _ := by rw [I_mul_I]; push_cast; ring
    rw [he1, he2, ← Complex.ofReal_exp, ← Complex.ofReal_exp, Real.sinh_eq]
    push_cast
    ring
  have hre := congrArg Complex.re hdiff
  rw [Complex.ofReal_re] at hre
  unfold polarSine
  simpa [Complex.div_ofNat_re, Complex.sub_re] using hre

theorem polarSine_of_source {p : SourceGraph} {f : ℝ → ℝ}
    (hp : p.val.fst =ᵐ[massMeasure] phiDoobInv f) :
    polarSine p = ∫ x : ℝ, f x * Real.sinh (x / 2) := by
  rw [polarSine_eq_integral_sinh]
  apply integral_congr_ae
  filter_upwards [volume_absolutelyContinuous_mass.ae_eq hp] with x hx
  rw [phiDoobTest, hx, phiDoobInv, mul_div_cancel₀ _ (riemannKernelReal_pos x).ne']

theorem sourcePair_oddPolarVectorAt_of_source {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) {p : SourceGraph} {f : ℝ → ℝ}
    (hp : p.val.fst =ᵐ[massMeasure] phiDoobInv f) :
    sourcePair (oddPolarVectorAt a ha) p = ∫ x : ℝ, f x * Real.sinh (x / 2) := by
  rw [sourcePair_oddPolarVectorAt hane ha, polarSine_of_source hp]

/-- **Universal Algebraic Doob Edge Polarization Identity**:
for any edge endpoints `(x, y)`, subtracting the mixed ground-state difference product
`(ψ_x - ψ_y)(ψ_x w_x² - ψ_y w_y²)` from `(ψ_x w_x - ψ_y w_y)²` yields the pure Dirichlet
difference square `ψ_x ψ_y (w_x - w_y)²`. -/
theorem doob_edge_polarization_identity (ψx ψy wx wy : ℝ) :
    (ψx * wx - ψy * wy) ^ 2 - (ψx - ψy) * (ψx * wx ^ 2 - ψy * wy ^ 2) =
      ψx * ψy * (wx - wy) ^ 2 := by
  ring

/-- The archimedean Lévy density `ω(s) = e^{-s/2} / (1 - e^{-2s})` is strictly decreasing on
`(0, ∞)`. -/
theorem strictAntiOn_archLevyDensity_Ioi : StrictAntiOn archLevyDensity (Ioi (0 : ℝ)) := by
  intro s hs t ht hst
  have hs0 : 0 < s := mem_Ioi.mp hs
  have ht0 : 0 < t := mem_Ioi.mp ht
  unfold archLevyDensity
  have hden_s : 0 < 1 - Real.exp (-2 * s) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hden_t : 0 < 1 - Real.exp (-2 * t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hnum : Real.exp (-t / 2) < Real.exp (-s / 2) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hden : 1 - Real.exp (-2 * s) < 1 - Real.exp (-2 * t) :=
    sub_lt_sub_left (Real.exp_lt_exp.mpr (by linarith)) 1
  exact div_lt_div₀ hnum hden.le (Real.exp_pos _).le hden_s

theorem archLevyDensity_add_lt_sub {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    0 < archLevyDensity s - archLevyDensity (2 * x + s) :=
  sub_pos.mpr (strictAntiOn_archLevyDensity_Ioi hs (mem_Ioi.mpr (by linarith)) (by linarith))

/-- Test function `f(x) = m_a(x) w(x)` factored through the odd ground profile `m_a = oddProfile a`. -/
def oddProfileTest (a : ℝ) (w : ℝ → ℝ) (x : ℝ) : ℝ :=
  oddProfile a x * w x

/-- The pure Dirichlet shift-jump integrand in `oddProfile a` coordinates:
`oddProfileShiftJump a w t x = m_a(x) m_a(x + t) (w(x) - w(x + t))²`. -/
def oddProfileShiftJump (a : ℝ) (w : ℝ → ℝ) (t x : ℝ) : ℝ :=
  oddProfile a x * oddProfile a (x + t) * (w x - w (x + t)) ^ 2

theorem oddProfile_pointwise_jump_sub_mixed (a : ℝ) (w : ℝ → ℝ) (t x : ℝ) :
    (oddProfileTest a w x - oddProfileTest a w (x + t)) ^ 2 -
        (oddProfile a x - oddProfile a (x + t)) *
          (oddProfileTest a (fun y => w y ^ 2) x -
            oddProfileTest a (fun y => w y ^ 2) (x + t)) =
      oddProfileShiftJump a w t x := by
  unfold oddProfileTest oddProfileShiftJump
  ring

theorem oddProfileShiftJump_nonneg_of_pos {a t x : ℝ} (ha : 0 < a) (hx : 0 < x) (ht : 0 ≤ t)
    (w : ℝ → ℝ) :
    0 ≤ oddProfileShiftJump a w t x := by
  unfold oddProfileShiftJump
  exact mul_nonneg
    (mul_nonneg (oddProfile_pos ha hx).le (oddProfile_pos ha (by linarith)).le)
    (sq_nonneg _)

/-- For any even `w : ℝ → ℝ` (`w(-x) = w(x)`), the `sinh(x / 2)` moment of `m_a(x) w(x)²` folds
onto twice the strictly nonnegative half-line integral
`2 ∫_{x > 0} m_a(x) sinh(x / 2) w(x)² dx ≥ 0`. -/
theorem integral_oddProfileTest_sq_mul_sinh_eq_two_mul_Ioi (a : ℝ) {w : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x) :
    (∫ x : ℝ, oddProfileTest a (fun y => w y ^ 2) x * Real.sinh (x / 2)) =
      2 * ∫ x in Ioi (0 : ℝ), oddProfile a x * Real.sinh (x / 2) * w x ^ 2 := by
  set f : ℝ → ℝ := fun x => oddProfileTest a (fun y => w y ^ 2) x * Real.sinh (x / 2)
  have hf_int : Integrable f := by
    have hw2c : HasCompactSupport (fun x : ℝ => w x ^ 2) := by
      rw [hasCompactSupport_iff_eventuallyEq] at hwc ⊢
      filter_upwards [hwc] with x hx; simp [hx]
    have hfc : HasCompactSupport f := by
      have h1 : HasCompactSupport (oddProfileTest a (fun y => w y ^ 2)) := hw2c.mul_left
      exact h1.mul_right
    exact (((continuous_oddProfile a).mul (hw.pow 2)).mul
      (Real.continuous_sinh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport hfc
  have hsplit := integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hf_int
  rw [compl_Iic] at hsplit
  have hneg : (∫ x in Iic (0 : ℝ), f x) = ∫ x in Ioi (0 : ℝ), f x := by
    have h1 := integral_comp_neg_Iic (c := (0 : ℝ)) f
    rw [neg_zero] at h1
    rw [← h1]
    refine setIntegral_congr_fun measurableSet_Iic fun x _ => ?_
    dsimp [f, oddProfileTest]
    rw [oddProfile_neg, heven x, neg_div, Real.sinh_neg]
    ring
  have hpos_eq : (∫ x in Ioi (0 : ℝ), f x) =
      ∫ x in Ioi (0 : ℝ), oddProfile a x * Real.sinh (x / 2) * w x ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    dsimp [f, oddProfileTest]
    ring
  change (∫ x : ℝ, f x) = 2 * ∫ x in Ioi (0 : ℝ), oddProfile a x * Real.sinh (x / 2) * w x ^ 2
  linarith

theorem integral_oddProfile_mul_sinh_mul_sq_nonneg {a : ℝ} (ha : 0 < a) (w : ℝ → ℝ) :
    0 ≤ ∫ x in Ioi (0 : ℝ), oddProfile a x * Real.sinh (x / 2) * w x ^ 2 := by
  refine setIntegral_nonneg measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := mem_Ioi.mp hx
  exact mul_nonneg
    (mul_nonneg (oddProfile_pos ha hx0).le (Real.sinh_pos_iff.mpr (half_pos hx0)).le)
    (sq_nonneg _)

/-- **The Secondary Odd-Sector Doob Ground-State Pairing Formula**:
when a graph source `p` represents the secondary Doob square `u(x) = m_a(x) w(x)² / Θ(x) = Ψ_a(x) w(x)²`
with `w` even, pairing `p` against the odd polar ground vector `Ψ_a = oddPolarVectorAt a ha` produces
twice the strictly positive half-line `sinh(x / 2)` potential:
`sourcePair (oddPolarVectorAt a ha) p = 2 ∫_{x > 0} m_a(x) sinh(x / 2) w(x)² dx ≥ 0`. -/
theorem sourcePair_oddPolarVectorAt_oddProfileTest_sq {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) {p : SourceGraph} {w : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x)
    (hp : p.val.fst =ᵐ[massMeasure] phiDoobInv (oddProfileTest a (fun y => w y ^ 2))) :
    sourcePair (oddPolarVectorAt a ha) p =
      2 * ∫ x in Ioi (0 : ℝ), oddProfile a x * Real.sinh (x / 2) * w x ^ 2 := by
  rw [sourcePair_oddPolarVectorAt_of_source hane ha hp,
    integral_oddProfileTest_sq_mul_sinh_eq_two_mul_Ioi a hw hwc heven]

theorem sourcePair_oddPolarVectorAt_oddProfileTest_sq_nonneg {a : ℝ} (ha0 : 0 < a)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) {p : SourceGraph} {w : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x)
    (hp : p.val.fst =ᵐ[massMeasure] phiDoobInv (oddProfileTest a (fun y => w y ^ 2))) :
    0 ≤ sourcePair (oddPolarVectorAt a ha) p := by
  rw [sourcePair_oddPolarVectorAt_oddProfileTest_sq ha0.ne' ha hw hwc heven hp]
  exact mul_nonneg (by norm_num) (integral_oddProfile_mul_sinh_mul_sq_nonneg ha0 w)

/-- **Exact Half-Line `(0, ∞)` Folding of the Odd-Profile Doob Shift Jump for Even `w`**:
in contrast to the even-`Θ` Doob transform on odd tests (where the origin-crossing collar `(0, t)`
produced a sum-of-values `(v(x) + v(t - x))²`), factoring an odd test as `f(x) = m_a(x) w(x)` with
`w` even turns BOTH the direct term on `(0, ∞)` and the reflected collar term on `(0, t)` into the
**pure Dirichlet difference square** `m_a(x) m_a(y) (w(x) - w(y))²`:
`∫_ℝ m_a(x) m_a(x + t) (w(x) - w(x + t))² dx
  = 2 ∫_{x > 0} m_a(x) m_a(x + t) (w(x) - w(x + t))² dx
    - ∫_{x ∈ (0, t)} m_a(x) m_a(t - x) (w(x) - w(t - x))² dx`. -/
theorem integral_oddProfileShiftJump_eq_halfLine_of_even (a : ℝ) {w : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w)
    (heven : ∀ x, w (-x) = w x) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x : ℝ, oddProfileShiftJump a w t x) =
      2 * (∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w t x) -
        ∫ x in Ioo (0 : ℝ) t,
          oddProfile a x * oddProfile a (t - x) * (w x - w (t - x)) ^ 2 := by
  have hint : Integrable (oddProfileShiftJump a w t) := by
    have hsub : HasCompactSupport (fun x : ℝ => w x - w (x + t)) :=
      hwc.sub (hwc.comp_homeomorph (Homeomorph.addRight t))
    have hsub2 : HasCompactSupport (fun x : ℝ => (w x - w (x + t)) ^ 2) := by
      rw [hasCompactSupport_iff_eventuallyEq] at hsub ⊢
      filter_upwards [hsub] with x hx; simp [hx]
    have hc : Continuous (oddProfileShiftJump a w t) := by
      unfold oddProfileShiftJump
      exact (((continuous_oddProfile a).mul
        ((continuous_oddProfile a).comp (continuous_id.add continuous_const))).mul
        ((hw.sub (hw.comp (continuous_id.add continuous_const))).pow 2))
    exact hc.integrable_of_hasCompactSupport hsub2.mul_left
  have hsplit0 := integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hint
  rw [compl_Iic] at hsplit0
  set g : ℝ → ℝ := fun u =>
    -(oddProfile a u * oddProfile a (t - u) * (w u - w (t - u)) ^ 2)
  have hneg : (∫ x in Iic (0 : ℝ), oddProfileShiftJump a w t x) =
      ∫ u in Ioi (0 : ℝ), g u := by
    have h1 := integral_comp_neg_Ioi (c := (0 : ℝ)) (oddProfileShiftJump a w t)
    rw [neg_zero] at h1
    rw [← h1]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    dsimp [g, oddProfileShiftJump]
    rw [oddProfile_neg, show -u + t = t - u by ring, heven u]
    ring
  have hg_int : IntegrableOn g (Ioi (0 : ℝ)) := by
    have hint_neg : IntegrableOn (fun u : ℝ => oddProfileShiftJump a w t (-u)) (Ioi (0 : ℝ)) :=
      hint.comp_neg.integrableOn
    refine hint_neg.congr_fun (fun u _ => ?_) measurableSet_Ioi
    dsimp [g, oddProfileShiftJump]
    rw [oddProfile_neg, show -u + t = t - u by ring, heven u]
    ring
  have hsplit_t : (∫ u in Ioi (0 : ℝ), g u) =
      (∫ u in Ioo (0 : ℝ) t, g u) + ∫ u in Ioi t, g u := by
    have h_union_eq : Ioc (0 : ℝ) t ∪ Ioi t = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi ht
    have hdisj : Disjoint (Ioc (0 : ℝ) t) (Ioi t) := Ioc_disjoint_Ioi le_rfl
    rw [← h_union_eq, setIntegral_union hdisj measurableSet_Ioi
      (hg_int.mono_set Ioc_subset_Ioi_self) (hg_int.mono_set (Ioi_subset_Ioi ht)),
      integral_Ioc_eq_integral_Ioo]
  have hcollar : (∫ u in Ioo (0 : ℝ) t, g u) =
      -∫ u in Ioo (0 : ℝ) t,
        oddProfile a u * oddProfile a (t - u) * (w u - w (t - u)) ^ 2 := by
    dsimp [g]
    exact integral_neg _
  have htail : (∫ u in Ioi t, g u) = ∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w t x := by
    have hmp : MeasurePreserving (fun x : ℝ => x + t) volume volume :=
      measurePreserving_add_right volume t
    have hemb : MeasurableEmbedding (fun x : ℝ => x + t) :=
      (Homeomorph.addRight t).measurableEmbedding
    have hpre : (fun x : ℝ => x + t) ⁻¹' Ioi t = Ioi (0 : ℝ) := by ext x; simp
    have htr := hmp.setIntegral_preimage_emb hemb g (Ioi t)
    rw [hpre] at htr
    rw [← htr]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    dsimp [g, oddProfileShiftJump]
    rw [show t - (x + t) = -x by ring, oddProfile_neg, heven x]
    ring
  rw [← hsplit0, hneg, hsplit_t, hcollar, htail]
  ring

/-- The archimedean collar-absorbed Dirichlet integrand on `(0, ∞)²`:
`absorbedArchIntegrand a w s x = (ω(s) - ω(2x + s)) m_a(x) m_a(x + s) (w(x) - w(x + s))²`. -/
def absorbedArchIntegrand (a : ℝ) (w : ℝ → ℝ) (s x : ℝ) : ℝ :=
  (archLevyDensity s - archLevyDensity (2 * x + s)) * oddProfileShiftJump a w s x

/-- **Pointwise Positivity of the Absorbed Archimedean Kernel**:
for every `a > 0`, `s > 0`, `x > 0`, and `w : ℝ → ℝ`,
`0 ≤ (ω(s) - ω(2x + s)) m_a(x) m_a(x + s) (w(x) - w(x + s))²`. -/
theorem absorbedArchIntegrand_nonneg {a s x : ℝ} (ha : 0 < a) (hs : 0 < s) (hx : 0 < x)
    (w : ℝ → ℝ) :
    0 ≤ absorbedArchIntegrand a w s x :=
  mul_nonneg (archLevyDensity_add_lt_sub hs hx).le
    (oddProfileShiftJump_nonneg_of_pos ha hx hs.le w)

end RHTower.CHMDPolar
