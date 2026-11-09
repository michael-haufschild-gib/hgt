import GaloisForLFunctions.SurfaceOfSpecZ.TwoFrobeniiNeedAnAttainedTop
import GaloisForLFunctions.RHTower.CrossRouteReceiverBridges
import GaloisForLFunctions.RHTower.AsymptoticAbscissaLawProducers

/-!
# Stepanov bounds produce the asymptotic abscissa law

The asymptotic abscissa law (`RHTower.AsymptoticAbscissaLaw`): if only finitely many zeros of `ζ` lie
right of `½ + h`, none does. It follows from the absence of an attained top
(`RHTower.asymptoticAbscissaLaw_of_not_attainedTop`), and the sampling theorems give exactly that:
a one-sided bound at a sampling set leaves no deepest off-line zero.

* `asymptoticAbscissaLaw_of_noDeepest`: no deepest off-line zero gives the law;
* from a lower or an upper bound on the spline traces at the primes `p ≡ a (mod q)`
  (`asymptoticAbscissaLaw_of_bddBelow_primes_mod`, `asymptoticAbscissaLaw_of_bddAbove_primes_mod`),
  at the primes off a set of relative density zero
  (`asymptoticAbscissaLaw_of_bddBelow_primes_off_null`), or at the degrees `pᵃqᵇ` of two primes
  (`asymptoticAbscissaLaw_of_bddBelow_twoPrimes`).

At these degree sets the bounds are not known to give RH: their Dirichlet series carry other
`L`-functions or have no power-saving gaps, and at the `pᵃqᵇ` the attained top cannot be dropped
(`TwoFrobeniiNeedAnAttainedTop`). They give the abscissa law, which is what remains without
attainment. Unlike the geometric grids of `RHTower.CrossRouteReceiverBridges`, no resonant steps
are excluded.
-/

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-- **No deepest off-line zero gives the asymptotic abscissa law.** -/
theorem asymptoticAbscissaLaw_of_noDeepest
    (hno : ∀ ρ₀ ∈ zetaZeroConfig.carrier, 1 / 2 < ρ₀.re →
      ∃ ρ ∈ zetaZeroConfig.carrier, ρ₀.re < ρ.re) :
    _root_.RHTower.AsymptoticAbscissaLaw := by
  refine _root_.RHTower.asymptoticAbscissaLaw_of_not_attainedTop ?_
  rintro ⟨β₀, hβ₀, ⟨q₀, hq₀⟩, hmax⟩
  have hρ₀ := _root_.RHTower.CrossRouteReceiverBridges.xiZeroCopy_mem_zetaZeroConfig_carrier q₀
  obtain ⟨ρ, hρ, hgt⟩ := hno _ hρ₀ (by rw [hq₀]; exact hβ₀)
  have hxi :=
    (_root_.RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp
      hρ).1
  obtain ⟨q, hq⟩ := _root_.RHTower.exists_xiZeroCopy_of_xi_eq_zero hxi
  have hle := hmax q
  rw [hq] at hle
  rw [hq₀] at hgt
  linarith

/-- **From below at the primes in a residue class.** -/
theorem asymptoticAbscissaLaw_of_bddBelow_primes_mod {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) {K : ℝ}
    (hK : ∀ p : ℕ, p.Prime → (p : ZMod q) = a →
      -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re) :
    _root_.RHTower.AsymptoticAbscissaLaw :=
  asymptoticAbscissaLaw_of_noDeepest fun _ hρ₀ hoff =>
    exists_re_gt_of_bddBelow_primes_mod ha hK hρ₀ hoff

/-- **From above at the primes in a residue class.** -/
theorem asymptoticAbscissaLaw_of_bddAbove_primes_mod {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) {K : ℝ}
    (hK : ∀ p : ℕ, p.Prime → (p : ZMod q) = a →
      2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re ≤ K) :
    _root_.RHTower.AsymptoticAbscissaLaw :=
  asymptoticAbscissaLaw_of_noDeepest fun _ hρ₀ hoff =>
    exists_re_gt_of_bddAbove_primes_mod ha hK hρ₀ hoff

/-- **From below at almost all primes.** -/
theorem asymptoticAbscissaLaw_of_bddBelow_primes_off_null (E : Set ℕ) [DecidablePred (· ∈ E)]
    (hE : Filter.Tendsto (fun σ => wSum (fun j => primeWeight j - primeOffWeight E j) σ /
      wSum primeWeight σ) (nhdsWithin 1 (Set.Ioi 1)) (nhds 0)) {K : ℝ}
    (hK : ∀ p : ℕ, p.Prime → p ∉ E →
      -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re) :
    _root_.RHTower.AsymptoticAbscissaLaw :=
  asymptoticAbscissaLaw_of_noDeepest fun _ hρ₀ hoff =>
    exists_re_gt_of_bddBelow_primes_off_null E hE hK hρ₀ hoff

/-- **From below at the degrees of two primes.** -/
theorem asymptoticAbscissaLaw_of_bddBelow_twoPrimes {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {K : ℝ}
    (hK : ∀ a b : ℕ, -K ≤
      2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (a * Real.log p + b * Real.log q)).re) :
    _root_.RHTower.AsymptoticAbscissaLaw :=
  asymptoticAbscissaLaw_of_noDeepest fun _ hρ₀ hoff =>
    exists_re_gt_of_bddBelow_twoPrimes hp hq hpq hK hρ₀ hoff

end GaloisForLFunctions.SurfaceOfSpecZ
