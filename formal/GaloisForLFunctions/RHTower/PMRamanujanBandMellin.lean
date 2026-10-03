import GaloisForLFunctions.RHTower.PMRamanujanPeriodDiagonal
import GaloisForLFunctions.RHTower.NymanMellinGaugeCollapse

/-!
# Literal Mellin symbols of complete Ramanujan bands

The actual reciprocal primitive is a finite signed Nyman combination.
Its Mellin transform retains the full divisor symbol, and finite natural
bands retain every actual coefficient. These identities are the source
input for the moving-band spectral analysis; no Euler-limit interchange,
Hilbert escape theorem, small-damping energy ceiling or RH is asserted.
-/

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower
open GaloisForLFunctions.NymanMellin

/-- The literal primitive in the reciprocal spatial coordinate. -/
def pmRamanujanPrimitiveSource (q : ℕ) (t : ℝ) : ℂ :=
  pmRamanujanPrimitive q ⌊1 / t⌋₊

/-- The complete finite divisor symbol, before any infinite Euler rearrangement. -/
def pmRamanujanMellinSymbol (q : ℕ) (s : ℂ) : ℂ :=
  ∑ x ∈ q.divisorsAntidiagonal, (moebius x.2 : ℂ) * (x.1 : ℂ) ^ (1-s)

private theorem pmb_floor_fract {x : ℝ} (hx : 0 ≤ x) (d : ℕ) :
    ((⌊x⌋₊ / d : ℕ) : ℂ) =
      (((x / (d : ℝ) - Int.fract (x / (d : ℝ))) : ℝ) : ℂ) := by
  rw [Int.fract, sub_sub_cancel,
    ← Int.natCast_floor_eq_floor (div_nonneg hx (Nat.cast_nonneg d)),
    Int.cast_natCast, Nat.floor_div_natCast]
  norm_cast

theorem pmRamanujanPrimitiveSource_eq_nyman {q : ℕ} (hq : 1 < q)
    {t : ℝ} (ht : 0 < t) :
    pmRamanujanPrimitiveSource q t =
      ∑ x ∈ q.divisorsAntidiagonal,
        (-(x.1 : ℂ) * (moebius x.2 : ℂ)) * nymanGen (x.1 : ℝ) t := by
  rw [pmRamanujanPrimitiveSource, pmRamanujanPrimitive_eq_floor]
  have ht0 : 0 ≤ 1 / t := (one_div_pos.mpr ht).le
  simp_rw [pmb_floor_fract ht0, Complex.ofReal_sub, Complex.ofReal_div,
    Complex.ofReal_natCast, Complex.ofReal_one, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hlin : (∑ x ∈ q.divisorsAntidiagonal,
      (x.1 : ℂ) * (moebius x.2 : ℂ) * (((1 / t : ℝ) : ℂ) / (x.1 : ℂ))) = 0 := by
    calc
      _ = (((1 / t : ℝ) : ℂ)) *
          ∑ x ∈ q.divisorsAntidiagonal, (moebius x.2 : ℂ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        have hd : (x.1 : ℂ) ≠ 0 := by
          exact_mod_cast (Nat.pos_of_mem_divisors
            (Nat.fst_mem_divisors_of_mem_antidiagonal hx)).ne'
        field_simp
      _ = 0 := by rw [pm_mobius_antidiagonal_sum]; simp [ne_of_gt hq]
  simp only [Complex.ofReal_div, Complex.ofReal_one] at hlin
  rw [hlin, zero_sub, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have he : (1 / t) / (x.1 : ℝ) = 1 / ((x.1 : ℝ) * t) := by ring
  rw [he, nymanGen]
  ring

private theorem pmb_nyman_integrable {q : ℕ} {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (x : ℕ × ℕ)
    (hx : x ∈ q.divisorsAntidiagonal) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s-1) •
      ((-(x.1 : ℂ) * (moebius x.2 : ℂ)) * nymanGen (x.1 : ℝ) t)) (Ioi 0) := by
  apply mellinConvergent_const_mul
  apply mellinConvergent_nymanGen hs0 hs1
  exact_mod_cast Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)

theorem hasMellin_pmRamanujanPrimitiveSource {q : ℕ} (hq : 1 < q)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    HasMellin (pmRamanujanPrimitiveSource q) s
      (riemannZeta s / s * pmRamanujanMellinSymbol q s) := by
  have hsum : IntegrableOn (fun t : ℝ =>
      ∑ x ∈ q.divisorsAntidiagonal, (t : ℂ) ^ (s-1) •
        ((-(x.1 : ℂ) * (moebius x.2 : ℂ)) * nymanGen (x.1 : ℝ) t)) (Ioi 0) :=
    integrable_finsetSum q.divisorsAntidiagonal (pmb_nyman_integrable hs0 hs1)
  have he (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      (t : ℂ) ^ (s-1) • pmRamanujanPrimitiveSource q t =
        ∑ x ∈ q.divisorsAntidiagonal, (t : ℂ) ^ (s-1) •
          ((-(x.1 : ℂ) * (moebius x.2 : ℂ)) * nymanGen (x.1 : ℝ) t) := by
    rw [pmRamanujanPrimitiveSource_eq_nyman hq ht, Finset.smul_sum]
  constructor
  · exact hsum.congr_fun (fun t ht => (he t ht).symm) measurableSet_Ioi
  · rw [mellin, setIntegral_congr_fun measurableSet_Ioi he,
      integral_finsetSum _ (pmb_nyman_integrable hs0 hs1)]
    change (∑ x ∈ q.divisorsAntidiagonal,
      mellin (fun t => (-(x.1 : ℂ) * (moebius x.2 : ℂ)) *
        nymanGen (x.1 : ℝ) t) s) = _
    rw [pmRamanujanMellinSymbol, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have hd : 0 < (x.1 : ℝ) := by
      exact_mod_cast Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)
    have hd0 : (x.1 : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [mellin_const_mul, mellin_nymanGen hs0 hs1 hd,
      sub_eq_add_neg, Complex.cpow_add _ _ hd0, Complex.cpow_one]
    push_cast
    ring

/-- The literal complete natural band in the reciprocal spatial coordinate. -/
def pmRamanujanDenominatorBandSource (ε : ℝ) (X Y : ℕ) (t : ℝ) : ℂ :=
  pmRamanujanDenominatorBand ε X Y ⌊1/t⌋₊

/-- The signed band transform keeps every denominator and cofactor. -/
theorem hasMellin_pmRamanujanDenominatorBandSource (ε : ℝ) {X Y : ℕ}
    (hX : 1 ≤ X) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    HasMellin (pmRamanujanDenominatorBandSource ε X Y) s
      (riemannZeta s / s * ∑ q ∈ Finset.Ioc X Y,
        pmPowerDampedRamanujanWeight ε q * pmRamanujanMellinSymbol q s) := by
  have hq (q : ℕ) (hq : q ∈ Finset.Ioc X Y) : 1 < q :=
    lt_of_le_of_lt hX (Finset.mem_Ioc.mp hq).1
  have hi (q : ℕ) (hq' : q ∈ Finset.Ioc X Y) :
      IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s-1) •
        (pmPowerDampedRamanujanWeight ε q * pmRamanujanPrimitiveSource q t)) (Ioi 0) :=
    mellinConvergent_const_mul (hasMellin_pmRamanujanPrimitiveSource (hq q hq') hs0 hs1).1
  have he (t : ℝ) : (t : ℂ) ^ (s-1) • pmRamanujanDenominatorBandSource ε X Y t =
      ∑ q ∈ Finset.Ioc X Y, (t : ℂ) ^ (s-1) •
        (pmPowerDampedRamanujanWeight ε q * pmRamanujanPrimitiveSource q t) := by
    simp only [pmRamanujanDenominatorBandSource, pmRamanujanDenominatorBand,
      pmRamanujanPrimitiveSource, Finset.smul_sum]
  have hsum : IntegrableOn (fun t : ℝ =>
      ∑ q ∈ Finset.Ioc X Y, (t : ℂ) ^ (s-1) •
        (pmPowerDampedRamanujanWeight ε q * pmRamanujanPrimitiveSource q t)) (Ioi 0) :=
    integrable_finsetSum _ hi
  constructor
  · exact hsum.congr_fun (fun t _ => (he t).symm) measurableSet_Ioi
  · rw [mellin, setIntegral_congr_fun measurableSet_Ioi (fun t _ => he t),
      integral_finsetSum _ hi]
    change (∑ q ∈ Finset.Ioc X Y,
      mellin (fun t => pmPowerDampedRamanujanWeight ε q * pmRamanujanPrimitiveSource q t) s) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq'
    rw [mellin_const_mul, (hasMellin_pmRamanujanPrimitiveSource (hq q hq') hs0 hs1).2]
    ring

theorem pmRamanujanMellinSymbol_prime {p : ℕ} (hp : p.Prime) (s : ℂ) :
    pmRamanujanMellinSymbol p s = (p : ℂ) ^ (1-s)-1 := by
  rw [pmRamanujanMellinSymbol,
    Nat.sum_divisorsAntidiagonal (fun d m => (moebius m : ℂ) * (d : ℂ) ^ (1-s)),
    hp.divisors]
  simp [hp.ne_one.symm, Nat.div_self hp.pos, ArithmeticFunction.moebius_apply_prime hp]
  ring

end RHTower
