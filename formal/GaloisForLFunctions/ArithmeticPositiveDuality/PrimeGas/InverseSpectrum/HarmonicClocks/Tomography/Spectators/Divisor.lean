import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Spectators.Equilibrium
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Calibration.LaurentReadout

/-! # The divisor and leading coefficients of a spectator-deformed return -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology HTGeometry ZeroForcingCalculus
open _root_.RHTower.PrimeCoShift

/-- Trace of the finite spectator at complex inverse temperature. -/
def spectatorFactor (q : Nat.Primes) (g : ℕ) (s : ℂ) : ℂ := 1 + g * heat s (primePNat q)

theorem spectatorFactor_real (q : Nat.Primes) (g : ℕ) (β : TraceTemperature) :
    spectatorFactor q g (β.val:ℂ) = (spectatorWeight β q g : ℂ) := by
  simp only [spectatorFactor,spectatorWeight,heat,thermalWeight,Complex.ofReal_add,Complex.ofReal_one,
    Complex.ofReal_mul,Complex.ofReal_natCast,Complex.ofReal_exp,Complex.ofReal_neg]

theorem spectatorFactor_analytic (q : Nat.Primes) (g : ℕ) (s : ℂ) : AnalyticAt ℂ (spectatorFactor q g) s :=
  analyticAt_const.add (analyticAt_const.mul (analyticAt_id.neg.mul analyticAt_const).cexp)

/-- The logarithmic energy makes every spectator zero simple. -/
theorem spectatorFactor_order (q : Nat.Primes) (g : ℕ) (s : ℂ) :
    meromorphicOrderAt (spectatorFactor q g) s = if spectatorFactor q g s = 0 then 1 else 0 := by
  have ha := spectatorFactor_analytic q g s
  split_ifs with h
  · let L : ℂ := energy (primePNat q)
    have hL : L ≠ 0 := Complex.ofReal_ne_zero.mpr (prime_energy_pos q).ne'
    have hg : (g:ℂ) * heat s (primePNat q) = -1 := by
      change 1 + (g:ℂ)*heat s (primePNat q) = 0 at h
      linear_combination h
    have he := ((hasDerivAt_id s).neg.mul_const L)
    have hd := (((Complex.hasDerivAt_exp _).comp s he).const_mul (g:ℂ)).const_add 1
    have hd' : deriv (spectatorFactor q g) s = L := by
      calc
        _ = (g:ℂ) * (heat s (primePNat q) * (-1 * L)) := hd.deriv
        _ = L := by rw [← mul_assoc,hg]; ring
    rw [ha.meromorphicOrderAt_eq,ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero h (hd' ▸ hL)]
    rfl
  · exact meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero ha h

/-- The combined return extends by dividing the original return by the spectator trace. -/
def continuedSpectatorReturn (p : Nat.Primes) (D : ℕ+) (q : Nat.Primes) (g : ℕ) : ℂ → ℂ :=
  continuedClockReturn p D / spectatorFactor q g

theorem continuedSpectatorReturn_real (β : TraceTemperature) {p q : Nat.Primes}
    (hpq : p ≠ q) (D : ℕ+) (g : ℕ) :
    continuedSpectatorReturn p D q g β.val = (spectatorReturn β p D q g : ℂ) := by
  let χ := fun _ : ℕ+ => (1:Circle)
  rw [continuedSpectatorReturn,Pi.div_apply,continuedClockReturn_real χ,spectatorFactor_real,
    spectatorReturn_eq χ β hpq D,Complex.ofReal_div]

theorem continuedSpectatorReturn_meromorphic (p : Nat.Primes) (D : ℕ+) (q : Nat.Primes) (g : ℕ) :
    Meromorphic (continuedSpectatorReturn p D q g) := fun s =>
  (continuedClockReturn_meromorphic p D s).div (spectatorFactor_analytic q g s).meromorphicAt

/-- Multiplying by the finite trace recovers the base germ. Its isolated zeros do not
affect uniqueness of division on a punctured neighborhood. -/
theorem continuedSpectatorReturn_unique {p q : Nat.Primes} (hpq : p ≠ q) (D : ℕ+) (g : ℕ)
    {F : ℂ → ℂ} (hF : Meromorphic F)
    (hR : ∀ β : TraceTemperature, F β.val = (spectatorReturn β p D q g : ℂ)) (s : ℂ) :
    F =ᶠ[𝓝[≠] s] continuedSpectatorReturn p D q g := by
  let χ := fun _ : ℕ+ => (1:Circle)
  have h := continuedClockReturn_unique χ p D (F := F * spectatorFactor q g)
    (fun z => (hF z).mul (spectatorFactor_analytic q g z).meromorphicAt) (fun β => by
      rw [Pi.mul_apply,hR,spectatorReturn_eq χ β hpq D,Complex.ofReal_div,spectatorFactor_real]
      exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (spectatorWeight_pos β q g).ne')) s
  have hn : meromorphicOrderAt (spectatorFactor q g) s ≠ ⊤ := by
    rw [spectatorFactor_order]; split_ifs <;> simp
  filter_upwards [h,(meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (spectatorFactor_analytic q g s).meromorphicAt).mp hn] with z hz hne
  exact (eq_div_iff hne).mpr hz

/-- Orders add at coincident zeta and spectator zeros, including multiple zeta zeros. -/
theorem continuedSpectatorReturn_order (p : Nat.Primes) (D : ℕ+) (q : Nat.Primes) (g : ℕ)
    {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt (continuedSpectatorReturn p D q g) s =
      -meromorphicOrderAt riemannZeta s - (if spectatorFactor q g s = 0 then 1 else 0) := by
  rw [continuedSpectatorReturn,meromorphicOrderAt_div (continuedClockReturn_meromorphic p D s)
    (spectatorFactor_analytic q g s).meromorphicAt,continuedClockReturn_order p D hs,spectatorFactor_order]

/-- Even the leading coefficients at the additional poles give the same relative clock reading. -/
theorem spectatorCoefficient_excess (p : Nat.Primes) (D : ℕ+) (q : Nat.Primes) (g : ℕ)
    {s : ℂ} (hs : 0 < s.re) :
    meromorphicTrailingCoeffAt (continuedSpectatorReturn p D q g) s /
      meromorphicTrailingCoeffAt (continuedSpectatorReturn p (D+D) q g) s - 1 =
        heat s (primeRayLabel p D.val) := by
  have ha := (spectatorFactor_analytic q g s).meromorphicAt
  have hn : meromorphicOrderAt (spectatorFactor q g) s ≠ ⊤ := by
    rw [spectatorFactor_order]; split_ifs <;> simp
  have hcoeff (E : ℕ+) : meromorphicTrailingCoeffAt (continuedSpectatorReturn p E q g) s =
      meromorphicTrailingCoeffAt (continuedClockReturn p E) s / meromorphicTrailingCoeffAt (spectatorFactor q g) s := by
    rw [continuedSpectatorReturn,div_eq_mul_inv,(continuedClockReturn_meromorphic p E s).meromorphicTrailingCoeffAt_mul ha.inv,
      meromorphicTrailingCoeffAt_inv,div_eq_mul_inv]
  rw [hcoeff,hcoeff,div_div_div_cancel_right₀ (ha.meromorphicTrailingCoeffAt_ne_zero hn)]
  exact returnCoefficient_excess p D hs

#print axioms spectatorFactor_real
#print axioms spectatorFactor_analytic
#print axioms spectatorFactor_order
#print axioms continuedSpectatorReturn_real
#print axioms continuedSpectatorReturn_meromorphic
#print axioms continuedSpectatorReturn_unique
#print axioms continuedSpectatorReturn_order
#print axioms spectatorCoefficient_excess

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
