import GaloisForLFunctions.RHTower.XiHorizontalCollisionGaussHodgePrimeCurrent
import GaloisForLFunctions.RHTower.PrimeLogTripleCluster

/-!
# HC Gauss--Hodge bounded-diagonal route kill

The literal multiplicity-faithful HC current is much larger off the critical line than its
previous nonsummability theorem records. Exact Gauss residue growth, Fisher positivity, and the
virial inequality give a positive linear lower bound in every ordinary-prime label. Hence one
off-line Xi copy makes each containing finite-window current escape to positive infinity along
ordered primes.

Consequently, a bounded diagonal receiver exists for one window exactly when that window's
horizontal-collision charge is zero. Requiring bounded receivers for all windows is exactly RH.
This eliminates every bounded diagonal HC comparison, independently of the receiver's formula;
any surviving HC route must use signed off-diagonal cancellation and an unbounded or singular
landing.
-/

open Complex Set Filter Topology
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Positive linear escape coefficient of one off-line Gauss--Hodge copy. -/
def gaussHodgePrimeLinearEscapeConstant (m : ℕ) (q : XiZeroCopy) : ℝ :=
  Real.log 2 * primeDepthBVWoldXiCenteredRate q.1 ^ (2 : ℕ) *
    ((1 / 2 : ℝ) ^ (2 * m) / (8 * (m : ℝ) ^ (2 : ℕ)))

theorem gaussHodgePrimeLinearEscapeConstant_pos
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy)
    (hq : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    0 < gaussHodgePrimeLinearEscapeConstant m q := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  rw [gaussHodgePrimeLinearEscapeConstant]
  positivity

/-- The exact Gauss residue/Fisher coefficient grows at least linearly in the prime label. -/
theorem gaussResidueFisherLog_linear_lower
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) :
    ((1 / 2 : ℝ) ^ (2 * m) / (8 * (m : ℝ) ^ (2 : ℕ))) * (p : ℝ) ≤
      gaussChannelResidueCurrent m p *
        primeActivationOccupancyFisherDensity p * Real.log (p : ℝ) := by
  let P : ℝ := p
  let M : ℝ := m
  have hp2 : (2 : ℝ) ≤ P := by
    dsimp [P]
    exact_mod_cast p.2.two_le
  have hp0 : 0 < P := lt_of_lt_of_le (by norm_num) hp2
  have hm0 : 0 < M := by
    dsimp [M]
    exact_mod_cast (show 0 < m by omega)
  have hratio : (1 / 2 : ℝ) ≤ (P - 1) / P := by
    rw [le_div_iff₀ hp0]
    linarith
  have hlocal : (1 / 2 : ℝ) ^ (2 * m) ≤ gaussLocalFactorWeight m p := by
    rw [gaussLocalFactorWeight]
    exact pow_le_pow_left₀ (by norm_num) hratio (2 * m)
  have hpowNat : (p : ℕ) ≤ (p : ℕ) ^ m := Nat.le_pow (by omega)
  have hpow : P ≤ P ^ m := by
    dsimp [P]
    exact_mod_cast hpowNat
  have hgap : P / 2 ≤ P ^ m - 1 := by linarith
  have hgap0 : 0 ≤ P / 2 := by positivity
  have hgapSq : (P / 2) ^ (2 : ℕ) ≤ (P ^ m - 1) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hgap0 hgap 2
  have hfisher := (primeActivationOccupancyFisherDensity_bounds p).1
  have hcurrent := gaussChannelResidueCurrent_mul_log hm p
  have hcoef : 0 ≤ 2 / M ^ (2 : ℕ) := by positivity
  have hlocal0 : 0 ≤ gaussLocalFactorWeight m p := by
    exact le_trans (by positivity) hlocal
  have hgapSq0 : 0 ≤ (P ^ m - 1) ^ (2 : ℕ) := sq_nonneg _
  have hmain :
      (2 / M ^ (2 : ℕ)) * (1 / 2 : ℝ) ^ (2 * m) * (P / 2) ^ (2 : ℕ) ≤
        (2 / M ^ (2 : ℕ)) * gaussLocalFactorWeight m p * (P ^ m - 1) ^ (2 : ℕ) := by
    gcongr
  have hbase :
      (2 / M ^ (2 : ℕ)) * (1 / 2 : ℝ) ^ (2 * m) * (P / 2) ^ (2 : ℕ) * (1 / (4 * P)) ≤
        (gaussChannelResidueCurrent m p * Real.log P) *
          primeActivationOccupancyFisherDensity p := by
    calc
      _ ≤ ((2 / M ^ (2 : ℕ)) * gaussLocalFactorWeight m p * (P ^ m - 1) ^ (2 : ℕ)) *
          primeActivationOccupancyFisherDensity p := by
            apply mul_le_mul hmain
            · simpa [P] using hfisher
            · positivity
            · positivity
      _ = _ := by rw [hcurrent]
  calc
    ((1 / 2 : ℝ) ^ (2 * m) / (8 * (m : ℝ) ^ (2 : ℕ))) * (p : ℝ) =
        (2 / M ^ (2 : ℕ)) * (1 / 2 : ℝ) ^ (2 * m) * (P / 2) ^ (2 : ℕ) *
          (1 / (4 * P)) := by
            dsimp [M, P]
            field_simp [hp0.ne']
            ring
    _ ≤ (gaussChannelResidueCurrent m p * Real.log P) *
          primeActivationOccupancyFisherDensity p := hbase
    _ = gaussChannelResidueCurrent m p *
          primeActivationOccupancyFisherDensity p * Real.log (p : ℝ) := by
            dsimp [P]
            ring

/-- Every off-line Gauss--Hodge copy dominates a positive linear prime profile. -/
theorem gaussHodgePrimeLinearEscapeConstant_mul_prime_le
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    gaussHodgePrimeLinearEscapeConstant m q * (p : ℝ) ≤
      gaussHodgeMassCurrent m q p := by
  have hbase := gaussResidueFisherLog_linear_lower hm p
  have hscale :
      0 ≤ Real.log 2 * primeDepthBVWoldXiCenteredRate q.1 ^ (2 : ℕ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hbase hscale
  have hvirial := gaussHodgeMassCurrent_virial_lower hm q p
  rw [gaussHodgePrimeLinearEscapeConstant]
  exact le_trans (le_of_eq (by ring))
    (le_trans hscaled (le_trans (le_of_eq (by ring)) hvirial))

/-- Every off-line copy escapes to positive infinity along ordered prime labels. -/
theorem tendsto_gaussHodgeMassCurrent_nthPrime_atTop_of_rate_ne_zero
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy)
    (hq : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    Tendsto (fun n : ℕ => gaussHodgeMassCurrent m q (nthPrimeSubtype n))
      atTop atTop := by
  have hp : Tendsto (fun n : ℕ => (nthPrimeSubtype n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp nthPrimeSubtype_strictMono.tendsto_atTop
  have hC := gaussHodgePrimeLinearEscapeConstant_pos hm q hq
  have hscaled : Tendsto
      (fun n : ℕ => gaussHodgePrimeLinearEscapeConstant m q *
        (nthPrimeSubtype n : ℝ)) atTop atTop :=
    hp.const_mul_atTop hC
  exact Filter.tendsto_atTop_mono
    (fun n => gaussHodgePrimeLinearEscapeConstant_mul_prime_le hm q
      (nthPrimeSubtype n)) hscaled

/-- A bounded diagonal receiver for one HC window. The receiver may depend arbitrarily on every
prime label; only one finite upper ceiling is required. -/
def HCHasBoundedDiagonalReceiver (m : ℕ) (T : ℝ) : Prop :=
  ∃ b : Nat.Primes → ℝ, (∃ C : ℝ, ∀ p, b p ≤ C) ∧
    ∀ p, xiHorizontalCollisionGaussHodgePrimeCurrent m T p ≤ b p

theorem xiHorizontalCollisionGaussHodgePrimeCurrent_eq_zero_of_charge_eq_zero
    {m : ℕ} (hm : 1 ≤ m) (T : ℝ)
    (hcharge : xiHorizontalCollisionCharge T = 0) :
    xiHorizontalCollisionGaussHodgePrimeCurrent m T = 0 := by
  have hline :=
    (xiHorizontalCollisionCharge_eq_zero_iff_stripSupport_onLine T).1 hcharge
  funext p
  rw [xiHorizontalCollisionGaussHodgePrimeCurrent,
    xiFiniteGaussHodgePrimeCurrent]
  apply Finset.sum_eq_zero
  intro q hq
  apply (gaussHodgeMassCurrent_eq_zero_iff hm q p).2
  exact hline q.1 (mem_xiFiniteMultiplicityCopyPacket.mp hq)

/-- Nonzero horizontal collision charge forces the complete finite-window current to escape. -/
theorem tendsto_xiHorizontalCollisionGaussHodgePrimeCurrent_nthPrime_atTop_of_charge_ne_zero
    {m : ℕ} (hm : 1 ≤ m) (T : ℝ)
    (hcharge : xiHorizontalCollisionCharge T ≠ 0) :
    Tendsto
      (fun n : ℕ => xiHorizontalCollisionGaussHodgePrimeCurrent m T
        (nthPrimeSubtype n)) atTop atTop := by
  have hnotall :
      ¬ ∀ rho ∈ xiStripWindowDivisorSupportFinset T,
        (rho : ℂ).re = 1 / 2 := by
    intro hline
    exact hcharge
      ((xiHorizontalCollisionCharge_eq_zero_iff_stripSupport_onLine T).2 hline)
  push Not at hnotall
  obtain ⟨rho, hrho, hoff⟩ := hnotall
  let q : XiZeroCopy := xiFirstZeroCopy rho
  have hq : q ∈ xiFiniteMultiplicityCopyPacket
      (xiStripWindowDivisorSupportFinset T) := by
    rw [mem_xiFiniteMultiplicityCopyPacket]
    exact hrho
  have hrate : primeDepthBVWoldXiCenteredRate q.1 ≠ 0 := by
    rw [primeDepthBVWoldXiCenteredRate]
    change 2 * (rho : ℂ).re - 1 ≠ 0
    intro hzero
    apply hoff
    linarith
  have hcopy := tendsto_gaussHodgeMassCurrent_nthPrime_atTop_of_rate_ne_zero
    hm q hrate
  have hterm : ∀ p : Nat.Primes,
      gaussHodgeMassCurrent m q p ≤
        xiHorizontalCollisionGaussHodgePrimeCurrent m T p := by
    intro p
    rw [xiHorizontalCollisionGaussHodgePrimeCurrent,
      xiFiniteGaussHodgePrimeCurrent]
    exact Finset.single_le_sum
      (fun q' _ => gaussHodgeMassCurrent_nonneg hm q' p) hq
  exact Filter.tendsto_atTop_mono (fun n => hterm (nthPrimeSubtype n)) hcopy

/-- **Bounded-diagonal HC classification.** A finite-window HC current has any bounded diagonal
receiver exactly when its horizontal collision charge vanishes. -/
theorem hcHasBoundedDiagonalReceiver_iff_charge_eq_zero
    {m : ℕ} (hm : 1 ≤ m) (T : ℝ) :
    HCHasBoundedDiagonalReceiver m T ↔ xiHorizontalCollisionCharge T = 0 := by
  constructor
  · rintro ⟨b, ⟨C, hC⟩, hdom⟩
    by_contra hcharge
    have htop :=
      tendsto_xiHorizontalCollisionGaussHodgePrimeCurrent_nthPrime_atTop_of_charge_ne_zero
        hm T hcharge
    rcases (htop.eventually_gt_atTop C).exists with ⟨n, hn⟩
    linarith [hdom (nthPrimeSubtype n), hC (nthPrimeSubtype n)]
  · intro hcharge
    refine ⟨0, ⟨0, fun p => le_rfl⟩, ?_⟩
    rw [xiHorizontalCollisionGaussHodgePrimeCurrent_eq_zero_of_charge_eq_zero
      hm T hcharge]
    intro p
    exact le_rfl

/-- **HC bounded-diagonal route kill.** Bounded diagonal reception of every finite horizontal
collision window is equivalent to RH. -/
theorem riemannHypothesis_iff_forall_hcHasBoundedDiagonalReceiver
    {m : ℕ} (hm : 1 ≤ m) :
    RiemannHypothesis ↔ ∀ T : ℝ, HCHasBoundedDiagonalReceiver m T := by
  rw [riemannHypothesis_iff_forall_horizontalCollisionCharge_eq_zero]
  exact forall_congr' fun T =>
    (hcHasBoundedDiagonalReceiver_iff_charge_eq_zero hm T).symm

/-- Hypothesis-free grade-one endpoint: bounded diagonal reception of every HC window is exactly
RH. -/
theorem riemannHypothesis_iff_forall_hcHasBoundedDiagonalReceiver_one :
    RiemannHypothesis ↔ ∀ T : ℝ, HCHasBoundedDiagonalReceiver 1 T :=
  riemannHypothesis_iff_forall_hcHasBoundedDiagonalReceiver (by norm_num)

end

end RHTower
