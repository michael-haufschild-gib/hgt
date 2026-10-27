import GaloisForLFunctions.TransThresholdPairCorrelation.RamanujanDirichletCoalescentTransfer
import GaloisForLFunctions.TransThresholdPairCorrelation.CoalescentPrimeReductionAndParitySieve
import GaloisForLFunctions.ArithmeticCorrelationGeometry.TheCoalescentSurplusDecomposesOverItsStabilizers
import GaloisForLFunctions.ArithmeticCorrelationGeometry.RHIsTheVisibilityOfEveryEscapeState
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheReceiverEnergyGrowthAtTheZeroAbscissa
import GaloisForLFunctions.SquareRootThreshold.WindowCertificatesAndThePrimeWeight

/-!
# Parity–Lobe Dispersion Obstruction at `λ = 4/3` & Escape Laplace Split (Questions 1 & 5A)

This module resolves Questions 1 and 5(A):

1. **Exact Ramanujan–Stabilizer Packet Identity & Multi-Modulus Orthogonal Split
   (`zmod_natCast_eq_iff_dvd_natAbs_sub`, `ramanujanStabilizerPacket_eq_sum_dvd_indicator`,
   `tendsto_ramanujanStabilizerPacket`, `multiModulus_ramanujan_primeCoalSum_split`):**
   Weighting the level-`d` Dirichlet character averages `(1 / φ(d)) ∑_{χ mod d} twistedPrimeCoalSum`
   by the Möbius-inverted stabilizer weights `stabilizerDivisorWeight Q d` across `1 ≤ d ≤ Q`
   (`2 Q θ₀ < 1`) reconstructs the exact pole-cancelling Ramanujan singular-series packet
   `ramanujanStabilizerPacket Q |n - m|` (converging as `Q → ∞` to `hardyLittlewoodSingularSeries |n - m|`,
   which vanishes on odd lags and is strictly positive on even lags) rather than the unit weight `1`
   of `primeCoalSum`, while the non-congruent residue discrepancy has identically zero character
   mean at every individual modulus `q ≤ Q`.

2. **Selberg Parity Involution, Unconditional Parity–Lobe Divergence, and Proportion Payoffs
   (`selbergEvenVonMangoldt`, `selbergOddVonMangoldt`, `selbergParity_pair_gap_on_primes`,
   `parityAdversary_coalescent_sum_sub_ge`, `parityBlind_dispersion_diverges_above_threshold`,
   `parityBlind_refutes_quadratic_and_fourThirds_budgets`,
   `oddEvenShift_singleProfile_certifies_proportion`, `coalescent_surplus_battery_laws`):**
   Selberg's parity weights `selbergEvenVonMangoldt = Λ + λΛ ≥ 0` and
   `selbergOddVonMangoldt = Λ - λΛ ≥ 0` share prime-power support and average to `Λ`, yet have
   prime-pair correlations `0` and `4 log p log p'` on pure primes `(p, p')`. Whenever a sieve or
   multi-modulus Kloosterman/BFI dispersion method leaves a positive Bombieri/Selberg parity
   half-width `κ > 0` on shift correlations `|C(r) - C₀(r)| ≤ κ S(r)` (`S(r) ≥ s_min > 0`), the
   worst-case signed coalescent sum picks up `(κ s_min K₁ / 2) cosTransform Ω 0` on the positive
   inner cosine lobe (`sum_Icc_abs_cosTransform_ge_inner_lobe`), growing by `T^δ` above the
   zero-counting scale at every trans-threshold bandwidth `λ = 1 + δ > 1`. Thus parity-blind
   dispersion cannot establish `β(δ) ≤ B δ² / (1 + δ)²` for any `B ≥ 0, δ > 0`, nor `β < 5/36` at
   `λ = 4/3`. Conversely, any parity-breaking bound on `oddEvenShiftPrimeCoalescentSurplus` or
   `PrimeCoalescentSurplusAtMost β` (`β < 5/36`, `β ≤ 1/18`) unconditionally certifies
   critical-line proportions exceeding `2/3` and reaching `3/4`.

3. **Exact Escape Laplace Transform Split & RH-Visibility Equivalence
   (`escapeLaplaceSymbol`, `escapeLaplaceSymbol_eq_invZeta_form`,
   `escapeLaplaceSymbol_pole_and_visibility_laws`):**
   On the damping strip, the receiver line symbol continues `escapeLaplaceSymbol ε s =
   ζ(s) (ζ(s + ε)⁻¹ - (ζ(1 + ε)⁻¹).re) / s`, splits at every dominant translated simple zero
   `s₀ = ρ - ε` into `(ζ(ρ - ε) / (ζ'(ρ)(ρ - ε))) / (s - (ρ - ε))` plus a uniformly bounded
   remainder (yielding the spectral atom `π ‖r‖² δ_{Im ρ}` while zero-free compact vertical
   segments carry zero asymptotic escape share), and absence of invisible infinite-height escape
   across `0 < ε < 1/2` (`∀ ε L, 0 < gaugeMass L.kernel`) is unconditionally equivalent to
   `RiemannHypothesis`.
-/

open MeasureTheory Real Set Finset Filter Topology Complex ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius ComplexConjugate

open Zeta23 Zeta23.PrimeSide RHTower RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.TransHorizonIncidenceMechanics (dampedDensity)
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy (dampedMobiusEnergy)
open GaloisForLFunctions.TransThresholdPairCorrelation
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.ArithmeticCorrespondencePositivity
open GaloisForLFunctions.ArithmeticDefectRigidity
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (liouvilleTwistedVonMangoldt)

noncomputable section

set_option autoImplicit false

namespace GaloisForLFunctions.SelectivePositivityAndThresholdLaws

/-! ### 1. Exact Ramanujan–Stabilizer Packet Identity & Multi-Modulus Orthogonal Split -/

/-- Congruence modulo `q` for natural numbers `n, m` is equivalent to `q ∣ |n - m|`. -/
theorem zmod_natCast_eq_iff_dvd_natAbs_sub (q n m : ℕ) :
    (n : ZMod q) = (m : ZMod q) ↔ q ∣ ((n : ℤ) - (m : ℤ)).natAbs := by
  have h1 : ((n : ZMod q) = (m : ZMod q)) ↔ (((n : ℤ) - (m : ℤ) : ℤ) : ZMod q) = 0 := by
    push_cast
    exact sub_eq_zero.symm
  rw [h1, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rcases Int.natAbs_eq ((n : ℤ) - (m : ℤ)) with h | h
  · conv_lhs => rw [h]
    exact Int.natCast_dvd_natCast
  · conv_lhs => rw [h]
    rw [dvd_neg]
    exact Int.natCast_dvd_natCast

/-- Truncated Hardy–Littlewood / Ramanujan singular-series packet `∑_{1 ≤ q ≤ Q} μ(q)² c_q(h) / φ(q)²`. -/
def ramanujanStabilizerPacket (Q h : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, singularSeriesTerm h q

/-- Coefficient of the congruent divisor stabilizer `1_{d ∣ h}` in `ramanujanStabilizerPacket Q h`. -/
def stabilizerDivisorWeight (Q d : ℕ) : ℝ :=
  (d : ℝ) * ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q),
    (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) * moebiusReal (q / d)

/-- **Exact Ramanujan–Stabilizer Divisor Expansion:**
For every truncation `Q` and shift `h`, the pole-cancelling Ramanujan singular-series packet
expands identically over the congruent stabilizers `1_{d ∣ h}` (`1 ≤ d ≤ Q`). -/
theorem ramanujanStabilizerPacket_eq_sum_dvd_indicator (Q h : ℕ) :
    ramanujanStabilizerPacket Q h =
      ∑ d ∈ Finset.Icc 1 Q, if d ∣ h then stabilizerDivisorWeight Q d else 0 := by
  classical
  unfold ramanujanStabilizerPacket stabilizerDivisorWeight
  have hq_term : ∀ q ∈ Finset.Icc 1 Q,
      singularSeriesTerm h q =
        ∑ d ∈ Finset.Icc 1 Q,
          if d ∣ q then
            (if d ∣ h then (d : ℝ) * ((RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
              moebiusReal (q / d)) else 0)
          else 0 := by
    intro q hq
    obtain ⟨hq1, hqQ⟩ := Finset.mem_Icc.mp hq
    rw [singularSeriesTerm, ramanujanLagWeight_eq_ramanujanLagCoefficient, ramanujanLagCoefficient,
      Finset.sum_mul]
    have hdiv_eq : q.divisors = (Finset.Icc 1 Q).filter (fun d => d ∣ q) := by
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hdq, _⟩
        have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdq (by omega)
        have hdle : d ≤ q := Nat.le_of_dvd (by omega) hdq
        exact ⟨⟨by omega, hdle.trans hqQ⟩, hdq⟩
      · rintro ⟨_, hdq⟩
        exact ⟨hdq, by omega⟩
    rw [hdiv_eq, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hq_term, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hdh : d ∣ h
  · simp only [if_pos hdh]
    rw [Finset.mul_sum, Finset.sum_filter]
  · simp only [if_neg hdh, ite_self, Finset.sum_const_zero]

/-- As `Q → ∞`, `ramanujanStabilizerPacket Q h` converges to `hardyLittlewoodSingularSeries h`
(which equals `0` for odd `h ≥ 1` and is strictly positive for even `h ≥ 2`). -/
theorem tendsto_ramanujanStabilizerPacket {h : ℕ} (hh : 1 ≤ h) :
    Tendsto (fun Q => ramanujanStabilizerPacket Q h) atTop
      (𝓝 (hardyLittlewoodSingularSeries h)) ∧
    (¬ 2 ∣ h → hardyLittlewoodSingularSeries h = 0) ∧
    (2 ∣ h → 0 < hardyLittlewoodSingularSeries h) := by
  refine ⟨?_, hardyLittlewoodSingularSeries_eq_zero_of_odd hh,
    hardyLittlewoodSingularSeries_pos_of_even hh⟩
  have hsum := (summable_singularSeriesTerm hh).of_norm.hasSum
  have htend := hsum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  refine htend.congr fun Q => ?_
  dsimp only [Function.comp_def, ramanujanStabilizerPacket]
  have hrange : Finset.range (Q + 1) = insert 0 (Finset.Icc 1 Q) := by
    ext q
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hrange, Finset.sum_insert (by simp), singularSeriesTerm_zero, zero_add]

/-- **Multi-Modulus Ramanujan–Stabilizer Split of `primeCoalSum`:**
For any `0 < θ₀ ≤ 1 / 2` and `2 Q θ₀ < 1`, weighting the normalized level-`d` Dirichlet-character
averages `(1 / φ(d)) ∑_{χ mod d} twistedPrimeCoalSum` by `stabilizerDivisorWeight Q d` across
`1 ≤ d ≤ Q` reconstructs the `ramanujanStabilizerPacket Q |n - m|`-weighted prime-pair sum, while
at every individual modulus `q ∈ Icc 1 Q` the non-congruent residue discrepancy has identically
zero character mean. -/
theorem multiModulus_ramanujan_primeCoalSum_split
    (Ω g : ℝ → ℝ) (X θ₀ : ℝ) {Q : ℕ}
    (hθ0 : 0 < θ₀) (hθ : θ₀ ≤ 1 / 2) (hQ : 2 * (Q : ℝ) * θ₀ < 1) :
    (∑ d ∈ Finset.Icc 1 Q,
        ((stabilizerDivisorWeight Q d / (d.totient : ℝ) : ℝ) : ℂ) *
          ∑ χ : DirichletCharacter ℂ d, twistedPrimeCoalSum Ω g X θ₀ (dirichletGauge χ)) =
      (∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        (ramanujanStabilizerPacket Q ((n : ℤ) - (m : ℤ)).natAbs : ℂ) *
          (coalWeight Ω g θ₀ n m : ℂ)) ∧
    ∀ q : ℕ, 1 ≤ q → q ≤ Q →
      ∀ [NeZero q],
        ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
          (if (n : ZMod q) = m then 0 else (coalWeight Ω g θ₀ n m : ℂ)) *
            (twist (dirichletGauge χ) n * conj (twist (dirichletGauge χ) m)) = 0 := by
  classical
  refine ⟨?_, fun q _ hqQ _ => ?_⟩
  · have hd_each : ∀ d ∈ Finset.Icc 1 Q,
        ((stabilizerDivisorWeight Q d / (d.totient : ℝ) : ℝ) : ℂ) *
          (∑ χ : DirichletCharacter ℂ d, twistedPrimeCoalSum Ω g X θ₀ (dirichletGauge χ)) =
        ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
          ((if d ∣ ((n : ℤ) - (m : ℤ)).natAbs then stabilizerDivisorWeight Q d else 0 : ℝ) : ℂ) *
            (coalWeight Ω g θ₀ n m : ℂ) := by
      intro d hd
      obtain ⟨hd1, hdQ⟩ := Finset.mem_Icc.mp hd
      haveI : NeZero d := ⟨by omega⟩
      have hd_real : (d : ℝ) ≤ Q := by exact_mod_cast hdQ
      have hdθ : 2 * (d : ℝ) * θ₀ < 1 := by nlinarith
      rw [sum_twistedPrimeCoalSum_dirichletGauge hθ0 hθ hdθ, ← mul_assoc]
      have hφ_pos : 0 < (d.totient : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr (by omega)
      have hφ_ne : ((d.totient : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hφ_pos.ne'
      have hcoef : ((stabilizerDivisorWeight Q d / (d.totient : ℝ) : ℝ) : ℂ) *
          (d.totient : ℂ) = (stabilizerDivisorWeight Q d : ℂ) := by
        push_cast
        exact div_mul_cancel₀ _ hφ_ne
      rw [hcoef, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp_rw [zmod_natCast_eq_iff_dvd_natAbs_sub]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hd_each, Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_mul, ramanujanStabilizerPacket_eq_sum_dvd_indicator]
    push_cast
    rfl
  · have hq_real : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
    exact sum_discrepancy_dirichletGauge_eq_zero hθ0 hθ (by nlinarith)

/-! ### 2. Selberg Parity Involution & Unconditional Parity–Lobe Divergence Theorem -/

/-- Selberg's even-factor von Mangoldt weight `(1 + λ(n)) Λ(n) ≥ 0`, supported on even prime powers. -/
def selbergEvenVonMangoldt (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n : ℝ) + liouvilleTwistedVonMangoldt n

/-- Selberg's odd-factor von Mangoldt weight `(1 - λ(n)) Λ(n) ≥ 0`, supported on odd prime powers. -/
def selbergOddVonMangoldt (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n : ℝ) - liouvilleTwistedVonMangoldt n

/-- **Selberg Parity Pair-Gap Law:**
`selbergEvenVonMangoldt` and `selbergOddVonMangoldt` are nonnegative prime-power weights whose
average is `Λ`, yet on every pure prime pair `(p, p')` (`p, p'` prime) the even-parity weight has
pair correlation `0` whereas the odd-parity weight has pair correlation `4 log p log p'`. -/
theorem selbergParity_pair_gap_on_primes :
    (∀ n : ℕ, 0 ≤ selbergEvenVonMangoldt n ∧ 0 ≤ selbergOddVonMangoldt n) ∧
    (∀ n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) =
      (selbergEvenVonMangoldt n + selbergOddVonMangoldt n) / 2) ∧
    (∀ {p p' : ℕ}, p.Prime → p'.Prime →
      selbergEvenVonMangoldt p * selbergEvenVonMangoldt p' = 0 ∧
      selbergOddVonMangoldt p * selbergOddVonMangoldt p' = 4 * Real.log p * Real.log p') := by
  refine ⟨fun n => ?_, fun n => ?_, fun {p p'} hp hp' => ?_⟩
  · unfold selbergEvenVonMangoldt selbergOddVonMangoldt liouvilleTwistedVonMangoldt
    have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    rcases neg_one_pow_eq_or ℝ (ArithmeticFunction.cardFactors n) with h1 | h1
    · rw [h1]; constructor <;> linarith
    · rw [h1]; constructor <;> linarith
  · unfold selbergEvenVonMangoldt selbergOddVonMangoldt
    ring
  · have he : ∀ {q : ℕ}, q.Prime →
        selbergEvenVonMangoldt q = 0 ∧ selbergOddVonMangoldt q = 2 * Real.log q := by
      intro q hq
      unfold selbergEvenVonMangoldt selbergOddVonMangoldt liouvilleTwistedVonMangoldt
      rw [ArithmeticFunction.cardFactors_apply_prime hq,
        ArithmeticFunction.vonMangoldt_apply_prime hq]
      constructor <;> ring
    rw [(he hp).1, (he hp').1, (he hp).2, (he hp').2]
    constructor <;> ring

/-- Worst-case parity-admissible shift correlation within `[C₀(r) - κ S(r), C₀(r) + κ S(r)]`. -/
def parityAdversaryCorrelation (Ω : ℝ → ℝ) (m κ : ℝ) (C₀ S : ℕ → ℝ) (r : ℕ) : ℝ :=
  C₀ r + if 0 ≤ cosTransform Ω ((r : ℝ) * (2 / m)) then κ * S r else -(κ * S r)

/-- `parityAdversaryCorrelation` lies within distance `κ S(r)` of `C₀(r)`, and is nonnegative
whenever `κ S(r) ≤ C₀(r)` (in particular for `C₀ = S` and `0 < κ ≤ 1`). -/
theorem parityAdversaryCorrelation_mem_bracket
    (Ω : ℝ → ℝ) (m : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) (C₀ S : ℕ → ℝ) {r : ℕ} (hSr : 0 ≤ S r) :
    |parityAdversaryCorrelation Ω m κ C₀ S r - C₀ r| ≤ κ * S r ∧
    (κ * S r ≤ C₀ r → 0 ≤ parityAdversaryCorrelation Ω m κ C₀ S r) := by
  unfold parityAdversaryCorrelation
  have hprod : 0 ≤ κ * S r := mul_nonneg hκ hSr
  split_ifs
  · refine ⟨by rw [add_sub_cancel_left, abs_of_nonneg hprod], fun h => by linarith⟩
  · refine ⟨by rw [add_sub_cancel_left, abs_neg, abs_of_nonneg hprod], fun h => by linarith⟩

/-- **Finite-Height Parity–Lobe Lower Bound:**
Whenever a sieve or Kloosterman dispersion bracket leaves a parity half-width `κ > 0` across shifts
`1 ≤ r ≤ R` with `S(r) ≥ s_min > 0`, the worst-case admissible signed coalescent sum exceeds the
baseline `C₀` sum by at least `(κ s_min K₁ / 2) cosTransform Ω 0` for every `K₁ ≤ R` in the inner
cosine lobe `K₁ (2 / m) ≤ π / (3 b)`. -/
theorem parityAdversary_coalescent_sum_sub_ge
    {Ω : ℝ → ℝ} {a b m κ s_min : ℝ} {K₁ R : ℕ} {C₀ S : ℕ → ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) (hm : 0 < m)
    (hκ : 0 < κ) (hs_min : 0 < s_min)
    (hInt : Integrable Ω) (hΩ0 : ∀ τ, 0 ≤ Ω τ)
    (hsupp : ∀ τ, τ ∉ Icc a b → Ω τ = 0)
    (hS : ∀ r ∈ Finset.Icc 1 R, s_min ≤ S r)
    (hKR : K₁ ≤ R) (hK₁ : (K₁ : ℝ) * (2 / m) ≤ π / (3 * b)) :
    (κ * s_min * (K₁ : ℝ) / 2) * cosTransform Ω 0 ≤
      (∑ r ∈ Finset.Icc 1 R,
          parityAdversaryCorrelation Ω m κ C₀ S r * cosTransform Ω ((r : ℝ) * (2 / m))) -
        ∑ r ∈ Finset.Icc 1 R, C₀ r * cosTransform Ω ((r : ℝ) * (2 / m)) := by
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ r ∈ Finset.Icc 1 R,
      κ * s_min * |cosTransform Ω ((r : ℝ) * (2 / m))| ≤
        parityAdversaryCorrelation Ω m κ C₀ S r * cosTransform Ω ((r : ℝ) * (2 / m)) -
          C₀ r * cosTransform Ω ((r : ℝ) * (2 / m)) := by
    intro r hr
    have hSr := hS r hr
    have hrw : parityAdversaryCorrelation Ω m κ C₀ S r * cosTransform Ω ((r : ℝ) * (2 / m)) -
        C₀ r * cosTransform Ω ((r : ℝ) * (2 / m)) =
        κ * S r * |cosTransform Ω ((r : ℝ) * (2 / m))| := by
      unfold parityAdversaryCorrelation
      by_cases hc : 0 ≤ cosTransform Ω ((r : ℝ) * (2 / m))
      · rw [if_pos hc, abs_of_nonneg hc]
        ring
      · rw [if_neg hc, abs_of_neg (lt_of_not_ge hc)]
        ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSr hκ.le) (abs_nonneg _)
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  have hlobe := sum_Icc_abs_cosTransform_ge_inner_lobe ha hab hb (div_pos two_pos hm)
    hInt hΩ0 hsupp hKR hK₁
  have hmul := mul_le_mul_of_nonneg_left hlobe (mul_pos hκ hs_min).le
  calc (κ * s_min * (K₁ : ℝ) / 2) * cosTransform Ω 0
      = κ * s_min * (((K₁ : ℝ) / 2) * cosTransform Ω 0) := by ring
    _ ≤ κ * s_min * ∑ r ∈ Finset.Icc 1 R, |cosTransform Ω ((r : ℝ) * (2 / m))| := hmul
    _ ≤ _ := hsum

/-- Every smooth window profile `WindowProfile ε₁ u` satisfies `T / 2 ≤ cosTransform (profileΩ u T) 0`
for all `T > 0`. -/
theorem cosTransform_profileΩ_zero_ge_half {ε₁ : ℝ} {u : ℝ → ℝ}
    (hu : WindowProfile ε₁ u) {T : ℝ} (hT : 0 < T) :
    T / 2 ≤ cosTransform (profileΩ u T) 0 := by
  rw [cosTransform_zero_eq_integral]
  have hΩc : Continuous (profileΩ u T) := by
    unfold profileΩ profileU
    exact ((hu.smooth 0).continuous.comp ((continuous_id.sub continuous_const).div_const T)).pow 4
  have hΩS : ∀ τ, τ ∉ Icc (T + ε₁ * T) (2 * T - ε₁ * T) → profileΩ u T τ = 0 := fun τ hτ => by
    unfold profileΩ
    rw [profileU_eq_zero hu hT hτ]
    norm_num
  have hΩi : Integrable (profileΩ u T) := by
    refine hΩc.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc : IsCompact (Icc (T + ε₁ * T) (2 * T - ε₁ * T))) fun τ hτ => ?_
    by_contra hnot
    exact hτ (hΩS τ hnot)
  have hΩ0 : ∀ τ, 0 ≤ profileΩ u T τ := fun τ => by unfold profileΩ; positivity
  set J : Set ℝ := Icc (T + 2 * ε₁ * T) (2 * T - 2 * ε₁ * T)
  have hJle : T + 2 * ε₁ * T ≤ 2 * T - 2 * ε₁ * T := by nlinarith [hu.le, hT]
  have hJ1 : ∀ τ ∈ J, profileΩ u T τ = 1 := fun τ hτ => by
    unfold profileΩ
    rw [profileU_eq_one hu hT hτ]
    norm_num
  have hset : ∫ τ in J, profileΩ u T τ ≤ ∫ τ, profileΩ u T τ :=
    setIntegral_le_integral hΩi (Eventually.of_forall hΩ0)
  have hval : ∫ τ in J, profileΩ u T τ = (2 * T - 2 * ε₁ * T) - (T + 2 * ε₁ * T) := by
    rw [setIntegral_congr_fun measurableSet_Icc hJ1, setIntegral_const,
      Real.volume_real_Icc_of_le hJle, smul_eq_mul, mul_one]
  have hεT : ε₁ * T ≤ (1 / 8) * T := mul_le_mul_of_nonneg_right hu.le hT.le
  linarith [hεT, hT, hset, hval]

/-- Eventually `(Ncount T (2 * T) : ℝ) ≤ T * Real.log T`. -/
theorem eventually_Ncount_le_T_mul_log :
    ∀ᶠ T in atTop, (Ncount T (2 * T) : ℝ) ≤ T * Real.log T := by
  obtain ⟨CR, TR, hRvM⟩ := paperInputs_zeta.RvM.main
  have hπ := Real.pi_gt_three
  filter_upwards [eventually_ge_atTop (max TR (max (2 * |CR|) 4)), eventually_l_bounds]
    with T hTmax ⟨hlog1, _, _, hhi⟩
  have hTR : TR ≤ T := (le_max_left _ _).trans hTmax
  have hT2 : max (2 * |CR|) 4 ≤ T := (le_max_right _ _).trans hTmax
  have hTCR : 2 * |CR| ≤ T := (le_max_left _ _).trans hT2
  have hT4 : 4 ≤ T := (le_max_right _ _).trans hT2
  have hT0 : 0 < T := by linarith
  have hRv0 := hRvM T hTR
  have hRv : (zetaZeroConfig.N T (2 * T) : ℝ) - T * ell1 T / (2 * π) ≤ |CR| * Real.log T := by
    have h1 := (abs_le.mp hRv0).2
    rw [show T / (2 * π) * ell1 T = T * ell1 T / (2 * π) by ring] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
  rw [zetaZeroConfig_N] at hRv
  have hlog2 : 2 * Real.log 2 - 1 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hell : ell1 T ≤ 2 * Real.log T := by
    unfold ell1
    linarith
  have hmain : T * ell1 T / (2 * π) ≤ T * Real.log T / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : T * ell1 T * 2 ≤ T * (2 * Real.log T) * 2 := by nlinarith
    have h2 : T * (2 * Real.log T) * 2 ≤ T * Real.log T * (2 * π) := by
      have hTL : 0 ≤ T * Real.log T := by positivity
      nlinarith
    linarith
  have herr : |CR| * Real.log T ≤ T * Real.log T / 2 := by
    have hlog0 : 0 ≤ Real.log T := by linarith
    nlinarith
  linarith

/-- **Unconditional Trans-Threshold Parity–Lobe Divergence Theorem:**
For **every** bandwidth excess `δ > 0` (`λ = 1 + δ > 1`), **every** smooth window profile
`WindowProfile ε₁ u`, **every** parity half-width `κ > 0`, **every** shift-density floor
`s_min > 0`, and **every** finite budget `M_budget : ℝ`, for all sufficiently large heights `T`,
at scale `m(T) = T^{1+δ}` and any shift horizon `R(T) ≥ ⌊(π / 12) T^δ⌋₊` with `S(T, r) ≥ s_min`,
the normalized parity-blind worst-case coalescent deviation strictly exceeds
`M_budget * N(T, 2T)`. -/
theorem parityBlind_dispersion_diverges_above_threshold
    {δ ε₁ κ s_min : ℝ} {u : ℝ → ℝ}
    (hδ : 0 < δ) (hu : WindowProfile ε₁ u) (hκ : 0 < κ) (hs_min : 0 < s_min)
    (M_budget : ℝ) (R : ℝ → ℕ) (C₀ S : ℝ → ℕ → ℝ)
    (hR : ∀ᶠ T in atTop, ⌊(π / 12) * T ^ δ⌋₊ ≤ R T)
    (hS : ∀ᶠ T in atTop, ∀ r ∈ Finset.Icc 1 (R T), s_min ≤ S T r) :
    ∀ᶠ T in atTop,
      M_budget * (Ncount T (2 * T) : ℝ) <
        ((∑ r ∈ Finset.Icc 1 (R T),
            parityAdversaryCorrelation (profileΩ u T) (T ^ (1 + δ)) κ (C₀ T) (S T) r *
              cosTransform (profileΩ u T) ((r : ℝ) * (2 / T ^ (1 + δ)))) -
          ∑ r ∈ Finset.Icc 1 (R T),
            C₀ T r * cosTransform (profileΩ u T) ((r : ℝ) * (2 / T ^ (1 + δ)))) /
          Real.log T ^ 2 := by
  have hπ := Real.pi_gt_three
  set B_pos : ℝ := max M_budget 1
  have hB_pos : 0 < B_pos := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hexp_lt : 1 - δ < 1 := by linarith
  have hrate1 := eventually_log_pow_rpow_le 3 hexp_lt (by positivity : 0 ≤ 2 * B_pos)
    (by positivity : (0 : ℝ) < κ * s_min * π / 96)
  have htend_K : Tendsto (fun T : ℝ => (π / 12) * T ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).const_mul_atTop (by positivity)
  filter_upwards [eventually_ge_atTop (4 : ℝ), eventually_l_bounds,
    eventually_Ncount_le_T_mul_log, hR, hS, hrate1,
    htend_K.eventually (eventually_ge_atTop (2 : ℝ))]
    with T hT4 ⟨hlog1, _, _, _⟩ hNle hRT hST hrt hK2
  have hT0 : 0 < T := by linarith
  have hm0 : 0 < T ^ (1 + δ) := Real.rpow_pos_of_pos hT0 _
  set K₁ : ℕ := ⌊(π / 12) * T ^ δ⌋₊
  have hK₁_ge : (π / 24) * T ^ δ ≤ (K₁ : ℝ) := by
    have hlt := Nat.sub_one_lt_floor ((π / 12) * T ^ δ)
    linarith
  have hK₁_le : (K₁ : ℝ) ≤ (π / 12) * T ^ δ := Nat.floor_le (by positivity)
  have hΩc : Continuous (profileΩ u T) := by
    unfold profileΩ profileU
    exact ((hu.smooth 0).continuous.comp ((continuous_id.sub continuous_const).div_const T)).pow 4
  have hΩS0 : ∀ τ, τ ∉ Icc (0 : ℝ) (2 * T) → profileΩ u T τ = 0 := by
    intro τ hτ
    unfold profileΩ
    rw [profileU_eq_zero hu hT0]
    · norm_num
    · intro hmem
      exact hτ ⟨by nlinarith [hmem.1, hu.pos, hT0], by nlinarith [hmem.2, hu.pos, hT0]⟩
  have hΩi : Integrable (profileΩ u T) := by
    refine hΩc.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * T))) fun τ hτ => ?_
    by_contra hnot
    exact hτ (hΩS0 τ hnot)
  have hΩ0 : ∀ τ, 0 ≤ profileΩ u T τ := fun τ => by unfold profileΩ; positivity
  have hrpow_split : T ^ (1 + δ) = T * T ^ δ := by
    rw [Real.rpow_add hT0, Real.rpow_one]
  have hK₁_step : (K₁ : ℝ) * (2 / T ^ (1 + δ)) ≤ π / (3 * (2 * T)) := by
    have hTδ : 0 < T ^ δ := Real.rpow_pos_of_pos hT0 δ
    calc (K₁ : ℝ) * (2 / T ^ (1 + δ))
        ≤ ((π / 12) * T ^ δ) * (2 / (T * T ^ δ)) := by
          rw [hrpow_split]
          exact mul_le_mul_of_nonneg_right hK₁_le (by positivity)
      _ = π / (3 * (2 * T)) := by
          field_simp [hT0.ne', hTδ.ne']
          ring
  have hdiff_ge := parityAdversary_coalescent_sum_sub_ge (C₀ := C₀ T)
    (le_refl (0 : ℝ)) (by linarith : (0 : ℝ) ≤ 2 * T) (by linarith : (0 : ℝ) < 2 * T) hm0
    hκ hs_min hΩi hΩ0 hΩS0 hST hRT hK₁_step
  have hcos0 := cosTransform_profileΩ_zero_ge_half hu hT0
  have hnum_ge : (κ * s_min * π / 96) * (T * T ^ δ) ≤
      (∑ r ∈ Finset.Icc 1 (R T),
          parityAdversaryCorrelation (profileΩ u T) (T ^ (1 + δ)) κ (C₀ T) (S T) r *
            cosTransform (profileΩ u T) ((r : ℝ) * (2 / T ^ (1 + δ)))) -
        ∑ r ∈ Finset.Icc 1 (R T),
          C₀ T r * cosTransform (profileΩ u T) ((r : ℝ) * (2 / T ^ (1 + δ))) := by
    calc (κ * s_min * π / 96) * (T * T ^ δ)
        = (κ * s_min * ((π / 24) * T ^ δ) / 2) * (T / 2) := by ring
      _ ≤ (κ * s_min * (K₁ : ℝ) / 2) * cosTransform (profileΩ u T) 0 := by
          refine mul_le_mul ?_ hcos0 (by positivity) (by positivity)
          have : κ * s_min * ((π / 24) * T ^ δ) ≤ κ * s_min * (K₁ : ℝ) :=
            mul_le_mul_of_nonneg_left hK₁_ge (mul_pos hκ hs_min).le
          linarith
      _ ≤ _ := hdiff_ge
  have hlog_sq_pos : 0 < Real.log T ^ 2 := by positivity
  rw [lt_div_iff₀ hlog_sq_pos]
  have hN_nn : 0 ≤ (Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hM_le : M_budget * (Ncount T (2 * T) : ℝ) * Real.log T ^ 2 ≤
      B_pos * Real.log T ^ 3 * T := by
    calc M_budget * (Ncount T (2 * T) : ℝ) * Real.log T ^ 2
        ≤ B_pos * (Ncount T (2 * T) : ℝ) * Real.log T ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hN_nn) hlog_sq_pos.le
      _ ≤ B_pos * (T * Real.log T) * Real.log T ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hNle hB_pos.le) hlog_sq_pos.le
      _ = B_pos * Real.log T ^ 3 * T := by ring
  have hrt' : (2 * B_pos) * Real.log T ^ 3 * T ^ (1 - δ) ≤ (κ * s_min * π / 96) * T := by
    simpa [mul_assoc] using hrt
  have hT_split : T = T ^ (1 - δ) * T ^ δ := by
    rw [← Real.rpow_add hT0]
    ring_nf
    exact (Real.rpow_one T).symm
  have hstrict : B_pos * Real.log T ^ 3 * T < (κ * s_min * π / 96) * (T * T ^ δ) := by
    have h2le : 2 * (B_pos * Real.log T ^ 3 * T) ≤ (κ * s_min * π / 96) * (T * T ^ δ) := by
      calc 2 * (B_pos * Real.log T ^ 3 * T)
          = (2 * B_pos * Real.log T ^ 3) * T := by ring
        _ = (2 * B_pos * Real.log T ^ 3) * (T ^ (1 - δ) * T ^ δ) :=
              congrArg ((2 * B_pos * Real.log T ^ 3) * ·) hT_split
        _ = ((2 * B_pos) * Real.log T ^ 3 * T ^ (1 - δ)) * T ^ δ := by ring
        _ ≤ ((κ * s_min * π / 96) * T) * T ^ δ :=
              mul_le_mul_of_nonneg_right hrt' (Real.rpow_nonneg hT0.le δ)
        _ = (κ * s_min * π / 96) * (T * T ^ δ) := by ring
    have hpos_term : 0 < B_pos * Real.log T ^ 3 * T := by positivity
    linarith
  linarith

/-- Specialization of `parityBlind_dispersion_diverges_above_threshold` refuting both the
narrow-strip quadratic surplus budget `B δ² / (1 + δ)²` (`∀ B ≥ 0, δ > 0`) and the bandwidth-`4/3`
first-rung budget `5 / 36`. -/
theorem parityBlind_refutes_quadratic_and_fourThirds_budgets
    {ε₁ κ s_min : ℝ} {u : ℝ → ℝ}
    (hu : WindowProfile ε₁ u) (hκ : 0 < κ) (hs_min : 0 < s_min) :
    (∀ {δ B : ℝ}, 0 < δ → 0 ≤ B →
      ∀ (R : ℝ → ℕ) (C₀ S : ℝ → ℕ → ℝ),
        (∀ᶠ T in atTop, ⌊(π / 12) * T ^ δ⌋₊ ≤ R T) →
        (∀ᶠ T in atTop, ∀ r ∈ Finset.Icc 1 (R T), s_min ≤ S T r) →
        ∀ᶠ T in atTop,
          (B * δ ^ 2 / (1 + δ) ^ 2) * (Ncount T (2 * T) : ℝ) <
            ((∑ r ∈ Finset.Icc 1 (R T),
                parityAdversaryCorrelation (profileΩ u T) (T ^ (1 + δ)) κ (C₀ T) (S T) r *
                  cosTransform (profileΩ u T) ((r : ℝ) * (2 / T ^ (1 + δ)))) -
              ∑ r ∈ Finset.Icc 1 (R T),
                C₀ T r * cosTransform (profileΩ u T) ((r : ℝ) * (2 / T ^ (1 + δ)))) /
              Real.log T ^ 2) ∧
    (∀ (R : ℝ → ℕ) (C₀ S : ℝ → ℕ → ℝ),
      (∀ᶠ T in atTop, ⌊(π / 12) * T ^ (1 / 3 : ℝ)⌋₊ ≤ R T) →
      (∀ᶠ T in atTop, ∀ r ∈ Finset.Icc 1 (R T), s_min ≤ S T r) →
      ∀ᶠ T in atTop,
        (5 / 36 : ℝ) * (Ncount T (2 * T) : ℝ) <
          ((∑ r ∈ Finset.Icc 1 (R T),
              parityAdversaryCorrelation (profileΩ u T) (T ^ (1 + (1 / 3 : ℝ))) κ (C₀ T) (S T) r *
                cosTransform (profileΩ u T) ((r : ℝ) * (2 / T ^ (1 + (1 / 3 : ℝ))))) -
            ∑ r ∈ Finset.Icc 1 (R T),
              C₀ T r * cosTransform (profileΩ u T) ((r : ℝ) * (2 / T ^ (1 + (1 / 3 : ℝ))))) /
            Real.log T ^ 2) := by
  refine ⟨fun {δ B} hδ _ R C₀ S hR hS =>
    parityBlind_dispersion_diverges_above_threshold hδ hu hκ hs_min (B * δ ^ 2 / (1 + δ) ^ 2)
      R C₀ S hR hS,
    fun R C₀ S hR hS =>
      parityBlind_dispersion_diverges_above_threshold (by norm_num : (0 : ℝ) < 1 / 3) hu hκ hs_min
        (5 / 36) R C₀ S hR hS⟩

/-! ### 3. Question 1 Proportion Transfer Laws & Battery Verification -/

/-- **Single-Profile Odd-Prime Even-Shift Proportion Transfer (Question 1 Statement):**
If for one smooth profile `WindowProfile ε₁ u` and one `0 < η < 1 / 3`, the odd-prime even-shift
coalescent surplus satisfies `oddEvenShiftPrimeCoalescentSurplus u η T ≤ (β + ε / 4) N(T, 2T)`
eventually, then `(29 / 36 - 32 π ε₁ - β - ε) N(T, 2T) ≤ N₀*(T, 2T)` eventually. -/
theorem oddEvenShift_singleProfile_certifies_proportion
    {ε₁ η β ε : ℝ} {u : ℝ → ℝ}
    (hu : WindowProfile ε₁ u) (hη0 : 0 < η) (hη3 : η < 1 / 3) (hε : 0 < ε)
    (hodd : ∀ᶠ T in atTop,
      oddEvenShiftPrimeCoalescentSurplus u η T ≤ (β + ε / 4) * (Ncount T (2 * T) : ℝ)) :
    ∀ᶠ T in atTop,
      (29 / 36 - 32 * π * ε₁ - β - ε) * (Ncount T (2 * T) : ℝ) ≤ (N0star T (2 * T) : ℝ) := by
  have hexp_neg : -1 / 3 + η < 0 := by linarith
  have htend : Tendsto (fun T : ℝ => 1024 * Real.sqrt 2 * T ^ (-1 / 3 + η)) atTop (𝓝 0) := by
    have h0 := tendsto_rpow_neg_atTop (by linarith : 0 < -(-1 / 3 + η))
      |>.congr' (Eventually.of_forall fun T => by rw [neg_neg])
    simpa [mul_zero] using h0.const_mul (1024 * Real.sqrt 2)
  filter_upwards [zeta_coalescent_certificate_four_thirds hu hη0 (by linarith : (0 : ℝ) < ε / 2),
    eventually_primeCoalescentSurplus_eq_oddEvenShift u (by linarith : η < 1),
    eventually_abs_coalescentSurplus_sub_primeCoalescentSurplus_le_mul_Ncount hu (by linarith : η < 1),
    htend.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 4)),
    hodd]
    with T hcert heq hpp hsmall hsurp
  have hN0 : 0 ≤ (Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hpp' : coalescentSurplus u η T - primeCoalescentSurplus u η T ≤
      (ε / 4) * (Ncount T (2 * T) : ℝ) := by
    exact (le_abs_self _).trans (hpp.trans (mul_le_mul_of_nonneg_right hsmall.le hN0))
  rw [heq] at hpp'
  linarith

/-- **Question 1 Complete Proportion & Battery Package:**
1. *Exact threshold payoffs:* `PrimeCoalescentSurplusAtMost β` certifies
   `N₀*(T, 2T) ≥ (29 / 36 - β - ε) N(T, 2T)` eventually — strictly beating `2 / 3` whenever
   `β < 5 / 36` (with positive margin `(5 / 36 - β) / 2 > 0`) and reaching `3 / 4` whenever
   `β ≤ 1 / 18`;
2. *Prime-power retention & elimination:* `CoalescentSurplusAtMost β ↔ PrimeCoalescentSurplusAtMost β`;
3. *Haar-typical gauge vanishing (`β = 0`):* for every profile `u`, `η < 1`, and `δ_b > 0`, the
   gauge-Haar measure of twists exceeding `δ_b N(T, 2T)` tends to `0`;
4. *Narrow-strip optimal gain:* any quadratic bound `B ≥ 0` across `λ = 1 + δ` achieves strictly
   positive gain `narrowStripGain B (1 / (3B + 2)) > 0` over `2 / 3`. -/
theorem coalescent_surplus_battery_laws :
    (∀ {β : ℝ}, PrimeCoalescentSurplusAtMost β →
      ∀ ε > 0, ∀ᶠ T in atTop,
        (29 / 36 - β - ε) * (Ncount T (2 * T) : ℝ) ≤ (N0star T (2 * T) : ℝ)) ∧
    (∀ {β : ℝ}, β < 5 / 36 → PrimeCoalescentSurplusAtMost β →
      0 < (5 / 36 - β) / 2 ∧
      ∀ᶠ T in atTop,
        (2 / 3 + (5 / 36 - β) / 2) * (Ncount T (2 * T) : ℝ) ≤ (N0star T (2 * T) : ℝ)) ∧
    (∀ {β : ℝ}, β ≤ 1 / 18 → PrimeCoalescentSurplusAtMost β →
      ∀ ε > 0, ∀ᶠ T in atTop,
        (3 / 4 - ε) * (Ncount T (2 * T) : ℝ) ≤ (N0star T (2 * T) : ℝ)) ∧
    (∀ β : ℝ, CoalescentSurplusAtMost β ↔ PrimeCoalescentSurplusAtMost β) ∧
    (∀ {ε₁ : ℝ} {u : ℝ → ℝ}, WindowProfile ε₁ u → ∀ {η : ℝ}, η < 1 → ∀ {δ_b : ℝ}, 0 < δ_b →
      Tendsto (fun T => gaugeHaar.real
        {x | δ_b * (Ncount T (2 * T) : ℝ) ≤ ‖twistedPrimeCoalescentSurplus u η T x‖}) atTop (𝓝 0)) ∧
    (∀ {B : ℝ}, 0 ≤ B → 0 < narrowStripGain B (1 / (3 * B + 2))) := by
  refine ⟨?_, ?_, ?_, coalescentSurplusAtMost_iff_primeCoalescentSurplusAtMost,
    fun {_ _} hu {_} hη {_} hδ => tendsto_gaugeHaar_large_twistedSurplus hu hη hδ,
    fun hB => (narrowStrip_optimal_delta_gain hB).2⟩
  · intro β hP ε hε
    obtain ⟨η, u, ε₁, _, _, _, hev⟩ := hP (ε / 2) (by linarith)
    filter_upwards [hev] with T ⟨hcert, hsurp⟩
    linarith
  · intro β hβ hP
    have hγ : 0 < (5 / 36 - β) / 2 := by linarith
    refine ⟨hγ, ?_⟩
    obtain ⟨η, u, ε₁, _, _, _, hev⟩ := hP ((5 / 36 - β) / 4) (by linarith)
    filter_upwards [hev] with T ⟨hcert, hsurp⟩
    linarith
  · intro β hβ hP ε hε
    obtain ⟨η, u, ε₁, _, _, _, hev⟩ := hP (ε / 2) (by linarith)
    filter_upwards [hev] with T ⟨hcert, hsurp⟩
    have hN0 : 0 ≤ (Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
    have hle : (3 / 4 - ε) * (Ncount T (2 * T) : ℝ) ≤
        (29 / 36 - β - ε) * (Ncount T (2 * T) : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hN0
    have hcomb : (29 / 36 - β - ε) * (Ncount T (2 * T) : ℝ) =
        (29 / 36 - ε / 2) * (Ncount T (2 * T) : ℝ) -
          (β + ε / 2) * (Ncount T (2 * T) : ℝ) := by ring
    linarith

/-! ### 4. Exact Escape Laplace Transform Split & RH-Visibility Equivalence (Question 5A) -/

/-- The damped Möbius escape Laplace symbol
`G_ε(s) = (ζ(s) / ζ(s + ε) - m_ε ζ(s)) / s`, where `m_ε = dampedDensity ε = Re(ζ(1 + ε)⁻¹)`. -/
def escapeLaplaceSymbol (ε : ℝ) (s : ℂ) : ℂ :=
  (riemannZeta s / riemannZeta (s + ε) - (dampedDensity ε : ℂ) * riemannZeta s) / s

/-- For `ε > 0`, `escapeLaplaceSymbol ε s` equals Question 5(A)'s closed form
`ζ(s) (ζ(s + ε)⁻¹ - (Re(ζ(1 + ε)⁻¹))) / s`. -/
theorem escapeLaplaceSymbol_eq_invZeta_form {ε : ℝ} (hε : 0 < ε) (s : ℂ) :
    escapeLaplaceSymbol ε s =
      riemannZeta s * ((riemannZeta (s + ε))⁻¹ - (((riemannZeta (1 + ε))⁻¹).re : ℂ)) / s := by
  have hne : (1 : ℂ) + (ε : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hd : dampedDensity ε = ((riemannZeta (1 + (ε : ℂ)))⁻¹).re := by
    have h1 := invZeta_one_add_eq_dampedDensity hε
    rw [invZeta_eq_inv hne] at h1
    have h2 := congrArg Complex.re h1
    simpa using h2.symm
  unfold escapeLaplaceSymbol
  rw [hd, div_eq_mul_inv]
  ring

/-- **Exact Escape Laplace Transform Split & Global RH-Visibility Theorem:**
1. *Continuation on the strip:* under receiver energy `O((T + 1)^κ)` and `0 < ε < 1`, for
   `c > κ / 2` and `s = c + 1 / 2 + i y` with `Re s < 1`, `ζ(s + ε) ≠ 0`, `s + ε ≠ 1`,
   `lineSymbol (receiverLogProfile ε) c y = escapeLaplaceSymbol ε s`;
2. *Simple-pole residue split at translated zeros:* at every simple zero `ρ` of `ζ` (`ρ ≠ 1`,
   `ρ - ε ∉ {0, 1}`), `escapeLaplaceSymbol ε s - (ζ(ρ - ε) / (ζ'(ρ)(ρ - ε))) / (s - (ρ - ε))` is
   uniformly bounded on a punctured disc around `ρ - ε` (producing the spectral atom
   `π ‖ζ(ρ - ε) / (ζ'(ρ)(ρ - ε))‖² δ_{Im ρ}` when `ρ` is dominant via `tendsto_receiver_window_atom`),
   while every zero-free compact vertical segment carries zero asymptotic share of an escaping
   receiver (`tendsto_receiver_window_share_zero`);
3. *Global infinite-height remainder equivalence:* positive gauge mass on every actual escape state
   across `0 < ε < 1 / 2` (equivalently, full visible gauge mass `1` with zero mass escaping to
   infinite height) is **unconditionally equivalent to `RiemannHypothesis`**. -/
theorem escapeLaplaceSymbol_pole_and_visibility_laws :
    (∀ {ε C κ c y : ℝ}, 0 < ε → ε < 1 → 0 ≤ C → 0 ≤ κ →
      (∀ T : ℕ, dampedMobiusEnergy ε T ≤ C * ((T : ℝ) + 1) ^ κ) →
      κ / 2 < c → c + 1 / 2 < 1 →
      let s : ℂ := ((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I
      riemannZeta (s + ε) ≠ 0 → s + ε ≠ 1 →
      lineSymbol (receiverLogProfile ε) c y = escapeLaplaceSymbol ε s) ∧
    (∀ {ε : ℝ} {ρ : ℂ}, riemannZeta ρ = 0 → deriv riemannZeta ρ ≠ 0 →
      ρ ≠ 1 → ρ - (ε : ℂ) ≠ 0 → ρ - (ε : ℂ) ≠ 1 →
      ∃ η > 0, ∃ M : ℝ, ∀ s : ℂ, ‖s - (ρ - (ε : ℂ))‖ < η → s ≠ ρ - (ε : ℂ) →
        ‖escapeLaplaceSymbol ε s -
          riemannZeta (ρ - (ε : ℂ)) / (deriv riemannZeta ρ * (ρ - (ε : ℂ))) /
            (s - (ρ - (ε : ℂ)))‖ ≤ M) ∧
    (RiemannHypothesis ↔
      ∀ ε : SubcriticalDamping, ∀ L : ActualCofactorLimit ε, 0 < gaugeMass L.kernel) ∧
    (RiemannHypothesis ↔
      ∀ ε : SubcriticalDamping, ∀ L : ActualCofactorLimit ε, gaugeMass L.kernel = 1) := by
  refine ⟨?_, ?_, riemannHypothesis_iff_forall_gaugeMass_pos, ?_⟩
  · intro ε C κ c y hε hε1 hC hκ hE hc hc1 s hζ hne
    rw [lineSymbol_receiver_eq hC hκ hE hc y]
    have hsre : s.re = c + 1 / 2 := by simp [s]
    have hΦ := complexMellinPairing_receiver_eq hε hε1 hC hκ hE (s := s)
      (by rw [hsre]; linarith) (by rw [hsre]; exact hc1) hζ hne
    rw [show ((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I = s from rfl, hΦ]
    rfl
  · intro ε ρ hρ hd hρ1 hs0 hs1
    obtain ⟨η, hη, M, hpole⟩ :=
      exists_cofactor_pole_bound (ε := (ε : ℂ)) (dampedDensity ε : ℂ) hρ hd hρ1 hs0 hs1
    exact ⟨η, hη, M, fun s hs hne => (hpole s hs hne).2.2.2.2⟩
  · constructor
    · exact gaugeMass_eq_one_of_riemannHypothesis
    · intro h1
      exact riemannHypothesis_iff_forall_gaugeMass_pos.mpr fun ε L => by
        rw [h1 ε L]
        exact one_pos

end GaloisForLFunctions.SelectivePositivityAndThresholdLaws
