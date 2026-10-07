import GaloisForLFunctions.RHTower.WeilWorkPBAPGramPackets
import GaloisForLFunctions.HTGeometry.InfiniteTorusCharacter
import GaloisForLFunctions.HTGeometry.SmoothNumbers
import GaloisForLFunctions.HTGeometry.ComplexIntegralGram
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Representing measures realized by null packets

A probability measure on the prime torus that annihilates positive integer
characters gives positive Gram matrices with zero divisibility diagonals.
Their smooth packet realizations retain the measure's rational moments, multiplied
by the exact finite coefficient correlation. No Weil-energy sign is assumed.
-/

open Complex MeasureTheory Zeta23 GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped BigOperators ComplexConjugate ContDiff ComplexOrder MatrixOrder

noncomputable section

namespace RHTower.WeilWorkPBAP

open WeilOneSided

/-- The compact torus with one circle coordinate for each prime. -/
abbrev PrimePhaseSpace := UnitAddTorus Nat.Primes

/-- The prime factorization of an integer, as an integer-valued character index. -/
def arithmeticExponent (n : ℕ) : Nat.Primes →₀ ℤ :=
  (primeExponentVector n).mapRange (fun k : ℕ => (k : ℤ)) (by simp)

@[simp] theorem arithmeticExponent_apply (n : ℕ) (p : Nat.Primes) :
    arithmeticExponent n p = (n.factorization (p : ℕ) : ℤ) := by
  simp [arithmeticExponent]

@[simp] theorem arithmeticExponent_one : arithmeticExponent 1 = 0 := by
  ext p
  simp

theorem arithmeticExponent_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    arithmeticExponent (m * n) = arithmeticExponent m + arithmeticExponent n := by
  ext p
  simp [Nat.factorization_mul hm hn]

/-- The positive integer monomial on the prime torus. -/
def arithmeticPhase (n : ℕ) : C(PrimePhaseSpace, ℂ) :=
  torusCharacter (arithmeticExponent n)

@[simp] theorem arithmeticPhase_one (z : PrimePhaseSpace) : arithmeticPhase 1 z = 1 := by
  simp [arithmeticPhase, torusCharacter_zero]

theorem arithmeticPhase_mul_conj (n : ℕ) (z : PrimePhaseSpace) :
    arithmeticPhase n z * conj (arithmeticPhase n z) = 1 := by
  unfold arithmeticPhase
  rw [← torusCharacter_neg_index, ← torusCharacter_add_index,
    add_neg_cancel, torusCharacter_zero]

theorem arithmeticPhase_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (z : PrimePhaseSpace) :
    arithmeticPhase (m * n) z = arithmeticPhase m z * arithmeticPhase n z := by
  unfold arithmeticPhase
  rw [arithmeticExponent_mul hm hn, torusCharacter_add_index]

theorem arithmeticPhase_rational_fibre {a b m k : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hm : m ≠ 0) (hk : k ≠ 0)
    (heq : a * k = b * m) (z : PrimePhaseSpace) :
    arithmeticPhase m z * conj (arithmeticPhase k z) =
      arithmeticPhase a z * conj (arithmeticPhase b z) := by
  have he := congrArg arithmeticExponent heq
  rw [arithmeticExponent_mul ha hk, arithmeticExponent_mul hb hm] at he
  have hd : arithmeticExponent m - arithmeticExponent k =
      arithmeticExponent a - arithmeticExponent b := by
    calc
      arithmeticExponent m - arithmeticExponent k =
          (arithmeticExponent b + arithmeticExponent m) -
            (arithmeticExponent b + arithmeticExponent k) := by abel
      _ = (arithmeticExponent a + arithmeticExponent k) -
            (arithmeticExponent b + arithmeticExponent k) := by rw [← he]
      _ = arithmeticExponent a - arithmeticExponent b := by abel
  unfold arithmeticPhase
  rw [← torusCharacter_neg_index, ← torusCharacter_add_index,
    ← torusCharacter_neg_index, ← torusCharacter_add_index,
    ← sub_eq_add_neg, ← sub_eq_add_neg, hd]

/-- Probability measures representing evaluation at the origin on integer monomials. -/
def RepresentingPhaseMeasure :=
  {μ : ProbabilityMeasure PrimePhaseSpace //
    ∀ n : ℕ, 2 ≤ n → ∫ z, arithmeticPhase n z ∂(μ : Measure PrimePhaseSpace) = 0}

/-- A rational character moment of a prime-torus probability measure. -/
def phaseMoment (μ : ProbabilityMeasure PrimePhaseSpace) (a b : ℕ) : ℂ :=
  ∫ z, arithmeticPhase a z * conj (arithmeticPhase b z) ∂(μ : Measure PrimePhaseSpace)

@[simp] theorem phaseMoment_self (μ : ProbabilityMeasure PrimePhaseSpace) (n : ℕ) :
    phaseMoment μ n n = 1 := by
  simp [phaseMoment, arithmeticPhase_mul_conj]

theorem phaseMoment_rational_fibre (μ : ProbabilityMeasure PrimePhaseSpace)
    {a b m k : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hm : m ≠ 0) (hk : k ≠ 0)
    (heq : a * k = b * m) : phaseMoment μ m k = phaseMoment μ a b := by
  unfold phaseMoment
  exact integral_congr_ae (Filter.Eventually.of_forall
    (arithmeticPhase_rational_fibre ha hb hm hk heq))

/-- The actual feature Gram matrix of weighted integer characters. -/
def phaseMomentMatrix {N : ℕ} (μ : ProbabilityMeasure PrimePhaseSpace)
    (d : PacketIndex N → ℂ) : Matrix (PacketIndex N) (PacketIndex N) ℂ :=
  complexFeatureGram (μ : Measure PrimePhaseSpace)
    (fun m z => d m * arithmeticPhase (m : ℕ) z)

theorem phaseMomentMatrix_apply {N : ℕ} (μ : ProbabilityMeasure PrimePhaseSpace)
    (d : PacketIndex N → ℂ) (m k : PacketIndex N) :
    phaseMomentMatrix μ d m k = d m * conj (d k) * phaseMoment μ m k := by
  unfold phaseMomentMatrix complexFeatureGram phaseMoment
  simp_rw [map_mul]
  calc
    _ = ∫ z, (d m * conj (d k)) *
        (arithmeticPhase (m : ℕ) z * conj (arithmeticPhase (k : ℕ) z))
          ∂(μ : Measure PrimePhaseSpace) := by
      congr 1
      funext z
      ring
    _ = _ := integral_const_mul _ _

theorem phaseMomentMatrix_posSemidef {N : ℕ}
    (μ : ProbabilityMeasure PrimePhaseSpace) (d : PacketIndex N → ℂ) :
    (phaseMomentMatrix μ d).PosSemidef := by
  apply complexFeatureGram_posSemidef
  intro m k
  have hc : Continuous (fun z : PrimePhaseSpace =>
      (d m * arithmeticPhase (m : ℕ) z) * conj (d k * arithmeticPhase (k : ℕ) z)) :=
    (continuous_const.mul (arithmeticPhase _).continuous).mul
      (continuous_const.mul (arithmeticPhase _).continuous).star
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem phaseMomentMatrix_trace {N : ℕ} (μ : ProbabilityMeasure PrimePhaseSpace)
    (d : PacketIndex N → ℂ) :
    (phaseMomentMatrix μ d).trace = ((∑ m, ‖d m‖ ^ 2 : ℝ) : ℂ) := by
  simp [Matrix.trace, Matrix.diag, phaseMomentMatrix_apply, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

theorem phaseMomentMatrix_divisible {N n : ℕ} (μ : RepresentingPhaseMeasure)
    (d : PacketIndex N → ℂ) (hn : 2 ≤ n) (m k : PacketIndex N)
    (heq : n * (k : ℕ) = (m : ℕ)) : phaseMomentMatrix μ.1 d m k = 0 := by
  have hm := (Finset.mem_Icc.mp m.property).1
  have hk := (Finset.mem_Icc.mp k.property).1
  rw [phaseMomentMatrix_apply, phaseMoment_rational_fibre μ.1
    (by omega : n ≠ 0) (by omega : 1 ≠ 0) (by omega) (by omega) (by simpa using heq)]
  simp [phaseMoment, μ.2 n hn]

/-- Representing measures supply the null Gram constraint without assuming matrix positivity. -/
def representingPacketGram {N : ℕ} (μ : RepresentingPhaseMeasure)
    (d : PacketIndex N → ℂ) : NullPacketGram N :=
  ⟨phaseMomentMatrix μ.1 d, phaseMomentMatrix_posSemidef μ.1 d, by
    intro n hn
    apply Finset.sum_eq_zero
    intro m _
    apply Finset.sum_eq_zero
    intro k _
    split_ifs with heq
    · exact phaseMomentMatrix_divisible μ d (Finset.mem_Icc.mp hn).1 m k heq
    · rfl⟩

/-- The multiplicative coefficient correlation retained by the finite packet window. -/
def packetCoeffCorrelation {N : ℕ} (d : PacketIndex N → ℂ) (a b : ℕ) : ℂ :=
  ∑ m : PacketIndex N, ∑ k : PacketIndex N,
    if a * (k : ℕ) = b * (m : ℕ) then d m * conj (d k) else 0

theorem phaseMomentMatrix_rational_sum {N a b : ℕ}
    (μ : ProbabilityMeasure PrimePhaseSpace) (d : PacketIndex N → ℂ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (∑ m : PacketIndex N, ∑ k : PacketIndex N,
      if a * (k : ℕ) = b * (m : ℕ) then phaseMomentMatrix μ d m k else 0) =
        phaseMoment μ a b * packetCoeffCorrelation d a b := by
  simp only [packetCoeffCorrelation, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
  split_ifs with heq
  · have hm := (Finset.mem_Icc.mp m.property).1
    have hk := (Finset.mem_Icc.mp k.property).1
    rw [phaseMomentMatrix_apply, phaseMoment_rational_fibre μ
      (by omega) (by omega) (by omega) (by omega) heq]
    ring
  · simp

/-- Weighted samples of a finite mixture of full Weil tests. -/
def mixtureSample (c : WeilTestFn →₀ ℝ) (y : ℝ) : ℂ :=
  (Finsupp.linearCombination ℝ (fun f : WeilTestFn => EF.weilTest f.1 f.1 y)) c

theorem mixtureSample_smul (r : ℝ) (c : WeilTestFn →₀ ℝ) (y : ℝ) :
    mixtureSample (r • c) y = r • mixtureSample c y := by
  exact map_smul (Finsupp.linearCombination ℝ _) r c

theorem mixtureSample_packetMixture {N : ℕ} (f : PacketIndex N → WeilTestFn) (y : ℝ) :
    mixtureSample (packetMixture f) y = ∑ i, EF.weilTest (f i).1 (f i).1 y := by
  unfold mixtureSample packetMixture
  rw [map_sum]
  simp only [Finsupp.linearCombination_single, one_smul]

/-- Coefficient profiles of unit squared mass. -/
def UnitPacketCoeffs (N : ℕ) :=
  {d : PacketIndex N → ℂ // ∑ m, ‖d m‖ ^ 2 = 1}

private theorem inverse_packetMass_smul (N L : ℕ) (z : ℂ) :
    (packetMass N L)⁻¹ • ((packetMass N L : ℂ) * z) = z := by
  rw [Complex.real_smul, Complex.ofReal_inv, ← mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (packetMass_pos N L).ne'), one_mul]

/-- Every representing measure and unit coefficient profile admit an actual smooth
finite mixture with mass one, all integer null constraints, and exact rational samples.
The finite coefficient correlation is the entire error in realizing each target moment. -/
theorem exists_normalized_representing_mixture (N L : ℕ)
    (μ : RepresentingPhaseMeasure) (d : UnitPacketCoeffs N) :
    ∃ (f : PacketIndex N → WeilTestFn) (c : WeilTestFn →₀ ℝ),
      (∀ i, ContDiff ℝ ∞ (f i).1) ∧
      c = (packetMass N (L + 1))⁻¹ • packetMixture f ∧
      (∀ g, 0 ≤ c g) ∧
      (∀ n : ℕ, 2 ≤ n → c.sum (fun g t => t * logValue g.1 n) = 0) ∧
      mixtureSample c 0 = 1 ∧
      ∀ (a b : ℕ), 1 ≤ a → 1 ≤ b → b ≤ L + 1 →
        mixtureSample c (Real.log a - Real.log b) =
          phaseMoment μ.1 a b * packetCoeffCorrelation d.1 a b := by
  obtain ⟨f, hf, hc, hn, hm, hs⟩ :=
    exists_nullPacket_mixture N L (representingPacketGram μ d.1)
  refine ⟨f, (packetMass N (L + 1))⁻¹ • packetMixture f, hf, rfl, ?_, ?_, ?_, ?_⟩
  · intro g
    change 0 ≤ (packetMass N (L + 1))⁻¹ * packetMixture f g
    exact mul_nonneg (inv_nonneg.mpr (packetMass_pos _ _).le) (hc g)
  · intro n hn2
    change (Finsupp.linearCombination ℝ (fun g : WeilTestFn => logValue g.1 n))
      ((packetMass N (L + 1))⁻¹ • packetMixture f) = 0
    rw [map_smul]
    change (packetMass N (L + 1))⁻¹ *
      (packetMixture f).sum (fun g t => t * logValue g.1 n) = 0
    rw [hn n hn2, mul_zero]
  · rw [mixtureSample_smul, mixtureSample_packetMixture, hm]
    change (packetMass N (L + 1))⁻¹ •
      ((packetMass N (L + 1) : ℂ) * (phaseMomentMatrix μ.1 d.1).trace) = 1
    rw [inverse_packetMass_smul, phaseMomentMatrix_trace, d.2, Complex.ofReal_one]
  · intro a b ha hb hbL
    rw [mixtureSample_smul, mixtureSample_packetMixture, hs a b ha hb hbL,
      inverse_packetMass_smul]
    exact phaseMomentMatrix_rational_sum μ.1 d.1 ha hb

end RHTower.WeilWorkPBAP
