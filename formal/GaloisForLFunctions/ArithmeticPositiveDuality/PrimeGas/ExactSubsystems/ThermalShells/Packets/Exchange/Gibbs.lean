import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exchange.Spectrum
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Temperatures

/-! # Gibbs partitions and marked occupation moments of the two exchange sectors -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exchange

open Finset Real

def atom (b : ℝ) (p : Nat.Primes) := weight b energy (quantum p)

def singleZ (S : Finset Nat.Primes) (b : ℝ) := ∑ p ∈ S,atom b p

def sectorZ (S : Finset Nat.Primes) (squares : Bool) (b : ℝ) := reading S squares (weight b energy)

def hit (H : Finset Nat.Primes) (p : Nat.Primes) : ℝ := if p ∈ H then 1 else 0

def firstMoment (S : Finset Nat.Primes) (b : ℝ) (a : Nat.Primes → ℝ) := ∑ p ∈ S,atom b p*a p

def markedZ (S H : Finset Nat.Primes) (b : ℝ) := firstMoment S b (hit H)

/-- Count marked occupations directly in the prime factorization of the integer energy label. -/
def markedCount (H : Finset Nat.Primes) (n : ℕ+) : ℝ := ((∑ r ∈ H,label.symm n r : ℕ) : ℝ)

def tested (S : Finset Nat.Primes) (squares : Bool) (b : ℝ) (F : ℕ+ → ℝ) :=
  reading S squares (fun n => weight b energy n*F n)

def moment (S H : Finset Nat.Primes) (squares : Bool) (b : ℝ) := tested S squares b (markedCount H)

theorem singleZ_pos {S : Finset Nat.Primes} (hs : S.Nonempty) (b : ℝ) : 0 < singleZ S b :=
  sum_pos (fun _ _ => exp_pos _) hs

theorem pair_weight (b : ℝ) (p q : Nat.Primes) : weight b energy (pair p q) = atom b p*atom b q := by
  simp only [weight,atom,pair,energy_mul,mul_add,exp_add]

theorem doubled_atom (b : ℝ) (p : Nat.Primes) : atom (2*b) p = atom b p^2 := by
  unfold atom weight
  rw [sq,← exp_add]
  congr 1; ring

theorem marked_pair (H : Finset Nat.Primes) (p q : Nat.Primes) :
    markedCount H (pair p q) = hit H p+hit H q := by
  simp [markedCount,pair_vector,Finsupp.single_apply,sum_add_distrib,hit]

theorem sum_separable (S : Finset Nat.Primes) (f g : Nat.Primes → ℝ) :
    (∑ p ∈ S, ∑ q ∈ S,f p*g q) = (∑ p ∈ S,f p)*(∑ q ∈ S,g q) := by
  rw [sum_mul]
  simp only [mul_sum]

/-- Exchange addition gives the square of the one-prime partition. Exchange subtraction
leaves the one-prime partition at twice the inverse temperature. -/
theorem partition_traces (S : Finset Nat.Primes) (b : ℝ) :
    sectorZ S true b + sectorZ S false b = singleZ S b^2 ∧
    sectorZ S true b - sectorZ S false b = singleZ S (2*b) := by
  constructor
  · simp only [sectorZ,reading_add,pair_weight,sum_separable,singleZ,sq]
  · simp only [sectorZ,reading_sub,pair_weight,singleZ,doubled_atom,sq]

/-- For additive observables, exchange addition recovers two independent prime readings.
Exchange subtraction measures one prime at doubled inverse temperature, counted twice. -/
theorem additive_traces (S : Finset Nat.Primes) (b : ℝ) (a : Nat.Primes → ℝ) (F : ℕ+ → ℝ)
    (hF : ∀ p q, F (pair p q) = a p+a q) :
    tested S true b F + tested S false b F = 2*firstMoment S b a*singleZ S b ∧
    tested S true b F - tested S false b F = 2*firstMoment S (2*b) a := by
  constructor
  · rw [tested,tested,reading_add]
    have one (p q : Nat.Primes) : weight b energy (pair p q)*F (pair p q) =
        (atom b p*a p)*atom b q + atom b p*(atom b q*a q) := by
      rw [pair_weight,hF]; ring
    simp only [one,sum_add_distrib,sum_separable,firstMoment,singleZ]
    ring
  · rw [tested,tested,reading_sub,firstMoment,mul_sum]
    apply sum_congr rfl
    intro p _
    rw [pair_weight,hF,doubled_atom]; ring

theorem moment_traces (S H : Finset Nat.Primes) (b : ℝ) :
    moment S H true b + moment S H false b = 2*markedZ S H b*singleZ S b ∧
    moment S H true b - moment S H false b = 2*markedZ S H (2*b) :=
  additive_traces S b _ _ (marked_pair H)

def expectation (S : Finset Nat.Primes) (squares : Bool) (b : ℝ) (F : ℕ+ → ℝ) :=
  tested S squares b F/sectorZ S squares b

/-- A sector with zero partition has zero unnormalized reading for every test. -/
theorem weighted_expectation (S : Finset Nat.Primes) (squares : Bool) (b : ℝ) (F : ℕ+ → ℝ) :
    sectorZ S squares b * expectation S squares b F = tested S squares b F := by
  by_cases h : (levels S squares).Nonempty
  · exact mul_div_cancel₀ _ (sum_pos (fun _ _ => exp_pos _) h : 0 < sectorZ S squares b).ne'
  · simp only [sectorZ,tested,reading,not_nonempty_iff_eq_empty.mp h,sum_empty,zero_mul]

def sectorMean (S H : Finset Nat.Primes) (squares : Bool) (b : ℝ) :=
  expectation S squares b (markedCount H)

theorem weighted_mean (S H : Finset Nat.Primes) (squares : Bool) (b : ℝ) :
    sectorZ S squares b * sectorMean S H squares b = moment S H squares b :=
  weighted_expectation S squares b (markedCount H)

#print axioms additive_traces
#print axioms marked_pair
#print axioms partition_traces
#print axioms moment_traces
#print axioms weighted_mean

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exchange
