import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.Labels
import GaloisForLFunctions.RHTower.SquarefreeEulerModularCoronaCurvatureColligation
import GaloisForLFunctions.RHTower.Sieve.PrimeCosineSum

/-! # Finite measurements of the squarefree orientation -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.Window

open _root_.RHTower

abbrev packet (N : ℕ) := Sieve.primeSubtypeLE N
abbrev Config (N : ℕ) := SquarefreeBitConfig (packet N)

/-- Restrict the squarefree output of the two-copy unitary to the observed primes. -/
def readBits (N : ℕ) (q : ℕ+ × ℕ+) : Config N :=
  fun p => squarefreeBasis.symm (basis q).2.2 p.val

/-- The vacuum event tests which of the two inputs has the greater prime multiplicity. -/
theorem readBits_vacuum_iff (N : ℕ) (q : ℕ+ × ℕ+) :
    readBits N q = 0 ↔ ∀ p : ↥(packet N),
      q.2.val.factorization p.val.val ≤ q.1.val.factorization p.val.val := by
  have bit (p : ↥(packet N)) : readBits N q p = 1 ↔
      q.1.val.factorization p.val.val < q.2.val.factorization p.val.val := by
    change squarefreeBasis.symm (squarefreeBasis _) p.val = 1 ↔ _
    rw [squarefreeBasis.symm_apply_apply]
    change (mode (label.symm q.1 p.val,label.symm q.2 p.val)).2.2 = 1 ↔ _
    rw [orientation_iff,show label.symm q.1 p.val = _ from primeExponentVector_apply q.1.val p.val,
      show label.symm q.2 p.val = _ from primeExponentVector_apply q.2.val p.val]
  constructor
  · intro he p
    apply le_of_not_gt
    intro hp
    have ho := (bit p).mpr hp
    rw [he] at ho
    exact zero_ne_one ho
  · intro h
    funext p
    have hn : readBits N q p ≠ 1 := fun he => (not_lt.mpr (h p)) ((bit p).mp he)
    apply Fin.ext
    change (readBits N q p).val = 0
    have hh := (readBits N q p).isLt
    have hne : (readBits N q p).val ≠ 1 := fun e => hn (Fin.ext e)
    omega

/-- Finite binary partition, continued to complex inverse temperature. -/
def partition (N : ℕ) (s : ℂ) : ℂ := ∏ p ∈ N.primesLE, (1+(p:ℂ)^(-s))

theorem product_over_packet (N : ℕ) (f : ℕ → ℂ) :
    (∏ p : ↥(packet N), f p.val.val) = ∏ p ∈ N.primesLE, f p := by
  calc
    _ = ∏ p ∈ packet N, f p.val := Finset.prod_coe_sort (packet N) (fun p : Nat.Primes => f p.val)
    _ = _ := Finset.prod_subtype_of_mem f (fun n hn => Nat.prime_of_mem_primesLE hn)

private theorem prime_heat (p : Nat.Primes) (s : ℂ) :
    (p.val:ℂ)^(-s) = Complex.exp (-s*(Real.log (p:ℝ):ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr p.property.ne_zero),
    ← Complex.ofReal_natCast,← Complex.ofReal_log (Nat.cast_nonneg p.val),mul_comm]

theorem partition_bits (N : ℕ) (s : ℂ) :
    partition N s = ∏ p : ↥(packet N), (1+Complex.exp (-s*(squarefreePrimeEnergy p.val:ℂ))) := by
  rw [partition,← product_over_packet]
  exact Finset.prod_congr rfl (fun p _ => congrArg (1+·) (prime_heat p.val s))

theorem partition_real (N : ℕ) (s : ℝ) :
    partition N s = (finiteSquarefreePartition (packet N) s : ℂ) := by
  rw [partition_bits,finiteSquarefreePartition]
  push_cast
  apply Finset.prod_congr rfl
  intro p _
  simp only [squarefreePrimeNome,primeSchurWeight,squarefreePrimeEnergy,Complex.ofReal_exp,
    Complex.ofReal_mul,Complex.ofReal_neg]

/-- Sum of complex heat amplitudes over actual binary occupation configurations. -/
theorem partition_trace (N : ℕ) (s : ℂ) :
    (∑ x : Config N, Complex.exp (-s*(finiteSquarefreeHamiltonian (packet N) x:ℂ))) =
      partition N s := by
  classical
  let f := fun (p : ↥(packet N)) (b : Fin 2) =>
    Complex.exp (-s*((b.val:ℂ)*(squarefreePrimeEnergy p.val:ℂ)))
  have hterm (x : Config N) :
      Complex.exp (-s*(finiteSquarefreeHamiltonian (packet N) x:ℂ)) = ∏ p, f p (x p) := by
    unfold finiteSquarefreeHamiltonian squarefreeBitEnergy
    push_cast
    rw [Finset.mul_sum,Complex.exp_sum]
  rw [Finset.sum_congr rfl (fun x _ => hterm x),← Fintype.prod_sum f,partition_bits]
  apply Finset.prod_congr rfl
  intro p _
  simp [Fin.sum_univ_two,f]

/-- Born probability of the all-empty output for a wave with damping x. -/
def vacuumProbability (N : ℕ) (x : ℝ) : ℝ := finiteSquarefreeBornWeight (packet N) (2*x) 0

theorem vacuumProbability_eq (N : ℕ) (x : ℝ) :
    (vacuumProbability N x : ℂ) = (partition N (2*(x:ℂ)))⁻¹ := by
  have he : finiteSquarefreeHamiltonian (packet N) (0 : Config N) = 0 := by
    simp [finiteSquarefreeHamiltonian,squarefreeBitEnergy]
  rw [vacuumProbability,finiteSquarefreeBornWeight_eq,he,mul_zero,Real.exp_zero,one_div,
    show 2*(x:ℂ) = ((2*x:ℝ):ℂ) by norm_cast,partition_real,Complex.ofReal_inv]

#print axioms readBits_vacuum_iff
#print axioms product_over_packet
#print axioms partition_bits
#print axioms partition_real
#print axioms partition_trace
#print axioms vacuumProbability_eq

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.Window
