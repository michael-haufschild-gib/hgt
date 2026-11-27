import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.Readings

/-! # Recovering the split damping and its isometry line from one-bit Gibbs comparisons -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell

open _root_.HTGeometry (finiteGibbsStateWeight)

/-- One bit computed from the centered negative logarithms of a Gibbs law. -/
def positiveBit {I : Type*} [Fintype I] (P : I → ℝ) :=
  0<oddTrace (centered (Observation.information P)) 1

def splitLaw (p : Nat.Primes) (A B : ℕ) (s : ℂ) :=
  finiteGibbsStateWeight (2*s.re-1) (primeModes p (occupation A B))

theorem bit_iff_response (p : Nat.Primes) (A B : ℕ) (s : ℂ) :
    positiveBit (splitLaw p A B s) ↔ 0<response p A B (2*s.re-1) := by
  let E := primeModes p (occupation A B)
  let d := 2*s.re-1
  have eq := funext (Observation.gibbs_information E d)
  change 0<oddTrace (centered (Observation.information (finiteGibbsStateWeight d E))) 1 ↔
    0<oddTrace (centered E) d
  rw [eq,centered_affine]
  simp only [oddTrace,oddTerm,one_mul,neg_mul]

/-- The real part of the composition parameter is identified from a family
of binary comparisons on the same three shells of a single prime. -/
theorem real_part_iff_bits (p : Nat.Primes) (s w : ℂ) :
    (∀ A B : ℕ, 0<B → (positiveBit (splitLaw p A B s) ↔ positiveBit (splitLaw p A B w))) ↔ s.re=w.re := by
  simp only [bit_iff_response]
  rw [readings_iff]
  constructor <;> intro h <;> linarith only [h]

/-- The critical line is exactly the common tie at which no probe records
a positive signed comparison. -/
theorem split_isometric_iff_bits (p : Nat.Primes) (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x) ↔
      ∀ A B : ℕ, 0<B → ¬positiveBit (splitLaw p A B s) := by
  rw [split_isometric_iff]
  have test := readings_iff p (2*s.re-1) 0
  have zero (A B : ℕ) : response p A B 0=0 := odd_zero _
  simp only [zero,lt_irrefl,iff_false] at test
  simp only [bit_iff_response]
  rw [test]
  constructor <;> intro h <;> linarith only [h]

#print axioms real_part_iff_bits
#print axioms split_isometric_iff_bits

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell
