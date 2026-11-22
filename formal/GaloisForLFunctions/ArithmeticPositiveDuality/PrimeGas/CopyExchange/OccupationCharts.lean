import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ParityOccupationCubes

/-!
# Two charts for the same prime occupation cubes

In exchange coordinates the common occupation at each prime is the minimum
of the two occupations. The residual is their absolute difference and its
orientation bit records which copy has the larger occupation.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange

open scoped Classical

private def exchangeEncode (x : Occupation × Occupation) : OccupationCube where
  residual := (x.1 - x.2) + (x.2 - x.1)
  pairs := x.1 ⊓ x.2
  bits := (x.2 - x.1).support
  allowed := by
    intro p hp
    rw [Finsupp.mem_support_iff, Finsupp.tsub_apply] at hp
    rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.tsub_apply]
    omega

private def exchangeDecode (c : OccupationCube) : Occupation × Occupation :=
  (c.pairs + c.residual.filter (fun p => p ∉ c.bits),
   c.pairs + c.residual.filter (fun p => p ∈ c.bits))

private theorem decode_encode (x : Occupation × Occupation) : exchangeDecode (exchangeEncode x) = x := by
  apply Prod.ext <;> apply Finsupp.ext <;> intro p <;>
    simp only [exchangeDecode, exchangeEncode, Finsupp.add_apply, Finsupp.filter_apply,
      Finsupp.inf_apply, Finsupp.mem_support_iff, Finsupp.tsub_apply, Nat.min_def] <;>
    split_ifs <;> omega

private theorem encode_decode (c : OccupationCube) : exchangeEncode (exchangeDecode c) = c := by
  apply OccupationCube.ext
  · apply Finsupp.ext
    intro p
    by_cases h : p ∈ c.bits <;>
      simp [exchangeEncode, exchangeDecode, h]
  · apply Finsupp.ext
    intro p
    by_cases h : p ∈ c.bits <;>
      simp [exchangeEncode, exchangeDecode, h]
  · ext p
    by_cases h : p ∈ c.bits
    · have ha := Finsupp.mem_support_iff.mp (c.allowed h)
      simp [exchangeEncode, exchangeDecode, Finsupp.mem_support_iff, h,ha]
    · simp [exchangeEncode, exchangeDecode, Finsupp.mem_support_iff,h]

/-- The orientation of the excess above the common occupation parametrizes all ordered pairs. -/
def exchangeCubes : (ℕ+ × ℕ+) ≃ OccupationCube :=
  (label.symm.prodCongr label.symm).trans
    ⟨exchangeEncode, exchangeDecode, decode_encode, encode_decode⟩

theorem exchange_total (c : OccupationCube) :
    (exchangeCubes.symm c).1 * (exchangeCubes.symm c).2 = label (c.residual + (c.pairs+c.pairs)) := by
  change label (exchangeDecode c).1 * label (exchangeDecode c).2 = _
  rw [← label_add]
  congr 1
  apply Finsupp.ext
  intro p
  by_cases h : p ∈ c.bits <;>
    simp [exchangeDecode,h] <;> omega

/-- The two charts agree on the physical shell, including all its prime occupations. -/
theorem exchange_shell (c : OccupationCube) :
    (exchangeCubes.symm c).1 * (exchangeCubes.symm c).2 = (pairCubes.symm c).1 * (pairCubes.symm c).2 :=
  (exchange_total c).trans (cube_product c).symm

/-- Occupations in the physical copies read directly in exchange coordinates. -/
theorem exchange_occupations (c : OccupationCube) (p : Nat.Primes) :
    label.symm (exchangeCubes.symm c).1 p = c.pairs p + (if p ∈ c.bits then 0 else c.residual p) ∧
    label.symm (exchangeCubes.symm c).2 p = c.pairs p + (if p ∈ c.bits then c.residual p else 0) := by
  change label.symm (label (exchangeDecode c).1) p = _ ∧ label.symm (label (exchangeDecode c).2) p = _
  by_cases h : p ∈ c.bits <;> simp [exchangeDecode,h]

/-- In the parity chart the bits are precisely the odd occupations in the second copy. -/
theorem parity_bit_iff (x : ℕ+ × ℕ+) (p : Nat.Primes) :
    p ∈ (pairCubes x).bits ↔ label.symm x.2 p % 2 = 1 := by
  change p ∈ (label.symm x.2).support.filter (fun q => label.symm x.2 q % 2 = 1) ↔ _
  rw [Finset.mem_filter, Finsupp.mem_support_iff]
  exact ⟨And.right,fun h => ⟨by intro hz; simp [hz] at h,h⟩⟩

def emptyCube (k : Occupation) : OccupationCube := ⟨0,k,∅,Finset.empty_subset _⟩

theorem empty_exchange (k : Occupation) : exchangeCubes.symm (emptyCube k) = (label k,label k) := by
  change (label (exchangeDecode _).1, label (exchangeDecode _).2) = _
  have hz (P : Nat.Primes → Prop) [DecidablePred P] : (0 : Occupation).filter P = 0 := by
    ext p
    simp [Finsupp.filter_apply]
  simp [exchangeDecode, emptyCube,hz]

theorem empty_parity (k : Occupation) : pairCubes.symm (emptyCube k) = squareState (label k) := by
  let e : Occupation := Finsupp.indicator (∅ : Finset Nat.Primes) (fun _ _ => (1 : ℕ))
  have hbit : e = 0 := by
    ext p
    simp [e,Finsupp.indicator_apply]
  change (label (0 - e), label (k+k+e)) = _
  rw [hbit, tsub_zero, add_zero, label_add]
  change (label 0, label k * label k) = (1, label k * label k)
  congr 1

#print axioms exchangeCubes
#print axioms exchange_shell
#print axioms exchange_occupations
#print axioms parity_bit_iff
#print axioms empty_exchange
#print axioms empty_parity

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange
