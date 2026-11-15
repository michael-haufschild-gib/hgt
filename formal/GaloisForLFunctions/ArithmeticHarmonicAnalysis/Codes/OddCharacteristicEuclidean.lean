import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.DivisibleSymbolOrthogonality

/-!
# Euclidean orthogonality in odd characteristic

The odd-characteristic criterion recalled by Heng–Xie (arXiv:2611.13963)
follows from vanishing unary moments. Ordinary polarization recovers the
bilinear pairing because two is nonzero in the coefficient field.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
variable {K ι : Type*} [Field K] [Fintype ι]

/-- In characteristic different from two, the diagonal determines a symmetric coordinate pairing. -/
theorem euclidean_selfOrthogonal_of_diagonal (h2 : (2 : K) ≠ 0)
    (C : Submodule K (ι → K))
    (hC : ∀ c ∈ C, twistedPair (RingHom.id K) c c = 0) :
    SelfOrthogonal (RingHom.id K) C := by
  intro c hc d hd
  have hsym : twistedPair (RingHom.id K) d c = twistedPair (RingHom.id K) c d := by
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm (d i) (c i)
  have hmix : twistedPair (RingHom.id K) d c + twistedPair (RingHom.id K) c d = 0 := by
    simpa only [twistedPair_add_smul, hC c hc, hC d hd, map_one,
      one_mul, mul_zero, zero_add, add_zero] using
      hC (c + (1 : K) • d) (C.add_mem hc (C.smul_mem 1 hd))
  rw [hsym, ← two_mul] at hmix
  exact (mul_eq_zero.mp hmix).resolve_left h2

/-- Characteristic-divisible codes containing one are Euclidean self-orthogonal in odd characteristic. -/
theorem oddCharacteristic_divisible_selfOrthogonal [Fintype K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : p ≠ 2)
    (C : Submodule K (ι → K)) (h1 : (fun _ => (1 : K)) ∈ C)
    (hC : Divisible p C) : SelfOrthogonal (RingHom.id K) C := by
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp h
    exact hp (Nat.le_antisymm (Nat.le_of_dvd (Nat.succ_pos 1) hd)
      (Fact.out : p.Prime).two_le)
  apply euclidean_selfOrthogonal_of_diagonal h2 C
  intro c hc
  exact sum_observable_eq_zero p C h1 hC c hc (fun a => a * a)

#print axioms oddCharacteristic_divisible_selfOrthogonal
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
