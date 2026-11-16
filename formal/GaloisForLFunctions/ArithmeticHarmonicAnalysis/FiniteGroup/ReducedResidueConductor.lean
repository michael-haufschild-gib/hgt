import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.ReducedResiduePoleOrders
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.WeightedResidueConductor

/-!
# Sharp bounds for reduced residue weights

Multiplication residues are divisible by the common divisor of their
multiplier and modulus. Their maximum is therefore at most `N-gcd(N,R)`.
The corresponding weight bound is attained only at the last index,
with a maximal multiplication residue.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- A multiplication residue is at most the modulus minus the common divisor. -/
theorem mul_mod_le_sub_gcd (N R i : ℕ) (hN : 0 < N) :
    i * R % N ≤ N - Nat.gcd N R := by
  have hdN := Nat.gcd_dvd_left N R
  have hdR := Nat.gcd_dvd_right N R
  have hdres : Nat.gcd N R ∣ i * R % N :=
    (Nat.dvd_mod_iff hdN).mpr (dvd_mul_of_dvd_right hdR i)
  have hdsub : Nat.gcd N R ∣ N - i * R % N := Nat.dvd_sub hdN hdres
  have hlt := Nat.mod_lt (i * R) hN
  have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hdsub
  omega

/-- Every reduced weight lies below its exact arithmetic conductor bound. -/
theorem reducedResidue_weight_bound (N m R : ℕ) (hN : 0 < N) (i : Fin N) :
    i.val + m * (i.val * R % N) ≤ m * (N - Nat.gcd N R) + N - 1 := by
  have hres := Nat.mul_le_mul_left m (mul_mod_le_sub_gcd N R i.val hN)
  have hi := i.isLt
  omega

/-- A reduced weight attains the bound exactly at the last index with a maximal multiplication residue. -/
theorem reducedResidue_weight_bound_eq_iff (N m R : ℕ) (hN : 0 < N) (hm : 0 < m)
    (i : Fin N) :
    i.val + m * (i.val * R % N) = m * (N - Nat.gcd N R) + N - 1 ↔
      i.val = N - 1 ∧ i.val * R % N = N - Nat.gcd N R := by
  have hres := mul_mod_le_sub_gcd N R i.val hN
  have hmul := Nat.mul_le_mul_left m hres
  have hi := i.isLt
  constructor
  · intro h
    have hi' : i.val = N - 1 := by omega
    have heq : m * (i.val * R % N) = m * (N - Nat.gcd N R) := by omega
    exact ⟨hi', Nat.eq_of_mul_eq_mul_left hm heq⟩
  · rintro ⟨hi', hres'⟩
    rw [hres', hi']
    omega

/-- The final possible gap is present exactly when the last multiplication residue is maximal. -/
theorem reducedResidue_last_gap_iff (N m R : ℕ) (hN : 0 < N) (hm : 0 < m)
    (hcop : Nat.Coprime (1 + m * R) N) (hB : 0 < m * (N - Nat.gcd N R)) :
    (¬ ∃ i : Fin N, ∃ k : ℕ,
      N * k + (i.val + m * (i.val * R % N)) = m * (N - Nat.gcd N R) - 1) ↔
      (N - 1) * R % N = N - Nat.gcd N R := by
  let D : Fin N → ℕ := fun i => i.val + m * (i.val * R % N)
  have hresidue (i j : Fin N) (h : D i % N = D j % N) : i = j := by
    dsimp only [D] at h
    rw [reducedResidue_mod, reducedResidue_mod] at h
    have hmod : Nat.ModEq N i.val j.val := Nat.ModEq.cancel_left_of_coprime hcop.symm h
    exact Fin.ext (hmod.eq_of_lt_of_lt i.isLt j.isLt)
  rw [weightedResidue_last_gap_iff hN D hresidue _ hB
    (fun i => reducedResidue_weight_bound N m R hN i)]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨hi', hres⟩ := (reducedResidue_weight_bound_eq_iff N m R hN hm i).mp hi
    rwa [hi'] at hres
  · intro h
    let i : Fin N := ⟨N - 1, Nat.sub_lt hN Nat.zero_lt_one⟩
    exact ⟨i, (reducedResidue_weight_bound_eq_iff N m R hN hm i).mpr ⟨rfl, h⟩⟩

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
