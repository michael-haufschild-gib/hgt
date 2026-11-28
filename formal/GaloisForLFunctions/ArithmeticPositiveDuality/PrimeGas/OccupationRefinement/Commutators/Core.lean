import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators.Coefficients

/-! # Measured creation and annihilation on the finite prime-occupation core -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators

open CoassociativeSplitting
open scoped ComplexConjugate

abbrev Occupation := Nat.Primes →₀ ℕ
abbrev Core := Occupation →₀ ℂ

def ket (m : Occupation) : Core := Finsupp.single m 1
def particle (p : Nat.Primes) : Occupation := Finsupp.single p 1

def lower (K : Kernel) (p : Nat.Primes) : Core →ₗ[ℂ] Core :=
  Finsupp.linearCombination ℂ fun m => ladder K p (m p) • ket (m - particle p)

def raise (K : Kernel) (p : Nat.Primes) : Core →ₗ[ℂ] Core :=
  Finsupp.linearCombination ℂ fun m => conj (ladder K p (m p+1)) • ket (m + particle p)

theorem lower_ket (K : Kernel) (p : Nat.Primes) (m : Occupation) :
    lower K p (ket m) = ladder K p (m p) • ket (m - particle p) := by
  rw [show ket m = Finsupp.single m 1 from rfl, lower, Finsupp.linearCombination_single, one_smul]

theorem raise_ket (K : Kernel) (p : Nat.Primes) (m : Occupation) :
    raise K p (ket m) = conj (ladder K p (m p+1)) • ket (m + particle p) := by
  rw [show ket m = Finsupp.single m 1 from rfl, raise, Finsupp.linearCombination_single, one_smul]

theorem add_count (m : Occupation) (p : Nat.Primes) : (m+particle p) p=m p+1 := by
  rw [Finsupp.add_apply,particle,Finsupp.single_eq_same]

theorem sub_count (m : Occupation) (p : Nat.Primes) : (m-particle p) p=m p-1 := by
  rw [Finsupp.tsub_apply,particle,Finsupp.single_eq_same]

theorem restore {m : Occupation} {p : Nat.Primes} (hm : m p≠0) : m-particle p+particle p=m :=
  tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hm))

/-- Every finite-core linear map is determined by its values on unit kets. -/
theorem core_ext {M : Type*} [AddCommMonoid M] [Module ℂ M] {T U : Core →ₗ[ℂ] M}
    (basis : ∀ m, T (ket m)=U (ket m)) : T=U := by
  apply Finsupp.lhom_ext
  intro m c
  have single : Finsupp.single m c = c • ket m := by rw [ket, Finsupp.smul_single', mul_one]
  rw [single, T.map_smul, U.map_smul, basis]

/-- Coordinates in the actual integer-labelled Hilbert space. -/
def embed : Core →ₗ[ℂ] Gas :=
  Finsupp.linearCombination ℂ fun m => lp.single 2 (label m) (1:ℂ)

theorem embed_ket (m : Occupation) : embed (ket m) = lp.single 2 (label m) (1:ℂ) := by
  rw [embed,ket,Finsupp.linearCombination_single,one_smul]

theorem ket_inner (m n : Occupation) : inner ℂ (embed (ket m)) (embed (ket n)) =
    if m=n then 1 else 0 := by
  classical
  rw [embed_ket,embed_ket,lp.inner_single_left,lp.single_apply,RCLike.inner_apply,map_one,mul_one]
  by_cases h : m=n
  · subst n
    simp
  · simp [h]

#print axioms lower_ket
#print axioms raise_ket
#print axioms ket_inner

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators
