import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.KoszulLocalizationDescent

/-! An ideal multiple descends from a localized lattice when the
localization denominator is invertible modulo the ideal. -/

noncomputable section

open scoped Pointwise

namespace GlobalTheory.WH

variable {R E : Type} [CommRing R] [AddCommGroup E] [Module R E]

/-- The intrinsic ideal multiple of a lattice identifies with its
ideal multiple in the ambient module. -/
theorem subtype_mem_ideal_smul_iff (I : Ideal R) (P : Submodule R E) {v : P} :
    v ∈ I • (⊤ : Submodule R P) ↔ (v : E) ∈ I • P := by
  have hmap : ((I • (⊤ : Submodule R P)).map P.subtype) = I • P := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  constructor
  · intro hv
    rw [← hmap]
    exact Submodule.mem_map_of_mem hv
  · intro hv
    rw [← hmap] at hv
    obtain ⟨u, hu, he⟩ := hv
    exact (Subtype.ext he) ▸ hu

/-- Clearing denominators in the lattice also clears denominators
in every ideal multiple of the lattice. -/
theorem exists_pow_smul_mem_ideal_smul_of_lattice
    (I : Ideal R) {P Q : Submodule R E} {a : R}
    (hden : ∀ v ∈ Q, ∃ n : ℕ, a ^ n • v ∈ P)
    {v : E} (hv : v ∈ I • Q) :
    ∃ n : ℕ, a ^ n • v ∈ I • P := by
  refine Submodule.smul_induction_on hv ?_ ?_
  · intro r hr u hu
    obtain ⟨n, hn⟩ := hden u hu
    refine ⟨n, ?_⟩
    rw [smul_comm]
    exact Submodule.smul_mem_smul hr hn
  · rintro u v ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    rw [smul_add]
    apply Submodule.add_mem
    · rw [add_comm m n, pow_add, mul_smul]
      exact (I • P).smul_mem _ hm
    · rw [pow_add, mul_smul]
      exact (I • P).smul_mem _ hn

/-- A denominator invertible modulo the ideal gives descent of ideal
membership for coefficients in the original lattice. -/
theorem mem_ideal_smul_of_localized_lattice
    (I : Ideal R) {P Q : Submodule R E} {a b : R}
    (hab : 1 - a * b ∈ I) (hden : ∀ v ∈ Q, ∃ n : ℕ, a ^ n • v ∈ P)
    {v : E} (hv : v ∈ P) (hv' : v ∈ I • Q) :
    v ∈ I • P := by
  obtain ⟨n, hn⟩ := exists_pow_smul_mem_ideal_smul_of_lattice I hden hv'
  exact mem_of_pow_smul_mem_of_one_sub_mul_smul_mem (I • P) hn
    (Submodule.smul_mem_smul hab hv)

end GlobalTheory.WH
