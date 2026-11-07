import GaloisForLFunctions.RigidArithmeticOfCuts.AnExactCountForcesTheRationalPrimes
import GaloisForLFunctions.RHTower.BeurlingSystemCounting

/-!
# Amplifying norm collisions

A relation between two free factorizations yields arbitrarily many factorizations
of powers of their common norm. Uniformly bounded multiplicities therefore force
unique factorization. No distributional or analytic input is used.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

open GaloisForLFunctions.RigidArithmeticOfCuts

/-- Distinct multiset endpoints give distinct points on every integer segment. -/
theorem multisetSegment_injective {α : Type*} (u v : Multiset α) (hne : u ≠ v) (k : ℕ) :
    Function.Injective (fun j : Fin (k + 1) => (j : ℕ) • u + (k - j) • v) := by
  classical
  intro i j hij
  by_cases heq : i = j
  · exact heq
  · exfalso
    apply hne
    ext a
    have hc := congrArg (Multiset.count a) hij
    simp only [Multiset.count_add, Multiset.count_nsmul] at hc
    have hc' : (i : ℕ) * (u.count a : ℤ) + (k - (i : ℕ) : ℕ) * (v.count a : ℤ) =
        (j : ℕ) * (u.count a : ℤ) + (k - (j : ℕ) : ℕ) * (v.count a : ℤ) := by
      exact_mod_cast hc
    have hi : ((k - (i : ℕ) : ℕ) : ℤ) = (k : ℤ) - (i : ℕ) := by omega
    have hj : ((k - (j : ℕ) : ℕ) : ℤ) = (k : ℤ) - (j : ℕ) := by omega
    rw [hi, hj] at hc'
    have hf : (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * ((u.count a : ℤ) - v.count a) = 0 := by
      nlinarith only [hc']
    have hneij : (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ≠ 0 := by
      intro h
      apply heq
      apply Fin.ext
      omega
    have := sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left hneij)
    exact_mod_cast this

/-- Repeated addition of a factorization raises its norm to the corresponding power. -/
private theorem intNorm_nsmul (B : RHTower.BeurlingSystem)
    (g : B.Integer) (k : ℕ) : B.intNorm (k • g) = B.intNorm g ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, B.intNorm_add, ih, pow_succ]

/-- A norm collision produces k+1 distinct factorizations of the k-th power. -/
theorem exists_norm_fibre_of_card_succ (B : RHTower.BeurlingSystem) (u v : B.Integer)
    (hne : u ≠ v) (huv : B.intNorm u = B.intNorm v) (k : ℕ) :
    ∃ S : Finset B.Integer, S.card = k + 1 ∧
      ∀ g ∈ S, B.intNorm g = B.intNorm u ^ k := by
  classical
  let f (j : Fin (k + 1)) := (j : ℕ) • u + (k - j) • v
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (multisetSegment_injective u v hne k)]
    simp only [Finset.card_univ, Fintype.card_fin]
  · intro g hg
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hg
    dsimp only [f]
    rw [B.intNorm_add, intNorm_nsmul, intNorm_nsmul, ← huv, ← pow_add]
    congr 1
    omega

/-- Uniform bounds for finite subsets of norm fibres force unique factorization. -/
theorem uniform_finite_fibres_iff_norm_injective (B : RHTower.BeurlingSystem) :
    (∃ C : ℕ, ∀ x : ℝ, ∀ S : Finset B.Integer,
      (∀ g ∈ S, B.intNorm g = x) → S.card ≤ C) ↔ Function.Injective B.intNorm := by
  classical
  constructor
  · rintro ⟨C, hC⟩ u v huv
    by_contra hne
    obtain ⟨S, hS, hnS⟩ := exists_norm_fibre_of_card_succ B u v hne huv C
    have := hC (B.intNorm u ^ C) S hnS
    omega
  · intro hinj
    refine ⟨1, fun x S hS => Finset.card_le_one.mpr ?_⟩
    intro u hu v hv
    exact hinj ((hS u hu).trans (hS v hv).symm)

/-- Integer generator norms give positive integer norms for every factorization. -/
theorem exists_nat_intNorm (B : RHTower.BeurlingSystem) (h : HasIntegerNorms B)
    (g : B.Integer) : ∃ n : ℕ, 1 ≤ n ∧ B.intNorm g = n := by
  classical
  induction g using Multiset.induction_on with
  | empty => exact ⟨1, le_rfl, by simp⟩
  | cons p g ih =>
    obtain ⟨n, hn, hgn⟩ := ih
    obtain ⟨m, hm⟩ := h p
    have hm1 : 1 ≤ m := by
      have hp := B.one_lt_labelNorm p
      rw [hm] at hp
      have : 1 < m := by exact_mod_cast hp
      omega
    refine ⟨m * n, Nat.mul_pos hm1 hn, ?_⟩
    rw [← Multiset.singleton_add, B.intNorm_add, B.intNorm_singleton, hm, hgn]
    exact (Nat.cast_mul m n).symm

/-- Local finiteness transfers collision amplification to the norm multiplicity. -/
theorem intCount_pow_ge_of_collision (B : RHTower.BeurlingSystem) (hdisc : B.IsDiscrete)
    {u v : B.Integer} (hne : u ≠ v) (huv : B.intNorm u = B.intNorm v)
    {m : ℕ} (hmu : B.intNorm u = m) (k : ℕ) : k + 1 ≤ intCount B (m ^ k) := by
  classical
  obtain ⟨S, hS, hnS⟩ := exists_norm_fibre_of_card_succ B u v hne huv k
  have hfinite : {g : B.Integer | B.intNorm g = ((m ^ k : ℕ) : ℝ)}.Finite :=
    (hdisc ((m ^ k : ℕ) : ℝ)).subset (fun g hg => hg.le)
  rw [← hS, intCount, Set.ncard_eq_toFinset_card _ hfinite]
  apply Finset.card_le_card
  intro g hg
  rw [Set.Finite.mem_toFinset]
  have hnorm := hnS g hg
  rw [hmu] at hnorm
  simpa only [Set.mem_setOf_eq, Nat.cast_pow] using hnorm

/-- Bounded integer multiplicities are equivalent to injectivity of the norm. -/
theorem bounded_intCount_iff_norm_injective (B : RHTower.BeurlingSystem)
    (h : HasIntegerNorms B) (hdisc : B.IsDiscrete) :
    (∃ C : ℕ, ∀ n, 1 ≤ n → intCount B n ≤ C) ↔ Function.Injective B.intNorm := by
  classical
  constructor
  · rintro ⟨C, hC⟩ u v huv
    by_contra hne
    obtain ⟨m, hm, hmu⟩ := exists_nat_intNorm B h u
    have hcard := intCount_pow_ge_of_collision B hdisc hne huv hmu C
    have hp : 0 < m ^ C := pow_pos (by omega) C
    have hb := hC (m ^ C) hp
    omega
  · intro hinj
    refine ⟨1, fun n _ => ?_⟩
    have hs : {g : B.Integer | B.intNorm g = (n : ℝ)}.Subsingleton :=
      fun u hu v hv => hinj (hu.trans hv.symm)
    exact (Set.ncard_le_one hs.finite).mpr fun a ha b hb => hs ha hb

/-- A common integer norm of distinct factorizations is at least two. -/
theorem collision_norm_ge_two (B : RHTower.BeurlingSystem)
    {u v : B.Integer} (hne : u ≠ v) (huv : B.intNorm u = B.intNorm v)
    {m : ℕ} (hmu : B.intNorm u = m) : 2 ≤ m := by
  classical
  have hex : ∃ g : B.Integer, g ≠ 0 ∧ B.intNorm g = m := by
    by_cases hu : u = 0
    · exact ⟨v, fun hv => hne (hu.trans hv.symm), huv.symm.trans hmu⟩
    · exact ⟨u, hu, hmu⟩
  obtain ⟨g, hg, hgm⟩ := hex
  obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero hg
  obtain ⟨g', he⟩ := Multiset.exists_cons_of_mem hp
  rw [he, ← Multiset.singleton_add, B.intNorm_add, B.intNorm_singleton] at hgm
  have hgp := B.one_le_intNorm g'
  have hpp := B.one_lt_labelNorm p
  have hmul := mul_le_mul_of_nonneg_left hgp (show 0 ≤ B.labelNorm p by linarith only [hpp])
  simp only [mul_one] at hmul
  have hm : (1 : ℝ) < m := by linarith only [hpp, hmul, hgm]
  exact_mod_cast hm

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
