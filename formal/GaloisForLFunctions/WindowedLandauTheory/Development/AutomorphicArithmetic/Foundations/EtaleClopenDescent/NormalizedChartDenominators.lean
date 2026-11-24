import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedIntersectionLocalization
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveCupResidue

/-! A regular element on an intersection can be cleared on a single
chart using only the ratios for the added chart indices. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

theorem chartRatio_mem_rB {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I)
    (j : Fin (d + 1)) : algebraMap F E (x j / x i) ∈ rB k E x I := by
  let a : rA k x I := ⟨x j / x i, Algebra.subset_adjoin ⟨i, hi, j, rfl⟩⟩
  exact isIntegral_algebraMap (x := a)

private theorem exists_pow_mul_mem_of_away {A C : Subalgebra k E}
    [Algebra A C] [IsScalarTower A C E] (u : A) [IsLocalization.Away u C] (b : C) :
    ∃ n : ℕ, (u : E) ^ n * (b : E) ∈ A := by
  obtain ⟨⟨a, ⟨w, n, rfl⟩⟩, he⟩ := IsLocalization.surj (Submonoid.powers u) b
  have h := congrArg (algebraMap C E) he
  simp only [map_mul, map_pow, ← IsScalarTower.algebraMap_apply A C E] at h
  change (b : E) * (u : E) ^ n = (a : E) at h
  refine ⟨n, ?_⟩
  rw [mul_comm ((u : E) ^ n) (b : E), h]
  exact a.property

/-- A power of the new coordinate ratio clears a regular function
on the intersection of two normalized charts. -/
theorem IsPd.exists_pow_mul_mem_rB (h : IsPd k x) (i j : Fin (d + 1)) (b : E)
    (hb : b ∈ rB k E x {i, j}) :
    ∃ n : ℕ, algebraMap F E (x i / x j) ^ n * b ∈ rB k E x {j} := by
  by_cases hij : i = j
  · subst i
    refine ⟨0, ?_⟩
    have hset : ({j, j} : Finset (Fin (d + 1))) = {j} :=
      Finset.insert_eq_of_mem (Finset.mem_singleton_self j)
    simpa only [pow_zero, one_mul, hset] using hb
  let A := rA k x {j}
  let B := rB k E x {j}
  let C := rB k E x {i, j}
  let s := chartDenominator k x {i, j} j
  let u : B := algebraMap A (integralClosure A E) s
  have hj : j ∈ ({i, j} : Finset (Fin (d + 1))) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self j)
  letI : Algebra B C := normalizedIntersectionAlgebra (k := k) (x := x) (E := E) hj
  letI : IsScalarTower B C E := normalizedIntersection_tower (k := k) (x := x) (E := E) hj
  letI : IsLocalization.Away u C := normalizedIntersection_isLocalization (E := E) h hj
  obtain ⟨n, hn⟩ := exists_pow_mul_mem_of_away u (⟨b, hb⟩ : C)
  have hs : (s : F) = x i / x j := by
    simp only [s, chartDenominator, Finset.prod_pair hij, div_self (h.ne j), mul_one]
  have hu : (u : E) = algebraMap F E (x i / x j) :=
    congrArg (algebraMap F E) hs
  refine ⟨n, ?_⟩
  have hnu : (u : E) ^ n * b ∈ rB k E x {j} := hn
  rwa [hu] at hnu

/-- A function regular on one chart has a common denominator bound
for passage to any of the other charts. -/
theorem IsPd.exists_uniform_pow_mul_mem_rB (h : IsPd k x) (i : Fin (d + 1)) (b : E)
    (hb : b ∈ rB k E x {i}) :
    ∃ N : ℕ, ∀ j : Fin (d + 1), algebraMap F E (x i / x j) ^ N * b ∈ rB k E x {j} := by
  have hex (j : Fin (d + 1)) := h.exists_pow_mul_mem_rB i j b
    (rB_mono (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self i {j})) hb)
  choose N hN using hex
  refine ⟨Finset.univ.sup N, fun j => ?_⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := N) (Finset.mem_univ j))
  rw [hm, pow_add, mul_assoc, mul_left_comm]
  exact mul_mem (pow_mem (chartRatio_mem_rB (k := k) (Finset.mem_singleton_self j) i) m) (hN j)

end GlobalTheory.PD
