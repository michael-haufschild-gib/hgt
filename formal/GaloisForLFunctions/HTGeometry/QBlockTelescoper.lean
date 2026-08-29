import GaloisForLFunctions.HTGeometry.PrincipalPartScale

/-!
# The block telescoper of a `q`-orbit at one pole order

Inside one multiplicative orbit and one pole order the dilation acts as a weighted shift, so the
principal parts of a rational function are a coboundary exactly when their `q`-discrete residue
vanishes.  This file constructs the telescoper explicitly.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

open scoped RatFunc

noncomputable section

variable {K : Type*} [Field K]

/-- The telescoping coefficients solving `q^{-d}·B(n+1) − B n = A n` on a symmetric window. -/
def blockCoeff (q : K) (d N : ℕ) (A : ℤ → K) (n : ℤ) : K :=
  -((q ^ (d : ℤ)) ^ n) *
    ∑ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun m => n ≤ m),
      ((q ^ (-(d : ℤ))) ^ m) * A m

theorem blockCoeff_rec {q : K} (hq : q ≠ 0) (d N : ℕ) (A : ℤ → K)
    (hA : ∀ n : ℤ, n ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) → A n = 0) (n : ℤ) :
    (q ^ (-(d : ℤ))) * blockCoeff q d N A (n + 1) - blockCoeff q d N A n = A n := by
  classical
  have hmu0 : (q ^ (d : ℤ)) ≠ 0 := zpow_ne_zero _ hq
  have hlm : (q ^ (-(d : ℤ))) * (q ^ (d : ℤ)) = 1 := by
    rw [← zpow_add₀ hq, neg_add_cancel, zpow_zero]
  set T : ℤ → K := fun j => ∑ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun m => j ≤ m),
      ((q ^ (-(d : ℤ))) ^ m) * A m with hT
  have hdiff : ∀ j : ℤ, T j - T (j + 1)
      = if j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then ((q ^ (-(d : ℤ))) ^ j) * A j else 0 := by
    intro j
    by_cases hj : j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)
    · have hins : (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun m => j ≤ m)
          = insert j ((Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun m => j + 1 ≤ m)) := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_Icc] at hj ⊢
        constructor
        · rintro ⟨hm, hjm⟩
          rcases eq_or_lt_of_le hjm with h | h
          · exact Or.inl h.symm
          · exact Or.inr ⟨hm, by omega⟩
        · rintro (rfl | ⟨hm, hjm⟩)
          · exact ⟨hj, le_rfl⟩
          · exact ⟨hm, by omega⟩
      have hnotmem : j ∉ (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun m => j + 1 ≤ m) := by
        simp only [Finset.mem_filter]
        rintro ⟨-, h⟩
        omega
      rw [hT]
      simp only
      rw [hins, Finset.sum_insert hnotmem, if_pos hj]
      ring
    · have hset : (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun m => j ≤ m)
          = (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun m => j + 1 ≤ m) := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
        constructor
        · rintro ⟨hm, hjm⟩
          refine ⟨hm, ?_⟩
          rcases eq_or_lt_of_le hjm with h | h
          · exact absurd (by omega : -(N : ℤ) ≤ j ∧ j ≤ (N : ℤ)) (by simpa using hj)
          · omega
        · rintro ⟨hm, hjm⟩
          exact ⟨hm, by omega⟩
      rw [hT]
      simp only
      rw [hset, if_neg hj, sub_self]
  have hrec : (q ^ (-(d : ℤ))) * blockCoeff q d N A (n + 1) - blockCoeff q d N A n
      = ((q ^ (d : ℤ)) ^ n) * (T n - T (n + 1)) := by
    have hstep : (q ^ (-(d : ℤ))) * ((q ^ (d : ℤ)) ^ (n + 1)) = (q ^ (d : ℤ)) ^ n := by
      rw [zpow_add₀ hmu0, zpow_one, ← mul_assoc, mul_comm (q ^ (-(d : ℤ))), mul_assoc, hlm,
        mul_one]
    rw [blockCoeff, blockCoeff, hT]
    simp only
    rw [show (q ^ (-(d : ℤ))) *
        (-((q ^ (d : ℤ)) ^ (n + 1)) *
          ∑ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun m => n + 1 ≤ m),
            ((q ^ (-(d : ℤ))) ^ m) * A m)
        = -((q ^ (-(d : ℤ))) * ((q ^ (d : ℤ)) ^ (n + 1))) *
          ∑ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun m => n + 1 ≤ m),
            ((q ^ (-(d : ℤ))) ^ m) * A m from by ring, hstep]
    ring
  rw [hrec, hdiff n]
  by_cases hn : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)
  · rw [if_pos hn, ← mul_assoc, ← mul_zpow, mul_comm (q ^ (d : ℤ)), hlm, one_zpow, one_mul]
  · rw [if_neg hn, mul_zero, hA n hn]

theorem blockCoeff_eq_zero_of_gt {q : K} (d N : ℕ) (A : ℤ → K) {n : ℤ} (hn : (N : ℤ) < n) :
    blockCoeff q d N A n = 0 := by
  classical
  have hempty : (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun m => n ≤ m) = ∅ := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]
    rintro ⟨⟨-, hm⟩, hnm⟩
    omega
  rw [blockCoeff, hempty, Finset.sum_empty, mul_zero]

theorem blockCoeff_eq_zero_of_lt {q : K} (d N : ℕ) (A : ℤ → K)
    (hres : ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ((q ^ (-(d : ℤ))) ^ m) * A m = 0)
    {n : ℤ} (hn : n < -(N : ℤ)) :
    blockCoeff q d N A n = 0 := by
  classical
  have hall : (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun m => n ≤ m)
      = Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hm, -⟩
      exact hm
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2⟩, by omega⟩
  rw [blockCoeff, hall, hres, mul_zero]


/-- The block telescoper attached to one orbit and one pole order. -/
def blockTelescoper (q α : K) (d N : ℕ) (A : ℤ → K) : RatFunc K :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    algebraMap K (RatFunc K) (blockCoeff q d N A n) * invLinPow (α * q ^ n) d

theorem zpow_neg_natCast (q : K) (d : ℕ) : q ^ (-(d : ℤ)) = (q ^ d)⁻¹ := by
  rw [zpow_neg, zpow_natCast]

/-- **The block coboundary.**  When the `q`-discrete residue of the block vanishes, the block is
exactly the dilation coboundary of its telescoper. -/
theorem ratFuncScale_blockTelescoper_sub {q : K} (hq : q ≠ 0) (α : K) (d N : ℕ) (A : ℤ → K)
    (hA : ∀ n : ℤ, n ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) → A n = 0)
    (hres : ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ((q ^ (-(d : ℤ))) ^ m) * A m = 0) :
    ratFuncScale q hq (blockTelescoper q α d N A) - blockTelescoper q α d N A
      = ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          algebraMap K (RatFunc K) (A n) * invLinPow (α * q ^ n) d := by
  classical
  have hshift : ∀ n : ℤ, α * q ^ n / q = α * q ^ (n - 1) := by
    intro n
    rw [zpow_sub₀ hq, zpow_one, mul_div_assoc]
  have hσ : ratFuncScale q hq (blockTelescoper q α d N A)
      = ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          algebraMap K (RatFunc K) ((q ^ (-(d : ℤ))) * blockCoeff q d N A n)
            * invLinPow (α * q ^ (n - 1)) d := by
    rw [blockTelescoper, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, AlgHom.commutes, ratFuncScale_invLinPow hq, hshift n, zpow_neg_natCast, map_mul]
    ring
  -- reindex the shifted sum
  have hreindex : ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        algebraMap K (RatFunc K) ((q ^ (-(d : ℤ))) * blockCoeff q d N A n)
          * invLinPow (α * q ^ (n - 1)) d
      = ∑ m ∈ Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) - 1),
        algebraMap K (RatFunc K) ((q ^ (-(d : ℤ))) * blockCoeff q d N A (m + 1))
          * invLinPow (α * q ^ m) d := by
    have hmap : (Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) - 1)).map (addRightEmbedding (1 : ℤ))
        = Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      rw [Finset.map_add_right_Icc]
      congr 1 <;> ring
    rw [← hmap, Finset.sum_map]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [addRightEmbedding_apply]
    rw [show m + 1 - 1 = m from by ring]
  -- extend both sums to the common window
  have hV : ∀ f : ℤ → RatFunc K,
      (∀ n : ℤ, n ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) → f n = 0) →
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f n
        = ∑ n ∈ Finset.Icc (-(N : ℤ) - 1) (N : ℤ), f n := by
    intro f hf
    refine Finset.sum_subset ?_ fun n _ hn => hf n hn
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  have hV2 : ∀ f : ℤ → RatFunc K,
      (∀ n : ℤ, n ∉ Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) - 1) → f n = 0) →
      ∑ n ∈ Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) - 1), f n
        = ∑ n ∈ Finset.Icc (-(N : ℤ) - 1) (N : ℤ), f n := by
    intro f hf
    refine Finset.sum_subset ?_ fun n _ hn => hf n hn
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  have hbt : blockTelescoper q α d N A
      = ∑ n ∈ Finset.Icc (-(N : ℤ) - 1) (N : ℤ),
          algebraMap K (RatFunc K) (blockCoeff q d N A n) * invLinPow (α * q ^ n) d := by
    rw [blockTelescoper]
    refine hV _ fun n hn => ?_
    have hlt : n < -(N : ℤ) ∨ (N : ℤ) < n := by
      simp only [Finset.mem_Icc] at hn
      omega
    rcases hlt with h | h
    · rw [blockCoeff_eq_zero_of_lt d N A hres h, map_zero, zero_mul]
    · rw [blockCoeff_eq_zero_of_gt d N A h, map_zero, zero_mul]
  have hσ2 : ratFuncScale q hq (blockTelescoper q α d N A)
      = ∑ m ∈ Finset.Icc (-(N : ℤ) - 1) (N : ℤ),
          algebraMap K (RatFunc K) ((q ^ (-(d : ℤ))) * blockCoeff q d N A (m + 1))
            * invLinPow (α * q ^ m) d := by
    rw [hσ, hreindex]
    refine hV2 _ fun m hm => ?_
    have hcases : m + 1 < -(N : ℤ) ∨ (N : ℤ) < m + 1 := by
      by_contra hcon
      push Not at hcon
      exact hm (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    rcases hcases with h | h
    · rw [blockCoeff_eq_zero_of_lt d N A hres h, mul_zero, map_zero, zero_mul]
    · rw [blockCoeff_eq_zero_of_gt d N A h, mul_zero, map_zero, zero_mul]
  rw [hσ2, hbt, ← Finset.sum_sub_distrib]
  have hlast : ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      algebraMap K (RatFunc K) (A n) * invLinPow (α * q ^ n) d
      = ∑ n ∈ Finset.Icc (-(N : ℤ) - 1) (N : ℤ),
        algebraMap K (RatFunc K) (A n) * invLinPow (α * q ^ n) d :=
    hV _ fun n hn => by rw [hA n hn, map_zero, zero_mul]
  rw [hlast]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← sub_mul, ← map_sub, blockCoeff_rec hq d N A hA n]

end

end GaloisForLFunctions.HTGeometry
