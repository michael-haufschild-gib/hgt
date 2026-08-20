import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# Reciprocals of distinct nonzero integers

A finite set of `r` distinct positive integers has reciprocal sum at most the `r`-th harmonic
number, because its largest element is at least `r`.  Splitting by sign, a family of `r` *distinct
nonzero integers* has reciprocal-of-absolute-value sum at most `2(1 + log r)`.

This is the combinatorial engine behind every off-diagonal estimate for a mean value of Dirichlet
polynomials: the frequencies attached to distinct terms differ by distinct nonzero integers.
-/

open Finset

noncomputable section

namespace RHTower.Sieve

/-- A finite set of positive integers has reciprocal sum at most the harmonic number of its
cardinality. -/
theorem sum_inv_le_sum_Icc (A : Finset ℕ) (hA : ∀ a ∈ A, 1 ≤ a) :
    ∑ a ∈ A, (1 : ℝ) / a ≤ ∑ j ∈ Finset.Icc 1 A.card, (1 : ℝ) / j := by
  classical
  induction A using Finset.strongInduction with
  | _ A ih =>
    rcases A.eq_empty_or_nonempty with rfl | hne
    · simp
    · have hMmem : A.max' hne ∈ A := A.max'_mem hne
      set M : ℕ := A.max' hne with hM
      have hsub : A ⊆ Finset.Icc 1 M := fun a ha =>
        Finset.mem_Icc.mpr ⟨hA a ha, A.le_max' a ha⟩
      have hcardle : A.card ≤ M := by
        have h := Finset.card_le_card hsub
        simpa [Nat.card_Icc] using h
      have hcardpos : 0 < A.card := Finset.card_pos.mpr hne
      have herase := ih (A.erase M) (Finset.erase_ssubset hMmem)
        (fun a ha => hA a (Finset.mem_of_mem_erase ha))
      have hcarderase : (A.erase M).card = A.card - 1 := Finset.card_erase_of_mem hMmem
      have hsplit : ∑ a ∈ A, (1 : ℝ) / a
          = (1 : ℝ) / M + ∑ a ∈ A.erase M, (1 : ℝ) / a :=
        (Finset.add_sum_erase A (fun a : ℕ => (1 : ℝ) / a) hMmem).symm
      have hMinv : (1 : ℝ) / M ≤ (1 : ℝ) / A.card := by
        refine one_div_le_one_div_of_le ?_ ?_
        · exact_mod_cast hcardpos
        · exact_mod_cast hcardle
      have htop : ∑ j ∈ Finset.Icc 1 A.card, (1 : ℝ) / j
          = (1 : ℝ) / A.card + ∑ j ∈ Finset.Icc 1 (A.card - 1), (1 : ℝ) / j := by
        have hcard : Finset.Icc 1 A.card = insert A.card (Finset.Icc 1 (A.card - 1)) := by
          ext j
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        rw [hcard, Finset.sum_insert (by simp)]
      rw [hcarderase] at herase
      rw [hsplit, htop]
      linarith [herase, hMinv]

theorem sum_inv_le_one_add_log (A : Finset ℕ) (hA : ∀ a ∈ A, 1 ≤ a) :
    ∑ a ∈ A, (1 : ℝ) / a ≤ 1 + Real.log A.card :=
  le_trans (sum_inv_le_sum_Icc A hA) (sum_Icc_one_div_le_one_add_log A.card)

private theorem sum_inv_abs_signed_le {ι : Type*} [DecidableEq ι] (s t : Finset ι)
    (v w : ι → ℤ) (hts : t ⊆ s)
    (hwinj : ∀ i ∈ t, ∀ j ∈ t, w i = w j → i = j)
    (hwpos : ∀ i ∈ t, 0 < w i)
    (hwabs : ∀ i ∈ t, ((w i).toNat : ℝ) = |((v i : ℤ) : ℝ)|) :
    ∑ i ∈ t, (1 : ℝ) / |((v i : ℤ) : ℝ)| ≤ 1 + Real.log s.card := by
  classical
  have hinjt : ∀ i ∈ t, ∀ j ∈ t, (w i).toNat = (w j).toNat → i = j := by
    intro i hi j hj heq
    refine hwinj i hi j hj ?_
    have hi' : ((w i).toNat : ℤ) = w i := Int.toNat_of_nonneg (hwpos i hi).le
    have hj' : ((w j).toNat : ℤ) = w j := Int.toNat_of_nonneg (hwpos j hj).le
    rw [← hi', ← hj', heq]
  set A : Finset ℕ := t.image (fun i => (w i).toNat) with hA
  have hA1 : ∀ a ∈ A, 1 ≤ a := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    have := hwpos i hi
    omega
  have hcardA : A.card = t.card :=
    Finset.card_image_of_injOn (fun i hi j hj => hinjt i hi j hj)
  have hsum : ∑ a ∈ A, (1 : ℝ) / a = ∑ i ∈ t, (1 : ℝ) / |((v i : ℤ) : ℝ)| := by
    rw [hA, Finset.sum_image (fun i hi j hj => hinjt i hi j hj)]
    exact Finset.sum_congr rfl fun i hi => by rw [hwabs i hi]
  have hbound := sum_inv_le_one_add_log A hA1
  rw [hsum, hcardA] at hbound
  refine le_trans hbound ?_
  have hcard : t.card ≤ s.card := Finset.card_le_card hts
  have hmono : Real.log t.card ≤ Real.log s.card := by
    rcases Nat.eq_zero_or_pos t.card with h0 | hpos
    · rw [h0]
      simpa using Real.log_natCast_nonneg s.card
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)
  linarith

/-- **Reciprocals of distinct nonzero integers.** -/
theorem sum_inv_abs_le_of_injOn {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ℤ)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, v i = v j → i = j) (hne : ∀ i ∈ s, v i ≠ 0) :
    ∑ i ∈ s, (1 : ℝ) / |((v i : ℤ) : ℝ)| ≤ 2 * (1 + Real.log s.card) := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun i => 0 < v i)
    (fun i => (1 : ℝ) / |((v i : ℤ) : ℝ)|)
  have hpos := sum_inv_abs_signed_le s (s.filter (fun i => 0 < v i)) v v
    (Finset.filter_subset _ _)
    (fun i hi j hj heq =>
      hinj i (Finset.mem_of_mem_filter i hi) j (Finset.mem_of_mem_filter j hj) heq)
    (fun i hi => (Finset.mem_filter.mp hi).2)
    (fun i hi => by
      have h := (Finset.mem_filter.mp hi).2
      have h1 : ((v i).toNat : ℤ) = v i := Int.toNat_of_nonneg h.le
      have h2 : ((v i).toNat : ℝ) = ((v i : ℤ) : ℝ) := by exact_mod_cast h1
      rw [h2, abs_of_pos (by exact_mod_cast h)])
  have hneg := sum_inv_abs_signed_le s (s.filter (fun i => ¬ (0 < v i))) v (fun i => -v i)
    (Finset.filter_subset _ _)
    (fun i hi j hj heq =>
      hinj i (Finset.mem_of_mem_filter i hi) j (Finset.mem_of_mem_filter j hj) (by omega))
    (fun i hi => by
      obtain ⟨his, hnp⟩ := Finset.mem_filter.mp hi
      have hv0 : v i ≠ 0 := hne i his
      omega)
    (fun i hi => by
      obtain ⟨his, hnp⟩ := Finset.mem_filter.mp hi
      have hv0 : v i ≠ 0 := hne i his
      have hvneg : v i < 0 := by omega
      have h1 : ((-v i).toNat : ℤ) = -v i := Int.toNat_of_nonneg (by omega)
      have h2 : ((-v i).toNat : ℝ) = -((v i : ℤ) : ℝ) := by exact_mod_cast h1
      rw [h2, abs_of_neg (by exact_mod_cast hvneg)])
  linarith [hsplit, hpos, hneg]

end RHTower.Sieve

end
