import GaloisForLFunctions.RHTower.Sieve.HuxleyExplicitLargeValues

/-!
# Huxley's large-values theorem over a general multiplicative range
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- One term of a Dirichlet polynomial on the line `sigma`. -/
noncomputable def rangeTerm (c : ℕ → ℂ) (sigma t : ℝ) (n : ℕ) : ℂ :=
  c n * (((n : ℝ) ^ (-sigma) : ℝ) : ℂ) *
    Complex.exp (((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I)

theorem blockPoly_eq_sum_rangeTerm (N : ℕ) (c : ℕ → ℂ) (sigma t : ℝ) :
    blockPoly N c sigma t = ∑ n ∈ Finset.Ico N (2 * N), rangeTerm c sigma t n := rfl

/-- **The dyadic decomposition of a range polynomial.**  A range of multiplicative width `2^J` is
the disjoint union of `J` dyadic blocks. -/
theorem sum_blockPoly_eq_range (A : ℕ) (c : ℕ → ℂ) (sigma t : ℝ) (J : ℕ) :
    ∑ j ∈ Finset.range J, blockPoly (A * 2 ^ j) c sigma t
      = ∑ n ∈ Finset.Ico A (A * 2 ^ J), rangeTerm c sigma t n := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, blockPoly_eq_sum_rangeTerm]
    have hmul : 2 * (A * 2 ^ J) = A * 2 ^ (J + 1) := by ring
    rw [hmul]
    have hpow : 0 < (2 : ℕ) ^ J := Nat.two_pow_pos J
    have h1 : A ≤ A * 2 ^ J := Nat.le_mul_of_pos_right A hpow
    have h2 : A * 2 ^ J ≤ A * 2 ^ (J + 1) := by
      have : (2 : ℕ) ^ J ≤ 2 ^ (J + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact Nat.mul_le_mul_left A this
    exact Finset.sum_Ico_consecutive _ h1 h2

/-- **Pigeonhole across the dyadic blocks.**  If the range polynomial is large then one of its
`J` dyadic blocks is large at threshold `V/J`. -/
theorem exists_block_large {A J : ℕ} (hJ : 1 ≤ J) (c : ℕ → ℂ) {sigma t V : ℝ}
    (hbig : V ≤ ‖∑ n ∈ Finset.Ico A (A * 2 ^ J), rangeTerm c sigma t n‖) :
    ∃ j ∈ Finset.range J, V / (J : ℝ) ≤ ‖blockPoly (A * 2 ^ j) c sigma t‖ := by
  by_contra hcon
  push Not at hcon
  have hJ0 : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have htri : ‖∑ j ∈ Finset.range J, blockPoly (A * 2 ^ j) c sigma t‖
      ≤ ∑ j ∈ Finset.range J, ‖blockPoly (A * 2 ^ j) c sigma t‖ :=
    norm_sum_le _ _
  have hlt : ∑ j ∈ Finset.range J, ‖blockPoly (A * 2 ^ j) c sigma t‖
      < ∑ _j ∈ Finset.range J, V / (J : ℝ) := by
    refine Finset.sum_lt_sum_of_nonempty ?_ ?_
    · exact Finset.nonempty_range_iff.2 (by omega)
    · intro j hj
      exact hcon j hj
  have hval : ∑ _j ∈ Finset.range J, V / (J : ℝ) = V := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  rw [hval] at hlt
  rw [sum_blockPoly_eq_range A c sigma t J] at htri
  linarith

/-- **Huxley's large-values theorem over a range of multiplicative width `2^J`.**  Splitting into
`J` dyadic blocks and paying the pigeonhole factor `J` in the threshold, the count over the range is
at most the sum of the block counts at threshold `V/J`. -/
theorem huxley_range_large_values {A J : ℕ} (hA : 1 ≤ A) (hJ : 1 ≤ J) (c : ℕ → ℂ)
    {delta Ttot V D : ℝ} (hdelta : 0 < delta) (hV : 0 < V) (hTtot : 0 ≤ Ttot) (hD : 0 ≤ D)
    (hc : ∀ j ∈ Finset.range J,
      ∀ n ∈ Finset.Ico (A * 2 ^ j) (2 * (A * 2 ^ j)), ‖c n‖ ≤ D)
    (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → delta ≤ |x - y|)
    (hspread : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ Ttot)
    (hbig : ∀ x ∈ S, V ≤ ‖∑ n ∈ Finset.Ico A (A * 2 ^ J), rangeTerm c 1 x n‖)
    (hthresh : ∀ j ∈ Finset.range J,
      (D ^ 2 / ((A * 2 ^ j : ℕ) : ℝ))
          * (1 + 1536 * Real.sqrt (3 * ((A * 2 ^ j : ℕ) : ℝ) / (4 * Real.pi)))
        ≤ (V / (J : ℝ)) ^ 2 / 3) :
    ((S.card : ℝ)) * (V / (J : ℝ)) ^ 2
      ≤ ∑ j ∈ Finset.range J,
        (1648656 * Ttot * D ^ 4 / (((A * 2 ^ j : ℕ) : ℝ) ^ 2 * (V / (J : ℝ)) ^ 4) + 1)
          * (2 * D ^ 2 * (1 + 12 * Real.pi * (1 + Real.log (Ttot / delta + 1)) / delta)) := by
  classical
  have hJ0 : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hVJ : (0 : ℝ) < V / (J : ℝ) := by positivity
  set P : ℕ → ℝ → Prop := fun j x => V / (J : ℝ) ≤ ‖blockPoly (A * 2 ^ j) c 1 x‖ with hP
  have hcover : S ⊆ (Finset.range J).biUnion (fun j => S.filter (fun x => P j x)) := by
    intro x hx
    obtain ⟨j, hj, hjx⟩ := exists_block_large hJ c (hbig x hx)
    exact Finset.mem_biUnion.2 ⟨j, hj, Finset.mem_filter.2 ⟨hx, hjx⟩⟩
  have hcard : (S.card : ℝ)
      ≤ ∑ j ∈ Finset.range J, ((S.filter (fun x => P j x)).card : ℝ) := by
    have h1 : S.card ≤ ∑ j ∈ Finset.range J, (S.filter (fun x => P j x)).card :=
      le_trans (Finset.card_le_card hcover) (Finset.card_biUnion_le)
    exact_mod_cast h1
  have hstep : ∀ j ∈ Finset.range J,
      ((S.filter (fun x => P j x)).card : ℝ) * (V / (J : ℝ)) ^ 2
        ≤ (1648656 * Ttot * D ^ 4 / (((A * 2 ^ j : ℕ) : ℝ) ^ 2 * (V / (J : ℝ)) ^ 4) + 1)
          * (2 * D ^ 2 * (1 + 12 * Real.pi * (1 + Real.log (Ttot / delta + 1)) / delta)) := by
    intro j hj
    have hA0 : 1 ≤ A * 2 ^ j := Nat.one_le_iff_ne_zero.2 (by positivity)
    refine huxley_block_large_values_explicit hA0 c hdelta hVJ hTtot hD (hc j hj) _
      (fun x hx y hy hxy => hsep x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1 hxy)
      (fun x hx y hy => hspread x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1)
      (fun x hx => (Finset.mem_filter.1 hx).2) (hthresh j hj)
  calc ((S.card : ℝ)) * (V / (J : ℝ)) ^ 2
      ≤ (∑ j ∈ Finset.range J, ((S.filter (fun x => P j x)).card : ℝ)) * (V / (J : ℝ)) ^ 2 := by
        exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ∑ j ∈ Finset.range J, ((S.filter (fun x => P j x)).card : ℝ) * (V / (J : ℝ)) ^ 2 := by
        rw [Finset.sum_mul]
    _ ≤ _ := Finset.sum_le_sum hstep

/-- **The range count against the shortest block.**  Every block bound is largest at the shortest
block, so the sum over the `J` dyadic blocks is at most `J` times the bound at length `A`.  This is
the form in which the range estimate matches the dyadic one. -/
theorem huxley_range_large_values_uniform {A J : ℕ} (hA : 1 ≤ A) (hJ : 1 ≤ J) (c : ℕ → ℂ)
    {delta Ttot V D : ℝ} (hdelta : 0 < delta) (hV : 0 < V) (hTtot : 0 ≤ Ttot) (hD : 0 ≤ D)
    (hc : ∀ j ∈ Finset.range J,
      ∀ n ∈ Finset.Ico (A * 2 ^ j) (2 * (A * 2 ^ j)), ‖c n‖ ≤ D)
    (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → delta ≤ |x - y|)
    (hspread : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ Ttot)
    (hbig : ∀ x ∈ S, V ≤ ‖∑ n ∈ Finset.Ico A (A * 2 ^ J), rangeTerm c 1 x n‖)
    (hthresh : ∀ j ∈ Finset.range J,
      (D ^ 2 / ((A * 2 ^ j : ℕ) : ℝ))
          * (1 + 1536 * Real.sqrt (3 * ((A * 2 ^ j : ℕ) : ℝ) / (4 * Real.pi)))
        ≤ (V / (J : ℝ)) ^ 2 / 3) :
    ((S.card : ℝ)) * (V / (J : ℝ)) ^ 2
      ≤ (J : ℝ) * ((1648656 * Ttot * D ^ 4 / ((A : ℝ) ^ 2 * (V / (J : ℝ)) ^ 4) + 1)
          * (2 * D ^ 2 * (1 + 12 * Real.pi * (1 + Real.log (Ttot / delta + 1)) / delta))) := by
  have hbase := huxley_range_large_values hA hJ c hdelta hV hTtot hD hc S hsep hspread hbig hthresh
  refine le_trans hbase ?_
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hJ0 : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hVJ : (0 : ℝ) < V / (J : ℝ) := by positivity
  have hnum : (0 : ℝ) ≤ 1648656 * Ttot * D ^ 4 :=
    mul_nonneg (mul_nonneg (by norm_num) hTtot) (by positivity)
  have hterm : ∀ j ∈ Finset.range J,
      (1648656 * Ttot * D ^ 4 / (((A * 2 ^ j : ℕ) : ℝ) ^ 2 * (V / (J : ℝ)) ^ 4) + 1)
          * (2 * D ^ 2 * (1 + 12 * Real.pi * (1 + Real.log (Ttot / delta + 1)) / delta))
        ≤ (1648656 * Ttot * D ^ 4 / ((A : ℝ) ^ 2 * (V / (J : ℝ)) ^ 4) + 1)
          * (2 * D ^ 2 * (1 + 12 * Real.pi * (1 + Real.log (Ttot / delta + 1)) / delta)) := by
    intro j _
    have hAj : (A : ℝ) ≤ ((A * 2 ^ j : ℕ) : ℝ) := by
      have : A ≤ A * 2 ^ j := Nat.le_mul_of_pos_right A (Nat.two_pow_pos j)
      exact_mod_cast this
    have hden : (0 : ℝ) < (A : ℝ) ^ 2 * (V / (J : ℝ)) ^ 4 := by positivity
    have hden' : (A : ℝ) ^ 2 * (V / (J : ℝ)) ^ 4
        ≤ ((A * 2 ^ j : ℕ) : ℝ) ^ 2 * (V / (J : ℝ)) ^ 4 := by
      have hsq : (A : ℝ) ^ 2 ≤ ((A * 2 ^ j : ℕ) : ℝ) ^ 2 := by nlinarith [hAj, hA0]
      exact mul_le_mul_of_nonneg_right hsq (by positivity)
    have hmono : 1648656 * Ttot * D ^ 4 / (((A * 2 ^ j : ℕ) : ℝ) ^ 2 * (V / (J : ℝ)) ^ 4)
        ≤ 1648656 * Ttot * D ^ 4 / ((A : ℝ) ^ 2 * (V / (J : ℝ)) ^ 4) :=
      div_le_div_of_nonneg_left hnum hden hden'
    have hpos : (0 : ℝ) ≤ 2 * D ^ 2
        * (1 + 12 * Real.pi * (1 + Real.log (Ttot / delta + 1)) / delta) := by
      have hlog : (0 : ℝ) ≤ Real.log (Ttot / delta + 1) := by
        refine Real.log_nonneg ?_
        have : (0 : ℝ) ≤ Ttot / delta := div_nonneg hTtot hdelta.le
        linarith
      have : (0 : ℝ) ≤ 12 * Real.pi * (1 + Real.log (Ttot / delta + 1)) / delta := by positivity
      have h2 : (0 : ℝ) ≤ 2 * D ^ 2 := by positivity
      nlinarith [h2, this]
    exact mul_le_mul_of_nonneg_right (by linarith [hmono]) hpos
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end RHTower.Sieve
