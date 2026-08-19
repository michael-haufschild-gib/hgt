/-
# The Schatten norm of a product

Iterating the two-factor Hölder inequality along a list gives the norm of the product against the
product of the norms, with a constant depending only on the exponent and the length.  The constant
grows superexponentially in the length -- that is intrinsic to the approximation-number route -- but
the length is *fixed* in every use here, so the growth is harmless.

Main results:
* `schattenProdConst` — the accumulated Hölder constant.
* `schattenNorm_list_prod_le` — **the norm of a product of Schatten-`p` operators**.
-/
import GaloisForLFunctions.HTGeometry.SchattenListProduct

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

/-- The accumulated Hölder constant for a product of `n` factors. -/
noncomputable def schattenProdConst (p : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | (n + 2) => (2 : ℝ) ^ (((n : ℝ) + 2) / p) * schattenProdConst p (n + 1)

theorem schattenProdConst_nonneg (p : ℝ) : ∀ n : ℕ, 0 ≤ schattenProdConst p n
  | 0 => by rw [schattenProdConst]; norm_num
  | 1 => by rw [schattenProdConst]; norm_num
  | (n + 2) => by
      rw [schattenProdConst]
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (schattenProdConst_nonneg p (n + 1))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **The Schatten norm of a product of Schatten-`p` operators.** -/
theorem schattenNorm_list_prod_le {p : ℝ} (hp : 0 < p) :
    ∀ L : List (H →L[ℂ] H), L ≠ [] → (∀ X ∈ L, MemSchattenClass p X) →
      schattenNorm (p / (L.length : ℝ)) L.prod
        ≤ schattenProdConst p L.length * (L.map (schattenNorm p)).prod := by
  intro L
  induction L with
  | nil => intro h _; exact absurd rfl h
  | cons x L ih =>
      intro _ hmem
      rcases eq_or_ne L [] with rfl | hL
      · simp [schattenProdConst]
      · have hLmem : ∀ X ∈ L, MemSchattenClass p X :=
          fun X hX => hmem X (List.mem_cons_of_mem x hX)
        have hIH := ih hL hLmem
        have hn : 0 < L.length := List.length_pos_of_ne_nil hL
        have hnR : (0 : ℝ) < (L.length : ℝ) := by exact_mod_cast hn
        have htriple : Real.HolderTriple p (p / (L.length : ℝ)) (p / ((L.length : ℝ) + 1)) := by
          refine ⟨?_, hp, div_pos hp hnR⟩
          field_simp
          ring
        have hLprod : MemSchattenClass (p / (L.length : ℝ)) L.prod :=
          memSchattenClass_list_prod hp L hL hLmem
        have hstep := schattenNorm_comp_le htriple (hmem x (by simp)) hLprod
        have hpow : (1 : ℝ) / (p / ((L.length : ℝ) + 1)) = ((L.length : ℝ) + 1) / p := by
          field_simp
        rw [hpow] at hstep
        have hprod : (x :: L).prod = x ∘L L.prod := by
          rw [List.prod_cons]
          rfl
        have hlen : (((x :: L).length : ℕ) : ℝ) = (L.length : ℝ) + 1 := by simp
        rw [hprod, hlen]
        have hconstpos : (0 : ℝ) ≤ (2 : ℝ) ^ (((L.length : ℝ) + 1) / p) :=
          Real.rpow_nonneg (by norm_num) _
        have hxnn : 0 ≤ schattenNorm p x := schattenNorm_nonneg p x
        have hmid : schattenNorm p x * schattenNorm (p / (L.length : ℝ)) L.prod
            ≤ schattenNorm p x * (schattenProdConst p L.length * (L.map (schattenNorm p)).prod) :=
          mul_le_mul_of_nonneg_left hIH hxnn
        have hchain : (2 : ℝ) ^ (((L.length : ℝ) + 1) / p)
              * (schattenNorm p x * schattenNorm (p / (L.length : ℝ)) L.prod)
            ≤ (2 : ℝ) ^ (((L.length : ℝ) + 1) / p)
              * (schattenNorm p x
                * (schattenProdConst p L.length * (L.map (schattenNorm p)).prod)) :=
          mul_le_mul_of_nonneg_left hmid hconstpos
        refine le_trans hstep (le_trans hchain (le_of_eq ?_))
        obtain ⟨m, hm⟩ : ∃ m : ℕ, L.length = m + 1 := ⟨L.length - 1, by omega⟩
        have hexp : ((L.length : ℝ) + 1) = ((m : ℝ) + 2) := by
          rw [hm]
          push_cast
          ring
        have hlist : (x :: L).length = m + 2 := by rw [List.length_cons, hm]
        rw [hexp, hlist, schattenProdConst, hm]
        simp only [List.map_cons, List.prod_cons]
        ring

end

end GaloisForLFunctions.HTGeometry
