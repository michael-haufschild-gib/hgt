/-
# Approximation numbers are submultiplicative

The `(m+n)`-th approximation number of a composition is at most the product of the `m`-th and the
`n`-th: subtracting near-optimal finite-rank approximants of the two factors leaves the product of
the two errors, and the corrected approximant has rank at most `m+n`.

This is the multiplicative half of the Ky Fan inequalities -- the additive half
(`approxNumber_add_le`) is already in the corpus -- and it is what makes Schatten classes an
*ideal scale* rather than merely a family of ideals.

Main results:
* `approxNumber_comp_add_le` — **submultiplicativity**.
* `approxNumber_pow_le` — the iterate bound `a_{k·n}(T^k) ≤ a_n(T)^k`.
-/
import GaloisForLFunctions.RHTower.NuclearRankOneSchatten
import GaloisForLFunctions.RHTower.FiniteRankOperatorAlgebra

open ContinuousLinearMap Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **Submultiplicativity of the approximation numbers.** -/
theorem approxNumber_comp_add_le (S T : H →L[ℂ] H) (m n : ℕ) :
    approxNumber (S ∘L T) (m + n) ≤ approxNumber S m * approxNumber T n := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set a : ℝ := approxNumber S m with ha'
  set b : ℝ := approxNumber T n with hb'
  have ha : 0 ≤ a := approxNumber_nonneg S m
  have hb : 0 ≤ b := approxNumber_nonneg T n
  set δ : ℝ := min 1 (ε / (a + b + 1)) with hδ'
  have hsum : (0 : ℝ) < a + b + 1 := by linarith
  have hδpos : 0 < δ := lt_min one_pos (div_pos hε hsum)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδe : δ * (a + b + 1) ≤ ε := by
    have hle : δ ≤ ε / (a + b + 1) := min_le_right _ _
    calc δ * (a + b + 1) ≤ (ε / (a + b + 1)) * (a + b + 1) :=
          mul_le_mul_of_nonneg_right hle hsum.le
      _ = ε := by field_simp
  obtain ⟨F, hF, hFlt⟩ := exists_hasRankLE_norm_sub_lt S m (by linarith : a < a + δ)
  obtain ⟨G, hG, hGlt⟩ := exists_hasRankLE_norm_sub_lt T n (by linarith : b < b + δ)
  have hid : S ∘L T - (F ∘L T + (S - F) ∘L G) = (S - F) ∘L (T - G) := by
    simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
    abel
  have hrank : HasRankLE (F ∘L T + (S - F) ∘L G) (m + n) :=
    HasRankLE.add (hF.comp_right T) (hG.comp_left (S - F))
  have hstep : approxNumber (S ∘L T) (m + n) ≤ ‖(S - F) ∘L (T - G)‖ := by
    have := approxNumber_le (S ∘L T) (m + n) _ hrank
    rwa [hid] at this
  have hnorm : ‖(S - F) ∘L (T - G)‖ ≤ ‖S - F‖ * ‖T - G‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have hprod : ‖S - F‖ * ‖T - G‖ ≤ (a + δ) * (b + δ) :=
    mul_le_mul hFlt.le hGlt.le (norm_nonneg _) (by linarith)
  have hexpand : (a + δ) * (b + δ) ≤ a * b + ε := by
    have hδsq : δ * δ ≤ δ := by nlinarith
    nlinarith [hδe, hδsq, hδpos.le, ha, hb]
  linarith [hstep, hnorm, hprod, hexpand]

omit [CompleteSpace H] in
/-- The iterate bound: the `k·n`-th approximation number of a `k`-th power is at most the `k`-th
power of the `n`-th. -/
theorem approxNumber_pow_le (T : H →L[ℂ] H) (n : ℕ) : ∀ k : ℕ, 0 < k →
    approxNumber (T ^ k) (k * n) ≤ approxNumber T n ^ k := by
  intro k
  induction k with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | succ j ih =>
      intro _
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj
        simp
      · have hstep : approxNumber (T ^ (j + 1)) (n + j * n)
            ≤ approxNumber T n * approxNumber (T ^ j) (j * n) := by
          have hpow : (T : H →L[ℂ] H) ^ (j + 1) = T ∘L (T ^ j) := by
            rw [pow_succ']
            rfl
          rw [hpow]
          exact approxNumber_comp_add_le T (T ^ j) n (j * n)
        have hidx : (j + 1) * n = n + j * n := by ring
        rw [hidx]
        refine le_trans hstep ?_
        have hIH := ih hj
        calc approxNumber T n * approxNumber (T ^ j) (j * n)
            ≤ approxNumber T n * approxNumber T n ^ j :=
              mul_le_mul_of_nonneg_left hIH (approxNumber_nonneg T n)
          _ = approxNumber T n ^ (j + 1) := by rw [pow_succ']

end

end GaloisForLFunctions.HTGeometry
