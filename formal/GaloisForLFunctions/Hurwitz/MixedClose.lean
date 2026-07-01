/-
# The mixed harmonic/shifted-power close — Lemma 1's final wiring

Proves `MixedTailIndependent N s` outright (for `s ∉ ℤ`), the single unproven leaf of the all-N
row-descent chain: the harmonic coefficients of a mixed relation vanish.  Architecture
(worklog blueprint): induction on the harmonic degree bound — one finite difference lowers it
(constants die), spreading the shifted-power side by one ray; when the harmonic coefficients are
constants, one more difference gives a harmonic-free multi-ray relation, compressed and killed by
`HurwitzRayPeeling.multiRay_nat_relation_poly_kill`; the compressed conclusions telescope in the
shifted variables `ψ_t = SP(A_t ∘ (X + t))`, leaving `SP(C c) = 0` on ray 0, whence `c = 0` by
`shiftedPowerPolynomial_const_coeff_eq_zero`.
-/
import GaloisForLFunctions.Hurwitz.RayPeeling
import GaloisForLFunctions.Hurwitz.AllNTailIndependence

open Polynomial Complex Filter
open HurwitzRayPeeling HurwitzAllNTailIndependence HurwitzAllNTailIndependence.HurwitzZetaTail

namespace HurwitzMixedClose

/-- The harmonic tail difference: `H_i(n) = H_i(n−1) + n^{−(s+i)}` for `n ≥ 1`. -/
theorem harmonicTail_succ_diff {N : ℕ} (s : ℂ) (i : Fin (N + 1)) {n : ℕ} (hn : 1 ≤ n) :
    harmonicTail (N := N) s i n
      = harmonicTail (N := N) s i (n - 1) + ((n : ℂ)) ^ (-(s + (i : ℂ))) := by
  have hsplit : n = (n - 1) + 1 := by omega
  have h1 : harmonicTail (N := N) s i ((n - 1) + 1)
      = harmonicTail (N := N) s i (n - 1)
        + ((((n - 1 : ℕ)) : ℂ) + 1) ^ (-(s + (i : ℂ))) := by
    unfold harmonicTail
    exact Finset.sum_range_succ _ _
  have hcast : (((n - 1 : ℕ)) : ℂ) + 1 = ((n : ℂ)) := by
    rw [Nat.cast_sub hn]
    push_cast
    ring
  rw [← hsplit] at h1
  rw [h1, hcast]

/-- A polynomial fixed by the shift `X ↦ X − 1` is constant. -/
theorem eq_C_of_comp_X_sub_one_eq {p : Polynomial ℂ}
    (h : p.comp (Polynomial.X - Polynomial.C 1) = p) : p = Polynomial.C (p.eval 0) := by
  have hstep : ∀ n : ℕ, p.eval ((n : ℂ)) = p.eval 0 := by
    intro n
    induction n with
    | zero => simp
    | succ m ihm =>
      have := congrArg (fun q => Polynomial.eval ((m : ℂ) + 1) q) h
      simp only [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C] at this
      have hval : (m : ℂ) + 1 - 1 = (m : ℂ) := by ring
      rw [hval] at this
      have hcast : ((m + 1 : ℕ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
      rw [hcast, ← this, ihm]
  have hroots : p - Polynomial.C (p.eval 0) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have himg : ((fun n : ℕ => ((n : ℂ))) '' Set.univ).Infinite :=
      Set.infinite_univ.image (fun a _ b _ hab => by exact_mod_cast hab)
    refine himg.mono ?_
    rintro v ⟨n, -, rfl⟩
    show (p - Polynomial.C (p.eval 0)).IsRoot ((n : ℂ))
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C, hstep n, sub_self]
  have := sub_eq_zero.mp hroots
  exact this

end HurwitzMixedClose

namespace HurwitzMixedClose

/-- The differenced shifted-power coefficients of the mixed Δ-step. -/
noncomputable def mixedDiffA {N : ℕ} (h : Fin (N + 1) → Polynomial ℂ) (T : ℕ)
    (A : ℕ → Fin (N + 1) → Polynomial ℂ) (t : ℕ) (i : Fin (N + 1)) : Polynomial ℂ :=
  (if t ≤ T then A t i else 0)
    + (if t = 0 then (h i).comp (Polynomial.X - Polynomial.C 1) else 0)
    - (if ht : 1 ≤ t then
        (if t - 1 ≤ T then (A (t - 1) i).comp (Polynomial.X - Polynomial.C 1) else 0)
      else 0)

/-- **The mixed Δ-step.**  Differencing a mixed multi-ray relation lowers the harmonic
coefficients to their finite differences, spreads the shifted-power side by one ray (ray 0
absorbing the harmonic debris `h∘(X−1)`), and differences the polynomial side. -/
theorem mixed_diff_step {N : ℕ} {s : ℂ} (h : Fin (N + 1) → Polynomial ℂ) (T : ℕ)
    (A : ℕ → Fin (N + 1) → Polynomial ℂ) (Q : Polynomial ℂ) (M : ℕ)
    (hrel : ∀ n : ℕ, M ≤ n → T < n →
      (∑ i : Fin (N + 1), (h i).eval ((n : ℂ)) * harmonicTail (N := N) s i n)
        + (∑ t ∈ Finset.range (T + 1), ∑ i : Fin (N + 1),
            (A t i).eval ((n : ℂ)) * (((n - t : ℕ)) : ℂ) ^ (-(s + (i : ℂ))))
        = Q.eval ((n : ℂ))) :
    ∀ n : ℕ, M + 1 ≤ n → T + 1 < n →
      (∑ i : Fin (N + 1),
          ((h i) - (h i).comp (Polynomial.X - Polynomial.C 1)).eval ((n : ℂ))
            * harmonicTail (N := N) s i n)
        + (∑ t ∈ Finset.range (T + 2), ∑ i : Fin (N + 1),
            (mixedDiffA h T A t i).eval ((n : ℂ)) * (((n - t : ℕ)) : ℂ) ^ (-(s + (i : ℂ))))
        = (Q - Q.comp (Polynomial.X - Polynomial.C 1)).eval ((n : ℂ)) := by
  intro n hMn hTn
  have h1 := hrel n (by omega) (by omega)
  have h2 := hrel (n - 1) (by omega) (by omega)
  have hcastn : (((n - 1 : ℕ)) : ℂ) = ((n : ℂ)) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  -- rewrite the shifted instance into evaluations at n via comp (X − 1)
  have hcompeval : ∀ p : Polynomial ℂ,
      (p.comp (Polynomial.X - Polynomial.C 1)).eval ((n : ℂ)) = p.eval (((n - 1 : ℕ)) : ℂ) := by
    intro p
    rw [Polynomial.eval_comp]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [hcastn]
  -- the harmonic rebase at n
  have hharm : ∀ i : Fin (N + 1),
      harmonicTail (N := N) s i (n - 1)
        = harmonicTail (N := N) s i n - ((n : ℂ)) ^ (-(s + (i : ℂ))) := by
    intro i
    have := harmonicTail_succ_diff (N := N) s i (n := n) (by omega)
    linear_combination -this
  -- expand the harmonic difference block
  have hharm_block :
      (∑ i : Fin (N + 1), (h i).eval ((n : ℂ)) * harmonicTail (N := N) s i n)
        - (∑ i : Fin (N + 1), (h i).eval (((n - 1 : ℕ)) : ℂ) * harmonicTail (N := N) s i (n - 1))
      = (∑ i : Fin (N + 1),
          ((h i) - (h i).comp (Polynomial.X - Polynomial.C 1)).eval ((n : ℂ))
            * harmonicTail (N := N) s i n)
        + (∑ i : Fin (N + 1),
            ((h i).comp (Polynomial.X - Polynomial.C 1)).eval ((n : ℂ))
              * ((n : ℂ)) ^ (-(s + (i : ℂ)))) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Polynomial.eval_sub]
    rw [hcompeval (h i)]
    linear_combination (-(Polynomial.eval (((n - 1 : ℕ)) : ℂ) (h i))) * hharm i
  -- expand the shifted-power difference block: reindex the shifted instance
  have hshift_block :
      (∑ t ∈ Finset.range (T + 1), ∑ i : Fin (N + 1),
          (A t i).eval (((n - 1 : ℕ)) : ℂ) * (((n - 1 - t : ℕ)) : ℂ) ^ (-(s + (i : ℂ))))
      = ∑ t ∈ Finset.range (T + 2), ∑ i : Fin (N + 1),
          (if ht : 1 ≤ t then
            (if t - 1 ≤ T then
              ((A (t - 1) i).comp (Polynomial.X - Polynomial.C 1)).eval ((n : ℂ)) else 0)
          else 0) * (((n - t : ℕ)) : ℂ) ^ (-(s + (i : ℂ))) := by
    rw [Finset.sum_range_succ' (n := T + 1)]
    have hzero : (∑ i : Fin (N + 1),
        (if ht : 1 ≤ 0 then
          (if 0 - 1 ≤ T then
            ((A (0 - 1) i).comp (Polynomial.X - Polynomial.C 1)).eval ((n : ℂ)) else 0)
        else 0) * (((n - 0 : ℕ)) : ℂ) ^ (-(s + (i : ℂ)))) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [dif_neg (by omega)]
      ring
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl fun t htmem => ?_
    have htT : t ≤ T := Nat.lt_succ_iff.mp (Finset.mem_range.mp htmem)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dif_pos (by omega : 1 ≤ t + 1)]
    simp only [Nat.add_sub_cancel]
    rw [if_pos htT, hcompeval (A t i)]
    have hsub : (n - 1 - t : ℕ) = (n - (t + 1) : ℕ) := by omega
    rw [hsub]
  -- assemble
  have hnew_first :
      ∑ t ∈ Finset.range (T + 2), ∑ i : Fin (N + 1),
        ((if t ≤ T then A t i else 0)
          + (if t = 0 then (h i).comp (Polynomial.X - Polynomial.C 1) else 0)).eval ((n : ℂ))
          * (((n - t : ℕ)) : ℂ) ^ (-(s + (i : ℂ)))
      = (∑ t ∈ Finset.range (T + 1), ∑ i : Fin (N + 1),
          (A t i).eval ((n : ℂ)) * (((n - t : ℕ)) : ℂ) ^ (-(s + (i : ℂ))))
        + (∑ i : Fin (N + 1),
            ((h i).comp (Polynomial.X - Polynomial.C 1)).eval ((n : ℂ))
              * ((n : ℂ)) ^ (-(s + (i : ℂ)))) := by
    rw [Finset.sum_range_succ]
    have hlast : (∑ i : Fin (N + 1),
        ((if T + 1 ≤ T then A (T + 1) i else 0)
          + (if T + 1 = 0 then (h i).comp (Polynomial.X - Polynomial.C 1) else 0)).eval ((n : ℂ))
          * (((n - (T + 1) : ℕ)) : ℂ) ^ (-(s + (i : ℂ)))) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg (by omega), if_neg (by omega)]
      simp
    rw [hlast, add_zero]
    have hsum : ∀ t ∈ Finset.range (T + 1),
        (∑ i : Fin (N + 1),
          ((if t ≤ T then A t i else 0)
            + (if t = 0 then (h i).comp (Polynomial.X - Polynomial.C 1) else 0)).eval ((n : ℂ))
            * (((n - t : ℕ)) : ℂ) ^ (-(s + (i : ℂ))))
        = (∑ i : Fin (N + 1), (A t i).eval ((n : ℂ)) * (((n - t : ℕ)) : ℂ) ^ (-(s + (i : ℂ))))
          + (if t = 0 then (∑ i : Fin (N + 1),
              ((h i).comp (Polynomial.X - Polynomial.C 1)).eval ((n : ℂ))
                * ((n : ℂ)) ^ (-(s + (i : ℂ)))) else 0) := by
      intro t htmem
      have htT : t ≤ T := Nat.lt_succ_iff.mp (Finset.mem_range.mp htmem)
      split_ifs with h0
      · subst h0
        have hper : ∀ i ∈ (Finset.univ : Finset (Fin (N + 1))),
            (A 0 i + (h i).comp (Polynomial.X - Polynomial.C 1)).eval
                ((n : ℂ)) * (((n - 0 : ℕ)) : ℂ) ^ (-(s + (i : ℂ)))
            = (A 0 i).eval ((n : ℂ)) * (((n - 0 : ℕ)) : ℂ) ^ (-(s + (i : ℂ)))
              + ((h i).comp (Polynomial.X - Polynomial.C 1)).eval ((n : ℂ))
                * ((n : ℂ)) ^ (-(s + (i : ℂ))) := by
          intro i _
          simp only [Polynomial.eval_add, Nat.sub_zero]
          ring
        rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib]
      · rw [add_zero]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [add_zero]
    have hconst : (∑ t ∈ Finset.range (T + 1),
        (if t = 0 then (∑ i : Fin (N + 1),
          ((h i).comp (Polynomial.X - Polynomial.C 1)).eval ((n : ℂ))
            * ((n : ℂ)) ^ (-(s + (i : ℂ)))) else 0))
        = ∑ i : Fin (N + 1),
            ((h i).comp (Polynomial.X - Polynomial.C 1)).eval ((n : ℂ))
              * ((n : ℂ)) ^ (-(s + (i : ℂ))) := by
      rw [Finset.sum_eq_single 0 (fun b _ hb => if_neg hb)
        (fun hnotmem => absurd (Finset.mem_range.mpr (by omega)) hnotmem)]
      rw [if_pos rfl]
    calc ∑ t ∈ Finset.range (T + 1), ∑ i : Fin (N + 1),
          ((if t ≤ T then A t i else 0)
            + (if t = 0 then (h i).comp (Polynomial.X - Polynomial.C 1) else 0)).eval ((n : ℂ))
            * (((n - t : ℕ)) : ℂ) ^ (-(s + (i : ℂ)))
        = ∑ t ∈ Finset.range (T + 1),
            ((∑ i : Fin (N + 1), (A t i).eval ((n : ℂ))
                * (((n - t : ℕ)) : ℂ) ^ (-(s + (i : ℂ))))
              + (if t = 0 then (∑ i : Fin (N + 1),
                  ((h i).comp (Polynomial.X - Polynomial.C 1)).eval ((n : ℂ))
                    * ((n : ℂ)) ^ (-(s + (i : ℂ)))) else 0)) :=
          Finset.sum_congr rfl hsum
      _ = (∑ t ∈ Finset.range (T + 1), ∑ i : Fin (N + 1),
            (A t i).eval ((n : ℂ)) * (((n - t : ℕ)) : ℂ) ^ (-(s + (i : ℂ))))
          + (∑ t ∈ Finset.range (T + 1),
              (if t = 0 then (∑ i : Fin (N + 1),
                ((h i).comp (Polynomial.X - Polynomial.C 1)).eval ((n : ℂ))
                  * ((n : ℂ)) ^ (-(s + (i : ℂ)))) else 0)) := Finset.sum_add_distrib
      _ = _ := by rw [hconst]
  -- final algebra
  have hsplitA : ∀ t ∈ Finset.range (T + 2), ∀ i : Fin (N + 1),
      (mixedDiffA h T A t i).eval ((n : ℂ))
        = ((if t ≤ T then A t i else 0)
            + (if t = 0 then (h i).comp (Polynomial.X - Polynomial.C 1) else 0)).eval ((n : ℂ))
          - (if ht : 1 ≤ t then
              (if t - 1 ≤ T then
                ((A (t - 1) i).comp (Polynomial.X - Polynomial.C 1)).eval ((n : ℂ)) else 0)
            else 0) := by
    intro t _ i
    unfold mixedDiffA
    simp only [Polynomial.eval_sub, Polynomial.eval_add]
    split_ifs <;> simp
  have hray : (∑ t ∈ Finset.range (T + 2), ∑ i : Fin (N + 1),
      (mixedDiffA h T A t i).eval ((n : ℂ)) * (((n - t : ℕ)) : ℂ) ^ (-(s + (i : ℂ))))
      = ((∑ t ∈ Finset.range (T + 1), ∑ i : Fin (N + 1),
          (A t i).eval ((n : ℂ)) * (((n - t : ℕ)) : ℂ) ^ (-(s + (i : ℂ))))
        + (∑ i : Fin (N + 1),
            ((h i).comp (Polynomial.X - Polynomial.C 1)).eval ((n : ℂ))
              * ((n : ℂ)) ^ (-(s + (i : ℂ)))))
        - (∑ t ∈ Finset.range (T + 1), ∑ i : Fin (N + 1),
            (A t i).eval (((n - 1 : ℕ)) : ℂ)
              * (((n - 1 - t : ℕ)) : ℂ) ^ (-(s + (i : ℂ)))) := by
    have hsplit2 : (∑ t ∈ Finset.range (T + 2), ∑ i : Fin (N + 1),
        (mixedDiffA h T A t i).eval ((n : ℂ)) * (((n - t : ℕ)) : ℂ) ^ (-(s + (i : ℂ))))
        = (∑ t ∈ Finset.range (T + 2), ∑ i : Fin (N + 1),
            ((if t ≤ T then A t i else 0)
              + (if t = 0 then (h i).comp (Polynomial.X - Polynomial.C 1) else 0)).eval
              ((n : ℂ)) * (((n - t : ℕ)) : ℂ) ^ (-(s + (i : ℂ))))
          - (∑ t ∈ Finset.range (T + 2), ∑ i : Fin (N + 1),
              (if ht : 1 ≤ t then
                (if t - 1 ≤ T then
                  ((A (t - 1) i).comp (Polynomial.X - Polynomial.C 1)).eval ((n : ℂ))
                else 0)
              else 0) * (((n - t : ℕ)) : ℂ) ^ (-(s + (i : ℂ)))) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun t htmem => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hsplitA t htmem i]
      ring
    rw [hsplit2, hnew_first, ← hshift_block]
  have hQdiff : (Q - Q.comp (Polynomial.X - Polynomial.C 1)).eval ((n : ℂ))
      = Q.eval ((n : ℂ)) - Q.eval (((n - 1 : ℕ)) : ℂ) := by
    simp only [Polynomial.eval_sub]
    rw [hcompeval Q]
  rw [hQdiff, ← h1, ← h2]
  linear_combination -hharm_block + hray

end HurwitzMixedClose

namespace HurwitzMixedClose

/-- Exponent bookkeeping: trading a `cpow` shift for a natural power. -/
theorem cpow_nat_shift {w : ℂ} (hw : w ≠ 0) {i N : ℕ} (hiN : i ≤ N) (s : ℂ) :
    w ^ (-(s + (i : ℂ))) * w ^ (N : ℕ) = w ^ (-s) * w ^ ((N - i : ℕ)) := by
  rw [← Complex.cpow_natCast w N, ← Complex.cpow_natCast w (N - i),
    ← Complex.cpow_add _ _ hw, ← Complex.cpow_add _ _ hw]
  congr 1
  rw [Nat.cast_sub hiN]
  push_cast
  ring

/-- Beyond ray `T+1` the differenced coefficients vanish. -/
theorem mixedDiffA_zero_of_gt {N : ℕ} (h : Fin (N + 1) → Polynomial ℂ) (T : ℕ)
    (A : ℕ → Fin (N + 1) → Polynomial ℂ) {t : ℕ} (ht : T + 1 < t) (i : Fin (N + 1)) :
    mixedDiffA h T A t i = 0 := by
  unfold mixedDiffA
  rw [if_neg (by omega), if_neg (by omega), dif_pos (by omega), if_neg (by omega)]
  ring

/-- Finite sums distribute over polynomial composition. -/
theorem finsetSum_comp {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ) (q : Polynomial ℂ) :
    (∑ i ∈ s, f i).comp q = ∑ i ∈ s, (f i).comp q := by
  simp [Polynomial.comp, Polynomial.eval₂_finsetSum]

/-- **The constants endgame.**  A mixed multi-ray relation whose harmonic coefficients are
constants forces those constants to vanish: one difference produces a harmonic-free relation,
compression and `multiRay_nat_relation_poly_kill` kill every compressed ray, and the compressed
conclusions telescope in the shift-normalised variables `ψ_t`, leaving the constant
shifted-power polynomial on ray `0`. -/
theorem constants_harmonic_kill {N : ℕ} {s : ℂ} (hs : ∀ k : ℤ, s ≠ (k : ℂ))
    (c : Fin (N + 1) → ℂ) (T : ℕ) (A : ℕ → Fin (N + 1) → Polynomial ℂ) (Q : Polynomial ℂ)
    (M : ℕ)
    (hrel : ∀ n : ℕ, M ≤ n → T < n →
      (∑ i : Fin (N + 1), (Polynomial.C (c i)).eval ((n : ℂ)) * harmonicTail (N := N) s i n)
        + (∑ t ∈ Finset.range (T + 1), ∑ i : Fin (N + 1),
            (A t i).eval ((n : ℂ)) * (((n - t : ℕ)) : ℂ) ^ (-(s + (i : ℂ))))
        = Q.eval ((n : ℂ))) :
    ∀ i, c i = 0 := by
  classical
  set h : Fin (N + 1) → Polynomial ℂ := fun i => Polynomial.C (c i) with hh
  have hdiff := mixed_diff_step (N := N) (s := s) h T A Q M hrel
  -- the differenced harmonic block vanishes
  have hpure : ∀ n : ℕ, M + 1 ≤ n → T + 1 < n →
      (∑ t ∈ Finset.range (T + 2), ∑ i : Fin (N + 1),
          (mixedDiffA h T A t i).eval ((n : ℂ)) * (((n - t : ℕ)) : ℂ) ^ (-(s + (i : ℂ))))
        = (Q - Q.comp (Polynomial.X - Polynomial.C 1)).eval ((n : ℂ)) := by
    intro n h1 h2
    have hd := hdiff n h1 h2
    have hharmzero : (∑ i : Fin (N + 1),
        ((h i) - (h i).comp (Polynomial.X - Polynomial.C 1)).eval ((n : ℂ))
          * harmonicTail (N := N) s i n) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hh]
      simp
    rw [hharmzero, zero_add] at hd
    exact hd
  -- compression
  set SPt : ℕ → Polynomial ℂ := fun t =>
    ∑ i : Fin (N + 1), mixedDiffA h T A t i
      * (Polynomial.X - Polynomial.C ((t : ℕ) : ℂ)) ^ (N - (i : ℕ)) with hSPtdef
  set Etil : ℕ → Polynomial ℂ := fun t =>
    SPt t * ∏ t' ∈ (Finset.range (T + 2)).erase t,
      (Polynomial.X - Polynomial.C ((t' : ℕ) : ℂ)) ^ N with hEtildef
  set Qtil : Polynomial ℂ := (Q - Q.comp (Polynomial.X - Polynomial.C 1))
    * ∏ t' ∈ Finset.range (T + 2), (Polynomial.X - Polynomial.C ((t' : ℕ) : ℂ)) ^ N with hQtildef
  have hcomp_rel : ∀ n : ℕ, M + 1 ≤ n → T + 1 < n →
      ∑ t ∈ Finset.range (T + 2), (((n - t : ℕ)) : ℂ) ^ (-s) * (Etil t).eval ((n : ℂ))
        = Qtil.eval ((n : ℂ)) := by
    intro n h1 h2
    have hProdEval : ∀ (S : Finset ℕ),
        (∏ t' ∈ S, (Polynomial.X - Polynomial.C ((t' : ℕ) : ℂ)) ^ N).eval ((n : ℂ))
          = ∏ t' ∈ S, ((n : ℂ) - (t' : ℂ)) ^ N := by
      intro S
      rw [Polynomial.eval_prod]
      refine Finset.prod_congr rfl fun t' _ => ?_
      simp
    have hterm : ∀ t ∈ Finset.range (T + 2),
        (((n - t : ℕ)) : ℂ) ^ (-s) * (Etil t).eval ((n : ℂ))
          = (∑ i : Fin (N + 1),
              (mixedDiffA h T A t i).eval ((n : ℂ)) * (((n - t : ℕ)) : ℂ) ^ (-(s + (i : ℂ))))
            * (∏ t' ∈ Finset.range (T + 2), ((n : ℂ) - (t' : ℂ)) ^ N) := by
      intro t htmem
      have htn : t < n := by
        have := Finset.mem_range.mp htmem
        omega
      have hcast : (((n - t : ℕ)) : ℂ) = (n : ℂ) - (t : ℂ) := by
        rw [Nat.cast_sub (by omega)]
      have hbase : (((n - t : ℕ)) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hbase' : (n : ℂ) - (t : ℂ) ≠ 0 := by
        rw [← hcast]
        exact hbase
      have hsplitP : (∏ t' ∈ Finset.range (T + 2), ((n : ℂ) - (t' : ℂ)) ^ N)
          = ((n : ℂ) - (t : ℂ)) ^ N * ∏ t' ∈ (Finset.range (T + 2)).erase t,
              ((n : ℂ) - (t' : ℂ)) ^ N := by
        rw [← Finset.mul_prod_erase (Finset.range (T + 2)) _ htmem]
      rw [hEtildef]
      simp only [Polynomial.eval_mul]
      rw [hSPtdef, Polynomial.eval_finsetSum,
        hProdEval ((Finset.range (T + 2)).erase t), hsplitP]
      simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C]
      conv_lhs => rw [Finset.sum_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hshift := cpow_nat_shift (w := (n : ℂ) - (t : ℂ)) hbase'
        (i := (i : ℕ)) (N := N) (by omega : (i : ℕ) ≤ N) s
      rw [hcast]
      linear_combination (-(Polynomial.eval ((n : ℂ)) (mixedDiffA h T A t i)
        * ∏ t' ∈ (Finset.range (T + 2)).erase t, ((n : ℂ) - (t' : ℂ)) ^ N)) * hshift
    calc ∑ t ∈ Finset.range (T + 2), (((n - t : ℕ)) : ℂ) ^ (-s) * (Etil t).eval ((n : ℂ))
        = ∑ t ∈ Finset.range (T + 2), (∑ i : Fin (N + 1),
              (mixedDiffA h T A t i).eval ((n : ℂ)) * (((n - t : ℕ)) : ℂ) ^ (-(s + (i : ℂ))))
            * (∏ t' ∈ Finset.range (T + 2), ((n : ℂ) - (t' : ℂ)) ^ N) :=
          Finset.sum_congr rfl hterm
      _ = (∑ t ∈ Finset.range (T + 2), ∑ i : Fin (N + 1),
              (mixedDiffA h T A t i).eval ((n : ℂ)) * (((n - t : ℕ)) : ℂ) ^ (-(s + (i : ℂ))))
            * (∏ t' ∈ Finset.range (T + 2), ((n : ℂ) - (t' : ℂ)) ^ N) :=
          (Finset.sum_mul _ _ _).symm
      _ = (Q - Q.comp (Polynomial.X - Polynomial.C 1)).eval ((n : ℂ))
            * (∏ t' ∈ Finset.range (T + 2), ((n : ℂ) - (t' : ℂ)) ^ N) := by
          rw [hpure n h1 h2]
      _ = Qtil.eval ((n : ℂ)) := by
          rw [hQtildef]
          simp only [Polynomial.eval_mul]
          rw [hProdEval (Finset.range (T + 2))]
  -- kill the compressed system
  have hEtil_gt : ∀ t, T + 1 < t → Etil t = 0 := by
    intro t ht
    have h0 : SPt t = 0 := by
      rw [hSPtdef]
      exact Finset.sum_eq_zero fun i _ => by
        rw [mixedDiffA_zero_of_gt h T A ht i, zero_mul]
    simp only [hEtildef]
    rw [h0, zero_mul]
  set D : ℕ := Finset.sup (Finset.range (T + 2)) (fun t => (Etil t).natDegree) with hD
  have hdegE : ∀ t, (Etil t).natDegree ≤ D := by
    intro t
    rcases lt_or_ge t (T + 2) with hlt | hge
    · rw [hD]
      exact Finset.le_sup (f := fun t => (Etil t).natDegree) (Finset.mem_range.mpr hlt)
    · rw [hEtil_gt t (by omega)]
      simp
  obtain ⟨hEtil0, -⟩ := multiRay_nat_relation_poly_kill hs Qtil.natDegree (T + 1) D
    (by omega) Etil hdegE Qtil le_rfl (M + 1) hcomp_rel
  -- cancel the erase products
  have hSPt0 : ∀ t ≤ T + 1, SPt t = 0 := by
    intro t ht
    have hE := hEtil0 t ht
    rw [hEtildef] at hE
    have hprodne : (∏ t' ∈ (Finset.range (T + 2)).erase t,
        (Polynomial.X - Polynomial.C ((t' : ℕ) : ℂ)) ^ N) ≠ 0 :=
      (Polynomial.monic_prod_of_monic _ _
        fun t' _ => (Polynomial.monic_X_sub_C _).pow N).ne_zero
    exact (mul_eq_zero.mp hE).resolve_right hprodne
  -- shift-normalised compressed rays
  set ψ : ℕ → Polynomial ℂ := fun r =>
    ∑ i : Fin (N + 1), (A r i).comp (Polynomial.X + Polynomial.C ((r : ℕ) : ℂ))
      * Polynomial.X ^ (N - (i : ℕ)) with hψdef
  have hSPcomp : ∀ t ≤ T + 1,
      (∑ i : Fin (N + 1),
        (mixedDiffA h T A t i).comp (Polynomial.X + Polynomial.C ((t : ℕ) : ℂ))
          * Polynomial.X ^ (N - (i : ℕ))) = 0 := by
    intro t ht
    have h0 := congrArg (fun p : Polynomial ℂ =>
      p.comp (Polynomial.X + Polynomial.C ((t : ℕ) : ℂ))) (hSPt0 t ht)
    simp only [Polynomial.zero_comp] at h0
    rw [hSPtdef, finsetSum_comp] at h0
    have hper : ∀ i ∈ (Finset.univ : Finset (Fin (N + 1))),
        (mixedDiffA h T A t i
          * (Polynomial.X - Polynomial.C ((t : ℕ) : ℂ)) ^ (N - (i : ℕ))).comp
            (Polynomial.X + Polynomial.C ((t : ℕ) : ℂ))
        = (mixedDiffA h T A t i).comp (Polynomial.X + Polynomial.C ((t : ℕ) : ℂ))
            * Polynomial.X ^ (N - (i : ℕ)) := by
      intro i _
      rw [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.X_comp,
        Polynomial.C_comp]
      have hX : (Polynomial.X + Polynomial.C ((t : ℕ) : ℂ)) - Polynomial.C ((t : ℕ) : ℂ)
          = (Polynomial.X : Polynomial ℂ) := by ring
      rw [hX]
    rw [Finset.sum_congr rfl hper] at h0
    exact h0
  -- the shift compositions of the three coefficient shapes
  have hshiftcomp : ∀ (p : Polynomial ℂ) (t : ℕ), 1 ≤ t →
      (p.comp (Polynomial.X - Polynomial.C 1)).comp
        (Polynomial.X + Polynomial.C ((t : ℕ) : ℂ))
      = p.comp (Polynomial.X + Polynomial.C (((t - 1 : ℕ)) : ℂ)) := by
    intro p t ht
    rw [Polynomial.comp_assoc]
    congr 1
    rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
    have hc : ((t : ℕ) : ℂ) - 1 = (((t - 1 : ℕ)) : ℂ) := by
      rw [Nat.cast_sub ht]
      push_cast
      ring
    calc (Polynomial.X + Polynomial.C ((t : ℕ) : ℂ)) - Polynomial.C 1
        = Polynomial.X + Polynomial.C (((t : ℕ) : ℂ) - 1) := by
          rw [Polynomial.C_sub]
          ring
      _ = Polynomial.X + Polynomial.C (((t - 1 : ℕ)) : ℂ) := by rw [hc]
  -- ray T+1 kills ψ T
  have hψT : ψ T = 0 := by
    have h0 := hSPcomp (T + 1) le_rfl
    have hper : ∀ i ∈ (Finset.univ : Finset (Fin (N + 1))),
        (mixedDiffA h T A (T + 1) i).comp
            (Polynomial.X + Polynomial.C (((T + 1 : ℕ)) : ℂ))
          * Polynomial.X ^ (N - (i : ℕ))
        = -((A T i).comp (Polynomial.X + Polynomial.C ((T : ℕ) : ℂ))
            * Polynomial.X ^ (N - (i : ℕ))) := by
      intro i _
      have hA : mixedDiffA h T A (T + 1) i
          = -((A T i).comp (Polynomial.X - Polynomial.C 1)) := by
        unfold mixedDiffA
        rw [if_neg (by omega), if_neg (by omega), dif_pos (by omega)]
        simp only [Nat.add_sub_cancel]
        rw [if_pos (le_refl T)]
        ring
      rw [hA, Polynomial.neg_comp, hshiftcomp (A T i) (T + 1) (by omega)]
      simp only [Nat.add_sub_cancel]
      ring
    rw [Finset.sum_congr rfl hper, Finset.sum_neg_distrib] at h0
    have := neg_eq_zero.mp h0
    rw [hψdef]
    exact this
  -- the middle rays telescope
  have hψchain : ∀ t, 1 ≤ t → t ≤ T → ψ t = ψ (t - 1) := by
    intro t h1t htT
    have h0 := hSPcomp t (by omega)
    have hper : ∀ i ∈ (Finset.univ : Finset (Fin (N + 1))),
        (mixedDiffA h T A t i).comp (Polynomial.X + Polynomial.C ((t : ℕ) : ℂ))
          * Polynomial.X ^ (N - (i : ℕ))
        = (A t i).comp (Polynomial.X + Polynomial.C ((t : ℕ) : ℂ))
            * Polynomial.X ^ (N - (i : ℕ))
          - (A (t - 1) i).comp (Polynomial.X + Polynomial.C (((t - 1 : ℕ)) : ℂ))
            * Polynomial.X ^ (N - (i : ℕ)) := by
      intro i _
      have hA : mixedDiffA h T A t i
          = A t i - (A (t - 1) i).comp (Polynomial.X - Polynomial.C 1) := by
        unfold mixedDiffA
        rw [if_pos htT, if_neg (by omega), dif_pos h1t, if_pos (by omega)]
        ring
      rw [hA, Polynomial.sub_comp, hshiftcomp (A (t - 1) i) t h1t]
      ring
    rw [Finset.sum_congr rfl hper, Finset.sum_sub_distrib] at h0
    have := sub_eq_zero.mp h0
    rw [hψdef]
    exact this
  -- downward induction: every ψ vanishes
  have hψall : ∀ j, j ≤ T → ψ (T - j) = 0 := by
    intro j
    induction j with
    | zero =>
      intro _
      simpa using hψT
    | succ m ihm =>
      intro hm
      have hTm : T - m = (T - (m + 1)) + 1 := by omega
      have hprev : ψ (T - m) = 0 := ihm (by omega)
      have hstep := hψchain (T - m) (by omega) (by omega)
      rw [hTm] at hprev hstep
      simp only [Nat.add_sub_cancel] at hstep
      rw [← hstep]
      rw [← hTm]
      exact ihm (by omega)
  -- ray 0 leaves the constant shifted-power polynomial
  have hconst : (∑ i : Fin (N + 1), Polynomial.C (c i)
      * Polynomial.X ^ (N - (i : ℕ))) = 0 := by
    have h0 := hSPcomp 0 (by omega)
    have hper : ∀ i ∈ (Finset.univ : Finset (Fin (N + 1))),
        (mixedDiffA h T A 0 i).comp (Polynomial.X + Polynomial.C (((0 : ℕ)) : ℂ))
          * Polynomial.X ^ (N - (i : ℕ))
        = (A 0 i).comp (Polynomial.X + Polynomial.C (((0 : ℕ)) : ℂ))
            * Polynomial.X ^ (N - (i : ℕ))
          + Polynomial.C (c i) * Polynomial.X ^ (N - (i : ℕ)) := by
      intro i _
      have hA : mixedDiffA h T A 0 i = A 0 i + Polynomial.C (c i) := by
        unfold mixedDiffA
        rw [if_pos (Nat.zero_le T), if_pos rfl, dif_neg (by omega)]
        simp only [hh, Polynomial.C_comp]
        ring
      rw [hA, Polynomial.add_comp, Polynomial.C_comp]
      ring
    rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib] at h0
    have hψ0 : (∑ i : Fin (N + 1),
        (A 0 i).comp (Polynomial.X + Polynomial.C (((0 : ℕ)) : ℂ))
          * Polynomial.X ^ (N - (i : ℕ))) = 0 := by
      have hz := hψall T le_rfl
      rw [Nat.sub_self] at hz
      rw [hψdef] at hz
      exact hz
    rw [hψ0, zero_add] at h0
    exact h0
  intro i
  refine HurwitzNonRat.shiftedPowerPolynomial_const_coeff_eq_zero (N := N) (c := c) ?_ i
  rw [HurwitzNonRat.shiftedPowerPolynomial]
  exact hconst

end HurwitzMixedClose
