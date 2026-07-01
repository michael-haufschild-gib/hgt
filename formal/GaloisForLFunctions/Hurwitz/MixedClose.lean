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
