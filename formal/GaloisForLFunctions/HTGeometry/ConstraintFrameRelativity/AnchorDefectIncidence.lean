import Mathlib

/-!
# The anchor--defect incidence current and its interchange defect

A finite aperture carries the normalised complete bipartite current on an anchor set `H` and a
defect set `D`:

`J_{H,D}(a,p) = 1/(|H||D|)` on `H × D` and `0` elsewhere.

It has edge `ℓ¹` norm one, total oriented mass one, squared `ℓ²` norm `1/(|H||D|)`, and boundary
`u_D - u_H`.  When the defect set splits as a disjoint union `O ⊔ L`, the current is the convex
combination `(d/(d+ℓ)) J_{H,O} + (ℓ/(d+ℓ)) J_{H,L}`, so the interchange defect between direct and
outer incidence is

`Ω = J_{H,O ⊔ L} - J_{H,O} = (ℓ/(d+ℓ)) (J_{H,L} - J_{H,O})`,

with `‖Ω‖₁ = 2ℓ/(d+ℓ)`, `‖Ω‖₂² = ℓ/(a d (d+ℓ))`, zero net mass, and boundary
`(ℓ/(d+ℓ))(u_L - u_O)`.

Composition of three stages obeys an exact Bianchi identity: with the interchange defect written
as `Ω = J₁ - J₂ - T J₃` for a transport `T` satisfying `T_t T_s = T_{ts}` and additivity, both
sides of the three-stage identity expand to the same four-term expression.
-/

namespace HTGeometry.ConstraintFrameRelativity

open Finset

variable {F : Type*} [Fintype F] [DecidableEq F]

/-! ## The normalised bipartite current -/

/-- The normalised complete bipartite current on `H × D`. -/
noncomputable def bipartiteCurrent (H D : Finset F) (e : F × F) : ℝ :=
  if e.1 ∈ H ∧ e.2 ∈ D then (1 : ℝ) / ((H.card : ℝ) * (D.card : ℝ)) else 0

omit [Fintype F] in
theorem bipartiteCurrent_nonneg (H D : Finset F) (e : F × F) : 0 ≤ bipartiteCurrent H D e := by
  rw [bipartiteCurrent]
  split_ifs
  · positivity
  · exact le_rfl

omit [Fintype F] in
theorem bipartiteCurrent_eq_zero_of_empty (H : Finset F) (e : F × F) :
    bipartiteCurrent H (∅ : Finset F) e = 0 := by
  rw [bipartiteCurrent]
  simp

/-- **Total oriented mass one.** -/
theorem sum_bipartiteCurrent {H D : Finset F} (hH : H.Nonempty) (hD : D.Nonempty) :
    ∑ e : F × F, bipartiteCurrent H D e = 1 := by
  have hHc : (0 : ℝ) < H.card := by
    exact_mod_cast Finset.card_pos.mpr hH
  have hDc : (0 : ℝ) < D.card := by
    exact_mod_cast Finset.card_pos.mpr hD
  have hfilter : (Finset.univ.filter fun e : F × F => e.1 ∈ H ∧ e.2 ∈ D) = H ×ˢ D := by
    ext e
    simp [Finset.mem_product]
  simp only [bipartiteCurrent]
  rw [← Finset.sum_filter, hfilter, Finset.sum_const, Finset.card_product, nsmul_eq_mul]
  push_cast
  field_simp

/-- **Squared `ℓ²` norm.** -/
theorem sum_sq_bipartiteCurrent {H D : Finset F} (hH : H.Nonempty) (hD : D.Nonempty) :
    ∑ e : F × F, (bipartiteCurrent H D e) ^ 2 = 1 / ((H.card : ℝ) * (D.card : ℝ)) := by
  have hHc : (0 : ℝ) < H.card := by
    exact_mod_cast Finset.card_pos.mpr hH
  have hDc : (0 : ℝ) < D.card := by
    exact_mod_cast Finset.card_pos.mpr hD
  have hfilter : (Finset.univ.filter fun e : F × F => e.1 ∈ H ∧ e.2 ∈ D) = H ×ˢ D := by
    ext e
    simp [Finset.mem_product]
  have hpt : ∀ e : F × F, (bipartiteCurrent H D e) ^ 2
      = if e.1 ∈ H ∧ e.2 ∈ D then (1 : ℝ) / ((H.card : ℝ) * (D.card : ℝ)) ^ 2 else 0 := by
    intro e
    rw [bipartiteCurrent]
    split_ifs
    · rw [div_pow, one_pow]
    · exact zero_pow two_ne_zero
  rw [Finset.sum_congr rfl fun e _ => hpt e]
  rw [← Finset.sum_filter, hfilter, Finset.sum_const, Finset.card_product, nsmul_eq_mul]
  push_cast
  field_simp

/-! ## The boundary map -/

/-- The oriented boundary of an edge current, valued on coloured vertices. -/
def edgeBoundary (J : F × F → ℝ) : F ⊕ F → ℝ
  | Sum.inl a => -(∑ p : F, J (a, p))
  | Sum.inr p => ∑ a : F, J (a, p)

/-- **The boundary of the bipartite current is the difference of uniform vertex measures.** -/
theorem edgeBoundary_bipartiteCurrent {H D : Finset F} (hH : H.Nonempty) (hD : D.Nonempty) :
    edgeBoundary (bipartiteCurrent H D)
      = fun v => match v with
        | Sum.inl a => -(if a ∈ H then (1 : ℝ) / (H.card : ℝ) else 0)
        | Sum.inr p => if p ∈ D then (1 : ℝ) / (D.card : ℝ) else 0 := by
  have hHc : (0 : ℝ) < H.card := by
    exact_mod_cast Finset.card_pos.mpr hH
  have hDc : (0 : ℝ) < D.card := by
    exact_mod_cast Finset.card_pos.mpr hD
  funext v
  rcases v with a | p
  · simp only [edgeBoundary]
    congr 1
    by_cases ha : a ∈ H
    · rw [if_pos ha]
      have hpt : ∀ p : F, bipartiteCurrent H D (a, p)
          = if p ∈ D then (1 : ℝ) / ((H.card : ℝ) * (D.card : ℝ)) else 0 := by
        intro p
        rw [bipartiteCurrent]
        by_cases hp : p ∈ D <;> simp [ha, hp]
      rw [Finset.sum_congr rfl fun p _ => hpt p, Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_const, nsmul_eq_mul]
      field_simp
    · rw [if_neg ha]
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [bipartiteCurrent]
      simp [ha]
  · simp only [edgeBoundary]
    by_cases hp : p ∈ D
    · rw [if_pos hp]
      have hpt : ∀ a : F, bipartiteCurrent H D (a, p)
          = if a ∈ H then (1 : ℝ) / ((H.card : ℝ) * (D.card : ℝ)) else 0 := by
        intro a
        rw [bipartiteCurrent]
        by_cases ha : a ∈ H <;> simp [ha, hp]
      rw [Finset.sum_congr rfl fun a _ => hpt a, Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_const, nsmul_eq_mul]
      field_simp
    · rw [if_neg hp]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [bipartiteCurrent]
      simp [hp]

omit [DecidableEq F] in
theorem edgeBoundary_sub (J K : F × F → ℝ) :
    edgeBoundary (J - K) = edgeBoundary J - edgeBoundary K := by
  funext v
  rcases v with a | p <;> simp only [edgeBoundary, Pi.sub_apply, Finset.sum_sub_distrib]
  ring

/-! ## The convex split of a disjoint defect union -/

omit [Fintype F] in
/-- **Convex decomposition of the current over a split defect set.** -/
theorem bipartiteCurrent_union {H O L : Finset F} (hO : O.Nonempty) (hL : L.Nonempty)
    (hdisj : Disjoint O L) :
    bipartiteCurrent H (O ∪ L)
      = fun e => ((O.card : ℝ) / ((O.card : ℝ) + (L.card : ℝ))) * bipartiteCurrent H O e
        + ((L.card : ℝ) / ((O.card : ℝ) + (L.card : ℝ))) * bipartiteCurrent H L e := by
  have hOc : (0 : ℝ) < O.card := by
    exact_mod_cast Finset.card_pos.mpr hO
  have hLc : (0 : ℝ) < L.card := by
    exact_mod_cast Finset.card_pos.mpr hL
  have hcard : ((O ∪ L).card : ℝ) = (O.card : ℝ) + (L.card : ℝ) := by
    rw [Finset.card_union_of_disjoint hdisj]
    push_cast
    ring
  funext e
  by_cases ha : e.1 ∈ H
  · by_cases hOm : e.2 ∈ O
    · have hLm : e.2 ∉ L := Finset.disjoint_left.mp hdisj hOm
      have hmem : e.2 ∈ O ∪ L := Finset.mem_union_left _ hOm
      rw [bipartiteCurrent, bipartiteCurrent, bipartiteCurrent, if_pos ⟨ha, hmem⟩,
        if_pos ⟨ha, hOm⟩, if_neg (by simp [hLm]), hcard]
      field_simp
      ring
    · by_cases hLm : e.2 ∈ L
      · have hmem : e.2 ∈ O ∪ L := Finset.mem_union_right _ hLm
        rw [bipartiteCurrent, bipartiteCurrent, bipartiteCurrent, if_pos ⟨ha, hmem⟩,
          if_neg (by simp [hOm]), if_pos ⟨ha, hLm⟩, hcard]
        field_simp
        ring
      · have hmem : e.2 ∉ O ∪ L := by simp [hOm, hLm]
        rw [bipartiteCurrent, bipartiteCurrent, bipartiteCurrent, if_neg (by simp [hmem]),
          if_neg (by simp [hOm]), if_neg (by simp [hLm])]
        ring
  · rw [bipartiteCurrent, bipartiteCurrent, bipartiteCurrent, if_neg (by simp [ha]),
      if_neg (by simp [ha]), if_neg (by simp [ha])]
    ring

omit [Fintype F] in
/-- **The exact interchange defect.** -/
theorem interchange_defect {H O L : Finset F} (hO : O.Nonempty) (hL : L.Nonempty)
    (hdisj : Disjoint O L) :
    bipartiteCurrent H (O ∪ L) - bipartiteCurrent H O
      = fun e => ((L.card : ℝ) / ((O.card : ℝ) + (L.card : ℝ)))
        * (bipartiteCurrent H L e - bipartiteCurrent H O e) := by
  have hOc : (0 : ℝ) < O.card := by
    exact_mod_cast Finset.card_pos.mpr hO
  have hLc : (0 : ℝ) < L.card := by
    exact_mod_cast Finset.card_pos.mpr hL
  funext e
  have h : bipartiteCurrent H (O ∪ L) e
      = ((O.card : ℝ) / ((O.card : ℝ) + (L.card : ℝ))) * bipartiteCurrent H O e
        + ((L.card : ℝ) / ((O.card : ℝ) + (L.card : ℝ))) * bipartiteCurrent H L e := by
    simpa using congrFun (bipartiteCurrent_union (H := H) hO hL hdisj) e
  simp only [Pi.sub_apply]
  rw [h]
  field_simp
  ring

/-! ## Norms of the interchange defect -/

theorem sum_abs_interchange_defect {H O L : Finset F} (hH : H.Nonempty) (hO : O.Nonempty)
    (hL : L.Nonempty) (hdisj : Disjoint O L) :
    ∑ e : F × F, |bipartiteCurrent H (O ∪ L) e - bipartiteCurrent H O e|
      = 2 * (L.card : ℝ) / ((O.card : ℝ) + (L.card : ℝ)) := by
  have hOc : (0 : ℝ) < O.card := by
    exact_mod_cast Finset.card_pos.mpr hO
  have hLc : (0 : ℝ) < L.card := by
    exact_mod_cast Finset.card_pos.mpr hL
  have hsum : (0 : ℝ) < (O.card : ℝ) + (L.card : ℝ) := by linarith
  have hpt : ∀ e : F × F, |bipartiteCurrent H (O ∪ L) e - bipartiteCurrent H O e|
      = ((L.card : ℝ) / ((O.card : ℝ) + (L.card : ℝ)))
        * (bipartiteCurrent H L e + bipartiteCurrent H O e) := by
    intro e
    rw [show bipartiteCurrent H (O ∪ L) e - bipartiteCurrent H O e
        = ((L.card : ℝ) / ((O.card : ℝ) + (L.card : ℝ)))
          * (bipartiteCurrent H L e - bipartiteCurrent H O e) from by
      simpa using congrFun (interchange_defect (H := H) hO hL hdisj) e, abs_mul,
      abs_of_pos (by positivity)]
    congr 1
    by_cases hLm : e.2 ∈ L
    · have hOm : e.2 ∉ O := Finset.disjoint_right.mp hdisj hLm
      have h0 : bipartiteCurrent H O e = 0 := by
        rw [bipartiteCurrent]
        simp [hOm]
      rw [h0, sub_zero, add_zero, abs_of_nonneg (bipartiteCurrent_nonneg H L e)]
    · have h0 : bipartiteCurrent H L e = 0 := by
        rw [bipartiteCurrent]
        simp [hLm]
      rw [h0, zero_sub, zero_add, abs_neg, abs_of_nonneg (bipartiteCurrent_nonneg H O e)]
  rw [Finset.sum_congr rfl fun e _ => hpt e, ← Finset.mul_sum, Finset.sum_add_distrib,
    sum_bipartiteCurrent hH hL, sum_bipartiteCurrent hH hO]
  ring

/-- **Zero net mass of the interchange defect.** -/
theorem sum_interchange_defect {H O L : Finset F} (hH : H.Nonempty) (hO : O.Nonempty)
    (hL : L.Nonempty) (hdisj : Disjoint O L) :
    ∑ e : F × F, (bipartiteCurrent H (O ∪ L) e - bipartiteCurrent H O e) = 0 := by
  have hdef : ∀ e : F × F, bipartiteCurrent H (O ∪ L) e - bipartiteCurrent H O e
      = ((L.card : ℝ) / ((O.card : ℝ) + (L.card : ℝ)))
        * (bipartiteCurrent H L e - bipartiteCurrent H O e) := fun e => by
    simpa using congrFun (interchange_defect (H := H) hO hL hdisj) e
  rw [Finset.sum_congr rfl fun e _ => hdef e, ← Finset.mul_sum, Finset.sum_sub_distrib,
    sum_bipartiteCurrent hH hL, sum_bipartiteCurrent hH hO]
  ring

/-! ## The three-stage Bianchi identity -/

/-- **Exact interchange Bianchi identity.**  For any transport that is additive and composes
strictly, the three-stage interchange defects satisfy the coboundary relation
`Ω_{m;t,sr} + T_t Ω_{m;s,r} = Ω_{m;ts,r} + Ω_{rm;t,s}`. -/
theorem interchange_bianchi {E : Type*} [AddCommGroup E]
    (T : ℕ → E → E) (hT : ∀ s t x, T t (T s x) = T (t * s) x)
    (hTsub : ∀ t x y, T t (x - y) = T t x - T t y)
    (J : ℕ → ℕ → E) (m r s t : ℕ) :
    (J m (t * (s * r)) - J (s * r * m) t - T t (J m (s * r)))
        + T t (J m (s * r) - J (r * m) s - T s (J m r))
      = (J m (t * s * r) - J (r * m) (t * s) - T (t * s) (J m r))
        + (J (r * m) (t * s) - J (s * (r * m)) t - T t (J (r * m) s)) := by
  rw [hTsub, hTsub, hT, mul_assoc t s r, mul_assoc s r m]
  abel

end HTGeometry.ConstraintFrameRelativity
