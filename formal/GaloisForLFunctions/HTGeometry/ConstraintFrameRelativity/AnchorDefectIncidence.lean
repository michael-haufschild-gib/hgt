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
    ∑ e : F × F, (bipartiteCurrent H D e) ^ (2 : ℕ) = 1 / ((H.card : ℝ) * (D.card : ℝ)) := by
  have hHc : (0 : ℝ) < H.card := by
    exact_mod_cast Finset.card_pos.mpr hH
  have hDc : (0 : ℝ) < D.card := by
    exact_mod_cast Finset.card_pos.mpr hD
  have hfilter : (Finset.univ.filter fun e : F × F => e.1 ∈ H ∧ e.2 ∈ D) = H ×ˢ D := by
    ext e
    simp [Finset.mem_product]
  have hpt : ∀ e : F × F, (bipartiteCurrent H D e) ^ (2 : ℕ)
      = if e.1 ∈ H ∧ e.2 ∈ D then (1 : ℝ) / ((H.card : ℝ) * (D.card : ℝ)) ^ (2 : ℕ) else 0 := by
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

/-! ## The arithmetic anchor and defect sets -/

section Arithmetic

variable {A : Finset ℕ}

/-- The anchor set: primes of the aperture attaining the shell height. -/
def anchorSet (A : Finset ℕ) (M N : ℕ) : Finset ℕ :=
  A.filter fun p => N.factorization p = M

/-- The defect set: primes of the aperture whose exponent is not divisible by `q`. -/
def defectSet (A : Finset ℕ) (q N : ℕ) : Finset ℕ :=
  A.filter fun p => ¬ q ∣ N.factorization p

theorem mem_anchorSet {A : Finset ℕ} {M N p : ℕ} :
    p ∈ anchorSet A M N ↔ p ∈ A ∧ N.factorization p = M := by
  simp [anchorSet]

theorem mem_defectSet {A : Finset ℕ} {q N p : ℕ} :
    p ∈ defectSet A q N ↔ p ∈ A ∧ ¬ q ∣ N.factorization p := by
  simp [defectSet]

/-- **Anchors are disjoint from defects** when the divisor divides the shell height. -/
theorem anchorSet_disjoint_defectSet {A : Finset ℕ} {M q N : ℕ} (hqM : q ∣ M) :
    Disjoint (anchorSet A M N) (defectSet A q N) := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  obtain ⟨-, hM⟩ := mem_anchorSet.mp hp
  obtain ⟨-, hq⟩ := mem_defectSet.mp hp'
  exact hq (hM ▸ hqM)

/-- **The defect set is empty exactly when every aperture exponent is a multiple of `q`.** -/
theorem defectSet_eq_empty_iff {A : Finset ℕ} {q N : ℕ} :
    defectSet A q N = ∅ ↔ ∀ p ∈ A, q ∣ N.factorization p := by
  constructor
  · intro h p hp
    by_contra hq
    have : p ∈ defectSet A q N := mem_defectSet.mpr ⟨hp, hq⟩
    rw [h] at this
    simp at this
  · intro h
    refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
    obtain ⟨hpA, hq⟩ := mem_defectSet.mp hp
    exact hq (h p hpA)

/-- **The direct defect set splits into outer and latent-inner layers.** -/
theorem defectSet_mul_eq_union {A : Finset ℕ} {s r N : ℕ} :
    defectSet A (s * r) N = defectSet A s N ∪ (defectSet A (s * r) N \ defectSet A s N) := by
  refine (Finset.union_sdiff_of_subset ?_).symm
  intro p hp
  obtain ⟨hpA, hq⟩ := mem_defectSet.mp hp
  refine mem_defectSet.mpr ⟨hpA, fun hdvd => hq ?_⟩
  exact dvd_trans (Dvd.intro r rfl) hdvd

theorem defectSet_disjoint_sdiff {A : Finset ℕ} {s r N : ℕ} :
    Disjoint (defectSet A s N) (defectSet A (s * r) N \ defectSet A s N) :=
  Finset.disjoint_sdiff

/-! ## The three-prime witness -/

theorem factorization_three_primes {p₀ p₁ p₂ : ℕ} (h0 : p₀.Prime) (h1 : p₁.Prime)
    (h2 : p₂.Prime) (a b c q : ℕ) :
    (p₀ ^ a * p₁ ^ b * p₂ ^ c).factorization q
      = (if q = p₀ then a else 0) + (if q = p₁ then b else 0) + (if q = p₂ then c else 0) := by
  have hn0 : (p₀ : ℕ) ^ a ≠ 0 := pow_ne_zero _ h0.ne_zero
  have hn1 : (p₁ : ℕ) ^ b ≠ 0 := pow_ne_zero _ h1.ne_zero
  have hn2 : (p₂ : ℕ) ^ c ≠ 0 := pow_ne_zero _ h2.ne_zero
  rw [Nat.factorization_mul (Nat.mul_ne_zero hn0 hn1) hn2,
    Nat.factorization_mul hn0 hn1, Nat.factorization_pow, Nat.factorization_pow,
    Nat.factorization_pow, h0.factorization, h1.factorization, h2.factorization]
  simp [Finsupp.single_apply, eq_comm]

/-- **The unconditional nonzero witness.**  For three distinct primes and `m, r, s ≥ 2` the
anchor set is `{p₀}`, the outer layer is `{p₂}` and the latent-inner layer is `{p₁}`. -/
theorem witness_layers {p₀ p₁ p₂ m r s : ℕ} (h0 : p₀.Prime) (h1 : p₁.Prime) (h2 : p₂.Prime)
    (h01 : p₀ ≠ p₁) (h02 : p₀ ≠ p₂) (h12 : p₁ ≠ p₂) (hm : 2 ≤ m) (hr : 2 ≤ r) (hs : 2 ≤ s) :
    anchorSet {p₀, p₁, p₂} (s * r * m) (p₀ ^ (s * r * m) * p₁ ^ s * p₂ ^ (1 : ℕ)) = {p₀}
      ∧ defectSet {p₀, p₁, p₂} s (p₀ ^ (s * r * m) * p₁ ^ s * p₂ ^ (1 : ℕ)) = {p₂}
      ∧ defectSet {p₀, p₁, p₂} (s * r) (p₀ ^ (s * r * m) * p₁ ^ s * p₂ ^ (1 : ℕ))
          \ defectSet {p₀, p₁, p₂} s (p₀ ^ (s * r * m) * p₁ ^ s * p₂ ^ (1 : ℕ)) = {p₁} := by
  set N : ℕ := p₀ ^ (s * r * m) * p₁ ^ s * p₂ ^ (1 : ℕ) with hN
  have hfac := factorization_three_primes h0 h1 h2 (s * r * m) s 1
  have e0 : N.factorization p₀ = s * r * m := by
    rw [hN, hfac]
    simp [h01, h02]
  have e1 : N.factorization p₁ = s := by
    rw [hN, hfac]
    simp [Ne.symm h01, h12]
  have e2 : N.factorization p₂ = 1 := by
    rw [hN, hfac]
    simp [Ne.symm h02, Ne.symm h12]
  have hsr_pos : 0 < s * r := by positivity
  have hsrm_lb : 4 * s ≤ s * r * m := by nlinarith
  have hsrm2 : 2 ≤ s * r * m := by nlinarith
  have hdvd_s : s ∣ s * r * m := ⟨r * m, by ring⟩
  have hdvd_sr : s * r ∣ s * r * m := ⟨m, rfl⟩
  have hnd_s_one : ¬ s ∣ 1 := fun h => by
    have hs1 := Nat.le_of_dvd one_pos h
    omega
  have hnd_sr_s : ¬ s * r ∣ s := fun h => by
    have := Nat.le_of_dvd (by omega) h
    nlinarith
  have hnd_sr_one : ¬ s * r ∣ 1 := fun h => by
    have := Nat.le_of_dvd one_pos h
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · ext p
    simp only [mem_anchorSet, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hmem, hval⟩
      rcases hmem with h | h | h
      · exact h
      · rw [h, e1] at hval
        omega
      · rw [h, e2] at hval
        omega
    · rintro rfl
      exact ⟨Or.inl rfl, e0⟩
  · ext p
    simp only [mem_defectSet, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hmem, hval⟩
      rcases hmem with h | h | h
      · rw [h, e0] at hval
        exact absurd hdvd_s hval
      · rw [h, e1] at hval
        exact absurd dvd_rfl hval
      · exact h
    · rintro rfl
      refine ⟨Or.inr (Or.inr rfl), ?_⟩
      rw [e2]
      exact hnd_s_one
  · ext p
    simp only [Finset.mem_sdiff, mem_defectSet, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hmem, hval⟩, hnot⟩
      rcases hmem with h | h | h
      · rw [h, e0] at hval
        exact absurd hdvd_sr hval
      · exact h
      · exact absurd ⟨Or.inr (Or.inr h), by rw [h, e2]; exact hnd_s_one⟩ hnot
    · rintro rfl
      refine ⟨⟨Or.inr (Or.inl rfl), ?_⟩, ?_⟩
      · rw [e1]
        exact hnd_sr_s
      · rintro ⟨-, hval⟩
        rw [e1] at hval
        exact hval dvd_rfl

/-! ## Ordered first-failure flags -/

/-- Defect sets increase along divisibility. -/
theorem defectSet_mono {A : Finset ℕ} {d e N : ℕ} (h : d ∣ e) :
    defectSet A d N ⊆ defectSet A e N := by
  intro p hp
  obtain ⟨hpA, hq⟩ := mem_defectSet.mp hp
  exact mem_defectSet.mpr ⟨hpA, fun hdvd => hq (dvd_trans h hdvd)⟩

/-- The ordered first-failure layer of a chain of divisors. -/
def failureLayer (A : Finset ℕ) (d : ℕ → ℕ) (N i : ℕ) : Finset ℕ :=
  defectSet A (d (i + 1)) N \ defectSet A (d i) N

theorem chain_dvd {d : ℕ → ℕ} (hd : ∀ i, d i ∣ d (i + 1)) {i j : ℕ} (hij : i ≤ j) :
    d i ∣ d j := by
  induction j with
  | zero => simp [Nat.le_zero.mp hij]
  | succ n ih =>
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · exact dvd_trans (ih (Nat.lt_succ_iff.mp h)) (hd n)
    · have : i = n + 1 := le_antisymm hij h
      simp [this]

/-- **The ordered failure flags are pairwise disjoint.** -/
theorem failureLayer_disjoint {A : Finset ℕ} {d : ℕ → ℕ} (hd : ∀ i, d i ∣ d (i + 1)) (N : ℕ)
    {i j : ℕ} (hij : i < j) :
    Disjoint (failureLayer A d N i) (failureLayer A d N j) := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  have hpi : p ∈ defectSet A (d (i + 1)) N := (Finset.mem_sdiff.mp hp).1
  have hpj : p ∉ defectSet A (d j) N := (Finset.mem_sdiff.mp hp').2
  exact hpj (defectSet_mono (chain_dvd hd (Nat.succ_le_of_lt hij)) hpi)

/-- **The direct defect set is the base layer together with the ordered failure flags.** -/
theorem defectSet_eq_union_failureLayers {A : Finset ℕ} {d : ℕ → ℕ} (hd : ∀ i, d i ∣ d (i + 1))
    (N : ℕ) : ∀ k : ℕ,
      defectSet A (d k) N
        = defectSet A (d 0) N ∪ (Finset.range k).biUnion (failureLayer A d N) := by
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
    have hrange : Finset.range (n + 1) = insert n (Finset.range n) := by
      ext j
      simp
      omega
    rw [hrange, Finset.biUnion_insert]
    ext p
    simp only [Finset.mem_union]
    constructor
    · intro hp
      by_cases hpn : p ∈ defectSet A (d n) N
      · rw [ih] at hpn
        rcases Finset.mem_union.mp hpn with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl (Finset.mem_sdiff.mpr ⟨hp, hpn⟩))
    · rintro (h | h | h)
      · refine defectSet_mono (hd n) ?_
        rw [ih]
        exact Finset.mem_union_left _ h
      · exact (Finset.mem_sdiff.mp h).1
      · refine defectSet_mono (hd n) ?_
        rw [ih]
        exact Finset.mem_union_right _ h

/-- **Refined incidence agrees with direct incidence.**  Splitting the defect set splits the
incidence rectangle. -/
theorem product_union (H O L : Finset ℕ) :
    H ×ˢ (O ∪ L) = (H ×ˢ O) ∪ (H ×ˢ L) := by
  ext e
  simp only [Finset.mem_product, Finset.mem_union]
  tauto

end Arithmetic

end HTGeometry.ConstraintFrameRelativity
