import GaloisForLFunctions.HTGeometry.WeightedMinimax.SignRealization

/-!
# Roots, coefficient signs, and sign realization inside a coefficient hyperplane

Three purely algebraic facts feed the coefficient duality of the weighted minimax problem.

* Every coefficient of a monic product of linear factors with **positive** roots is nonzero, with
  sign alternating in the coefficient index (`prod_X_sub_C_coeff_sign`). Hence a nonzero polynomial
  of degree at most `n` with `n` distinct positive roots has all coefficients up to index `n`
  nonzero (`coeff_ne_zero_of_positive_roots`): the space `{p : deg p ≤ n, coeff j p = 0}` is a Haar
  space of dimension `n` on the positive half-line.
* Strictly alternating values at `n+1` increasing positive nodes produce `n` distinct positive roots
  (`roots_finset_of_alternating`).
* A finite sign pattern on `m+1` positive nodes with `m+1 ≤ n` is realized by a polynomial of
  degree at most `n` whose `j`-th coefficient vanishes (`exists_sign_realizing_coeffKer`): correct
  the unconstrained realizer by a multiple of the polynomial vanishing at all the nodes.
-/

namespace GaloisForLFunctions.HTGeometry.WeightedMinimax

noncomputable section
open Set Polynomial

/-! ### Products of linear factors -/

theorem natDegree_prod_X_sub_C (s : Finset ℝ) :
    (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).natDegree = s.card := by
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun r _ => Polynomial.monic_X_sub_C r)]
  simp

theorem monic_prod_X_sub_C (s : Finset ℝ) :
    (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun r _ => Polynomial.monic_X_sub_C r)

theorem prod_X_sub_C_dvd {s : Finset ℝ} {d : Polynomial ℝ} (hroots : ∀ r ∈ s, d.eval r = 0) :
    (∏ r ∈ s, (Polynomial.X - Polynomial.C r)) ∣ d := by
  classical
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · intro x hx y hy hxy
    exact Polynomial.pairwise_coprime_X_sub_C (Function.injective_id) hxy
  · intro r hr
    exact Polynomial.dvd_iff_isRoot.mpr (hroots r hr)

theorem prod_X_sub_C_eval_eq_zero {s : Finset ℝ} {y : ℝ} (hy : y ∈ s) :
    (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).eval y = 0 := by
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero hy (by simp)

/-- Every coefficient of a monic product of linear factors with positive roots is nonzero, with
sign alternating in the coefficient index. -/
theorem prod_X_sub_C_coeff_sign : ∀ s : Finset ℝ, (∀ r ∈ s, 0 < r) → ∀ j ≤ s.card,
    0 < (-1 : ℝ) ^ (s.card - j) * (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).coeff j := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ j hj
    simp only [Finset.card_empty, Nat.le_zero] at hj
    subst hj
    simp
  | insert c s hc ih =>
    intro hpos j hj
    have hcpos : 0 < c := hpos c (Finset.mem_insert_self c s)
    have hspos : ∀ r ∈ s, 0 < r := fun r hr => hpos r (Finset.mem_insert_of_mem hr)
    have hcard : (insert c s).card = s.card + 1 := Finset.card_insert_of_notMem hc
    rw [hcard] at hj ⊢
    rw [Finset.prod_insert hc]
    have hPdeg : (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).natDegree = s.card :=
      natDegree_prod_X_sub_C s
    match j with
    | 0 =>
      have hc0 : ((Polynomial.X - Polynomial.C c) *
          ∏ r ∈ s, (Polynomial.X - Polynomial.C r)).coeff 0
          = -c * (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).coeff 0 := by
        rw [Polynomial.mul_coeff_zero]
        simp
      rw [hc0]
      have hih := ih hspos 0 (Nat.zero_le _)
      have hpow : (-1 : ℝ) ^ (s.card + 1 - 0) = -((-1 : ℝ) ^ (s.card - 0)) := by
        simp only [Nat.sub_zero]
        rw [pow_succ]
        ring
      rw [hpow]
      simp only [Nat.sub_zero] at hih ⊢
      nlinarith
    | (k + 1) =>
      have hk : k ≤ s.card := by omega
      have hck : ((Polynomial.X - Polynomial.C c) *
          ∏ r ∈ s, (Polynomial.X - Polynomial.C r)).coeff (k + 1)
          = (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).coeff k
            - c * (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).coeff (k + 1) := by
        rw [show (Polynomial.X - Polynomial.C c) * ∏ r ∈ s, (Polynomial.X - Polynomial.C r)
            = Polynomial.X * ∏ r ∈ s, (Polynomial.X - Polynomial.C r)
              - Polynomial.C c * ∏ r ∈ s, (Polynomial.X - Polynomial.C r) by ring,
          Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]
      rw [hck, Nat.succ_sub_succ]
      have h1 : 0 < (-1 : ℝ) ^ (s.card - k) *
          (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).coeff k := ih hspos k hk
      rcases Nat.lt_or_ge k s.card with hks | hks
      · have h2 : 0 < (-1 : ℝ) ^ (s.card - (k + 1)) *
            (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).coeff (k + 1) := ih hspos (k + 1) (by omega)
        have hpow : (-1 : ℝ) ^ (s.card - k) = -((-1 : ℝ) ^ (s.card - (k + 1))) := by
          have he : s.card - k = (s.card - (k + 1)) + 1 := by omega
          rw [he, pow_succ]
          ring
        rw [hpow] at h1 ⊢
        nlinarith [mul_pos hcpos h2]
      · have h3 : (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).coeff (k + 1) = 0 := by
          refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
          rw [hPdeg]
          omega
        rw [h3]
        nlinarith

/-- The penultimate coefficient of a monic product of linear factors is minus the sum of the
roots. -/
theorem prod_X_sub_C_coeff_pred : ∀ s : Finset ℝ, s.Nonempty →
    (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).coeff (s.card - 1) = -∑ r ∈ s, r := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro h; exact absurd h (by simp)
  | insert c s hc ih =>
    intro _
    have hcard : (insert c s).card = s.card + 1 := Finset.card_insert_of_notMem hc
    rw [hcard, Nat.add_sub_cancel, Finset.prod_insert hc, Finset.sum_insert hc]
    have hPdeg : (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).natDegree = s.card :=
      natDegree_prod_X_sub_C s
    rcases Finset.eq_empty_or_nonempty s with rfl | hsne
    · simp
    · have hm : 1 ≤ s.card := Finset.card_pos.mpr hsne
      have hx : (Polynomial.X * ∏ r ∈ s, (Polynomial.X - Polynomial.C r)).coeff s.card
          = (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).coeff (s.card - 1) := by
        obtain ⟨k, hk⟩ : ∃ k, s.card = k + 1 := ⟨s.card - 1, by omega⟩
        rw [hk, Polynomial.coeff_X_mul]
        simp
      have hck : ((Polynomial.X - Polynomial.C c) *
          ∏ r ∈ s, (Polynomial.X - Polynomial.C r)).coeff s.card
          = (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).coeff (s.card - 1)
            - c * (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).coeff s.card := by
        rw [show (Polynomial.X - Polynomial.C c) * ∏ r ∈ s, (Polynomial.X - Polynomial.C r)
            = Polynomial.X * ∏ r ∈ s, (Polynomial.X - Polynomial.C r)
              - Polynomial.C c * ∏ r ∈ s, (Polynomial.X - Polynomial.C r) by ring,
          Polynomial.coeff_sub, Polynomial.coeff_C_mul, hx]
      have hlead : (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).coeff s.card = 1 := by
        have h1 := (monic_prod_X_sub_C s).coeff_natDegree
        rwa [hPdeg] at h1
      rw [hck, ih hsne, hlead]
      ring

/-- A nonzero polynomial of degree at most `n` with `n` distinct positive roots has every
coefficient up to index `n` nonzero. -/
theorem coeff_ne_zero_of_positive_roots {d : Polynomial ℝ} {n : ℕ} (hd : d ≠ 0)
    (hdeg : d.natDegree ≤ n) {s : Finset ℝ} (hcard : s.card = n) (hspos : ∀ r ∈ s, 0 < r)
    (hroots : ∀ r ∈ s, d.eval r = 0) : ∀ j ≤ n, d.coeff j ≠ 0 := by
  classical
  obtain ⟨q, hq⟩ := prod_X_sub_C_dvd hroots
  have hPne : (∏ r ∈ s, (Polynomial.X - Polynomial.C r)) ≠ 0 := (monic_prod_X_sub_C s).ne_zero
  have hqne : q ≠ 0 := by
    intro h
    rw [h, mul_zero] at hq
    exact hd hq
  have hPdeg : (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).natDegree = n := by
    rw [natDegree_prod_X_sub_C s, hcard]
  have hsum : d.natDegree
      = (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).natDegree + q.natDegree := by
    rw [hq, Polynomial.natDegree_mul hPne hqne]
  have hq0 : q.natDegree = 0 := by omega
  obtain ⟨cq, hcq⟩ := Polynomial.natDegree_eq_zero.mp hq0
  have hcqne : cq ≠ 0 := by
    intro h
    rw [h, map_zero] at hcq
    exact hqne hcq.symm
  intro j hj
  rw [hq, ← hcq, mul_comm, Polynomial.coeff_C_mul]
  have hsign := prod_X_sub_C_coeff_sign s hspos j (by rw [hcard]; exact hj)
  refine mul_ne_zero hcqne ?_
  intro h
  rw [h, mul_zero] at hsign
  exact absurd hsign (lt_irrefl 0)

/-- A monic polynomial of degree `n` with `n` distinct roots is their product of linear factors. -/
theorem eq_prod_X_sub_C_of_monic {T : Polynomial ℝ} {n : ℕ} (hmonic : T.Monic)
    (hdeg : T.natDegree = n) {s : Finset ℝ} (hcard : s.card = n)
    (hroots : ∀ r ∈ s, T.eval r = 0) :
    T = ∏ r ∈ s, (Polynomial.X - Polynomial.C r) := by
  classical
  obtain ⟨q, hq⟩ := prod_X_sub_C_dvd hroots
  have hPm : (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).Monic := monic_prod_X_sub_C s
  have hPdeg : (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).natDegree = n := by
    rw [natDegree_prod_X_sub_C s, hcard]
  have hTne : T ≠ 0 := hmonic.ne_zero
  have hqne : q ≠ 0 := by
    intro h
    rw [h, mul_zero] at hq
    exact hTne hq
  have hsum : T.natDegree
      = (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).natDegree + q.natDegree := by
    rw [hq, Polynomial.natDegree_mul hPm.ne_zero hqne]
  have hq0 : q.natDegree = 0 := by omega
  obtain ⟨cq, hcq⟩ := Polynomial.natDegree_eq_zero.mp hq0
  have hlead : T.leadingCoeff
      = (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).leadingCoeff * q.leadingCoeff := by
    rw [hq, Polynomial.leadingCoeff_mul]
  rw [hmonic.leadingCoeff, hPm.leadingCoeff, ← hcq, Polynomial.leadingCoeff_C, one_mul] at hlead
  rw [hq, ← hcq, ← hlead]
  simp

/-! ### Alternating values give distinct roots -/

/-- From `n+1` strictly alternating nodes one extracts one root strictly inside each gap. -/
theorem exists_roots_of_alternating {d : Polynomial ℝ} {n : ℕ} {z : ℕ → ℝ}
    (hz : ∀ i < n, z i < z (i + 1)) (halt : ∀ i < n, d.eval (z i) * d.eval (z (i + 1)) < 0) :
    ∃ r : ℕ → ℝ, (∀ i < n, z i < r i ∧ r i < z (i + 1)) ∧ (∀ i < n, d.eval (r i) = 0) := by
  have hex : ∀ i, ∃ y, i < n → (z i < y ∧ y < z (i + 1) ∧ d.eval y = 0) := by
    intro i
    by_cases hi : i < n
    · have hlt := hz i hi
      have hsign := halt i hi
      have hcont : ContinuousOn (fun y => d.eval y) (Set.Icc (z i) (z (i + 1))) :=
        (Polynomial.continuous d).continuousOn
      rcases lt_trichotomy (d.eval (z i)) 0 with h | h | h
      · have h2 : 0 < d.eval (z (i + 1)) := by nlinarith
        have hsub : Set.Ioo (d.eval (z i)) (d.eval (z (i + 1))) ⊆
            (fun y => d.eval y) '' Set.Ioo (z i) (z (i + 1)) :=
          intermediate_value_Ioo (le_of_lt hlt) hcont
        obtain ⟨y, hy, hy0⟩ := hsub ⟨h, h2⟩
        exact ⟨y, fun _ => ⟨hy.1, hy.2, hy0⟩⟩
      · exact absurd hsign (by rw [h]; simp)
      · have h2 : d.eval (z (i + 1)) < 0 := by nlinarith
        have hsub : Set.Ioo (d.eval (z (i + 1))) (d.eval (z i)) ⊆
            (fun y => d.eval y) '' Set.Ioo (z i) (z (i + 1)) :=
          intermediate_value_Ioo' (le_of_lt hlt) hcont
        obtain ⟨y, hy, hy0⟩ := hsub ⟨h2, h⟩
        exact ⟨y, fun _ => ⟨hy.1, hy.2, hy0⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose r hr using hex
  exact ⟨r, fun i hi => ⟨(hr i hi).1, (hr i hi).2.1⟩, fun i hi => (hr i hi).2.2⟩

/-- Strictly alternating values at `n+1` increasing positive nodes give `n` distinct positive
roots. -/
theorem roots_finset_of_alternating {d : Polynomial ℝ} {n : ℕ} {z : ℕ → ℝ}
    (hz : ∀ i < n, z i < z (i + 1)) (hz0 : 0 < z 0)
    (halt : ∀ i < n, d.eval (z i) * d.eval (z (i + 1)) < 0) :
    ∃ s : Finset ℝ, s.card = n ∧ (∀ r ∈ s, 0 < r) ∧ (∀ r ∈ s, d.eval r = 0) ∧
      (∀ r ∈ s, r < z n) := by
  classical
  obtain ⟨r, hgap, hroot⟩ := exists_roots_of_alternating hz halt
  have hzm := step_mono hz
  have hrlt : ∀ i i', i < i' → i' < n → r i < r i' := by
    intro i i' hii hi'
    have h1 : r i < z (i + 1) := (hgap i (by omega)).2
    have h2 : z (i + 1) ≤ z i' := hzm i' (le_of_lt hi') (i + 1) (by omega)
    have h3 : z i' < r i' := (hgap i' hi').1
    linarith
  have hrpos : ∀ i < n, 0 < r i := by
    intro i hi
    have h1 : z 0 ≤ z i := hzm i (le_of_lt hi) 0 (Nat.zero_le _)
    have h2 : z i < r i := (hgap i hi).1
    linarith
  have hrub : ∀ i < n, r i < z n := by
    intro i hi
    have h1 : r i < z (i + 1) := (hgap i hi).2
    have h2 : z (i + 1) ≤ z n := hzm n le_rfl (i + 1) (by omega)
    linarith
  refine ⟨(Finset.range n).image r, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi i' hi' he
    simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
    rcases lt_trichotomy i i' with h | h | h
    · exact absurd he (ne_of_lt (hrlt i i' h hi'))
    · exact h
    · exact absurd he.symm (ne_of_lt (hrlt i' i h hi))
  · intro y hy
    simp only [Finset.mem_image, Finset.mem_range] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    exact hrpos i hi
  · intro y hy
    simp only [Finset.mem_image, Finset.mem_range] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    exact hroot i hi
  · intro y hy
    simp only [Finset.mem_image, Finset.mem_range] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    exact hrub i hi

/-! ### Elementary sign arithmetic -/

theorem sub_mul_sub_neg {A B A' B' : ℝ} (h : A * A' < 0) (hB : |B| < |A|)
    (hB' : |B'| < |A'|) : (A - B) * (A' - B') < 0 := by
  rcases abs_lt.mp hB with ⟨hB1, hB2⟩
  rcases abs_lt.mp hB' with ⟨hB1', hB2'⟩
  rcases lt_trichotomy A 0 with hA | hA | hA
  · have hA' : 0 < A' := by nlinarith
    rw [abs_of_neg hA] at hB1
    rw [abs_of_pos hA'] at hB2'
    exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
  · exact absurd h (by rw [hA]; simp)
  · have hA' : A' < 0 := by nlinarith
    rw [abs_of_pos hA] at hB2
    rw [abs_of_neg hA'] at hB1'
    exact mul_neg_of_pos_of_neg (by linarith) (by linarith)

theorem eq_of_abs_add_eq {A B c : ℝ} (hc : 0 < c) (hA : |A| = c) (hB : |B| = c)
    (hsum : |A + B| = c + c) : A = B := by
  rcases abs_cases A with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases B with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
    rcases abs_cases (A + B) with ⟨h3, _⟩ | ⟨h3, _⟩ <;>
    rw [h1] at hA <;> rw [h2] at hB <;> rw [h3] at hsum <;> linarith

/-! ### Sign realization inside a coefficient hyperplane -/

/-- A finite sign pattern on `m+1` increasing positive nodes, with `m+1 ≤ n`, is realized by a
polynomial of degree at most `n` whose `j`-th coefficient vanishes. -/
theorem exists_sign_realizing_coeffKer {y μ : ℕ → ℝ} {m n j : ℕ}
    (hy : ∀ i < m, y i < y (i + 1)) (hy0 : 0 < y 0)
    (hμ : ∀ i ≤ m, μ i ≠ 0) (hmn : m + 1 ≤ n) :
    ∃ g : Polynomial ℝ, g.natDegree ≤ n ∧ g.coeff j = 0 ∧
      ∀ i ≤ m, 0 < μ i * g.eval (y i) := by
  classical
  obtain ⟨k, h, idx, hdeg, hnodes, _, hmono, hle, hidxk, _⟩ :=
    exists_sign_realizing y μ m hy hμ
  have hidxge : ∀ i ≤ k, i ≤ idx i := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ p ih =>
      intro hp
      have h1 := hmono p (by omega)
      have h2 := ih (by omega)
      omega
  have hk : k ≤ m := by
    have h1 := hidxge k le_rfl
    rw [hidxk] at h1
    exact h1
  have hhdeg : h.natDegree ≤ m := le_trans hdeg hk
  have hymono := step_mono hy
  have hypos : ∀ i ≤ m, 0 < y i := by
    intro i hi
    have := hymono i hi 0 (Nat.zero_le _)
    linarith
  set s : Finset ℝ := (Finset.range (m + 1)).image y with hs
  have hspos : ∀ r ∈ s, 0 < r := by
    intro r hr
    rw [hs] at hr
    simp only [Finset.mem_image, Finset.mem_range] at hr
    obtain ⟨i, hi, rfl⟩ := hr
    exact hypos i (by omega)
  have hscard : s.card = m + 1 := by
    rw [hs, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi i' hi' he
    simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
    rcases lt_trichotomy i i' with hc | hc | hc
    · have : y i < y i' := step_mono_lt hy hc (by omega)
      exact absurd he (ne_of_lt this)
    · exact hc
    · have : y i' < y i := step_mono_lt hy hc (by omega)
      exact absurd he.symm (ne_of_lt this)
  have hqroot : ∀ i ≤ m, (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).eval (y i) = 0 := by
    intro i hi
    refine prod_X_sub_C_eval_eq_zero ?_
    rw [hs]
    exact Finset.mem_image_of_mem y (Finset.mem_range.mpr (by omega))
  by_cases hj : j ≤ m + 1
  · have hqj : (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).coeff j ≠ 0 := by
      have hsign := prod_X_sub_C_coeff_sign s hspos j (by rw [hscard]; exact hj)
      intro hz
      rw [hz, mul_zero] at hsign
      exact absurd hsign (lt_irrefl 0)
    refine ⟨h - Polynomial.C (h.coeff j /
      (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).coeff j) *
      ∏ r ∈ s, (Polynomial.X - Polynomial.C r), ?_, ?_, ?_⟩
    · refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le (by omega) ?_)
      refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      rw [natDegree_prod_X_sub_C, hscard]
      exact hmn
    · rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, div_mul_cancel₀ _ hqj, sub_self]
    · intro i hi
      rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hqroot i hi, mul_zero,
        sub_zero]
      exact hnodes i hi
  · refine ⟨h, le_trans hhdeg (by omega), ?_, hnodes⟩
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

end
end GaloisForLFunctions.HTGeometry.WeightedMinimax
