import GaloisForLFunctions.HTGeometry.ToeplitzPerturbationCornerRatio

/-!
# Elementary products, their corner ratio, and pair perturbations

For a list `x₁ ≥ x₂ ≥ … ≥ 0` put `E(y) = ∏ (1 + x_i y)` (`elemProd`), so that `E_n = e_n(x)`.

**Corner ratio** (`cornerRatio_elemProd`).  `x_{j+1} e_j(x) ≤ (j+1) e_{j+1}(x)`.  Consequently
`e_{j−m} ≤ (j/θ)^m e_j` whenever `x_j ≥ θ > 0` (`coeff_elemProd_sub_le`), and `e_j ≥ (θ/j)^j`.

**Pair perturbation** (`coeff_mul_prod_pair_ge`).  Replace squared factors `(1 + x_p y)²` by
`(1 + x_p y)² − 4β_p y` with `β_p ≥ 0`.  If the unperturbed coefficients satisfy
`e_{j−m} ≤ ρ^m e_j`, the `j`-th coefficient of the perturbed product is at least
`e_j (2 − ∏_p (1 + 4ρβ_p))`.  Expand over the subsets `T` of perturbed pairs: the term of `T`
is `(−4)^{|T|} β^T` times a coefficient of index `j − |T|` of a sub-product, which is at most
`ρ^{|T|} e_j`.

This is the algebra of a conjugate pair `w, w̄` of complex atoms: `(1 + wy)(1 + w̄y) =
(1 + |w|y)² − 2(|w| − Re w) y`.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Nonnegative coefficients -/

theorem polyCoeff_mul_nonneg {f g : ℝ[X]} (hf : ∀ n, 0 ≤ f.coeff n) (hg : ∀ n, 0 ≤ g.coeff n)
    (n : ℕ) : 0 ≤ (f * g).coeff n := by
  rw [coeff_mul]
  exact Finset.sum_nonneg fun _ _ => mul_nonneg (hf _) (hg _)

theorem polyCoeff_prod_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℝ[X])
    (hf : ∀ i ∈ s, ∀ n, 0 ≤ (f i).coeff n) (n : ℕ) : 0 ≤ (∏ i ∈ s, f i).coeff n := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty => rw [Finset.prod_empty, coeff_one]; split_ifs <;> norm_num
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact polyCoeff_mul_nonneg (hf i (Finset.mem_insert_self i s))
      (fun m => ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)) m) n

/-- Multiplying by a nonnegative polynomial with constant term at least `1` increases every
coefficient of a nonnegative polynomial. -/
theorem polyCoeff_le_coeff_mul {f g : ℝ[X]} (hf : ∀ n, 0 ≤ f.coeff n) (hg : ∀ n, 0 ≤ g.coeff n)
    (hg0 : 1 ≤ g.coeff 0) (n : ℕ) : f.coeff n ≤ (f * g).coeff n := by
  rw [coeff_mul]
  have hmem : (n, 0) ∈ Finset.HasAntidiagonal.antidiagonal n := by simp
  calc f.coeff n ≤ f.coeff n * g.coeff 0 := le_mul_of_one_le_right (hf n) hg0
    _ ≤ ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, f.coeff x.1 * g.coeff x.2 :=
        Finset.single_le_sum (f := fun x : ℕ × ℕ => f.coeff x.1 * g.coeff x.2)
          (fun _ _ => mul_nonneg (hf _) (hg _)) hmem

/-! ## Elementary products -/

/-- `∏_{a ∈ xs} (1 + a y)`. -/
def elemProd (xs : List ℝ) : ℝ[X] := (xs.map fun a => 1 + C a * X).prod

theorem elemProd_nil : elemProd [] = 1 := by simp [elemProd]

theorem elemProd_append (xs ys : List ℝ) : elemProd (xs ++ ys) = elemProd xs * elemProd ys := by
  simp [elemProd, List.map_append, List.prod_append]

theorem elemProd_append_singleton (xs : List ℝ) (y : ℝ) :
    elemProd (xs ++ [y]) = elemProd xs * (1 + C y * X) := by
  rw [elemProd_append]
  simp [elemProd]

theorem elemProd_perm {xs ys : List ℝ} (h : xs.Perm ys) : elemProd xs = elemProd ys :=
  (h.map _).prod_eq

theorem coeff_mul_one_add_C_mul_X_succ (p : ℝ[X]) (a : ℝ) (n : ℕ) :
    (p * (1 + C a * X)).coeff (n + 1) = p.coeff (n + 1) + a * p.coeff n := by
  rw [mul_add, mul_one, coeff_add, show p * (C a * X) = C a * (X * p) by ring, coeff_C_mul,
    coeff_X_mul]

theorem coeff_mul_one_add_C_mul_X_zero (p : ℝ[X]) (a : ℝ) :
    (p * (1 + C a * X)).coeff 0 = p.coeff 0 := by
  rw [mul_add, mul_one, coeff_add, show p * (C a * X) = C a * (X * p) by ring, coeff_C_mul,
    coeff_X_mul_zero, mul_zero, add_zero]

theorem coeff_elemProd_nonneg {xs : List ℝ} (hxs : ∀ a ∈ xs, 0 ≤ a) (n : ℕ) :
    0 ≤ (elemProd xs).coeff n := by
  induction xs using List.reverseRecOn generalizing n with
  | nil => rw [elemProd_nil, coeff_one]; split_ifs <;> norm_num
  | append_singleton ys y ih =>
    have hy : 0 ≤ y := hxs y (by simp)
    have ih' := ih (fun a ha => hxs a (by simp [ha]))
    rw [elemProd_append_singleton]
    rcases n with _ | n
    · rw [coeff_mul_one_add_C_mul_X_zero]; exact ih' 0
    · rw [coeff_mul_one_add_C_mul_X_succ]; exact add_nonneg (ih' _) (mul_nonneg hy (ih' _))

theorem coeff_elemProd_zero (xs : List ℝ) : (elemProd xs).coeff 0 = 1 := by
  induction xs using List.reverseRecOn with
  | nil => simp [elemProd_nil]
  | append_singleton ys y ih => rw [elemProd_append_singleton, coeff_mul_one_add_C_mul_X_zero, ih]

theorem coeff_elemProd_eq_zero_of_lt (xs : List ℝ) {n : ℕ} (hn : xs.length < n) :
    (elemProd xs).coeff n = 0 := by
  induction xs using List.reverseRecOn generalizing n with
  | nil => rw [elemProd_nil, coeff_one]; simp at hn; simp [show n ≠ 0 by omega]
  | append_singleton ys y ih =>
    rw [elemProd_append_singleton]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    simp only [List.length_append, List.length_singleton] at hn
    rw [coeff_mul_one_add_C_mul_X_succ, ih (by omega), ih (by omega), mul_zero, add_zero]

/-- **Corner ratio of an elementary product.**  For `x₁ ≥ x₂ ≥ … ≥ 0`,
`x_{j+1} e_j(x) ≤ (j+1) e_{j+1}(x)`. -/
theorem cornerRatio_elemProd : ∀ (xs : List ℝ), xs.Pairwise (· ≥ ·) → (∀ a ∈ xs, 0 ≤ a) →
    ∀ j : ℕ, xs.getD j 0 * (elemProd xs).coeff j ≤ (j + 1) * (elemProd xs).coeff (j + 1) := by
  intro xs
  induction xs using List.reverseRecOn with
  | nil => intro _ _ j; simp [elemProd_nil, Polynomial.coeff_one]
  | append_singleton ys y ih =>
    intro hs hnn j
    have hsy := List.pairwise_append.mp hs
    have hys : ys.Pairwise (· ≥ ·) := hsy.1
    have hge : ∀ a ∈ ys, y ≤ a := fun a ha => hsy.2.2 a ha y (by simp)
    have hy : 0 ≤ y := hnn y (by simp)
    have hnn' : ∀ a ∈ ys, 0 ≤ a := fun a ha => hnn a (by simp [ha])
    have IH := ih hys hnn'
    have hE := coeff_elemProd_nonneg hnn'
    rw [elemProd_append_singleton]
    rcases Nat.lt_trichotomy j ys.length with hj | hj | hj
    · -- `j` inside `ys`
      rw [List.getD_append _ _ _ _ hj]
      rcases j with _ | i
      · rw [coeff_mul_one_add_C_mul_X_zero, coeff_mul_one_add_C_mul_X_succ]
        have := IH 0
        rw [coeff_elemProd_zero] at this ⊢
        nlinarith
      · rw [coeff_mul_one_add_C_mul_X_succ, coeff_mul_one_add_C_mul_X_succ]
        have h1 := IH (i + 1)
        have h2 := IH i
        have hanti : ys.getD (i + 1) 0 ≤ ys.getD i 0 := getD_antitone hys hnn' (by omega)
        have h3 : ys.getD (i + 1) 0 * (elemProd ys).coeff i ≤
            ((i : ℝ) + 1) * (elemProd ys).coeff (i + 1) :=
          (mul_le_mul_of_nonneg_right hanti (hE i)).trans (by exact_mod_cast h2)
        have h4 : ((i : ℝ) + 1) * (elemProd ys).coeff (i + 1) ≤
            ((i : ℝ) + 1 + 1) * (elemProd ys).coeff (i + 1) := by
          have := hE (i + 1)
          nlinarith
        push_cast at h1 ⊢
        nlinarith [h1, mul_le_mul_of_nonneg_left (h3.trans h4) hy]
    · -- `j` is the position of `y`
      subst hj
      rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero,
        coeff_mul_one_add_C_mul_X_succ,
        coeff_elemProd_eq_zero_of_lt ys (n := ys.length + 1) (by omega), zero_add]
      rcases hlen : ys.length with _ | i
      · rw [coeff_mul_one_add_C_mul_X_zero]
        push_cast
        nlinarith
      · rw [coeff_mul_one_add_C_mul_X_succ]
        have h2 := IH i
        have hyi : y ≤ ys.getD i 0 := by
          rw [List.getD_eq_getElem _ _ (by omega)]
          exact hge _ (List.getElem_mem _)
        have h3 : y * (elemProd ys).coeff i ≤ ((i : ℝ) + 1) * (elemProd ys).coeff (i + 1) :=
          (mul_le_mul_of_nonneg_right hyi (hE i)).trans (by exact_mod_cast h2)
        have h5 := hE (i + 1)
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left h3 hy, mul_nonneg hy h5]
    · -- beyond the list
      rw [List.getD_eq_default _ _ (by simp; omega), zero_mul]
      exact mul_nonneg (by positivity)
        (by rw [← elemProd_append_singleton]; exact coeff_elemProd_nonneg hnn _)

/-- **Corner ratio with multiplicity.**  If `c` entries of a nonnegative list are at least
`θ ≥ 0`, then `θ (c − i + 1) e_{i−1} ≤ i e_i` for `1 ≤ i ≤ c`.  No ordering is needed: each
`(i−1)`-subset extends by at least `c − i + 1` of the large entries, and each `i`-subset arises at
most `i` times. -/
theorem cornerRatio_elemProd_count {θ : ℝ} (hθ : 0 ≤ θ) : ∀ (xs : List ℝ), (∀ a ∈ xs, 0 ≤ a) →
    ∀ i : ℕ, 1 ≤ i → i ≤ (xs.filter fun x => decide (θ ≤ x)).length →
      θ * (((xs.filter fun x => decide (θ ≤ x)).length : ℝ) - i + 1) * (elemProd xs).coeff (i - 1) ≤
        i * (elemProd xs).coeff i := by
  intro xs
  induction xs using List.reverseRecOn with
  | nil => intro _ i hi hc; simp at hc; omega
  | append_singleton ys y ih =>
    intro hnn i hi hc
    have hy : 0 ≤ y := hnn y (by simp)
    have hnn' : ∀ a ∈ ys, 0 ≤ a := fun a ha => hnn a (by simp [ha])
    have hE := coeff_elemProd_nonneg hnn'
    have IH := ih hnn'
    set c := (ys.filter fun x => decide (θ ≤ x)).length with hcdef
    -- the inductive hypothesis at `k + 1`, written without subtraction in the index
    have IH' : ∀ k : ℕ, k + 1 ≤ c →
        θ * ((c : ℝ) - k) * (elemProd ys).coeff k ≤ ((k : ℝ) + 1) * (elemProd ys).coeff (k + 1) := by
      intro k hk
      have := IH (k + 1) (by omega) hk
      simp only [Nat.add_sub_cancel] at this
      push_cast at this
      linarith
    rw [elemProd_append_singleton]
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [coeff_mul_one_add_C_mul_X_succ]
    by_cases hyθ : θ ≤ y
    · have hcount : ((ys ++ [y]).filter fun x => decide (θ ≤ x)).length = c + 1 := by
        rw [List.filter_append, List.length_append]
        simp [hyθ, hcdef]
      rw [hcount] at hc ⊢
      push_cast
      rcases i with _ | k
      · rw [coeff_mul_one_add_C_mul_X_zero]
        have hA : θ * (c : ℝ) * (elemProd ys).coeff 0 ≤ (elemProd ys).coeff 1 := by
          rcases Nat.eq_zero_or_pos c with h0 | hpos
          · rw [h0]; simp [hE 1]
          · have := IH' 0 (by omega); simpa using this
        have hB := mul_le_mul_of_nonneg_right hyθ (hE 0)
        push_cast
        nlinarith
      · rw [coeff_mul_one_add_C_mul_X_succ]
        have hA : θ * ((c : ℝ) - k - 1) * (elemProd ys).coeff (k + 1) ≤
            ((k : ℝ) + 2) * (elemProd ys).coeff (k + 2) := by
          rcases Nat.lt_or_ge (k + 1) c with hlt | hge
          · have := IH' (k + 1) (by omega); push_cast at this; linarith
          · have hck : (c : ℝ) - k - 1 = 0 := by
              have : c = k + 1 := by omega
              rw [this]; push_cast; ring
            rw [hck, mul_zero, zero_mul]
            exact mul_nonneg (by positivity) (hE _)
        have hB := IH' k (by omega)
        have hC := mul_le_mul_of_nonneg_right hyθ (hE (k + 1))
        have hB' := mul_le_mul_of_nonneg_left hB hy
        push_cast
        nlinarith
    · have hcount : ((ys ++ [y]).filter fun x => decide (θ ≤ x)).length = c := by
        rw [List.filter_append, List.length_append]
        simp [hyθ, hcdef]
      rw [hcount] at hc ⊢
      rcases i with _ | k
      · rw [coeff_mul_one_add_C_mul_X_zero]
        have := IH' 0 (by omega)
        push_cast at this ⊢
        nlinarith [hE 0, hE 1]
      · rw [coeff_mul_one_add_C_mul_X_succ]
        have hA := IH' (k + 1) (by omega)
        have hB := IH' k (by omega)
        have hB2 : θ * ((c : ℝ) - k - 1) * (elemProd ys).coeff k ≤
            ((k : ℝ) + 2) * (elemProd ys).coeff (k + 1) := by
          have h1 : θ * ((c : ℝ) - k - 1) * (elemProd ys).coeff k ≤
              θ * ((c : ℝ) - k) * (elemProd ys).coeff k := by
            have := mul_nonneg hθ (hE k); nlinarith
          have h2 : ((k : ℝ) + 1) * (elemProd ys).coeff (k + 1) ≤
              ((k : ℝ) + 2) * (elemProd ys).coeff (k + 1) := by
            have := hE (k + 1); nlinarith
          linarith
        have hB' := mul_le_mul_of_nonneg_left hB2 hy
        push_cast at hA ⊢
        nlinarith

/-- Iterating a one-step coefficient ratio. -/
theorem coeff_sub_le_pow (P : ℝ[X]) {ρ : ℝ} (hρ : 0 ≤ ρ) (j : ℕ)
    (h : ∀ i < j, P.coeff i ≤ ρ * P.coeff (i + 1)) :
    ∀ m ≤ j, P.coeff (j - m) ≤ ρ ^ m * P.coeff j := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have h1 := h (j - (m + 1)) (by omega)
    rw [show j - (m + 1) + 1 = j - m by omega] at h1
    calc P.coeff (j - (m + 1)) ≤ ρ * P.coeff (j - m) := h1
      _ ≤ ρ * (ρ ^ m * P.coeff j) := mul_le_mul_of_nonneg_left (ih (by omega)) hρ
      _ = ρ ^ (m + 1) * P.coeff j := by ring

/-- **One-step ratio below rank `j`.**  If `x_j ≥ θ > 0` in a decreasing nonnegative list, then
`e_i ≤ (j/θ) e_{i+1}` for `i < j`. -/
theorem coeff_elemProd_pred_le {xs : List ℝ} (hs : xs.Pairwise (· ≥ ·)) (hnn : ∀ a ∈ xs, 0 ≤ a)
    {j : ℕ} {θ : ℝ} (hθ : 0 < θ) (hxj : θ ≤ xs.getD (j - 1) 0) :
    ∀ i < j, (elemProd xs).coeff i ≤ ((j : ℝ) / θ) * (elemProd xs).coeff (i + 1) := by
  intro i hi
  have h1 := cornerRatio_elemProd xs hs hnn i
  have hanti : θ ≤ xs.getD i 0 := hxj.trans (getD_antitone hs hnn (by omega))
  have hE := coeff_elemProd_nonneg hnn
  have h2 : θ * (elemProd xs).coeff i ≤ (j : ℝ) * (elemProd xs).coeff (i + 1) := by
    have hij : ((i : ℝ) + 1) ≤ j := by exact_mod_cast hi
    calc θ * (elemProd xs).coeff i ≤ xs.getD i 0 * (elemProd xs).coeff i :=
          mul_le_mul_of_nonneg_right hanti (hE i)
      _ ≤ ((i : ℝ) + 1) * (elemProd xs).coeff (i + 1) := by exact_mod_cast h1
      _ ≤ (j : ℝ) * (elemProd xs).coeff (i + 1) := mul_le_mul_of_nonneg_right hij (hE _)
  rw [div_mul_eq_mul_div, le_div_iff₀ hθ]
  linarith

/-- **Ratio bound below rank `j`.**  If `x_j ≥ θ > 0` in a decreasing nonnegative list, then
`e_{j−m} ≤ (j/θ)^m e_j` for `m ≤ j`. -/
theorem coeff_elemProd_sub_le {xs : List ℝ} (hs : xs.Pairwise (· ≥ ·)) (hnn : ∀ a ∈ xs, 0 ≤ a)
    {j : ℕ} {θ : ℝ} (hθ : 0 < θ) (hxj : θ ≤ xs.getD (j - 1) 0) :
    ∀ m ≤ j, (elemProd xs).coeff (j - m) ≤ ((j : ℝ) / θ) ^ m * (elemProd xs).coeff j :=
  coeff_sub_le_pow _ (by positivity) j (coeff_elemProd_pred_le hs hnn hθ hxj)

/-- The one-step ratio `E_i ≤ ρ E_{i+1}` (`i < j`) survives multiplication by a nonnegative
polynomial. -/
theorem coeff_mul_pred_le {E B : ℝ[X]} (hE : ∀ n, 0 ≤ E.coeff n) (hB : ∀ n, 0 ≤ B.coeff n)
    {ρ : ℝ} (hρ : 0 ≤ ρ) {j : ℕ} (h : ∀ i < j, E.coeff i ≤ ρ * E.coeff (i + 1)) :
    ∀ i < j, (E * B).coeff i ≤ ρ * (E * B).coeff (i + 1) := by
  intro i hi
  rw [coeff_mul, coeff_mul, Finset.Nat.sum_antidiagonal_succ, mul_add, Finset.mul_sum]
  have h1 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal i, E.coeff p.1 * B.coeff p.2 ≤
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal i, ρ * (E.coeff (p.1 + 1) * B.coeff p.2) := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hp1 : p.1 + p.2 = i := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have := h p.1 (by omega)
    calc E.coeff p.1 * B.coeff p.2 ≤ (ρ * E.coeff (p.1 + 1)) * B.coeff p.2 :=
          mul_le_mul_of_nonneg_right this (hB _)
      _ = ρ * (E.coeff (p.1 + 1) * B.coeff p.2) := by ring
  have h0 : 0 ≤ ρ * (E.coeff 0 * B.coeff (i + 1)) := mul_nonneg hρ (mul_nonneg (hE 0) (hB _))
  linarith

/-- A quadratic `(1 + a y)² − b y` with `b ≤ 2a` has nonnegative coefficients. -/
theorem coeff_sq_sub_nonneg {a b : ℝ} (hb : b ≤ 2 * a) (n : ℕ) :
    0 ≤ ((1 + C a * X) ^ 2 - C b * X).coeff n := by
  have e : (1 + C a * X) ^ 2 - C b * X = 1 + C (2 * a - b) * X + C (a ^ 2) * X ^ 2 := by
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    ring
  rw [e, coeff_add, coeff_add, coeff_one, coeff_C_mul_X, coeff_C_mul_X_pow]
  rcases n with _ | _ | _ | n <;> simp <;> nlinarith

/-! ## Pair perturbations -/

/-- **Pair perturbation.**  Let `A` have nonnegative coefficients and let
`P = A ∏_{p ∈ s} (1 + x_p y)²` satisfy `P_{j−m} ≤ ρ^m P_j` for `m ≤ j`.  Then, for `β_p ≥ 0`,
`[y^j] A ∏_{p ∈ s} ((1 + x_p y)² − 4β_p y) ≥ P_j (2 − ∏_{p ∈ s} (1 + 4ρβ_p))`. -/
theorem coeff_mul_prod_pair_ge {ι : Type*} [DecidableEq ι] (A : ℝ[X])
    (hA : ∀ n, 0 ≤ A.coeff n) (s : Finset ι) (x β : ι → ℝ) (hx : ∀ p ∈ s, 0 ≤ x p)
    (hβ : ∀ p ∈ s, 0 ≤ β p) (j : ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ m ≤ j, (A * ∏ p ∈ s, (1 + C (x p) * X) ^ 2).coeff (j - m) ≤
      ρ ^ m * (A * ∏ p ∈ s, (1 + C (x p) * X) ^ 2).coeff j) :
    (A * ∏ p ∈ s, (1 + C (x p) * X) ^ 2).coeff j * (2 - ∏ p ∈ s, (1 + 4 * ρ * β p)) ≤
      (A * ∏ p ∈ s, ((1 + C (x p) * X) ^ 2 - C (4 * β p) * X)).coeff j := by
  set F : ι → ℝ[X] := fun p => (1 + C (x p) * X) ^ 2 with hF
  set Pj := (A * ∏ p ∈ s, F p).coeff j with hPj
  have hFnn : ∀ p ∈ s, ∀ n, 0 ≤ (F p).coeff n := by
    intro p hp n
    have e : F p = elemProd [x p, x p] := by simp [hF, elemProd, sq]
    rw [e]
    exact coeff_elemProd_nonneg (by simp [hx p hp]) n
  have hF0 : ∀ t ⊆ s, 1 ≤ (∏ p ∈ t, F p).coeff 0 := by
    intro t _
    rw [coeff_zero_prod]
    refine le_of_eq (Finset.prod_eq_one fun p _ => ?_).symm
    simp [hF, sq]
  -- sub-products are dominated
  have hsub : ∀ t ⊆ s, ∀ i, (A * ∏ p ∈ s \ t, F p).coeff i ≤ (A * ∏ p ∈ s, F p).coeff i := by
    intro t ht i
    rw [← Finset.prod_sdiff ht, ← mul_assoc]
    exact polyCoeff_le_coeff_mul
      (polyCoeff_mul_nonneg hA (polyCoeff_prod_nonneg _ _ fun p hp => hFnn p (Finset.sdiff_subset hp)))
      (polyCoeff_prod_nonneg _ _ fun p hp => hFnn p (ht hp)) (hF0 t ht) i
  have hsubnn : ∀ t ⊆ s, ∀ i, 0 ≤ (A * ∏ p ∈ s \ t, F p).coeff i := fun t _ i =>
    polyCoeff_mul_nonneg hA (polyCoeff_prod_nonneg _ _ fun p hp => hFnn p (Finset.sdiff_subset hp)) i
  -- subset expansion
  have hexp : ∏ p ∈ s, ((1 + C (x p) * X) ^ 2 - C (4 * β p) * X) =
      ∑ t ∈ s.powerset, (∏ p ∈ t, C (-(4 * β p)) * X) * ∏ p ∈ s \ t, F p := by
    rw [← Finset.prod_add]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp only [hF, map_neg]
    ring
  have hterm : ∀ t ∈ s.powerset, (A * ((∏ p ∈ t, C (-(4 * β p)) * X) * ∏ p ∈ s \ t, F p)).coeff j =
      (∏ p ∈ t, (-(4 * β p))) *
        (if t.card ≤ j then (A * ∏ p ∈ s \ t, F p).coeff (j - t.card) else 0) := by
    intro t _
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← map_prod,
      show A * (C (∏ p ∈ t, -(4 * β p)) * X ^ t.card * ∏ p ∈ s \ t, F p) =
        C (∏ p ∈ t, -(4 * β p)) * (X ^ t.card * (A * ∏ p ∈ s \ t, F p)) by ring,
      coeff_C_mul, coeff_X_pow_mul']
  rw [hexp, Finset.mul_sum, finsetSum_coeff, Finset.sum_congr rfl hterm]
  -- termwise lower bound
  have hbound : ∀ t ∈ s.powerset,
      ((if t = ∅ then 2 else 0) - ∏ p ∈ t, (4 * ρ * β p)) * Pj ≤
        (∏ p ∈ t, (-(4 * β p))) *
          (if t.card ≤ j then (A * ∏ p ∈ s \ t, F p).coeff (j - t.card) else 0) := by
    intro t ht
    have hts : t ⊆ s := Finset.mem_powerset.mp ht
    by_cases h0 : t = ∅
    · subst h0
      simp [hPj]
      norm_num
    · rw [if_neg h0, zero_sub, neg_mul]
      have hβt : ∀ p ∈ t, 0 ≤ β p := fun p hp => hβ p (hts hp)
      have hprod : ∏ p ∈ t, (4 * ρ * β p) = ρ ^ t.card * (∏ p ∈ t, (4 * β p)) := by
        rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun p _ => by ring
      have habs : |∏ p ∈ t, (-(4 * β p))| = ∏ p ∈ t, (4 * β p) := by
        rw [Finset.abs_prod]
        exact Finset.prod_congr rfl fun p hp => by
          rw [abs_neg, abs_of_nonneg (by linarith [hβt p hp])]
      have hPnn : 0 ≤ Pj := by
        rw [hPj]
        exact polyCoeff_mul_nonneg hA (polyCoeff_prod_nonneg _ _ hFnn) j
      have h4nn : 0 ≤ ∏ p ∈ t, (4 * β p) := Finset.prod_nonneg fun p hp => by linarith [hβt p hp]
      split_ifs with hc
      · have hc1 := hsub t hts (j - t.card)
        have hc2 := hρ t.card hc
        have hcnn := hsubnn t hts (j - t.card)
        have hle : |(∏ p ∈ t, (-(4 * β p))) * (A * ∏ p ∈ s \ t, F p).coeff (j - t.card)| ≤
            (∏ p ∈ t, (4 * β p)) * (ρ ^ t.card * Pj) := by
          rw [abs_mul, habs, abs_of_nonneg hcnn]
          exact mul_le_mul_of_nonneg_left (hc1.trans hc2) h4nn
        have := neg_abs_le ((∏ p ∈ t, (-(4 * β p))) * (A * ∏ p ∈ s \ t, F p).coeff (j - t.card))
        rw [hprod]
        nlinarith
      · rw [mul_zero, hprod]
        have : 0 ≤ ρ ^ t.card * (∏ p ∈ t, (4 * β p)) * Pj :=
          mul_nonneg (mul_nonneg (pow_nonneg hρ0 _) h4nn) hPnn
        linarith
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum hbound)
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq' s.powerset ∅ (fun _ => (2 : ℝ)),
    if_pos (Finset.empty_mem_powerset s), Finset.prod_one_add]
  ring

end

end GaloisForLFunctions.HTGeometry
