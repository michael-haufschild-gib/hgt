import GaloisForLFunctions.PrimeTorusTheory.TheEnergyOfTheOrbit
import GaloisForLFunctions.PrimeTorusTheory.UniqueFactorizationPaysForNonAlignment

/-!
# The diagonal range of the prime orbit

For the integers, `k`-tuples of primes with equal product are permutations of one another, so a fibre of the product has at
most `k!` tuples (`card_fiber_le`). Distinct products are distinct integers, hence separated by `1/N` in logarithm, for
`N = y^k`. So up to width `H ≍ y^k`, the *diagonal range*, the near-diagonal energy is diagonal:

`E_k(H) ≤ k! (Σ a_r²)^k (1 + 16 N²/H²)` (`energy_le`).

Together with the count of large values this gives the **last-moment bound** (`card_largeValue_le`): a separated family of
heights at level `θ` inside a clock of width `H ≥ 4y^k` has at most `16 k Λ H k! (Σ a²)^k / (θ (θS)^{2k})` members. For
unit weights on `d` primes `≤ y = (log H)^A` this is `H^{1/A + o(1)}` at the last scale `k ≈ log H / log y`. So large
values are rare at every level, by a power of the height, and they are not excluded: the exponent `1/A` is the Rankin
exponent of `y`-smooth numbers.

Past `k = log H / log y`, integers no longer separate at the resolution `1/H`, and this is where the near-diagonal energy
stops being known (`TheEnergyOfTheOrbit` for what it must contain).
-/

open Finset

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- The integer `Π u_s` of a tuple of elements of `Q`. -/
def tupleProd {Q : Finset ℕ} {k : ℕ} (u : Fin k → Q) : ℕ := ∏ s, (u s : ℕ)

variable {Q : Finset ℕ} {k : ℕ}

theorem tupleProd_pos (hQ : ∀ r ∈ Q, r.Prime) (u : Fin k → Q) : 0 < tupleProd u :=
  Finset.prod_pos fun s _ => (hQ _ (u s).2).pos

theorem tupleProd_le {y : ℕ} (hy : ∀ r ∈ Q, r ≤ y) (u : Fin k → Q) : tupleProd u ≤ y ^ k := by
  have := Finset.prod_le_pow_card (Finset.univ : Finset (Fin k)) (fun s => ((u s : Q) : ℕ)) y
    fun s _ => hy _ (u s).2
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact this

theorem primeSystem_tupleStep (hQ : ∀ r ∈ Q, r.Prime) (a : ℕ → ℝ) (ha : ∀ r ∈ Q, 0 ≤ a r)
    (u : Fin k → Q) :
    (primeSystem Q a ha).tupleStep u = Real.log (tupleProd u) := by
  unfold PhaseSystem.tupleStep tupleProd primeSystem
  push_cast
  rw [Real.log_prod fun s _ => by exact_mod_cast (hQ _ (u s).2).ne_zero]

/-- Tuples of primes with equal product are rearrangements of one another. -/
theorem perm_of_tupleProd_eq (hQ : ∀ r ∈ Q, r.Prime) {u v : Fin k → Q}
    (h : tupleProd u = tupleProd v) :
    (List.ofFn fun s => (u s : ℕ)).Perm (List.ofFn fun s => (v s : ℕ)) := by
  have h1 := Nat.primeFactorsList_unique (n := tupleProd u)
    (l := List.ofFn fun s => (u s : ℕ))
    (by rw [List.prod_ofFn]; rfl)
    (by
      intro p hp
      obtain ⟨s, rfl⟩ := (List.mem_ofFn' _ _).mp hp
      exact hQ _ (u s).2)
  have h2 := Nat.primeFactorsList_unique (n := tupleProd u)
    (l := List.ofFn fun s => (v s : ℕ))
    (by rw [List.prod_ofFn, h]; rfl)
    (by
      intro p hp
      obtain ⟨s, rfl⟩ := (List.mem_ofFn' _ _).mp hp
      exact hQ _ (v s).2)
  exact h1.trans h2.symm

/-- Rearranged integer tuples differ by a permutation of the coordinates. -/
theorem exists_perm_of_perm {f g : Fin k → ℕ} (h : (List.ofFn f).Perm (List.ofFn g)) :
    ∃ σ : Equiv.Perm (Fin k), g = f ∘ σ := by
  have h1 := Equiv.Perm.ofFn_comp_perm (Tuple.sort f) f
  have h2 := Equiv.Perm.ofFn_comp_perm (Tuple.sort g) g
  have hp := (h1.trans h).trans h2.symm
  have hsf : (List.ofFn (f ∘ Tuple.sort f)).Pairwise (· ≤ ·) :=
    List.pairwise_ofFn.mpr fun _ _ h => Tuple.monotone_sort f h.le
  have hsg : (List.ofFn (g ∘ Tuple.sort g)).Pairwise (· ≤ ·) :=
    List.pairwise_ofFn.mpr fun _ _ h => Tuple.monotone_sort g h.le
  have heq := hp.eq_of_pairwise (fun _ _ _ _ h₁ h₂ => le_antisymm h₁ h₂) hsf hsg
  have hfun : f ∘ Tuple.sort f = g ∘ Tuple.sort g := List.ofFn_injective heq
  refine ⟨Tuple.sort f * (Tuple.sort g)⁻¹, ?_⟩
  funext s
  have := congrFun hfun ((Tuple.sort g)⁻¹ s)
  have e : (Tuple.sort g) ((Tuple.sort g)⁻¹ s) = s := by simp
  simp only [Function.comp_apply, e] at this
  simp only [Function.comp_apply, Equiv.Perm.coe_mul]
  exact this.symm

open Classical in
/-- **A fibre of the product has at most `k!` tuples.** -/
theorem card_fiber_le (hQ : ∀ r ∈ Q, r.Prime) (u : Fin k → Q) :
    ((Finset.univ.filter fun v : Fin k → Q => tupleProd v = tupleProd u).card) ≤ k.factorial := by
  have hsub : (Finset.univ.filter fun v : Fin k → Q => tupleProd v = tupleProd u) ⊆
      (Finset.univ : Finset (Equiv.Perm (Fin k))).image
        fun σ : Equiv.Perm (Fin k) => (u ∘ ⇑σ : Fin k → Q) := by
    intro v hv
    have hv' := (Finset.mem_filter.mp hv).2
    obtain ⟨σ, hσ⟩ := exists_perm_of_perm (perm_of_tupleProd_eq hQ hv'.symm)
    refine Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, ?_⟩
    funext s
    have := congrFun hσ s
    exact Subtype.ext this.symm
  have hc := (Finset.card_le_card hsub).trans Finset.card_image_le
  rwa [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hc

/-- `Σ_{j=1}^N 1/j² ≤ 2`. -/
theorem sum_Icc_inv_sq_le (N : ℕ) : ∑ j ∈ Finset.Icc 1 N, 1 / (j : ℝ) ^ 2 ≤ 2 := by
  have h : ∀ N : ℕ, ∑ j ∈ Finset.Icc 1 (N + 1), 1 / (j : ℝ) ^ 2 ≤ 2 - 1 / ((N : ℝ) + 1) := by
    intro N
    induction N with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have key : 1 / (((n + 1 + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / ((n : ℝ) + 1) - 1 / (((n + 1 : ℕ) : ℝ) + 1) := by
        push_cast
        rw [div_sub_div _ _ hn.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      push_cast at ih key ⊢
      linarith
  cases N with
  | zero => simp
  | succ n =>
    have := h n
    have h0 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- `Σ_{n ∈ A, n ≠ m} 1/(m − n)² ≤ 4` over any finite set of integers. -/
theorem sum_erase_inv_sq_le (A : Finset ℕ) (m : ℕ) :
    ∑ n ∈ A.erase m, 1 / ((m : ℝ) - n) ^ 2 ≤ 4 := by
  classical
  set N := A.sup id + m with hN
  have hle : ∀ n ∈ A, n ≤ N := fun n hn =>
    (Finset.le_sup (f := id) hn).trans (Nat.le_add_right _ _)
  have hsplit := Finset.sum_filter_add_sum_filter_not (A.erase m) (fun n => n < m)
    (fun n => 1 / ((m : ℝ) - n) ^ 2)
  rw [← hsplit]
  have h1 : ∑ n ∈ (A.erase m).filter (fun n => n < m), 1 / ((m : ℝ) - n) ^ 2 ≤ 2 := by
    refine le_trans ?_ (sum_Icc_inv_sq_le N)
    have hinj : Set.InjOn (fun n : ℕ => m - n) ((A.erase m).filter (fun n => n < m) : Finset ℕ) := by
      intro n hn n' hn' he
      have h2 := (Finset.mem_filter.mp hn).2
      have h3 := (Finset.mem_filter.mp hn').2
      simp only at he
      omega
    have hsum : ∑ n ∈ (A.erase m).filter (fun n => n < m), 1 / ((m : ℝ) - n) ^ 2 =
        ∑ j ∈ ((A.erase m).filter (fun n => n < m)).image (fun n => m - n), 1 / (j : ℝ) ^ 2 := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun n hn => ?_
      have h2 := (Finset.mem_filter.mp hn).2
      rw [Nat.cast_sub h2.le]
    rw [hsum]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
    intro j hj
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hj
    have h2 := (Finset.mem_filter.mp hn).2
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have h2 : ∑ n ∈ (A.erase m).filter (fun n => ¬ n < m), 1 / ((m : ℝ) - n) ^ 2 ≤ 2 := by
    refine le_trans ?_ (sum_Icc_inv_sq_le N)
    have hinj : Set.InjOn (fun n : ℕ => n - m) ((A.erase m).filter (fun n => ¬ n < m) : Finset ℕ) := by
      intro n hn n' hn' he
      have h2 := (Finset.mem_filter.mp hn).2
      have h3 := (Finset.mem_filter.mp hn').2
      simp only at he
      omega
    have hsum : ∑ n ∈ (A.erase m).filter (fun n => ¬ n < m), 1 / ((m : ℝ) - n) ^ 2 =
        ∑ j ∈ ((A.erase m).filter (fun n => ¬ n < m)).image (fun n => n - m), 1 / (j : ℝ) ^ 2 := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun n hn => ?_
      have h2 := not_lt.mp (Finset.mem_filter.mp hn).2
      rw [Nat.cast_sub h2, ← neg_sub, neg_sq]
    rw [hsum]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
    intro j hj
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hj
    have h3 := Finset.mem_filter.mp hn
    have h4 := not_lt.mp h3.2
    have h5 : n ≠ m := (Finset.mem_erase.mp h3.1).1
    have h6 := hle n (Finset.mem_erase.mp h3.1).2
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  linarith

/-- `sinc² x ≤ 1/x²`. -/
theorem sinc_sq_le_inv_sq {x : ℝ} (hx : x ≠ 0) : Real.sinc x ^ 2 ≤ 1 / x ^ 2 := by
  rw [Real.sinc_of_ne_zero hx, div_pow]
  exact div_le_div_of_nonneg_right (Real.sin_sq_le_one x) (by positivity)

/-- The clock kernel between two integers `≤ N`. -/
theorem sinc_sq_log_le {m n N : ℕ} (hm : 0 < m) (hn : 0 < n) (hmN : m ≤ N) (hnN : n ≤ N)
    (hne : n ≠ m) {H : ℝ} (hH : 0 < H) :
    Real.sinc (H * (Real.log m - Real.log n) / 2) ^ 2 ≤
      4 * (N : ℝ) ^ 2 / H ^ 2 * (1 / ((m : ℝ) - n) ^ 2) := by
  have hN : (0 : ℝ) < N := by
    have : 0 < N := lt_of_lt_of_le hm hmN
    exact_mod_cast this
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmn : (m : ℝ) - n ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hne.symm
  -- The gap in logarithms.
  have hgap : |(m : ℝ) - n| / N ≤ |Real.log m - Real.log n| := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hlt' : (n : ℝ) < m := by exact_mod_cast hlt
      rw [abs_of_pos (by linarith), abs_of_pos (by
        have := Real.log_lt_log hn' hlt'
        linarith)]
      have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hm' hn')
      rw [Real.log_div hm'.ne' hn'.ne', inv_div] at h1
      have h2 : ((m : ℝ) - n) / N ≤ ((m : ℝ) - n) / m :=
        div_le_div_of_nonneg_left (by linarith) hm' (by exact_mod_cast hmN)
      have h3 : ((m : ℝ) - n) / m = 1 - n / m := by
        field_simp
      linarith
    · have hgt' : (m : ℝ) < n := by exact_mod_cast hgt
      rw [abs_of_neg (by linarith), abs_of_neg (by
        have := Real.log_lt_log hm' hgt'
        linarith)]
      have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hn' hm')
      rw [Real.log_div hn'.ne' hm'.ne', inv_div] at h1
      have h2 : ((n : ℝ) - m) / N ≤ ((n : ℝ) - m) / n :=
        div_le_div_of_nonneg_left (by linarith) hn' (by exact_mod_cast hnN)
      have h3 : ((n : ℝ) - m) / n = 1 - m / n := by
        field_simp
      have e : -((m : ℝ) - n) / N = ((n : ℝ) - m) / N := by ring
      rw [e]
      linarith
  have hlogne : Real.log m - Real.log n ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hgap
    have : 0 < |(m : ℝ) - n| / N := div_pos (abs_pos.mpr hmn) hN
    linarith
  have hx : H * (Real.log m - Real.log n) / 2 ≠ 0 := by positivity
  refine (sinc_sq_le_inv_sq hx).trans ?_
  have hsq : ((m : ℝ) - n) ^ 2 / (N : ℝ) ^ 2 ≤ (Real.log m - Real.log n) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hgap 2
    rwa [div_pow, sq_abs, sq_abs] at this
  have hsqpos : 0 < ((m : ℝ) - n) ^ 2 := by positivity
  have hd : Real.log m - Real.log n ≠ 0 := hlogne
  have e1 : 1 / (H * (Real.log m - Real.log n) / 2) ^ 2 =
      4 / (H ^ 2 * (Real.log m - Real.log n) ^ 2) := by
    rw [show (H * (Real.log m - Real.log n) / 2) ^ 2 =
      H ^ 2 * (Real.log m - Real.log n) ^ 2 / 4 by ring, one_div_div]
  have e2 : 4 * (N : ℝ) ^ 2 / H ^ 2 * (1 / ((m : ℝ) - n) ^ 2) =
      4 * (N : ℝ) ^ 2 / (H ^ 2 * ((m : ℝ) - n) ^ 2) := by
    rw [mul_one_div, div_div]
  rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
  have h5 : ((m : ℝ) - n) ^ 2 ≤ (Real.log m - Real.log n) ^ 2 * (N : ℝ) ^ 2 := by
    rwa [div_le_iff₀ (by positivity)] at hsq
  have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 4 * H ^ 2)
  nlinarith

open Classical in
/-- The sum of the clock kernel over all tuples, at a fixed integer `m`. -/
theorem sum_tuple_sinc_sq_le (hQ : ∀ r ∈ Q, r.Prime) {y : ℕ} (hy : ∀ r ∈ Q, r ≤ y) (u : Fin k → Q)
    {H : ℝ} (hH : 0 < H) :
    ∑ v : Fin k → Q, Real.sinc (H * (Real.log (tupleProd u) - Real.log (tupleProd v)) / 2) ^ 2 ≤
      k.factorial * (1 + 16 * ((y : ℝ) ^ k) ^ 2 / H ^ 2) := by
  set m := tupleProd u with hm
  set N := y ^ k with hN
  have hNr : (N : ℝ) = (y : ℝ) ^ k := by rw [hN]; push_cast; rfl
  set A := (Finset.univ : Finset (Fin k → Q)).image tupleProd with hA
  have hApos : ∀ n ∈ A, 0 < n := by
    intro n hn
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hn
    exact tupleProd_pos hQ v
  have hAle : ∀ n ∈ A, n ≤ N := by
    intro n hn
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hn
    exact tupleProd_le hy v
  have hmpos : 0 < m := tupleProd_pos hQ u
  have hmle : m ≤ N := tupleProd_le hy u
  have hmA : m ∈ A := Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
  set g : ℕ → ℝ := fun n => Real.sinc (H * (Real.log m - Real.log n) / 2) ^ 2 with hg
  have hcomp := Finset.sum_comp (s := (Finset.univ : Finset (Fin k → Q))) g tupleProd
  simp only [nsmul_eq_mul] at hcomp
  rw [show (∑ v : Fin k → Q, Real.sinc (H * (Real.log m - Real.log (tupleProd v)) / 2) ^ 2) =
    ∑ v : Fin k → Q, g (tupleProd v) from rfl, hcomp]
  have hfiber : ∀ n ∈ A, (((Finset.univ.filter fun v : Fin k → Q => tupleProd v = n).card : ℕ) : ℝ) * g n ≤
      (k.factorial : ℝ) * g n := by
    intro n hn
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hn
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact_mod_cast card_fiber_le hQ v
  refine (Finset.sum_le_sum hfiber).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  rw [← Finset.add_sum_erase A g hmA]
  have hgm : g m = 1 := by
    simp [hg]
  rw [hgm]
  have hrest : ∑ n ∈ A.erase m, g n ≤ 16 * (N : ℝ) ^ 2 / H ^ 2 := by
    have hterm : ∀ n ∈ A.erase m, g n ≤ 4 * (N : ℝ) ^ 2 / H ^ 2 * (1 / ((m : ℝ) - n) ^ 2) := by
      intro n hn
      have hn' := Finset.mem_erase.mp hn
      exact sinc_sq_log_le hmpos (hApos n hn'.2) hmle (hAle n hn'.2) hn'.1 hH
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have h4 := sum_erase_inv_sq_le A m
    have h0 : 0 ≤ 4 * (N : ℝ) ^ 2 / H ^ 2 := by positivity
    calc
      4 * (N : ℝ) ^ 2 / H ^ 2 * ∑ n ∈ A.erase m, 1 / ((m : ℝ) - n) ^ 2
          ≤ 4 * (N : ℝ) ^ 2 / H ^ 2 * 4 := mul_le_mul_of_nonneg_left h4 h0
      _ = 16 * (N : ℝ) ^ 2 / H ^ 2 := by ring
  rw [← hNr]
  linarith

/-- The total square weight of the `k`-tuples. -/
theorem sum_tupleWeight_sq [DecidableEq Q] (a : ℕ → ℝ) (ha : ∀ r ∈ Q, 0 ≤ a r) :
    ∑ u : Fin k → Q, (primeSystem Q a ha).tupleWeight u ^ 2 = (∑ r ∈ Q, a r ^ 2) ^ k := by
  have h := Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset Q))
    (fun _ r => a (r : ℕ) ^ 2)
  rw [Fintype.piFinset_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  have e : ∑ r : Q, a (r : ℕ) ^ 2 = ∑ r ∈ Q, a r ^ 2 := Finset.sum_coe_sort Q fun r => a r ^ 2
  rw [e] at h
  rw [h]
  refine Finset.sum_congr rfl fun u _ => ?_
  unfold PhaseSystem.tupleWeight primeSystem
  rw [Finset.prod_pow]

/-- **The diagonal range.** `E_k(H) ≤ k! (Σ a_r²)^k (1 + 16 y^{2k}/H²)`. -/
theorem energy_le [DecidableEq Q] (hQ : ∀ r ∈ Q, r.Prime) {y : ℕ} (hy : ∀ r ∈ Q, r ≤ y)
    (a : ℕ → ℝ) (ha : ∀ r ∈ Q, 0 ≤ a r) (k : ℕ) {H : ℝ} (hH : 0 < H) :
    (primeSystem Q a ha).energy k H ≤
      k.factorial * (∑ r ∈ Q, a r ^ 2) ^ k * (1 + 16 * ((y : ℝ) ^ k) ^ 2 / H ^ 2) := by
  set S := primeSystem Q a ha with hS
  have hstep : ∀ u : Fin k → Q, S.tupleStep u = Real.log (tupleProd u) :=
    primeSystem_tupleStep hQ a ha
  have hsym : ∀ u v : Fin k → Q, S.tupleWeight u * S.tupleWeight v *
      Real.sinc (H * (S.tupleStep u - S.tupleStep v) / 2) ^ 2 ≤
      (S.tupleWeight u ^ 2 * Real.sinc (H * (S.tupleStep u - S.tupleStep v) / 2) ^ 2 +
        S.tupleWeight v ^ 2 * Real.sinc (H * (S.tupleStep v - S.tupleStep u) / 2) ^ 2) / 2 := by
    intro u v
    have e : Real.sinc (H * (S.tupleStep v - S.tupleStep u) / 2) ^ 2 =
        Real.sinc (H * (S.tupleStep u - S.tupleStep v) / 2) ^ 2 := by
      have : H * (S.tupleStep v - S.tupleStep u) / 2 = -(H * (S.tupleStep u - S.tupleStep v) / 2) := by
        ring
      rw [this, Real.sinc_neg]
    rw [e]
    nlinarith [sq_nonneg (S.tupleWeight u - S.tupleWeight v),
      mul_nonneg (sq_nonneg (S.tupleWeight u - S.tupleWeight v))
        (sq_nonneg (Real.sinc (H * (S.tupleStep u - S.tupleStep v) / 2)))]
  unfold PhaseSystem.energy
  have hle1 := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) =>
    Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) => hsym u v
  refine hle1.trans ?_
  -- The two halves are equal by symmetry.
  have hhalf : ∑ u : Fin k → Q, ∑ v : Fin k → Q,
      (S.tupleWeight u ^ 2 * Real.sinc (H * (S.tupleStep u - S.tupleStep v) / 2) ^ 2 +
        S.tupleWeight v ^ 2 * Real.sinc (H * (S.tupleStep v - S.tupleStep u) / 2) ^ 2) / 2 =
      ∑ u : Fin k → Q, S.tupleWeight u ^ 2 * ∑ v : Fin k → Q,
        Real.sinc (H * (S.tupleStep u - S.tupleStep v) / 2) ^ 2 := by
    simp only [add_div, Finset.sum_add_distrib]
    have hswap : ∑ u : Fin k → Q, ∑ v : Fin k → Q,
        S.tupleWeight v ^ 2 * Real.sinc (H * (S.tupleStep v - S.tupleStep u) / 2) ^ 2 / 2 =
        ∑ u : Fin k → Q, ∑ v : Fin k → Q,
          S.tupleWeight u ^ 2 * Real.sinc (H * (S.tupleStep u - S.tupleStep v) / 2) ^ 2 / 2 :=
      Finset.sum_comm
    rw [hswap, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [hhalf]
  have hB : (0 : ℝ) ≤ k.factorial * (1 + 16 * ((y : ℝ) ^ k) ^ 2 / H ^ 2) := by positivity
  calc
    ∑ u : Fin k → Q, S.tupleWeight u ^ 2 * ∑ v : Fin k → Q,
        Real.sinc (H * (S.tupleStep u - S.tupleStep v) / 2) ^ 2
        ≤ ∑ u : Fin k → Q, S.tupleWeight u ^ 2 * (k.factorial * (1 + 16 * ((y : ℝ) ^ k) ^ 2 / H ^ 2)) := by
          refine Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          simp_rw [hstep]
          exact sum_tuple_sinc_sq_le hQ hy u hH
    _ = k.factorial * (∑ r ∈ Q, a r ^ 2) ^ k * (1 + 16 * ((y : ℝ) ^ k) ^ 2 / H ^ 2) := by
          rw [← Finset.sum_mul, sum_tupleWeight_sq a ha]
          ring

/-- **The last-moment bound.** Inside a clock of width `H ≥ 4y^k`, a separated family of heights at level `θ` is rare. -/
theorem card_largeValue_le [DecidableEq Q] (hQ : ∀ r ∈ Q, r.Prime) {y : ℕ} (hy : ∀ r ∈ Q, r ≤ y)
    (a : ℕ → ℝ) (ha : ∀ r ∈ Q, 0 ≤ a r) {k : ℕ} (hk : 1 ≤ k) {Λ θ T₀ H : ℝ} (hΛ0 : 0 < Λ)
    (hΛ : ∀ r ∈ Q, Real.log r ≤ Λ) (hθ0 : 0 < θ) (hH : 4 * (y : ℝ) ^ k ≤ H) (hH0 : 0 < H)
    (R : Finset ℝ) (hmid : ∀ τ ∈ R, |τ - T₀| + θ / (4 * k * Λ) ≤ H / 2)
    (hR : ∀ τ ∈ R, τ ∈ (primeSystem Q a ha).largeValue θ)
    (hsep : ∀ τ ∈ R, ∀ σ ∈ R, τ ≠ σ → 2 * (θ / (4 * k * Λ)) ≤ |τ - σ|) :
    (R.card : ℝ) * (θ / (4 * k * Λ)) * (θ * ∑ r ∈ Q, a r) ^ (2 * k) / (2 * H) ≤
      2 * (k.factorial * (∑ r ∈ Q, a r ^ 2) ^ k) := by
  set S := primeSystem Q a ha with hS
  have hstep : ∀ i, |S.step i| ≤ Λ := by
    intro r
    have hr := (hQ _ r.2).one_lt
    have h0 : 0 ≤ Real.log ((r : ℕ) : ℝ) := Real.log_natCast_nonneg _
    rw [show S.step r = Real.log ((r : ℕ) : ℝ) from rfl, abs_of_nonneg h0]
    exact hΛ _ r.2
  have h1 := PhaseSystem.card_mul_le_clockedMoment (S := S) hk hΛ0 hstep hθ0 hH0 R hmid hR hsep
  rw [PhaseSystem.clockedMoment_eq _ _ _ hH0, primeSystem_size] at h1
  have h2 := (le_abs_self _).trans (S.abs_shiftedEnergy_le_energy k T₀ H)
  have h3 := energy_le hQ hy a ha k hH0
  have hy0 : (0 : ℝ) ≤ (y : ℝ) ^ k := by positivity
  have h4 : 16 * ((y : ℝ) ^ k) ^ 2 / H ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have h5 : (0 : ℝ) ≤ k.factorial * (∑ r ∈ Q, a r ^ 2) ^ k :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) _)
  nlinarith

end

end GaloisForLFunctions.PrimeTorusTheory
