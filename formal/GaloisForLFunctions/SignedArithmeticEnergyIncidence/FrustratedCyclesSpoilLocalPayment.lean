import GaloisForLFunctions.SignedArithmeticEnergyIncidence.CycleHolonomyDecidesBalance
import Mathlib.Algebra.Order.Chebyshev

/-!
# Frustrated cycles spoil local payment on every sign pattern

`TriangleHolonomyDecidesLocalPayment` proves the signed local–global principle on complete overlap
patterns, where triangles carry all the frustration.  A sparse incidence pattern can be frustrated
along long chordless cycles only.  Here the principle is proved for an arbitrary symmetric sign
pattern `σ`.  A form is **compatible** with `σ` when each overlap charge is a nonnegative multiple
of `σ_ij` (`SignCompatible`).

* **Frustration gap** (`frustratedCycle_poincare`): on a cycle of length `k` whose edge signs
  multiply to `−1`, `4 Σ h_i² ≤ k² Σ (h_i − e_i h_{i+1})²`.  After the gauge `s_i = Π_{j<i} e_j`
  the profile changes sign once around the cycle, so every value is half a signed sum of the
  increments.  At the local-payment threshold the frustrated cycle form is therefore strictly
  positive, and it stays nonnegative at the charge `½ + 1/k²` (`frustratedCycle_energy_nonneg`).
* **Shortest frustrated walks are cycles** (`exists_nodup_frustrated`): a closed walk of holonomy
  `−1` splits at a repeated point into two shorter closed walks, one of them frustrated.  A
  frustrated walk without repetitions has length at least `3`.
* **Cycle witness** (`cycleWitness`): unit budgets and charges `t` along a frustrated simple cycle,
  oriented by `σ`.  At `t = ½ + 1/k²` it is nonnegative (`cycleWitness_nonneg`), but no local
  allocation pays it (`cycleWitness_not_locallyPayable`): each edge needs `2t` from its two
  shares, and each point lends at most `1` to its two edges.
* **Signed local–global principle** (`localPayment_lossless_iff_isBalanced`): every nonnegative form
  compatible with `σ` is locally payable iff `σ` is balanced, iff every closed walk of `σ` is
  aligned.
-/

open Finset

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-! ### The frustration gap of a signed cycle -/

/-- The gauge `s_i = Π_{j<i} e_j` along a signed path. -/
def prefixSign (e : ℕ → ℝ) (i : ℕ) : ℝ := ∏ j ∈ range i, e j

theorem prefixSign_succ (e : ℕ → ℝ) (i : ℕ) : prefixSign e (i + 1) = prefixSign e i * e i :=
  prod_range_succ e i

theorem prefixSign_sq {e : ℕ → ℝ} (he : ∀ i, e i ^ 2 = 1) (i : ℕ) : prefixSign e i ^ 2 = 1 := by
  unfold prefixSign
  rw [← prod_pow]
  exact prod_eq_one fun j _ => he j

/-- **Frustration gap**: on a cycle of length `k` with holonomy `−1`,
`4 Σ h_i² ≤ k² Σ (h_i − e_i h_{i+1})²`. -/
theorem frustratedCycle_poincare {e : ℕ → ℝ} (he : ∀ i, e i ^ 2 = 1) {k : ℕ}
    (hhol : ∏ i ∈ range k, e i = -1) (h : ℕ → ℝ) (hk : h k = h 0) :
    4 * ∑ i ∈ range k, h i ^ 2 ≤ (k : ℝ) ^ 2 * ∑ i ∈ range k, (h i - e i * h (i + 1)) ^ 2 := by
  -- gauge away the signs: `H_i = s_i h_i` changes sign once around the cycle
  obtain ⟨H, hH, hHsq, hHk⟩ : ∃ H : ℕ → ℝ,
      (∀ i, H i - H (i + 1) = prefixSign e i * (h i - e i * h (i + 1))) ∧
      (∀ i, H i ^ 2 = h i ^ 2) ∧ H k = -H 0 := by
    refine ⟨fun i => prefixSign e i * h i, fun i => ?_, fun i => ?_, ?_⟩
    · simp only [prefixSign_succ]; ring
    · simp only [mul_pow, prefixSign_sq he, one_mul]
    · simp only [prefixSign, hhol, hk, prod_range_zero]; ring
  have hDsq : ∀ i, (H i - H (i + 1)) ^ 2 = (h i - e i * h (i + 1)) ^ 2 := fun i => by
    rw [hH, mul_pow, prefixSign_sq he, one_mul]
  have htel : ∀ m, ∑ i ∈ range m, (H i - H (i + 1)) = H 0 - H m := fun m => sum_range_sub' H m
  -- every value is half a signed sum of the increments
  have hpt : ∀ m, m ≤ k → 2 * |H m| ≤ ∑ i ∈ range k, |H i - H (i + 1)| := by
    intro m hm
    have hsplit : ∑ i ∈ range m, (H i - H (i + 1)) + ∑ i ∈ Ico m k, (H i - H (i + 1)) =
        ∑ i ∈ range k, (H i - H (i + 1)) := sum_range_add_sum_Ico _ hm
    have hIco : ∑ i ∈ Ico m k, (H i - H (i + 1)) = H m + H 0 := by
      rw [htel, htel, hHk] at hsplit; linarith
    have e2 : 2 * H m = ∑ i ∈ Ico m k, (H i - H (i + 1)) - ∑ i ∈ range m, (H i - H (i + 1)) := by
      rw [hIco, htel]; ring
    have a1 := le_abs_self (∑ i ∈ Ico m k, (H i - H (i + 1)))
    have a2 := neg_abs_le (∑ i ∈ Ico m k, (H i - H (i + 1)))
    have a3 := le_abs_self (∑ i ∈ range m, (H i - H (i + 1)))
    have a4 := neg_abs_le (∑ i ∈ range m, (H i - H (i + 1)))
    have habs : |2 * H m| ≤ |∑ i ∈ Ico m k, (H i - H (i + 1))| +
        |∑ i ∈ range m, (H i - H (i + 1))| := abs_le.2 ⟨by linarith, by linarith⟩
    have hrec : ∑ i ∈ range m, |H i - H (i + 1)| + ∑ i ∈ Ico m k, |H i - H (i + 1)| =
        ∑ i ∈ range k, |H i - H (i + 1)| := sum_range_add_sum_Ico _ hm
    rw [abs_mul, abs_two] at habs
    linarith [abs_sum_le_sum_abs (fun i => H i - H (i + 1)) (Ico m k),
      abs_sum_le_sum_abs (fun i => H i - H (i + 1)) (range m)]
  have hcs : (∑ i ∈ range k, |H i - H (i + 1)|) ^ 2 ≤
      k * ∑ i ∈ range k, (h i - e i * h (i + 1)) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := range k) (f := fun i => |H i - H (i + 1)|)
    simpa only [card_range, sq_abs, hDsq] using this
  have hpoint : ∀ m ∈ range k, 4 * h m ^ 2 ≤ k * ∑ i ∈ range k, (h i - e i * h (i + 1)) ^ 2 := by
    intro m hm
    have h2 : (2 * |H m|) ^ 2 ≤ (∑ i ∈ range k, |H i - H (i + 1)|) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (hpt m (mem_range.1 hm).le) 2
    rw [mul_pow, sq_abs, hHsq] at h2
    linarith
  calc 4 * ∑ i ∈ range k, h i ^ 2 = ∑ m ∈ range k, 4 * h m ^ 2 := by rw [mul_sum]
    _ ≤ ∑ _m ∈ range k, (k : ℝ) * ∑ i ∈ range k, (h i - e i * h (i + 1)) ^ 2 := sum_le_sum hpoint
    _ = (k : ℝ) ^ 2 * ∑ i ∈ range k, (h i - e i * h (i + 1)) ^ 2 := by
      rw [sum_const, card_range, nsmul_eq_mul]; ring

/-- **A frustrated cycle survives beyond the payment threshold**: at the charge `½ + 1/k²` the
frustrated cycle form `Σ h_i² − 2t Σ e_i h_i h_{i+1}` is still nonnegative. -/
theorem frustratedCycle_energy_nonneg {e : ℕ → ℝ} (he : ∀ i, e i ^ 2 = 1) {k : ℕ} (hk0 : 0 < k)
    (hhol : ∏ i ∈ range k, e i = -1) (h : ℕ → ℝ) (hk : h k = h 0) :
    0 ≤ ∑ i ∈ range k, h i ^ 2 -
      2 * (1 / 2 + 1 / (k : ℝ) ^ 2) * ∑ i ∈ range k, e i * h i * h (i + 1) := by
  have hP := frustratedCycle_poincare he hhol h hk
  have hshift : ∑ i ∈ range k, h (i + 1) ^ 2 = ∑ i ∈ range k, h i ^ 2 := by
    have h1 := sum_range_succ (fun i => h i ^ 2) k
    have h2 := sum_range_succ' (fun i => h i ^ 2) k
    rw [hk] at h1; linarith
  have hexp : ∑ i ∈ range k, (h i - e i * h (i + 1)) ^ 2 =
      2 * ∑ i ∈ range k, h i ^ 2 - 2 * ∑ i ∈ range k, e i * h i * h (i + 1) := by
    have hsq : ∀ i, (h i - e i * h (i + 1)) ^ 2 =
        h i ^ 2 + h (i + 1) ^ 2 - 2 * (e i * h i * h (i + 1)) := fun i => by
      rw [sub_sq, mul_pow, he i, one_mul]; ring
    simp only [hsq, sum_sub_distrib, sum_add_distrib, ← mul_sum, hshift]; ring
  have hB : ∑ i ∈ range k, e i * h i * h (i + 1) ≤ ∑ i ∈ range k, h i ^ 2 := by
    have : 0 ≤ ∑ i ∈ range k, (h i - e i * h (i + 1)) ^ 2 := sum_nonneg fun i _ => sq_nonneg _
    linarith
  have hK : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  rw [hexp] at hP
  have key : 2 * (∑ i ∈ range k, e i * h i * h (i + 1)) / (k : ℝ) ^ 2 ≤
      ∑ i ∈ range k, h i ^ 2 - ∑ i ∈ range k, e i * h i * h (i + 1) := by
    rw [div_le_iff₀ hK]; nlinarith
  have hsplit : 2 * (1 / 2 + 1 / (k : ℝ) ^ 2) * ∑ i ∈ range k, e i * h i * h (i + 1) =
      ∑ i ∈ range k, e i * h i * h (i + 1) +
        2 * (∑ i ∈ range k, e i * h i * h (i + 1)) / (k : ℝ) ^ 2 := by ring
  linarith

/-! ### Shortest frustrated walks are simple cycles -/

variable {ι : Type*}

/-- The `n`-th point of a walk from `u`; the endpoint once the walk is exhausted. -/
def walkVertex : ι → List ι → ℕ → ι
  | u, _, 0 => u
  | u, [], _ + 1 => u
  | _, y :: rest, n + 1 => walkVertex y rest n

theorem walkVertex_length (u : ι) (l : List ι) : walkVertex u l l.length = walkEnd u l := by
  induction l generalizing u with
  | nil => rfl
  | cons y rest ih => exact ih y

theorem walkVertex_succ (u : ι) (l : List ι) (i : ℕ) (hi : i < l.length) :
    walkVertex u l (i + 1) = l[i] := by
  induction l generalizing u i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons y rest ih =>
    cases i with
    | zero => simp only [walkVertex, List.getElem_cons_zero]
    | succ n =>
      rw [List.getElem_cons_succ]
      simp only [walkVertex]
      exact ih y n (by simpa using hi)

/-- The holonomy of a walk is the product of its edge signs. -/
theorem walkHolonomy_eq_prod (c : ι → ι → ℝ) (u : ι) (l : List ι) :
    walkHolonomy c u l =
      ∏ i ∈ range l.length, edgeSign c (walkVertex u l i) (walkVertex u l (i + 1)) := by
  induction l generalizing u with
  | nil => rfl
  | cons y rest ih =>
    rw [walkHolonomy, ih y, List.length_cons, prod_range_succ']
    simp only [walkVertex]
    ring

theorem isWalkFrom_vertex {c : ι → ι → ℝ} (u : ι) (l : List ι) (hl : IsWalkFrom c u l) (i : ℕ)
    (hi : i < l.length) :
    walkVertex u l i ≠ walkVertex u l (i + 1) ∧
      c (walkVertex u l i) (walkVertex u l (i + 1)) ≠ 0 := by
  induction l generalizing u i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons y rest ih =>
    obtain ⟨huy, hcuy, hrest⟩ := hl
    cases i with
    | zero => simp only [walkVertex]; exact ⟨huy, hcuy⟩
    | succ n => simp only [walkVertex]; exact ih y hrest n (by simpa using hi)

/-- A closed walk without repeated points visits distinct points before closing. -/
theorem walkVertex_injOn {u : ι} {l : List ι} (hend : walkEnd u l = u) (hnd : l.Nodup) (i j : ℕ)
    (hi : i < l.length) (hj : j < l.length) (h : walkVertex u l i = walkVertex u l j) : i = j := by
  -- the `m`-th point is `l[m - 1]`, and the start is the last entry `l[length - 1]`
  have hq : ∀ m, m < l.length → ∃ q, ∃ hq : q < l.length, walkVertex u l m = l[q] ∧
      (m = 0 → q = l.length - 1) ∧ (m ≠ 0 → q = m - 1) := by
    intro m hm
    rcases m with _ | m
    · refine ⟨l.length - 1, by omega, ?_, fun _ => rfl, fun h => absurd rfl h⟩
      rw [← walkVertex_succ u l _ (by omega), Nat.sub_add_cancel (by omega), walkVertex_length,
        hend]
      simp only [walkVertex]
    · exact ⟨m, by omega, walkVertex_succ u l m (by omega), fun h => absurd h (Nat.succ_ne_zero _),
        fun _ => rfl⟩
  obtain ⟨qi, hqi, ei, hi0, hi1⟩ := hq i hi
  obtain ⟨qj, hqj, ej, hj0, hj1⟩ := hq j hj
  rw [ei, ej, hnd.getElem_inj_iff] at h
  rcases Nat.eq_zero_or_pos i with rfl | hi' <;> rcases Nat.eq_zero_or_pos j with rfl | hj'
  · rfl
  · have := hi0 rfl; have := hj1 (by omega); omega
  · have := hi1 (by omega); have := hj0 rfl; omega
  · have := hi1 (by omega); have := hj1 (by omega); omega

theorem exists_split_of_not_nodup {l : List ι} (h : ¬ l.Nodup) :
    ∃ x s t, l = s ++ x :: t ∧ x ∈ t := by
  induction l with
  | nil => exact absurd List.nodup_nil h
  | cons a rest ih =>
    rw [List.nodup_cons, not_and_or, not_not] at h
    rcases h with h | h
    · exact ⟨a, [], rest, rfl, h⟩
    · obtain ⟨x, s, t, rfl, hx⟩ := ih h
      exact ⟨x, a :: s, t, rfl, hx⟩

theorem walkHolonomy_eq_one_or (c : ι → ι → ℝ) (u : ι) (l : List ι) :
    walkHolonomy c u l = 1 ∨ walkHolonomy c u l = -1 :=
  mul_self_eq_one_iff.1 (by rw [← sq]; exact walkHolonomy_sq c u l)

/-- **Shortest frustrated walks are simple**: a frustrated closed walk yields one without repeated
points. -/
theorem exists_nodup_frustrated {c : ι → ι → ℝ} (n : ℕ) :
    ∀ u l, l.length = n → IsWalkFrom c u l → walkEnd u l = u → walkHolonomy c u l = -1 →
      ∃ v l', IsWalkFrom c v l' ∧ walkEnd v l' = v ∧ walkHolonomy c v l' = -1 ∧ l'.Nodup := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro u l hn hl hend hhol
  by_cases hnd : l.Nodup
  · exact ⟨u, l, hl, hend, hhol, hnd⟩
  obtain ⟨x, s, t, rfl, hx⟩ := exists_split_of_not_nodup hnd
  obtain ⟨t₁, t₂, rfl⟩ := List.append_of_mem hx
  -- `l = P ++ M ++ T` with `P = s ++ [x]` from `u` to `x`, `M = t₁ ++ [x]` a loop at `x`
  have hsplit : s ++ x :: (t₁ ++ x :: t₂) = (s ++ [x]) ++ ((t₁ ++ [x]) ++ t₂) := by simp
  rw [hsplit] at hl hend hhol hn
  have hP : walkEnd u (s ++ [x]) = x := by rw [walkEnd_append]; rfl
  have hM : walkEnd x (t₁ ++ [x]) = x := by rw [walkEnd_append]; rfl
  rw [isWalkFrom_append c u (s ++ [x]), hP, isWalkFrom_append c x (t₁ ++ [x]), hM] at hl
  rw [walkEnd_append u (s ++ [x]), hP, walkEnd_append x (t₁ ++ [x]), hM] at hend
  rw [walkHolonomy_append c u (s ++ [x]), hP, walkHolonomy_append c x (t₁ ++ [x]), hM] at hhol
  obtain ⟨hlP, hlM, hlT⟩ := hl
  simp only [List.length_append, List.length_cons, List.length_nil] at hn
  have hlen₁ : ((s ++ [x]) ++ t₂).length < n := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hlen₂ : (t₁ ++ [x]).length < n := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  rcases walkHolonomy_eq_one_or c x (t₁ ++ [x]) with h1 | h1
  · -- the outer loop `P ++ T` is frustrated and shorter
    rw [h1, one_mul] at hhol
    refine ih _ hlen₁ u _ rfl ?_ ?_ ?_
    · rw [isWalkFrom_append, hP]; exact ⟨hlP, hlT⟩
    · rw [walkEnd_append, hP]; exact hend
    · rw [walkHolonomy_append, hP]; exact hhol
  · -- the inner loop `M` is frustrated and shorter
    exact ih _ hlen₂ x _ rfl hlM hM h1

/-- A frustrated closed walk has length at least `3`. -/
theorem three_le_length_of_frustrated {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c) {u : ι}
    {l : List ι} (hl : IsWalkFrom c u l) (hend : walkEnd u l = u)
    (hhol : walkHolonomy c u l = -1) : 3 ≤ l.length := by
  rcases l with _ | ⟨y, _ | ⟨z, _ | ⟨w, rest⟩⟩⟩
  · change (1 : ℝ) = -1 at hhol; norm_num at hhol
  · exact absurd hend.symm hl.1
  · change z = u at hend
    subst hend
    change edgeSign c z y * (edgeSign c y z * 1) = -1 at hhol
    rw [mul_one, edgeSign_symm hc y z, ← sq, edgeSign_sq] at hhol
    norm_num at hhol
  · simp

/-! ### The cycle witness -/

/-- A form is **compatible** with the sign pattern `σ` when each overlap charge is a nonnegative
multiple of `σ`. -/
def SignCompatible (σ c : ι → ι → ℝ) : Prop := ∀ i j, i ≠ j → ∃ r : ℝ, 0 ≤ r ∧ c i j = r * σ i j

/-- Forms compatible with a balanced pattern are balanced. -/
theorem IsBalanced.of_signCompatible {σ c : ι → ι → ℝ} (hb : IsBalanced σ)
    (h : SignCompatible σ c) : IsBalanced c := by
  obtain ⟨s, hs, hz⟩ := hb
  refine ⟨s, hs, fun i j hij => ?_⟩
  obtain ⟨r, hr, hc⟩ := h i j hij
  have hz' : s i * s j * σ i j ≤ 0 := hz i j hij
  show s i * s j * c i j ≤ 0
  rw [hc, show s i * s j * (r * σ i j) = r * (s i * s j * σ i j) by ring]
  nlinarith

section Linear

variable [Fintype ι]

/-! The energy is linear in the coupling. -/

theorem incidenceEnergy_add' (a b : ι → ι → ℝ) (f : ι → ℝ) :
    incidenceEnergy (fun x y => a x y + b x y) f = incidenceEnergy a f + incidenceEnergy b f := by
  unfold incidenceEnergy
  rw [← sum_add_distrib]
  exact sum_congr rfl fun x _ => by
    rw [← sum_add_distrib]; exact sum_congr rfl fun y _ => by ring

theorem incidenceEnergy_finsetSum {κ : Type*} (s : Finset κ) (a : κ → ι → ι → ℝ) (f : ι → ℝ) :
    incidenceEnergy (fun x y => ∑ i ∈ s, a i x y) f = ∑ i ∈ s, incidenceEnergy (a i) f := by
  unfold incidenceEnergy
  calc ∑ x, ∑ y, (∑ i ∈ s, a i x y) * f x * f y = ∑ x, ∑ i ∈ s, ∑ y, a i x y * f x * f y :=
        sum_congr rfl fun x _ => by simp only [sum_mul]; exact sum_comm
    _ = ∑ i ∈ s, ∑ x, ∑ y, a i x y * f x * f y := sum_comm

theorem incidenceEnergy_const_mul (r : ℝ) (a : ι → ι → ℝ) (f : ι → ℝ) :
    incidenceEnergy (fun x y => r * a x y) f = r * incidenceEnergy a f := by
  unfold incidenceEnergy
  rw [mul_sum]
  exact sum_congr rfl fun x _ => by rw [mul_sum]; exact sum_congr rfl fun y _ => by ring

theorem incidenceEnergy_delta [DecidableEq ι] (f : ι → ℝ) :
    incidenceEnergy (fun x y => if x = y then 1 else 0) f = ∑ x, f x ^ 2 := by
  unfold incidenceEnergy
  refine sum_congr rfl fun x _ => ?_
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, if_true, sq]

end Linear

section Witness

variable [DecidableEq ι]

/-- The indicator coupling of the ordered pair `(a, b)`. -/
def pairCoupling (a b : ι) : ι → ι → ℝ := fun x y => if x = a ∧ y = b then 1 else 0

/-- How many times the ordered pair `(x, y)` is an edge `v_i v_{i+1}` or `v_{i+1} v_i`, `i < k`. -/
def edgeCount (v : ℕ → ι) (k : ℕ) (x y : ι) : ℝ :=
  ∑ i ∈ range k, (pairCoupling (v i) (v (i + 1)) x y + pairCoupling (v (i + 1)) (v i) x y)

/-- Unit budgets and charge `t` along the edges `v_i v_{i+1}` (`i < k`), oriented by `σ`. -/
def cycleWitness (σ : ι → ι → ℝ) (v : ℕ → ι) (k : ℕ) (t : ℝ) : ι → ι → ℝ := fun x y =>
  (if x = y then 1 else 0) + ∑ i ∈ range k, t * -edgeSign σ (v i) (v (i + 1)) *
    (pairCoupling (v i) (v (i + 1)) x y + pairCoupling (v (i + 1)) (v i) x y)

theorem pairCoupling_nonneg (a b x y : ι) : 0 ≤ pairCoupling a b x y := by
  unfold pairCoupling; split_ifs <;> norm_num

theorem edgeCount_nonneg (v : ℕ → ι) (k : ℕ) (x y : ι) : 0 ≤ edgeCount v k x y :=
  sum_nonneg fun _ _ => add_nonneg (pairCoupling_nonneg _ _ _ _) (pairCoupling_nonneg _ _ _ _)

theorem cycleWitness_isSymmetric (σ : ι → ι → ℝ) (v : ℕ → ι) (k : ℕ) (t : ℝ) :
    IsSymmetricCoupling (cycleWitness σ v k t) := by
  intro x y
  unfold cycleWitness pairCoupling
  congr 1
  · simp only [eq_comm]
  · refine sum_congr rfl fun i _ => ?_
    rw [add_comm (if x = v i ∧ y = v (i + 1) then (1 : ℝ) else 0)]
    simp only [and_comm]

/-- Off the diagonal the witness is `t` times the edge multiplicity, in the direction of `σ`. -/
theorem cycleWitness_offDiag {σ : ι → ι → ℝ} (hσ : IsSymmetricCoupling σ) {v : ℕ → ι} {k : ℕ}
    (hedge : ∀ i < k, σ (v i) (v (i + 1)) ≠ 0) (t : ℝ) {x y : ι} (hxy : x ≠ y) :
    cycleWitness σ v k t x y = t * edgeCount v k x y * (σ x y / |σ x y|) := by
  unfold cycleWitness edgeCount
  rw [if_neg hxy, zero_add, mul_sum, sum_mul]
  refine sum_congr rfl fun i hi => ?_
  have hne := hedge i (mem_range.1 hi)
  unfold pairCoupling
  by_cases h1 : x = v i ∧ y = v (i + 1)
  · obtain ⟨rfl, rfl⟩ := h1
    have h2 : ¬ (v i = v (i + 1) ∧ v (i + 1) = v i) := fun h => hxy h.1
    rw [if_pos ⟨rfl, rfl⟩, if_neg h2, edgeSign, if_neg hne]
    ring
  · by_cases h2 : x = v (i + 1) ∧ y = v i
    · obtain ⟨rfl, rfl⟩ := h2
      have hne' : σ (v (i + 1)) (v i) ≠ 0 := by rw [hσ]; exact hne
      rw [if_neg h1, if_pos ⟨rfl, rfl⟩, edgeSign, if_neg hne, hσ (v i) (v (i + 1))]
      ring
    · rw [if_neg h1, if_neg h2]; ring

theorem cycleWitness_diag (σ : ι → ι → ℝ) {v : ℕ → ι} {k : ℕ} (hne : ∀ i < k, v i ≠ v (i + 1))
    (t : ℝ) (x : ι) : cycleWitness σ v k t x x = 1 := by
  unfold cycleWitness pairCoupling
  rw [if_pos rfl, add_eq_left]
  refine sum_eq_zero fun i hi => ?_
  have h := hne i (mem_range.1 hi)
  rw [if_neg (fun h' => h (h'.1.symm.trans h'.2)), if_neg (fun h' => h (h'.2.symm.trans h'.1)),
    add_zero, mul_zero]

theorem cycleWitness_signCompatible {σ : ι → ι → ℝ} (hσ : IsSymmetricCoupling σ) {v : ℕ → ι}
    {k : ℕ} (hedge : ∀ i < k, σ (v i) (v (i + 1)) ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    SignCompatible σ (cycleWitness σ v k t) := by
  intro x y hxy
  refine ⟨t * edgeCount v k x y / |σ x y|,
    div_nonneg (mul_nonneg ht (edgeCount_nonneg v k x y)) (abs_nonneg _), ?_⟩
  rw [cycleWitness_offDiag hσ hedge t hxy]
  ring

variable [Fintype ι]

theorem incidenceEnergy_pairCoupling (a b : ι) (f : ι → ℝ) :
    incidenceEnergy (pairCoupling a b) f = f a * f b := by
  unfold incidenceEnergy pairCoupling
  rw [sum_eq_single a (fun x _ hx => sum_eq_zero fun y _ => by
      rw [if_neg (fun h => hx h.1), zero_mul, zero_mul]) (fun h => absurd (mem_univ a) h),
    sum_eq_single b (fun y _ hy => by rw [if_neg (fun h => hy h.2), zero_mul, zero_mul])
      (fun h => absurd (mem_univ b) h), if_pos ⟨rfl, rfl⟩, one_mul]

theorem incidenceEnergy_cycleWitness (σ : ι → ι → ℝ) (v : ℕ → ι) (k : ℕ) (t : ℝ) (f : ι → ℝ) :
    incidenceEnergy (cycleWitness σ v k t) f = ∑ x, f x ^ 2 -
      2 * t * ∑ i ∈ range k, edgeSign σ (v i) (v (i + 1)) * f (v i) * f (v (i + 1)) := by
  unfold cycleWitness
  rw [incidenceEnergy_add', incidenceEnergy_delta, incidenceEnergy_finsetSum]
  simp only [incidenceEnergy_const_mul, incidenceEnergy_add', incidenceEnergy_pairCoupling]
  rw [mul_sum, sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  exact sum_congr rfl fun i _ => by ring

/-- **The witness is nonnegative** at the charge `½ + 1/k²`. -/
theorem cycleWitness_nonneg (σ : ι → ι → ℝ) {v : ℕ → ι} {k : ℕ} (hk0 : 0 < k)
    (hinj : ∀ i j, i < k → j < k → v i = v j → i = j) (hvk : v k = v 0)
    (hhol : ∏ i ∈ range k, edgeSign σ (v i) (v (i + 1)) = -1) (f : ι → ℝ) :
    0 ≤ incidenceEnergy (cycleWitness σ v k (1 / 2 + 1 / (k : ℝ) ^ 2)) f := by
  rw [incidenceEnergy_cycleWitness]
  have hinj' : Set.InjOn v (range k : Finset ℕ) := by
    intro i hi j hj h
    exact hinj i j (mem_range.1 hi) (mem_range.1 hj) h
  have hsub : ∑ i ∈ range k, f (v i) ^ 2 ≤ ∑ x, f x ^ 2 := by
    rw [← sum_image (f := fun x => f x ^ 2) hinj']
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ => sq_nonneg _
  have := frustratedCycle_energy_nonneg (e := fun i => edgeSign σ (v i) (v (i + 1)))
    (fun i => edgeSign_sq σ _ _) hk0 hhol (fun i => f (v i)) (congrArg f hvk)
  linarith

/-- **The witness is not locally payable** once the charge exceeds `½`: each edge needs `2t` from
its two shares, while each point lends at most its unit budget to its two edges. -/
theorem cycleWitness_not_locallyPayable {σ : ι → ι → ℝ} (hσ : IsSymmetricCoupling σ) {v : ℕ → ι}
    {k : ℕ} (hk3 : 3 ≤ k) (hinj : ∀ i j, i < k → j < k → v i = v j → i = j) (hvk : v k = v 0)
    (hedge : ∀ i < k, σ (v i) (v (i + 1)) ≠ 0) {t : ℝ} (ht : 1 / 2 < t) :
    ¬ LocallyPayable (cycleWitness σ v k t) := by
  rintro ⟨A⟩
  -- points around the cycle are distinct, reading the index `k` as `0`
  have hidx : ∀ i j, i ≤ k → j ≤ k → (if i = k then 0 else i) ≠ (if j = k then 0 else j) →
      v i ≠ v j := by
    intro i j hi hj hij hv
    have ei : v i = v (if i = k then 0 else i) := by
      split_ifs with h
      · rw [h, hvk]
      · rfl
    have ej : v j = v (if j = k then 0 else j) := by
      split_ifs with h
      · rw [h, hvk]
      · rfl
    exact hij (hinj _ _ (by split_ifs <;> omega) (by split_ifs <;> omega) (ei ▸ ej ▸ hv))
  have hne : ∀ i < k, v i ≠ v (i + 1) := fun i hi =>
    hidx i (i + 1) hi.le hi (by split_ifs <;> omega)
  -- each edge needs `2t` from the two shares it receives
  have hpay : ∀ i < k, 2 * t ≤ A.share (v i) (v (i + 1)) + A.share (v (i + 1)) (v i) := by
    intro i hi
    have hp := A.pays _ _ (hne i hi)
    rw [cycleWitness_offDiag hσ hedge t (hne i hi)] at hp
    have hcount : 1 ≤ edgeCount v k (v i) (v (i + 1)) := by
      unfold edgeCount
      refine le_trans ?_ (single_le_sum (f := fun j => pairCoupling (v j) (v (j + 1)) (v i)
        (v (i + 1)) + pairCoupling (v (j + 1)) (v j) (v i) (v (i + 1)))
        (fun j _ => add_nonneg (pairCoupling_nonneg _ _ _ _) (pairCoupling_nonneg _ _ _ _))
        (mem_range.2 hi))
      have h1 : pairCoupling (v i) (v (i + 1)) (v i) (v (i + 1)) = 1 := if_pos ⟨rfl, rfl⟩
      linarith [pairCoupling_nonneg (v (i + 1)) (v i) (v i) (v (i + 1))]
    have hunit : (σ (v i) (v (i + 1)) / |σ (v i) (v (i + 1))|) ^ 2 = 1 := by
      rw [div_pow, sq_abs, div_self (pow_ne_zero 2 (hedge i hi))]
    rw [mul_pow, hunit, mul_one] at hp
    have ht0 : 0 < t := by linarith
    have htt : t ^ 2 ≤ (t * edgeCount v k (v i) (v (i + 1))) ^ 2 :=
      pow_le_pow_left₀ ht0.le (le_mul_of_one_le_right ht0.le hcount) 2
    have h1 := A.share_nonneg (v i) (v (i + 1))
    have h2 := A.share_nonneg (v (i + 1)) (v i)
    nlinarith [sq_nonneg (A.share (v i) (v (i + 1)) - A.share (v (i + 1)) (v i))]
  -- each point lends at most `1` to two distinct partners
  have hbud : ∀ i j l, j ≠ i → l ≠ i → j ≠ l → A.share i j + A.share i l ≤ 1 := by
    intro i j l hji hli hjl
    have h := A.within_budget i
    rw [cycleWitness_diag σ hne] at h
    have hsub : ({j, l} : Finset ι) ⊆ univ.erase i := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact mem_erase.2 ⟨hji, mem_univ _⟩
      · exact mem_erase.2 ⟨hli, mem_univ _⟩
    have := sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => A.share_nonneg i x
    rw [sum_pair hjl] at this
    linarith
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  -- the predecessor of `j` around the cycle
  let g : ℕ → ℝ := fun j => A.share (v j) (v (if j = 0 then n else j - 1))
  have hlend : ∀ j < n + 1, A.share (v j) (v (j + 1)) + g j ≤ 1 := by
    intro j hj
    apply hbud
    · exact (hne j hj).symm
    · exact hidx _ _ (by split_ifs <;> omega) hj.le (by split_ifs <;> omega)
    · exact hidx _ _ (by omega) (by split_ifs <;> omega) (by split_ifs <;> omega)
  have hshift : ∑ i ∈ range (n + 1), A.share (v (i + 1)) (v i) = ∑ j ∈ range (n + 1), g j := by
    rw [sum_range_succ, sum_range_succ' g, hvk]
    congr 1
  have hsum1 : 2 * t * (n + 1 : ℕ) ≤
      ∑ i ∈ range (n + 1), (A.share (v i) (v (i + 1)) + A.share (v (i + 1)) (v i)) := by
    have := sum_le_sum fun i hi => hpay i (mem_range.1 hi)
    rwa [sum_const, card_range, nsmul_eq_mul, mul_comm] at this
  have hsum2 : ∑ j ∈ range (n + 1), (A.share (v j) (v (j + 1)) + g j) ≤ ((n + 1 : ℕ) : ℝ) := by
    have := sum_le_sum fun j hj => hlend j (mem_range.1 hj)
    rwa [sum_const, card_range, nsmul_eq_mul, mul_one] at this
  rw [sum_add_distrib, hshift, ← sum_add_distrib] at hsum1
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  nlinarith

end Witness

/-! ### The signed local–global principle on arbitrary patterns -/

/-- **An unbalanced pattern carries an unpayable nonnegative form**, supported on a shortest
frustrated cycle. -/
theorem exists_frustrated_witness [Fintype ι] [DecidableEq ι] {σ : ι → ι → ℝ}
    (hσ : IsSymmetricCoupling σ) (hnb : ¬ IsBalanced σ) :
    ∃ c : ι → ι → ℝ, IsSymmetricCoupling c ∧ SignCompatible σ c ∧
      (∀ f, 0 ≤ incidenceEnergy c f) ∧ ¬ LocallyPayable c := by
  rw [isBalanced_iff_alignedCycles hσ] at hnb
  unfold HasAlignedCycles at hnb
  push Not at hnb
  obtain ⟨u, l, hl, hend, hhol⟩ := hnb
  obtain ⟨w, l', hl', hend', hhol', hnd⟩ := exists_nodup_frustrated l.length u l rfl hl hend
    ((walkHolonomy_eq_one_or σ u l).resolve_left hhol)
  have hk3 := three_le_length_of_frustrated hσ hl' hend' hhol'
  have hvk : walkVertex w l' l'.length = walkVertex w l' 0 := by
    rw [walkVertex_length, hend']; simp only [walkVertex]
  have hedge : ∀ i < l'.length, σ (walkVertex w l' i) (walkVertex w l' (i + 1)) ≠ 0 :=
    fun i hi => (isWalkFrom_vertex w l' hl' i hi).2
  have hprod : ∏ i ∈ range l'.length,
      edgeSign σ (walkVertex w l' i) (walkVertex w l' (i + 1)) = -1 := by
    rw [← walkHolonomy_eq_prod]; exact hhol'
  have hinj : ∀ i j, i < l'.length → j < l'.length →
      walkVertex w l' i = walkVertex w l' j → i = j := walkVertex_injOn hend' hnd
  have ht : (1 : ℝ) / 2 < 1 / 2 + 1 / (l'.length : ℝ) ^ 2 := by
    have : (0 : ℝ) < (l'.length : ℝ) := by exact_mod_cast (by omega : 0 < l'.length)
    linarith [show (0 : ℝ) < 1 / (l'.length : ℝ) ^ 2 by positivity]
  exact ⟨cycleWitness σ (walkVertex w l') l'.length (1 / 2 + 1 / (l'.length : ℝ) ^ 2),
    cycleWitness_isSymmetric _ _ _ _, cycleWitness_signCompatible hσ hedge (by positivity),
    cycleWitness_nonneg σ (by omega) hinj hvk hprod,
    cycleWitness_not_locallyPayable hσ hk3 hinj hvk hedge ht⟩

/-- **Signed local–global principle on arbitrary patterns.**  Every nonnegative form compatible
with the symmetric sign pattern `σ` is locally payable iff `σ` is balanced. -/
theorem localPayment_lossless_iff_isBalanced [Fintype ι] [DecidableEq ι] {σ : ι → ι → ℝ}
    (hσ : IsSymmetricCoupling σ) :
    (∀ c : ι → ι → ℝ, IsSymmetricCoupling c → SignCompatible σ c →
      (∀ f, 0 ≤ incidenceEnergy c f) → LocallyPayable c) ↔ IsBalanced σ := by
  constructor
  · intro h
    by_contra hnb
    obtain ⟨c, hc, hcomp, hnn, hnp⟩ := exists_frustrated_witness hσ hnb
    exact hnp (h c hc hcomp hnn)
  · intro hb c hc hcomp hnn
    exact (nonneg_iff_locallyPayable_of_isBalanced hc (hb.of_signCompatible hcomp)).mp hnn

/-- **Cycle form of the principle**: local payment is lossless on the pattern `σ` iff every closed
walk of `σ` is aligned. -/
theorem localPayment_lossless_iff_alignedCycles [Fintype ι] [DecidableEq ι] {σ : ι → ι → ℝ}
    (hσ : IsSymmetricCoupling σ) :
    (∀ c : ι → ι → ℝ, IsSymmetricCoupling c → SignCompatible σ c →
      (∀ f, 0 ≤ incidenceEnergy c f) → LocallyPayable c) ↔ HasAlignedCycles σ :=
  (localPayment_lossless_iff_isBalanced hσ).trans (isBalanced_iff_alignedCycles hσ)

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
