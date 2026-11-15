import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheCubicStepanovCount
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheDegreeTwoCharacterOfTheCubeRootsOfTwoHasItsHodgeIndex

/-!
# The cubic curve count without Weil

Let `|E| = p^n = s² = 3N + 1` and `h` squarefree of degree `D ≥ 1` with `s ≥ 3D + 10`.

* **Stepanov's bound** (`cubic_stepanov_bound`): the choice `ℓ = s`, `K = ⌊(s² − 2D)/3⌋`,
  `J = ⌊(s + 3D + 6)/3⌋` meets the dimension condition of `cubic_stepanov_count`, so
  `3·#{x : h(x) ≠ 0, h(x)^N = ε} ≤ s² + (5D + 4)s` for every `ε`.
* **Equidistribution** (`abs_three_mul_card_sub_le`): `h(x)^N` is a cube root of unity, and the three
  classes share the `s² − #{h = 0}` nonroots; the upper bound for two of them is a lower bound for
  the third: `|3·#{h(x)^N = 1} − s²| ≤ 2(5D + 4)s + 3D`.
* **The curve** (`abs_card_cubicCurve_sub_le`): `#{(x, y) : y³ = h(x)} = #{h = 0} + 3·#{h(x)^N = 1}`,
  a nonzero cube having three cube roots; hence `|#{y³ = h(x)} − s²| ≤ 2(5D + 4)s + 4D`. This is the
  Hasse–Weil bound for the cubic curve `y³ = h(x)` over the even-degree extensions, by counting.
-/

open Polynomial Finset

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

open RHTower.Stepanov

variable {E : Type*} [Field E]

/-- The dimension condition for `ℓ = s`, `K = ⌊(s² − 2D)/3⌋`, `J = ⌊(s + 3D + 6)/3⌋`. -/
theorem cubic_dimension_condition {s D K J : ℕ} (hsD : 3 * D + 10 ≤ s) (hsq2 : 2 * D + 2 ≤ s ^ 2)
    (hK1 : s ^ 2 - 2 * D - 2 ≤ 3 * K) (hJ1 : s + 3 * D + 4 ≤ 3 * J) (hJ2 : 3 * J ≤ s + 3 * D + 6) :
    ∑ k : Fin s, (K + (k : ℕ) * D + J) < 3 * (J * K) := by
  have hsum := sum_fin_linear s K J D
  set S := ∑ k : Fin s, (K + (k : ℕ) * D + J)
  have hs1 : 1 ≤ s := by omega
  have hsumZ : (2 * S : ℤ) = 2 * s * (K + J) + D * (s * (s - 1)) := by
    have := hsum
    zify [hs1] at this
    exact this
  have hA1 : ((s : ℤ) ^ 2 - 2 * D - 2) ≤ 3 * K := by
    have e : ((s ^ 2 - 2 * D - 2 : ℕ) : ℤ) = (s : ℤ) ^ 2 - 2 * D - 2 := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
    have h' : ((s ^ 2 - 2 * D - 2 : ℕ) : ℤ) ≤ ((3 * K : ℕ) : ℤ) := by exact_mod_cast hK1
    rw [e] at h'; push_cast at h'; exact h'
  have hB1 : ((s : ℤ) + 3 * D + 4) ≤ 3 * J := by exact_mod_cast hJ1
  have hB2 : (3 * (J : ℤ)) ≤ s + 3 * D + 6 := by exact_mod_cast hJ2
  have hsD' : ((3 : ℤ) * D + 10) ≤ s := by exact_mod_cast hsD
  have hD0 : (0 : ℤ) ≤ D := by positivity
  have hA0 : (0 : ℤ) ≤ (s : ℤ) ^ 2 - 2 * D - 2 := by
    have : ((2 * D + 2 : ℕ) : ℤ) ≤ ((s ^ 2 : ℕ) : ℤ) := by exact_mod_cast hsq2
    push_cast at this; linarith
  have p1 : ((s : ℤ) ^ 2 - 2 * D - 2) * (3 * D + 4) ≤ (3 * K) * (3 * J - s) :=
    mul_le_mul hA1 (by linarith) (by positivity) (by linarith)
  have p2 : (s : ℤ) * (3 * J) ≤ s * (s + 3 * D + 6) :=
    mul_le_mul_of_nonneg_left hB2 (by positivity)
  have p3 : ((3 : ℤ) * D + 6) * (3 * D + 10) ≤ (3 * D + 6) * s :=
    mul_le_mul_of_nonneg_left hsD' (by positivity)
  have p4 : (s : ℤ) * ((3 * D + 6) * (3 * D + 10)) ≤ s * ((3 * D + 6) * s) :=
    mul_le_mul_of_nonneg_left p3 (by positivity)
  have p5 : ((3 : ℤ) * D + 10) * (9 * D ^ 2 + 45 * D + 48) ≤ s * (9 * D ^ 2 + 45 * D + 48) :=
    mul_le_mul_of_nonneg_right hsD' (by positivity)
  have : (3 * (2 * S) : ℤ) < 2 * (3 * K) * (3 * J) := by nlinarith
  have : (S : ℤ) < 3 * (J * K) := by nlinarith
  exact_mod_cast this

/-- The count bound for the same parameters. -/
theorem cubic_count_arith {s D K J N T : ℕ} (hc : s * T ≤ (K - 1) + 2 * (N * D) + s ^ 2 * (J - 1))
    (hK0 : 0 < K) (hJ1 : 1 ≤ J) (hN : 3 * N + 1 = s ^ 2) (hK2 : 3 * K ≤ s ^ 2 - 2 * D)
    (hJ2 : 3 * J ≤ s + 3 * D + 6) (hs0 : 0 < s) (hsq2 : 2 * D ≤ s ^ 2) :
    3 * T ≤ s ^ 2 + (5 * D + 4) * s := by
  have hc' : ((s * T : ℕ) : ℤ) ≤ (((K - 1) + 2 * (N * D) + s ^ 2 * (J - 1) : ℕ) : ℤ) := by
    exact_mod_cast hc
  push_cast [Nat.cast_sub hK0, Nat.cast_sub hJ1] at hc'
  have hNZ : (3 * (N : ℤ)) = (s : ℤ) ^ 2 - 1 := by
    have : ((3 * N + 1 : ℕ) : ℤ) = ((s ^ 2 : ℕ) : ℤ) := by exact_mod_cast hN
    push_cast at this; linarith
  have hK2' : (3 * (K : ℤ)) ≤ (s : ℤ) ^ 2 - 2 * D := by
    have h' : ((3 * K : ℕ) : ℤ) ≤ ((s ^ 2 - 2 * D : ℕ) : ℤ) := by exact_mod_cast hK2
    rw [Nat.cast_sub hsq2] at h'; push_cast at h'; exact h'
  have hJ2' : (3 * (J : ℤ)) ≤ s + 3 * D + 6 := by exact_mod_cast hJ2
  have q1 : (3 : ℤ) * ((s : ℤ) ^ 2 * (J - 1)) ≤ (s : ℤ) ^ 2 * (s + 3 * D + 3) := by
    have := mul_le_mul_of_nonneg_left (show (3 * ((J : ℤ) - 1)) ≤ s + 3 * D + 3 by linarith)
      (show (0 : ℤ) ≤ (s : ℤ) ^ 2 by positivity)
    linarith
  have q2 : (3 : ℤ) * (2 * ((N : ℤ) * D)) = 2 * D * ((s : ℤ) ^ 2 - 1) := by
    rw [← hNZ]; ring
  have hD0 : (0 : ℤ) ≤ D := by positivity
  have hZ : (s : ℤ) * (3 * T) ≤ s * (s ^ 2 + (5 * D + 4) * s) := by
    have e1 : (s : ℤ) * (s ^ 2 + (5 * D + 4) * s) = s ^ 2 * (s + 3 * D + 3) + 2 * D * ((s : ℤ) ^ 2 - 1) +
        ((s : ℤ) ^ 2 - 2 * D) - 3 + (4 * D + 3) := by ring
    rw [e1]
    linarith
  have hsZ : (0 : ℤ) < s := by exact_mod_cast hs0
  exact_mod_cast le_of_mul_le_mul_left hZ hsZ

/-- **Stepanov's bound for a character of order three.** -/
theorem cubic_stepanov_bound [Fintype E] [DecidableEq E] {p n : ℕ} [Fact p.Prime] [CharP E p]
    (hcard : Fintype.card E = p ^ n) {h : E[X]} (hsq : Squarefree h) (hdeg : 1 ≤ h.natDegree)
    {N s : ℕ} (hQ : p ^ n = 3 * N + 1) (hs : p ^ n = s ^ 2) (hsD : 3 * h.natDegree + 10 ≤ s)
    (ε : E) :
    3 * (univ.filter (fun x : E => h.eval x ≠ 0 ∧ h.eval x ^ N = ε)).card ≤
      s ^ 2 + (5 * h.natDegree + 4) * s := by
  set D := h.natDegree
  have hsq2 : 2 * D + 2 ≤ s ^ 2 := by nlinarith
  have hN : 3 * N + 1 = s ^ 2 := by rw [← hQ, hs]
  have hsN : s ≤ N := by nlinarith
  have h100 : 100 ≤ s ^ 2 := by nlinarith
  have hK0 : 0 < (s ^ 2 - 2 * D) / 3 := by omega
  have hc := cubic_stepanov_count hcard hsq hdeg hQ hsN hK0 (J := (s + 3 * D + 6) / 3)
    (by rw [hs]; omega)
    (cubic_dimension_condition hsD hsq2 (by omega) (by omega) (by omega)) ε
  rw [hs] at hc
  exact cubic_count_arith hc hK0 (by omega) hN (by omega) (by omega) (by omega) (by omega)

/-- A finite field with `3 ∣ |E| − 1` has a primitive cube root of unity. -/
theorem exists_cube_root_of_unity [Fintype E] (h3 : 3 ∣ Fintype.card E - 1) :
    ∃ ω : E, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcu : 3 ∣ Fintype.card Eˣ := by rw [Fintype.card_units]; exact h3
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 hcu
  refine ⟨(u : E), ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  · intro h1
    have : u = 1 := Units.ext (h1.trans Units.val_one.symm)
    rw [this, orderOf_one] at hu
    norm_num at hu

theorem eq_of_pow_three_eq_one {ω y : E} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hy : y ^ 3 = 1) :
    y = 1 ∨ y = ω ∨ y = ω ^ 2 := by
  have hsum : ω ^ 2 + ω + 1 = 0 := by
    have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hω1)
  have : (y - 1) * (y - ω) * (y - ω ^ 2) = 0 := by
    linear_combination hy + (y - y ^ 2) * hsum + (y - 1) * hω
  rcases mul_eq_zero.mp this with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

/-- **Equidistribution of the cubic classes.** `h(x)^N` is a cube root of unity at every nonroot;
the upper bounds for two classes bound the third from below. -/
theorem abs_three_mul_card_sub_le_of_cube_eq_one [Fintype E] [DecidableEq E] {p n : ℕ} [Fact p.Prime]
    [CharP E p] (hcard : Fintype.card E = p ^ n) {h : E[X]} (hsq : Squarefree h)
    (hdeg : 1 ≤ h.natDegree) {N s : ℕ} (hQ : p ^ n = 3 * N + 1) (hs : p ^ n = s ^ 2)
    (hsD : 3 * h.natDegree + 10 ≤ s) {ε : E} (hε : ε ^ 3 = 1) :
    |(3 * (univ.filter (fun x : E => h.eval x ≠ 0 ∧ h.eval x ^ N = ε)).card : ℤ) - s ^ 2| ≤
      2 * (5 * h.natDegree + 4) * s + 3 * h.natDegree := by
  have hh0 : h ≠ 0 := by rintro rfl; simp at hdeg
  set D := h.natDegree
  obtain ⟨ω, hω3, hω1⟩ := exists_cube_root_of_unity (E := E) (by rw [hcard, hQ]; omega)
  have hω0 : ω ≠ 0 := by rintro rfl; norm_num at hω3
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h2
    apply hω1
    calc ω = ω ^ 2 * ω := by rw [h2, one_mul]
      _ = ω ^ 3 := by ring
      _ = 1 := hω3
  have hωω2 : ω ≠ ω ^ 2 := by
    intro h2
    have : ω * (ω - 1) = 0 := by linear_combination -h2
    rcases mul_eq_zero.mp this with h' | h'
    · exact hω0 h'
    · exact hω1 (sub_eq_zero.mp h')
  set T : E → Finset E := fun ε => univ.filter (fun x : E => h.eval x ≠ 0 ∧ h.eval x ^ N = ε)
  have hb : ∀ ε, (3 * (T ε).card : ℤ) ≤ s ^ 2 + (5 * D + 4) * s := fun ε => by
    exact_mod_cast cubic_stepanov_bound hcard hsq hdeg hQ hs hsD ε
  have hdisj : ∀ ε ε', ε ≠ ε' → Disjoint (T ε) (T ε') := by
    intro ε ε' hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [T, Finset.mem_filter] at hx hx'
    exact hne (hx.2.2.symm.trans hx'.2.2)
  have hcube : ∀ x : E, h.eval x ≠ 0 → (h.eval x ^ N) ^ 3 = 1 := by
    intro x hx
    rw [← pow_mul, show N * 3 = Fintype.card E - 1 by rw [hcard, hQ]; omega]
    exact FiniteField.pow_card_sub_one_eq_one _ hx
  have hunion : univ.filter (fun x : E => h.eval x ≠ 0) = T 1 ∪ T ω ∪ T (ω ^ 2) := by
    ext x
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hx
      rcases eq_of_pow_three_eq_one hω3 hω1 (hcube x hx) with h' | h' | h'
      · exact Or.inl (Or.inl ⟨hx, h'⟩)
      · exact Or.inl (Or.inr ⟨hx, h'⟩)
      · exact Or.inr ⟨hx, h'⟩
    · rintro ((⟨hx, _⟩ | ⟨hx, _⟩) | ⟨hx, _⟩) <;> exact hx
  have hcardU : (univ.filter (fun x : E => h.eval x ≠ 0)).card =
      (T 1).card + (T ω).card + (T (ω ^ 2)).card := by
    rw [hunion, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint (hdisj _ _ (Ne.symm hω1))]
    exact Finset.disjoint_union_left.mpr ⟨hdisj _ _ (Ne.symm hω2), hdisj _ _ hωω2⟩
  have hroots : (univ.filter (fun x : E => h.eval x = 0)).card ≤ D := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro x hx
    rw [Finset.mem_val, Finset.mem_filter] at hx
    exact (Polynomial.mem_roots hh0).mpr hx.2
  have hcompl := Finset.card_filter_add_card_filter_not (s := (univ : Finset E))
    (fun x : E => h.eval x = 0)
  simp only [Finset.card_univ, hcard, hs] at hcompl
  rw [hcardU] at hcompl
  have hcZ : ((univ.filter (fun x : E => h.eval x = 0)).card : ℤ) + (T 1).card + (T ω).card +
      (T (ω ^ 2)).card = s ^ 2 := by
    have := hcompl
    push_cast [← add_assoc] at this ⊢
    exact_mod_cast this
  have hrZ : ((univ.filter (fun x : E => h.eval x = 0)).card : ℤ) ≤ D := by exact_mod_cast hroots
  have hr0 : (0 : ℤ) ≤ (univ.filter (fun x : E => h.eval x = 0)).card := by positivity
  have h1 := hb 1
  have h2 := hb ω
  have h3 := hb (ω ^ 2)
  have hs0 : (0 : ℤ) ≤ s := by positivity
  have hD0 : (0 : ℤ) ≤ D := by positivity
  change |(3 * (T ε).card : ℤ) - s ^ 2| ≤ _
  rw [abs_le]
  rcases eq_of_pow_three_eq_one hω3 hω1 hε with rfl | rfl | rfl <;>
    constructor <;> nlinarith

/-- The class of `1`. -/
theorem abs_three_mul_card_sub_le [Fintype E] [DecidableEq E] {p n : ℕ} [Fact p.Prime] [CharP E p]
    (hcard : Fintype.card E = p ^ n) {h : E[X]} (hsq : Squarefree h) (hdeg : 1 ≤ h.natDegree)
    {N s : ℕ} (hQ : p ^ n = 3 * N + 1) (hs : p ^ n = s ^ 2) (hsD : 3 * h.natDegree + 10 ≤ s) :
    |(3 * (univ.filter (fun x : E => h.eval x ≠ 0 ∧ h.eval x ^ N = 1)).card : ℤ) - s ^ 2| ≤
      2 * (5 * h.natDegree + 4) * s + 3 * h.natDegree :=
  abs_three_mul_card_sub_le_of_cube_eq_one hcard hsq hdeg hQ hs hsD (one_pow 3)

/-- The cubic curve `y³ = h(x)` has `#{h = 0} + 3·#{h(x)^N = 1}` points: a nonzero `a` has three cube
roots if `a^N = 1` and none otherwise, and `0` has one. -/
theorem card_cubicCurve [Fintype E] [DecidableEq E] (h : E[X]) {N : ℕ}
    (hQ : Fintype.card E = 3 * N + 1) :
    (univ.filter (fun q : E × E => q.2 ^ 3 = h.eval q.1)).card =
      (univ.filter (fun x : E => h.eval x = 0)).card +
        3 * (univ.filter (fun x : E => h.eval x ≠ 0 ∧ h.eval x ^ N = 1)).card := by
  have hfib : ∀ x : E, (univ.filter (fun y : E => y ^ 3 = h.eval x)).card =
      (if h.eval x = 0 then 1 else 0) + 3 * (if h.eval x ≠ 0 ∧ h.eval x ^ N = 1 then 1 else 0) := by
    intro x
    by_cases hx : h.eval x = 0
    · rw [hx, if_pos rfl, if_neg (fun h' => h'.1 rfl)]
      have : univ.filter (fun y : E => y ^ 3 = 0) = {0} := by
        ext y; simp [pow_eq_zero_iff]
      rw [this, Finset.card_singleton]
    · have hc := AbsoluteGeometryOfSpecZ.CubeRootsOfTwo.card_cube_roots_of_dvd
        (F := E) (by rw [hQ]; omega) hx
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
        show (Fintype.card E - 1) / 3 = N by rw [hQ]; omega] at hc
      rw [hc, if_neg hx]
      by_cases h1 : h.eval x ^ N = 1
      · rw [if_pos h1, if_pos ⟨hx, h1⟩]
      · rw [if_neg h1, if_neg (fun h' => h1 h'.2)]
  rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
  simp only [← Finset.card_filter]
  rw [Finset.sum_congr rfl fun x _ => hfib x, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.card_filter, Finset.card_filter]

/-- **The Hasse–Weil bound for `y³ = h(x)` over `𝔽_{s²}`, by counting.** -/
theorem abs_card_cubicCurve_sub_le [Fintype E] [DecidableEq E] {p n : ℕ} [Fact p.Prime] [CharP E p]
    (hcard : Fintype.card E = p ^ n) {h : E[X]} (hsq : Squarefree h) (hdeg : 1 ≤ h.natDegree)
    {N s : ℕ} (hQ : p ^ n = 3 * N + 1) (hs : p ^ n = s ^ 2) (hsD : 3 * h.natDegree + 10 ≤ s) :
    |((univ.filter (fun q : E × E => q.2 ^ 3 = h.eval q.1)).card : ℤ) - s ^ 2| ≤
      2 * (5 * h.natDegree + 4) * s + 4 * h.natDegree := by
  have hh0 : h ≠ 0 := by rintro rfl; simp at hdeg
  have he := abs_three_mul_card_sub_le hcard hsq hdeg hQ hs hsD
  rw [card_cubicCurve h (hcard.trans hQ)]
  have hroots : (univ.filter (fun x : E => h.eval x = 0)).card ≤ h.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro x hx
    rw [Finset.mem_val, Finset.mem_filter] at hx
    exact (Polynomial.mem_roots hh0).mpr hx.2
  have hrZ : ((univ.filter (fun x : E => h.eval x = 0)).card : ℤ) ≤ h.natDegree := by
    exact_mod_cast hroots
  have hr0 : (0 : ℤ) ≤ (univ.filter (fun x : E => h.eval x = 0)).card := by positivity
  push_cast
  rw [abs_le] at he ⊢
  constructor <;> linarith [he.1, he.2]

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
