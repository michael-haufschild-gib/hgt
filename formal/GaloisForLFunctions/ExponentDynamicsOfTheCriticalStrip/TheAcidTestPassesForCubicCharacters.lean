import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheCubicNormCharacterSumHasTheWeilBound
import GaloisForLFunctions.RHTower.HyperellipticRiemannHypothesis

/-!
# The acid test passes for cubic characters

Let `χ ≠ 1` be a cubic character of `F`, `|F| = q = 3N + 1`, and `f ∈ F[X]` squarefree and split of
degree `m` with `χ^m ≠ 1` (`3 ∤ m`). The degree sums `s_k` of `w(P) = χ(Res(P, f))` vanish from `k = m`
on, so `L*(X) = Σ_{k<m} s_k X^{m−1−k}` (`lPolyC`) is monic of degree `m − 1` with reciprocal roots `ω_i`.

* **Base change** (`powerSumW_eq_neg_rootPowerSumC`, `extChar_eq_neg_sum_pow`): Newton's identities
  for the weight and for the `ω_i` give `Σ_{x ∈ E} χ(N_{E/F} f(x)) = −Σ_i ω_i^n`, `n = [E : F]`.
* **The count at the even degrees** (`norm_rootEnumC_le`): over the extension of degree `2k`,
  `|E| = (q^k)²`, the cubic Stepanov count (`norm_sum_char_norm_le`) bounds `Σ_i (ω_i²)^k` by
  `O(q^k)`, so `|ω_i| ≤ √q`.
* **The top coefficient** (`norm_prod_lRootsC`): `|Π ω_i| = |s_{m−1}| = q^{(m−1)/2}`.
* **The line** (`riemannHypothesis_cubicCharacter`): every `ω_i` has modulus `√q`. The base-change
  lever and a count at every even degree give the Riemann hypothesis for these `L`-functions without
  Weil's theorem; torsion of order three costs nothing over `𝔽_q[T]`.
-/

open Polynomial Finset

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

open RHTower.WeilKloosterman RHTower.Hyperelliptic

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] (χ : MulChar F ℂ)

/-- The degree sums `s_k = Σ_{deg h = k} χ(Res(h, f))`. -/
noncomputable def degSumC (f : F[X]) (k : ℕ) : ℂ := degSumW (charW χ f) k

theorem degSumC_zero (f : F[X]) : degSumC χ f 0 = 1 := by
  unfold degSumC degSumW
  rw [sum_monicDeg]
  simp [monicOf, charW_one]

/-- The reversed L-polynomial `L*(X) = Σ_{k<m} s_k X^{m−1−k}`. -/
noncomputable def lPolyC (f : F[X]) : ℂ[X] :=
  ∑ k ∈ range f.natDegree, C (degSumC χ f k) * X ^ (f.natDegree - 1 - k)

theorem lPolyC_coeff (f : F[X]) {j : ℕ} (hj : j < f.natDegree) :
    (lPolyC χ f).coeff j = degSumC χ f (f.natDegree - 1 - j) := by
  unfold lPolyC
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single (f.natDegree - 1 - j)]
  · rw [if_pos (by omega)]
  · intro k hk hkj
    rw [if_neg (by have := mem_range.mp hk; omega)]
  · intro h; exact absurd (mem_range.mpr (by omega)) h

theorem lPolyC_natDegree_le (f : F[X]) : (lPolyC χ f).natDegree ≤ f.natDegree - 1 := by
  unfold lPolyC
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem lPolyC_monic (f : F[X]) (hm : 0 < f.natDegree) : (lPolyC χ f).Monic := by
  refine monic_of_natDegree_le_of_coeff_eq_one (f.natDegree - 1) (lPolyC_natDegree_le χ f) ?_
  rw [lPolyC_coeff χ f (by omega), show f.natDegree - 1 - (f.natDegree - 1) = 0 by omega,
    degSumC_zero]

theorem lPolyC_natDegree (f : F[X]) (hm : 0 < f.natDegree) :
    (lPolyC χ f).natDegree = f.natDegree - 1 := by
  refine le_antisymm (lPolyC_natDegree_le χ f) ?_
  exact le_natDegree_of_ne_zero (by
    rw [lPolyC_coeff χ f (by omega), show f.natDegree - 1 - (f.natDegree - 1) = 0 by omega,
      degSumC_zero]; exact one_ne_zero)

/-- The reciprocal roots `ω` of the L-function. -/
noncomputable def lRootsC (f : F[X]) : Multiset ℂ := (lPolyC χ f).roots

theorem card_lRootsC (f : F[X]) (hm : 0 < f.natDegree) :
    Multiset.card (lRootsC χ f) = f.natDegree - 1 := by
  rw [lRootsC, IsAlgClosed.card_roots_eq_natDegree, lPolyC_natDegree χ f hm]

variable {χ}

/-- **Vieta**: `e_k(ω) = (−1)^k s_k`. -/
theorem esymm_lRootsC (hχ : χ ≠ 1) {f : F[X]} (hsq : Squarefree f) (hsplit : f.Splits)
    (hm : 0 < f.natDegree) (k : ℕ) : (lRootsC χ f).esymm k = (-1) ^ k * degSumC χ f k := by
  rcases Nat.lt_or_ge k f.natDegree with hk | hk
  · have h := coeff_eq_esymm_roots_of_card (p := lPolyC χ f)
      (by rw [IsAlgClosed.card_roots_eq_natDegree]) (k := f.natDegree - 1 - k)
      (by rw [lPolyC_natDegree χ f hm]; omega)
    rw [lPolyC_coeff χ f (by omega), show f.natDegree - 1 - (f.natDegree - 1 - k) = k by omega,
      (lPolyC_monic χ f hm).leadingCoeff, lPolyC_natDegree χ f hm,
      show f.natDegree - 1 - (f.natDegree - 1 - k) = k by omega, one_mul] at h
    rw [h, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
    rfl
  · rw [show degSumC χ f k = 0 from degSumW_charW_eq_zero hχ hsq hsplit hm hk, mul_zero,
      Multiset.esymm, Multiset.powersetCard_eq_empty _ (by rw [card_lRootsC χ f hm]; omega)]
    simp

variable (χ)

/-- The power sums `p_n = Σ ω_i^n`. -/
noncomputable def rootPowerSumC (f : F[X]) (n : ℕ) : ℂ := ((lRootsC χ f).map (· ^ n)).sum

variable {χ}

/-- **Newton's identity for the reciprocal roots**: `n s_n = −Σ_{k<n} s_k p_{n−k}`, `n ≥ 1`. -/
theorem newton_lRootsC (hχ : χ ≠ 1) {f : F[X]} (hsq : Squarefree f) (hsplit : f.Splits)
    (hm : 0 < f.natDegree) {n : ℕ} (hn : 0 < n) :
    (n : ℂ) * degSumC χ f n = -∑ k ∈ range n, degSumC χ f k * rootPowerSumC χ f (n - k) := by
  have hN := GaloisForLFunctions.multiset_newton (rootEnum (lRootsC χ f)) n hn
  have hmap : ∀ j, (univ.val.map fun i => rootEnum (lRootsC χ f) i ^ j).sum =
      rootPowerSumC χ f j := by
    intro j
    rw [show (univ.val.map fun i => rootEnum (lRootsC χ f) i ^ j) =
        (univ.val.map (rootEnum (lRootsC χ f))).map (· ^ j) by
      rw [Multiset.map_map]; rfl, univ_map_rootEnum]
    rfl
  simp only [hmap] at hN
  rw [univ_map_rootEnum] at hN
  simp only [esymm_lRootsC hχ hsq hsplit hm] at hN
  have hanti : ∑ a ∈ {a ∈ antidiagonal n | a.1 ∈ Set.Ioo 0 n},
      (-1) ^ a.1 * ((-1) ^ a.1 * degSumC χ f a.1) * rootPowerSumC χ f a.2 =
      ∑ k ∈ range n, if 0 < k then degSumC χ f k * rootPowerSumC χ f (n - k) else 0 := by
    rw [Finset.sum_filter, Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => if a ∈ Set.Ioo 0 n then (-1) ^ a * ((-1) ^ a * degSumC χ f a) *
        rootPowerSumC χ f b else 0), Finset.sum_range_succ]
    simp only [Set.mem_Ioo, lt_irrefl, and_false, if_false, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn := mem_range.mp hk
    by_cases hk0 : 0 < k
    · rw [if_pos ⟨hk0, hkn⟩, if_pos hk0, ← mul_assoc, ← pow_add, ← two_mul, pow_mul,
        neg_one_sq, one_pow, one_mul]
    · rw [if_neg (fun h => hk0 h.1), if_neg hk0]
  rw [hanti] at hN
  have hsplit0 : ∑ k ∈ range n, degSumC χ f k * rootPowerSumC χ f (n - k) =
      rootPowerSumC χ f n +
        ∑ k ∈ range n, if 0 < k then degSumC χ f k * rootPowerSumC χ f (n - k) else 0 := by
    rw [← Nat.succ_pred_eq_of_pos hn, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [degSumC_zero, one_mul, Nat.sub_zero, lt_irrefl, if_false, add_zero,
      Nat.succ_pos, if_true]
    ring
  rw [hsplit0]
  have hsign : (-1 : ℂ) ^ (n + 1) * n * ((-1) ^ n * degSumC χ f n) = -(n * degSumC χ f n) := by
    rw [pow_succ]
    have : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    linear_combination -(n * degSumC χ f n) * this
  rw [hsign] at hN
  linear_combination hN

/-- **The power sums of the weight are minus the power sums of the reciprocal roots.** -/
theorem powerSumW_eq_neg_rootPowerSumC (hχ : χ ≠ 1) {f : F[X]} (hsq : Squarefree f)
    (hsplit : f.Splits) (hm : 0 < f.natDegree) {n : ℕ} (hn : 0 < n) :
    powerSumW (charW χ f) n = -rootPowerSumC χ f n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hc := newton_identity (charW χ f) (fun _ _ hP hQ => charW_mul χ f hP hQ) (charW_one χ f)
      (n' + 1)
    have hr := newton_lRootsC hχ hsq hsplit hm hn
    change ((n' + 1 : ℕ) : ℂ) * degSumC χ f (n' + 1) = _ at hc
    have hre : ∑ j ∈ Finset.Icc 1 (n' + 1), powerSumW (charW χ f) j * degSumW (charW χ f) (n' + 1 - j) =
        ∑ k ∈ range (n' + 1), powerSumW (charW χ f) (n' + 1 - k) * degSumC χ f k := by
      refine Finset.sum_nbij' (fun j => n' + 1 - j) (fun k => n' + 1 - k) ?_ ?_ ?_ ?_ ?_
      · intro j hj; rw [Finset.mem_Icc] at hj; rw [mem_range]; omega
      · intro k hk; rw [mem_range] at hk; rw [Finset.mem_Icc]; omega
      · intro j hj; rw [Finset.mem_Icc] at hj; omega
      · intro k hk; rw [mem_range] at hk; omega
      · intro j hj
        rw [Finset.mem_Icc] at hj
        rw [show n' + 1 - (n' + 1 - j) = j by omega]
        rfl
    rw [hre, Finset.sum_range_succ'] at hc
    rw [Finset.sum_range_succ'] at hr
    simp only [Nat.sub_zero, degSumC_zero, mul_one, one_mul] at hc hr
    have hih : ∀ k ∈ range n', powerSumW (charW χ f) (n' + 1 - (k + 1)) * degSumC χ f (k + 1) =
        -(degSumC χ f (k + 1) * rootPowerSumC χ f (n' + 1 - (k + 1))) := by
      intro k hk
      have hk' := mem_range.mp hk
      rw [ih (n' + 1 - (k + 1)) (by omega) (by omega)]
      ring
    rw [Finset.sum_congr rfl hih, Finset.sum_neg_distrib] at hc
    linear_combination hr - hc

/-- The extension sums are the power sums of the reciprocal roots. -/
theorem extChar_eq_neg_sum_pow (hχ : χ ≠ 1) {f : F[X]} (hsq : Squarefree f) (hsplit : f.Splits)
    (hm : 0 < f.natDegree) (E : Type*) [Field E] [Fintype E] [Algebra F E] :
    extChar χ (E := E) f = -((lRootsC χ f).map (· ^ Module.finrank F E)).sum := by
  rw [extChar_eq_powerSumW, powerSumW_eq_neg_rootPowerSumC hχ hsq hsplit hm Module.finrank_pos,
    rootPowerSumC]

theorem prod_lRootsC (f : F[X]) (hm : 0 < f.natDegree) :
    (lRootsC χ f).prod = (-1) ^ (f.natDegree - 1) * degSumC χ f (f.natDegree - 1) := by
  have hmon := lPolyC_monic χ f hm
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon
    (IsAlgClosed.card_roots_eq_natDegree (p := lPolyC χ f))
  have h0 := congrArg (eval 0) hprod
  rw [eval_multiset_prod, Multiset.map_map] at h0
  simp only [Function.comp_def, eval_sub, eval_X, eval_C, zero_sub] at h0
  rw [Multiset.prod_map_neg, ← coeff_zero_eq_eval_zero, lPolyC_coeff χ f hm, Nat.sub_zero] at h0
  have hc : Multiset.card (lPolyC χ f).roots = f.natDegree - 1 := card_lRootsC χ f hm
  rw [hc] at h0
  have hsq : ((-1 : ℂ) ^ (f.natDegree - 1)) * (-1) ^ (f.natDegree - 1) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  change (-1) ^ (f.natDegree - 1) * (lRootsC χ f).prod = _ at h0
  linear_combination (-1 : ℂ) ^ (f.natDegree - 1) * h0 - (lRootsC χ f).prod * hsq

theorem norm_prod_lRootsC (hχ : χ ≠ 1) {f : F[X]} (hsq : Squarefree f) (hsplit : f.Splits)
    (hm : 0 < f.natDegree) (hχm : χ ^ f.natDegree ≠ 1) :
    ‖(lRootsC χ f).prod‖ = Real.sqrt (Fintype.card F) ^ (f.natDegree - 1) := by
  rw [prod_lRootsC f hm, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, degSumC,
    norm_degSumW_charW_pred hχ hsq hsplit hm hχm]

theorem pow_mod_three_of_mod {q : ℕ} (hq : q % 3 = 1) (j : ℕ) : q ^ j % 3 = 1 := by
  rw [Nat.pow_mod, hq, one_pow]
  norm_num

/-- **The count at the even degrees bounds the reciprocal roots**: over the extension of degree
`2k` the cubic Stepanov count bounds `Σ_i (ω_i²)^k` by `O(q^k)`, so `|ω_i| ≤ √q`. -/
theorem norm_rootEnumC_le {p : ℕ} [hp : Fact p.Prime] [CharP F p] (hχ : χ ≠ 1) (hχ3 : χ ^ 3 = 1)
    {NF : ℕ} (hqF : Fintype.card F = 3 * NF + 1) {f : F[X]} (hsq : Squarefree f)
    (hsplit : f.Splits) (hm : 0 < f.natDegree) (i : Fin (lRootsC χ f).toList.length) :
    ‖rootEnum (lRootsC χ f) i‖ ≤ Real.sqrt (Fintype.card F) := by
  set m := f.natDegree
  set q := Fintype.card F
  obtain ⟨r, -, hq⟩ := FiniteField.card F p
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  have hq3 : q % 3 = 1 := by omega
  have hbound : ∀ k, 3 * m + 10 ≤ k →
      ‖∑ j ∈ univ, (rootEnum (lRootsC χ f) j ^ 2) ^ k‖ ≤ (10 * m + 11 : ℝ) * (q : ℝ) ^ k := by
    intro k hk
    haveI : NeZero (2 * k) := ⟨by omega⟩
    let E := FiniteField.Extension F p (2 * k)
    letI : Fintype E := Fintype.ofFinite E
    have hfin : Module.finrank F E = 2 * k := FiniteField.finrank_extension F p (2 * k)
    have hcardE : Fintype.card E = q ^ (2 * k) := by
      rw [Fintype.card_eq_nat_card, FiniteField.natCard_extension, Nat.card_eq_fintype_card]
    haveI : CharP E p := charP_of_injective_algebraMap (algebraMap F E).injective p
    have hcard : Fintype.card E = p ^ ((r : ℕ) * (2 * k)) := by
      rw [hcardE, show q = p ^ (r : ℕ) from hq, ← pow_mul]
    have hl : ∑ j ∈ univ, (rootEnum (lRootsC χ f) j ^ 2) ^ k =
        ((lRootsC χ f).map (· ^ (2 * k))).sum := by
      rw [Finset.sum_eq_multiset_sum]
      conv_rhs => rw [← univ_map_rootEnum (lRootsC χ f)]
      rw [Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl fun j _ => ?_
      simp [← pow_mul]
    have hsum : ∑ j ∈ univ, (rootEnum (lRootsC χ f) j ^ 2) ^ k = -extChar χ (E := E) f := by
      rw [hl, extChar_eq_neg_sum_pow hχ hsq hsplit hm E, hfin, neg_neg]
    rw [hsum, norm_neg]
    have hmod : q ^ (2 * k) % 3 = 1 := pow_mod_three_of_mod hq3 _
    have hpk : 3 * m + 10 ≤ q ^ k := by
      have : k < 2 ^ k := Nat.lt_two_pow_self
      have : 2 ^ k ≤ q ^ k := Nat.pow_le_pow_left hq2 k
      omega
    have hst := norm_sum_char_norm_le (E := E) hχ hχ3 hqF (p := p) (n := (r : ℕ) * (2 * k)) hcard
      hsq hm (N := (q ^ (2 * k) - 1) / 3) (s := q ^ k)
      (by rw [← hcard, hcardE]; omega) (by rw [← hcard, hcardE]; ring) hpk
    have hpk1 : (1 : ℝ) ≤ (q : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ q))
    have hm0 : (0 : ℝ) ≤ m := by positivity
    have hpkR : (m : ℝ) ≤ (q : ℝ) ^ k := by exact_mod_cast (by omega : m ≤ q ^ k)
    calc ‖extChar χ (E := E) f‖ ≤ 2 * (5 * m + 4) * (q ^ k : ℕ) + 3 * m := hst
      _ ≤ (10 * m + 11 : ℝ) * (q : ℝ) ^ k := by push_cast; linarith
  have h := norm_le_of_power_sums_bound univ (fun j => rootEnum (lRootsC χ f) j ^ 2)
    (C := 10 * m + 11) (ρ := q) (m0 := 3 * m + 10) (by positivity) hbound i (mem_univ i)
  rw [norm_pow] at h
  exact Real.le_sqrt_of_sq_le h

/-- **The Riemann hypothesis for the L-function of a cubic character, by counting.** For `F` with
`|F| ≡ 1 (3)`, a cubic character `χ ≠ 1` and `f` squarefree and split of degree `m` with `χ^m ≠ 1`,
the `m − 1` reciprocal roots have modulus `√q`, and for every finite extension `E` of degree `n`,
`Σ_{x ∈ E} χ(N_{E/F} f(x)) = −Σ_i ω_i^n`. -/
theorem riemannHypothesis_cubicCharacter (hχ : χ ≠ 1) (hχ3 : χ ^ 3 = 1) {NF : ℕ}
    (hqF : Fintype.card F = 3 * NF + 1) {f : F[X]} (hsq : Squarefree f) (hsplit : f.Splits)
    (hm : 0 < f.natDegree) (hχm : χ ^ f.natDegree ≠ 1) :
    Multiset.card (lRootsC χ f) = f.natDegree - 1 ∧
      (∀ ω ∈ lRootsC χ f, ‖ω‖ = Real.sqrt (Fintype.card F)) ∧
      ∀ (E : Type*) [Field E] [Fintype E] [Algebra F E],
        extChar χ (E := E) f = -((lRootsC χ f).map (· ^ Module.finrank F E)).sum := by
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  refine ⟨card_lRootsC χ f hm, ?_, fun E _ _ _ => extChar_eq_neg_sum_pow hχ hsq hsplit hm E⟩
  have hprod := norm_prod_lRootsC hχ hsq hsplit hm hχm
  have hall : ∀ i, ‖rootEnum (lRootsC χ f) i‖ = Real.sqrt (Fintype.card F) := by
    refine eq_of_prod_eq_pow (Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos))
      (fun i => norm_nonneg _) (norm_rootEnumC_le (p := ringChar F) hχ hχ3 hqF hsq hsplit hm) ?_
    rw [← norm_prod, Finset.prod_eq_multiset_prod, univ_map_rootEnum, hprod, Fintype.card_fin,
      Multiset.length_toList, card_lRootsC χ f hm]
  intro ω hω
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp (Multiset.mem_toList.mpr hω)
  rw [← hi]
  exact hall i

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
