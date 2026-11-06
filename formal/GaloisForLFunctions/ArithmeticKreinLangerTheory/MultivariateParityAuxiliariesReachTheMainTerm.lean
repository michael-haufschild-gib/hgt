import GaloisForLFunctions.ArithmeticKreinLangerTheory.TheUnivariateIntegerChebyshevCeiling
import GaloisForLFunctions.ArithmeticKreinLangerTheory.FinitePrimeHeckeAuxiliaryObstructions
import GaloisForLFunctions.BezoutValuationIncidence.CoprimeMertensSawtoothCancellation
import GaloisForLFunctions.RHTower.Sieve.MoebiusLogarithmicNormalization
import GaloisForLFunctions.ArithmeticKreinLangerTheory.TheMobiusNormalizationHasARate

/-!
# Multivariate parity-selective integer auxiliaries reach the PNT main term

This module proves unconditionally that multivariate, parity-selective integer Hecke–factorial
auxiliaries (outside the Hecke algebra of a single prime) reach normalized vanishing-order slope
`< 1 + ε` for every `ε > 0`, yielding the prime number theorem upper bounds
`ψ(x) ≤ (1 + ε) x + C (log x)²` and `θ(x) ≤ (1 + ε) x + C (log x)²` by vanishing-order arguments
alone, and strictly beating every restricted ceiling:

* the univariate integer-Chebyshev ceiling on `[0, 1]` (`sup_{x ∈ [0,1]} |P(x)| > exp(-(87/100) n)`);
* the single-prime Hecke ceiling (`≥ (p₀ log p₀) / (p₀ - 1) ≥ 2 log 2`);
* every finite-prime alphabet ceiling (`> 1 + 1 / ((∏_{p ∈ S} p + 1)(∏_{p ∈ S} p + 2)) > 1`);
* the parity-blind (`c(k) ≤ 0` for `k ≥ 2`) multinomial ceiling (`> 31 / 30`).

## Proof mechanism

1. **Finite Farkas / Fourier–Motzkin duality (`finset_farkas`).** Over any finite divisor index set
   `J = (Nat.divisors L').erase 1`, either there exist real weights `x : ℕ → ℝ` satisfying the
   slope cap `(1 + ε₀)(1 - 1/B)` together with residue dominance `≥ 1` on `[1, B)` and `≥ 0` on
   `[B, L')`, or there exists a nonnegative residue measure `u` on `[1, L')` satisfying the exact
   harmonic identity `∑_{1 ≤ r < L'} u(r) (r % k) = log k` for every `k ∣ L'` while putting mass
   `> (1 + ε₀)(1 - 1/B)` on `[1, B)`.
2. **Upward rational rounding and denominator clearing (`exists_stencil_of_real_lp`).** Because the
   residue kernels `r % k` are nonnegative, rounding each `x_k` strictly upward into `ℚ` preserves
   all lower bounds `[1, B)` and `[B, L')` simultaneously while perturbing the logarithmic slope by
   at most `ε₀ (1 - 1/B)`. Clearing denominators produces an exact balanced integer stencil
   `c = (∑_{k ∈ J} z_k) e_1 - ∑_{k ∈ J} k z_k e_k` whose step weight is `L'`-periodic and globally
   nonnegative.
3. **Balanced Möbius harmonic kernel (`exists_real_lp_solution`).** At dyadic cutoffs `T = 2^ℓ`,
   `B = T + 1`, and `L' = 2^M (T + 1)!`, pairing any dual residue measure `u` against
   `F_T(r) = ∑_{1 ≤ b ≤ T} (-μ(b)/b) (r % b) + m(T) (r % (T + 1))` collapses identically to `1` on
   the main window `1 ≤ r ≤ T` by Möbius inversion, evaluates globally to
   `-∑_{b ≤ T} μ(b) (log b)/b + m(T) log(T + 1) → 1` (`tendsto_moebiusLogHarmonicPartial_one`), and
   has negligible tail mass across `[T + 1, 2^{4ℓ}(T + 1))`, `[2^{4ℓ}(T + 1), 2^{M-1}(T + 1))`,
   and `[2^{M-1}(T + 1), L')` by coprime Mertens sawtooth cancellation
   (`exists_abs_sum_coprime_moebius_fract_le`, `exists_abs_coprimeMoebiusHarmonicSum_le_four`) and
   divisor-level Chebyshev Markov bounds.
-/

open Finset Filter Topology
open scoped Polynomial

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

/-! ### Finite Fourier–Motzkin / Farkas alternative -/

/-- **Finite Farkas alternative over `ℝ`.** For finite index sets `I` and `J`, either the linear
system `∑_{k ∈ J} A i k * x k ≤ b i` (`i ∈ I`) admits a primal solution `x : α → ℝ`, or there exist
nonnegative dual weights `w : ι → ℝ` annihilating every column `k ∈ J` with `∑_{i ∈ I} w i * b i < 0`. -/
theorem finset_farkas {ι α : Type*} (I : Finset ι) (J : Finset α)
    (A : ι → α → ℝ) (b : ι → ℝ) :
    (∃ x : α → ℝ, ∀ i ∈ I, ∑ k ∈ J, A i k * x k ≤ b i) ∨
      (∃ w : ι → ℝ, (∀ i ∈ I, 0 ≤ w i) ∧ (∀ k ∈ J, ∑ i ∈ I, w i * A i k = 0) ∧
        ∑ i ∈ I, w i * b i < 0) := by
  classical
  induction J using Finset.cons_induction generalizing ι with
  | empty =>
    by_cases hb : ∃ i₀ ∈ I, b i₀ < 0
    · obtain ⟨i₀, hi₀, hbi₀⟩ := hb
      refine Or.inr ⟨fun i => if i = i₀ then 1 else 0,
        fun i _ => by dsimp only; split_ifs <;> norm_num,
        fun _ hk => by simp at hk, ?_⟩
      simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', hi₀, if_true]
      exact hbi₀
    · refine Or.inl ⟨fun _ => 0, fun i hi => ?_⟩
      rw [sum_empty]
      exact le_of_not_gt fun hlt => hb ⟨i, hi, hlt⟩
  | cons a J ha ih =>
    let I_pos : Finset ι := I.filter fun i => 0 < A i a
    let I_neg : Finset ι := I.filter fun i => A i a < 0
    let I_zero : Finset ι := I.filter fun i => A i a = 0
    let ι' := (ι × ι) ⊕ ι
    let e_inl : (ι × ι) ↪ ι' := ⟨Sum.inl, Sum.inl_injective⟩
    let e_inr : ι ↪ ι' := ⟨Sum.inr, Sum.inr_injective⟩
    let I' : Finset ι' := (I_pos ×ˢ I_neg).map e_inl ∪ I_zero.map e_inr
    have hdisj_I' : Disjoint ((I_pos ×ˢ I_neg).map e_inl) (I_zero.map e_inr) := by
      rw [Finset.disjoint_left]
      rintro _ hp hz
      obtain ⟨_, _, rfl⟩ := mem_map.mp hp
      obtain ⟨_, _, h⟩ := mem_map.mp hz
      cases h
    let A' : ι' → α → ℝ := Sum.elim
      (fun p k => (-A p.2 a) * A p.1 k + A p.1 a * A p.2 k)
      (fun i k => A i k)
    let b' : ι' → ℝ := Sum.elim
      (fun p => (-A p.2 a) * b p.1 + A p.1 a * b p.2)
      (fun i => b i)
    rcases ih I' A' b' with ⟨x, hx⟩ | ⟨w', hw'0, hw'A, hw'b⟩
    · -- Primal lift: separate lower bounds from `I_neg` and upper bounds from `I_pos`.
      let S : ι → ℝ := fun i => ∑ k ∈ J, A i k * x k
      have hLU : ∀ i ∈ I_pos, ∀ j ∈ I_neg,
          (S j - b j) / (-A j a) ≤ (b i - S i) / A i a := by
        intro i hi j hj
        have hi_pos : 0 < A i a := (mem_filter.mp hi).2
        have hj_neg : A j a < 0 := (mem_filter.mp hj).2
        have hj_pos : 0 < -A j a := by linarith
        have hmem : e_inl (i, j) ∈ I' :=
          mem_union_left _ (mem_map_of_mem e_inl (mem_product.mpr ⟨hi, hj⟩))
        have hpair := hx (e_inl (i, j)) hmem
        have hsum_pair : ∑ k ∈ J, A' (e_inl (i, j)) k * x k =
            (-A j a) * S i + A i a * S j := by
          simp only [A', e_inl, Function.Embedding.coeFn_mk, Sum.elim_inl, add_mul,
            sum_add_distrib, S, mul_sum]
          congr 1 <;> refine sum_congr rfl fun _ _ => by ring
        rw [hsum_pair] at hpair
        simp only [b', e_inl, Function.Embedding.coeFn_mk, Sum.elim_inl] at hpair
        rw [div_le_div_iff₀ hj_pos hi_pos]
        linarith
      obtain ⟨t, ht_pos, ht_neg⟩ : ∃ t : ℝ,
          (∀ i ∈ I_pos, t ≤ (b i - S i) / A i a) ∧
          (∀ j ∈ I_neg, (S j - b j) / (-A j a) ≤ t) := by
        by_cases hpos : I_pos.Nonempty
        · refine ⟨I_pos.inf' hpos (fun i => (b i - S i) / A i a),
            fun i hi => Finset.inf'_le _ hi,
            fun j hj => (Finset.le_inf'_iff hpos _).mpr fun i hi => hLU i hi j hj⟩
        · have hpos_emp : I_pos = ∅ := Finset.not_nonempty_iff_eq_empty.mp hpos
          by_cases hneg : I_neg.Nonempty
          · refine ⟨I_neg.sup' hneg (fun j => (S j - b j) / (-A j a)),
              fun i hi => by simp [hpos_emp] at hi,
              fun j hj => Finset.le_sup' (f := fun j => (S j - b j) / (-A j a)) hj⟩
          · have hneg_emp : I_neg = ∅ := Finset.not_nonempty_iff_eq_empty.mp hneg
            exact ⟨0, fun i hi => by simp [hpos_emp] at hi,
              fun j hj => by simp [hneg_emp] at hj⟩
      refine Or.inl ⟨fun k => if k = a then t else x k, fun i hi => ?_⟩
      rw [sum_cons]
      dsimp only
      rw [if_pos rfl]
      have hrest : ∑ k ∈ J, A i k * (if k = a then t else x k) = S i := by
        refine sum_congr rfl fun k hk => ?_
        have hka : k ≠ a := fun h => ha (h ▸ hk)
        rw [if_neg hka]
      rw [hrest]
      rcases lt_trichotomy 0 (A i a) with hgt | heq | hlt
      · have hle := (le_div_iff₀ hgt).mp (ht_pos i (mem_filter.mpr ⟨hi, hgt⟩))
        have hcomm : A i a * t = t * A i a := mul_comm _ _
        linarith
      · have hz : A i a = 0 := heq.symm
        have hmem : e_inr i ∈ I' := mem_union_right _ (mem_map_of_mem e_inr (mem_filter.mpr ⟨hi, hz⟩))
        have hpair := hx (e_inr i) hmem
        simp only [A', b', e_inr, Function.Embedding.coeFn_mk, Sum.elim_inr] at hpair
        rw [hz, zero_mul, zero_add]
        exact hpair
      · have hpos_neg : 0 < -A i a := by linarith
        have hle := (div_le_iff₀ hpos_neg).mp (ht_neg i (mem_filter.mpr ⟨hi, hlt⟩))
        have hcomm : t * (-A i a) = -(A i a * t) := by ring
        linarith
    · -- Dual lift: pull `w'` back along the Fourier–Motzkin elimination rows.
      let w : ι → ℝ := fun i =>
        if 0 < A i a then ∑ j ∈ I_neg, w' (e_inl (i, j)) * (-A j a)
        else if A i a < 0 then ∑ i' ∈ I_pos, w' (e_inl (i', i)) * A i' a
        else w' (e_inr i)
      have hw_nonneg : ∀ i ∈ I, 0 ≤ w i := by
        intro i hi
        dsimp only [w]
        split_ifs with h1 h2
        · refine sum_nonneg fun j hj => mul_nonneg ?_ (by linarith [(mem_filter.mp hj).2])
          exact hw'0 _ (mem_union_left _ (mem_map_of_mem e_inl
            (mem_product.mpr ⟨mem_filter.mpr ⟨hi, h1⟩, hj⟩)))
        · refine sum_nonneg fun i' hi' => mul_nonneg ?_ (le_of_lt (mem_filter.mp hi').2)
          exact hw'0 _ (mem_union_left _ (mem_map_of_mem e_inl
            (mem_product.mpr ⟨hi', mem_filter.mpr ⟨hi, h2⟩⟩)))
        · have hz : A i a = 0 := by linarith
          exact hw'0 _ (mem_union_right _ (mem_map_of_mem e_inr (mem_filter.mpr ⟨hi, hz⟩)))
      have hI_part : I_pos ∪ (I_neg ∪ I_zero) = I := by
        ext i
        simp only [I_pos, I_neg, I_zero, mem_union, mem_filter]
        constructor
        · rintro (h | h | h) <;> exact h.1
        · intro hi
          rcases lt_trichotomy 0 (A i a) with h | h | h
          · exact Or.inl ⟨hi, h⟩
          · exact Or.inr (Or.inr ⟨hi, h.symm⟩)
          · exact Or.inr (Or.inl ⟨hi, h⟩)
      have hdisj1 : Disjoint I_pos (I_neg ∪ I_zero) := by
        rw [Finset.disjoint_left]
        simp only [I_pos, I_neg, I_zero, mem_union, mem_filter]
        rintro i ⟨_, h1⟩ (⟨_, h2⟩ | ⟨_, h2⟩) <;> linarith
      have hdisj2 : Disjoint I_neg I_zero := by
        rw [Finset.disjoint_left]
        simp only [I_neg, I_zero, mem_filter]
        rintro i ⟨_, h1⟩ ⟨_, h2⟩
        linarith
      have hsum_w_mul : ∀ f : ι → ℝ, ∑ i ∈ I, w i * f i =
          (∑ p ∈ I_pos ×ˢ I_neg, w' (e_inl p) * ((-A p.2 a) * f p.1 + A p.1 a * f p.2)) +
            ∑ i ∈ I_zero, w' (e_inr i) * f i := by
        intro f
        rw [← hI_part, sum_union hdisj1, sum_union hdisj2]
        have hpos_sum : ∑ i ∈ I_pos, w i * f i =
            ∑ p ∈ I_pos ×ˢ I_neg, w' (e_inl p) * ((-A p.2 a) * f p.1) := by
          rw [Finset.sum_product]
          refine sum_congr rfl fun i hi => ?_
          have hi' : 0 < A i a := (mem_filter.mp hi).2
          simp only [w, if_pos hi', sum_mul, mul_assoc]
        have hneg_sum : ∑ j ∈ I_neg, w j * f j =
            ∑ p ∈ I_pos ×ˢ I_neg, w' (e_inl p) * (A p.1 a * f p.2) := by
          rw [Finset.sum_product_right]
          refine sum_congr rfl fun j hj => ?_
          have hj' : A j a < 0 := (mem_filter.mp hj).2
          have hj_not : ¬ 0 < A j a := by linarith
          simp only [w, if_neg hj_not, if_pos hj', sum_mul, mul_assoc]
        have hzero_sum : ∑ i ∈ I_zero, w i * f i = ∑ i ∈ I_zero, w' (e_inr i) * f i := by
          refine sum_congr rfl fun i hi => ?_
          have hz : A i a = 0 := (mem_filter.mp hi).2
          simp only [w, hz, lt_irrefl, if_false]
        rw [hpos_sum, hneg_sum, hzero_sum, ← add_assoc, ← sum_add_distrib]
        congr 1
        refine sum_congr rfl fun _ _ => by ring
      have hI'_expand : ∀ g : ι' → ℝ, ∑ idx ∈ I', w' idx * g idx =
          (∑ p ∈ I_pos ×ˢ I_neg, w' (e_inl p) * g (e_inl p)) +
            ∑ i ∈ I_zero, w' (e_inr i) * g (e_inr i) := by
        intro g
        rw [sum_union hdisj_I', sum_map, sum_map]
      refine Or.inr ⟨w, hw_nonneg, ?_, ?_⟩
      · intro k hk
        rcases mem_cons.mp hk with hka | hkJ
        · rw [hka, hsum_w_mul]
          have h1 : ∑ p ∈ I_pos ×ˢ I_neg,
              w' (e_inl p) * ((-A p.2 a) * A p.1 a + A p.1 a * A p.2 a) = 0 :=
            sum_eq_zero fun _ _ => by ring
          have h2 : ∑ i ∈ I_zero, w' (e_inr i) * A i a = 0 :=
            sum_eq_zero fun i hi => by rw [(mem_filter.mp hi).2, mul_zero]
          rw [h1, h2, add_zero]
        · rw [hsum_w_mul]
          have heq := hw'A k hkJ
          rw [hI'_expand (fun idx => A' idx k)] at heq
          exact heq
      · rw [hsum_w_mul]
        have hlt := hw'b
        rw [hI'_expand b'] at hlt
        exact hlt

/-! ### Upward rational rounding and integer stencil realization -/

/-- **From real divisor LP weights to an integer vanishing-order stencil.** Given real weights `x`
on `J = (Nat.divisors L').erase 1` (`2 ≤ B ≤ L'`) with slope `≤ (1 + ε₀)(1 - 1/B)`, dominance `≥ 1`
on `[1, B)`, and nonnegativity `≥ 0` on `[B, L')`, upward rational rounding and denominator
clearing construct a balanced integer stencil `(c, m, B)` achieving normalized slope `< 1 + 2 ε₀`. -/
theorem exists_stencil_of_real_lp_with_support {B L' : ℕ} {ε₀ : ℝ} (hB : 2 ≤ B) (hBL : B ≤ L')
    (hε₀ : 0 < ε₀) {x : ℕ → ℝ}
    (hx_slope : ∑ k ∈ (Nat.divisors L').erase 1, Real.log k * x k ≤
      (1 + ε₀) * (1 - 1 / (B : ℝ)))
    (hx_win : ∀ r ∈ Ico 1 B,
      (1 : ℝ) ≤ ∑ k ∈ (Nat.divisors L').erase 1, ((r % k : ℕ) : ℝ) * x k)
    (hx_nonneg : ∀ r ∈ Ico B L',
      (0 : ℝ) ≤ ∑ k ∈ (Nat.divisors L').erase 1, ((r % k : ℕ) : ℝ) * x k) :
    ∃ (c : ℕ →₀ ℤ) (m : ℕ),
      c 0 = 0 ∧ IsBalanced c ∧ 1 ≤ m ∧
        (∀ r : ℕ, 0 ≤ stepWeight c r) ∧
        (∀ r ∈ Ico 1 B, (m : ℤ) ≤ stepWeight c r) ∧
        stencilSlope c / ((m : ℝ) * (1 - 1 / (B : ℝ))) < 1 + 2 * ε₀ ∧
        (∀ k ∈ c.support, k ∣ L') := by
  classical
  have hL'_pos : 0 < L' := by omega
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hB1 : (1 : ℝ) < B := by exact_mod_cast hB
  have h1B : 0 < 1 - 1 / (B : ℝ) := by rw [sub_pos, div_lt_one hB0]; exact hB1
  set J := (Nat.divisors L').erase 1
  have hJ_ge2 : ∀ k ∈ J, 2 ≤ k := by
    intro k hk
    have hk1 : k ≠ 1 := (mem_erase.mp hk).1
    have hk0 : 0 < k := Nat.pos_of_mem_divisors (mem_erase.mp hk).2
    omega
  have hJ_dvd : ∀ k ∈ J, k ∣ L' := fun k hk => Nat.dvd_of_mem_divisors (mem_erase.mp hk).2
  set S_log : ℝ := ∑ k ∈ J, Real.log k
  have hS_log_nonneg : 0 ≤ S_log :=
    sum_nonneg fun k hk => Real.log_nonneg (by exact_mod_cast (by have := hJ_ge2 k hk; omega : 1 ≤ k))
  set δ_rat : ℝ := ε₀ * (1 - 1 / (B : ℝ)) / (S_log + 1)
  have hδ_pos : 0 < δ_rat := div_pos (mul_pos hε₀ h1B) (by linarith)
  have hSδ_lt : S_log * δ_rat < ε₀ * (1 - 1 / (B : ℝ)) := by
    have h1 : (S_log + 1) * δ_rat = ε₀ * (1 - 1 / (B : ℝ)) :=
      mul_div_cancel₀ _ (by linarith)
    linarith
  have hrat_ex : ∀ k : ℕ, ∃ q : ℚ, x k < (q : ℝ) ∧ (q : ℝ) < x k + δ_rat :=
    fun k => exists_rat_btwn (lt_add_of_pos_right (x k) hδ_pos)
  let q : ℕ → ℚ := fun k => Classical.choose (hrat_ex k)
  have hq_gt : ∀ k : ℕ, x k < (q k : ℝ) := fun k => (Classical.choose_spec (hrat_ex k)).1
  have hq_lt : ∀ k : ℕ, (q k : ℝ) < x k + δ_rat := fun k => (Classical.choose_spec (hrat_ex k)).2
  have hq_slope : ∑ k ∈ J, Real.log k * (q k : ℝ) < (1 + 2 * ε₀) * (1 - 1 / (B : ℝ)) := by
    have hle : ∑ k ∈ J, Real.log k * (q k : ℝ) ≤ ∑ k ∈ J, Real.log k * (x k + δ_rat) := by
      refine sum_le_sum fun k hk => ?_
      have hlk : 0 ≤ Real.log k :=
        Real.log_nonneg (by exact_mod_cast (by have := hJ_ge2 k hk; omega : 1 ≤ k))
      exact mul_le_mul_of_nonneg_left (hq_lt k).le hlk
    have hexp : ∑ k ∈ J, Real.log k * (x k + δ_rat) =
        (∑ k ∈ J, Real.log k * x k) + S_log * δ_rat := by
      simp only [S_log, mul_add, sum_add_distrib, sum_mul]
    linarith
  have hq_win : ∀ r ∈ Ico 1 B, (1 : ℝ) ≤ ∑ k ∈ J, ((r % k : ℕ) : ℝ) * (q k : ℝ) := by
    intro r hr
    refine (hx_win r hr).trans (sum_le_sum fun k _ => ?_)
    exact mul_le_mul_of_nonneg_left (hq_gt k).le (Nat.cast_nonneg _)
  have hq_nonneg : ∀ r ∈ Ico B L', (0 : ℝ) ≤ ∑ k ∈ J, ((r % k : ℕ) : ℝ) * (q k : ℝ) := by
    intro r hr
    refine (hx_nonneg r hr).trans (sum_le_sum fun k _ => ?_)
    exact mul_le_mul_of_nonneg_left (hq_gt k).le (Nat.cast_nonneg _)
  set D : ℕ := ∏ k ∈ J, (q k).den
  have hD_pos : 0 < D := prod_pos fun k _ => (q k).pos
  have hD_ge1 : 1 ≤ D := hD_pos
  have hD_real_pos : (0 : ℝ) < D := by exact_mod_cast hD_pos
  let z : ℕ → ℤ := fun k => (q k).num * ((D / (q k).den : ℕ) : ℤ)
  have hz_real : ∀ k ∈ J, (z k : ℝ) = (D : ℝ) * (q k : ℝ) := by
    intro k hk
    have hdvd : (q k).den ∣ D := dvd_prod_of_mem (fun j => (q j).den) hk
    have hden_ne : ((q k).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (q k).pos.ne'
    simp only [z, Int.cast_mul, Int.cast_natCast, Nat.cast_div hdvd hden_ne, Rat.cast_def]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  let c : ℕ →₀ ℤ := Finsupp.single 1 (∑ k ∈ J, z k) + ∑ k ∈ J, Finsupp.single k (-(k : ℤ) * z k)
  have h1_notMem : 1 ∉ J := fun h => (mem_erase.mp h).1 rfl
  have hc0 : c 0 = 0 := by
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (by omega : (0 : ℕ) ≠ 1),
      Finsupp.finsetSum_apply, zero_add, sum_eq_zero]
    intro k hk
    have hk_ge2 := hJ_ge2 k hk
    exact Finsupp.single_eq_of_ne (by omega : (0 : ℕ) ≠ k)
  have hc1 : c 1 = ∑ k ∈ J, z k := by
    have hsum0 : (∑ k ∈ J, Finsupp.single k (-(k : ℤ) * z k)) 1 = 0 := by
      rw [Finsupp.finsetSum_apply, sum_eq_zero]
      intro k hk
      exact Finsupp.single_eq_of_ne (fun h => (mem_erase.mp hk).1 h.symm)
    rw [Finsupp.add_apply, Finsupp.single_eq_same, hsum0, add_zero]
  have hc_mem : ∀ k ∈ J, c k = -(k : ℤ) * z k := by
    intro k hk
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (mem_erase.mp hk).1, zero_add,
      Finsupp.finsetSum_apply, sum_eq_single k]
    · exact Finsupp.single_eq_same
    · intro j _ hjk
      exact Finsupp.single_eq_of_ne hjk.symm
    · intro h; exact absurd hk h
  have hc_out : ∀ k : ℕ, k ∉ insert 1 J → c k = 0 := by
    intro k hk
    have hk1 : k ≠ 1 := fun h => hk (mem_insert.mpr (Or.inl h))
    have hkJ : k ∉ J := fun h => hk (mem_insert.mpr (Or.inr h))
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hk1, zero_add,
      Finsupp.finsetSum_apply, sum_eq_zero]
    intro j hj
    exact Finsupp.single_eq_of_ne (fun h => hkJ (h ▸ hj))
  have hc_supp : c.support ⊆ insert 1 J := by
    intro k hk
    by_contra hnot
    exact Finsupp.mem_support_iff.mp hk (hc_out k hnot)
  have hbal : IsBalanced c := by
    rw [IsBalanced, sum_subset hc_supp (fun k _ hk => by
      rw [Finsupp.notMem_support_iff.mp hk, Int.cast_zero, zero_div]),
      sum_insert h1_notMem, hc1, Nat.cast_one, div_one, Int.cast_sum]
    have hsumJ : ∑ k ∈ J, (c k : ℝ) / k = -∑ k ∈ J, (z k : ℝ) := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun k hk => ?_
      have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hJ_ge2 k hk; omega)
      rw [hc_mem k hk]
      push_cast
      rw [div_eq_iff hk_ne]
      ring
    rw [hsumJ]
    ring
  have hstep_formula : ∀ r : ℕ, (stepWeight c r : ℝ) =
      (D : ℝ) * ∑ k ∈ J, ((r % k : ℕ) : ℝ) * (q k : ℝ) := by
    intro r
    rw [stepWeight_eq_sum_mod hc0 hbal r,
      sum_subset hc_supp (fun k _ hk => by
        rw [Finsupp.notMem_support_iff.mp hk, Int.cast_zero, neg_zero, zero_div, zero_mul]),
      sum_insert h1_notMem, Nat.mod_one, Nat.cast_zero, mul_zero, zero_add, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hJ_ge2 k hk; omega)
    rw [hc_mem k hk]
    push_cast
    have hdiv : -(-(k : ℝ) * (z k : ℝ)) / k = (z k : ℝ) := by
      rw [div_eq_iff hk_ne]
      ring
    rw [hdiv, hz_real k hk]
    ring
  have hstep_mod_L' : ∀ r : ℕ, stepWeight c r = stepWeight c (r % L') := by
    intro r
    have hR : (stepWeight c r : ℝ) = (stepWeight c (r % L') : ℝ) := by
      rw [hstep_formula r, hstep_formula (r % L')]
      congr 1
      refine sum_congr rfl fun k hk => ?_
      rw [Nat.mod_mod_of_dvd r (hJ_dvd k hk)]
    exact_mod_cast hR
  have hwin_c : ∀ r ∈ Ico 1 B, (D : ℤ) ≤ stepWeight c r := by
    intro r hr
    have hR : (D : ℝ) ≤ (stepWeight c r : ℝ) := by
      rw [hstep_formula r]
      calc (D : ℝ) = (D : ℝ) * 1 := (mul_one _).symm
        _ ≤ (D : ℝ) * ∑ k ∈ J, ((r % k : ℕ) : ℝ) * (q k : ℝ) :=
            mul_le_mul_of_nonneg_left (hq_win r hr) hD_real_pos.le
    exact_mod_cast hR
  have hstep_nonneg : ∀ r : ℕ, 0 ≤ stepWeight c r := by
    intro r
    rw [hstep_mod_L']
    set r' := r % L'
    have hr'_lt : r' < L' := Nat.mod_lt r hL'_pos
    rcases Nat.eq_zero_or_pos r' with hz | hpos
    · rw [hz, stepWeight_zero]
    · by_cases hr'B : r' < B
      · have hle := hwin_c r' (mem_Ico.mpr ⟨hpos, hr'B⟩)
        omega
      · have hR : (0 : ℝ) ≤ (stepWeight c r' : ℝ) := by
          rw [hstep_formula r']
          exact mul_nonneg hD_real_pos.le (hq_nonneg r' (mem_Ico.mpr ⟨by omega, hr'_lt⟩))
        exact_mod_cast hR
  have hslope_eq : stencilSlope c = (D : ℝ) * ∑ k ∈ J, Real.log k * (q k : ℝ) := by
    rw [stencilSlope,
      sum_subset hc_supp (fun k _ hk => by
        rw [Finsupp.notMem_support_iff.mp hk, Int.cast_zero, neg_zero, zero_mul, zero_div]),
      sum_insert h1_notMem, Nat.cast_one, Real.log_one, mul_zero, zero_div, zero_add, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hJ_ge2 k hk; omega)
    rw [hc_mem k hk]
    push_cast
    have hdiv : -(-(k : ℝ) * (z k : ℝ)) * Real.log k / k = (z k : ℝ) * Real.log k := by
      rw [div_eq_iff hk_ne]
      ring
    rw [hdiv, hz_real k hk]
    ring
  have hslope_lt : stencilSlope c / ((D : ℝ) * (1 - 1 / (B : ℝ))) < 1 + 2 * ε₀ := by
    rw [div_lt_iff₀ (mul_pos hD_real_pos h1B), hslope_eq]
    have hmul := mul_lt_mul_of_pos_left hq_slope hD_real_pos
    linarith [show (D : ℝ) * ((1 + 2 * ε₀) * (1 - 1 / (B : ℝ))) =
      (1 + 2 * ε₀) * ((D : ℝ) * (1 - 1 / (B : ℝ))) by ring]
  refine ⟨c, D, hc0, hbal, hD_ge1, hstep_nonneg, hwin_c, hslope_lt, ?_⟩
  intro k hk
  rcases mem_insert.mp (hc_supp hk) with rfl | hkJ
  · exact one_dvd _
  · exact hJ_dvd k hkJ

/-- Rational rounding preserves residue inequalities and produces a balanced integer stencil. -/
theorem exists_stencil_of_real_lp {B L' : ℕ} {ε₀ : ℝ} (hB : 2 ≤ B) (hBL : B ≤ L')
    (hε₀ : 0 < ε₀) {x : ℕ → ℝ}
    (hx_slope : ∑ k ∈ (Nat.divisors L').erase 1, Real.log k * x k ≤
      (1 + ε₀) * (1 - 1 / (B : ℝ)))
    (hx_win : ∀ r ∈ Ico 1 B,
      (1 : ℝ) ≤ ∑ k ∈ (Nat.divisors L').erase 1, ((r % k : ℕ) : ℝ) * x k)
    (hx_nonneg : ∀ r ∈ Ico B L',
      (0 : ℝ) ≤ ∑ k ∈ (Nat.divisors L').erase 1, ((r % k : ℕ) : ℝ) * x k) :
    ∃ (c : ℕ →₀ ℤ) (m : ℕ), c 0 = 0 ∧ IsBalanced c ∧ 1 ≤ m ∧
      (∀ r : ℕ, 0 ≤ stepWeight c r) ∧
      (∀ r ∈ Ico 1 B, (m : ℤ) ≤ stepWeight c r) ∧
      stencilSlope c / ((m : ℝ) * (1 - 1 / (B : ℝ))) < 1 + 2 * ε₀ := by
  obtain ⟨c, m, h0, hb, hm, hn, hw, hs, _⟩ :=
    exists_stencil_of_real_lp_with_support hB hBL hε₀ hx_slope hx_win hx_nonneg
  exact ⟨c, m, h0, hb, hm, hn, hw, hs⟩

/-! ### Exact Möbius identities and elementary dyadic estimates -/

private lemma sum_Ico_split {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (g : ℕ → ℝ) :
    ∑ r ∈ Ico a c, g r = (∑ r ∈ Ico a b, g r) + ∑ r ∈ Ico b c, g r := by
  have hunion : Ico a b ∪ Ico b c = Ico a c := Ico_union_Ico_eq_Ico hab hbc
  have hdisj : Disjoint (Ico a b) (Ico b c) := by
    rw [Finset.disjoint_left]
    intro r h1 h2
    simp only [mem_Ico] at h1 h2
    omega
  rw [← hunion, sum_union hdisj]

private lemma nat_div_succ_sub_div (b m : ℕ) (hb : 1 ≤ b) :
    (((m + 1) / b : ℕ) : ℤ) - ((m / b : ℕ) : ℤ) = if b ∣ m + 1 then 1 else 0 := by
  have hdiv := Nat.div_add_mod m b
  have hlt := Nat.mod_lt m hb
  set q := m / b
  set s := m % b
  have hm1 : m + 1 = (s + 1) + b * q := by omega
  by_cases hs : s + 1 < b
  · have hmod : (m + 1) % b = s + 1 := by
      rw [hm1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
    have hndvd : ¬ b ∣ m + 1 := fun h => by
      have := Nat.mod_eq_zero_of_dvd h; omega
    have hquot : (m + 1) / b = q := by
      rw [hm1, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hs, zero_add]
    rw [hquot, if_neg hndvd, sub_self]
  · have hs' : s + 1 = b := by omega
    have hm1' : m + 1 = b * (q + 1) := by
      calc m + 1 = (s + 1) + b * q := hm1
        _ = b + b * q := by rw [hs']
        _ = b * (q + 1) := by ring
    have hdvd : b ∣ m + 1 := ⟨q + 1, hm1'⟩
    have hquot : (m + 1) / b = q + 1 := by
      rw [hm1', Nat.mul_div_right _ hb]
    rw [hquot, if_pos hdvd]
    push_cast
    ring

/-- **Exact Möbius floor-sum identity.** `∑_{1 ≤ b ≤ r} μ(b) ⌊r / b⌋ = 1` for every `r ≥ 1`. -/
theorem sum_Icc_moebius_mul_div_eq_one {r : ℕ} (hr : 1 ≤ r) :
    ∑ b ∈ Icc 1 r, (ArithmeticFunction.moebius b : ℝ) * ((r / b : ℕ) : ℝ) = 1 := by
  have hint : ∀ n : ℕ,
      ∑ b ∈ Icc 1 (n + 1), ArithmeticFunction.moebius b * (((n + 1) / b : ℕ) : ℤ) = 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hext : ∑ b ∈ Icc 1 (n + 1 + 1),
          ArithmeticFunction.moebius b * (((n + 1) / b : ℕ) : ℤ) = 1 := by
        rw [Finset.sum_Icc_succ_top (by omega), ih,
          Nat.div_eq_of_lt (by omega : n + 1 < n + 1 + 1), Nat.cast_zero, mul_zero, add_zero]
      have hdiff : (∑ b ∈ Icc 1 (n + 1 + 1),
            ArithmeticFunction.moebius b * (((n + 1 + 1) / b : ℕ) : ℤ)) -
          (∑ b ∈ Icc 1 (n + 1 + 1),
            ArithmeticFunction.moebius b * (((n + 1) / b : ℕ) : ℤ)) = 0 := by
        rw [← sum_sub_distrib]
        have hterm : ∀ b ∈ Icc 1 (n + 1 + 1),
            ArithmeticFunction.moebius b * (((n + 1 + 1) / b : ℕ) : ℤ) -
              ArithmeticFunction.moebius b * (((n + 1) / b : ℕ) : ℤ) =
            if b ∣ n + 1 + 1 then ArithmeticFunction.moebius b else 0 := by
          intro b hb
          rw [← mul_sub, nat_div_succ_sub_div b (n + 1) (mem_Icc.mp hb).1]
          split_ifs <;> simp
        rw [sum_congr rfl hterm, ← sum_filter]
        have hdiv_set : (Icc 1 (n + 1 + 1)).filter (· ∣ n + 1 + 1) = (n + 1 + 1).divisors := by
          ext b
          simp only [mem_filter, mem_Icc, Nat.mem_divisors]
          constructor
          · rintro ⟨_, hd⟩; exact ⟨hd, by omega⟩
          · rintro ⟨hd, _⟩
            exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), Nat.le_of_dvd (by omega) hd⟩, hd⟩
        rw [hdiv_set, ← ArithmeticFunction.coe_mul_zeta_apply,
          ArithmeticFunction.moebius_mul_coe_zeta,
          ArithmeticFunction.one_apply_ne (by omega : n + 1 + 1 ≠ 1)]
      omega
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = n + 1 := ⟨r - 1, by omega⟩
  have hR := congrArg (Int.cast (R := ℝ)) (hint n)
  simpa only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_one] using hR

private lemma coprimeMoebiusHarmonicSum_one (T : ℕ) :
    GaloisForLFunctions.BezoutValuationIncidence.coprimeMoebiusHarmonicSum 1 T =
      ∑ b ∈ Icc 1 T, (ArithmeticFunction.moebius b : ℝ) / b := by
  unfold GaloisForLFunctions.BezoutValuationIncidence.coprimeMoebiusHarmonicSum
  refine sum_congr rfl fun b _ => ?_
  rw [if_pos (Nat.coprime_one_right b)]

private lemma rankinProduct_one :
    GaloisForLFunctions.BezoutValuationIncidence.rankinProduct 1 = 1 := by
  simp [GaloisForLFunctions.BezoutValuationIncidence.rankinProduct]

private lemma moebiusLogHarmonicPartial_eq_sum_Icc (T : ℕ) :
    _root_.RHTower.Sieve.moebiusLogHarmonicPartial T =
      ∑ b ∈ Icc 1 T, (-(ArithmeticFunction.moebius b : ℝ) / b) * Real.log b := by
  rw [_root_.RHTower.Sieve.moebiusLogHarmonicPartial]
  have hrange : range (T + 1) = insert 0 (Icc 1 T) := by
    ext b
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hrange, sum_insert (by simp), _root_.RHTower.Sieve.moebiusLogHarmonicTerm_zero, zero_add]
  refine sum_congr rfl fun b _ => ?_
  rw [_root_.RHTower.Sieve.moebiusLogHarmonicTerm, Real.rpow_neg_one, div_eq_mul_inv]
  ring

private lemma nat_sq_lt_two_pow {m : ℕ} (hm : 5 ≤ m) : m ^ 2 < 2 ^ m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases eq_or_lt_of_le hm with h5 | h6
    · have hm4 : m = 4 := by omega
      subst hm4
      norm_num
    · have ihm := ih (by omega : 5 ≤ m)
      have h2m : 2 * m + 1 < m ^ 2 := by
        have : 5 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
        rw [sq]
        omega
      calc (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by ring
        _ < m ^ 2 + m ^ 2 := by omega
        _ = m ^ 2 * 2 := by ring
        _ < 2 ^ m * 2 := Nat.mul_lt_mul_of_pos_right ihm zero_lt_two
        _ = 2 ^ (m + 1) := by ring

private lemma sum_linear_div_two_pow_le (K : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∑ i ∈ range K, (A + i) / (2 : ℝ) ^ i ≤ 2 * A + 2 := by
  have htel : ∀ n : ℕ, ∑ i ∈ range n, (A + i) / (2 : ℝ) ^ i =
      (2 * A + 2) - (2 * A + 2 * n + 2) / (2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have h2n : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
      have hstep : (2 * A + 2 * ((n + 1 : ℕ) : ℝ) + 2) / (2 : ℝ) ^ (n + 1) =
          (2 * A + 2 * (n : ℝ) + 2) / (2 : ℝ) ^ n - (A + (n : ℝ)) / (2 : ℝ) ^ n := by
        rw [← sub_div, show (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n * 2 by ring,
          div_eq_div_iff (mul_ne_zero h2n two_ne_zero) h2n]
        push_cast
        ring
      linarith
  rw [htel K]
  have hnonneg : 0 ≤ (2 * A + 2 * (K : ℝ) + 2) / (2 : ℝ) ^ K := by positivity
  linarith

/-! ### Balanced Möbius residue test function and dual elimination -/

/-- The balanced Möbius residue test function at cutoff `T`:
`F_T(r) = ∑_{1 ≤ b ≤ T} (-μ(b)/b) (r % b) + m(T) (r % (T + 1))`. -/
def moebiusResidueTest (T r : ℕ) : ℝ :=
  (∑ b ∈ Icc 1 T, (-(ArithmeticFunction.moebius b : ℝ) / b) * ((r % b : ℕ) : ℝ)) +
    GaloisForLFunctions.BezoutValuationIncidence.coprimeMoebiusHarmonicSum 1 T *
      ((r % (T + 1) : ℕ) : ℝ)

/-- **Exact window identity.** On `1 ≤ r ≤ T`, `moebiusResidueTest T r = 1`. -/
theorem moebiusResidueTest_eq_one {T r : ℕ} (hr1 : 1 ≤ r) (hrT : r ≤ T) :
    moebiusResidueTest T r = 1 := by
  rw [moebiusResidueTest, coprimeMoebiusHarmonicSum_one,
    Nat.mod_eq_of_lt (by omega : r < T + 1)]
  have hterm : ∀ b ∈ Icc 1 T,
      (-(ArithmeticFunction.moebius b : ℝ) / b) * ((r % b : ℕ) : ℝ) =
        -((ArithmeticFunction.moebius b : ℝ) / b) * (r : ℝ) +
          (ArithmeticFunction.moebius b : ℝ) * ((r / b : ℕ) : ℝ) := by
    intro b hb
    have hb1 : 1 ≤ b := (mem_Icc.mp hb).1
    have hbR : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hdiv : (b : ℝ) * ((r / b : ℕ) : ℝ) + ((r % b : ℕ) : ℝ) = r := by
      exact_mod_cast Nat.div_add_mod r b
    have hmodR : ((r % b : ℕ) : ℝ) = (r : ℝ) - (b : ℝ) * ((r / b : ℕ) : ℝ) := by linarith
    rw [hmodR, mul_sub]
    have hcancel : (-(ArithmeticFunction.moebius b : ℝ) / b) * ((b : ℝ) * ((r / b : ℕ) : ℝ)) =
        -((ArithmeticFunction.moebius b : ℝ) * ((r / b : ℕ) : ℝ)) := by
      rw [← mul_assoc, div_mul_cancel₀ _ hbR]
      ring
    rw [hcancel]
    ring
  rw [sum_congr rfl hterm, sum_add_distrib]
  have hlin : ∑ b ∈ Icc 1 T, -((ArithmeticFunction.moebius b : ℝ) / b) * (r : ℝ) =
      -(∑ b ∈ Icc 1 T, (ArithmeticFunction.moebius b : ℝ) / b) * (r : ℝ) := by
    rw [neg_mul, sum_mul, ← sum_neg_distrib]
    exact sum_congr rfl fun _ _ => by ring
  have hfloor : ∑ b ∈ Icc 1 T, (ArithmeticFunction.moebius b : ℝ) * ((r / b : ℕ) : ℝ) = 1 := by
    rw [← sum_subset (Icc_subset_Icc_right hrT)]
    · exact sum_Icc_moebius_mul_div_eq_one hr1
    · intro b hb hnot
      have hgt : r < b := by
        simp only [mem_Icc] at hb hnot
        omega
      rw [Nat.div_eq_of_lt hgt, Nat.cast_zero, mul_zero]
  rw [hlin, hfloor]
  ring

/-- Dual reduction of the finite divisor LP on `J = (Nat.divisors L').erase 1`. -/
private lemma exists_real_lp_or_dual {B L' : ℕ} {ε₀ : ℝ} (hB : 2 ≤ B) (hBL : B < L') :
    (∃ x : ℕ → ℝ,
        (∑ k ∈ (Nat.divisors L').erase 1, Real.log k * x k ≤
          (1 + ε₀) * (1 - 1 / (B : ℝ))) ∧
        (∀ r ∈ Ico 1 B,
          (1 : ℝ) ≤ ∑ k ∈ (Nat.divisors L').erase 1, ((r % k : ℕ) : ℝ) * x k) ∧
        (∀ r ∈ Ico B L',
          (0 : ℝ) ≤ ∑ k ∈ (Nat.divisors L').erase 1, ((r % k : ℕ) : ℝ) * x k)) ∨
      (∃ u : ℕ → ℝ,
        (∀ r ∈ Ico 1 L', 0 ≤ u r) ∧
        (∀ k : ℕ, 1 ≤ k → k ∣ L' →
          ∑ r ∈ Ico 1 L', u r * ((r % k : ℕ) : ℝ) = Real.log k) ∧
        (1 + ε₀) * (1 - 1 / (B : ℝ)) < ∑ r ∈ Ico 1 B, u r) := by
  set J := (Nat.divisors L').erase 1
  let A : ℕ → ℕ → ℝ := fun i k => if i = 0 then Real.log k else -((i % k : ℕ) : ℝ)
  let b : ℕ → ℝ := fun i =>
    if i = 0 then (1 + ε₀) * (1 - 1 / (B : ℝ)) else if i < B then -1 else 0
  rcases finset_farkas (range L') J A b with ⟨x, hx⟩ | ⟨w, hw0, hwA, hwb⟩
  · refine Or.inl ⟨x, ?_, ?_, ?_⟩
    · have h0 := hx 0 (mem_range.mpr (by omega))
      simpa only [A, b, if_true] using h0
    · intro r hr
      obtain ⟨hr1, hrB⟩ := mem_Ico.mp hr
      have hr0 : r ≠ 0 := by omega
      have h := hx r (mem_range.mpr (by omega))
      simp only [A, b, if_neg hr0, if_pos hrB, neg_mul, sum_neg_distrib] at h
      linarith
    · intro r hr
      obtain ⟨hrB, hrL⟩ := mem_Ico.mp hr
      have hr0 : r ≠ 0 := by omega
      have hrnB : ¬ r < B := by omega
      have h := hx r (mem_range.mpr hrL)
      simp only [A, b, if_neg hr0, if_neg hrnB, neg_mul, sum_neg_distrib] at h
      linarith
  · have hrange_eq : range L' = insert 0 (Ico 1 L') := by
      ext i
      simp only [mem_range, mem_insert, mem_Ico]
      omega
    have hw_col : ∀ k ∈ J, ∑ r ∈ Ico 1 L', w r * ((r % k : ℕ) : ℝ) = w 0 * Real.log k := by
      intro k hk
      have h := hwA k hk
      rw [hrange_eq, sum_insert (by simp)] at h
      have h0 : w 0 * A 0 k = w 0 * Real.log k := by simp [A]
      have hrest : ∑ r ∈ Ico 1 L', w r * A r k =
          -∑ r ∈ Ico 1 L', w r * ((r % k : ℕ) : ℝ) := by
        rw [← sum_neg_distrib]
        refine sum_congr rfl fun r hr => ?_
        have hr0 : r ≠ 0 := by have := (mem_Ico.mp hr).1; omega
        simp only [A, if_neg hr0, mul_neg]
      linarith
    have hw0_pos : 0 < w 0 := by
      have hw0_nonneg : 0 ≤ w 0 := hw0 0 (mem_range.mpr (by omega))
      rcases eq_or_lt_of_le hw0_nonneg with hzero | hpos
      · exfalso
        have hL'_mem : L' ∈ J :=
          mem_erase.mpr ⟨by omega, Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩⟩
        have hcolL := hw_col L' hL'_mem
        rw [← hzero, zero_mul] at hcolL
        have hall_zero : ∀ r ∈ Ico 1 L', w r = 0 := by
          have hnonneg : ∀ r ∈ Ico 1 L', 0 ≤ w r * ((r % L' : ℕ) : ℝ) := fun r hr =>
            mul_nonneg (hw0 r (mem_range.mpr (mem_Ico.mp hr).2)) (Nat.cast_nonneg _)
          have hsum0 := (sum_eq_zero_iff_of_nonneg hnonneg).mp hcolL
          intro r hr
          have hm := hsum0 r hr
          rw [Nat.mod_eq_of_lt (mem_Ico.mp hr).2] at hm
          have hrR : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (mem_Ico.mp hr).1; omega)
          exact (mul_eq_zero.mp hm).resolve_right hrR
        have hb0 : ∑ i ∈ range L', w i * b i = 0 := by
          rw [hrange_eq, sum_insert (by simp), ← hzero, zero_mul, zero_add]
          exact sum_eq_zero fun r hr => by rw [hall_zero r hr, zero_mul]
        linarith
      · exact hpos
    refine Or.inr ⟨fun r => w r / w 0, ?_, ?_, ?_⟩
    · intro r hr
      exact div_nonneg (hw0 r (mem_range.mpr (mem_Ico.mp hr).2)) hw0_pos.le
    · intro k hk1 hk_dvd
      rcases eq_or_lt_of_le hk1 with rfl | hk2
      · simp [Nat.mod_one]
      · have hkJ : k ∈ J :=
          mem_erase.mpr ⟨by omega, Nat.mem_divisors.mpr ⟨hk_dvd, by omega⟩⟩
        have hsum : ∑ r ∈ Ico 1 L', (w r / w 0) * ((r % k : ℕ) : ℝ) =
            (∑ r ∈ Ico 1 L', w r * ((r % k : ℕ) : ℝ)) / w 0 := by
          rw [sum_div]
          exact sum_congr rfl fun _ _ => by ring
        rw [hsum, hw_col k hkJ, mul_div_cancel_left₀ _ hw0_pos.ne']
    · have hb_expand : ∑ i ∈ range L', w i * b i =
          w 0 * ((1 + ε₀) * (1 - 1 / (B : ℝ))) - ∑ r ∈ Ico 1 B, w r := by
        rw [hrange_eq, sum_insert (by simp), sum_Ico_split (by omega) hBL.le]
        have h0 : w 0 * b 0 = w 0 * ((1 + ε₀) * (1 - 1 / (B : ℝ))) := by simp [b]
        have h1 : ∑ r ∈ Ico 1 B, w r * b r = -∑ r ∈ Ico 1 B, w r := by
          rw [← sum_neg_distrib]
          refine sum_congr rfl fun r hr => ?_
          obtain ⟨hr1, hrB⟩ := mem_Ico.mp hr
          have hr0 : r ≠ 0 := by omega
          simp only [b, if_neg hr0, if_pos hrB, mul_neg, mul_one]
        have h2 : ∑ r ∈ Ico B L', w r * b r = 0 := by
          refine sum_eq_zero fun r hr => ?_
          obtain ⟨hrB, _⟩ := mem_Ico.mp hr
          have hr0 : r ≠ 0 := by omega
          have hrnB : ¬ r < B := by omega
          simp only [b, if_neg hr0, if_neg hrnB, mul_zero]
        linarith
      rw [hb_expand] at hwb
      have hsum_div : ∑ r ∈ Ico 1 B, w r / w 0 = (∑ r ∈ Ico 1 B, w r) / w 0 :=
        (sum_div _ _ _).symm
      rw [hsum_div, lt_div_iff₀ hw0_pos]
      linarith [show ((1 + ε₀) * (1 - 1 / (B : ℝ))) * w 0 =
        w 0 * ((1 + ε₀) * (1 - 1 / (B : ℝ))) by ring]

private lemma global_pairing_moebiusResidueTest {T L' : ℕ} {u : ℕ → ℝ}
    (hTL' : ∀ b : ℕ, 1 ≤ b → b ≤ T + 1 → b ∣ L')
    (hu_eq : ∀ k : ℕ, 1 ≤ k → k ∣ L' →
      ∑ r ∈ Ico 1 L', u r * ((r % k : ℕ) : ℝ) = Real.log k) :
    ∑ r ∈ Ico 1 L', u r * moebiusResidueTest T r =
      _root_.RHTower.Sieve.moebiusLogHarmonicPartial T +
        GaloisForLFunctions.BezoutValuationIncidence.coprimeMoebiusHarmonicSum 1 T *
          Real.log (T + 1 : ℕ) := by
  obtain ⟨δ_T, hδ_T⟩ : ∃ δ_T : ℝ,
      δ_T = GaloisForLFunctions.BezoutValuationIncidence.coprimeMoebiusHarmonicSum 1 T := ⟨_, rfl⟩
  rw [← hδ_T]
  have hexp : ∀ r ∈ Ico 1 L', u r * moebiusResidueTest T r =
      (∑ b ∈ Icc 1 T, (-(ArithmeticFunction.moebius b : ℝ) / b) *
        (u r * ((r % b : ℕ) : ℝ))) +
        δ_T * (u r * ((r % (T + 1) : ℕ) : ℝ)) := by
    intro r _
    rw [moebiusResidueTest, ← hδ_T, mul_add, mul_sum]
    congr 1
    · exact sum_congr rfl fun _ _ => by ring
    · ring
  rw [sum_congr rfl hexp, sum_add_distrib, sum_comm, ← mul_sum]
  have hsum1 : ∑ b ∈ Icc 1 T, ∑ r ∈ Ico 1 L',
      (-(ArithmeticFunction.moebius b : ℝ) / b) * (u r * ((r % b : ℕ) : ℝ)) =
      _root_.RHTower.Sieve.moebiusLogHarmonicPartial T := by
    rw [moebiusLogHarmonicPartial_eq_sum_Icc]
    refine sum_congr rfl fun b hb => ?_
    obtain ⟨hb1, hbT⟩ := mem_Icc.mp hb
    rw [← mul_sum, hu_eq b hb1 (hTL' b hb1 (by omega))]
  rw [hsum1, hu_eq (T + 1) (by omega) (hTL' (T + 1) (by omega) le_rfl)]

private lemma dyadic_log_scale_bounds {ℓ T : ℕ} (hℓ10 : 10 ≤ ℓ) (hT : T = 2 ^ ℓ) :
    (ℓ : ℝ) / 2 ≤ 1 + Real.log (T : ℝ) ∧
      Real.log (T + 1 : ℕ) ≤ 2 * (ℓ : ℝ) ∧
      (ℓ : ℝ) ^ 3 / 8 ≤ (1 + Real.log (T : ℝ)) ^ 3 ∧
      (ℓ : ℝ) ^ 4 / 16 ≤ (1 + Real.log (T : ℝ)) ^ 4 ∧
      (ℓ : ℝ) ^ 2 / 9 ≤ Real.sqrt (T : ℝ) := by
  have hlog2_lo : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2_hi : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast (by omega : 1 ≤ ℓ)
  have hℓ_nn : (0 : ℝ) ≤ ℓ := by positivity
  have hlogT_eq : Real.log (T : ℝ) = (ℓ : ℝ) * Real.log 2 := by
    rw [hT, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  have hlogT_lo : (ℓ : ℝ) / 2 ≤ 1 + Real.log (T : ℝ) := by
    rw [hlogT_eq]
    linarith [mul_le_mul_of_nonneg_left hlog2_lo hℓ_nn]
  have hlogB_hi : Real.log (T + 1 : ℕ) ≤ 2 * (ℓ : ℝ) := by
    have hT1 : 1 ≤ T := by rw [hT]; exact Nat.one_le_pow ℓ 2 zero_lt_two
    have hle : ((T + 1 : ℕ) : ℝ) ≤ (2 ^ (ℓ + 1) : ℕ) := by
      exact_mod_cast (show T + 1 ≤ 2 ^ (ℓ + 1) by rw [pow_succ, hT]; omega)
    calc Real.log (T + 1 : ℕ) ≤ Real.log (2 ^ (ℓ + 1) : ℕ) := Real.log_le_log (by positivity) hle
      _ = ((ℓ + 1 : ℕ) : ℝ) * Real.log 2 := by rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
      _ ≤ ((ℓ : ℝ) + 1) * 1 := by
          push_cast; exact mul_le_mul_of_nonneg_left hlog2_hi (by positivity)
      _ ≤ 2 * (ℓ : ℝ) := by linarith
  have hL3_ge : (ℓ : ℝ) ^ 3 / 8 ≤ (1 + Real.log (T : ℝ)) ^ 3 := by
    calc (ℓ : ℝ) ^ 3 / 8 = ((ℓ : ℝ) / 2) ^ 3 := by ring
      _ ≤ (1 + Real.log (T : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) hlogT_lo 3
  have hL4_ge : (ℓ : ℝ) ^ 4 / 16 ≤ (1 + Real.log (T : ℝ)) ^ 4 := by
    calc (ℓ : ℝ) ^ 4 / 16 = ((ℓ : ℝ) / 2) ^ 4 := by ring
      _ ≤ (1 + Real.log (T : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) hlogT_lo 4
  have hsqrtT_ge : (ℓ : ℝ) ^ 2 / 9 ≤ Real.sqrt (T : ℝ) := by
    obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ℓ / 2 := ⟨ℓ / 2, rfl⟩
    have hm5 : 5 ≤ m := by omega
    have hm_sq : m ^ 2 < 2 ^ m := nat_sq_lt_two_pow hm5
    have h3m : ℓ ≤ m * 3 := by omega
    have hℓ3 : (ℓ : ℝ) / 3 ≤ m := by
      rw [div_le_iff₀ (by norm_num)]
      exact_mod_cast h3m
    have h2m_sq : (2 ^ m) ^ 2 ≤ T := by
      rw [← pow_mul, hT]
      exact Nat.pow_le_pow_right zero_lt_two (by omega : m * 2 ≤ ℓ)
    have hsqrt_ge_2m : ((2 ^ m : ℕ) : ℝ) ≤ Real.sqrt (T : ℝ) :=
      Real.le_sqrt_of_sq_le (by exact_mod_cast h2m_sq)
    have hm_sqR : (m : ℝ) ^ 2 ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast hm_sq.le
    calc (ℓ : ℝ) ^ 2 / 9 = ((ℓ : ℝ) / 3) ^ 2 := by ring
      _ ≤ (m : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hℓ3 2
      _ ≤ Real.sqrt (T : ℝ) := hm_sqR.trans hsqrt_ge_2m
  exact ⟨hlogT_lo, hlogB_hi, hL3_ge, hL4_ge, hsqrtT_ge⟩

private lemma abs_moebiusResidueTest_le_tail {T : ℕ} {K₁ K₂ : ℝ}
    (hT256 : 256 ≤ T) (hK₁0 : 0 ≤ K₁)
    (hK₁ : ∀ (f c M X t : ℕ), f ≠ 0 → 1 ≤ c → M / c = t → 256 ≤ t →
      |∑ b ∈ Icc 1 X, GaloisForLFunctions.BezoutValuationIncidence.coprimeMoebiusWeight f b *
        Int.fract ((M : ℝ) / ((c * b : ℕ) : ℝ))| ≤
        K₁ * GaloisForLFunctions.BezoutValuationIncidence.rankinProduct f * (t : ℝ) /
          (1 + Real.log (t : ℝ)) ^ 3 + Real.sqrt (t : ℝ))
    (hδ_bound : |GaloisForLFunctions.BezoutValuationIncidence.coprimeMoebiusHarmonicSum 1 T| ≤
      K₂ / (1 + Real.log (T : ℝ)) ^ 4)
    {r : ℕ} (hr : T + 1 ≤ r) :
    |moebiusResidueTest T r| ≤
      (K₁ / (1 + Real.log (T : ℝ)) ^ 3 + 1 / Real.sqrt (T : ℝ) +
        K₂ / (1 + Real.log (T : ℝ)) ^ 4) * (r : ℝ) := by
  obtain ⟨δ_T, hδ_T⟩ : ∃ δ_T : ℝ,
      δ_T = GaloisForLFunctions.BezoutValuationIncidence.coprimeMoebiusHarmonicSum 1 T := ⟨_, rfl⟩
  rw [← hδ_T] at hδ_bound
  have hT_pos : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hr256 : 256 ≤ r := by omega
  have hrR_ge : (T : ℝ) ≤ r := by exact_mod_cast (by omega : T ≤ r)
  have hr_pos : (0 : ℝ) < r := by positivity
  have hfract_eq : ∑ b ∈ Icc 1 T, (-(ArithmeticFunction.moebius b : ℝ) / b) * ((r % b : ℕ) : ℝ) =
      -∑ b ∈ Icc 1 T, GaloisForLFunctions.BezoutValuationIncidence.coprimeMoebiusWeight 1 b *
        Int.fract ((r : ℝ) / ((1 * b : ℕ) : ℝ)) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun b _ => ?_
    rw [GaloisForLFunctions.BezoutValuationIncidence.coprimeMoebiusWeight,
      if_pos (Nat.coprime_one_right b), one_mul, Int.fract_div_natCast_eq_div_natCast_mod]
    ring
  have hsaw := hK₁ 1 1 r T r one_ne_zero le_rfl (Nat.div_one r) hr256
  rw [rankinProduct_one, mul_one] at hsaw
  have hlog_mono : 1 + Real.log (T : ℝ) ≤ 1 + Real.log (r : ℝ) := by
    linarith [Real.log_le_log hT_pos hrR_ge]
  have hterm1 : K₁ * (r : ℝ) / (1 + Real.log (r : ℝ)) ^ 3 ≤
      (K₁ / (1 + Real.log (T : ℝ)) ^ 3) * (r : ℝ) := by
    rw [mul_div_right_comm]
    refine mul_le_mul_of_nonneg_right ?_ hr_pos.le
    exact div_le_div_of_nonneg_left hK₁0 (by positivity)
      (pow_le_pow_left₀ (by positivity) hlog_mono 3)
  have hterm2 : Real.sqrt (r : ℝ) ≤ (1 / Real.sqrt (T : ℝ)) * (r : ℝ) := by
    have hsq_mono : Real.sqrt (T : ℝ) ≤ Real.sqrt (r : ℝ) := Real.sqrt_le_sqrt hrR_ge
    have hsqT_pos : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr hT_pos
    rw [one_div_mul_eq_div, le_div_iff₀ hsqT_pos]
    calc Real.sqrt (r : ℝ) * Real.sqrt (T : ℝ)
        ≤ Real.sqrt (r : ℝ) * Real.sqrt (r : ℝ) :=
          mul_le_mul_of_nonneg_left hsq_mono (Real.sqrt_nonneg _)
      _ = r := Real.mul_self_sqrt hr_pos.le
  have hterm3 : |δ_T * ((r % (T + 1) : ℕ) : ℝ)| ≤
      (K₂ / (1 + Real.log (T : ℝ)) ^ 4) * (r : ℝ) := by
    rw [abs_mul, abs_of_nonneg (a := ((r % (T + 1) : ℕ) : ℝ)) (Nat.cast_nonneg _)]
    have hmod_le : ((r % (T + 1) : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.mod_le r (T + 1)
    have hK₂_nn : 0 ≤ K₂ / (1 + Real.log (T : ℝ)) ^ 4 := (abs_nonneg δ_T).trans hδ_bound
    exact mul_le_mul hδ_bound hmod_le (Nat.cast_nonneg _) hK₂_nn
  rw [moebiusResidueTest, ← hδ_T, hfract_eq]
  calc |-∑ b ∈ Icc 1 T, GaloisForLFunctions.BezoutValuationIncidence.coprimeMoebiusWeight 1 b *
          Int.fract ((r : ℝ) / ((1 * b : ℕ) : ℝ)) + δ_T * ((r % (T + 1) : ℕ) : ℝ)|
      ≤ |∑ b ∈ Icc 1 T, GaloisForLFunctions.BezoutValuationIncidence.coprimeMoebiusWeight 1 b *
          Int.fract ((r : ℝ) / ((1 * b : ℕ) : ℝ))| + |δ_T * ((r % (T + 1) : ℕ) : ℝ)| := by
        simpa only [abs_neg] using abs_add_le
          (-∑ b ∈ Icc 1 T,
            GaloisForLFunctions.BezoutValuationIncidence.coprimeMoebiusWeight 1 b *
              Int.fract ((r : ℝ) / ((1 * b : ℕ) : ℝ)))
          (δ_T * ((r % (T + 1) : ℕ) : ℝ))
    _ ≤ (K₁ * (r : ℝ) / (1 + Real.log (r : ℝ)) ^ 3 + Real.sqrt (r : ℝ)) +
          (K₂ / (1 + Real.log (T : ℝ)) ^ 4) * (r : ℝ) := add_le_add hsaw hterm3
    _ ≤ ((K₁ / (1 + Real.log (T : ℝ)) ^ 3) * (r : ℝ) + (1 / Real.sqrt (T : ℝ)) * (r : ℝ)) +
          (K₂ / (1 + Real.log (T : ℝ)) ^ 4) * (r : ℝ) :=
        add_le_add (add_le_add hterm1 hterm2) le_rfl
    _ = (K₁ / (1 + Real.log (T : ℝ)) ^ 3 + 1 / Real.sqrt (T : ℝ) +
          K₂ / (1 + Real.log (T : ℝ)) ^ 4) * (r : ℝ) := by ring

private lemma abs_moebiusResidueTest_le_three_mul {T : ℕ} (hT1 : 1 ≤ T)
    (hδ_le_one : |GaloisForLFunctions.BezoutValuationIncidence.coprimeMoebiusHarmonicSum 1 T| ≤ 1)
    (r : ℕ) :
    |moebiusResidueTest T r| ≤ 3 * (T : ℝ) := by
  obtain ⟨δ_T, hδ_T⟩ : ∃ δ_T : ℝ,
      δ_T = GaloisForLFunctions.BezoutValuationIncidence.coprimeMoebiusHarmonicSum 1 T := ⟨_, rfl⟩
  rw [← hδ_T] at hδ_le_one
  have hT_real : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  have h1 : |∑ b ∈ Icc 1 T, (-(ArithmeticFunction.moebius b : ℝ) / b) * ((r % b : ℕ) : ℝ)| ≤ T := by
    calc |∑ b ∈ Icc 1 T, (-(ArithmeticFunction.moebius b : ℝ) / b) * ((r % b : ℕ) : ℝ)|
        ≤ ∑ b ∈ Icc 1 T, |(-(ArithmeticFunction.moebius b : ℝ) / b) * ((r % b : ℕ) : ℝ)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ Icc 1 T, (1 : ℝ) := by
          refine sum_le_sum fun b hb => ?_
          have hb1 : 1 ≤ b := (mem_Icc.mp hb).1
          have hb0 : (0 : ℝ) < b := by exact_mod_cast hb1
          have hμ : |(ArithmeticFunction.moebius b : ℝ)| ≤ 1 := by
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          have hdiv_nn : 0 ≤ ((r % b : ℕ) : ℝ) / b := div_nonneg (Nat.cast_nonneg _) hb0.le
          have hmod : ((r % b : ℕ) : ℝ) / b ≤ 1 := by
            rw [div_le_one hb0]; exact_mod_cast (Nat.mod_lt r hb1).le
          rw [show (-(ArithmeticFunction.moebius b : ℝ) / b) * ((r % b : ℕ) : ℝ) =
            -(ArithmeticFunction.moebius b : ℝ) * (((r % b : ℕ) : ℝ) / b) by ring,
            abs_mul, abs_neg, abs_of_nonneg hdiv_nn]
          exact mul_le_one₀ hμ hdiv_nn hmod
      _ = T := by simp
  have h2 : |δ_T * ((r % (T + 1) : ℕ) : ℝ)| ≤ (T : ℝ) + 1 := by
    rw [abs_mul, abs_of_nonneg (a := ((r % (T + 1) : ℕ) : ℝ)) (Nat.cast_nonneg _)]
    have hmod : ((r % (T + 1) : ℕ) : ℝ) ≤ (T : ℝ) + 1 := by
      exact_mod_cast (Nat.mod_lt r (by omega : 0 < T + 1)).le
    calc |δ_T| * ((r % (T + 1) : ℕ) : ℝ) ≤ 1 * ((T : ℝ) + 1) :=
          mul_le_mul hδ_le_one hmod (Nat.cast_nonneg _) zero_le_one
      _ = (T : ℝ) + 1 := one_mul _
  rw [moebiusResidueTest, ← hδ_T]
  have habs := abs_add_le
    (∑ b ∈ Icc 1 T, (-(ArithmeticFunction.moebius b : ℝ) / b) * ((r % b : ℕ) : ℝ))
    (δ_T * ((r % (T + 1) : ℕ) : ℝ))
  linarith

private lemma abs_sum_dual_reg1_le {ℓ T B k₀ L' : ℕ} {K₁ K₂ η_T : ℝ} {u : ℕ → ℝ}
    (hℓ10 : 10 ≤ ℓ) (hT : T = 2 ^ ℓ) (hB : B = T + 1) (hk₀ : k₀ = 2 ^ (4 * ℓ) * B)
    (hk₀_le_L' : k₀ ≤ L') (hk₀_dvd : k₀ ∣ L')
    (hK₁0 : 0 ≤ K₁) (hK₂0 : 0 ≤ K₂)
    (hL3_ge : (ℓ : ℝ) ^ 3 / 8 ≤ (1 + Real.log (T : ℝ)) ^ 3)
    (hL4_ge : (ℓ : ℝ) ^ 4 / 16 ≤ (1 + Real.log (T : ℝ)) ^ 4)
    (hsqrtT_ge : (ℓ : ℝ) ^ 2 / 9 ≤ Real.sqrt (T : ℝ))
    (hη_eq : η_T = K₁ / (1 + Real.log (T : ℝ)) ^ 3 + 1 / Real.sqrt (T : ℝ) +
      K₂ / (1 + Real.log (T : ℝ)) ^ 4)
    (hF_reg1 : ∀ r : ℕ, B ≤ r → |moebiusResidueTest T r| ≤ η_T * (r : ℝ))
    (hu0 : ∀ r ∈ Ico 1 L', 0 ≤ u r)
    (hu_eq : ∀ k : ℕ, 1 ≤ k → k ∣ L' →
      ∑ r ∈ Ico 1 L', u r * ((r % k : ℕ) : ℝ) = Real.log k) :
    |∑ r ∈ Ico B k₀, u r * moebiusResidueTest T r| ≤
      (48 * K₁ + 54 + 96 * K₂) / (ℓ : ℝ) := by
  have hℓ_pos : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast (by omega : 1 ≤ ℓ)
  have hT_pos_nat : 1 ≤ T := by rw [hT]; exact Nat.one_le_pow ℓ 2 zero_lt_two
  have hB1 : 1 ≤ B := by omega
  have hk₀_pos : 1 ≤ k₀ := by rw [hk₀]; exact Nat.mul_pos (pow_pos zero_lt_two _) hB1
  have hlog2_hi : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hη_nonneg : 0 ≤ η_T := by rw [hη_eq]; positivity
  have hsum_ur : ∑ r ∈ Ico B k₀, u r * (r : ℝ) ≤ Real.log (k₀ : ℝ) := by
    have hsub : Ico B k₀ ⊆ Ico 1 L' :=
      (Ico_subset_Ico_left hB1).trans (Ico_subset_Ico_right hk₀_le_L')
    calc ∑ r ∈ Ico B k₀, u r * (r : ℝ)
        = ∑ r ∈ Ico B k₀, u r * ((r % k₀ : ℕ) : ℝ) := by
          refine sum_congr rfl fun r hr => ?_
          rw [Nat.mod_eq_of_lt (mem_Ico.mp hr).2]
      _ ≤ ∑ r ∈ Ico 1 L', u r * ((r % k₀ : ℕ) : ℝ) :=
          sum_le_sum_of_subset_of_nonneg hsub fun r hr _ =>
            mul_nonneg (hu0 r hr) (Nat.cast_nonneg _)
      _ = Real.log (k₀ : ℝ) := hu_eq k₀ hk₀_pos hk₀_dvd
  have hlog_k₀ : Real.log (k₀ : ℝ) ≤ 6 * (ℓ : ℝ) := by
    have hk₀_le_nat : k₀ ≤ 2 ^ (6 * ℓ) := by
      have hB_le : B ≤ 2 ^ (2 * ℓ) := by
        calc B = T + 1 := hB
          _ ≤ 2 * T := by omega
          _ = 2 ^ (ℓ + 1) := by rw [hT, pow_succ]; ring
          _ ≤ 2 ^ (2 * ℓ) := Nat.pow_le_pow_right zero_lt_two (by omega)
      calc k₀ = 2 ^ (4 * ℓ) * B := hk₀
        _ ≤ 2 ^ (4 * ℓ) * 2 ^ (2 * ℓ) := Nat.mul_le_mul_left _ hB_le
        _ = 2 ^ (6 * ℓ) := by rw [← pow_add]; congr 1; omega
    calc Real.log (k₀ : ℝ) ≤ Real.log (2 ^ (6 * ℓ) : ℕ) :=
          Real.log_le_log (by exact_mod_cast hk₀_pos) (by exact_mod_cast hk₀_le_nat)
      _ = ((6 * ℓ : ℕ) : ℝ) * Real.log 2 := by rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
      _ ≤ (6 * (ℓ : ℝ)) * 1 := by
          push_cast; exact mul_le_mul_of_nonneg_left hlog2_hi (by positivity)
      _ = 6 * (ℓ : ℝ) := mul_one _
  have h6η : η_T * (6 * (ℓ : ℝ)) ≤ (48 * K₁ + 54 + 96 * K₂) / (ℓ : ℝ) := by
    have hp1 : (K₁ / (1 + Real.log (T : ℝ)) ^ 3) * (6 * (ℓ : ℝ)) ≤ 48 * K₁ / (ℓ : ℝ) := by
      have hℓ2_le3 : (ℓ : ℝ) ^ 2 ≤ (ℓ : ℝ) ^ 3 := pow_le_pow_right₀ hℓ1 (by omega)
      calc (K₁ / (1 + Real.log (T : ℝ)) ^ 3) * (6 * (ℓ : ℝ))
          ≤ (K₁ / ((ℓ : ℝ) ^ 3 / 8)) * (6 * (ℓ : ℝ)) :=
            mul_le_mul_of_nonneg_right
              (div_le_div_of_nonneg_left hK₁0 (by positivity) hL3_ge) (by positivity)
        _ = 48 * K₁ * (ℓ : ℝ) / (ℓ : ℝ) ^ 3 := by ring
        _ ≤ 48 * K₁ * (ℓ : ℝ) / (ℓ : ℝ) ^ 2 :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hℓ2_le3
        _ = 48 * K₁ / (ℓ : ℝ) := by rw [sq, mul_div_mul_right _ _ hℓ_pos.ne']
    have hp2 : (1 / Real.sqrt (T : ℝ)) * (6 * (ℓ : ℝ)) ≤ 54 / (ℓ : ℝ) := by
      calc (1 / Real.sqrt (T : ℝ)) * (6 * (ℓ : ℝ))
          ≤ (1 / ((ℓ : ℝ) ^ 2 / 9)) * (6 * (ℓ : ℝ)) :=
            mul_le_mul_of_nonneg_right
              (one_div_le_one_div_of_le (by positivity) hsqrtT_ge) (by positivity)
        _ = 54 * (ℓ : ℝ) / (ℓ : ℝ) ^ 2 := by ring
        _ = 54 / (ℓ : ℝ) := by rw [sq, mul_div_mul_right _ _ hℓ_pos.ne']
    have hp3 : (K₂ / (1 + Real.log (T : ℝ)) ^ 4) * (6 * (ℓ : ℝ)) ≤ 96 * K₂ / (ℓ : ℝ) := by
      have hℓ2_le4 : (ℓ : ℝ) ^ 2 ≤ (ℓ : ℝ) ^ 4 := pow_le_pow_right₀ hℓ1 (by omega)
      calc (K₂ / (1 + Real.log (T : ℝ)) ^ 4) * (6 * (ℓ : ℝ))
          ≤ (K₂ / ((ℓ : ℝ) ^ 4 / 16)) * (6 * (ℓ : ℝ)) :=
            mul_le_mul_of_nonneg_right
              (div_le_div_of_nonneg_left hK₂0 (by positivity) hL4_ge) (by positivity)
        _ = 96 * K₂ * (ℓ : ℝ) / (ℓ : ℝ) ^ 4 := by ring
        _ ≤ 96 * K₂ * (ℓ : ℝ) / (ℓ : ℝ) ^ 2 :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hℓ2_le4
        _ = 96 * K₂ / (ℓ : ℝ) := by rw [sq, mul_div_mul_right _ _ hℓ_pos.ne']
    calc η_T * (6 * (ℓ : ℝ))
        = (K₁ / (1 + Real.log (T : ℝ)) ^ 3) * (6 * (ℓ : ℝ)) +
            (1 / Real.sqrt (T : ℝ)) * (6 * (ℓ : ℝ)) +
            (K₂ / (1 + Real.log (T : ℝ)) ^ 4) * (6 * (ℓ : ℝ)) := by
          rw [hη_eq]; ring
      _ ≤ 48 * K₁ / (ℓ : ℝ) + 54 / (ℓ : ℝ) + 96 * K₂ / (ℓ : ℝ) :=
          add_le_add (add_le_add hp1 hp2) hp3
      _ = (48 * K₁ + 54 + 96 * K₂) / (ℓ : ℝ) := by ring
  calc |∑ r ∈ Ico B k₀, u r * moebiusResidueTest T r|
      ≤ ∑ r ∈ Ico B k₀, |u r * moebiusResidueTest T r| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ Ico B k₀, u r * (η_T * (r : ℝ)) := by
        refine sum_le_sum fun r hr => ?_
        have hr_mem : r ∈ Ico 1 L' :=
          (Ico_subset_Ico_left hB1) ((Ico_subset_Ico_right hk₀_le_L') hr)
        rw [abs_mul, abs_of_nonneg (hu0 r hr_mem)]
        exact mul_le_mul_of_nonneg_left (hF_reg1 r (mem_Ico.mp hr).1) (hu0 r hr_mem)
    _ = η_T * ∑ r ∈ Ico B k₀, u r * (r : ℝ) := by
        rw [mul_sum]
        exact sum_congr rfl fun _ _ => by ring
    _ ≤ η_T * (6 * (ℓ : ℝ)) :=
        mul_le_mul_of_nonneg_left (hsum_ur.trans hlog_k₀) hη_nonneg
    _ ≤ (48 * K₁ + 54 + 96 * K₂) / (ℓ : ℝ) := h6η

private lemma sum_dual_dyadic_blocks_le {j₀ M B L' : ℕ} {u : ℕ → ℝ}
    (hB1 : 1 ≤ B)
    (hdvd_block : ∀ d : ℕ, j₀ + d + 1 ≤ M - 1 → 2 ^ (j₀ + d + 1) * B ∣ L')
    (hle_block : ∀ d : ℕ, j₀ + d + 1 ≤ M - 1 → 2 ^ (j₀ + d + 1) * B ≤ L')
    (hu0 : ∀ r ∈ Ico 1 L', 0 ≤ u r)
    (hu_eq : ∀ k : ℕ, 1 ≤ k → k ∣ L' →
      ∑ r ∈ Ico 1 L', u r * ((r % k : ℕ) : ℝ) = Real.log k) :
    ∀ d : ℕ, j₀ + d ≤ M - 1 →
      ∑ r ∈ Ico (2 ^ j₀ * B) (2 ^ (j₀ + d) * B), u r ≤
        ∑ i ∈ range d, Real.log ((2 ^ (j₀ + i + 1) * B : ℕ) : ℝ) /
          ((2 ^ (j₀ + i) * B : ℕ) : ℝ) := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hdM
    have hdM' : j₀ + d + 1 ≤ M - 1 := by omega
    have hlo : 2 ^ j₀ * B ≤ 2 ^ (j₀ + d) * B :=
      Nat.mul_le_mul_right B (Nat.pow_le_pow_right zero_lt_two (by omega))
    have hhi : 2 ^ (j₀ + d) * B ≤ 2 ^ (j₀ + (d + 1)) * B :=
      Nat.mul_le_mul_right B (Nat.pow_le_pow_right zero_lt_two (by omega))
    rw [sum_Ico_split hlo hhi, Finset.sum_range_succ]
    refine add_le_add (ih (by omega)) ?_
    obtain ⟨k_lo, hk_lo⟩ : ∃ k_lo : ℕ, k_lo = 2 ^ (j₀ + d) * B := ⟨_, rfl⟩
    obtain ⟨k_hi, hk_hi⟩ : ∃ k_hi : ℕ, k_hi = 2 ^ (j₀ + d + 1) * B := ⟨_, rfl⟩
    have hk_hi_eq : 2 ^ (j₀ + (d + 1)) * B = k_hi := by rw [hk_hi, add_assoc]
    rw [hk_hi_eq, ← hk_lo, ← hk_hi]
    have hk_lo_pos_nat : 1 ≤ k_lo := by rw [hk_lo]; exact Nat.mul_pos (pow_pos zero_lt_two _) hB1
    have hk_hi_pos_nat : 1 ≤ k_hi := by rw [hk_hi]; exact Nat.mul_pos (pow_pos zero_lt_two _) hB1
    have hk_lo_pos : (0 : ℝ) < k_lo := by exact_mod_cast hk_lo_pos_nat
    have hk_hi_dvd : k_hi ∣ L' := hk_hi ▸ hdvd_block d hdM'
    have hsub : Ico k_lo k_hi ⊆ Ico 1 L' :=
      (Ico_subset_Ico_left hk_lo_pos_nat).trans (Ico_subset_Ico_right (hk_hi ▸ hle_block d hdM'))
    rw [le_div_iff₀ hk_lo_pos, mul_comm, mul_sum]
    calc ∑ r ∈ Ico k_lo k_hi, (k_lo : ℝ) * u r
        ≤ ∑ r ∈ Ico k_lo k_hi, u r * ((r % k_hi : ℕ) : ℝ) := by
          refine sum_le_sum fun r hr => ?_
          obtain ⟨hr1, hr2⟩ := mem_Ico.mp hr
          rw [Nat.mod_eq_of_lt hr2, mul_comm]
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hr1) (hu0 r (hsub hr))
      _ ≤ ∑ r ∈ Ico 1 L', u r * ((r % k_hi : ℕ) : ℝ) :=
          sum_le_sum_of_subset_of_nonneg hsub fun r hr _ =>
            mul_nonneg (hu0 r hr) (Nat.cast_nonneg _)
      _ = Real.log (k_hi : ℝ) := hu_eq k_hi hk_hi_pos_nat hk_hi_dvd

private lemma abs_sum_dual_reg2_le {ℓ T B j₀ M k₀ k_top L' : ℕ} {u : ℕ → ℝ}
    (hℓ10 : 10 ≤ ℓ) (hT_sq : ℓ ^ 2 < T) (hT : T = 2 ^ ℓ) (hB : B = T + 1)
    (hj₀ : j₀ = 4 * ℓ) (hM_j₀ : j₀ + 2 ≤ M)
    (hk₀ : k₀ = 2 ^ j₀ * B) (hktop : k_top = 2 ^ (M - 1) * B)
    (hktop_le_L' : k_top ≤ L')
    (hlogB_hi : Real.log (B : ℝ) ≤ 2 * (ℓ : ℝ))
    (hdvd_block : ∀ d : ℕ, j₀ + d + 1 ≤ M - 1 → 2 ^ (j₀ + d + 1) * B ∣ L')
    (hle_block : ∀ d : ℕ, j₀ + d + 1 ≤ M - 1 → 2 ^ (j₀ + d + 1) * B ≤ L')
    (hF_unif : ∀ r : ℕ, |moebiusResidueTest T r| ≤ 3 * (T : ℝ))
    (hu0 : ∀ r ∈ Ico 1 L', 0 ≤ u r)
    (hu_eq : ∀ k : ℕ, 1 ≤ k → k ∣ L' →
      ∑ r ∈ Ico 1 L', u r * ((r % k : ℕ) : ℝ) = Real.log k) :
    |∑ r ∈ Ico k₀ k_top, u r * moebiusResidueTest T r| ≤ 84 / (ℓ : ℝ) := by
  have hℓ_pos : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  have hT_ge1 : 1 ≤ T := by rw [hT]; exact Nat.one_le_pow ℓ 2 zero_lt_two
  have hB2 : 2 ≤ B := by omega
  have hk₀_pos_nat : 1 ≤ k₀ := by rw [hk₀]; exact Nat.mul_pos (pow_pos zero_lt_two _) (by omega)
  have hk₀_pos : (0 : ℝ) < k₀ := by exact_mod_cast hk₀_pos_nat
  obtain ⟨d₀, hd₀⟩ : ∃ d₀ : ℕ, d₀ = M - 1 - j₀ := ⟨_, rfl⟩
  have hd₀_eq : j₀ + d₀ = M - 1 := by omega
  have hu_reg2 : ∑ r ∈ Ico k₀ k_top, u r ≤
      Real.log (B : ℝ) * (2 * (j₀ : ℝ) + 6) / (k₀ : ℝ) := by
    have hd := sum_dual_dyadic_blocks_le (by omega : 1 ≤ B) hdvd_block hle_block hu0 hu_eq
      d₀ (by omega)
    rw [hd₀_eq, ← hk₀, ← hktop] at hd
    have hterm_le : ∀ i ∈ range d₀,
        Real.log ((2 ^ (j₀ + i + 1) * B : ℕ) : ℝ) / ((2 ^ (j₀ + i) * B : ℕ) : ℝ) ≤
          (Real.log (B : ℝ) / (k₀ : ℝ)) * (((j₀ : ℝ) + 2 + i) / (2 : ℝ) ^ i) := by
      intro i _
      have hpow_le : 2 ^ (j₀ + i + 1) * B ≤ B ^ (j₀ + i + 2) := by
        calc 2 ^ (j₀ + i + 1) * B ≤ B ^ (j₀ + i + 1) * B :=
              Nat.mul_le_mul_right B (Nat.pow_le_pow_left hB2 _)
          _ = B ^ (j₀ + i + 2) := by ring
      have hlog_le : Real.log ((2 ^ (j₀ + i + 1) * B : ℕ) : ℝ) ≤
          ((j₀ : ℝ) + 2 + i) * Real.log (B : ℝ) := by
        have hpos : (0 : ℝ) < (2 ^ (j₀ + i + 1) * B : ℕ) := by
          exact_mod_cast Nat.mul_pos (pow_pos zero_lt_two _) (by omega)
        calc Real.log ((2 ^ (j₀ + i + 1) * B : ℕ) : ℝ)
            ≤ Real.log ((B ^ (j₀ + i + 2) : ℕ) : ℝ) :=
              Real.log_le_log hpos (by exact_mod_cast hpow_le)
          _ = ((j₀ + i + 2 : ℕ) : ℝ) * Real.log (B : ℝ) := by
              rw [Nat.cast_pow, Real.log_pow]
          _ = ((j₀ : ℝ) + 2 + i) * Real.log (B : ℝ) := by push_cast; ring
      have hden_eq : ((2 ^ (j₀ + i) * B : ℕ) : ℝ) = (k₀ : ℝ) * (2 : ℝ) ^ i := by
        rw [hk₀]
        push_cast
        rw [pow_add]
        ring
      rw [hden_eq, show (Real.log (B : ℝ) / (k₀ : ℝ)) * (((j₀ : ℝ) + 2 + i) / (2 : ℝ) ^ i) =
        (((j₀ : ℝ) + 2 + i) * Real.log (B : ℝ)) / ((k₀ : ℝ) * (2 : ℝ) ^ i) by ring]
      exact div_le_div_of_nonneg_right hlog_le (by positivity)
    have hlin_sum := sum_linear_div_two_pow_le d₀ (show (0 : ℝ) ≤ (j₀ : ℝ) + 2 by positivity)
    calc ∑ r ∈ Ico k₀ k_top, u r
        ≤ ∑ i ∈ range d₀, (Real.log (B : ℝ) / (k₀ : ℝ)) * (((j₀ : ℝ) + 2 + i) / (2 : ℝ) ^ i) :=
          hd.trans (sum_le_sum hterm_le)
      _ = (Real.log (B : ℝ) / (k₀ : ℝ)) * ∑ i ∈ range d₀, ((j₀ : ℝ) + 2 + i) / (2 : ℝ) ^ i :=
          (mul_sum _ _ _).symm
      _ ≤ (Real.log (B : ℝ) / (k₀ : ℝ)) * (2 * ((j₀ : ℝ) + 2) + 2) :=
          mul_le_mul_of_nonneg_left hlin_sum
            (div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B))) hk₀_pos.le)
      _ = Real.log (B : ℝ) * (2 * (j₀ : ℝ) + 6) / (k₀ : ℝ) := by ring
  have h2j₀_eq : ((2 ^ j₀ : ℕ) : ℝ) = (T : ℝ) ^ 4 := by
    rw [hj₀, hT]
    push_cast
    rw [mul_comm 4 ℓ, pow_mul]
  have hT4_ge : (ℓ : ℝ) ^ 3 ≤ (T : ℝ) ^ 4 := by
    have hℓ2 : (ℓ : ℝ) ^ 2 ≤ T := by exact_mod_cast hT_sq.le
    have h1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast (by omega : 1 ≤ ℓ)
    calc (ℓ : ℝ) ^ 3 ≤ (ℓ : ℝ) ^ 8 := pow_le_pow_right₀ h1 (by omega)
      _ = ((ℓ : ℝ) ^ 2) ^ 4 := by ring
      _ ≤ (T : ℝ) ^ 4 := pow_le_pow_left₀ (by positivity) hℓ2 4
  have hB_pos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hT_le_B : (T : ℝ) ≤ B := by exact_mod_cast (by omega : T ≤ B)
  have h2j6 : 2 * (j₀ : ℝ) + 6 ≤ 14 * (ℓ : ℝ) := by
    have hj_cast : (j₀ : ℝ) = 4 * (ℓ : ℝ) := by rw [hj₀]; push_cast; rfl
    have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast (by omega : 1 ≤ ℓ)
    linarith
  calc |∑ r ∈ Ico k₀ k_top, u r * moebiusResidueTest T r|
      ≤ ∑ r ∈ Ico k₀ k_top, |u r * moebiusResidueTest T r| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ Ico k₀ k_top, u r * (3 * (T : ℝ)) := by
        refine sum_le_sum fun r hr => ?_
        have hr_mem : r ∈ Ico 1 L' :=
          (Ico_subset_Ico_left hk₀_pos_nat) ((Ico_subset_Ico_right hktop_le_L') hr)
        rw [abs_mul, abs_of_nonneg (hu0 r hr_mem)]
        exact mul_le_mul_of_nonneg_left (hF_unif r) (hu0 r hr_mem)
    _ = 3 * (T : ℝ) * ∑ r ∈ Ico k₀ k_top, u r := by
        rw [mul_sum]
        exact sum_congr rfl fun _ _ => by ring
    _ ≤ 3 * (T : ℝ) * (Real.log (B : ℝ) * (2 * (j₀ : ℝ) + 6) / (k₀ : ℝ)) :=
        mul_le_mul_of_nonneg_left hu_reg2 (by positivity)
    _ = (3 * ((T : ℝ) / (B : ℝ))) *
          (Real.log (B : ℝ) * (2 * (j₀ : ℝ) + 6) / (T : ℝ) ^ 4) := by
        have hk₀_cast : (k₀ : ℝ) = (T : ℝ) ^ 4 * (B : ℝ) := by
          rw [show (k₀ : ℝ) = ((2 ^ j₀ : ℕ) : ℝ) * (B : ℝ) by rw [hk₀]; push_cast; rfl, h2j₀_eq]
        rw [hk₀_cast, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
        ring
    _ ≤ 3 * ((2 * (ℓ : ℝ)) * (14 * (ℓ : ℝ)) / (ℓ : ℝ) ^ 3) := by
        have hTB1 : (T : ℝ) / (B : ℝ) ≤ 1 := (div_le_one hB_pos).mpr hT_le_B
        have hnum : Real.log (B : ℝ) * (2 * (j₀ : ℝ) + 6) ≤ (2 * (ℓ : ℝ)) * (14 * (ℓ : ℝ)) :=
          mul_le_mul hlogB_hi h2j6 (by positivity) (by positivity)
        have hfrac : Real.log (B : ℝ) * (2 * (j₀ : ℝ) + 6) / (T : ℝ) ^ 4 ≤
            (2 * (ℓ : ℝ)) * (14 * (ℓ : ℝ)) / (ℓ : ℝ) ^ 3 :=
          (div_le_div_of_nonneg_right hnum (by positivity)).trans
            (div_le_div_of_nonneg_left (by positivity) (by positivity) hT4_ge)
        exact mul_le_mul (by linarith) hfrac
          (div_nonneg (mul_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B)))
            (by positivity)) (by positivity)) (by norm_num)
    _ = 84 / (ℓ : ℝ) := by
        rw [show 3 * ((2 * (ℓ : ℝ)) * (14 * (ℓ : ℝ)) / (ℓ : ℝ) ^ 3) =
          84 * (ℓ : ℝ) ^ 2 / (ℓ : ℝ) ^ 3 by ring,
          show (ℓ : ℝ) ^ 3 = (ℓ : ℝ) * (ℓ : ℝ) ^ 2 by ring,
          mul_div_mul_right _ _ (pow_ne_zero 2 hℓ_pos.ne')]

private lemma abs_sum_dual_reg3_le {T B L₀ M k_top L' : ℕ} {ε₀ : ℝ} {u : ℕ → ℝ}
    (hε₀ : 0 < ε₀) (hTB : T ≤ B) (hB1 : 1 ≤ B) (hL₀_pos : 0 < L₀)
    (hM6 : 6 ≤ M)
    (hM_ceil : Nat.ceil (24 * (2 + Real.log (L₀ : ℝ)) / ε₀) + 6 ≤ M)
    (hktop : k_top = 2 ^ (M - 1) * B)
    (hL' : L' = 2 ^ M * L₀)
    (hF_unif : ∀ r : ℕ, |moebiusResidueTest T r| ≤ 3 * (T : ℝ))
    (hu0 : ∀ r ∈ Ico 1 L', 0 ≤ u r)
    (hu_eq : ∀ k : ℕ, 1 ≤ k → k ∣ L' →
      ∑ r ∈ Ico 1 L', u r * ((r % k : ℕ) : ℝ) = Real.log k) :
    |∑ r ∈ Ico k_top L', u r * moebiusResidueTest T r| ≤ ε₀ / 8 := by
  have hlog2_hi : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hktop_pos_nat : 1 ≤ k_top := by rw [hktop]; exact Nat.mul_pos (pow_pos zero_lt_two _) hB1
  have hktop_pos : (0 : ℝ) < k_top := by exact_mod_cast hktop_pos_nat
  have hL'_pos : 1 ≤ L' := by rw [hL']; exact Nat.mul_pos (pow_pos zero_lt_two _) hL₀_pos
  have hu_reg3 : ∑ r ∈ Ico k_top L', u r ≤ Real.log (L' : ℝ) / (k_top : ℝ) := by
    have hsub : Ico k_top L' ⊆ Ico 1 L' := Ico_subset_Ico_left hktop_pos_nat
    rw [le_div_iff₀ hktop_pos, mul_comm, mul_sum]
    calc ∑ r ∈ Ico k_top L', (k_top : ℝ) * u r
        ≤ ∑ r ∈ Ico k_top L', u r * ((r % L' : ℕ) : ℝ) := by
          refine sum_le_sum fun r hr => ?_
          obtain ⟨hr1, hr2⟩ := mem_Ico.mp hr
          rw [Nat.mod_eq_of_lt hr2, mul_comm]
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hr1) (hu0 r (hsub hr))
      _ ≤ ∑ r ∈ Ico 1 L', u r * ((r % L' : ℕ) : ℝ) :=
          sum_le_sum_of_subset_of_nonneg hsub fun r hr _ =>
            mul_nonneg (hu0 r hr) (Nat.cast_nonneg _)
      _ = Real.log (L' : ℝ) := hu_eq L' hL'_pos dvd_rfl
  have hlogL' : Real.log (L' : ℝ) ≤ (M : ℝ) + Real.log (L₀ : ℝ) := by
    have hcast : (L' : ℝ) = (2 : ℝ) ^ M * (L₀ : ℝ) := by rw [hL']; push_cast; rfl
    rw [hcast, Real.log_mul (pow_ne_zero M two_ne_zero) (by exact_mod_cast hL₀_pos.ne'),
      Real.log_pow]
    linarith [mul_le_mul_of_nonneg_left hlog2_hi (Nat.cast_nonneg M)]
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : ℕ, m₁ = M - 1 := ⟨_, rfl⟩
  have hm₁_ge5 : 5 ≤ m₁ := by omega
  have hm₁_sq : ((m₁ : ℝ) ^ 2) < (2 : ℝ) ^ m₁ := by exact_mod_cast nat_sq_lt_two_pow hm₁_ge5
  have hm₁_pos : (0 : ℝ) < m₁ := by exact_mod_cast (by omega : 0 < m₁)
  have hm₁_ceil : 24 * (2 + Real.log (L₀ : ℝ)) / ε₀ < (m₁ : ℝ) := by
    have h1 : 24 * (2 + Real.log (L₀ : ℝ)) / ε₀ ≤
        Nat.ceil (24 * (2 + Real.log (L₀ : ℝ)) / ε₀) := Nat.le_ceil _
    have h2 : Nat.ceil (24 * (2 + Real.log (L₀ : ℝ)) / ε₀) + 5 ≤ m₁ := by omega
    have h2R : (Nat.ceil (24 * (2 + Real.log (L₀ : ℝ)) / ε₀) : ℝ) + 5 ≤ m₁ := by exact_mod_cast h2
    linarith
  have hlogL₀_nn : 0 ≤ Real.log (L₀ : ℝ) := Real.log_nonneg (by exact_mod_cast hL₀_pos)
  have hML₀_le : (M : ℝ) + Real.log (L₀ : ℝ) ≤ (m₁ : ℝ) * (2 + Real.log (L₀ : ℝ)) := by
    have hM_eq : (M : ℝ) = (m₁ : ℝ) + 1 := by exact_mod_cast (by omega : M = m₁ + 1)
    have hm₁_ge1 : (1 : ℝ) ≤ m₁ := by exact_mod_cast (by omega : 1 ≤ m₁)
    have hexp : (m₁ : ℝ) * (2 + Real.log (L₀ : ℝ)) - ((m₁ : ℝ) + 1 + Real.log (L₀ : ℝ)) =
        ((m₁ : ℝ) - 1) * (1 + Real.log (L₀ : ℝ)) := by ring
    have hnn : 0 ≤ ((m₁ : ℝ) - 1) * (1 + Real.log (L₀ : ℝ)) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  have hTB_le : (T : ℝ) ≤ B := by exact_mod_cast hTB
  calc |∑ r ∈ Ico k_top L', u r * moebiusResidueTest T r|
      ≤ ∑ r ∈ Ico k_top L', |u r * moebiusResidueTest T r| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ Ico k_top L', u r * (3 * (T : ℝ)) := by
        refine sum_le_sum fun r hr => ?_
        have hr_mem : r ∈ Ico 1 L' := (Ico_subset_Ico_left hktop_pos_nat) hr
        rw [abs_mul, abs_of_nonneg (hu0 r hr_mem)]
        exact mul_le_mul_of_nonneg_left (hF_unif r) (hu0 r hr_mem)
    _ = 3 * (T : ℝ) * ∑ r ∈ Ico k_top L', u r := by
        rw [mul_sum]
        exact sum_congr rfl fun _ _ => by ring
    _ ≤ 3 * (B : ℝ) * (Real.log (L' : ℝ) / ((2 : ℝ) ^ m₁ * (B : ℝ))) := by
        have hktop_cast : (k_top : ℝ) = (2 : ℝ) ^ m₁ * (B : ℝ) := by
          rw [hktop, ← hm₁]; push_cast; rfl
        rw [← hktop_cast]
        exact mul_le_mul (by linarith) hu_reg3
          (sum_nonneg fun r hr => hu0 r ((Ico_subset_Ico_left hktop_pos_nat) hr))
          (by positivity)
    _ = 3 * Real.log (L' : ℝ) / (2 : ℝ) ^ m₁ := by
        have hB_ne : (B : ℝ) ≠ 0 := by exact_mod_cast (by omega : B ≠ 0)
        rw [show 3 * (B : ℝ) * (Real.log (L' : ℝ) / ((2 : ℝ) ^ m₁ * (B : ℝ))) =
          (3 * Real.log (L' : ℝ)) * (B : ℝ) / ((2 : ℝ) ^ m₁ * (B : ℝ)) by ring,
          mul_div_mul_right _ _ hB_ne]
    _ ≤ 3 * ((m₁ : ℝ) * (2 + Real.log (L₀ : ℝ))) / (m₁ : ℝ) ^ 2 :=
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hlogL'.trans hML₀_le) (by norm_num)) (by positivity)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hm₁_sq.le)
    _ = 3 * (2 + Real.log (L₀ : ℝ)) / (m₁ : ℝ) := by
        rw [show 3 * ((m₁ : ℝ) * (2 + Real.log (L₀ : ℝ))) =
          (3 * (2 + Real.log (L₀ : ℝ))) * (m₁ : ℝ) by ring, sq,
          mul_div_mul_right _ _ hm₁_pos.ne']
    _ ≤ ε₀ / 8 := by
        rw [div_le_iff₀ hm₁_pos]
        have hm := (div_lt_iff₀ hε₀).mp hm₁_ceil
        linarith [show (ε₀ / 8) * (m₁ : ℝ) = ((m₁ : ℝ) * ε₀) / 8 by ring]

/-- A common period for the divisor-residue producer at dyadic cutoff `2^ℓ`. -/
def producerPeriod (ε : ℝ) (ℓ : ℕ) : ℕ :=
  2 ^ max (4 * ℓ + 2)
    (Nat.ceil (24 * (2 + Real.log (((2 ^ ℓ + 1).factorial : ℕ) : ℝ)) / ε) + 6) *
      (2 ^ ℓ + 1).factorial

/-- Explicit finite scale at which the Möbius test excludes every Farkas dual witness. -/
theorem exists_real_lp_solution_at {ε₀ K₁ K₂ : ℝ} (hε₀ : 0 < ε₀)
    (hK₁0 : 0 ≤ K₁) (hK₂0 : 0 ≤ K₂)
    (hK₁ : ∀ f c M X t : ℕ, f ≠ 0 → 1 ≤ c → M / c = t → 256 ≤ t →
      |∑ b ∈ Icc 1 X, BezoutValuationIncidence.coprimeMoebiusWeight f b *
        Int.fract ((M : ℝ) / ((c * b : ℕ) : ℝ))| ≤
          K₁ * BezoutValuationIncidence.rankinProduct f * t /
            (1 + Real.log t) ^ 3 + Real.sqrt t)
    (hK₂ : ∀ f : ℕ, f ≠ 0 → ∀ Y : ℕ, 1 ≤ Y →
      |BezoutValuationIncidence.coprimeMoebiusHarmonicSum f Y| ≤
        K₂ * BezoutValuationIncidence.rankinProduct f / (1 + Real.log Y) ^ 4)
    {ℓ : ℕ} (hℓ10 : 10 ≤ ℓ)
    (hscale : 8 * (48 * K₁ + 128 * K₂ + 140 + (1 + ε₀)) / ε₀ + 16 * K₂ < (ℓ : ℝ))
    (hnormal : _root_.RHTower.Sieve.moebiusLogHarmonicPartial (2 ^ ℓ) < 1 + ε₀ / 8) :
    ∃ (B L' : ℕ) (x : ℕ → ℝ), B = 2 ^ ℓ + 1 ∧ L' = producerPeriod ε₀ ℓ ∧
      2 ≤ B ∧ B ≤ L' ∧
      (∑ k ∈ (Nat.divisors L').erase 1, Real.log k * x k ≤
        (1 + ε₀) * (1 - 1 / (B : ℝ))) ∧
      (∀ r ∈ Ico 1 B,
        (1 : ℝ) ≤ ∑ k ∈ (Nat.divisors L').erase 1, ((r % k : ℕ) : ℝ) * x k) ∧
      (∀ r ∈ Ico B L',
        (0 : ℝ) ≤ ∑ k ∈ (Nat.divisors L').erase 1, ((r % k : ℕ) : ℝ) * x k) := by
  obtain ⟨C_all, hC_all⟩ : ∃ C_all : ℝ,
      C_all = 48 * K₁ + 128 * K₂ + 140 + (1 + ε₀) := ⟨_, rfl⟩
  have hC_all_pos : 0 < C_all := by rw [hC_all]; positivity
  have hℓ_ceil : 8 * C_all / ε₀ + 16 * K₂ < (ℓ : ℝ) := by
    simpa only [hC_all] using hscale
  have hℓ_pos : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  obtain ⟨T, hT⟩ : ∃ T : ℕ, T = 2 ^ ℓ := ⟨_, rfl⟩
  have hT_ge256 : 256 ≤ T := by
    rw [hT]
    calc (256 : ℕ) = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right zero_lt_two (by omega)
  have hT_gt_ℓ : ℓ < T := hT ▸ Nat.lt_two_pow_self
  have hT_sq : ℓ ^ 2 < T := hT ▸ nat_sq_lt_two_pow (by omega)
  obtain ⟨B, hB⟩ : ∃ B : ℕ, B = T + 1 := ⟨_, rfl⟩
  have hB2 : 2 ≤ B := by omega
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℕ, L₀ = B.factorial := ⟨_, rfl⟩
  have hL₀_pos : 0 < L₀ := hL₀ ▸ Nat.factorial_pos B
  have hB_le_L₀ : B ≤ L₀ := hL₀ ▸ Nat.self_le_factorial B
  have hB_dvd_L₀ : B ∣ L₀ := hL₀ ▸ Nat.dvd_factorial (by omega) le_rfl
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : ℕ, j₀ = 4 * ℓ := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ,
      M = max (j₀ + 2) (Nat.ceil (24 * (2 + Real.log (L₀ : ℝ)) / ε₀) + 6) := ⟨_, rfl⟩
  have hM_j₀ : j₀ + 2 ≤ M := hM ▸ le_max_left _ _
  have hM_ceil : Nat.ceil (24 * (2 + Real.log (L₀ : ℝ)) / ε₀) + 6 ≤ M := hM ▸ le_max_right _ _
  have hM6 : 6 ≤ M := by omega
  obtain ⟨L', hL'⟩ : ∃ L' : ℕ, L' = 2 ^ M * L₀ := ⟨_, rfl⟩
  have hBL' : B < L' := by
    rw [hL']
    have h2M : 2 ≤ 2 ^ M := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ M := Nat.pow_le_pow_right zero_lt_two (by omega)
    calc B = 1 * B := (one_mul B).symm
      _ < 2 * B := Nat.mul_lt_mul_of_pos_right (by norm_num) (by omega)
      _ ≤ 2 ^ M * L₀ := Nat.mul_le_mul h2M hB_le_L₀
  rcases exists_real_lp_or_dual (ε₀ := ε₀) hB2 hBL' with ⟨x, hx1, hx2, hx3⟩ | ⟨u, hu0, hu_eq, hu_win⟩
  · refine ⟨B, L', x, ?_, ?_, hB2, hBL'.le, hx1, hx2, hx3⟩
    · omega
    · simp only [producerPeriod, hL', hL₀, hM, hj₀, hB, hT]
  · exfalso
    obtain ⟨δ_T, hδ_T⟩ : ∃ δ_T : ℝ,
        δ_T = GaloisForLFunctions.BezoutValuationIncidence.coprimeMoebiusHarmonicSum 1 T := ⟨_, rfl⟩
    have hTL' : ∀ b : ℕ, 1 ≤ b → b ≤ T + 1 → b ∣ L' := by
      intro b hb1 hbT1
      rw [hL', hL₀]
      exact dvd_mul_of_dvd_right (Nat.dvd_factorial hb1 (by omega : b ≤ B)) (2 ^ M)
    have hpair_global : ∑ r ∈ Ico 1 L', u r * moebiusResidueTest T r =
        _root_.RHTower.Sieve.moebiusLogHarmonicPartial T + δ_T * Real.log (T + 1 : ℕ) := by
      rw [hδ_T]
      exact global_pairing_moebiusResidueTest hTL' hu_eq
    obtain ⟨_, hlogB_hi_T, hL3_ge, hL4_ge, hsqrtT_ge⟩ := dyadic_log_scale_bounds hℓ10 hT
    have hδ_bound_raw :
        |GaloisForLFunctions.BezoutValuationIncidence.coprimeMoebiusHarmonicSum 1 T| ≤
          K₂ / (1 + Real.log (T : ℝ)) ^ 4 := by
      have h := hK₂ 1 one_ne_zero T (by omega)
      rwa [rankinProduct_one, mul_one] at h
    have hδ_bound : |δ_T| ≤ K₂ / (1 + Real.log (T : ℝ)) ^ 4 := hδ_T ▸ hδ_bound_raw
    have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast (by omega : 1 ≤ ℓ)
    have hδ_le_one : |δ_T| ≤ 1 := by
      have hℓ4 : (ℓ : ℝ) ≤ (ℓ : ℝ) ^ 4 := by
        calc (ℓ : ℝ) = (ℓ : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (ℓ : ℝ) ^ 4 := pow_le_pow_right₀ hℓ1 (by omega)
      calc |δ_T| ≤ K₂ / ((ℓ : ℝ) ^ 4 / 16) :=
            hδ_bound.trans (div_le_div_of_nonneg_left hK₂0 (by positivity) hL4_ge)
        _ = 16 * K₂ / (ℓ : ℝ) ^ 4 := by ring
        _ ≤ 16 * K₂ / (ℓ : ℝ) := div_le_div_of_nonneg_left (by positivity) hℓ_pos hℓ4
        _ ≤ 1 := by
            rw [div_le_one hℓ_pos]
            have : 0 ≤ 8 * C_all / ε₀ := by positivity
            linarith
    have hδ_log_le : |δ_T * Real.log (T + 1 : ℕ)| ≤ 32 * K₂ / (ℓ : ℝ) := by
      have hlog_nn : 0 ≤ Real.log (T + 1 : ℕ) :=
        Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ T + 1))
      have hℓ2_le4 : (ℓ : ℝ) ^ 2 ≤ (ℓ : ℝ) ^ 4 := pow_le_pow_right₀ hℓ1 (by omega)
      rw [abs_mul, abs_of_nonneg hlog_nn]
      calc |δ_T| * Real.log (T + 1 : ℕ)
          ≤ (K₂ / ((ℓ : ℝ) ^ 4 / 16)) * (2 * (ℓ : ℝ)) :=
            mul_le_mul (hδ_bound.trans (div_le_div_of_nonneg_left hK₂0 (by positivity) hL4_ge))
              hlogB_hi_T hlog_nn (by positivity)
        _ = 32 * K₂ * (ℓ : ℝ) / (ℓ : ℝ) ^ 4 := by ring
        _ ≤ 32 * K₂ * (ℓ : ℝ) / (ℓ : ℝ) ^ 2 :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hℓ2_le4
        _ = 32 * K₂ / (ℓ : ℝ) := by rw [sq, mul_div_mul_right _ _ hℓ_pos.ne']
    obtain ⟨η_T, hη_T⟩ : ∃ η_T : ℝ,
        η_T = K₁ / (1 + Real.log (T : ℝ)) ^ 3 + 1 / Real.sqrt (T : ℝ) +
          K₂ / (1 + Real.log (T : ℝ)) ^ 4 := ⟨_, rfl⟩
    have hF_reg1 : ∀ r : ℕ, B ≤ r → |moebiusResidueTest T r| ≤ η_T * (r : ℝ) := by
      intro r hr
      rw [hη_T]
      exact abs_moebiusResidueTest_le_tail hT_ge256 hK₁0 hK₁ hδ_bound_raw (by omega)
    have hF_unif : ∀ r : ℕ, |moebiusResidueTest T r| ≤ 3 * (T : ℝ) :=
      abs_moebiusResidueTest_le_three_mul (by omega) (hδ_T ▸ hδ_le_one)
    obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, k₀ = 2 ^ j₀ * B := ⟨_, rfl⟩
    obtain ⟨k_top, hktop⟩ : ∃ k_top : ℕ, k_top = 2 ^ (M - 1) * B := ⟨_, rfl⟩
    have hB_le_k₀ : B ≤ k₀ := by
      rw [hk₀]
      calc B = 1 * B := (one_mul B).symm
        _ ≤ 2 ^ j₀ * B := Nat.mul_le_mul_right B (Nat.one_le_pow j₀ 2 zero_lt_two)
    have hk₀_le_ktop : k₀ ≤ k_top := by
      rw [hk₀, hktop]
      exact Nat.mul_le_mul_right B (Nat.pow_le_pow_right zero_lt_two (by omega : j₀ ≤ M - 1))
    have hktop_le_L' : k_top ≤ L' := by
      rw [hktop, hL']
      exact Nat.mul_le_mul (Nat.pow_le_pow_right zero_lt_two (by omega : M - 1 ≤ M)) hB_le_L₀
    have hk₀_dvd : k₀ ∣ L' := by
      rw [hk₀, hL']
      exact mul_dvd_mul (Nat.pow_dvd_pow 2 (by omega : j₀ ≤ M)) hB_dvd_L₀
    have hReg1 : |∑ r ∈ Ico B k₀, u r * moebiusResidueTest T r| ≤
        (48 * K₁ + 54 + 96 * K₂) / (ℓ : ℝ) :=
      abs_sum_dual_reg1_le hℓ10 hT hB (by rw [hk₀, hj₀])
        (hk₀_le_ktop.trans hktop_le_L') hk₀_dvd hK₁0 hK₂0 hL3_ge hL4_ge hsqrtT_ge
        hη_T hF_reg1 hu0 hu_eq
    have hdvd_block : ∀ d : ℕ, j₀ + d + 1 ≤ M - 1 → 2 ^ (j₀ + d + 1) * B ∣ L' := by
      intro d hd
      rw [hL']
      exact mul_dvd_mul (Nat.pow_dvd_pow 2 (by omega : j₀ + d + 1 ≤ M)) hB_dvd_L₀
    have hle_block : ∀ d : ℕ, j₀ + d + 1 ≤ M - 1 → 2 ^ (j₀ + d + 1) * B ≤ L' := by
      intro d hd
      rw [hL']
      exact Nat.mul_le_mul (Nat.pow_le_pow_right zero_lt_two (by omega : j₀ + d + 1 ≤ M)) hB_le_L₀
    have hReg2 : |∑ r ∈ Ico k₀ k_top, u r * moebiusResidueTest T r| ≤ 84 / (ℓ : ℝ) :=
      abs_sum_dual_reg2_le hℓ10 hT_sq hT hB hj₀ hM_j₀ hk₀ hktop hktop_le_L'
        (hB ▸ hlogB_hi_T) hdvd_block hle_block hF_unif hu0 hu_eq
    have hReg3 : |∑ r ∈ Ico k_top L', u r * moebiusResidueTest T r| ≤ ε₀ / 8 :=
      abs_sum_dual_reg3_le hε₀ (by omega) (by omega) hL₀_pos hM6 hM_ceil hktop hL'
        hF_unif hu0 hu_eq
    have hsplit_all : ∑ r ∈ Ico 1 L', u r * moebiusResidueTest T r =
        (∑ r ∈ Ico 1 B, u r) +
          (∑ r ∈ Ico B k₀, u r * moebiusResidueTest T r) +
          (∑ r ∈ Ico k₀ k_top, u r * moebiusResidueTest T r) +
          (∑ r ∈ Ico k_top L', u r * moebiusResidueTest T r) := by
      rw [sum_Ico_split (by omega : 1 ≤ B) hBL'.le,
        sum_Ico_split hB_le_k₀ (hk₀_le_ktop.trans hktop_le_L'),
        sum_Ico_split hk₀_le_ktop hktop_le_L']
      have hmain : ∑ r ∈ Ico 1 B, u r * moebiusResidueTest T r = ∑ r ∈ Ico 1 B, u r := by
        refine sum_congr rfl fun r hr => ?_
        obtain ⟨hr1, hrB⟩ := mem_Ico.mp hr
        rw [moebiusResidueTest_eq_one hr1 (by omega : r ≤ T), mul_one]
      rw [hmain]
      ring
    have hmoeb_lt : _root_.RHTower.Sieve.moebiusLogHarmonicPartial T < 1 + ε₀ / 8 :=
      by simpa only [hT] using hnormal
    have hB_disc : (1 + ε₀) / (B : ℝ) ≤ (1 + ε₀) / (ℓ : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hℓ_pos
        (by exact_mod_cast (by omega : ℓ ≤ B))
    have hsum_err :
        |δ_T * Real.log (T + 1 : ℕ)| +
          |∑ r ∈ Ico B k₀, u r * moebiusResidueTest T r| +
          |∑ r ∈ Ico k₀ k_top, u r * moebiusResidueTest T r| +
          (1 + ε₀) / (B : ℝ) ≤ C_all / (ℓ : ℝ) := by
      calc |δ_T * Real.log (T + 1 : ℕ)| +
              |∑ r ∈ Ico B k₀, u r * moebiusResidueTest T r| +
              |∑ r ∈ Ico k₀ k_top, u r * moebiusResidueTest T r| +
              (1 + ε₀) / (B : ℝ)
          ≤ 32 * K₂ / (ℓ : ℝ) + (48 * K₁ + 54 + 96 * K₂) / (ℓ : ℝ) +
              84 / (ℓ : ℝ) + (1 + ε₀) / (ℓ : ℝ) :=
            add_le_add (add_le_add (add_le_add hδ_log_le hReg1) hReg2) hB_disc
        _ ≤ C_all / (ℓ : ℝ) := by
            rw [hC_all, ← add_div, ← add_div, ← add_div]
            exact div_le_div_of_nonneg_right (by linarith) hℓ_pos.le
    have hC_lt : C_all / (ℓ : ℝ) < ε₀ / 8 := by
      rw [div_lt_iff₀ hℓ_pos]
      have h1 : 8 * C_all / ε₀ < (ℓ : ℝ) := by linarith
      have h2 := (div_lt_iff₀ hε₀).mp h1
      linarith [show (ε₀ / 8) * (ℓ : ℝ) = ((ℓ : ℝ) * ε₀) / 8 by ring]
    have hwin_upper : ∑ r ∈ Ico 1 B, u r ≤
        _root_.RHTower.Sieve.moebiusLogHarmonicPartial T +
          |δ_T * Real.log (T + 1 : ℕ)| +
          |∑ r ∈ Ico B k₀, u r * moebiusResidueTest T r| +
          |∑ r ∈ Ico k₀ k_top, u r * moebiusResidueTest T r| +
          |∑ r ∈ Ico k_top L', u r * moebiusResidueTest T r| := by
      have h1 := le_abs_self (δ_T * Real.log (T + 1 : ℕ))
      have h2 := neg_le_abs (∑ r ∈ Ico B k₀, u r * moebiusResidueTest T r)
      have h3 := neg_le_abs (∑ r ∈ Ico k₀ k_top, u r * moebiusResidueTest T r)
      have h4 := neg_le_abs (∑ r ∈ Ico k_top L', u r * moebiusResidueTest T r)
      linarith [hpair_global, hsplit_all]
    have hdisc_eq : (1 + ε₀) * (1 - 1 / (B : ℝ)) = 1 + ε₀ - (1 + ε₀) / (B : ℝ) := by ring
    linarith

/-- **Unconditional feasibility of the real divisor LP at dyadic scales.** For every `ε₀ > 0`,
there exist `B ≥ 2` and `L' ≥ B` such that the divisor residue LP on `(Nat.divisors L').erase 1`
admits a primal solution with slope cap `(1 + ε₀)(1 - 1/B)`. -/
theorem exists_real_lp_solution {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ (B L' : ℕ) (x : ℕ → ℝ), 2 ≤ B ∧ B ≤ L' ∧
      (∑ k ∈ (Nat.divisors L').erase 1, Real.log k * x k ≤
        (1 + ε₀) * (1 - 1 / (B : ℝ))) ∧
      (∀ r ∈ Ico 1 B,
        (1 : ℝ) ≤ ∑ k ∈ (Nat.divisors L').erase 1, ((r % k : ℕ) : ℝ) * x k) ∧
      (∀ r ∈ Ico B L',
        (0 : ℝ) ≤ ∑ k ∈ (Nat.divisors L').erase 1, ((r % k : ℕ) : ℝ) * x k) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ :=
    GaloisForLFunctions.BezoutValuationIncidence.exists_abs_sum_coprime_moebius_fract_le
  obtain ⟨K₂, hK₂0, hK₂⟩ :=
    GaloisForLFunctions.BezoutValuationIncidence.exists_abs_coprimeMoebiusHarmonicSum_le_four
  have hlim := (tendsto_order.mp _root_.RHTower.Sieve.tendsto_moebiusLogHarmonicPartial_one).2
    (1 + ε₀ / 8) (by linarith)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hlim
  obtain ⟨C_all, hC_all⟩ : ∃ C_all : ℝ, C_all = 48 * K₁ + 128 * K₂ + 140 + (1 + ε₀) := ⟨_, rfl⟩
  have hC_all_pos : 0 < C_all := by rw [hC_all]; positivity
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℕ, ℓ = max (max 10 N₁) (Nat.ceil (8 * C_all / ε₀ + 16 * K₂) + 1) :=
    ⟨_, rfl⟩
  have hℓ10 : 10 ≤ ℓ := by rw [hℓ]; exact le_trans (le_max_left 10 N₁) (le_max_left _ _)
  have hℓN₁ : N₁ ≤ ℓ := by rw [hℓ]; exact le_trans (le_max_right 10 N₁) (le_max_left _ _)
  have hℓ_ceil : 8 * C_all / ε₀ + 16 * K₂ < (ℓ : ℝ) := by
    have h1 : 8 * C_all / ε₀ + 16 * K₂ ≤ Nat.ceil (8 * C_all / ε₀ + 16 * K₂) := Nat.le_ceil _
    have h2 : (Nat.ceil (8 * C_all / ε₀ + 16 * K₂) : ℝ) + 1 ≤ ℓ := by
      rw [hℓ]; exact_mod_cast le_max_right (max 10 N₁) _
    linarith
  obtain ⟨B, L', x, _, _, hB, hBL, hs, hw, hn⟩ :=
    exists_real_lp_solution_at hε₀ hK₁0 hK₂0 hK₁ hK₂ hℓ10
      (by simpa only [hC_all] using hℓ_ceil)
      (hN₁ (2 ^ ℓ) (hℓN₁.trans (Nat.lt_two_pow_self.le)))
  exact ⟨B, L', x, hB, hBL, hs, hw, hn⟩

/-- One absolute scale constant suffices for every slope excess. The alphabet is contained
in the divisors of an explicit factorial period, with dyadic exponent `O(1/ε)`. -/
theorem exists_producer_with_quantitative_support :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (c : ℕ →₀ ℤ) (m B : ℕ),
        c 0 = 0 ∧ IsBalanced c ∧ 1 ≤ m ∧ 2 ≤ B ∧
        (∀ r : ℕ, 0 ≤ stepWeight c r) ∧
        (∀ r ∈ Ico 1 B, (m : ℤ) ≤ stepWeight c r) ∧
        stencilSlope c / ((m : ℝ) * (1 - 1 / (B : ℝ))) < 1 + ε ∧
        B = 2 ^ (Nat.ceil (K / ε) + 10) + 1 ∧
        (∀ k ∈ c.support, k ∣ producerPeriod (ε / 2) (Nat.ceil (K / ε) + 10)) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ :=
    BezoutValuationIncidence.exists_abs_sum_coprime_moebius_fract_le
  obtain ⟨K₂, hK₂0, hK₂⟩ :=
    BezoutValuationIncidence.exists_abs_coprimeMoebiusHarmonicSum_le_four
  obtain ⟨K₃, hK₃0, hK₃⟩ := exists_abs_moebiusLogHarmonicPartial_sub_one_le
  let K : ℝ := 16 * (48 * K₁ + 128 * K₂ + 142) + 32 * K₂ + 128 * K₃ + 10
  have hK0 : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK0, fun ε hε hε1 => ?_⟩
  let ℓ : ℕ := Nat.ceil (K / ε) + 10
  have hℓ10 : 10 ≤ ℓ := by dsimp [ℓ]; omega
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast (by omega : 1 ≤ ℓ)
  have hscaleK : K / ε < (ℓ : ℝ) := by
    have h := Nat.le_ceil (K / ε)
    dsimp only [ℓ]
    push_cast
    linarith
  have hKε : K < (ℓ : ℝ) * ε := (div_lt_iff₀ hε).mp hscaleK
  have hscale : 8 * (48 * K₁ + 128 * K₂ + 140 + (1 + ε / 2)) / (ε / 2) +
      16 * K₂ < (ℓ : ℝ) := by
    have hK2ε : 16 * K₂ * ε ≤ 16 * K₂ :=
      mul_le_of_le_one_right (by positivity) hε1
    have hnum : 16 * (48 * K₁ + 128 * K₂ + 140 + (1 + ε / 2)) + 16 * K₂ * ε <
        (ℓ : ℝ) * ε := by
      dsimp [K] at hKε
      linarith
    have heq : 8 * (48 * K₁ + 128 * K₂ + 140 + (1 + ε / 2)) / (ε / 2) +
        16 * K₂ =
        (16 * (48 * K₁ + 128 * K₂ + 140 + (1 + ε / 2)) + 16 * K₂ * ε) / ε := by
      field_simp
      ring
    rw [heq, div_lt_iff₀ hε]
    exact hnum
  have hT3 : 3 ≤ 2 ^ ℓ := by
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right zero_lt_two (by omega)
  have hlog : (ℓ : ℝ) / 2 ≤ Real.log (2 ^ ℓ : ℕ) := by
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith [mul_le_mul_of_nonneg_left hlog2 hℓ0.le]
  have hnormal : _root_.RHTower.Sieve.moebiusLogHarmonicPartial (2 ^ ℓ) < 1 + (ε / 2) / 8 := by
    have hcube : (ℓ : ℝ) ≤ (ℓ : ℝ) ^ 3 := by
      calc (ℓ : ℝ) = (ℓ : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (ℓ : ℝ) ^ 3 := pow_le_pow_right₀ hℓ1 (by omega)
    have hlog0 : 0 < Real.log (2 ^ ℓ : ℕ) := lt_of_lt_of_le (by positivity) hlog
    have hden : (ℓ : ℝ) ^ 3 / 8 ≤ (Real.log (2 ^ ℓ : ℕ)) ^ 3 := by
      convert pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (ℓ : ℝ) / 2) hlog 3 using 1 <;> ring
    have herror : |_root_.RHTower.Sieve.moebiusLogHarmonicPartial (2 ^ ℓ) - 1| ≤
        8 * K₃ / (ℓ : ℝ) := by
      calc |_root_.RHTower.Sieve.moebiusLogHarmonicPartial (2 ^ ℓ) - 1|
          ≤ K₃ / (Real.log (2 ^ ℓ : ℕ)) ^ 3 := hK₃ _ hT3
        _ ≤ K₃ / ((ℓ : ℝ) ^ 3 / 8) :=
          div_le_div_of_nonneg_left hK₃0.le (by positivity) hden
        _ = 8 * K₃ / (ℓ : ℝ) ^ 3 := by ring
        _ ≤ 8 * K₃ / (ℓ : ℝ) := div_le_div_of_nonneg_left (by positivity) hℓ0 hcube
    have hsmall : 8 * K₃ / (ℓ : ℝ) < ε / 16 := by
      rw [div_lt_iff₀ hℓ0]
      dsimp [K] at hKε
      nlinarith
    have := (abs_le.mp herror).2
    linarith
  obtain ⟨B, L', x, hB, hL, hB2, hBL, hs, hw, hn⟩ :=
    exists_real_lp_solution_at (by linarith : 0 < ε / 2) hK₁0 hK₂0 hK₁ hK₂
      hℓ10 hscale hnormal
  obtain ⟨c, m, hc0, hbal, hm, hnonneg, hwin, hslope, hsupp⟩ :=
    exists_stencil_of_real_lp_with_support hB2 hBL (by linarith : 0 < ε / 2) hs hw hn
  refine ⟨c, m, B, hc0, hbal, hm, hB2, hnonneg, hwin, ?_, hB, ?_⟩
  · linarith
  · simpa only [hL] using hsupp

/-! ### Main theorems and corollaries -/

/-- **Main Producer Theorem.** For every `ε > 0`, there exists a balanced, parity-selective
(sign-alternating on `k ≥ 2`) integer Hecke–factorial stencil `(c, m, B)` whose factorial quotient
is an exact integer for every `n`, vanishes to order at least `m` at every prime in `(n/B, n]`,
and achieves normalized exponential slope strictly below `1 + ε`. -/
theorem exists_multivariate_parity_producer {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : ℕ →₀ ℤ) (m B : ℕ),
      c 0 = 0 ∧
      IsBalanced c ∧
      ((∃ k₁ : ℕ, 2 ≤ k₁ ∧ 0 < c k₁) ∧ (∃ k₂ : ℕ, 2 ≤ k₂ ∧ c k₂ < 0)) ∧
      1 ≤ m ∧
      2 ≤ B ∧
      (∀ n : ℕ, stencilDen c n ∣ stencilNum c n) ∧
      (∀ r : ℕ, 0 ≤ stepWeight c r) ∧
      (∀ r ∈ Ico 1 B, (m : ℤ) ≤ stepWeight c r) ∧
      stencilSlope c / ((m : ℝ) * (1 - 1 / (B : ℝ))) < 1 + ε := by
  set ε' : ℝ := min ε (1 / 30)
  have hε'_pos : 0 < ε' := lt_min hε (by norm_num)
  have hε'_le_ε : ε' ≤ ε := min_le_left _ _
  have hε'_le_30 : ε' ≤ 1 / 30 := min_le_right _ _
  obtain ⟨B, L', x, hB2, hBL', hx1, hx2, hx3⟩ :=
    exists_real_lp_solution (ε₀ := ε' / 2) (by linarith)
  obtain ⟨c, m, hc0, hbal, hm1, hstep, hwin, hslope⟩ :=
    exists_stencil_of_real_lp hB2 hBL' (by linarith : 0 < ε' / 2) hx1 hx2 hx3
  have hslope' : stencilSlope c / ((m : ℝ) * (1 - 1 / (B : ℝ))) < 1 + ε' := by
    linarith
  have hsign : (∃ k₁ : ℕ, 2 ≤ k₁ ∧ 0 < c k₁) ∧ (∃ k₂ : ℕ, 2 ≤ k₂ ∧ c k₂ < 0) :=
    exists_sign_alternation_of_slope_le hc0 hbal hm1 hB2 hwin (by linarith)
  have hdvd : ∀ n : ℕ, stencilDen c n ∣ stencilNum c n :=
    stencilDen_dvd_stencilNum_of_nonneg hstep
  exact ⟨c, m, B, hc0, hbal, hsign, hm1, hB2, hdvd, hstep, hwin, by linarith⟩

/-- **Multivariate Prime-Hecke Polynomial Producer.** For every `ε > 0`, there exists a multivariate
integer polynomial `Q ∈ MvPolynomial PrimeVar ℤ` with both positive and negative nontrivial
monomial coefficients (`s₁, s₂ ≠ 0`) whose associated factorial stencil `(mvPolyToStencil Q, m, B)`
is integer-valued and reaches normalized vanishing-order slope `< 1 + ε`. -/
theorem exists_mvPolynomial_parity_producer {ε : ℝ} (hε : 0 < ε) :
    ∃ (Q : MvPolynomial PrimeVar ℤ) (m B : ℕ),
      IsBalanced (mvPolyToStencil Q) ∧
      ((∃ s₁ : PrimeVar →₀ ℕ, s₁ ≠ 0 ∧ 0 < Q.coeff s₁) ∧
        (∃ s₂ : PrimeVar →₀ ℕ, s₂ ≠ 0 ∧ Q.coeff s₂ < 0)) ∧
      1 ≤ m ∧
      2 ≤ B ∧
      (∀ n : ℕ, stencilDen (mvPolyToStencil Q) n ∣ stencilNum (mvPolyToStencil Q) n) ∧
      (∀ r : ℕ, 0 ≤ stepWeight (mvPolyToStencil Q) r) ∧
      (∀ r ∈ Ico 1 B, (m : ℤ) ≤ stepWeight (mvPolyToStencil Q) r) ∧
      stencilSlope (mvPolyToStencil Q) / ((m : ℝ) * (1 - 1 / (B : ℝ))) < 1 + ε := by
  obtain ⟨c, m, B, hc0, hbal, ⟨⟨k₁, hk₁, hck₁⟩, ⟨k₂, hk₂, hck₂⟩⟩, hm1, hB2, hdvd, hstep, hwin,
      hslope⟩ := exists_multivariate_parity_producer hε
  set Q := stencilToMvPoly c
  have hQc : mvPolyToStencil Q = c := mvPolyToStencil_stencilToMvPoly hc0
  have hs₁_ne : divisorMonomial k₁ ≠ 0 := by
    intro h0
    have := congrArg heckeDivisor h0
    rw [heckeDivisor_divisorMonomial (by omega), heckeDivisor, Finsupp.prod_zero_index] at this
    omega
  have hs₂_ne : divisorMonomial k₂ ≠ 0 := by
    intro h0
    have := congrArg heckeDivisor h0
    rw [heckeDivisor_divisorMonomial (by omega), heckeDivisor, Finsupp.prod_zero_index] at this
    omega
  have hQ₁ : Q.coeff (divisorMonomial k₁) = c k₁ := by
    rw [← mvPolyToStencil_apply_heckeDivisor Q (divisorMonomial k₁), hQc,
      heckeDivisor_divisorMonomial (by omega)]
  have hQ₂ : Q.coeff (divisorMonomial k₂) = c k₂ := by
    rw [← mvPolyToStencil_apply_heckeDivisor Q (divisorMonomial k₂), hQc,
      heckeDivisor_divisorMonomial (by omega)]
  refine ⟨Q, m, B, hQc.symm ▸ hbal,
    ⟨⟨divisorMonomial k₁, hs₁_ne, hQ₁ ▸ hck₁⟩, ⟨divisorMonomial k₂, hs₂_ne, hQ₂ ▸ hck₂⟩⟩,
    hm1, hB2, hQc.symm ▸ hdvd, hQc.symm ▸ hstep, hQc.symm ▸ hwin, hQc.symm ▸ hslope⟩

/-- **Prime Number Theorem Upper Bound for `ψ` via Vanishing Order.** Multivariate parity-selective
integer auxiliaries unconditionally yield `ψ(x) ≤ (1 + ε) x + C (log x)²` for every `ε > 0` and all
`x ≥ 2` by `p`-adic factorial valuation arguments alone. -/
theorem psi_le_one_add_eps_of_vanishing_order {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      Chebyshev.psi x ≤ (1 + ε) * x + C * (Real.log x) ^ 2 := by
  obtain ⟨c, m, B, hc0, hbal, _, hm1, hB2, _, hstep, hwin, hslope⟩ :=
    exists_multivariate_parity_producer hε
  obtain ⟨C, hC, hpsi⟩ := psi_le_of_stepWeight_producer hc0 hbal hstep hm1 hB2 hwin
  refine ⟨C, hC, fun x hx => (hpsi x hx).trans ?_⟩
  have hmul := mul_le_mul_of_nonneg_right hslope.le (by linarith : (0 : ℝ) ≤ x)
  linarith

/-- **Prime Number Theorem Upper Bound for `θ` via Vanishing Order.** Multivariate parity-selective
integer auxiliaries unconditionally yield `θ(x) ≤ (1 + ε) x + C (log x)²` for every `ε > 0` and all
`x ≥ 2`. -/
theorem theta_le_one_add_eps_of_vanishing_order {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      Chebyshev.theta x ≤ (1 + ε) * x + C * (Real.log x) ^ 2 := by
  obtain ⟨C, hC, hpsi⟩ := psi_le_one_add_eps_of_vanishing_order hε
  exact ⟨C, hC, fun x hx => (Chebyshev.theta_le_psi x).trans (hpsi x hx)⟩

/-- Set of normalized vanishing-order slopes achieved by all balanced integer Hecke–factorial
producers `(c, m, B)`. -/
def ProducerSlopeSet : Set ℝ :=
  {s : ℝ | ∃ (c : ℕ →₀ ℤ) (m B : ℕ),
    c 0 = 0 ∧ IsBalanced c ∧ (∀ r : ℕ, 0 ≤ stepWeight c r) ∧
    1 ≤ m ∧ 2 ≤ B ∧ (∀ r ∈ Ico 1 B, (m : ℤ) ≤ stepWeight c r) ∧
    s = stencilSlope c / ((m : ℝ) * (1 - 1 / (B : ℝ)))}

/-- **Sharp Infimum Law (`inf = 1`).** The greatest lower bound of normalized vanishing-order
slopes over all balanced integer Hecke–factorial producers is exactly `1`. -/
theorem isGLB_producerSlopeSet : IsGLB ProducerSlopeSet 1 := by
  refine ⟨?_, ?_⟩
  · rintro s ⟨c, m, B, hc0, hbal, hstep, hm1, hB2, hwin, rfl⟩
    exact (one_lt_normalized_slope_of_producer hc0 hbal hstep hm1 hB2 hwin).le
  · intro y hy
    by_contra! hgt
    obtain ⟨c, m, B, hc0, hbal, _, hm1, hB2, _, hstep, hwin, hslope⟩ :=
      exists_multivariate_parity_producer (ε := (y - 1) / 2) (by linarith)
    have hmem : stencilSlope c / ((m : ℝ) * (1 - 1 / (B : ℝ))) ∈ ProducerSlopeSet :=
      ⟨c, m, B, hc0, hbal, hstep, hm1, hB2, hwin, rfl⟩
    have hge := hy hmem
    linarith

/-- **Strict Non-Attainment Law (`1 ∉ ProducerSlopeSet`).** Although `inf ProducerSlopeSet = 1`,
no single finite-support integer stencil ever attains normalized slope `1`. -/
theorem one_notMem_producerSlopeSet : (1 : ℝ) ∉ ProducerSlopeSet := by
  rintro ⟨c, m, B, hc0, hbal, hstep, hm1, hB2, hwin, heq⟩
  have hgt := one_lt_normalized_slope_of_producer hc0 hbal hstep hm1 hB2 hwin
  linarith

/-- **Infinite-Prime Escape Corollary.** For every finite set `S` of primes, there exists a
parity-selective integer producer `(c, m, B)` whose normalized slope lies strictly below the
`S`-alphabet floor `1 + 1 / ((P_S + 1)(P_S + 2))` and whose prime support strictly escapes `S`. -/
theorem exists_producer_escaping_prime_finset {S : Finset ℕ} (hSp : ∀ p ∈ S, p.Prime) :
    ∃ (c : ℕ →₀ ℤ) (m B : ℕ),
      c 0 = 0 ∧ IsBalanced c ∧
      ((∃ k₁ : ℕ, 2 ≤ k₁ ∧ 0 < c k₁) ∧ (∃ k₂ : ℕ, 2 ≤ k₂ ∧ c k₂ < 0)) ∧
      1 ≤ m ∧ 2 ≤ B ∧
      (∀ r : ℕ, 0 ≤ stepWeight c r) ∧
      (∀ r ∈ Ico 1 B, (m : ℤ) ≤ stepWeight c r) ∧
      stencilSlope c / ((m : ℝ) * (1 - 1 / (B : ℝ))) <
        1 + 1 / (((∏ p ∈ S, p : ℕ) : ℝ) + 1) / (((∏ p ∈ S, p : ℕ) : ℝ) + 2) ∧
      ¬ IsPrimeAlphabetSupported S c := by
  set ε_S : ℝ := 1 / (((∏ p ∈ S, p : ℕ) : ℝ) + 1) / (((∏ p ∈ S, p : ℕ) : ℝ) + 2)
  have hε_pos : 0 < ε_S := by positivity
  obtain ⟨c, m, B, hc0, hbal, hsign, hm1, hB2, _, hstep, hwin, hslope⟩ :=
    exists_multivariate_parity_producer hε_pos
  refine ⟨c, m, B, hc0, hbal, hsign, hm1, hB2, hstep, hwin, hslope, ?_⟩
  intro hsupp
  have hgt := finite_prime_alphabet_slope_gt_one hSp hc0 hbal hsupp hstep hm1 hB2 hwin
  linarith

/-- **Complete Structural Resolution of the Multivariate Parity Auxiliary Question.**
Unconditionally establishes the affirmative answer together with the sharp hierarchy of restricted
obstructions:
1. Univariate integer polynomials of degree `≤ n` (`n ≥ 1`) satisfy
   `sup_{t ∈ [0,1]} |P(t)| > exp(-(87/100) n)`;
2. Single-prime Hecke producers satisfy normalized slope `≥ 2 log 2`;
3. `S`-supported finite-prime producers satisfy normalized slope `> 1 + 1 / ((P_S + 1)(P_S + 2))`;
4. Parity-blind (`c(k) ≤ 0` for `k ≥ 2`) producers satisfy normalized slope `> 31 / 30`;
5. Multivariate, parity-selective integer producers reach `< 1 + ε` and yield
   `ψ(x) ≤ (1 + ε) x + C (log x)²` for every `ε > 0`, with `inf ProducerSlopeSet = 1` and
   `1 ∉ ProducerSlopeSet`. -/
theorem multivariate_parity_resolution_of_chebyshev_ceiling :
    (∀ (P : ℤ[X]) {n : ℕ}, P ≠ 0 → 1 ≤ n → P.natDegree ≤ n →
      ∃ t ∈ Set.Icc (0 : ℝ) 1, Real.exp (-(87 / 100 : ℝ) * n) < |Polynomial.aeval t P|) ∧
    (∀ {c : ℕ →₀ ℤ} {p₀ K m R : ℕ}, p₀.Prime → IsBalanced c →
      (∀ k ∈ c.support, ∃ j ≤ K, k = p₀ ^ j) → (∀ r : ℕ, 0 ≤ stepWeight c r) →
      1 ≤ m → 1 ≤ R → (∀ r < R, (m : ℤ) ≤ stepWeight c (p₀ ^ r)) →
      2 * Real.log 2 ≤ stencilSlope c / ((m : ℝ) * (1 - 1 / (p₀ : ℝ) ^ R))) ∧
    (∀ {S : Finset ℕ}, (∀ p ∈ S, p.Prime) → ∀ {c : ℕ →₀ ℤ} {m B : ℕ},
      c 0 = 0 → IsBalanced c → IsPrimeAlphabetSupported S c →
      (∀ r : ℕ, 0 ≤ stepWeight c r) → 1 ≤ m → 2 ≤ B →
      (∀ r ∈ Ico 1 B, (m : ℤ) ≤ stepWeight c r) →
      1 + 1 / (((∏ p ∈ S, p : ℕ) : ℝ) + 1) / (((∏ p ∈ S, p : ℕ) : ℝ) + 2) <
        stencilSlope c / ((m : ℝ) * (1 - 1 / (B : ℝ)))) ∧
    (∀ {c : ℕ →₀ ℤ} {m B : ℕ}, c 0 = 0 → IsBalanced c → (∀ k : ℕ, 2 ≤ k → c k ≤ 0) →
      1 ≤ m → 2 ≤ B → (∀ r ∈ Ico 1 B, (m : ℤ) ≤ stepWeight c r) →
      (31 / 30 : ℝ) < stencilSlope c / ((m : ℝ) * (1 - 1 / (B : ℝ)))) ∧
    IsGLB ProducerSlopeSet 1 ∧
    (1 : ℝ) ∉ ProducerSlopeSet ∧
    (∀ {ε : ℝ}, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      Chebyshev.psi x ≤ (1 + ε) * x + C * (Real.log x) ^ 2) :=
  ⟨exists_Icc_gt_univariate_chebyshev_cap,
   single_prime_hecke_slope_ge_two_log_two,
   finite_prime_alphabet_slope_gt_one,
   non_alternating_stencil_slope_gt,
   isGLB_producerSlopeSet,
   one_notMem_producerSlopeSet,
   psi_le_one_add_eps_of_vanishing_order⟩

end GaloisForLFunctions.ArithmeticKreinLangerTheory
