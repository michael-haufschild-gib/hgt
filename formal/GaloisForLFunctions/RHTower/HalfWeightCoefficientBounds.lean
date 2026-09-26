import GaloisForLFunctions.RHTower.HalfWeightCoefficientContinuation

/-!
# Polynomial bounds for the Eisenstein coefficient factors

* `rootCard_le_two_pow`: `N_{p^a}(n) ≤ 2 p^{v_p(4n)}` (two square roots agree up to sign modulo
  `p^{a - v_p(4n)}`, `pm_classes`); hence `‖e_T(p^a)‖ ≤ 4 p^{v_p(4n)}` (`norm_eT_prime_pow_le'`) and the
  local factor `Σ_a ‖e_T(p^a)‖ p^{-aσ} ≤ 4 p^{v_p(4n)}/(1 - 2^{-σ})` (`tsum_eMaj_prime_pow_le`).
* `pow_card_primeFactors_le`: `B^{ω(N)} ≤ N^{log₂ B}` (since `2^{ω(N)} ≤ ∏_{p∣N} p ≤ N`);
  `prod_pow_padicValNat_le`: `∏_{p ∈ T} p^{v_p(m)} ≤ m`.
* `tsum_eMaj_le`, `norm_LSeries_eL_le`: `‖L(e_L, s)‖ ≤ 4|n| (4|n|M)^{β(Re s)}` for `Re s > 0`,
  `β(σ) = log₂(4/(1-2^{-σ}))` — polynomial in `n` (the Euler product over the finite set `T`).
* `norm_prod_one_sub_le`, `norm_eulerFin_le`: `‖∏_{p∣N}(1 - c_p p^{-s})‖ ≤ N` for `Re s ≥ 0`, `|c_p| ≤ 1`;
  `norm_eulerFin_inv_le`: `‖∏_{p∣N}(1-p^{-u})‖⁻¹ ≤ N^{γ(Re u)}`, `γ(σ) = log₂(1/(1-2^{-σ}))`.
* `betaE_anti`, `gammaE_anti`, `cst_anti`: the exponents and the kernel constant decrease in `σ`,
  so all bounds are uniform on compact sets of the spectral parameter.
-/

open Real Complex ArithmeticFunction Filter Topology

namespace GaloisForLFunctions.RHTower.HalfWeight

noncomputable section

/-! ### Local root counts bounded by the `p`-part of `4n` -/

section RootBound3

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Sharper root count**: `N_{p^a}(n) ≤ 2 p^{v_p(4n)}` for `n ≠ 0`. -/
theorem rootCard_le_two_pow {n : ℤ} (hn : n ≠ 0) (a : ℕ) [NeZero (p ^ a)] :
    rootCard n (p ^ a) ≤ 2 * p ^ padicValNat p (4 * n.natAbs) := by
  set e := padicValNat p (4 * n.natAbs) with he
  rw [rootCard_eq_card_range]
  by_cases hae : a ≤ e
  · calc _ ≤ (Finset.range (p ^ a)).card := Finset.card_filter_le _ _
      _ = p ^ a := Finset.card_range _
      _ ≤ p ^ e := Nat.pow_le_pow_right hp.out.pos hae
      _ ≤ 2 * p ^ e := by omega
  push Not at hae
  set F := (Finset.range (p ^ a)).filter fun m : ℕ => ((p ^ a : ℕ) : ℤ) ∣ n - (m : ℤ) ^ 2
  rcases F.eq_empty_or_nonempty with hF | ⟨m₀, hm₀⟩
  · rw [hF]; simp
  set q := p ^ (a - e)
  have hpa : p ^ a = p ^ e * q := by rw [← pow_add]; congr 1; omega
  set A := (Finset.range (p ^ e * q)).filter fun m : ℕ => (q : ℤ) ∣ (m₀ : ℤ) - m
  set B := (Finset.range (p ^ e * q)).filter fun m : ℕ => (q : ℤ) ∣ (-(m₀ : ℤ)) - m
  have hsub : F ⊆ A ∪ B := by
    intro m hm
    simp only [F, Finset.mem_filter, Finset.mem_range] at hm hm₀
    have hX : (p : ℤ) ^ a ∣ (m₀ : ℤ) ^ 2 - n := by
      have := hm₀.2; push_cast at this; rw [← neg_sub]; exact (dvd_neg).2 this
    have hY : (p : ℤ) ^ a ∣ (m : ℤ) ^ 2 - n := by
      have := hm.2; push_cast at this; rw [← neg_sub]; exact (dvd_neg).2 this
    have hmr : m < p ^ e * q := hpa ▸ hm.1
    rcases pm_classes hn hX hY with h | h
    · refine Finset.mem_union_left _ ?_
      simp only [A, Finset.mem_filter, Finset.mem_range]
      exact ⟨hmr, by push_cast [q]; exact h⟩
    · refine Finset.mem_union_right _ ?_
      simp only [B, Finset.mem_filter, Finset.mem_range]
      refine ⟨hmr, ?_⟩
      have : (q : ℤ) ∣ -((m₀ : ℤ) + m) := (dvd_neg).2 (by push_cast [q]; exact h)
      rw [show -(m₀ : ℤ) - m = -((m₀ : ℤ) + m) by ring]; exact this
  calc F.card ≤ (A ∪ B).card := Finset.card_le_card hsub
    _ ≤ A.card + B.card := Finset.card_union_le _ _
    _ ≤ p ^ e + p ^ e := add_le_add (card_class_le q _ _) (card_class_le q _ _)
    _ = 2 * p ^ e := by ring

end RootBound3

section FactoredBound

variable {n : ℤ} {M : ℕ} (hn : n ≠ 0)

include hn in
theorem norm_sqCount_prime_pow_le' {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ‖sqCount n (p ^ a)‖ ≤ 2 * (p : ℝ) ^ padicValNat p (4 * n.natAbs) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [sqCount_eq_rootCard, Complex.norm_natCast]
  exact_mod_cast rootCard_le_two_pow hn a

include hn in
/-- `‖e_T(p^a)‖ ≤ 4 p^{v_p(4n)}`. -/
theorem norm_eT_prime_pow_le' {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ‖eT (n := n) (M := M) (p ^ a)‖ ≤ 4 * (p : ℝ) ^ padicValNat p (4 * n.natAbs) := by
  have h1 : (1 : ℝ) ≤ (p : ℝ) ^ padicValNat p (4 * n.natAbs) :=
    one_le_pow₀ (by exact_mod_cast hp.one_lt.le)
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [pow_zero, (isMultiplicative_eT (n := n) (M := M)).map_one, norm_one]; linarith
  rw [eT_apply]
  split_ifs
  · rw [fN, moebius_mul_prime_pow _ hp ha, Nfun_apply, Nfun_apply]
    refine (norm_sub_le _ _).trans ?_
    have := norm_sqCount_prime_pow_le' hn hp a
    have := norm_sqCount_prime_pow_le' hn hp (a - 1)
    linarith
  · simp

theorem one_sub_two_rpow_pos {σ : ℝ} (hσ : 0 < σ) : 0 < 1 - (2 : ℝ) ^ (-σ) := by
  have : (2 : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  linarith

include hn in
/-- The local factor: `Σ_a ‖e_T(p^a)‖ p^{-aσ} ≤ 4 p^{v_p(4n)} / (1 - 2^{-σ})`. -/
theorem tsum_eMaj_prime_pow_le {σ : ℝ} (hσ : 0 < σ) {p : ℕ} (hp : p.Prime) :
    ∑' a : ℕ, eMaj (n := n) (M := M) σ (p ^ a) ≤
      4 * (p : ℝ) ^ padicValNat p (4 * n.natAbs) / (1 - (2 : ℝ) ^ (-σ)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  set r : ℝ := (p : ℝ) ^ (-σ)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hr2 : r ≤ (2 : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (by linarith)
  set C := 4 * (p : ℝ) ^ padicValNat p (4 * n.natAbs)
  have hC : 0 ≤ C := by positivity
  have hterm : ∀ a : ℕ, eMaj (n := n) (M := M) σ (p ^ a) ≤ C * r ^ a := by
    intro a
    rw [eMaj, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
      mul_comm (a : ℝ) (-σ), Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_right (norm_eT_prime_pow_le' hn hp a) (by positivity)
  have hgeo := (summable_geometric_of_lt_one hr0 hr1).mul_left C
  have hsum : Summable fun a : ℕ => eMaj (n := n) (M := M) σ (p ^ a) :=
    Summable.of_nonneg_of_le (fun a => by unfold eMaj; positivity) hterm hgeo
  calc ∑' a : ℕ, eMaj (n := n) (M := M) σ (p ^ a) ≤ ∑' a : ℕ, C * r ^ a :=
        hsum.tsum_le_tsum hterm hgeo
    _ = C / (1 - r) := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]
    _ ≤ C / (1 - (2 : ℝ) ^ (-σ)) :=
        div_le_div_of_nonneg_left hC (one_sub_two_rpow_pos hσ) (by linarith)

end FactoredBound


/-! ### Counting prime factors -/

/-- `B^{ω(N)} ≤ N^{log₂ B}` for `B ≥ 1`, `N ≠ 0`. -/
theorem pow_card_primeFactors_le {N : ℕ} (hN : N ≠ 0) {B : ℝ} (hB : 1 ≤ B) :
    B ^ N.primeFactors.card ≤ (N : ℝ) ^ Real.logb 2 B := by
  have h2 : (2 : ℕ) ^ N.primeFactors.card ≤ N := by
    refine (Finset.pow_card_le_prod _ _ 2 fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le).trans ?_
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (Nat.prod_primeFactors_dvd N)
  have h2' : (2 : ℝ) ^ N.primeFactors.card ≤ N := by exact_mod_cast h2
  have hl : 0 ≤ Real.logb 2 B := Real.logb_nonneg (by norm_num) hB
  calc B ^ N.primeFactors.card = ((2 : ℝ) ^ Real.logb 2 B) ^ N.primeFactors.card := by
        rw [Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]
    _ = ((2 : ℝ) ^ N.primeFactors.card) ^ Real.logb 2 B := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num), mul_comm]
    _ ≤ (N : ℝ) ^ Real.logb 2 B := Real.rpow_le_rpow (by positivity) h2' hl

/-- `∏_{p ∈ T} p^{v_p(m)} ≤ m` whenever the set of primes `T` contains the prime factors of `m ≠ 0`. -/
theorem prod_pow_padicValNat_le {m : ℕ} (hm : m ≠ 0) {T : Finset ℕ} (hTp : ∀ p ∈ T, p.Prime)
    (hT : m.primeFactors ⊆ T) : ∏ p ∈ T, (p : ℝ) ^ padicValNat p m ≤ m := by
  have e1 : ∏ p ∈ T, (p : ℝ) ^ padicValNat p m = ∏ p ∈ m.primeFactors, (p : ℝ) ^ padicValNat p m := by
    refine (Finset.prod_subset hT fun p hpT hp => ?_).symm
    have hnd : ¬ p ∣ m := fun hd => hp (Nat.mem_primeFactors.2 ⟨hTp p hpT, hd, hm⟩)
    rw [padicValNat.eq_zero_of_not_dvd hnd, pow_zero]
  rw [e1]
  have e2 : ∏ p ∈ m.primeFactors, (p : ℝ) ^ padicValNat p m =
      ((m.factorization.prod fun p k => p ^ k : ℕ) : ℝ) := by
    rw [Nat.prod_factorization_eq_prod_primeFactors]
    push_cast
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.factorization_def m (Nat.prime_of_mem_primeFactors hp)]
  rw [e2, Nat.prod_factorization_pow_eq_self hm]


/-! ### The factored series is polynomially bounded in `n` -/

section FactoredSeries

variable {n : ℤ} {M : ℕ} (hn : n ≠ 0) (hM : 0 < M)

/-- The exponent `β(σ) = log₂(4/(1 - 2^{-σ}))`. -/
def betaE (σ : ℝ) : ℝ := Real.logb 2 (4 / (1 - (2 : ℝ) ^ (-σ)))

include hn hM in
/-- `Σ_c ‖e_T(c)‖ c^{-σ} ≤ 4|n| · (4|n|M)^{β(σ)}`. -/
theorem tsum_eMaj_le {σ : ℝ} (hσ : 0 < σ) :
    ∑' c : ℕ, eMaj (n := n) (M := M) σ c ≤ 4 * n.natAbs * (kmod n M : ℝ) ^ betaE σ := by
  have hmulT := isMultiplicative_eT (n := n) (M := M)
  have h1 : eMaj (n := n) (M := M) σ 1 = 1 := by simp [eMaj, hmulT.map_one]
  have hmul : ∀ {a b : ℕ}, a.Coprime b →
      eMaj (n := n) (M := M) σ (a * b) = eMaj (n := n) (M := M) σ a * eMaj (n := n) (M := M) σ b := by
    intro a b hab
    simp only [eMaj, hmulT.map_mul_of_coprime hab, norm_mul, Nat.cast_mul]
    rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
  have hsum : ∀ {p : ℕ}, p.Prime → Summable fun a : ℕ => ‖eMaj (n := n) (M := M) σ (p ^ a)‖ := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    set r : ℝ := (p : ℝ) ^ (-σ)
    have hr0 : 0 ≤ r := by positivity
    have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    refine Summable.of_nonneg_of_le (fun a => norm_nonneg _) (fun a => ?_)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left (16 * (n.natAbs : ℝ)))
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold eMaj; positivity), eMaj, Nat.cast_pow,
      ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm (a : ℝ) (-σ),
      Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_right (norm_eT_prime_pow_le hn hp a) (by positivity)
  have hE := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum h1 hmul
    hsum (Tset (n := n) (M := M))).2
  have hsupp : Function.support (eMaj (n := n) (M := M) σ) ⊆ Nat.factoredNumbers (Tset (n := n) (M := M)) := by
    intro c hc
    by_contra hnc
    exact hc (by simp [eMaj, eT_apply, hnc])
  have hprime : ∀ p ∈ Tset (n := n) (M := M), p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hfilt : (Tset (n := n) (M := M)).filter Nat.Prime = Tset (n := n) (M := M) :=
    Finset.filter_true_of_mem hprime
  rw [← tsum_subtype_eq_of_support_subset hsupp, hE.tsum_eq, hfilt]
  set B : ℝ := 4 / (1 - (2 : ℝ) ^ (-σ))
  have hB : 1 ≤ B := by
    have h0 := one_sub_two_rpow_pos hσ
    have : 1 - (2 : ℝ) ^ (-σ) ≤ 1 := by have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (-σ); linarith
    rw [le_div_iff₀ h0]; linarith
  calc ∏ p ∈ Tset (n := n) (M := M), ∑' a : ℕ, eMaj (n := n) (M := M) σ (p ^ a)
      ≤ ∏ p ∈ Tset (n := n) (M := M), (B * (p : ℝ) ^ padicValNat p (4 * n.natAbs)) := by
        refine Finset.prod_le_prod (fun p _ => tsum_nonneg fun a => by unfold eMaj; positivity)
          fun p hp => ?_
        refine (tsum_eMaj_prime_pow_le hn hσ (hprime p hp)).trans (le_of_eq ?_)
        simp only [B]; ring
    _ = B ^ (Tset (n := n) (M := M)).card *
          ∏ p ∈ Tset (n := n) (M := M), (p : ℝ) ^ padicValNat p (4 * n.natAbs) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ ≤ (kmod n M : ℝ) ^ betaE σ * (4 * n.natAbs : ℕ) := by
        refine mul_le_mul (pow_card_primeFactors_le (kmod_pos hn hM).ne' hB) ?_ (by positivity)
          (by positivity)
        refine prod_pow_padicValNat_le (by positivity) hprime ?_
        exact Nat.primeFactors_mono (dvd_mul_right _ _) (kmod_pos hn hM).ne'
    _ = 4 * n.natAbs * (kmod n M : ℝ) ^ betaE σ := by push_cast; ring

include hn hM in
/-- **`‖L(e_L, s)‖ ≤ 4|n| (4|n|M)^{β(Re s)}`** for `Re s > 0`. -/
theorem norm_LSeries_eL_le {s : ℂ} (hs : 0 < s.re) :
    ‖LSeries (fun c => eL (n := n) (M := M) c) s‖ ≤ 4 * n.natAbs * (kmod n M : ℝ) ^ betaE s.re := by
  have hm := summable_eMaj (n := n) (M := M) hn hs
  have hb : ∀ c, ‖LSeries.term (fun c => eL (n := n) (M := M) c) s c‖ ≤ eMaj (n := n) (M := M) s.re c := by
    intro c
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp [LSeries.term_def, eMaj]
    rw [LSeries.term_of_ne_zero hc.ne', norm_div, Complex.norm_natCast_cpow_of_pos hc, eMaj,
      Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [eL_apply]
    split_ifs
    · exact le_rfl
    · simp
  have hsn : Summable fun c => ‖LSeries.term (fun c => eL (n := n) (M := M) c) s c‖ :=
    Summable.of_nonneg_of_le (fun c => norm_nonneg _) hb hm
  calc ‖LSeries (fun c => eL (n := n) (M := M) c) s‖
      ≤ ∑' c, ‖LSeries.term (fun c => eL (n := n) (M := M) c) s c‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' c, eMaj (n := n) (M := M) s.re c := hsn.tsum_le_tsum hb hm
    _ ≤ _ := tsum_eMaj_le hn hM hs

end FactoredSeries


/-! ### Finite Euler factors -/

theorem norm_one_sub_prime_cpow_le {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 ≤ s.re) (c : ℂ)
    (hc : ‖c‖ ≤ 1) : ‖1 - c * (p : ℂ) ^ (-s)‖ ≤ 2 := by
  have h1 : ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp.one_lt.le) (by simp; linarith)
  calc ‖1 - c * (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖c * (p : ℂ) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ 1 + 1 * 1 := by rw [norm_one, norm_mul]; gcongr
    _ = 2 := by norm_num

/-- `‖∏_{p∣N}(1 - c_p p^{-s})‖ ≤ N` for `Re s ≥ 0`, `|c_p| ≤ 1`. -/
theorem norm_prod_one_sub_le {N : ℕ} (hN : N ≠ 0) {s : ℂ} (hs : 0 ≤ s.re) (c : ℕ → ℂ)
    (hc : ∀ p, ‖c p‖ ≤ 1) : ‖∏ p ∈ N.primeFactors, (1 - c p * (p : ℂ) ^ (-s))‖ ≤ N := by
  rw [norm_prod]
  calc ∏ p ∈ N.primeFactors, ‖1 - c p * (p : ℂ) ^ (-s)‖ ≤ ∏ p ∈ N.primeFactors, (2 : ℝ) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p hp =>
          norm_one_sub_prime_cpow_le (Nat.prime_of_mem_primeFactors hp) hs _ (hc p)
    _ = 2 ^ N.primeFactors.card := Finset.prod_const _
    _ ≤ N := by
        have h2 : (2 : ℕ) ^ N.primeFactors.card ≤ N :=
          (Finset.pow_card_le_prod _ _ 2 fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le).trans
            (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (Nat.prod_primeFactors_dvd N))
        exact_mod_cast h2

theorem norm_eulerFin_le {N : ℕ} (hN : N ≠ 0) {s : ℂ} (hs : 0 ≤ s.re) : ‖eulerFin N s‖ ≤ N := by
  have := norm_prod_one_sub_le hN hs (fun _ => 1) (fun _ => by simp)
  simpa [eulerFin] using this

/-- The exponent `γ(σ) = log₂(1/(1 - 2^{-σ}))`. -/
def gammaE (σ : ℝ) : ℝ := Real.logb 2 (1 / (1 - (2 : ℝ) ^ (-σ)))

/-- `‖∏_{p∣N}(1 - p^{-u})‖⁻¹ ≤ N^{γ(Re u)}` for `Re u > 0`. -/
theorem norm_eulerFin_inv_le {N : ℕ} (hN : N ≠ 0) {u : ℂ} (hu : 0 < u.re) :
    ‖(eulerFin N u)⁻¹‖ ≤ (N : ℝ) ^ gammaE u.re := by
  set σ := u.re
  have h0 := one_sub_two_rpow_pos hu
  have hloc : ∀ p ∈ N.primeFactors, 1 - (2 : ℝ) ^ (-σ) ≤ ‖1 - (p : ℂ) ^ (-u)‖ := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have h1 : ‖(p : ℂ) ^ (-u)‖ ≤ (2 : ℝ) ^ (-σ) := by
      rw [Complex.norm_natCast_cpow_of_pos hpp.pos]
      exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hpp.two_le)
        (by simp only [Complex.neg_re]; linarith)
    have := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-u))
    rw [norm_one] at this
    linarith
  have hprod : (1 - (2 : ℝ) ^ (-σ)) ^ N.primeFactors.card ≤ ‖eulerFin N u‖ := by
    rw [eulerFin, norm_prod]
    calc (1 - (2 : ℝ) ^ (-σ)) ^ N.primeFactors.card = ∏ p ∈ N.primeFactors, (1 - (2 : ℝ) ^ (-σ)) :=
          (Finset.prod_const _).symm
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => h0.le) hloc
  have hpos : 0 < (1 - (2 : ℝ) ^ (-σ)) ^ N.primeFactors.card := pow_pos h0 _
  have hB : 1 ≤ 1 / (1 - (2 : ℝ) ^ (-σ)) := by
    rw [le_div_iff₀ h0]; have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (-σ); linarith
  rw [norm_inv]
  calc ‖eulerFin N u‖⁻¹ ≤ ((1 - (2 : ℝ) ^ (-σ)) ^ N.primeFactors.card)⁻¹ :=
        inv_anti₀ hpos hprod
    _ = (1 / (1 - (2 : ℝ) ^ (-σ))) ^ N.primeFactors.card := by rw [one_div, inv_pow]
    _ ≤ _ := pow_card_primeFactors_le hN hB


/-! ### Monotonicity of the exponents -/

theorem one_sub_two_rpow_mono {σ₁ σ₂ : ℝ} (h : σ₁ ≤ σ₂) :
    1 - (2 : ℝ) ^ (-σ₁) ≤ 1 - (2 : ℝ) ^ (-σ₂) := by
  have : (2 : ℝ) ^ (-σ₂) ≤ (2 : ℝ) ^ (-σ₁) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  linarith

theorem betaE_anti {σ₁ σ₂ : ℝ} (h1 : 0 < σ₁) (h : σ₁ ≤ σ₂) : betaE σ₂ ≤ betaE σ₁ := by
  have p1 := one_sub_two_rpow_pos h1
  have p2 := one_sub_two_rpow_pos (lt_of_lt_of_le h1 h)
  unfold betaE
  exact Real.logb_le_logb_of_le (by norm_num) (by positivity)
    (div_le_div_of_nonneg_left (by norm_num) p1 (one_sub_two_rpow_mono h))

theorem gammaE_anti {σ₁ σ₂ : ℝ} (h1 : 0 < σ₁) (h : σ₁ ≤ σ₂) : gammaE σ₂ ≤ gammaE σ₁ := by
  have p1 := one_sub_two_rpow_pos h1
  have p2 := one_sub_two_rpow_pos (lt_of_lt_of_le h1 h)
  unfold gammaE
  exact Real.logb_le_logb_of_le (by norm_num) (by positivity)
    (div_le_div_of_nonneg_left (by norm_num) p1 (one_sub_two_rpow_mono h))

theorem betaE_nonneg {σ : ℝ} (hσ : 0 < σ) : 0 ≤ betaE σ := by
  have p := one_sub_two_rpow_pos hσ
  have : 1 - (2 : ℝ) ^ (-σ) ≤ 1 := by
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (-σ); linarith
  exact Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ p]; linarith)

theorem gammaE_nonneg {σ : ℝ} (hσ : 0 < σ) : 0 ≤ gammaE σ := by
  have p := one_sub_two_rpow_pos hσ
  have : 1 - (2 : ℝ) ^ (-σ) ≤ 1 := by
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (-σ); linarith
  exact Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ p]; linarith)

open SelbergPoincareKernel in
theorem cst_anti {σ₁ σ₂ : ℝ} (h1 : 1 / 2 < σ₁) (h : σ₁ ≤ σ₂) : cst σ₂ ≤ cst σ₁ := by
  unfold cst
  refine MeasureTheory.integral_mono (integrable_one_add_sq (by linarith))
    (integrable_one_add_sq h1) fun t => ?_
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg t]) (by linarith)
