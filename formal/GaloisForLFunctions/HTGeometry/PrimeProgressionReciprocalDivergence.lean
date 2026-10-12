import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Divergence of the prime reciprocals in a residue class

**Theorem** (`not_summable_primeRecipClass`).  For `q ≥ 1` and a unit `a` mod `q`,
`Σ_{p ≡ a (q)} 1/p = ∞`.

**Proof.**  Suppose the sum converges, and pick `M` with tail `Σ_{p > M, p ≡ a} 1/p ≤ 1/(2φ(q))`.
For `1 < x ≤ 2` and a prime `p > M` in the class, `log p · p^{−x} ≤ (x − 1)^{−1} p^{−1}`, since
`log p ≤ p^{x−1}/(x − 1)`.  The prime powers contribute a bounded amount, and the primes `≤ M` a
fixed finite amount.  Hence `Σ_{n ≡ a} Λ(n) n^{−x} ≤ K + (2φ(q))^{−1}(x − 1)^{−1}`.  This contradicts
the lower bound `φ(q)^{−1}(x − 1)^{−1} − C` (`LSeries_residueClass_lower_bound`) as `x → 1⁺`.
-/

open ArithmeticFunction ArithmeticFunction.vonMangoldt Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `1/p` on the primes `p ≡ a (mod q)`, and `0` elsewhere. -/
def primeRecipClass (q : ℕ) (a : ZMod q) (n : ℕ) : ℝ :=
  if n.Prime ∧ (n : ZMod q) = a then (n : ℝ)⁻¹ else 0

theorem primeRecipClass_nonneg (q : ℕ) (a : ZMod q) (n : ℕ) : 0 ≤ primeRecipClass q a n := by
  unfold primeRecipClass; split_ifs <;> positivity

/-- `log n · n^{−x} ≤ (x − 1)^{−1} n^{−1}` for `x > 1`. -/
theorem log_div_rpow_le {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 1 < x) :
    Real.log n / (n : ℝ) ^ x ≤ (x - 1)⁻¹ * (n : ℝ)⁻¹ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hl := Real.log_le_rpow_div hn0.le (sub_pos.mpr hx)
  have hsplit : (n : ℝ) ^ x = (n : ℝ) ^ (x - 1) * n := by
    rw [← Real.rpow_add_one hn0.ne', sub_add_cancel]
  have hpos : 0 < (n : ℝ) ^ (x - 1) := Real.rpow_pos_of_pos hn0 _
  rw [hsplit, div_le_iff₀ (mul_pos hpos hn0)]
  calc Real.log n ≤ (n : ℝ) ^ (x - 1) / (x - 1) := hl
    _ = (x - 1)⁻¹ * (n : ℝ)⁻¹ * ((n : ℝ) ^ (x - 1) * n) := by field_simp

/-- The termwise bound: primes beyond `M` are controlled by `1/p`, the rest by `x = 1`. -/
theorem residueClass_div_rpow_le {q : ℕ} (a : ZMod q) (M n : ℕ) {x : ℝ} (hx : 1 < x) :
    residueClass a n / (n : ℝ) ^ x ≤
      (if n ≤ M then residueClass a n / n else 0) +
        (x - 1)⁻¹ * (if M < n then primeRecipClass q a n else 0) +
        (if n.Prime then 0 else residueClass a n) / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn1 : 1 ≤ n := hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr0 := residueClass_nonneg a n
  have hx0 : 0 ≤ (x - 1)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hx).le
  have hmono : residueClass a n / (n : ℝ) ^ x ≤ residueClass a n / n := by
    refine div_le_div_of_nonneg_left hr0 hn0 ?_
    calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (n : ℝ) ^ x := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) hx.le
  have hP : 0 ≤ primeRecipClass q a n := primeRecipClass_nonneg q a n
  by_cases hp : n.Prime
  · simp only [hp, if_true, zero_div, add_zero]
    by_cases hM : n ≤ M
    · rw [if_pos hM, if_neg (not_lt.mpr hM), mul_zero, add_zero]; exact hmono
    · rw [if_neg hM, if_pos (not_le.mp hM), zero_add]
      by_cases ha : (n : ZMod q) = a
      · have hres : residueClass a n = Real.log n := by
          simp [residueClass, Set.indicator, ha, vonMangoldt_apply_prime hp]
        rw [hres, primeRecipClass, if_pos ⟨hp, ha⟩]
        exact log_div_rpow_le hn1 hx
      · have hres : residueClass a n = 0 := by simp [residueClass, Set.indicator, ha]
        rw [hres, zero_div]; positivity
  · simp only [hp, if_false]
    have h1 : 0 ≤ (if n ≤ M then residueClass a n / n else 0) := by
      split_ifs <;> positivity
    have h2 : 0 ≤ (x - 1)⁻¹ * (if M < n then primeRecipClass q a n else 0) := by
      split_ifs <;> positivity
    linarith

/-- **Dirichlet divergence.**  `Σ_{p ≡ a (q)} 1/p = ∞` for every unit `a` mod `q`. -/
theorem not_summable_primeRecipClass {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ¬ Summable (primeRecipClass q a) := by
  intro hsum
  set φ' : ℝ := (q.totient : ℝ)⁻¹ with hφ'
  have hφ : 0 < φ' := inv_pos.mpr (by exact_mod_cast q.totient.pos_of_neZero)
  obtain ⟨C, hC⟩ := LSeries_residueClass_lower_bound ha
  -- a tail of the prime reciprocals below `φ'/2`
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp
    ((tendsto_sum_nat_add (primeRecipClass q a)).eventually (gt_mem_nhds (half_pos hφ)))
  set M : ℕ := M₀ with hMdef
  have hQ := summable_residueClass_non_primes_div a
  set C₁ : ℝ := ∑' n : ℕ, (if n.Prime then 0 else residueClass a n) / n with hC₁
  set CM : ℝ := ∑ n ∈ Finset.range (M + 1), residueClass a n / n with hCM
  have hsT : Summable fun n => if M < n then primeRecipClass q a n else 0 :=
    hsum.of_nonneg_of_le (fun n => by split_ifs <;> simp [primeRecipClass_nonneg])
      (fun n => by split_ifs <;> simp [primeRecipClass_nonneg])
  have htailM : ∑' n, (if M < n then primeRecipClass q a n else 0) < φ' / 2 := by
    rw [← hsT.sum_add_tsum_nat_add (M + 1)]
    have hz : ∑ i ∈ Finset.range (M + 1), (if M < i then primeRecipClass q a i else 0) = 0 :=
      Finset.sum_eq_zero fun i hi => if_neg (by simp at hi; omega)
    rw [hz, zero_add]
    have e : ∀ k, (if M < k + (M + 1) then primeRecipClass q a (k + (M + 1)) else 0) =
        primeRecipClass q a (k + (M + 1)) := fun k => if_pos (by omega)
    simp_rw [e]
    exact hM₀ (M + 1) (by omega)
  -- the upper bound for `1 < x ≤ 2`
  have hupper : ∀ x : ℝ, 1 < x →
      ∑' n, residueClass a n / (n : ℝ) ^ x ≤ CM + (x - 1)⁻¹ * (φ' / 2) + C₁ := by
    intro x hx
    have hx0 : 0 ≤ (x - 1)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hx).le
    have hs1 : Summable fun n => (if n ≤ M then residueClass a n / n else 0) :=
      summable_of_ne_finset_zero (s := Finset.range (M + 1)) fun n hn => by
        rw [if_neg]; simp at hn; omega
    have hs2 : Summable fun n => (x - 1)⁻¹ * (if M < n then primeRecipClass q a n else 0) :=
      hsT.mul_left _
    have hsB := (hs1.add hs2).add hQ
    have hsg : Summable fun n => residueClass a n / (n : ℝ) ^ x :=
      hsB.of_nonneg_of_le (fun n => by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · exact div_nonneg (residueClass_nonneg a n) (by positivity))
        (fun n => residueClass_div_rpow_le a M n hx)
    calc ∑' n, residueClass a n / (n : ℝ) ^ x
        ≤ ∑' n, ((if n ≤ M then residueClass a n / n else 0) +
            (x - 1)⁻¹ * (if M < n then primeRecipClass q a n else 0) +
            (if n.Prime then 0 else residueClass a n) / n) :=
          hsg.tsum_le_tsum (fun n => residueClass_div_rpow_le a M n hx) hsB
      _ = (∑' n, (if n ≤ M then residueClass a n / n else 0)) +
            (x - 1)⁻¹ * (∑' n, (if M < n then primeRecipClass q a n else 0)) + C₁ := by
          rw [(hs1.add hs2).tsum_add hQ, hs1.tsum_add hs2, tsum_mul_left]
      _ ≤ CM + (x - 1)⁻¹ * (φ' / 2) + C₁ := by
          have e1 : ∑' n, (if n ≤ M then residueClass a n / n else 0) = CM := by
            rw [tsum_eq_sum (s := Finset.range (M + 1)) fun n hn => by
              rw [if_neg]; simp at hn; omega]
            exact Finset.sum_congr rfl fun n hn => if_pos (by simp at hn; omega)
          rw [e1]
          gcongr
  -- the contradiction as `x → 1⁺`
  set K : ℝ := CM + C₁ + C with hK
  set δ : ℝ := min 1 (φ' / (4 * (|K| + 1))) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hx : 1 + δ ∈ Set.Ioc (1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have h1 := hC hx
  have h2 := hupper (1 + δ) hx.1
  have hsub : (1 + δ) - 1 = δ := by ring
  rw [hsub] at h1 h2
  have h3 : φ' / δ - C ≤ CM + δ⁻¹ * (φ' / 2) + C₁ := h1.trans h2
  have h4 : φ' / 2 / δ ≤ K := by
    have : φ' / δ = φ' / 2 / δ + δ⁻¹ * (φ' / 2) := by field_simp; ring
    rw [this] at h3
    linarith
  have h5 : 2 * (|K| + 1) ≤ φ' / 2 / δ := by
    rw [le_div_iff₀ hδpos]
    have : δ ≤ φ' / (4 * (|K| + 1)) := min_le_right _ _
    have hK1 : 0 < |K| + 1 := by positivity
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  have : K ≤ |K| := le_abs_self K
  linarith [abs_nonneg K]

/-- The prime reciprocals in a unit class have unbounded finite sums. -/
theorem exists_finset_primeRecip_gt {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) (R : ℝ) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ (p : ZMod q) = a) ∧ R < ∑ p ∈ S, ((p : ℝ))⁻¹ := by
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (primeRecipClass_nonneg q a)).mp (not_summable_primeRecipClass ha)
  obtain ⟨n, hn⟩ := (hdiv.eventually (eventually_gt_atTop R)).exists
  refine ⟨(Finset.range n).filter fun p => p.Prime ∧ (p : ZMod q) = a,
    fun p hp => (Finset.mem_filter.mp hp).2, ?_⟩
  rw [Finset.sum_filter]
  exact hn.trans_le (le_of_eq (Finset.sum_congr rfl fun p _ => by
    unfold primeRecipClass; split_ifs <;> rfl))

end

end GaloisForLFunctions.HTGeometry
