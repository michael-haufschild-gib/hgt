import GaloisForLFunctions.RHTower.JointAncestryMaximalOffLineExclusion
import GaloisForLFunctions.RHTower.WeilLagFunctionInteger

/-!
# The undressed JAS aggregate decides RH

At `σ = 0` the dressed aggregate is the Weil lag function on rational characters:
`N_0(u/v) = Φ(log v - log u)`.

* **RH ⟹ positivity at `σ = 0`.**  Under RH, `Φ(L) = Σ_γ e^{iγL} / (1/4 + γ²)` and the quadratic form
  is `Σ_γ |Σ_i c_i e^{iγ L_i}|² / (1/4 + γ²) ≥ 0`.  By monotonicity every dressing `σ ≥ 0` is then
  positive.
* **Positivity at `σ = 0` ⟹ RH.**  The `2 × 2` minor on the characters `1` and `n` gives
  `Re Φ(log n) ≤ Φ(0)`, the sharp integer lag criterion for RH.

So RH holds iff the undressed aggregate is positive, iff every dressing `σ ≥ 0` is positive.  Together
with the exclusion of a maximal off-line zero, positivity at any dressing `σ ≤ 1` implies either RH,
and with it positivity of the undressed aggregate, or an off-line zero set whose distances from the
critical line have no largest element.
-/

open Complex
open scoped ComplexConjugate BigOperators

namespace RHTower

noncomputable section

/-! ## Characters of natural numbers -/

/-- The character `n = ∏ p^{v_p(n)}`. -/
def jasNatChar (n : ℕ) : Nat.Primes →₀ ℤ :=
  Finsupp.onFinset ((n.primeFactors).subtype Nat.Prime)
    (fun p => ((n.factorization (p : ℕ) : ℕ) : ℤ)) (by
      intro p hp
      have hmem : p ∈ (n.primeFactors).subtype Nat.Prime ↔ (p : ℕ) ∈ n.primeFactors :=
        Finset.mem_subtype
      refine hmem.mpr ?_
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.mpr (by exact_mod_cast hp))

theorem jasNatChar_apply (n : ℕ) (p : Nat.Primes) :
    jasNatChar n p = ((n.factorization (p : ℕ) : ℕ) : ℤ) := rfl

theorem jasLogNeg_jasNatChar (n : ℕ) : jasLogNeg (jasNatChar n) = 0 := by
  unfold jasLogNeg
  rw [jasNatChar, Finsupp.onFinset_sum _ (by simp)]
  refine Finset.sum_eq_zero fun p _ => ?_
  simp

theorem jasLogPos_jasNatChar {n : ℕ} (hn : n ≠ 0) : jasLogPos (jasNatChar n) = Real.log n := by
  unfold jasLogPos
  rw [jasNatChar, Finsupp.onFinset_sum _ (by simp)]
  simp only [Int.toNat_natCast]
  have h : ∑ p ∈ (n.primeFactors).subtype Nat.Prime, ((n.factorization (p : ℕ) : ℕ) : ℝ) *
      Real.log (p : ℕ) = ∑ q ∈ (n.primeFactors).filter Nat.Prime,
        ((n.factorization q : ℕ) : ℝ) * Real.log q :=
    Finset.sum_subtype_eq_sum_filter (fun q : ℕ => ((n.factorization q : ℕ) : ℝ) * Real.log q)
  refine h.trans ?_
  rw [Finset.filter_true_of_mem fun q hq => Nat.prime_of_mem_primeFactors hq]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization, Nat.cast_prod,
    Real.log_prod (fun q hq => by
      have := (Nat.prime_of_mem_primeFactors hq).pos
      positivity)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Nat.cast_pow, Real.log_pow]

theorem jasNatChar_ne_zero {n : ℕ} (hn : 2 ≤ n) : jasNatChar n ≠ 0 := by
  intro h
  have := jasLogPos_jasNatChar (show n ≠ 0 by omega)
  rw [h] at this
  have hz : jasLogPos 0 = 0 := by simp [jasLogPos]
  rw [hz] at this
  have : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  linarith

theorem jasDressedLagAggregate_jasNatChar (σ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    jasDressedLagAggregate σ (jasNatChar n) =
      (Real.exp (-σ * Real.log n) : ℂ) * weilLagFunction (Real.log n) := by
  rw [jasDressedLagAggregate, jasLogSize, jasLogPos_jasNatChar hn, jasLogNeg_jasNatChar, add_zero,
    zero_sub, weilLagFunction_neg]

/-! ## The `2 × 2` minor -/

/-- Positivity bounds every off-diagonal coefficient: `Re N_σ(m) ≤ N_σ(0)`. -/
theorem re_jasDressedLagAggregate_le_of_psd {σ : ℝ} (h : JasDressedPSD σ)
    {m : Nat.Primes →₀ ℤ} (hm : m ≠ 0) :
    (jasDressedLagAggregate σ m).re ≤ poleSharpConstant := by
  have hinj : Set.InjOn (![0, m] : Fin 2 → Nat.Primes →₀ ℤ) (Finset.univ : Finset (Fin 2)) := by
    intro i _ j _ hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hform := h (Fin 2) Finset.univ ![1, -1] ![0, m] hinj
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sub_self, zero_sub,
    sub_zero, jasDressedLagAggregate_neg, jasDressedLagAggregate_zero, map_one, map_neg,
    Complex.add_re, Complex.mul_re] at hform
  simp at hform
  linarith

/-! ## Positivity at `σ = 0` -/

/-- **Positivity of the undressed aggregate implies RH.** -/
theorem riemannHypothesis_of_jasDressedPSD_zero (h : JasDressedPSD 0) : RiemannHypothesis := by
  refine riemannHypothesis_iff_integerLag_le_sharp.mpr fun n hn => ?_
  have hle := re_jasDressedLagAggregate_le_of_psd h (jasNatChar_ne_zero hn)
  rw [jasDressedLagAggregate_jasNatChar 0 (show n ≠ 0 by omega)] at hle
  simpa [integerLag, weilLagFunctionReal] using hle

theorem jasLogNeg_sub_jasLogPos (m : Nat.Primes →₀ ℤ) :
    jasLogNeg m - jasLogPos m = -(m.sum fun p k => (k : ℝ) * Real.log p) := by
  unfold jasLogNeg jasLogPos Finsupp.sum
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← sub_mul, ← neg_mul]
  congr 1
  rcases le_total 0 (m p) with hk | hk
  · have h1 : ((m p).toNat : ℝ) = (m p : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk
    rw [show (-(m p)).toNat = 0 by omega, h1]; push_cast; ring
  · have h1 : ((-(m p)).toNat : ℝ) = (-(m p) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ -(m p))
    rw [show (m p).toNat = 0 by omega, h1]; push_cast; ring

/-- The lag of a character is additive. -/
theorem jasLag_sub (a b : Nat.Primes →₀ ℤ) :
    jasLogNeg (a - b) - jasLogPos (a - b) =
      (jasLogNeg a - jasLogPos a) - (jasLogNeg b - jasLogPos b) := by
  rw [jasLogNeg_sub_jasLogPos, jasLogNeg_sub_jasLogPos, jasLogNeg_sub_jasLogPos,
    Finsupp.sum_sub_index (fun p b₁ b₂ => by push_cast; ring)]
  ring

/-- **RH ⟹ the undressed aggregate is positive semidefinite.** -/
theorem jasDressedPSD_zero_of_riemannHypothesis (hRH : RiemannHypothesis) : JasDressedPSD 0 := by
  intro ι t c n _
  set L : ι → ℝ := fun i => jasLogNeg (n i) - jasLogPos (n i) with hL
  have hN : ∀ i j, jasDressedLagAggregate 0 (n i - n j) = weilLagFunction (L i - L j) := by
    intro i j
    rw [jasDressedLagAggregate, jasLag_sub]
    simp [hL]
  set term : XiZeroCopy → ℂ := fun q => ∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) *
    (cexp (((L i - L j : ℝ) : ℂ) * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) with hterm
  have hsummable : Summable term := by
    rw [hterm]
    exact summable_sum fun i _ => summable_sum fun j _ => (summable_weilLagTerm _).mul_left _
  have hswap : ∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) * jasDressedLagAggregate 0 (n i - n j) =
      ∑' q, term q := by
    simp_rw [hN]
    rw [hterm, Summable.tsum_finsetSum (fun i _ => summable_sum fun j _ =>
      (summable_weilLagTerm _).mul_left _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Summable.tsum_finsetSum (fun j _ => (summable_weilLagTerm _).mul_left _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [weilLagFunction, tsum_mul_left]
  have hq : ∀ q : XiZeroCopy, 0 ≤ (term q).re := by
    intro q
    have hcrit : ((q.1 : ℂ)).re = 1 / 2 := xi_divisor_support_re_eq_half_of_rh hRH q.1
    set γ := ((q.1 : ℂ)).im with hγ
    have hρ : (q.1 : ℂ) - 1 / 2 = (γ : ℂ) * I := by
      apply Complex.ext <;> simp [hcrit, hγ]
    set w : ℝ := 1 / (1 / 4 + γ ^ 2) with hw
    have hw0 : 0 ≤ w := by rw [hw]; positivity
    set e : ι → ℂ := fun i => cexp ((L i * γ : ℝ) * I) with he
    have he2 : ∀ i j, e i * conj (e j) = cexp (((L i - L j : ℝ) : ℂ) * ((γ : ℂ) * I)) := by
      intro i j
      have hconj : conj (e j) = cexp ((-(L j * γ) : ℝ) * I) := by
        rw [he, ← Complex.exp_conj]; congr 1; simp
      rw [hconj, he, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hS : (((Complex.normSq (∑ i ∈ t, c i * e i)) : ℝ) : ℂ) =
        ∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) * (e i * conj (e j)) := by
      rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul]
      ring
    have hsplit : term q = (w : ℂ) * (((Complex.normSq (∑ i ∈ t, c i * e i)) : ℝ) : ℂ) := by
      rw [hS, hterm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [div_eq_mul_one_div _ ((q.1 : ℂ) * _), inv_mul_one_sub_eq_of_critical hcrit, ← hγ, ← hw,
        hρ, he2]
      ring
    rw [hsplit, Complex.re_ofReal_mul, Complex.ofReal_re]
    exact mul_nonneg hw0 (Complex.normSq_nonneg _)
  rw [hswap, Complex.re_tsum hsummable]
  exact tsum_nonneg hq

/-- **RH ⟺ the undressed JAS aggregate is positive semidefinite.** -/
theorem riemannHypothesis_iff_jasDressedPSD_zero : RiemannHypothesis ↔ JasDressedPSD 0 :=
  ⟨jasDressedPSD_zero_of_riemannHypothesis, riemannHypothesis_of_jasDressedPSD_zero⟩

/-- **RH ⟺ every dressing `σ ≥ 0` is positive.** -/
theorem riemannHypothesis_iff_forall_nonneg_jasDressedPSD :
    RiemannHypothesis ↔ ∀ σ : ℝ, 0 ≤ σ → JasDressedPSD σ :=
  ⟨fun h _ hσ => (jasDressedPSD_zero_of_riemannHypothesis h).mono hσ,
    fun h => riemannHypothesis_of_jasDressedPSD_zero (h 0 le_rfl)⟩

/-- **Positivity below `σ = 1`: RH or an off-line chain.**  If the dressed aggregate is positive at
some `σ ≤ 1`, then either RH holds (and the undressed aggregate is positive), or every off-line
Xi zero is strictly exceeded in distance from the critical line by another Xi zero. -/
theorem riemannHypothesis_or_offLine_chain_of_jasDressedPSD {σ : ℝ} (hσ : σ ≤ 1)
    (h : JasDressedPSD σ) :
    RiemannHypothesis ∨ ∀ q₀ : XiZeroCopy, (q₀.1 : ℂ).re ≠ 1 / 2 →
      ∃ q : XiZeroCopy, |(q₀.1 : ℂ).re - 1 / 2| < |(q.1 : ℂ).re - 1 / 2| := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · refine Or.inr fun q₀ hoff => exists_farther_zero_of_jasDressedPSD h q₀ hoff ?_
    have : 0 < |(q₀.1 : ℂ).re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hoff)
    linarith

end

end RHTower
