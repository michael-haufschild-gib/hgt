import GaloisForLFunctions.RHTower.JointAncestryRealSignTypical

/-!
# Almost every phase vector is JAS-positive, uniformly in the prime set

Test the JAS product aggregate at level `σ` on a finite prime set `P` with vectors
`z_p = r ω^{k_p}`, `ω = e^{2πi/N}`, `N ≥ 3`, `k : P → ℤ/N` (`jasPhaseAggregate`).  The count
`card_jasPhaseAggregate_re_neg_le` bounds the proportion of phase vectors with negative real part
by `(W/Φ(0))² (∏_P (1 + 2a² p^{1−2σ}) − 1)`, `a = r/(1 + r²)`, which at `σ = 1` is `O(Σ_P 1/p)`
and so needs a budget restriction on `P`.

**Theorem** (`exists_card_jasPhaseAggregate_re_neg_le`).  For every level `σ ≥ 1`, every `r ≥ 0`,
every `N ≥ 3` and every `ε > 0` there is `X` such that for **every** finite set `P` of primes
`p > X` at most `ε · N^{|P|}` phase vectors give a negative real part.  No hypothesis on the zeros.

Proof.  The mean square of the deviation at a zero is `∏_P (1 + a²(|A_p|² + |B_p|²)) − 1`, and at a
zero `|A_p|, |B_p| ≤ p^{−(σ−|Re ρ−½|)}`.  With `2a² ≤ ½` and `σ ≥ 1` this is at most
`∏_P (1 + p^{−s_ρ}) − 1`, `s_ρ = 2 − 2|Re ρ − ½| > 1`.  The weighted sum over zeros of these
quantities is the variance functional `V_P` of `R:JointAncestryRealSignTypical`, which tends to `0`
uniformly in `P` (`exists_jasSignVariance_le`).  The weighted Cauchy–Schwarz inequality then counts
the negative vectors by `N^{|P|} W V_P / Φ(0)²`.
-/

open Complex Filter
open scoped ComplexConjugate BigOperators

namespace RHTower

noncomputable section

/-- At a zero, `a²(|A_p|² + |B_p|²) ≤ p^{−s_ρ}` when `a = r/(1 + r²)` and `σ ≥ 1`. -/
theorem phase_second_moment_le {σ : ℝ} (hσ : 1 ≤ σ) {r : ℝ} (hr : 0 ≤ r) (q : XiZeroCopy)
    (p : Nat.Primes) :
    (r / (1 + r ^ 2)) ^ 2 * (‖jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p‖ ^ 2 +
      ‖jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p‖ ^ 2) ≤
      Real.exp (-jasSignExponent q * Real.log p) := by
  have ha0 : 0 ≤ r / (1 + r ^ 2) := by positivity
  have ha : r / (1 + r ^ 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg (r - 1)]
  have hA := norm_jasHoloA_dressed_le_abs σ q p
  have hB := norm_jasHoloB_dressed_le_abs σ q p
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log p) := ⟨_, rfl⟩
  rw [← he] at hA hB
  have he0 : 0 ≤ e := by rw [he]; exact (Real.exp_pos _).le
  have he2 : e ^ 2 ≤ Real.exp (-jasSignExponent q * Real.log p) := by
    rw [he, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have hL := log_prime_pos p
    unfold jasSignExponent
    push_cast
    nlinarith
  have h1 := pow_le_pow_left₀ (norm_nonneg _) hA 2
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hB 2
  have hsq : (r / (1 + r ^ 2)) ^ 2 ≤ 1 / 4 := by nlinarith
  calc (r / (1 + r ^ 2)) ^ 2 * (‖jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p‖ ^ 2 +
        ‖jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p‖ ^ 2)
      ≤ (1 / 4) * (e ^ 2 + e ^ 2) := by
        gcongr
    _ ≤ Real.exp (-jasSignExponent q * Real.log p) := by nlinarith

/-- **Counting the negative phase vectors, with the per-zero exponents.**  At a level `σ ≥ 1` the
number of phase vectors with negative real part is at most `N^{|P|} W V_P / Φ(0)²`. -/
theorem card_jasPhaseAggregate_re_neg_le_variance {σ : ℝ} (hσ : 1 ≤ σ) {r : ℝ} (hr : 0 ≤ r)
    {N : ℕ} (hN : 3 ≤ N) (P : Finset Nat.Primes) :
    ((Finset.univ.filter fun k : ↥P → Fin N => (jasPhaseAggregate σ r N P k).re < 0).card : ℝ) *
      poleSharpConstant ^ 2 ≤ lagWeightTotal * (N : ℝ) ^ P.card * jasSignVariance P := by
  classical
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = r / (1 + r ^ 2) := ⟨_, rfl⟩
  have ha : 0 ≤ a := by rw [hadef]; positivity
  have hΦ := poleSharpConstant_pos
  have hW := lagWeightTotal_nonneg
  obtain ⟨A, hAdef⟩ : ∃ A : XiZeroCopy → Nat.Primes → ℂ,
      A = fun q p => jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : XiZeroCopy → Nat.Primes → ℂ,
      B = fun q p => jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p := ⟨_, rfl⟩
  obtain ⟨e, hedef⟩ : ∃ e : Nat.Primes → ℝ,
      e = fun p : Nat.Primes => Real.exp (-(σ - 1 / 2) * Real.log p) := ⟨_, rfl⟩
  have hA : ∀ q p, ‖A q p‖ ≤ e p := fun q p => by
    rw [hAdef, hedef]; exact norm_jasHoloA_le_half σ q p
  have hB : ∀ q p, ‖B q p‖ ≤ e p := fun q p => by
    rw [hBdef, hedef]; exact norm_jasHoloB_le_half σ q p
  obtain ⟨Pi, hPidef⟩ : ∃ Pi : XiZeroCopy → (↥P → Fin N) → ℂ,
      Pi = fun q k => ∏ p : ↥P, phaseFactor N a (A q p) (B q p) (k p) := ⟨_, rfl⟩
  obtain ⟨w, hwdef⟩ : ∃ w : XiZeroCopy → ℂ, w = fun q => 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) :=
    ⟨_, rfl⟩
  have hws : Summable w := by rw [hwdef]; exact summable_inv_mul_one_sub
  have hwn : Summable fun q => ‖w q‖ := hws.norm
  obtain ⟨M₀, hM₀def⟩ : ∃ M₀ : ℝ, M₀ = ∏ p : ↥P, (1 + a * (2 * e p)) := ⟨_, rfl⟩
  have hPi : ∀ q k, ‖Pi q k‖ ≤ M₀ := by
    intro q k
    rw [hPidef, hM₀def, norm_prod]
    refine Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p _ => ?_
    refine (norm_phaseFactor_le ha _ _ _).trans ?_
    have := hA q p; have := hB q p
    nlinarith
  have hx : ∀ q k, ‖Pi q k - 1‖ ≤ M₀ + 1 := fun q k =>
    (norm_sub_le _ _).trans (by rw [norm_one]; linarith [hPi q k])
  have hagg : ∀ k, jasPhaseAggregate σ r N P k =
      (((1 + r ^ 2) ^ P.card : ℝ) : ℂ) * ∑' q, w q * Pi q k := by
    intro k
    unfold jasPhaseAggregate
    rw [← tsum_mul_left]
    refine tsum_congr fun q => ?_
    rw [Finset.prod_congr rfl fun p _ => jasBernoulliFactor_phase _ _ hr (k p),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe, hPidef,
      hwdef, hAdef, hBdef, hadef]
    push_cast
    ring
  have hsumPi : ∀ k, Summable fun q => w q * (Pi q k - 1) := fun k =>
    Summable.of_norm_bounded (hwn.mul_right (M₀ + 1)) fun q => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hx q k) (norm_nonneg _)
  have hsplit : ∀ k, ∑' q, w q * Pi q k = (poleSharpConstant : ℂ) + ∑' q, w q * (Pi q k - 1) := by
    intro k
    have e1 : ∀ q, w q * Pi q k = w q + w q * (Pi q k - 1) := fun q => by ring
    simp_rw [e1]
    rw [hws.tsum_add (hsumPi k), hwdef, tsum_inv_zero_mul_one_sub_zero]
  obtain ⟨S, hSdef⟩ : ∃ S : (↥P → Fin N) → ℝ, S = fun k => ∑' q, ‖w q‖ * ‖Pi q k - 1‖ :=
    ⟨_, rfl⟩
  have hSs : ∀ k, Summable fun q => ‖w q‖ * ‖Pi q k - 1‖ := fun k =>
    Summable.of_nonneg_of_le (fun q => by positivity)
      (fun q => mul_le_mul_of_nonneg_left (hx q k) (norm_nonneg _)) (hwn.mul_right _)
  have hSs2 : ∀ k, Summable fun q => ‖w q‖ * ‖Pi q k - 1‖ ^ 2 := fun k =>
    Summable.of_nonneg_of_le (fun q => by positivity)
      (fun q => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hx q k) 2)
        (norm_nonneg _)) (hwn.mul_right _)
  have hbad : ∀ k, (jasPhaseAggregate σ r N P k).re < 0 → poleSharpConstant ^ 2 ≤ S k ^ 2 := by
    intro k hk
    rw [hagg, hsplit, Complex.re_ofReal_mul] at hk
    have hc : 0 < ((1 + r ^ 2) ^ P.card : ℝ) := by positivity
    have hre : ((poleSharpConstant : ℂ) + ∑' q, w q * (Pi q k - 1)).re < 0 := by
      by_contra h; push Not at h; linarith [mul_nonneg hc.le h]
    rw [Complex.add_re, Complex.ofReal_re] at hre
    have h1 : poleSharpConstant ≤ ‖∑' q, w q * (Pi q k - 1)‖ := by
      have := (neg_le_abs _).trans (Complex.abs_re_le_norm (∑' q, w q * (Pi q k - 1))); linarith
    have h2 : ‖∑' q, w q * (Pi q k - 1)‖ ≤ S k := by
      rw [hSdef]
      refine (norm_tsum_le_tsum_norm (hsumPi k).norm).trans (le_of_eq ?_)
      exact tsum_congr fun q => norm_mul _ _
    exact pow_le_pow_left₀ hΦ.le (h1.trans h2) 2
  have hCS : ∀ k, S k ^ 2 ≤ lagWeightTotal * ∑' q, ‖w q‖ * ‖Pi q k - 1‖ ^ 2 := by
    intro k
    rw [hSdef]
    have := sq_tsum_mul_le (c := fun q => ‖w q‖) (x := fun q => ‖Pi q k - 1‖)
      (fun q => norm_nonneg _) hwn (hSs k) (hSs2 k)
    have hWt : ∑' q, ‖w q‖ = lagWeightTotal := by rw [hwdef]; rfl
    rwa [hWt] at this
  -- the mean square at a zero, with the per-zero exponent
  have hmsq : ∀ q, ∑ k : ↥P → Fin N, ‖Pi q k - 1‖ ^ 2 ≤ (N : ℝ) ^ P.card *
      ((∏ p ∈ P, (1 + Real.exp (-jasSignExponent q * Real.log p))) - 1) := by
    intro q
    have h := sum_normSq_prod_phaseFactor_sub_one hN a (fun p : ↥P => A q p) (fun p => B q p)
    rw [Fintype.card_coe] at h
    rw [hPidef]
    simp only at h ⊢
    rw [h]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hle : ∏ p : ↥P, (1 + a ^ 2 * (‖A q p‖ ^ 2 + ‖B q p‖ ^ 2)) ≤
        ∏ p : ↥P, (1 + Real.exp (-jasSignExponent q * Real.log p)) := by
      refine Finset.prod_le_prod (fun p _ => by positivity) fun p _ => ?_
      have := phase_second_moment_le hσ hr q p
      rw [hadef, hAdef, hBdef]
      linarith
    rw [Finset.prod_coe_sort P (fun p => 1 + Real.exp (-jasSignExponent q * Real.log p))] at hle
    linarith
  have htotal : ∑ k : ↥P → Fin N, S k ^ 2 ≤
      lagWeightTotal * ((N : ℝ) ^ P.card * jasSignVariance P) := by
    have h1 : ∑ k : ↥P → Fin N, S k ^ 2 ≤
        ∑ k : ↥P → Fin N, lagWeightTotal * ∑' q, ‖w q‖ * ‖Pi q k - 1‖ ^ 2 :=
      Finset.sum_le_sum fun k _ => hCS k
    rw [← Finset.mul_sum, ← Summable.tsum_finsetSum fun k _ => hSs2 k] at h1
    have h2 : ∑' q, ∑ k : ↥P → Fin N, ‖w q‖ * ‖Pi q k - 1‖ ^ 2 ≤
        ∑' q, (N : ℝ) ^ P.card * (‖lagWeight q‖ *
          ((∏ p ∈ P, (1 + Real.exp (-jasSignExponent q * Real.log p))) - 1)) := by
      refine Summable.tsum_le_tsum (fun q => ?_) (summable_sum fun k _ => hSs2 k)
        ((summable_jasSignVariance_term P).mul_left _)
      rw [← Finset.mul_sum]
      have hwq : ‖w q‖ = ‖lagWeight q‖ := by rw [hwdef]; rfl
      rw [hwq]
      have := mul_le_mul_of_nonneg_left (hmsq q) (norm_nonneg (lagWeight q))
      linarith
    rw [tsum_mul_left] at h2
    calc ∑ k : ↥P → Fin N, S k ^ 2
        ≤ lagWeightTotal * ((N : ℝ) ^ P.card * jasSignVariance P) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 hW)
      _ = lagWeightTotal * ((N : ℝ) ^ P.card * jasSignVariance P) := rfl
  have hcount : ((Finset.univ.filter fun k : ↥P → Fin N =>
      (jasPhaseAggregate σ r N P k).re < 0).card : ℝ) * poleSharpConstant ^ 2 ≤
      ∑ k : ↥P → Fin N, S k ^ 2 := by
    rw [show ((Finset.univ.filter fun k : ↥P → Fin N =>
        (jasPhaseAggregate σ r N P k).re < 0).card : ℝ) * poleSharpConstant ^ 2 =
        ∑ _k ∈ Finset.univ.filter (fun k : ↥P → Fin N => (jasPhaseAggregate σ r N P k).re < 0),
          poleSharpConstant ^ 2 by rw [Finset.sum_const, nsmul_eq_mul]]
    calc ∑ _k ∈ Finset.univ.filter (fun k : ↥P → Fin N => (jasPhaseAggregate σ r N P k).re < 0),
          poleSharpConstant ^ 2
        ≤ ∑ k ∈ Finset.univ.filter (fun k : ↥P → Fin N => (jasPhaseAggregate σ r N P k).re < 0),
            S k ^ 2 := Finset.sum_le_sum fun k hk => hbad k (Finset.mem_filter.mp hk).2
      _ ≤ ∑ k : ↥P → Fin N, S k ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun k _ _ => sq_nonneg _)
  calc _ ≤ ∑ k : ↥P → Fin N, S k ^ 2 := hcount
    _ ≤ lagWeightTotal * ((N : ℝ) ^ P.card * jasSignVariance P) := htotal
    _ = lagWeightTotal * (N : ℝ) ^ P.card * jasSignVariance P := by ring

/-- **Almost every phase vector is positive, uniformly in the prime set.**  For every level
`σ ≥ 1`, every `r ≥ 0`, every `N ≥ 3` and every `ε > 0` there is `X` such that for every finite set
`P` of primes `p > X` at most `ε · N^{|P|}` phase vectors `k : P → ℤ/N` give a JAS aggregate with
negative real part. -/
theorem exists_card_jasPhaseAggregate_re_neg_le {σ : ℝ} (hσ : 1 ≤ σ) {r : ℝ} (hr : 0 ≤ r)
    {N : ℕ} (hN : 3 ≤ N) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℕ, ∀ P : Finset Nat.Primes, (∀ p ∈ P, X < (p : ℕ)) →
      ((Finset.univ.filter fun k : ↥P → Fin N => (jasPhaseAggregate σ r N P k).re < 0).card : ℝ) ≤
        ε * (N : ℝ) ^ P.card := by
  have hΦ := poleSharpConstant_pos
  have hW0 := lagWeightTotal_nonneg
  obtain ⟨X, hX⟩ := exists_jasSignVariance_le
    (show 0 < ε * poleSharpConstant ^ 2 / (lagWeightTotal + 1) by positivity)
  refine ⟨X, fun P hP => ?_⟩
  have hc := card_jasPhaseAggregate_re_neg_le_variance hσ hr hN P
  have hV := hX P hP
  have hN0 : (0 : ℝ) < (N : ℝ) ^ P.card := by
    have : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    positivity
  have hV0 : 0 ≤ jasSignVariance P := tsum_nonneg fun q =>
    mul_nonneg (norm_nonneg _) (prod_one_add_exp_neg_sub_one_nonneg _ _)
  have key : lagWeightTotal * jasSignVariance P ≤ ε * poleSharpConstant ^ 2 := by
    calc lagWeightTotal * jasSignVariance P
        ≤ (lagWeightTotal + 1) * (ε * poleSharpConstant ^ 2 / (lagWeightTotal + 1)) := by
          gcongr
          linarith
      _ = ε * poleSharpConstant ^ 2 := by field_simp
  have hΦ2 : 0 < poleSharpConstant ^ 2 := by positivity
  have : ((Finset.univ.filter fun k : ↥P → Fin N => (jasPhaseAggregate σ r N P k).re < 0).card :
      ℝ) * poleSharpConstant ^ 2 ≤ ε * (N : ℝ) ^ P.card * poleSharpConstant ^ 2 := by
    calc _ ≤ lagWeightTotal * (N : ℝ) ^ P.card * jasSignVariance P := hc
      _ = (N : ℝ) ^ P.card * (lagWeightTotal * jasSignVariance P) := by ring
      _ ≤ (N : ℝ) ^ P.card * (ε * poleSharpConstant ^ 2) := mul_le_mul_of_nonneg_left key hN0.le
      _ = ε * (N : ℝ) ^ P.card * poleSharpConstant ^ 2 := by ring
  exact le_of_mul_le_mul_right this hΦ2

end

end RHTower
