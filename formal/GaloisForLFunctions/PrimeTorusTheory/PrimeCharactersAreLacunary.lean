import GaloisForLFunctions.PrimeTorusTheory.TheHullOverTheTorus

/-!
# Prime characters are lacunary

A family `x_p`, `p` prime, of random variables on a probability space is *lacunary* (`IsLacunary`) if it is unimodular and orthonormal, and if the correlations `∫_E x_p conj x_q`, `p ≠ q`, of every set `E` with its pair products satisfy Bessel's inequality up to a factor `2`. The characters of the gauge torus are lacunary, because unique factorization makes `x_p conj x_q`, `p ≠ q`, orthonormal (`integral_pairChar_mul_conj`, `isLacunary_twist`).

**The off-diagonal** (`le_setIntegral_normSq`). The tail of the correlations beyond some `P` is as small as we like (`exists_tail_corr_small`). If it is at most `τ²`, then `(|E| − τ) Σ_{P≤p} |a_p|² ≤ ∫_E |Σ_{P≤p} a_p x_p|²`.

**Zygmund's theorem** (`measure_bounded_primeSumOf_eq_zero`). Let `Re s_j ↓ ½`. For a lacunary family, the prime sums `g_j = Σ_p p^{−s_j} x_p`, perturbed by anything bounded in `L²` uniformly in `j`, are bounded on a set of measure zero only. A bound on a set `E` of positive measure would give `(|E|/2) Σ_{P≤p} p^{−2σ_j} = O(1)` uniformly in `j`, and `Σ 1/p = ∞`. On the gauge torus this is `measure_bounded_prime_sums_eq_zero`.
-/

open MeasureTheory Filter Topology Finset

namespace GaloisForLFunctions.PrimeTorusTheory

open ArithmeticCorrelationGeometry

noncomputable section

local notation "conj" => starRingEnd ℂ

/-! ### Prime sums -/

/-- The coefficient `n^{−s}`. -/
def powCoeff (s : ℂ) (n : ℕ) : ℂ := (n : ℂ) ^ (-s)

theorem norm_powCoeff_sq {p : ℕ} (hp : 0 < p) (s : ℂ) :
    ‖powCoeff s p‖ ^ 2 = (p : ℝ) ^ (-(2 * s.re)) := by
  unfold powCoeff
  rw [Complex.norm_natCast_cpow_of_pos hp, Complex.neg_re, ← Real.rpow_natCast,
    ← Real.rpow_mul (Nat.cast_nonneg p)]
  congr 1
  push_cast
  ring

theorem norm_powCoeff_le_one {p : ℕ} (hp : 0 < p) {s : ℂ} (hs : 0 ≤ s.re) : ‖powCoeff s p‖ ≤ 1 := by
  unfold powCoeff
  rw [Complex.norm_natCast_cpow_of_pos hp, Complex.neg_re]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp) (by linarith)

theorem primesBelow_subset {P N : ℕ} (h : P ≤ N) : P.primesBelow ⊆ N.primesBelow := fun p hp => by
  obtain ⟨h1, h2⟩ := Nat.mem_primesBelow.mp hp
  exact Nat.mem_primesBelow.mpr ⟨h1.trans_le h, h2⟩

/-- A sum over all primes is the limit of the sums over `primesBelow`. -/
theorem tendsto_sum_primesBelow {F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {g : ℕ → F}
    (h : Summable fun p : Nat.Primes => g p) :
    Tendsto (fun N : ℕ => ∑ p ∈ N.primesBelow, g p) atTop (𝓝 (∑' p : Nat.Primes, g p)) := by
  classical
  have h1 := h.hasSum
  have h2 : HasSum ({p : ℕ | p.Prime}.indicator g) (∑' p : Nat.Primes, g p) :=
    hasSum_subtype_iff_indicator.mp h1
  refine h2.tendsto_sum_nat.congr fun N => ?_
  unfold Nat.primesBelow
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hn : n.Prime
  · simp [hn]
  · simp [hn]

theorem sum_primesBelow_le_tsum {g : ℕ → ℝ} (hg : ∀ p, 0 ≤ g p)
    (h : Summable fun p : Nat.Primes => g p) (N : ℕ) :
    ∑ p ∈ N.primesBelow, g p ≤ ∑' p : Nat.Primes, g p := by
  have hm : Monotone fun N : ℕ => ∑ p ∈ N.primesBelow, g p := fun a b hab =>
    Finset.sum_le_sum_of_subset_of_nonneg (primesBelow_subset hab) fun p _ _ => hg p
  exact hm.ge_of_tendsto (tendsto_sum_primesBelow h) N

theorem norm_sub_sub_sub_sq_le (a b c d : ℂ) :
    ‖a - b - c - d‖ ^ 2 ≤ 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have h : ‖a - b - c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    calc
      ‖a - b - c - d‖ ≤ ‖a - b - c‖ + ‖d‖ := norm_sub_le _ _
      _ ≤ ‖a - b‖ + ‖c‖ + ‖d‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by gcongr; exact norm_sub_le _ _
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖), sq_nonneg (‖a‖ - ‖d‖),
    sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖b‖ - ‖d‖), sq_nonneg (‖c‖ - ‖d‖)]

/-- The partial sums of `Σ 1/p` are not bounded. -/
theorem not_bounded_sum_primes_inv (R : ℝ) :
    ¬ ∀ N : ℕ, ∑ p ∈ N.primesBelow, (1 : ℝ) / p ≤ R := by
  intro h
  refine not_summable_one_div_on_primes (summable_of_sum_range_le (c := R) (fun n => ?_) fun n => ?_)
  · exact Set.indicator_nonneg (fun m _ => by positivity) n
  · refine le_trans (le_of_eq ?_) (h n)
    unfold Nat.primesBelow
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : m.Prime
    · simp [hm]
    · simp [hm]

/-! ### Lacunary families -/

section Lacunary

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem integrable_of_bound {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] {f : Ω → F} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, ‖f ω‖ ≤ C) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall hC)

/-- **Bessel.** An orthonormal family of bounded measurable functions has correlations with a set of square sum at most its measure. -/
theorem bessel_of_orthonormal {ι : Type*} [DecidableEq ι] (T : Finset ι) {f : ι → Ω → ℂ}
    (hf : ∀ β, Measurable (f β)) (hb : ∀ β ω, ‖f β ω‖ ≤ 1)
    (horth : ∀ β ∈ T, ∀ γ ∈ T, ∫ ω, f β ω * conj (f γ ω) ∂μ = if β = γ then 1 else 0)
    (E : Set Ω) :
    ∑ β ∈ T, ‖∫ ω in E, f β ω ∂μ‖ ^ 2 ≤ (μ E).toReal := by
  set c : ι → ℂ := fun β => ∫ ω in E, f β ω ∂μ with hc
  set k : Ω → ℂ := fun ω => ∑ β ∈ T, conj (c β) * f β ω with hk
  have hkm : Measurable k := Finset.measurable_sum _ fun β _ => measurable_const.mul (hf β)
  set A : ℝ := ∑ β ∈ T, ‖c β‖ ^ 2 with hA
  have hfi : ∀ β, Integrable (f β) μ := fun β => integrable_of_bound (hf β) (hb β)
  have hkb : ∀ ω, ‖k ω‖ ≤ ∑ β ∈ T, ‖c β‖ := fun ω =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_of_le_one_right (norm_nonneg _) (hb β ω))
  have hki : Integrable k μ := integrable_of_bound hkm hkb
  -- The set integral of `k` is `A`.
  have hEk : ∫ ω in E, k ω ∂μ = (A : ℂ) := by
    simp only [hk]
    rw [integral_finsetSum _ fun β _ => ((hfi β).const_mul _).integrableOn]
    rw [hA]
    push_cast
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [integral_const_mul, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  -- The full integral of `|k|²` is `A`.
  have hfull : ∫ ω, ‖k ω‖ ^ 2 ∂μ = A := by
    have hexp : ∀ ω, ((‖k ω‖ ^ 2 : ℝ) : ℂ) = ∑ β ∈ T, ∑ γ ∈ T,
        conj (c β) * c γ * (f β ω * conj (f γ ω)) := by
      intro ω
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
      simp only [hk, map_sum, map_mul, Complex.conj_conj]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun γ _ => ?_
      ring
    have hi : ∀ β γ : ι, Integrable (fun ω => conj (c β) * c γ * (f β ω * conj (f γ ω))) μ :=
      fun β γ => integrable_of_bound
        (measurable_const.mul ((hf β).mul (Complex.continuous_conj.measurable.comp (hf γ))))
        (C := ‖c β‖ * ‖c γ‖) fun ω => by
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
          have h1 := hb β ω
          have h2 := hb γ ω
          have : ‖f β ω‖ * ‖f γ ω‖ ≤ 1 := by
            nlinarith [norm_nonneg (f β ω), norm_nonneg (f γ ω)]
          nlinarith [norm_nonneg (c β), norm_nonneg (c γ), mul_nonneg (norm_nonneg (c β)) (norm_nonneg (c γ))]
    have hcx : ((∫ ω, ‖k ω‖ ^ 2 ∂μ : ℝ) : ℂ) = (A : ℂ) := by
      rw [← integral_complex_ofReal]
      simp_rw [hexp]
      rw [integral_finsetSum _ fun β _ => integrable_finsetSum _ fun γ _ => hi β γ]
      rw [hA]
      push_cast
      refine Finset.sum_congr rfl fun β hβ => ?_
      rw [integral_finsetSum _ fun γ _ => hi β γ]
      have hterm : ∀ γ ∈ T, ∫ ω, conj (c β) * c γ * (f β ω * conj (f γ ω)) ∂μ =
          if γ = β then conj (c β) * c γ else 0 := by
        intro γ hγ
        rw [integral_const_mul, horth β hβ γ hγ]
        by_cases h : γ = β
        · simp [h]
        · simp [h, Ne.symm h]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' T β, if_pos hβ, mul_comm, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
      push_cast
      rfl
    exact_mod_cast hcx
  -- `|k|² ≥ 2 Re k − 1` on `E`.
  have hint2 : Integrable (fun ω => ‖k ω‖ ^ 2) μ :=
    integrable_of_bound (hkm.norm.pow_const 2) (C := (∑ β ∈ T, ‖c β‖) ^ 2) fun ω => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hkb ω) 2
  have hset : ∫ ω in E, ‖k ω‖ ^ 2 ∂μ ≤ A := by
    rw [← hfull]
    exact setIntegral_le_integral hint2 (Eventually.of_forall fun ω => by positivity)
  have hint3 : Integrable (fun ω => (k ω).re) μ := hki.re
  have hre : ∫ ω in E, (k ω).re ∂μ = A := by
    have h1 : ∫ ω in E, (k ω).re ∂μ = (∫ ω in E, k ω ∂μ).re :=
      Complex.reCLM.integral_comp_comm hki.integrableOn
    rw [h1, hEk, Complex.ofReal_re]
  have h2 : Integrable (fun ω => 2 * (k ω).re - 1) μ := (hint3.const_mul 2).sub (integrable_const 1)
  have hmono : ∫ ω in E, (2 * (k ω).re - 1) ∂μ ≤ ∫ ω in E, ‖k ω‖ ^ 2 ∂μ := by
    refine setIntegral_mono h2.integrableOn hint2.integrableOn fun ω => ?_
    have h3 : ‖k ω‖ ^ 2 = (k ω).re ^ 2 + (k ω).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    simp only
    nlinarith [sq_nonneg ((k ω).re - 1), sq_nonneg (k ω).im]
  have hval : ∫ ω in E, (2 * (k ω).re - 1) ∂μ = 2 * A - (μ E).toReal := by
    rw [integral_sub (hint3.const_mul 2).integrableOn (integrable_const 1).integrableOn,
      integral_const_mul, hre, setIntegral_const]
    simp [Measure.real]
  linarith

/-- A family of random variables on the primes that behaves like a lacunary series: unimodular, orthonormal, and with pair products whose correlations with any set have square sum at most twice its measure. -/
structure IsLacunary (μ : Measure Ω) (x : ℕ → Ω → ℂ) : Prop where
  measurable : ∀ n, Measurable (x n)
  norm_eq_one : ∀ p, p.Prime → ∀ ω, ‖x p ω‖ = 1
  integral_normSq : ∀ (s : Finset ℕ) (a : ℕ → ℂ), (∀ n ∈ s, n.Prime) →
    ∫ ω, ‖∑ n ∈ s, a n * x n ω‖ ^ 2 ∂μ = ∑ n ∈ s, ‖a n‖ ^ 2
  bessel : ∀ (E : Set Ω) (Ps : Finset ℕ), (∀ p ∈ Ps, p.Prime) →
    ∑ α ∈ Ps.offDiag, ‖∫ ω in E, x α.1 ω * conj (x α.2 ω) ∂μ‖ ^ 2 ≤ 2 * (μ E).toReal

variable {x : ℕ → Ω → ℂ}

/-- The correlation `∫_E x_p conj x_q` of a set with a pair product. -/
def corrOf (μ : Measure Ω) (x : ℕ → Ω → ℂ) (E : Set Ω) (α : ℕ × ℕ) : ℂ :=
  ∫ ω in E, x α.1 ω * conj (x α.2 ω) ∂μ

/-- The partial sum `Σ_{p<N} x_p p^{−s}`. -/
def primeSumOf (x : ℕ → Ω → ℂ) (N : ℕ) (s : ℂ) (ω : Ω) : ℂ := ∑ p ∈ N.primesBelow, powCoeff s p * x p ω

theorem IsLacunary.measurable_primeSumOf (hx : IsLacunary μ x) (N : ℕ) (s : ℂ) : Measurable (primeSumOf x N s) :=
  Finset.measurable_sum _ fun p _ => measurable_const.mul (hx.measurable p)

theorem IsLacunary.norm_sum_mul_le (hx : IsLacunary μ x) {s : Finset ℕ} (hs : ∀ n ∈ s, n.Prime) (a : ℕ → ℂ)
    (ω : Ω) : ‖∑ n ∈ s, a n * x n ω‖ ≤ ∑ n ∈ s, ‖a n‖ :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => by
    rw [norm_mul, hx.norm_eq_one n (hs n hn), mul_one])

theorem IsLacunary.norm_primeSumOf_le (hx : IsLacunary μ x) (P : ℕ) {s : ℂ} (hs : 0 < s.re) (ω : Ω) :
    ‖primeSumOf x P s ω‖ ≤ (P.primesBelow.card : ℝ) := by
  unfold primeSumOf
  calc
    ‖∑ p ∈ P.primesBelow, powCoeff s p * x p ω‖ ≤ ∑ p ∈ P.primesBelow, ‖powCoeff s p‖ :=
      hx.norm_sum_mul_le (fun p hp => (Nat.mem_primesBelow.mp hp).2) _ ω
    _ ≤ ∑ _p ∈ P.primesBelow, (1 : ℝ) := Finset.sum_le_sum fun p hp =>
      norm_powCoeff_le_one (Nat.mem_primesBelow.mp hp).2.pos hs.le
    _ = (P.primesBelow.card : ℝ) := by simp

/-- **The off-diagonal is small.** If the correlations of `E` with the pair products of `Ps` have square sum at most `τ²`, then `∫_E |Σ a_p x_p|² ≥ (|E| − τ) Σ |a_p|²`. -/
theorem IsLacunary.le_setIntegral_normSq (hx : IsLacunary μ x) {E : Set Ω} (Ps : Finset ℕ)
    (hPs : ∀ p ∈ Ps, p.Prime) (a : ℕ → ℂ) {τ : ℝ} (hτ0 : 0 ≤ τ)
    (hτ : ∑ α ∈ Ps.offDiag, ‖corrOf μ x E α‖ ^ 2 ≤ τ ^ 2) :
    ((μ E).toReal - τ) * ∑ p ∈ Ps, ‖a p‖ ^ 2 ≤ ∫ ω in E, ‖∑ p ∈ Ps, a p * x p ω‖ ^ 2 ∂μ := by
  classical
  set A : ℝ := ∑ p ∈ Ps, ‖a p‖ ^ 2 with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => by positivity
  have hexp : ∀ ω, ((‖∑ p ∈ Ps, a p * x p ω‖ ^ 2 : ℝ) : ℂ) =
      ∑ α ∈ Ps ×ˢ Ps, a α.1 * conj (a α.2) * (x α.1 ω * conj (x α.2 ω)) := by
    intro ω
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum,
      Finset.sum_product]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    simp only [map_mul]
    ring
  have hi : ∀ α ∈ Ps ×ˢ Ps, Integrable (fun ω => a α.1 * conj (a α.2) * (x α.1 ω * conj (x α.2 ω))) μ := by
    intro α hα
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hα
    refine integrable_of_bound (measurable_const.mul ((hx.measurable _).mul
      (Complex.continuous_conj.measurable.comp (hx.measurable _)))) (C := ‖a α.1‖ * ‖a α.2‖) fun ω => ?_
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj,
      hx.norm_eq_one _ (hPs _ h1), hx.norm_eq_one _ (hPs _ h2), mul_one, mul_one]
  have hset : ((∫ ω in E, ‖∑ p ∈ Ps, a p * x p ω‖ ^ 2 ∂μ : ℝ) : ℂ) =
      ∑ α ∈ Ps ×ˢ Ps, a α.1 * conj (a α.2) * corrOf μ x E α := by
    rw [← integral_complex_ofReal]
    simp_rw [hexp]
    rw [integral_finsetSum _ fun α hα => (hi α hα).integrableOn]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [integral_const_mul]
    rfl
  -- Split into the diagonal and the rest.
  rw [← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag _)] at hset
  have hdiag : ∑ α ∈ Ps.diag, a α.1 * conj (a α.2) * corrOf μ x E α =
      ((A * (μ E).toReal : ℝ) : ℂ) := by
    rw [Finset.sum_diag, hA]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hc : corrOf μ x E (p, p) = ((μ E).toReal : ℂ) := by
      unfold corrOf
      have h1 : ∀ ω, x p ω * conj (x p ω) = 1 := fun ω => by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hx.norm_eq_one p (hPs p hp)]
        simp
      simp only [h1]
      rw [setIntegral_const]
      simp [Measure.real]
    rw [hc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  -- The off-diagonal, by Cauchy–Schwarz.
  set O : ℂ := ∑ α ∈ Ps.offDiag, a α.1 * conj (a α.2) * corrOf μ x E α with hO
  have hOnorm : ‖O‖ ≤ A * τ := by
    have h1 : ‖O‖ ≤ ∑ α ∈ Ps.offDiag, (‖a α.1‖ * ‖a α.2‖) * ‖corrOf μ x E α‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
      rw [norm_mul, norm_mul, Complex.norm_conj]
    have h2 : (∑ α ∈ Ps.offDiag, (‖a α.1‖ * ‖a α.2‖) * ‖corrOf μ x E α‖) ^ 2 ≤
        (∑ α ∈ Ps.offDiag, (‖a α.1‖ * ‖a α.2‖) ^ 2) * ∑ α ∈ Ps.offDiag, ‖corrOf μ x E α‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h3 : ∑ α ∈ Ps.offDiag, (‖a α.1‖ * ‖a α.2‖) ^ 2 ≤ A ^ 2 := by
      have hsub : Ps.offDiag ⊆ Ps ×ˢ Ps := fun α hα =>
        Finset.mem_product.mpr ⟨(Finset.mem_offDiag.mp hα).1, (Finset.mem_offDiag.mp hα).2.1⟩
      refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans (le_of_eq ?_)
      rw [Finset.sum_product, hA, sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    have h4 : (∑ α ∈ Ps.offDiag, (‖a α.1‖ * ‖a α.2‖) * ‖corrOf μ x E α‖) ^ 2 ≤ (A * τ) ^ 2 := by
      refine h2.trans ?_
      rw [mul_pow]
      exact mul_le_mul h3 hτ (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
    have h5 := abs_le_of_sq_le_sq' h4 (by positivity)
    exact h1.trans h5.2
  have hre := congrArg Complex.re hset
  rw [Complex.ofReal_re, Complex.add_re, hdiag, Complex.ofReal_re] at hre
  rw [hre]
  have h6 := Complex.abs_re_le_norm O
  have h7 : -(A * τ) ≤ O.re := by
    have := (abs_le.mp (h6.trans hOnorm)).1
    linarith
  nlinarith

/-- **Fatou for orthogonal sums.** The a.e. limit of prime sums has square integral at most the bound on the coefficient sums. -/
theorem IsLacunary.lintegral_normSq_limit_le_of (hx : IsLacunary μ x) {s : ℕ → Finset ℕ}
    (hs : ∀ N, ∀ n ∈ s N, n.Prime) (a : ℕ → ℂ) {B : ℝ} (hB : ∀ N, ∑ n ∈ s N, ‖a n‖ ^ 2 ≤ B)
    {g : Ω → ℂ} (hg : ∀ᵐ ω ∂μ, Tendsto (fun N => ∑ n ∈ s N, a n * x n ω) atTop (𝓝 (g ω))) :
    ∫⁻ ω, ENNReal.ofReal (‖g ω‖ ^ 2) ∂μ ≤ ENNReal.ofReal B := by
  set f : ℕ → Ω → ENNReal := fun N ω => ENNReal.ofReal (‖∑ n ∈ s N, a n * x n ω‖ ^ 2) with hf
  have hm : ∀ N, Measurable fun ω => ‖∑ n ∈ s N, a n * x n ω‖ ^ 2 := fun N =>
    (Finset.measurable_sum _ fun n _ => measurable_const.mul (hx.measurable n)).norm.pow_const 2
  have hmeas : ∀ N, Measurable (f N) := fun N => ENNReal.measurable_ofReal.comp (hm N)
  have hae : (fun ω => ENNReal.ofReal (‖g ω‖ ^ 2)) =ᵐ[μ] fun ω => liminf (fun N => f N ω) atTop := by
    filter_upwards [hg] with ω hω
    exact (ENNReal.tendsto_ofReal (hω.norm.pow 2)).liminf_eq.symm
  rw [lintegral_congr_ae hae]
  refine (lintegral_liminf_le hmeas).trans ?_
  refine liminf_le_of_frequently_le' (Frequently.of_forall fun N => ?_)
  have hint : Integrable (fun ω => ‖∑ n ∈ s N, a n * x n ω‖ ^ 2) μ :=
    integrable_of_bound (hm N) (C := (∑ n ∈ s N, ‖a n‖) ^ 2) fun ω => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hx.norm_sum_mul_le (hs N) a ω) 2
  rw [show (∫⁻ ω, f N ω ∂μ) = ENNReal.ofReal (∫ ω, ‖∑ n ∈ s N, a n * x n ω‖ ^ 2 ∂μ) from
    (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω => by positivity)).symm,
    hx.integral_normSq (s N) a (hs N)]
  exact ENNReal.ofReal_le_ofReal (hB N)

/-- The correlations of a set with the pair products of large primes are small in square sum. -/
theorem IsLacunary.exists_tail_corr_small (hx : IsLacunary μ x) (E : Set Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℕ, ∀ Ps : Finset ℕ, (∀ p ∈ Ps, p.Prime ∧ P ≤ p) →
      ∑ α ∈ Ps.offDiag, ‖corrOf μ x E α‖ ^ 2 ≤ ε := by
  classical
  set f : ℕ × ℕ → ℝ := fun α => if α.1.Prime ∧ α.2.Prime ∧ α.1 ≠ α.2 then ‖corrOf μ x E α‖ ^ 2 else 0
    with hf
  have hf0 : ∀ α, 0 ≤ f α := fun α => by
    simp only [hf]
    split_ifs
    · positivity
    · exact le_rfl
  have hsum : Summable f := by
    refine summable_of_sum_le hf0 (c := 2 * (μ E).toReal) fun u => ?_
    set v := u.filter fun α => α.1.Prime ∧ α.2.Prime ∧ α.1 ≠ α.2 with hv
    set Ps : Finset ℕ := v.image Prod.fst ∪ v.image Prod.snd with hPs
    have h1 : ∑ α ∈ u, f α = ∑ α ∈ v, ‖corrOf μ x E α‖ ^ 2 := by
      rw [hv, Finset.sum_filter]
    have hsub : v ⊆ Ps.offDiag := fun α hα => by
      obtain ⟨-, h2, h3, h4⟩ := Finset.mem_filter.mp hα
      exact Finset.mem_offDiag.mpr ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hα),
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ hα), h4⟩
    have hprime : ∀ p ∈ Ps, p.Prime := fun p hp => by
      rcases Finset.mem_union.mp hp with h | h
      · obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp h
        exact (Finset.mem_filter.mp hα).2.1
      · obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp h
        exact (Finset.mem_filter.mp hα).2.2.1
    rw [h1]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans
      (hx.bessel E Ps hprime)
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hsum ε hε
  refine ⟨s.sup (fun α => α.1) + 1, fun Ps hPs => ?_⟩
  have hdisj : Disjoint Ps.offDiag s := by
    rw [Finset.disjoint_left]
    intro α hα hαs
    have h1 := (Finset.mem_offDiag.mp hα).1
    have h2 := (hPs _ h1).2
    have h3 : α.1 ≤ s.sup (fun α => α.1) := Finset.le_sup (f := fun α : ℕ × ℕ => α.1) hαs
    omega
  have h := hs _ hdisj
  have h1 : ∑ α ∈ Ps.offDiag, f α = ∑ α ∈ Ps.offDiag, ‖corrOf μ x E α‖ ^ 2 := by
    refine Finset.sum_congr rfl fun α hα => ?_
    obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.mp hα
    simp only [hf]
    rw [if_pos ⟨(hPs _ h1).1, (hPs _ h2).1, h3⟩]
  rw [h1, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)] at h
  exact h.le

/-- The square integral of the remainder of a prime sum. -/
theorem IsLacunary.lintegral_sub_primeSumOf_le (hx : IsLacunary μ x) {s : ℂ} {T : ℝ}
    (hT : ∀ N : ℕ, ∑ p ∈ N.primesBelow, (p : ℝ) ^ (-(2 * s.re)) ≤ T)
    {g : Ω → ℂ} (hg : ∀ᵐ ω ∂μ, Tendsto (fun N => primeSumOf x N s ω) atTop (𝓝 (g ω))) (N : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (‖g ω - primeSumOf x N s ω‖ ^ 2) ∂μ ≤
      ENNReal.ofReal (T - ∑ p ∈ N.primesBelow, (p : ℝ) ^ (-(2 * s.re))) := by
  classical
  have hsub : ∀ K, N.primesBelow ⊆ (N + K).primesBelow := fun K => primesBelow_subset (by omega)
  refine hx.lintegral_normSq_limit_le_of (s := fun K => (N + K).primesBelow \ N.primesBelow)
    (a := powCoeff s) (fun K n hn => (Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hn).1).2)
    (fun K => ?_) ?_
  · have h1 : ∑ n ∈ (N + K).primesBelow \ N.primesBelow, ‖powCoeff s n‖ ^ 2 =
        ∑ n ∈ (N + K).primesBelow, ‖powCoeff s n‖ ^ 2 - ∑ n ∈ N.primesBelow, ‖powCoeff s n‖ ^ 2 := by
      rw [← Finset.sum_sdiff (hsub K)]
      ring
    have h2 : ∀ L : ℕ, ∑ n ∈ L.primesBelow, ‖powCoeff s n‖ ^ 2 =
        ∑ p ∈ L.primesBelow, (p : ℝ) ^ (-(2 * s.re)) :=
      fun L => Finset.sum_congr rfl fun p hp => norm_powCoeff_sq (Nat.mem_primesBelow.mp hp).2.pos s
    rw [h1, h2, h2]
    linarith [hT (N + K)]
  · filter_upwards [hg] with ω hω
    have h1 : Tendsto (fun K => primeSumOf x (K + N) s ω) atTop (𝓝 (g ω)) :=
      (tendsto_add_atTop_iff_nat N).mpr hω
    have h2 := h1.sub_const (primeSumOf x N s ω)
    refine h2.congr fun K => ?_
    unfold primeSumOf
    rw [add_comm K N, ← Finset.sum_sdiff (hsub K)]
    ring

/-- The set integral of a function dominated by two functions bounded in `L¹`, and a constant. -/
theorem setLIntegral_ofReal_le {E : Set Ω} {f r e : Ω → ℝ} {c B₁ B₂ : ℝ}
    (hc : 0 ≤ c) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hr0 : ∀ ω, 0 ≤ r ω) (he0 : ∀ ω, 0 ≤ e ω)
    (hrm : AEMeasurable r μ)
    (hf : ∀ᵐ ω ∂μ.restrict E, f ω ≤ 4 * r ω + 4 * e ω + c)
    (hr : ∫⁻ ω, ENNReal.ofReal (r ω) ∂μ ≤ ENNReal.ofReal B₁)
    (he : ∫⁻ ω, ENNReal.ofReal (e ω) ∂μ ≤ ENNReal.ofReal B₂) :
    ∫⁻ ω in E, ENNReal.ofReal (f ω) ∂μ ≤ ENNReal.ofReal (4 * B₁ + 4 * B₂ + c) := by
  have h4 : ENNReal.ofReal 4 ≠ ⊤ := ENNReal.ofReal_ne_top
  have hE1 : μ E ≤ 1 := prob_le_one
  calc
    ∫⁻ ω in E, ENNReal.ofReal (f ω) ∂μ
        ≤ ∫⁻ ω in E, (ENNReal.ofReal 4 * ENNReal.ofReal (r ω) + ENNReal.ofReal 4 * ENNReal.ofReal (e ω) +
            ENNReal.ofReal c) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hf] with ω hω
          have hr1 := hr0 ω
          have he1 := he0 ω
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) hc]
          exact ENNReal.ofReal_le_ofReal hω
    _ = ∫⁻ ω in E, (ENNReal.ofReal 4 * ENNReal.ofReal (r ω) + ENNReal.ofReal 4 * ENNReal.ofReal (e ω)) ∂μ +
          ENNReal.ofReal c * μ E := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    _ ≤ ∫⁻ ω, (ENNReal.ofReal 4 * ENNReal.ofReal (r ω) + ENNReal.ofReal 4 * ENNReal.ofReal (e ω)) ∂μ +
          ENNReal.ofReal c * 1 := by
          exact add_le_add (setLIntegral_le_lintegral _ _) (by gcongr)
    _ = ENNReal.ofReal 4 * ∫⁻ ω, ENNReal.ofReal (r ω) ∂μ +
          ENNReal.ofReal 4 * ∫⁻ ω, ENNReal.ofReal (e ω) ∂μ + ENNReal.ofReal c := by
          rw [lintegral_add_left' (hrm.ennreal_ofReal.const_mul _), lintegral_const_mul' _ _ h4,
            lintegral_const_mul' _ _ h4, mul_one]
    _ ≤ ENNReal.ofReal 4 * ENNReal.ofReal B₁ + ENNReal.ofReal 4 * ENNReal.ofReal B₂ + ENNReal.ofReal c := by
          gcongr
    _ = ENNReal.ofReal (4 * B₁ + 4 * B₂ + c) := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) hc]

/-- **Zygmund's theorem for lacunary families.** Let `Re s_j → ½` from the right. The sums `Σ_p p^{−s_j} x_p`, perturbed by functions bounded in `L²` uniformly in `j`, stay bounded only on a null set. -/
theorem IsLacunary.measure_bounded_primeSumOf_eq_zero (hx : IsLacunary μ x) {s : ℕ → ℂ}
    (hs : ∀ j, 1 / 2 < (s j).re) (hlim : Tendsto (fun j => (s j).re) atTop (𝓝 (1 / 2)))
    {g e : ℕ → Ω → ℂ}
    (hg : ∀ j, ∀ᵐ ω ∂μ, Tendsto (fun N => primeSumOf x N (s j) ω) atTop (𝓝 (g j ω)))
    (he : ∀ j, AEMeasurable (e j) μ) {C : ℝ} (hC0 : 0 ≤ C)
    (heL : ∀ j, ∫⁻ ω, ENNReal.ofReal (‖e j ω‖ ^ 2) ∂μ ≤ ENNReal.ofReal C) (M : ℝ) (J : ℕ) :
    μ {ω | ∀ j, J ≤ j → ‖g j ω + e j ω‖ ≤ M} = 0 := by
  classical
  have hgm : ∀ j, AEMeasurable (g j) μ := fun j =>
    aemeasurable_of_tendsto_metrizable_ae atTop
      (fun N => (hx.measurable_primeSumOf N (s j)).aemeasurable) (hg j)
  -- A measurable set carrying the bound.
  set v : ℕ → Ω → ℂ := fun j => ((hgm j).add (he j)).mk _ with hv
  have hvm : ∀ j, Measurable (v j) := fun j => ((hgm j).add (he j)).measurable_mk
  have hve : ∀ᵐ ω ∂μ, ∀ j, g j ω + e j ω = v j ω :=
    ae_all_iff.mpr fun j => ((hgm j).add (he j)).ae_eq_mk
  set E : Set Ω := ⋂ j, ⋂ (_ : J ≤ j), {ω | ‖v j ω‖ ≤ M} with hE
  have hEm : MeasurableSet E := MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_le (hvm j).norm measurable_const
  have hsub : {ω | ∀ j, J ≤ j → ‖g j ω + e j ω‖ ≤ M} ≤ᵐ[μ] E := by
    filter_upwards [hve] with ω hω hZ
    show ω ∈ E
    refine Set.mem_iInter.mpr fun j => Set.mem_iInter.mpr fun hj => ?_
    show ‖v j ω‖ ≤ M
    rw [← hω j]
    exact hZ j hj
  refine le_antisymm ((measure_mono_ae hsub).trans (le_of_eq ?_)) zero_le
  by_contra hne
  set m : ℝ := (μ E).toReal with hm
  have hm0 : 0 < m := ENNReal.toReal_pos hne (measure_ne_top _ _)
  obtain ⟨P, hP⟩ := hx.exists_tail_corr_small E (ε := (m / 2) ^ 2) (by positivity)
  set S : ℕ → ℕ → ℝ := fun j N => ∑ p ∈ N.primesBelow, (p : ℝ) ^ (-(2 * (s j).re)) with hS
  set T : ℕ → ℝ := fun j => ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(2 * (s j).re)) with hT
  set K : ℝ := (P.primesBelow.card : ℝ) with hK
  have hsumm : ∀ j, Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(2 * (s j).re)) := fun j =>
    Nat.Primes.summable_rpow.mpr (by linarith [hs j])
  have hST : ∀ j N, S j N ≤ T j := fun j N =>
    sum_primesBelow_le_tsum (g := fun p : ℕ => (p : ℝ) ^ (-(2 * (s j).re)))
      (fun p => by positivity) (hsumm j) N
  have hSmono : ∀ j, Monotone (S j) := fun j a b hab =>
    Finset.sum_le_sum_of_subset_of_nonneg (primesBelow_subset hab) fun p _ _ => by positivity
  have hSlim : ∀ j, Tendsto (S j) atTop (𝓝 (T j)) := fun j =>
    tendsto_sum_primesBelow (g := fun p : ℕ => (p : ℝ) ^ (-(2 * (s j).re))) (hsumm j)
  -- The main inequality, for one exponent.
  have key : ∀ j, J ≤ j → ∀ N, P ≤ N →
      (m / 2) * (S j N - S j P) ≤ 4 * (T j - S j N) + 4 * C + (4 * M ^ 2 + 4 * K ^ 2) := by
    intro j hj N hPN
    set Ps : Finset ℕ := N.primesBelow \ P.primesBelow with hPs
    have hPs' : ∀ p ∈ Ps, p.Prime ∧ P ≤ p := by
      intro p hp
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hp
      have h3 := Nat.mem_primesBelow.mp h1
      refine ⟨h3.2, ?_⟩
      by_contra h4
      exact h2 (Nat.mem_primesBelow.mpr ⟨by omega, h3.2⟩)
    have h1 := hx.le_setIntegral_normSq (E := E) Ps (fun p hp => (hPs' p hp).1) (powCoeff (s j))
      (τ := m / 2) (by positivity) (hP Ps hPs')
    have hsumPs : ∑ p ∈ Ps, ‖powCoeff (s j) p‖ ^ 2 = S j N - S j P := by
      rw [Finset.sum_congr rfl fun p hp => norm_powCoeff_sq (hPs' p hp).1.pos (s j)]
      exact Finset.sum_sdiff_eq_sub (primesBelow_subset hPN)
    rw [hsumPs] at h1
    have hAm : Measurable fun ω => ‖∑ p ∈ Ps, powCoeff (s j) p * x p ω‖ ^ 2 :=
      (Finset.measurable_sum _ fun p _ => measurable_const.mul (hx.measurable p)).norm.pow_const 2
    have hAi : Integrable (fun ω => ‖∑ p ∈ Ps, powCoeff (s j) p * x p ω‖ ^ 2) μ :=
      integrable_of_bound hAm (C := (∑ p ∈ Ps, ‖powCoeff (s j) p‖) ^ 2) fun ω => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _)
          (hx.norm_sum_mul_le (fun p hp => (hPs' p hp).1) _ ω) 2
    have h2 : ENNReal.ofReal (∫ ω in E, ‖∑ p ∈ Ps, powCoeff (s j) p * x p ω‖ ^ 2 ∂μ) =
        ∫⁻ ω in E, ENNReal.ofReal (‖∑ p ∈ Ps, powCoeff (s j) p * x p ω‖ ^ 2) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hAi.integrableOn
        (Eventually.of_forall fun ω => by positivity)
    have hrm : AEMeasurable (fun ω => ‖g j ω - primeSumOf x N (s j) ω‖ ^ 2) μ :=
      (((hgm j).sub (hx.measurable_primeSumOf N (s j)).aemeasurable).norm).pow_const 2
    have h3 := setLIntegral_ofReal_le (E := E)
      (f := fun ω => ‖∑ p ∈ Ps, powCoeff (s j) p * x p ω‖ ^ 2)
      (r := fun ω => ‖g j ω - primeSumOf x N (s j) ω‖ ^ 2) (e := fun ω => ‖e j ω‖ ^ 2)
      (c := 4 * M ^ 2 + 4 * K ^ 2) (B₁ := T j - S j N) (B₂ := C) (by positivity)
      (by linarith [hST j N]) hC0 (fun ω => by positivity) (fun ω => by positivity) hrm ?_
      (hx.lintegral_sub_primeSumOf_le (hST j) (hg j) N) (heL j)
    · rw [← h2] at h3
      have h4 := (ENNReal.ofReal_le_ofReal_iff (by
        have := hST j N
        nlinarith [sq_nonneg M, sq_nonneg K])).mp h3
      have h5 : (μ E).toReal - m / 2 = m / 2 := by
        rw [← hm]
        ring
      rw [h5] at h1
      linarith
    · filter_upwards [ae_restrict_mem hEm, ae_restrict_of_ae hve] with ω hωE hω
      have hb : ‖v j ω‖ ≤ M := Set.mem_iInter.mp (Set.mem_iInter.mp hωE j) hj
      have hb2 : ‖v j ω‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      have hq2 : ‖primeSumOf x P (s j) ω‖ ^ 2 ≤ K ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hx.norm_primeSumOf_le P (by linarith [hs j]) ω) 2
      have hsplit : ∑ p ∈ Ps, powCoeff (s j) p * x p ω =
          v j ω - e j ω - primeSumOf x P (s j) ω - (g j ω - primeSumOf x N (s j) ω) := by
        have h6 : primeSumOf x N (s j) ω =
            (∑ p ∈ Ps, powCoeff (s j) p * x p ω) + primeSumOf x P (s j) ω := by
          unfold primeSumOf
          exact (Finset.sum_sdiff (primesBelow_subset hPN)).symm
        rw [← hω j, h6]
        ring
      rw [hsplit]
      have h7 := norm_sub_sub_sub_sq_le (v j ω) (e j ω) (primeSumOf x P (s j) ω)
        (g j ω - primeSumOf x N (s j) ω)
      nlinarith
  -- Let the exponent go to `½`.
  have hD : ∀ j, J ≤ j → ∀ N, S j N - S j P ≤ (2 / m) * (4 + 4 * C + (4 * M ^ 2 + 4 * K ^ 2)) := by
    intro j hj N
    have hev : ∀ᶠ N' in atTop, T j - S j N' < 1 := by
      have h1 : Tendsto (fun N' => T j - S j N') atTop (𝓝 (T j - T j)) := (hSlim j).const_sub _
      rw [sub_self] at h1
      exact h1.eventually (gt_mem_nhds one_pos)
    obtain ⟨N', hN1, hN2⟩ := (hev.and (eventually_ge_atTop (max N P))).exists
    have h2 := key j hj N' (le_trans (le_max_right _ _) hN2)
    have h3 := hSmono j (le_trans (le_max_left _ _) hN2)
    have h4 : (m / 2) * (S j N - S j P) ≤ 4 + 4 * C + (4 * M ^ 2 + 4 * K ^ 2) := by
      have h5 : (m / 2) * (S j N - S j P) ≤ (m / 2) * (S j N' - S j P) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hm0]
    nlinarith
  have hLim : ∀ N : ℕ, Tendsto (fun j => S j N) atTop (𝓝 (∑ p ∈ N.primesBelow, (1 : ℝ) / p)) := by
    intro N
    refine tendsto_finsetSum _ fun p hp => ?_
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.ne_zero
    have h1 : Tendsto (fun j => (p : ℝ) ^ (-(2 * (s j).re))) atTop
        (𝓝 ((p : ℝ) ^ (-(2 * (1 / 2 : ℝ))))) :=
      (Real.continuousAt_const_rpow hp0).tendsto.comp (hlim.const_mul 2).neg
    rwa [show -(2 * (1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one, ← one_div] at h1
  refine not_bounded_sum_primes_inv ((2 / m) * (4 + 4 * C + (4 * M ^ 2 + 4 * K ^ 2)) +
    ∑ p ∈ P.primesBelow, (1 : ℝ) / p) fun N => ?_
  have h1 := le_of_tendsto ((hLim N).sub (hLim P))
    ((eventually_ge_atTop J).mono fun j hj => hD j hj N)
  linarith

end Lacunary

/-! ### The gauge torus -/

/-- The character `x_p conj x_q`. -/
def pairChar (p q : ℕ) (x : GaugeTorus) : ℂ := twist x p * conj (twist x q)

theorem continuous_pairChar (p q : ℕ) : Continuous (pairChar p q) := by
  unfold pairChar
  exact (continuous_twist p).mul (Complex.continuous_conj.comp (continuous_twist q))

theorem norm_pairChar (p q : ℕ) (x : GaugeTorus) : ‖pairChar p q x‖ = 1 := by
  unfold pairChar
  rw [norm_mul, Complex.norm_conj, norm_twist, norm_twist, one_mul]

/-- Unique factorization makes the pair characters orthonormal. -/
theorem integral_pairChar_mul_conj {p q p' q' : ℕ} (hp : p.Prime) (hq : q.Prime) (hp' : p'.Prime)
    (hq' : q'.Prime) (hne : p ≠ q) :
    ∫ x, pairChar p q x * conj (pairChar p' q' x) ∂gaugeHaar =
      if (p, q) = (p', q') then 1 else 0 := by
  have e : ∀ x : GaugeTorus, pairChar p q x * conj (pairChar p' q' x) =
      twist x (p * q') * conj (twist x (q * p')) := by
    intro x
    unfold pairChar
    rw [twist_mul x hp.ne_zero hq'.ne_zero, twist_mul x hq.ne_zero hp'.ne_zero]
    simp only [map_mul, Complex.conj_conj]
    ring
  simp_rw [e]
  rw [integral_twist_mul_conj (Nat.mul_ne_zero hp.ne_zero hq'.ne_zero)
    (Nat.mul_ne_zero hq.ne_zero hp'.ne_zero)]
  congr 1
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : p ∣ q * p' := Dvd.intro _ h
    have h2 : p = p' := by
      rcases (Nat.Prime.dvd_mul hp).mp h1 with h3 | h3
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hq).mp h3) hne
      · exact (Nat.prime_dvd_prime_iff_eq hp hp').mp h3
    subst h2
    have h3 : q' = q := Nat.eq_of_mul_eq_mul_left hp.pos (by rw [h]; ring : p * q' = p * q)
    rw [h3]
  · obtain ⟨h1, h2⟩ := Prod.mk.inj h
    rw [h1, h2]
    ring

/-- **The characters of the gauge torus are lacunary.** -/
theorem isLacunary_twist : IsLacunary gaugeHaar fun n (x : GaugeTorus) => twist x n where
  measurable n := (continuous_twist n).measurable
  norm_eq_one p _ x := norm_twist x p
  integral_normSq s a hs := integral_normSq_twistSum (fun n hn => (hs n hn).ne_zero) a
  bessel E Ps hPs := by
    classical
    have h := bessel_of_orthonormal (μ := gaugeHaar) Ps.offDiag (f := fun α x => pairChar α.1 α.2 x)
      (fun α => (continuous_pairChar α.1 α.2).measurable) (fun α x => (norm_pairChar _ _ x).le)
      (fun β hβ γ hγ => by
        obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.mp hβ
        obtain ⟨h4, h5, -⟩ := Finset.mem_offDiag.mp hγ
        have := integral_pairChar_mul_conj (hPs _ h1) (hPs _ h2) (hPs _ h4) (hPs _ h5) h3
        simpa only [Prod.mk.eta] using this)
      E
    have h0 : 0 ≤ (gaugeHaar E).toReal := ENNReal.toReal_nonneg
    exact h.trans (by linarith)

/-- The partial sum `Σ_{p<N} x_p p^{−s}` on the gauge torus. -/
def primeSum (N : ℕ) (s : ℂ) (x : GaugeTorus) : ℂ := twistSum N.primesBelow (powCoeff s) x

/-- **Fatou for orthogonal sums on the gauge torus.** -/
theorem lintegral_normSq_limit_le {s : ℕ → Finset ℕ} (hs : ∀ N, ∀ n ∈ s N, n ≠ 0) (a : ℕ → ℂ) {B : ℝ}
    (hB : ∀ N, ∑ n ∈ s N, ‖a n‖ ^ 2 ≤ B) {g : GaugeTorus → ℂ}
    (hg : ∀ᵐ x ∂gaugeHaar, Tendsto (fun N => twistSum (s N) a x) atTop (𝓝 (g x))) :
    ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂gaugeHaar ≤ ENNReal.ofReal B := by
  set f : ℕ → GaugeTorus → ENNReal := fun N x => ENNReal.ofReal (‖twistSum (s N) a x‖ ^ 2) with hf
  have hcont : ∀ N, Continuous fun x => ‖twistSum (s N) a x‖ ^ 2 := fun N =>
    (continuous_twistSum (s N) a).norm.pow 2
  have hmeas : ∀ N, Measurable (f N) := fun N => ENNReal.measurable_ofReal.comp (hcont N).measurable
  have hae : (fun x => ENNReal.ofReal (‖g x‖ ^ 2)) =ᵐ[gaugeHaar] fun x => liminf (fun N => f N x) atTop := by
    filter_upwards [hg] with x hx
    exact (ENNReal.tendsto_ofReal (hx.norm.pow 2)).liminf_eq.symm
  rw [lintegral_congr_ae hae]
  refine (lintegral_liminf_le hmeas).trans ?_
  refine liminf_le_of_frequently_le' (Frequently.of_forall fun N => ?_)
  have hint : Integrable (fun x => ‖twistSum (s N) a x‖ ^ 2) gaugeHaar := by
    obtain ⟨C, hC⟩ := isCompact_range (hcont N) |>.isBounded.exists_norm_le
    exact Integrable.of_bound (hcont N).aestronglyMeasurable C (Eventually.of_forall fun x => hC _ ⟨x, rfl⟩)
  rw [show (∫⁻ x, f N x ∂gaugeHaar) = ENNReal.ofReal (∫ x, ‖twistSum (s N) a x‖ ^ 2 ∂gaugeHaar) from
    (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => by positivity)).symm,
    integral_normSq_twistSum (hs N) a]
  exact ENNReal.ofReal_le_ofReal (hB N)

/-- **Zygmund's theorem on the gauge torus.** -/
theorem measure_bounded_prime_sums_eq_zero {s : ℕ → ℂ} (hs : ∀ j, 1 / 2 < (s j).re)
    (hlim : Tendsto (fun j => (s j).re) atTop (𝓝 (1 / 2)))
    {g e : ℕ → GaugeTorus → ℂ}
    (hg : ∀ j, ∀ᵐ x ∂gaugeHaar, Tendsto (fun N => primeSum N (s j) x) atTop (𝓝 (g j x)))
    (he : ∀ j, AEMeasurable (e j) gaugeHaar) {C : ℝ} (hC0 : 0 ≤ C)
    (heL : ∀ j, ∫⁻ x, ENNReal.ofReal (‖e j x‖ ^ 2) ∂gaugeHaar ≤ ENNReal.ofReal C) (M : ℝ) (J : ℕ) :
    gaugeHaar {x | ∀ j, J ≤ j → ‖g j x + e j x‖ ≤ M} = 0 :=
  isLacunary_twist.measure_bounded_primeSumOf_eq_zero hs hlim hg he hC0 heL M J

end

end GaloisForLFunctions.PrimeTorusTheory
