import GaloisForLFunctions.RHTower.ThetaRateMobiusSourceTransfer

/-!
# Boundary examples for the Möbius reconstruction of theta rate measures

* **Gapped class.**  The seed inherits the rate gap, and Euler sums of gapped seeds with finite
  Laplace transform have finite Laplace transform.
* **Finite smooth stages.**  `ν_P = 2π Σ_{n P-smooth} n² δ_{πn²}` keeps the gap `π` and survives
  every deletion by primes of `P`, but for a prime `q ∉ P` the deletion `D_q ν_P` has coefficient
  `-2π q²` at the rate `π q²`.  No finite stage is in the all-sieve cone; the full Euler completion is
  the theta rate measure.
* **The measure `dλ`.**  `A_p(dλ) = dλ`, so every nonempty deletion vanishes although `dλ ≠ 0`; its
  Laplace profile is `1/t`, it has neither a rate gap nor a finite negative moment, infinitely many
  dilations reach the window `(-∞, 1]`, and it is not the Euler reconstruction of any seed.
* **The critical ghost `λ^{1/2} dλ`.**  `A_p` acts by `p⁻¹`, so
  `D_S ν_crit = ∏_{p ∈ S}(1 - 1/p) ν_crit ≥ 0` and `L(t) = Γ(3/2) t^{-3/2}`.  Along every prime
  exhaustion the product tends to zero (divergence of `Σ 1/p`), so cofinal deletion loses the whole
  measure on every window of finite mass; the ghost is not an Euler reconstruction and satisfies
  neither control condition.  Its flux potential `e^{3x} b(e^{2x})` is the nonzero constant
  `Γ(3/2)`, so it is not the flux of any tail-integrable source.
-/
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## Gapped Euler reconstructions -/

/-- In the gapped class the seed inherits the gap. -/
theorem rateMobius_seed_Iio_of_gap {ν ξ : Measure ℝ} (hξ : rateEuler ξ = ν) {l₀ : ℝ}
    (hgap : ν (Iio l₀) = 0) : ξ (Iio l₀) = 0 :=
  le_antisymm ((Measure.le_iff'.1 (hξ ▸ le_rateEuler ξ) _).trans hgap.le) zero_le

/-- **Laplace convergence of gapped Euler sums.**  If `ξ` is carried by `[λ₀, ∞)`, `λ₀ > 0`, and
has finite Laplace transform, so does `Σ_n A_n ξ`: on `λ ≥ λ₀`,
`e^{-n² t λ} ≤ e^{-tλ} e^{-(n²-1) t λ₀}`. -/
theorem rateLaplace_rateEuler_ne_top_of_gap {ξ : Measure ℝ} {l₀ : ℝ} (hl₀ : 0 < l₀)
    (hgap : ξ (Iio l₀) = 0) (hfin : ∀ t, 0 < t → rateLaplace ξ t ≠ ∞) {t : ℝ} (ht : 0 < t) :
    rateLaplace (rateEuler ξ) t ≠ ∞ := by
  have hae : ∀ᵐ l ∂ξ, l₀ ≤ l := by
    rw [ae_iff]
    refine measure_mono_null (fun l hl => ?_) hgap
    simp only [mem_setOf_eq, not_le] at hl
    exact hl
  have hterm : ∀ m : ℕ, (m : ℝ≥0∞) ^ 2 * rateLaplace ξ ((m : ℝ) ^ 2 * t) ≤
      ENNReal.ofReal ((m : ℝ) ^ 2 * Real.exp (-((m : ℝ) ^ 2 - 1) * t * l₀)) * rateLaplace ξ t := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    have hm1 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hm)
    have hL : rateLaplace ξ ((m : ℝ) ^ 2 * t) ≤
        ENNReal.ofReal (Real.exp (-((m : ℝ) ^ 2 - 1) * t * l₀)) * rateLaplace ξ t := by
      rw [rateLaplace, rateLaplace, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono_ae (hae.mono fun l hl => ?_)
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      nlinarith [mul_le_mul_of_nonneg_left hl (mul_nonneg (sub_nonneg.2 hm1) ht.le)]
    calc (m : ℝ≥0∞) ^ 2 * rateLaplace ξ ((m : ℝ) ^ 2 * t) ≤
          (m : ℝ≥0∞) ^ 2 * (ENNReal.ofReal (Real.exp (-((m : ℝ) ^ 2 - 1) * t * l₀)) *
            rateLaplace ξ t) := by gcongr
      _ = _ := by
        rw [← mul_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
  have hsum : Summable fun m : ℕ => (m : ℝ) ^ 2 * Real.exp (-((m : ℝ) ^ 2 - 1) * t * l₀) := by
    refine ((summable_pow_mul_exp_neg_nat_sq 2 (mul_pos ht hl₀)).mul_left
      (Real.exp (t * l₀))).congr fun m => ?_
    rw [mul_left_comm, ← Real.exp_add]
    ring_nf
  rw [rateLaplace_rateEuler]
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
  rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin t ht)

/-- The Euler dilation weights `n²` have finite `q`-mass `Σ n^{2-2q}` exactly for `q > 3/2`; at
`q = 3/2` it is the harmonic series. -/
theorem summable_eulerWeight_iff (q : ℝ) :
    (Summable fun n : ℕ => (n : ℝ) ^ (2 - 2 * q)) ↔ 3 / 2 < q := by
  rw [Real.summable_nat_rpow]
  constructor <;> intro h <;> linarith

/-! ## Single-prime deletions -/

theorem rateDeletionPart_singleton_true (q : ℕ) (ν : Measure ℝ) :
    rateDeletionPart (· ∈ ({q} : Finset ℕ)) true ν = ν := by
  classical
  ext E hE
  rw [rateDeletionPart, Measure.sum_apply _ hE, tsum_eq_single ∅]
  · rw [if_pos ⟨fun p hp => absurd hp (Finset.notMem_empty p), by simp⟩, Finset.prod_empty,
      rateDilate_one]
  · intro T hT
    rw [if_neg]
    · rfl
    rintro ⟨hTq, hpar⟩
    have hsub : T ⊆ {q} := fun p hp => (hTq p hp).2
    rcases Finset.subset_singleton_iff.1 hsub with rfl | rfl
    · exact hT rfl
    · simp at hpar
  
theorem rateDeletionPart_singleton_false {q : ℕ} (hq : q.Prime) (ν : Measure ℝ) :
    rateDeletionPart (· ∈ ({q} : Finset ℕ)) false ν = rateDilate q ν := by
  classical
  ext E hE
  rw [rateDeletionPart, Measure.sum_apply _ hE, tsum_eq_single {q}]
  · rw [if_pos ⟨fun p hp => ⟨Finset.mem_singleton.1 hp ▸ hq, hp⟩, by simp⟩,
      Finset.prod_singleton]
  · intro T hT
    rw [if_neg]
    · rfl
    rintro ⟨hTq, hpar⟩
    have hsub : T ⊆ {q} := fun p hp => (hTq p hp).2
    rcases Finset.subset_singleton_iff.1 hsub with rfl | rfl
    · simp at hpar
    · exact hT rfl

/-! ## Finite smooth-number stages -/

theorem le_rateEulerPart (Q : ℕ → Prop) (ξ : Measure ℝ) : ξ ≤ rateEulerPart Q ξ := by
  classical
  refine Measure.le_iff.2 fun E hE => ?_
  rw [rateEulerPart, Measure.sum_apply _ hE]
  calc ξ E = (if ∀ p ∈ (1 : ℕ).primeFactors, ¬ Q p then rateDilate 1 ξ else 0) E := by
        rw [if_pos (by simp), rateDilate_one]
    _ ≤ _ := ENNReal.le_tsum (f := fun m : ℕ =>
        (if ∀ p ∈ m.primeFactors, ¬ Q p then rateDilate m ξ else 0) E) 1

/-- The value of a partial Euler sum of an atom at an Euler rate. -/
theorem rateEulerPart_smul_dirac_singleton (Q : ℕ → Prop) [DecidablePred Q] (c : ℝ≥0∞) {a : ℝ}
    (ha : 0 < a) (n : ℕ) :
    rateEulerPart Q (c • Measure.dirac a) {(n : ℝ) ^ 2 * a} =
      if ∀ p ∈ n.primeFactors, ¬ Q p then (n : ℝ≥0∞) ^ 2 * c else 0 := by
  classical
  rw [rateEulerPart, Measure.sum_apply _ (measurableSet_singleton _), tsum_eq_single n]
  · by_cases h : ∀ p ∈ n.primeFactors, ¬ Q p
    · rw [if_pos h, if_pos h, rateDilate_apply _ _ (measurableSet_singleton _), Measure.smul_apply,
        smul_eq_mul, Measure.dirac_apply' _ (measurable_rateScale n (measurableSet_singleton _)),
        indicator_of_mem (by simp [rateScale])]
      simp
    · rw [if_neg h, if_neg h]
      rfl
  · intro m hmn
    split_ifs
    · rw [rateDilate_apply _ _ (measurableSet_singleton _), Measure.smul_apply, smul_eq_mul,
        Measure.dirac_apply' _ (measurable_rateScale m (measurableSet_singleton _)),
        indicator_of_notMem]
      · simp
      · simp only [rateScale, mem_preimage, mem_singleton_iff]
        intro h
        have h2 : (m : ℝ) ^ 2 = (n : ℝ) ^ 2 := mul_right_cancel₀ ha.ne' h
        have := (sq_eq_sq₀ (Nat.cast_nonneg m) (Nat.cast_nonneg n)).1 h2
        exact hmn (by exact_mod_cast this)
    · rfl

/-- The `P`-smooth stage `ν_P = 2π Σ_{n P-smooth} n² δ_{π n²}` of the theta rate measure. -/
def thetaSmoothStage (P : ℕ → Prop) : Measure ℝ :=
  rateEulerPart (fun p => ¬ P p) (ENNReal.ofReal (2 * Real.pi) • Measure.dirac Real.pi)

/-- The full Euler completion of the smooth stages is the theta rate measure. -/
theorem thetaSmoothStage_true : thetaSmoothStage (fun _ => True) = thetaRateMeasure := by
  simp [thetaSmoothStage, thetaRateMeasure, rateEuler]

/-- Smooth stages keep the rate gap `λ₀ = π`. -/
theorem thetaSmoothStage_Iio_pi (P : ℕ → Prop) : thetaSmoothStage P (Iio Real.pi) = 0 :=
  le_antisymm ((Measure.le_iff'.1 (rateEulerPart_le_rateEuler _ _) _).trans
    thetaRateMeasure_Iio_pi.le) zero_le

/-- A smooth stage survives every deletion by primes it contains. -/
theorem thetaSmoothStage_deletion_le (P : ℕ → Prop) [DecidablePred P] {S : Finset ℕ}
    (hSP : ∀ p ∈ S, P p) :
    rateDeletionPart (· ∈ S) false (thetaSmoothStage P) ≤
      rateDeletionPart (· ∈ S) true (thetaSmoothStage P) := by
  rw [thetaSmoothStage, rateDeletionPart_rateEulerPart (· ∈ S) (fun p => ¬ P p)
    (fun p _ hp => not_not.2 (hSP p hp))]
  exact Measure.le_add_right le_rfl

/-- **Undeclared primes break every smooth stage.**  If the prime `q` is not in `P`, the deletion
`D_q ν_P` has coefficient `-2π q²` at the rate `π q²`: its positive part vanishes there while its
negative part is `2π q²`. -/
theorem thetaSmoothStage_undeclared_prime (P : ℕ → Prop) [DecidablePred P] {q : ℕ} (hq : q.Prime)
    (hPq : ¬ P q) :
    rateDeletionPart (· ∈ ({q} : Finset ℕ)) true (thetaSmoothStage P)
        {(q : ℝ) ^ 2 * Real.pi} = 0 ∧
      rateDeletionPart (· ∈ ({q} : Finset ℕ)) false (thetaSmoothStage P)
        {(q : ℝ) ^ 2 * Real.pi} = ENNReal.ofReal (2 * Real.pi * (q : ℝ) ^ 2) := by
  constructor
  · rw [rateDeletionPart_singleton_true, thetaSmoothStage,
      rateEulerPart_smul_dirac_singleton _ _ Real.pi_pos, if_neg]
    rw [Nat.Prime.primeFactors hq]
    simpa using hPq
  · rw [rateDeletionPart_singleton_false hq, rateDilate_apply _ _ (measurableSet_singleton _)]
    have hpre : rateScale q ⁻¹' {(q : ℝ) ^ 2 * Real.pi} = {((1 : ℕ) : ℝ) ^ 2 * Real.pi} := by
      ext l
      simp only [rateScale, mem_preimage, mem_singleton_iff, Nat.cast_one, one_pow, one_mul]
      have hq2 : (q : ℝ) ^ 2 ≠ 0 := by have := hq.pos; positivity
      constructor
      · intro h; exact mul_left_cancel₀ hq2 h
      · intro h; rw [h]
    rw [hpre, thetaSmoothStage, rateEulerPart_smul_dirac_singleton _ _ Real.pi_pos,
      if_pos (by simp), show ENNReal.ofReal (2 * Real.pi * (q : ℝ) ^ 2) =
        ENNReal.ofReal (2 * Real.pi) * (q : ℝ≥0∞) ^ 2 by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]]
    simp only [Nat.cast_one, one_pow, one_mul]
    ring

/-- No smooth stage missing a prime belongs to the all-sieve cone. -/
theorem thetaSmoothStage_not_deletion_le (P : ℕ → Prop) [DecidablePred P] {q : ℕ}
    (hq : q.Prime) (hPq : ¬ P q) :
    ¬ rateDeletionPart (· ∈ ({q} : Finset ℕ)) false (thetaSmoothStage P) ≤
      rateDeletionPart (· ∈ ({q} : Finset ℕ)) true (thetaSmoothStage P) := by
  intro hle
  obtain ⟨h1, h2⟩ := thetaSmoothStage_undeclared_prime P hq hPq
  have h := Measure.le_iff'.1 hle {(q : ℝ) ^ 2 * Real.pi}
  rw [h1, h2, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h
  have : 0 < 2 * Real.pi * (q : ℝ) ^ 2 := by have := hq.pos; positivity
  linarith

/-- Every finite prime set leaves out a prime, so no finite smooth stage is in the all-sieve cone. -/
theorem thetaSmoothStage_finite_not_allSieve (P : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ P ∧
      ¬ rateDeletionPart (· ∈ ({q} : Finset ℕ)) false (thetaSmoothStage (· ∈ P)) ≤
        rateDeletionPart (· ∈ ({q} : Finset ℕ)) true (thetaSmoothStage (· ∈ P)) := by
  obtain ⟨q, hqP, hq⟩ := Nat.exists_infinite_primes (P.sup id + 1)
  have hqn : q ∉ P := fun hmem => by
    have := Finset.le_sup (f := id) hmem
    simp only [id] at this
    omega
  exact ⟨q, hq, hqn, thetaSmoothStage_not_deletion_le _ hq hqn⟩

/-! ## The rate measure `dλ`: a component invisible to every deletion -/

/-- Lebesgue measure on the positive rate half-line. -/
def lebesgueRate : Measure ℝ := volume.restrict (Ioi 0)

theorem lebesgueRate_compl_Ici : lebesgueRate (Ici 0)ᶜ = 0 := by
  rw [lebesgueRate, Measure.restrict_apply measurableSet_Ici.compl]
  convert measure_empty (μ := (volume : Measure ℝ))
  ext l
  simp only [mem_inter_iff, mem_compl_iff, mem_Ici, not_le, mem_Ioi, mem_empty_iff_false,
    iff_false, not_and, not_lt]
  exact fun h => h.le

/-- `∫ e^{-tλ} dλ = 1/t`. -/
theorem rateLaplace_lebesgueRate {t : ℝ} (ht : 0 < t) :
    rateLaplace lebesgueRate t = ENNReal.ofReal (1 / t) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) one_pos ht
  simp only [sub_self, Real.rpow_zero, one_mul, Real.rpow_one, Real.Gamma_one, mul_one] at h
  have hint : IntegrableOn (fun l : ℝ => Real.exp (-(t * l))) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 ht).congr_fun (fun l _ => by ring_nf) measurableSet_Ioi
  rw [rateLaplace, lebesgueRate, ← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun _ => (Real.exp_pos _).le), h]

theorem rateLaplace_lebesgueRate_ne_top {t : ℝ} (ht : 0 < t) : rateLaplace lebesgueRate t ≠ ∞ := by
  rw [rateLaplace_lebesgueRate ht]; exact ENNReal.ofReal_ne_top

theorem sq_mul_rateLaplace_lebesgueRate {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    (n : ℝ≥0∞) ^ 2 * rateLaplace lebesgueRate ((n : ℝ) ^ 2 * t) = rateLaplace lebesgueRate t := by
  have hn' : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  rw [rateLaplace_lebesgueRate (mul_pos hn' ht), rateLaplace_lebesgueRate ht,
    show ((n : ℝ≥0∞) ^ 2) = ENNReal.ofReal ((n : ℝ) ^ 2) by
      rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast],
    ← ENNReal.ofReal_mul hn'.le]
  congr 1
  field_simp

/-- **Prime dilation fixes `dλ`.** -/
theorem rateDilate_lebesgueRate {n : ℕ} (hn : 0 < n) : rateDilate n lebesgueRate = lebesgueRate := by
  refine eq_of_rateLaplace_eq (rateDilate_compl_Ici lebesgueRate_compl_Ici n)
    lebesgueRate_compl_Ici ?_ (rateLaplace_lebesgueRate_ne_top one_pos) fun t ht => ?_
  · rw [rateLaplace_rateDilate]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
      (rateLaplace_lebesgueRate_ne_top (by positivity))
  · rw [rateLaplace_rateDilate, sq_mul_rateLaplace_lebesgueRate hn ht]

/-- **Every nonempty deletion of `dλ` vanishes**: the even and odd parts coincide. -/
theorem rateDeletionPart_lebesgueRate {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) :
    rateDeletionPart (· ∈ S) true lebesgueRate = rateDeletionPart (· ∈ S) false lebesgueRate := by
  have hL : ∀ e : Bool, ∀ t, 0 < t → rateLaplace (rateDeletionPart (· ∈ S) e lebesgueRate) t =
      ((S.powerset.filter fun T => (Even T.card ↔ e = true)).card : ℝ≥0∞) *
        rateLaplace lebesgueRate t := by
    intro e t ht
    rw [rateLaplace_rateDeletionPart S hS, Finset.sum_congr rfl fun T hT =>
      sq_mul_rateLaplace_lebesgueRate (prod_pos_of_primes fun p hp =>
        hS p (Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1 hp)) ht]
    simp
  have hcard := card_even_words_eq S
  rw [if_neg hne.ne_empty, add_zero] at hcard
  have hfin : ∀ e : Bool, rateLaplace (rateDeletionPart (· ∈ S) e lebesgueRate) 1 ≠ ∞ := fun e => by
    rw [hL e 1 one_pos]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (rateLaplace_lebesgueRate_ne_top one_pos)
  refine eq_of_rateLaplace_eq (rateDeletionPart_compl_Ici lebesgueRate_compl_Ici _ _)
    (rateDeletionPart_compl_Ici lebesgueRate_compl_Ici _ _) (hfin true) (hfin false)
    fun t ht => ?_
  rw [hL true t ht, hL false t ht]
  simp only [Bool.false_eq_true, iff_false, iff_true]
  rw [hcard]

theorem lebesgueRate_Iio (l₀ : ℝ) : lebesgueRate (Iio l₀) = ENNReal.ofReal l₀ := by
  rw [lebesgueRate, Measure.restrict_apply measurableSet_Iio, inter_comm, Ioi_inter_Iio,
    Real.volume_Ioo, sub_zero]

theorem rateNegMoment_restrict_Ioi (q : ℝ) (μ : Measure ℝ) :
    rateNegMoment q (μ.restrict (Ioi 0)) = ∫⁻ l in Ioi 0, ENNReal.ofReal (l ^ (-q)) ∂μ := by
  rw [rateNegMoment, lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self]

theorem lintegral_Ioi_ofReal_eq_top {g : ℝ → ℝ} (hg : Measurable g) (hg0 : ∀ l, 0 < l → 0 ≤ g l)
    (hni : ¬ IntegrableOn g (Ioi 0)) : ∫⁻ l in Ioi 0, ENNReal.ofReal (g l) = ∞ := by
  by_contra hfin
  exact hni ⟨hg.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (ae_restrict_of_forall_mem measurableSet_Ioi fun l hl => hg0 l hl)).2 (lt_top_iff_ne_top.2 hfin)⟩

/-- `dλ` has no finite negative moment. -/
theorem rateNegMoment_lebesgueRate (q : ℝ) : rateNegMoment q lebesgueRate = ∞ := by
  rw [lebesgueRate, rateNegMoment_restrict_Ioi]
  exact lintegral_Ioi_ofReal_eq_top (measurable_id.pow_const _)
    (fun l hl => Real.rpow_nonneg hl.le _) (not_integrableOn_Ioi_rpow (-q))

/-- `dλ` satisfies neither control condition. -/
theorem not_rateControlled_lebesgueRate : ¬ RateControlled lebesgueRate := by
  rintro (⟨l₀, hl₀, h⟩ | ⟨q, -, h⟩)
  · rw [lebesgueRate_Iio, ENNReal.ofReal_eq_zero] at h
    linarith
  · exact h (rateNegMoment_lebesgueRate q)

/-- Infinitely many dilations of `dλ` reach the window `(-∞, 1]`. -/
theorem not_rateWindowFinite_lebesgueRate : ¬ RateWindowFinite lebesgueRate := by
  intro h
  apply h 1
  have hone : ∀ n : ℕ, rateDilate (1 * (n + 1)) lebesgueRate (Iic 1) = 1 := fun n => by
    rw [one_mul, rateDilate_lebesgueRate n.succ_pos, lebesgueRate,
      Measure.restrict_apply measurableSet_Iic, inter_comm, Ioi_inter_Iic, Real.volume_Ioc]
    simp
  refine top_le_iff.1 (le_trans ?_ (ENNReal.le_tsum 1))
  refine le_trans ?_ (ENNReal.tsum_comp_le_tsum_of_injective Nat.succ_injective
    (fun n => rateDilate (1 * n) lebesgueRate (Iic 1)))
  simp only [Nat.succ_eq_add_one]
  rw [tsum_congr hone, ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero]

/-- `dλ` is not the Euler reconstruction of any seed. -/
theorem not_rateEuler_eq_lebesgueRate (ξ : Measure ℝ) : rateEuler ξ ≠ lebesgueRate := by
  intro hξ
  have hdel := rateDeletionPart_rateEuler (· ∈ ({2} : Finset ℕ)) ξ
  rw [hξ, rateDeletionPart_singleton_true, rateDeletionPart_singleton_false Nat.prime_two,
    rateDilate_lebesgueRate two_pos] at hdel
  have hfin : ∀ R : ℝ, lebesgueRate (Iic R) ≠ ∞ := fun R =>
    measure_Iic_ne_top_of_laplace (by simpa [rateLaplace] using rateLaplace_lebesgueRate_ne_top one_pos) R
  have h0 : rateEulerPart (· ∈ ({2} : Finset ℕ)) ξ = 0 := by
    have := eq_of_add_eq_add hfin (ξ := 0) (ξ' := rateEulerPart (· ∈ ({2} : Finset ℕ)) ξ)
      (by rw [zero_add, add_comm]; exact hdel)
    exact this.symm
  have hξ0 : ξ = 0 := le_antisymm (h0 ▸ le_rateEulerPart _ ξ) (Measure.zero_le _)
  rw [hξ0] at hξ
  have hpos : lebesgueRate (Iio 1) ≠ 0 := by
    rw [lebesgueRate_Iio]; simp
  apply hpos
  rw [← hξ, rateEuler_apply _ measurableSet_Iio]
  simp [rateDilate_apply _ _ measurableSet_Iio]

/-! ## The critical-scaling ghost `λ^{1/2} dλ` -/

/-- The critical ghost `λ^{1/2} dλ` on `(0, ∞)`. -/
def criticalGhostRate : Measure ℝ :=
  lebesgueRate.withDensity fun l => ENNReal.ofReal (l ^ (1 / 2 : ℝ))

theorem measurable_sqrtDensity : Measurable fun l : ℝ => ENNReal.ofReal (l ^ (1 / 2 : ℝ)) :=
  ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)

theorem criticalGhostRate_compl_Ici : criticalGhostRate (Ici 0)ᶜ = 0 :=
  withDensity_absolutelyContinuous _ _ lebesgueRate_compl_Ici

/-- `∫ e^{-tλ} λ^{1/2} dλ = Γ(3/2) t^{-3/2}`. -/
theorem rateLaplace_criticalGhostRate {t : ℝ} (ht : 0 < t) :
    rateLaplace criticalGhostRate t =
      ENNReal.ofReal (Real.Gamma (3 / 2) * t ^ (-(3 / 2 : ℝ))) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3 / 2) (by norm_num) ht
  rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num, one_div t, Real.inv_rpow ht.le,
    ← Real.rpow_neg ht.le] at h
  have hint : IntegrableOn (fun l : ℝ => l ^ (1 / 2 : ℝ) * Real.exp (-(t * l))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1 / 2) (p := 1) (b := t) (by norm_num) le_rfl
      ht).congr_fun (fun l _ => by simp only [Real.rpow_one]; ring_nf) measurableSet_Ioi
  rw [rateLaplace, criticalGhostRate, lintegral_withDensity_eq_lintegral_mul _ measurable_sqrtDensity
    (show Measurable fun l : ℝ => ENNReal.ofReal (Real.exp (-(t * l))) from
      ENNReal.measurable_ofReal.comp (by fun_prop)), lebesgueRate]
  simp only [Pi.mul_apply]
  rw [setLIntegral_congr_fun measurableSet_Ioi (fun l (hl : l ∈ Ioi (0 : ℝ)) =>
      (ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hl) _)).symm),
    ← ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Ioi
      fun l hl => mul_nonneg (Real.rpow_nonneg (le_of_lt hl) _) (Real.exp_pos _).le), h, mul_comm]

theorem rateLaplace_criticalGhostRate_ne_top {t : ℝ} (ht : 0 < t) :
    rateLaplace criticalGhostRate t ≠ ∞ := by
  rw [rateLaplace_criticalGhostRate ht]; exact ENNReal.ofReal_ne_top

theorem rateLaplace_smul (c : ℝ≥0∞) (μ : Measure ℝ) (t : ℝ) :
    rateLaplace (c • μ) t = c * rateLaplace μ t := by
  rw [rateLaplace, lintegral_smul_measure, smul_eq_mul, rateLaplace]

theorem rateLaplace_add (μ ν : Measure ℝ) (t : ℝ) :
    rateLaplace (μ + ν) t = rateLaplace μ t + rateLaplace ν t := by
  simp only [rateLaplace, lintegral_add_measure]

theorem criticalGhost_scale {P : ℝ} (hP : 0 < P) {t : ℝ} (ht : 0 < t) :
    P ^ 2 * (Real.Gamma (3 / 2) * (P ^ 2 * t) ^ (-(3 / 2 : ℝ))) =
      1 / P * (Real.Gamma (3 / 2) * t ^ (-(3 / 2 : ℝ))) := by
  rw [Real.mul_rpow (by positivity) ht.le]
  have h : (P ^ 2) ^ (-(3 / 2 : ℝ)) = (P ^ 3)⁻¹ := by
    rw [← Real.rpow_natCast P 2, ← Real.rpow_mul hP.le, ← Real.rpow_natCast P 3,
      ← Real.rpow_neg hP.le]
    norm_num
  rw [h]
  field_simp

/-- `(∏T)² L(( ∏T)² t) = (∏T)⁻¹ L(t)` for the ghost. -/
theorem sq_mul_rateLaplace_criticalGhostRate {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    (n : ℝ≥0∞) ^ 2 * rateLaplace criticalGhostRate ((n : ℝ) ^ 2 * t) =
      ENNReal.ofReal (1 / n) * rateLaplace criticalGhostRate t := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [rateLaplace_criticalGhostRate (by positivity), rateLaplace_criticalGhostRate ht,
    show ((n : ℝ≥0∞) ^ 2) = ENNReal.ofReal ((n : ℝ) ^ 2) by
      rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast],
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    criticalGhost_scale hn' ht]

/-- **Critical scaling.**  `A_n (λ^{1/2} dλ) = n⁻¹ λ^{1/2} dλ`. -/
theorem rateDilate_criticalGhostRate {n : ℕ} (hn : 0 < n) :
    rateDilate n criticalGhostRate = ENNReal.ofReal (1 / n) • criticalGhostRate := by
  refine eq_of_rateLaplace_eq (rateDilate_compl_Ici criticalGhostRate_compl_Ici n) ?_ ?_ ?_
    fun t ht => ?_
  · rw [Measure.smul_apply, criticalGhostRate_compl_Ici, smul_zero]
  · rw [rateLaplace_rateDilate]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
      (rateLaplace_criticalGhostRate_ne_top (by positivity))
  · rw [rateLaplace_smul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (rateLaplace_criticalGhostRate_ne_top one_pos)
  · rw [rateLaplace_rateDilate, rateLaplace_smul, sq_mul_rateLaplace_criticalGhostRate hn ht]

/-- The inclusion–exclusion identity `Σ_{T even} 1/∏T = Σ_{T odd} 1/∏T + ∏_{p ∈ S} (1 - 1/p)`. -/
theorem sum_even_inv_prod_eq (S : Finset ℕ) :
    ∑ T ∈ S.powerset.filter (fun T => Even T.card), 1 / ((∏ p ∈ T, p : ℕ) : ℝ) =
      ∑ T ∈ S.powerset.filter (fun T => ¬ Even T.card), 1 / ((∏ p ∈ T, p : ℕ) : ℝ) +
        ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
  classical
  have h := Finset.prod_add (fun p : ℕ => -(1 / (p : ℝ))) (fun _ => 1) S
  simp only [Finset.prod_const_one, mul_one] at h
  have h' : ∏ p ∈ S, (1 - 1 / (p : ℝ)) = ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card *
      (1 / ((∏ p ∈ T, p : ℕ) : ℝ)) := by
    rw [show (∏ p ∈ S, (1 - 1 / (p : ℝ))) = ∏ p ∈ S, (-(1 / (p : ℝ)) + 1) from
      Finset.prod_congr rfl fun p _ => by ring, h]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_neg, Nat.cast_prod, Finset.prod_div_distrib, Finset.prod_const_one]
  have hsplit : ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * (1 / ((∏ p ∈ T, p : ℕ) : ℝ)) =
      ∑ T ∈ S.powerset.filter (fun T => Even T.card), 1 / ((∏ p ∈ T, p : ℕ) : ℝ) -
        ∑ T ∈ S.powerset.filter (fun T => ¬ Even T.card), 1 / ((∏ p ∈ T, p : ℕ) : ℝ) := by
    rw [← Finset.sum_filter_add_sum_filter_not S.powerset (fun T => Even T.card), sub_eq_add_neg,
      ← Finset.sum_neg_distrib]
    congr 1 <;> refine Finset.sum_congr rfl fun T hT => ?_
    · rw [(Finset.mem_filter.1 hT).2.neg_one_pow, one_mul]
    · rw [(Nat.not_even_iff_odd.1 (Finset.mem_filter.1 hT).2).neg_one_pow, neg_one_mul]
  rw [h', hsplit]
  ring

theorem rateLaplace_rateDeletionPart_criticalGhostRate {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (e : Bool) {t : ℝ} (ht : 0 < t) :
    rateLaplace (rateDeletionPart (· ∈ S) e criticalGhostRate) t =
      ENNReal.ofReal (∑ T ∈ S.powerset.filter (fun T => (Even T.card ↔ e = true)),
        1 / ((∏ p ∈ T, p : ℕ) : ℝ)) * rateLaplace criticalGhostRate t := by
  rw [rateLaplace_rateDeletionPart S hS, Finset.sum_congr rfl fun T hT =>
      sq_mul_rateLaplace_criticalGhostRate (prod_pos_of_primes fun p hp =>
        hS p (Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1 hp)) ht,
    ← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun T _ => by positivity]

/-- **Positive deletions of the ghost.**  `D_S (λ^{1/2} dλ) = ∏_{p ∈ S}(1 - 1/p) λ^{1/2} dλ`. -/
theorem rateDeletionPart_criticalGhostRate {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    rateDeletionPart (· ∈ S) true criticalGhostRate =
      rateDeletionPart (· ∈ S) false criticalGhostRate +
        ENNReal.ofReal (∏ p ∈ S, (1 - 1 / (p : ℝ))) • criticalGhostRate := by
  have hprod : 0 ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := Finset.prod_nonneg fun p hp => by
    have : (1 : ℝ) ≤ p := by exact_mod_cast (hS p hp).one_lt.le
    rw [sub_nonneg, div_le_one (by linarith)]
    exact this
  have hfin : ∀ e : Bool, rateLaplace (rateDeletionPart (· ∈ S) e criticalGhostRate) 1 ≠ ∞ :=
    fun e => by
      rw [rateLaplace_rateDeletionPart_criticalGhostRate hS e one_pos]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (rateLaplace_criticalGhostRate_ne_top one_pos)
  refine eq_of_rateLaplace_eq (rateDeletionPart_compl_Ici criticalGhostRate_compl_Ici _ _) ?_
    (hfin true) ?_ fun t ht => ?_
  · rw [Measure.add_apply, Measure.smul_apply, rateDeletionPart_compl_Ici criticalGhostRate_compl_Ici,
      criticalGhostRate_compl_Ici, smul_zero, add_zero]
  · rw [rateLaplace_add, rateLaplace_smul]
    exact ENNReal.add_ne_top.2 ⟨hfin false, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (rateLaplace_criticalGhostRate_ne_top one_pos)⟩
  · rw [rateLaplace_add, rateLaplace_smul,
      rateLaplace_rateDeletionPart_criticalGhostRate hS _ ht,
      rateLaplace_rateDeletionPart_criticalGhostRate hS _ ht, ← add_mul,
      ← ENNReal.ofReal_add (Finset.sum_nonneg fun T _ => by positivity) hprod]
    simp only [Bool.false_eq_true, iff_false, iff_true]
    rw [sum_even_inv_prod_eq]

theorem criticalGhostRate_deletion_le {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    rateDeletionPart (· ∈ S) false criticalGhostRate ≤
      rateDeletionPart (· ∈ S) true criticalGhostRate := by
  rw [rateDeletionPart_criticalGhostRate hS]
  exact Measure.le_add_right le_rfl

/-- Along every prime exhaustion the deletion factor `∏_{p ∈ S_j}(1 - 1/p)` tends to zero, by the
divergence of `Σ 1/p`. -/
theorem tendsto_prod_one_sub_inv_of_exhaustion {S : ℕ → Finset ℕ} (hmono : Monotone S)
    (hex : ∀ p, p.Prime → ∃ j, p ∈ S j) (hS : ∀ j, ∀ p ∈ S j, p.Prime) :
    Tendsto (fun j => ∏ p ∈ S j, (1 - 1 / (p : ℝ))) atTop (𝓝 0) := by
  set f : ℕ → ℝ := {p | p.Prime}.indicator fun n => 1 / (n : ℝ)
  have hf0 : ∀ n, 0 ≤ f n := fun n => Set.indicator_nonneg (fun n _ => by positivity) n
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg hf0).1 not_summable_one_div_on_primes
  have hsum : Tendsto (fun j => ∑ p ∈ S j, 1 / (p : ℝ)) atTop atTop := by
    refine tendsto_atTop.2 fun M => ?_
    obtain ⟨N, hN⟩ := (tendsto_atTop.1 hdiv M).exists
    have hev : ∀ᶠ j in atTop, ∀ p ∈ (Finset.range N).filter Nat.Prime, p ∈ S j := by
      rw [eventually_all_finset]
      intro p hp
      obtain ⟨j₀, hj₀⟩ := hex p (Finset.mem_filter.1 hp).2
      exact eventually_atTop.2 ⟨j₀, fun j hj => hmono hj hj₀⟩
    filter_upwards [hev] with j hj
    calc M ≤ ∑ i ∈ Finset.range N, f i := hN
      _ = ∑ p ∈ (Finset.range N).filter Nat.Prime, 1 / (p : ℝ) := by
          rw [Finset.sum_filter]
          exact Finset.sum_congr rfl fun i _ => by
            simp only [f, Set.indicator_apply, mem_setOf_eq]
      _ ≤ ∑ p ∈ S j, 1 / (p : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hj fun _ _ _ => by positivity
  have hle : ∀ j, ∏ p ∈ S j, (1 - 1 / (p : ℝ)) ≤ Real.exp (-∑ p ∈ S j, 1 / (p : ℝ)) := by
    intro j
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_le_prod (fun p hp => ?_) fun p _ => by
      linarith [Real.add_one_le_exp (-(1 / (p : ℝ)))]
    have : (1 : ℝ) ≤ p := by exact_mod_cast (hS j p hp).one_lt.le
    rw [sub_nonneg, div_le_one (by linarith)]
    exact this
  have hnn : ∀ j, 0 ≤ ∏ p ∈ S j, (1 - 1 / (p : ℝ)) := fun j => Finset.prod_nonneg fun p hp => by
    have : (1 : ℝ) ≤ p := by exact_mod_cast (hS j p hp).one_lt.le
    rw [sub_nonneg, div_le_one (by linarith)]
    exact this
  exact squeeze_zero hnn hle (Real.tendsto_exp_neg_atTop_nhds_zero.comp hsum)

/-- **Cofinal loss of the ghost.**  Along every prime exhaustion the deleted measures lose the whole
ghost on each window of finite mass. -/
theorem tendsto_criticalGhost_deletion {S : ℕ → Finset ℕ} (hmono : Monotone S)
    (hex : ∀ p, p.Prime → ∃ j, p ∈ S j) (hS : ∀ j, ∀ p ∈ S j, p.Prime) {E : Set ℝ}
    (hE : criticalGhostRate E ≠ ∞) :
    Tendsto (fun j => ENNReal.ofReal (∏ p ∈ S j, (1 - 1 / (p : ℝ))) * criticalGhostRate E)
      atTop (𝓝 0) := by
  have h := ENNReal.Tendsto.mul_const
    (ENNReal.tendsto_ofReal (tendsto_prod_one_sub_inv_of_exhaustion hmono hex hS)) (Or.inr hE)
  rwa [ENNReal.ofReal_zero, zero_mul] at h

theorem criticalGhostRate_Iic_ne_top (R : ℝ) : criticalGhostRate (Iic R) ≠ ∞ :=
  measure_Iic_ne_top_of_laplace (by
    simpa [rateLaplace] using rateLaplace_criticalGhostRate_ne_top one_pos) R

theorem criticalGhostRate_ne_zero : criticalGhostRate ≠ 0 := by
  intro h
  have h1 := rateLaplace_criticalGhostRate one_pos
  rw [h, rateLaplace, lintegral_zero_measure, eq_comm, ENNReal.ofReal_eq_zero] at h1
  have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  rw [Real.one_rpow, mul_one] at h1
  linarith

/-- **The ghost is not an Euler reconstruction.**  Its finite deletions are positive, but cofinal
deletion reads the zero seed. -/
theorem not_rateEuler_eq_criticalGhostRate (ξ : Measure ℝ) : rateEuler ξ ≠ criticalGhostRate := by
  intro hξ
  have hS := primeExhaustion_thetaPrimesUpTo
  have hstep : ∀ j, rateEulerPart (· ∈ thetaPrimesUpTo j) ξ =
      ENNReal.ofReal (∏ p ∈ thetaPrimesUpTo j, (1 - 1 / (p : ℝ))) • criticalGhostRate := by
    intro j
    have h1 := rateDeletionPart_rateEuler (· ∈ thetaPrimesUpTo j) ξ
    rw [hξ, rateDeletionPart_criticalGhostRate (hS.prime j)] at h1
    have hN : ∀ R : ℝ, rateDeletionPart (· ∈ thetaPrimesUpTo j) false criticalGhostRate (Iic R) ≠ ∞ :=
      measure_Iic_ne_top_of_laplace (by
        have := rateLaplace_rateDeletionPart_criticalGhostRate (hS.prime j) false one_pos
        have hne : rateLaplace (rateDeletionPart (· ∈ thetaPrimesUpTo j) false criticalGhostRate) 1
            ≠ ∞ := by
          rw [this]
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (rateLaplace_criticalGhostRate_ne_top one_pos)
        simpa [rateLaplace] using hne)
    exact (eq_of_add_eq_add hN (by rw [add_comm, h1, add_comm])).symm
  have hIic : ∀ R : ℝ, ξ (Iic R) = 0 := by
    intro R
    have hmono : Monotone thetaPrimesUpTo := fun a b hab p hp => by
      rw [thetaPrimesUpTo, Finset.mem_filter, Finset.mem_range] at hp ⊢
      exact ⟨by omega, hp.2⟩
    refine le_antisymm (ge_of_tendsto' (tendsto_criticalGhost_deletion hmono
      (fun p hp => (hS.eventually_mem p hp).exists) hS.prime (criticalGhostRate_Iic_ne_top R))
      fun j => ?_) zero_le
    calc ξ (Iic R) ≤ rateEulerPart (· ∈ thetaPrimesUpTo j) ξ (Iic R) :=
          Measure.le_iff'.1 (le_rateEulerPart _ ξ) _
      _ = _ := by rw [hstep j, Measure.smul_apply, smul_eq_mul]
  have hξ0 : ξ = 0 := by
    refine Measure.measure_univ_eq_zero.1 (measure_mono_null (fun l _ => ?_)
      (measure_iUnion_null fun n : ℕ => hIic n))
    exact mem_iUnion.2 ⟨⌈l⌉₊, mem_Iic.2 (Nat.le_ceil l)⟩
  apply criticalGhostRate_ne_zero
  rw [← hξ, hξ0, rateEuler_eq_sum]
  ext E hE
  simp [Measure.sum_apply _ hE, rateDilate_apply _ _ hE]

/-- The ghost has no finite negative moment. -/
theorem rateNegMoment_criticalGhostRate (q : ℝ) : rateNegMoment q criticalGhostRate = ∞ := by
  rw [rateNegMoment, criticalGhostRate, lintegral_withDensity_eq_lintegral_mul _
    measurable_sqrtDensity (show Measurable ((Ioi (0 : ℝ)).indicator
      fun l : ℝ => ENNReal.ofReal (l ^ (-q))) from
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).indicator measurableSet_Ioi),
    lebesgueRate]
  simp only [Pi.mul_apply]
  rw [setLIntegral_congr_fun measurableSet_Ioi (fun l (hl : l ∈ Ioi (0 : ℝ)) => by
    rw [indicator_of_mem hl, ← ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hl) _),
      ← Real.rpow_add hl])]
  exact lintegral_Ioi_ofReal_eq_top (measurable_id.pow_const _)
    (fun l hl => Real.rpow_nonneg hl.le _) (not_integrableOn_Ioi_rpow (1 / 2 + -q))

/-- The ghost has no rate gap and no finite negative moment. -/
theorem not_rateControlled_criticalGhostRate : ¬ RateControlled criticalGhostRate := by
  rintro (⟨l₀, hl₀, h⟩ | ⟨q, -, h⟩)
  · rw [criticalGhostRate, withDensity_apply_eq_zero' measurable_sqrtDensity.aemeasurable] at h
    have hsub : Ioo 0 l₀ ⊆ {l : ℝ | ENNReal.ofReal (l ^ (1 / 2 : ℝ)) ≠ 0} ∩ Iio l₀ := by
      intro l hl
      refine ⟨?_, hl.2⟩
      simp only [mem_setOf_eq, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact Real.rpow_pos_of_pos hl.1 _
    have h2 := measure_mono_null hsub h
    rw [lebesgueRate, Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.2 (fun l hl => hl.1), Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h2
    linarith
  · exact h (rateNegMoment_criticalGhostRate q)

/-- The flux potential `e^{3x} b(e^{2x})` of `b(t) = Γ(3/2) t^{-3/2}` is constant, so the recovery
formula `f(x) = -e^{-x/2} d/dx[e^{3x} b(e^{2x})]` returns the zero source. -/
theorem criticalGhost_fluxPotential (x : ℝ) :
    Real.exp (3 * x) * (Real.Gamma (3 / 2) * Real.exp (2 * x) ^ (-(3 / 2 : ℝ))) =
      Real.Gamma (3 / 2) := by
  rw [← Real.exp_mul, mul_left_comm, ← Real.exp_add]
  ring_nf
  simp

/-- **The ghost profile is not a tail flux.**  No flux source has `b_f(t) = Γ(3/2) t^{-3/2}`: its
flux potential `∫_{x > X} e^{x/2} f` would have to tend to zero, but it is the nonzero constant
`Γ(3/2)`. -/
theorem not_thetaFluxSource_criticalGhost :
    ¬ ∃ f : ℝ → ℝ, ThetaFluxSource f ∧
      ∀ t, 0 < t → thetaNormalizedFlux f t = Real.Gamma (3 / 2) * t ^ (-(3 / 2 : ℝ)) := by
  rintro ⟨f, hf, hb⟩
  have hconst : ∀ X : ℝ, (∫ x in Ioi X, Real.exp (x / 2) * f x) = Real.Gamma (3 / 2) := by
    intro X
    have h := thetaNormalizedFlux_exp f X
    rw [hb _ (Real.exp_pos _)] at h
    rw [← criticalGhost_fluxPotential X, h, ← mul_assoc, ← Real.exp_add]
    simp
  have hlim : Tendsto (fun X : ℝ => ∫ x in Ioi X, Real.exp (x / 2) * f x) atTop (𝓝 0) := by
    have h := tendsto_setIntegral_of_antitone (μ := volume)
      (f := fun x => Real.exp (x / 2) * f x) (s := fun X : ℝ => Ioi X)
      (fun X => measurableSet_Ioi) (fun a b hab => Ioi_subset_Ioi hab) ⟨0, hf.2 0⟩
    have hI : (⋂ X : ℝ, Ioi X) = ∅ := by
      ext x
      simp only [mem_iInter, mem_Ioi, mem_empty_iff_false, iff_false, not_forall, not_lt]
      exact ⟨x, le_rfl⟩
    rwa [hI, Measure.restrict_empty, integral_zero_measure] at h
  simp_rw [hconst] at hlim
  have := tendsto_nhds_unique tendsto_const_nhds hlim
  linarith [Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]

end

end RHTower
