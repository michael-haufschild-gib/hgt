import GaloisForLFunctions.RHTower.PhotonicLosslessProductPortCosineShiftProducer
import GaloisForLFunctions.RHTower.KiKimLeeLargeHeightReality
import GaloisForLFunctions.RHTower.DeBruijnNewmanConstant
import GaloisForLFunctions.RHTower.DeBruijnNewmanNonnegative
import GaloisForLFunctions.RHTower.DeBruijnLocalPairLawMonotonicity

/-!
# Finite-defect lossless producers along the de Bruijn–Newman flow

Let `H_t(z) = ∫ Φ(x) e^{tx²} e^{izx} dx` (`DeBruijn.riemannHeat`), so `H_0 = Ξ`.

* `exists_riemannHeat_eq_defect_mul_ptr`: for every `t > 0` there are a finite set `N` of
  divisor copies of `H_t`, exactly its non-real zeros, and a lossless product-port limit `G`, with

    `H_t(z) = ∏_{q ∈ N} (1 − z/a_q) · G(z)`.

  Ki–Kim–Lee reality at large height and the strip `|Im z| ≤ ½` make the non-real zeros finitely
  many (`finite_nonreal_zeroCopy_riemannHeat`). Over this reflection-closed set the genus-one
  factors multiply to the polynomial `∏(1 − z/a)`, because `Σ 1/a = 0`. The real zeros form a
  reflection-closed real canonical product, which is a lossless product-port limit.
* `isPtrProductPortLimit_riemannHeat_of_eighth_le`: for `t ≥ 1/8` there is no defect.
* `riemannHypothesis_iff_forall_isPtrProductPortLimit_riemannHeat`: RH holds iff `H_t` is a
  lossless product-port limit for every `t > 0`.
* `riemannHeat_defect_transition`: for every `t > 0` the defect is a polynomial of finite degree.
  For every `t < 0` there are infinitely many non-real zeros (Newman–Rodgers–Tao in the corpus).
  `Ξ` is the critical medium of the flow, and RH says the critical medium carries no defect.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.EntireZeroDivisor

namespace RHTower

noncomputable section

variable {f : ℂ → ℂ}

/-- Zero copies of a function with an order-one envelope in a bounded set are finitely many. -/
theorem finite_zeroCopy_norm_le {C : ℝ} (hC : 0 ≤ C) (hf : AnalyticOnNhd ℂ f univ)
    (hf0 : f 0 ≠ 0)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) (R : ℝ) :
    {q : ZeroCopy f | ‖zeroCopyPoint f q‖ ≤ R}.Finite := by
  have hsum := OrderOneHadamard.summable_inv_sq_zeroCopyPoint hC hf hf0 hbound
  set R' : ℝ := max R 0 + 1 with hR'
  have hR'pos : 0 < R' := by positivity
  have hev : ∀ᶠ q in cofinite, 1 / ‖zeroCopyPoint f q‖ ^ (2 : ℕ) < 1 / R' ^ (2 : ℕ) :=
    hsum.tendsto_cofinite_zero.eventually_lt_const (by positivity)
  refine (Filter.eventually_cofinite.mp hev).subset ?_
  intro q hq
  simp only [mem_setOf_eq, not_lt] at hq ⊢
  have hane := zeroCopyPoint_ne_zero hf hf0 q
  have hpos : 0 < ‖zeroCopyPoint f q‖ := norm_pos_iff.mpr hane
  have hlt : ‖zeroCopyPoint f q‖ < R' := by
    have := le_max_left R 0; linarith
  rw [one_div_le_one_div (by positivity) (by positivity)]
  exact pow_le_pow_left₀ hpos.le hlt.le 2

theorem riemannHeat_zero_ne {t : ℝ} (ht : 0 ≤ t) : DeBruijn.riemannHeat t 0 ≠ 0 :=
  (DeBruijn.riemannKernel_superExp.mul_exp_sq ht).cosTransform_zero_ne

/-- **Finitely many defects.** For `t > 0`, `H_t` has finitely many non-real zero copies. -/
theorem finite_nonreal_zeroCopy_riemannHeat {t : ℝ} (ht : 0 < t) :
    {q : ZeroCopy (DeBruijn.riemannHeat t) |
      (zeroCopyPoint (DeBruijn.riemannHeat t) q).im ≠ 0}.Finite := by
  obtain ⟨X₀, hX₀⟩ := DeBruijn.exists_riemannHeat_zeros_real ht
  obtain ⟨C, hC0, hC⟩ := (DeBruijn.riemannKernel_superExp.mul_exp_sq ht.le).exists_envelope
  refine (finite_zeroCopy_norm_le hC0 (DeBruijn.riemannHeat_analytic ht.le)
    (riemannHeat_zero_ne ht.le) hC (|X₀| + 1)).subset ?_
  intro q hq
  simp only [mem_setOf_eq] at hq ⊢
  set z := zeroCopyPoint (DeBruijn.riemannHeat t) q
  have hz : DeBruijn.riemannHeat t z = 0 := DeBruijn.apply_zeroCopyPoint
    (DeBruijn.riemannHeat_analytic ht.le) q
  have hre : |z.re| < X₀ := by
    by_contra hle
    exact hq (hX₀ z hz (not_lt.mp hle))
  have him : |z.im| ≤ 1 / 2 := by
    have h1 := DeBruijn.riemannHeat_zeros_im_sq_le ht hz
    have h2 : z.im ^ 2 ≤ (1 / 2) ^ 2 := h1.trans (max_le (by nlinarith) (by norm_num))
    have := sq_le_sq.mp h2
    rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ |X₀| + 1 := by linarith [le_abs_self X₀]

/-- On a finite reflection-closed set of nonzero points the genus-one factors multiply to the
polynomial `∏ (1 − z/a)`. -/
theorem prod_weierstrassE1_eq_prod_of_reflect {ι : Type*} (a : ι → ℂ) (σ : ι → ι)
    (hσσ : ∀ i, σ (σ i) = i) (hσa : ∀ i, a (σ i) = -a i) (hane : ∀ i, a i ≠ 0)
    (N : Finset ι) (hN : ∀ i ∈ N, σ i ∈ N) (z : ℂ) :
    ∏ i ∈ N, weierstrassE1 (z / a i) = ∏ i ∈ N, (1 - z / a i) := by
  have hsum : ∑ i ∈ N, z / a i = 0 := by
    refine Finset.sum_involution (fun i _ => σ i) (fun i _ => ?_) (fun i _ hne => ?_)
      (fun i hi => hN i hi) (fun i _ => hσσ i)
    · rw [hσa, div_neg, add_neg_cancel]
    · intro hfix
      have h1 : a i = -a i := by
        have := hσa i
        rwa [hfix] at this
      exact hane i (by linear_combination h1 / 2)
  unfold weierstrassE1
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, hsum, Complex.exp_zero, mul_one]

/-- **Finite-defect factorisation.** An even function of order one with `f(0) ≠ 0` and finitely
many non-real zeros is a polynomial whose roots are exactly those zeros, times a lossless
product-port limit. -/
theorem exists_eq_defect_mul_ptr_of_finite_nonreal {C : ℝ} (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f univ) (hf0 : f 0 ≠ 0) (heven : ∀ z, f (-z) = f z)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    (hfin : {q : ZeroCopy f | (zeroCopyPoint f q).im ≠ 0}.Finite) :
    ∃ N : Finset (ZeroCopy f), (∀ q, q ∈ N ↔ (zeroCopyPoint f q).im ≠ 0) ∧
      ∃ G : ℂ → ℂ, IsPtrProductPortLimit G ∧
        ∀ z, f z = (∏ q ∈ N, (1 - z / zeroCopyPoint f q)) * G z := by
  classical
  set a := zeroCopyPoint f with hadef
  set σ := OrderOneHadamard.zeroCopyReflect hf heven with hσdef
  have hσσ : ∀ q, σ (σ q) = q := zeroCopyReflect_involutive hf heven
  have hσa : ∀ q, a (σ q) = -a q := OrderOneHadamard.zeroCopyPoint_reflect hf heven
  have hane : ∀ q, a q ≠ 0 := zeroCopyPoint_ne_zero hf hf0
  have hsum := OrderOneHadamard.summable_inv_sq_zeroCopyPoint hC hf hf0 hbound
  have hford := DeBruijn.analyticOrderAt_ne_top_of_ne_zero hf hf0
  have hfac := OrderOneHadamard.eq_const_mul_hadamardProduct_of_even hC hf hf0 hford heven hbound
  obtain ⟨N, hmem⟩ : ∃ N : Finset (ZeroCopy f), ∀ q, q ∈ N ↔ (a q).im ≠ 0 :=
    ⟨hfin.toFinset, fun q => hfin.mem_toFinset⟩
  have hNσ : ∀ q ∈ N, σ q ∈ N := by
    intro q hq
    rw [hmem] at hq ⊢
    rw [hσa, Complex.neg_im]
    exact neg_ne_zero.mpr hq
  set ι' := ↥((N : Set (ZeroCopy f))ᶜ)
  have hnot : ∀ q : ι', q.1 ∉ N := fun q h => q.2 (Finset.mem_coe.mpr h)
  have hσ' : ∀ q : ι', σ q.1 ∈ ((N : Set (ZeroCopy f))ᶜ) := by
    intro q hq
    apply hnot q
    have := hNσ _ (Finset.mem_coe.mp hq)
    rwa [hσσ] at this
  set a' : ι' → ℂ := fun q => a q.1 with ha'
  set σ' : ι' → ι' := fun q => ⟨σ q.1, hσ' q⟩ with hσ'def
  have hσσ' : ∀ q, σ' (σ' q) = q := fun q => Subtype.ext (hσσ q.1)
  have hσa' : ∀ q, a' (σ' q) = -a' q := fun q => hσa q.1
  have him' : ∀ q, (a' q).im = 0 := by
    intro q
    by_contra h
    exact hnot q ((hmem q.1).mpr h)
  have hane' : ∀ q, a' q ≠ 0 := fun q => hane q.1
  have hsum' : Summable (fun q : ι' => 1 / ‖a' q‖ ^ (2 : ℕ)) :=
    hsum.subtype ((N : Set (ZeroCopy f))ᶜ)
  have hG := isPtrProductPortLimit_const_mul_canonicalProduct a' σ' hσσ' hσa' him' hane' hsum' hf0
  refine ⟨N, hmem, fun z => f 0 * canonicalProductE1Indexed a' z, hG, fun z => ?_⟩
  have hcompl : HasProd (fun q : ι' => weierstrassE1 (z / a' q)) (canonicalProductE1Indexed a' z) :=
    (multipliable_canonicalProductE1Indexed hane' hsum' z).hasProd
  have hsplit : HasProd (fun q => weierstrassE1 (z / a q))
      ((∏ q ∈ N, weierstrassE1 (z / a q)) * canonicalProductE1Indexed a' z) :=
    (N.hasProd (fun q => weierstrassE1 (z / a q))).mul_compl hcompl
  rw [hfac z]
  change f 0 * canonicalProductE1Indexed a z = _
  rw [show canonicalProductE1Indexed a z = _ from hsplit.tprod_eq,
    prod_weierstrassE1_eq_prod_of_reflect a σ hσσ hσa hane N hNσ z]
  ring

/-- **Finite-defect lossless producer.** For every `t > 0`, `H_t` is a polynomial whose roots are
exactly its non-real zeros, times a lossless product-port limit. -/
theorem exists_riemannHeat_eq_defect_mul_ptr {t : ℝ} (ht : 0 < t) :
    ∃ N : Finset (ZeroCopy (DeBruijn.riemannHeat t)),
      (∀ q, q ∈ N ↔ (zeroCopyPoint (DeBruijn.riemannHeat t) q).im ≠ 0) ∧
      ∃ G : ℂ → ℂ, IsPtrProductPortLimit G ∧
        ∀ z, DeBruijn.riemannHeat t z =
          (∏ q ∈ N, (1 - z / zeroCopyPoint (DeBruijn.riemannHeat t) q)) * G z := by
  obtain ⟨C, hC0, hC⟩ := (DeBruijn.riemannKernel_superExp.mul_exp_sq ht.le).exists_envelope
  exact exists_eq_defect_mul_ptr_of_finite_nonreal hC0 (DeBruijn.riemannHeat_analytic ht.le)
    (riemannHeat_zero_ne ht.le) (DeBruijn.riemannHeat_neg ht.le) hC
    (finite_nonreal_zeroCopy_riemannHeat ht)

/-- For `t ≥ 1/8`, `H_t` is a lossless product-port limit. -/
theorem isPtrProductPortLimit_riemannHeat_of_eighth_le {t : ℝ} (ht : 1 / 8 ≤ t) :
    IsPtrProductPortLimit (DeBruijn.riemannHeat t) := by
  have ht0 : 0 ≤ t := by linarith
  obtain ⟨C, hC0, hC⟩ := (DeBruijn.riemannKernel_superExp.mul_exp_sq ht0).exists_envelope
  exact isPtrProductPortLimit_of_even_realZeros hC0 (DeBruijn.riemannHeat_analytic ht0)
    (riemannHeat_zero_ne ht0) (DeBruijn.riemannHeat_neg ht0) hC
    (fun z hz => DeBruijn.riemannHeat_zeros_real ht hz)

theorem riemannHeat_zero_eq_XiC : DeBruijn.riemannHeat 0 = XiC := by
  funext z
  rw [DeBruijn.riemannHeat_zero, XiC, mul_comm]

/-- **RH is the lossless continuation of the heat flow.** -/
theorem riemannHypothesis_iff_forall_isPtrProductPortLimit_riemannHeat :
    RiemannHypothesis ↔ ∀ t : ℝ, 0 < t → IsPtrProductPortLimit (DeBruijn.riemannHeat t) := by
  constructor
  · intro hRH t ht
    have hreal0 := DeBruijn.riemannHypothesis_iff_riemannHeat_zero_real.mp hRH
    have hzeros : ∀ w, DeBruijn.cosTransform riemannKernelReal w = 0 → w.im ^ 2 ≤ 0 := by
      intro w hw
      rw [DeBruijn.cosTransform_riemannKernel, ← DeBruijn.riemannHeat_zero] at hw
      rw [hreal0 w hw]; norm_num
    obtain ⟨C, hC0, hC⟩ := (DeBruijn.riemannKernel_superExp.mul_exp_sq ht.le).exists_envelope
    exact isPtrProductPortLimit_of_even_realZeros hC0 (DeBruijn.riemannHeat_analytic ht.le)
      (riemannHeat_zero_ne ht.le) (DeBruijn.riemannHeat_neg ht.le) hC
      (fun z hz => DeBruijn.cosTransform_heat_zeros_real DeBruijn.riemannKernel_superExp hzeros
        (by linarith) ht z hz)
  · intro hall
    have hconv := DeBruijn.tendstoLocallyUniformly_riemannHeat (t := 0) le_rfl
    have hX : IsPtrProductPortLimit (DeBruijn.riemannHeat 0) :=
      isPtrProductPortLimit_of_tendstoLocallyUniformly
        (fun n => by simpa using hall (0 + 1 / ((n : ℝ) + 1)) (by positivity)) hconv
    rw [riemannHeat_zero_eq_XiC] at hX
    exact riemannHypothesis_iff_XiC_limit_losslessProductPort.mpr hX

/-- **Critical medium.** For `t > 0` the non-real zeros of `H_t` are finitely many (a polynomial
defect); for `t < 0` they are infinitely many. -/
theorem riemannHeat_defect_transition :
    (∀ t : ℝ, 0 < t → {q : ZeroCopy (DeBruijn.riemannHeat t) |
      (zeroCopyPoint (DeBruijn.riemannHeat t) q).im ≠ 0}.Finite) ∧
    (∀ τ : ℝ, 0 < τ → {z : ℂ | DeBruijn.riemannHeat (-τ) z = 0 ∧ z.im ≠ 0}.Infinite) :=
  ⟨fun _ ht => finite_nonreal_zeroCopy_riemannHeat ht,
    fun _ hτ => DeBruijn.riemannHeat_neg_nonreal_zeros_infinite hτ⟩

end

end RHTower
