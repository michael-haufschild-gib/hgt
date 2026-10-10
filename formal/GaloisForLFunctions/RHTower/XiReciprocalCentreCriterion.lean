import GaloisForLFunctions.RHTower.XiReciprocalCentreTotalPositivity
import GaloisForLFunctions.RHTower.XiHorizontalSlicePolyaFrequencyCriterion
import GaloisForLFunctions.HTGeometry.EvenReciprocalTotalPositivity

/-!
# RH as total positivity of one explicit sequence

**Theorem** (`riemannHypothesis_iff_reciprocalTP_xiCentreLift`).  The Riemann hypothesis holds
if and only if the Taylor coefficients of `z ↦ 1/Ξ(√z)` at `0` are nonnegative and every Toeplitz
minor of them with consecutive rows is nonnegative.

* `⟸` is the deflation theorem (`riemannHypothesis_of_reciprocalTP_xiCentreLift`).
* `⟹`: under RH every zero of `Ξ` is real.  Grouping the Hadamard product
  `Ξ(σ) = Ξ(0) ∏ E₁(σ/γ)` into reflection pairs gives factors `1 − σ²/γ²`.  Their reciprocals have
  geometric even coefficients `γ^{−2m}` (`HTGeometry.EvenRecipPF.one_sub_sq_div`).  Even-reciprocal
  total positivity is closed under products and under locally uniform limits on a zero-free
  disk (`HTGeometry.EvenRecipPF.mul`, `HTGeometry.EvenRecipPF.of_tendstoLocallyUniformlyOn`).
  The coefficients of `g(z) = 1/Ξ(√z)` are the even coefficients of `g(σ²) = 1/Ξ(σ)`
  (`HTGeometry.iteratedDeriv_comp_sq`).
-/

open Complex Filter Topology Metric
open scoped ComplexOrder Nat
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The reflection pair of Weierstrass factors: `E₁(σ/z) E₁(σ/(−z)) = 1 − σ²/z²`. -/
theorem weierstrassE1_reflection_pair {z : ℂ} (hz : z ≠ 0) (σ : ℂ) :
    weierstrassE1 (σ / z) * weierstrassE1 (σ / -z) = 1 - σ ^ 2 / z ^ 2 := by
  unfold weierstrassE1
  have hexp : cexp (σ / z) * cexp (σ / -z) = 1 := by
    rw [← Complex.exp_add, show σ / z + σ / -z = 0 by field_simp; ring, Complex.exp_zero]
  calc (1 - σ / z) * cexp (σ / z) * ((1 - σ / -z) * cexp (σ / -z))
      = (1 - σ / z) * (1 - σ / -z) * (cexp (σ / z) * cexp (σ / -z)) := by ring
    _ = 1 - σ ^ 2 / z ^ 2 := by
      rw [hexp, mul_one]
      field_simp
      ring

/-- A positive constant is even-reciprocally PF. -/
theorem evenRecipPF_const {c : ℝ} (hc : 0 < c) : EvenRecipPF (fun _ : ℂ => (c : ℂ)) := by
  have hinv : (fun σ : ℂ => ((fun _ : ℂ => (c : ℂ)) σ)⁻¹) = fun _ => ((c⁻¹ : ℝ) : ℂ) := by
    funext σ
    simp
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨analyticAt_const, hcne, fun m => ?_, fun m => ?_, fun k => ?_⟩
  · rw [hinv, iteratedDeriv_const]
    simp
  · rw [hinv, iteratedDeriv_const]
    split_ifs
    · exact Complex.zero_le_real.mpr (inv_nonneg.mpr hc.le)
    · exact le_rfl
  · have hcoef : evenRecipCoeff (fun _ : ℂ => (c : ℂ)) = twoTermSeq c⁻¹ 0 := by
      funext m
      unfold evenRecipCoeff twoTermSeq
      rw [hinv, iteratedDeriv_const]
      rcases m with _ | _ | m <;> simp
    rw [hcoef]
    exact PFSeq.twoTerm (inv_nonneg.mpr hc.le) le_rfl k

/-- **Under RH, `Ξ` is even-reciprocally totally positive.** -/
theorem evenRecipPF_XiC_of_riemannHypothesis (hRH : RiemannHypothesis) : EvenRecipPF XiC := by
  classical
  -- a zero-free disk about `0`
  have hXi0 : XiC 0 ≠ 0 := by
    have : XiC 0 = xi (((1 / 2 : ℝ)) : ℂ) := by simp [XiC]
    rw [this]
    exact xi_ne_zero_of_real _
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ∀ σ ∈ ball (0 : ℂ) r, XiC σ ≠ 0 := by
    have := XiC_differentiable.continuous.continuousAt.eventually_ne hXi0
    obtain ⟨r, hr, hsub⟩ := Metric.eventually_nhds_iff_ball.mp this
    exact ⟨r, hr, fun σ hσ => hsub σ hσ⟩
  have hfar : ∀ q : XiZeroCopy, r ≤ ‖xiSpectralPoint q‖ := by
    intro q
    by_contra hlt
    push Not at hlt
    exact hball _ (by rwa [mem_ball, dist_zero_right])
      ((XiC_eq_zero_iff_exists_xiZeroCopy _).mpr ⟨q, rfl⟩)
  -- the reflection-closed partial products
  set σr := xiZeroCopyReflectEquiv with hσr
  let c : Finset XiZeroCopy → Finset XiZeroCopy := fun S => S ∪ S.image σr
  have hc : Tendsto c atTop atTop :=
    tendsto_atTop_mono (fun S => Finset.subset_union_left) tendsto_id
  have hclosed : ∀ S, ∀ a ∈ c S, σr a ∈ c S := by
    intro S a ha
    simp only [c, Finset.mem_union, Finset.mem_image] at ha ⊢
    rcases ha with ha | ⟨b, hb, rfl⟩
    · exact Or.inr ⟨a, ha, rfl⟩
    · left
      rw [hσr, xiZeroCopyReflectEquiv_apply_apply]
      exact hb
  set f : XiZeroCopy → ℂ → ℂ := fun q σ => weierstrassE1 (σ / xiSpectralPoint q) with hf
  have hpair : ∀ q, σr q ≠ q → EvenRecipPF (f q * f (σr q)) := by
    intro q _
    obtain ⟨γ, hγ⟩ := xiSpectralPoint_real_of_rh hRH q
    have hγ0 : γ ≠ 0 := by
      intro h0
      apply xiSpectralPoint_ne_zero q
      rw [hγ, h0, Complex.ofReal_zero]
    have e : f q * f (σr q) = fun σ : ℂ => 1 - σ ^ 2 / ((γ ^ 2 : ℝ) : ℂ) := by
      funext σ
      simp only [Pi.mul_apply, hf, hσr, xiSpectralPoint_reflect, hγ]
      rw [weierstrassE1_reflection_pair (by exact_mod_cast hγ0)]
      push_cast
      ring
    rw [e]
    exact EvenRecipPF.one_sub_sq_div (by positivity)
  have hfin : ∀ S : Finset XiZeroCopy, EvenRecipPF (fun σ => ∏ q ∈ c S, f q σ) :=
    fun S => prod_of_involution_of_mul EvenRecipPF.one (fun _ _ hf hg => hf.mul hg) σr
      xiZeroCopyReflectEquiv_apply_apply f
      (fun a ha => absurd ha (xiZeroCopyReflectEquiv_ne_self a)) hpair (c S) (hclosed S)
  -- the factors do not vanish on the disk
  have hfac_ne : ∀ q : XiZeroCopy, ∀ σ ∈ ball (0 : ℂ) r, f q σ ≠ 0 := by
    intro q σ hσ
    simp only [hf, weierstrassE1]
    refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
    intro h
    have hσq : σ = xiSpectralPoint q := by
      have hz := xiSpectralPoint_ne_zero q
      field_simp at h
      linear_combination -h
    rw [mem_ball, dist_zero_right, hσq] at hσ
    exact absurd (hfar q) (not_le.mpr hσ)
  have hP : TendstoLocallyUniformlyOn
      (fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) xiCanonicalProduct atTop
      Set.univ := xiCanonicalProduct_hasProdLocallyUniformlyOn
  have hPc := (tendstoLocallyUniformlyOn_comp_index hP hc).mono (Set.subset_univ (ball 0 r))
  have hPdiff : Differentiable ℂ xiCanonicalProduct := fun z =>
    (xiCanonicalProduct_analytic z (Set.mem_univ z)).differentiableAt
  have hX : ∀ σ, XiC σ = XiC 0 * xiCanonicalProduct σ := fun σ => by
    simpa only [Pi.mul_apply] using congrFun XiC_eq_constant_mul_canonicalProduct σ
  have hPne : ∀ σ ∈ ball (0 : ℂ) r, xiCanonicalProduct σ ≠ 0 := by
    intro σ hσ h
    apply hball σ hσ
    rw [hX, h, mul_zero]
  have hlim : EvenRecipPF xiCanonicalProduct := by
    refine EvenRecipPF.of_tendstoLocallyUniformlyOn hr hfin (fun S => ?_) (fun S σ hσ => ?_)
      hPdiff.differentiableOn hPne hPc
    · refine DifferentiableOn.congr (f := fun σ => ∏ q ∈ c S, f q σ) ?_ (fun _ _ => rfl)
      intro σ _
      refine (Differentiable.differentiableAt ?_).differentiableWithinAt
      refine Differentiable.fun_finsetProd fun q _ => ?_
      simp only [hf, weierstrassE1]
      fun_prop
    · rw [Finset.prod_ne_zero_iff]
      exact fun q _ => hfac_ne q σ hσ
  -- multiply by the positive constant `Ξ(0)`
  have hXreal := XiC_zero_eq_ofReal
  have hXpos := re_xi_half_pos
  have hXeq : XiC = (fun _ : ℂ => (((xi ((1 / 2 : ℝ) : ℂ)).re : ℝ) : ℂ)) * xiCanonicalProduct := by
    funext σ
    rw [hX σ, hXreal]
    rfl
  rw [hXeq]
  exact (evenRecipPF_const hXpos).mul hlim

/-- **RH is total positivity of the reciprocal centre sequence.**  The Riemann hypothesis holds if
and only if the Taylor coefficients of `z ↦ 1/Ξ(√z)` at `0` are nonnegative and every Toeplitz
minor of them with consecutive rows is nonnegative. -/
theorem riemannHypothesis_iff_reciprocalTP_xiCentreLift :
    RiemannHypothesis ↔ ReciprocalTP xiCentreLift := by
  refine ⟨fun hRH => ?_, riemannHypothesis_of_reciprocalTP_xiCentreLift⟩
  have hE := evenRecipPF_XiC_of_riemannHypothesis hRH
  set g : ℂ → ℂ := recipNeg xiCentreLift with hg
  have hgsq : (fun σ => g (σ ^ 2)) = fun σ => (XiC σ)⁻¹ := by
    funext σ
    simp only [hg, recipNeg, xiCentreLift, neg_neg]
    rw [evenSquareLift_sq XiC_differentiable XiC_even]
  have hgan : AnalyticAt ℂ g 0 := by
    have hne : xiCentreLift (-0) ≠ 0 := by simpa using xiCentreLift_zero_ne_zero
    exact ((differentiable_xiCentreLift.comp differentiable_neg).analyticAt 0).inv hne
  have hcoef : ∀ n, ((n ! : ℂ))⁻¹ * iteratedDeriv n g 0 = ((evenRecipCoeff XiC n : ℝ) : ℂ) := by
    intro n
    rw [← iteratedDeriv_comp_sq hgan n, hgsq]
    exact hE.coeff_real n
  refine ⟨differentiable_xiCentreLift, xiCentreLift_zero_ne_zero, fun n => ?_, ?_⟩
  · have hD : iteratedDeriv n g 0 = ((n ! : ℂ)) * ((evenRecipCoeff XiC n : ℝ) : ℂ) := by
      rw [← hcoef n]
      have : (n ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
      field_simp
    show 0 ≤ iteratedDeriv n g 0
    rw [hD]
    refine mul_nonneg (Nat.cast_nonneg _) (Complex.zero_le_real.mpr ?_)
    have := hE.pf 1 1 le_rfl (fun _ => 0) (fun _ => n) (Subsingleton.strictMono _)
      (Subsingleton.strictMono _)
    simpa [toeplitzMinor, Matrix.det_unique, zext_natCast] using this
  · have heq : recipCoeff xiCentreLift = evenRecipCoeff XiC := by
      funext n
      unfold recipCoeff
      rw [← hg, hcoef n, Complex.ofReal_re]
    rw [heq]
    intro m i₀ j hj
    exact hE.pf m m le_rfl _ j (fun a b hab => by simpa using hab) hj

end

end RHTower
