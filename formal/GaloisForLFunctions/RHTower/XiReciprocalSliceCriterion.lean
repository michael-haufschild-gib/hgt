import GaloisForLFunctions.RHTower.XiReciprocalCentreCriterion
import GaloisForLFunctions.RHTower.XiReciprocalSliceNearestZero

/-!
# RH as total positivity of one sequence at any single height

At a height `t` with `Ξ(t) ≠ 0`, the pair product `h_t(σ) = Ξ(t+σ)Ξ(t−σ)` (`xiHorizontalPair`) is
even and entire.  So `h_t(σ) = F_t(−σ²)` for the entire `F_t = xiSliceLift t`.

**Theorem** (`riemannHypothesis_iff_reciprocalTP_xiSliceLift`).  For every `t` with `Ξ(t) ≠ 0`, RH
holds iff the Taylor coefficients of `z ↦ 1/h_t(√z)` at `0` are nonnegative and consecutive-row
totally positive (`ReciprocalTP (xiSliceLift t)`).

* `⟸`: by deflation every zero of `F_t` is a negative real `−D`.  A zero `z` of `Ξ` gives
  `F_t(−(z − t)²) = 0`, so `(z − t)² = D > 0` and `z` is real.
* `⟹`: under RH each zero copy contributes the even factor
  `E₁((t+σ)/γ) E₁((t−σ)/γ) = e^{2t/γ} ((γ−t)² − σ²)/γ²`.  This is a positive multiple of
  `1 − σ²/(γ−t)²`, whose reciprocal has geometric even coefficients.
-/

open Complex Filter Topology Metric
open scoped ComplexOrder Nat
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

theorem xiHorizontalPair_neg' (t : ℝ) (σ : ℂ) :
    xiHorizontalPair t (-σ) = xiHorizontalPair t σ := by
  unfold xiHorizontalPair
  rw [sub_neg_eq_add, ← sub_eq_add_neg, mul_comm]

/-- The slice lift `F_t(y) = h_t(√(−y))`, entire, with `F_t(−σ²) = h_t(σ)`. -/
def xiSliceLift (t : ℝ) (y : ℂ) : ℂ := evenSquareLift (xiHorizontalPair t) (-y)

theorem differentiable_xiSliceLift (t : ℝ) : Differentiable ℂ (xiSliceLift t) :=
  (differentiable_evenSquareLift (differentiable_xiHorizontalPair t)).comp differentiable_neg

theorem xiSliceLift_neg_sq (t : ℝ) (σ : ℂ) : xiSliceLift t (-(σ ^ 2)) = xiHorizontalPair t σ := by
  unfold xiSliceLift
  rw [neg_neg]
  exact evenSquareLift_sq (differentiable_xiHorizontalPair t) (xiHorizontalPair_neg' t) σ

/-- **Reciprocal total positivity at one height implies RH.** -/
theorem riemannHypothesis_of_reciprocalTP_xiSliceLift {t : ℝ}
    (h : ReciprocalTP (xiSliceLift t)) : RiemannHypothesis := by
  rw [riemannHypothesis_iff_XiC_zeros_real]
  intro z hz
  have hzero : xiSliceLift t (-((z - t) ^ 2)) = 0 := by
    rw [xiSliceLift_neg_sq]
    unfold xiHorizontalPair
    rw [show (t : ℂ) + (z - t) = z by ring, hz, zero_mul]
  obtain ⟨D, hD, hDeq⟩ := h.eq_neg_of_apply_eq_zero hzero
  have ht2 : (z - t) ^ 2 = (D : ℂ) := by linear_combination -hDeq
  have him := congrArg Complex.im ht2
  have hre := congrArg Complex.re ht2
  simp only [sq, Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, sub_zero] at him hre
  by_contra hne
  have hre0 : z.re - t = 0 := by
    have : 2 * (z.re - t) * z.im = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · exact absurd h1 hne
  rw [hre0] at hre
  nlinarith [sq_nonneg z.im]

/-- A positive multiple of an even-reciprocally PF function is even-reciprocally PF. -/
theorem EvenRecipPF.const_mul {u : ℂ → ℂ} (hu : EvenRecipPF u) {c : ℝ} (hc : 0 < c) :
    EvenRecipPF (fun σ => (c : ℂ) * u σ) := by
  have h := (evenRecipPF_const hc).mul hu
  exact h

/-- **Under RH, the pair product at a non-zero height is even-reciprocally PF.** -/
theorem evenRecipPF_xiHorizontalPair_of_riemannHypothesis (hRH : RiemannHypothesis) {t : ℝ}
    (ht : XiC t ≠ 0) : EvenRecipPF (xiHorizontalPair t) := by
  classical
  have hh0 : xiHorizontalPair t 0 ≠ 0 := by
    unfold xiHorizontalPair
    simpa using mul_ne_zero ht ht
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ∀ σ ∈ ball (0 : ℂ) r, xiHorizontalPair t σ ≠ 0 := by
    have := (differentiable_xiHorizontalPair t).continuous.continuousAt.eventually_ne hh0
    obtain ⟨r, hr, hsub⟩ := Metric.eventually_nhds_iff_ball.mp this
    exact ⟨r, hr, fun σ hσ => hsub σ hσ⟩
  -- each copy contributes an even factor
  set f : XiZeroCopy → ℂ → ℂ := fun q σ =>
    weierstrassE1 (((t : ℂ) + σ) / xiSpectralPoint q) *
      weierstrassE1 (((t : ℂ) - σ) / xiSpectralPoint q) with hf
  have hfac : ∀ q, EvenRecipPF (f q) := by
    intro q
    obtain ⟨γ, hγ⟩ := xiSpectralPoint_real_of_rh hRH q
    have hγ0 : γ ≠ 0 := by
      intro h0
      apply xiSpectralPoint_ne_zero q
      rw [hγ, h0, Complex.ofReal_zero]
    have hγt : γ - t ≠ 0 := by
      intro h0
      apply ht
      have : XiC (xiSpectralPoint q) = 0 :=
        (XiC_eq_zero_iff_exists_xiZeroCopy _).mpr ⟨q, rfl⟩
      rw [hγ] at this
      rwa [show (t : ℂ) = (γ : ℂ) by exact_mod_cast (by linarith : t = γ)]
    have e : f q = fun σ : ℂ =>
        ((Real.exp (2 * t / γ) * (γ - t) ^ 2 / γ ^ 2 : ℝ) : ℂ) *
          (1 - σ ^ 2 / (((γ - t) ^ 2 : ℝ) : ℂ)) := by
      funext σ
      have h1 := weierstrassE1_slice_pair (t := t) hγ0 (I * σ)
      simp only [hf, hγ]
      have e1 : ((t : ℂ) - I * (I * σ)) = (t : ℂ) + σ := by
        ring_nf
        rw [Complex.I_sq]
        ring
      have e2 : ((t : ℂ) + I * (I * σ)) = (t : ℂ) - σ := by
        ring_nf
        rw [Complex.I_sq]
        ring
      rw [e1, e2] at h1
      rw [h1]
      have hII : ∀ B : ℂ, B * (I * σ) * (I * σ) = -(B * σ ^ 2) := fun B => by
        ring_nf
        rw [Complex.I_sq]
        ring
      rw [hII]
      have hγtc : (γ : ℂ) - (t : ℂ) ≠ 0 := by
        rw [← Complex.ofReal_sub]
        exact_mod_cast hγt
      have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ0
      push_cast
      field_simp
      ring
    rw [e]
    exact EvenRecipPF.const_mul (EvenRecipPF.one_sub_sq_div (by positivity)) (by positivity)
  have hfin : ∀ S : Finset XiZeroCopy, EvenRecipPF (fun σ => ∏ q ∈ S, f q σ) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using EvenRecipPF.one
    | insert q S hq ih =>
      have e : (fun σ => ∏ q' ∈ insert q S, f q' σ) = f q * fun σ => ∏ q' ∈ S, f q' σ := by
        funext σ
        rw [Pi.mul_apply, Finset.prod_insert hq]
      rw [e]
      exact (hfac q).mul ih
  -- convergence of the partial products on the zero-free disk
  set φm : ℂ → ℂ := fun σ => (t : ℂ) + σ with hφm
  set φp : ℂ → ℂ := fun σ => (t : ℂ) - σ with hφp
  have hP : TendstoLocallyUniformlyOn
      (fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) xiCanonicalProduct atTop
      Set.univ := xiCanonicalProduct_hasProdLocallyUniformlyOn
  have hPcont : Continuous xiCanonicalProduct :=
    continuous_iff_continuousAt.mpr fun z =>
      (xiCanonicalProduct_analytic z (Set.mem_univ z)).continuousAt
  have hPdiff : Differentiable ℂ xiCanonicalProduct := fun z =>
    (xiCanonicalProduct_analytic z (Set.mem_univ z)).differentiableAt
  have hcm : Continuous φm := by rw [hφm]; fun_prop
  have hcp : Continuous φp := by rw [hφp]; fun_prop
  have hm := TendstoLocallyUniformlyOn.comp hP φm (Set.mapsTo_univ φm Set.univ) hcm.continuousOn
  have hp := TendstoLocallyUniformlyOn.comp hP φp (Set.mapsTo_univ φp Set.univ) hcp.continuousOn
  have hmul := hm.mul₀ hp (hPcont.comp hcm).continuousOn (hPcont.comp hcp).continuousOn
  have hX : ∀ a, XiC a = XiC 0 * xiCanonicalProduct a := fun a => by
    simpa only [Pi.mul_apply] using congrFun XiC_eq_constant_mul_canonicalProduct a
  set Q : ℂ → ℂ := (xiCanonicalProduct ∘ φm) * (xiCanonicalProduct ∘ φp) with hQ
  have hQne : ∀ σ ∈ ball (0 : ℂ) r, Q σ ≠ 0 := by
    intro σ hσ h
    apply hball σ hσ
    unfold xiHorizontalPair
    rw [hX ((t : ℂ) + σ), hX ((t : ℂ) - σ)]
    simp only [hQ, Pi.mul_apply, Function.comp_apply, hφm, hφp] at h
    rw [show XiC 0 * xiCanonicalProduct ((t : ℂ) + σ) * (XiC 0 * xiCanonicalProduct ((t : ℂ) - σ)) =
      XiC 0 * XiC 0 * (xiCanonicalProduct ((t : ℂ) + σ) * xiCanonicalProduct ((t : ℂ) - σ)) by ring,
      h, mul_zero]
  have hfinne : ∀ S : Finset XiZeroCopy, ∀ σ ∈ ball (0 : ℂ) r, (∏ q ∈ S, f q σ) ≠ 0 := by
    intro S σ hσ
    rw [Finset.prod_ne_zero_iff]
    intro q _ hzero
    simp only [hf, weierstrassE1] at hzero
    have hσq : ((t : ℂ) + σ) = xiSpectralPoint q ∨ ((t : ℂ) - σ) = xiSpectralPoint q := by
      have hz := xiSpectralPoint_ne_zero q
      rcases mul_eq_zero.mp hzero with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · left
          field_simp at h'
          linear_combination -h'
        · exact absurd h' (Complex.exp_ne_zero _)
      · rcases mul_eq_zero.mp h with h' | h'
        · right
          field_simp at h'
          linear_combination -h'
        · exact absurd h' (Complex.exp_ne_zero _)
    apply hball σ hσ
    unfold xiHorizontalPair
    have hzq : XiC (xiSpectralPoint q) = 0 := (XiC_eq_zero_iff_exists_xiZeroCopy _).mpr ⟨q, rfl⟩
    rcases hσq with h | h
    · rw [h, hzq, zero_mul]
    · rw [h, hzq, mul_zero]
  have hQlim : EvenRecipPF Q := by
    have hconv := (hmul.mono (Set.subset_univ (ball (0 : ℂ) r)))
    refine EvenRecipPF.of_tendstoLocallyUniformlyOn (l := (atTop : Filter (Finset XiZeroCopy)))
      hr hfin (fun S => ?_) hfinne
      ((hPdiff.comp (by rw [hφm]; fun_prop)).mul
        (hPdiff.comp (by rw [hφp]; fun_prop))).differentiableOn hQne ?_
    · intro σ _
      refine (Differentiable.differentiableAt ?_).differentiableWithinAt
      refine Differentiable.fun_finsetProd fun q _ => ?_
      simp only [hf, weierstrassE1]
      fun_prop
    · refine hconv.congr fun S σ _ => ?_
      simp only [Pi.mul_apply, Function.comp_apply, hf, hφm, hφp]
      rw [Finset.prod_mul_distrib]
  have hXreal := XiC_zero_eq_ofReal
  have hXpos := re_xi_half_pos
  have heq : xiHorizontalPair t = fun σ => ((((xi ((1 / 2 : ℝ) : ℂ)).re) ^ 2 : ℝ) : ℂ) * Q σ := by
    funext σ
    unfold xiHorizontalPair
    rw [hX ((t : ℂ) + σ), hX ((t : ℂ) - σ), hXreal]
    simp only [hQ, Pi.mul_apply, Function.comp_apply, hφm, hφp]
    push_cast
    ring
  rw [heq]
  exact EvenRecipPF.const_mul hQlim (by positivity)

/-- **RH is total positivity of one sequence at any single height.**  For every height `t` with
`Ξ(t) ≠ 0`, RH holds iff the Taylor coefficients of `z ↦ 1/(Ξ(t+√z)Ξ(t−√z))` at `0` are
nonnegative and consecutive-row totally positive. -/
theorem riemannHypothesis_iff_reciprocalTP_xiSliceLift {t : ℝ} (ht : XiC t ≠ 0) :
    RiemannHypothesis ↔ ReciprocalTP (xiSliceLift t) := by
  refine ⟨fun hRH => ?_, riemannHypothesis_of_reciprocalTP_xiSliceLift⟩
  have hE := evenRecipPF_xiHorizontalPair_of_riemannHypothesis hRH ht
  have hh0 : xiSliceLift t 0 ≠ 0 := by
    have h := xiSliceLift_neg_sq t 0
    rw [show -((0 : ℂ) ^ 2) = 0 by ring] at h
    rw [h]
    unfold xiHorizontalPair
    simpa using mul_ne_zero ht ht
  set g : ℂ → ℂ := recipNeg (xiSliceLift t) with hg
  have hgsq : (fun σ => g (σ ^ 2)) = fun σ => (xiHorizontalPair t σ)⁻¹ := by
    funext σ
    simp only [hg, recipNeg, xiSliceLift, neg_neg]
    rw [evenSquareLift_sq (differentiable_xiHorizontalPair t) (xiHorizontalPair_neg' t)]
  have hgan : AnalyticAt ℂ g 0 := by
    have hne : xiSliceLift t (-0) ≠ 0 := by simpa using hh0
    exact (((differentiable_xiSliceLift t).comp differentiable_neg).analyticAt 0).inv hne
  have hcoef : ∀ n, ((n ! : ℂ))⁻¹ * iteratedDeriv n g 0 =
      ((evenRecipCoeff (xiHorizontalPair t) n : ℝ) : ℂ) := by
    intro n
    rw [← iteratedDeriv_comp_sq hgan n, hgsq]
    exact hE.coeff_real n
  refine ⟨differentiable_xiSliceLift t, hh0, fun n => ?_, ?_⟩
  · have hD : iteratedDeriv n g 0 =
        ((n ! : ℂ)) * ((evenRecipCoeff (xiHorizontalPair t) n : ℝ) : ℂ) := by
      rw [← hcoef n]
      have : (n ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
      field_simp
    show 0 ≤ iteratedDeriv n g 0
    rw [hD]
    refine mul_nonneg (Nat.cast_nonneg _) (Complex.zero_le_real.mpr ?_)
    have := hE.pf 1 1 le_rfl (fun _ => 0) (fun _ => n) (Subsingleton.strictMono _)
      (Subsingleton.strictMono _)
    simpa [toeplitzMinor, Matrix.det_unique, zext_natCast] using this
  · have heq : recipCoeff (xiSliceLift t) = evenRecipCoeff (xiHorizontalPair t) := by
      funext n
      unfold recipCoeff
      rw [← hg, hcoef n, Complex.ofReal_re]
    rw [heq]
    intro m i₀ j hj
    exact hE.pf m m le_rfl _ j (fun a b hab => by simpa using hab) hj

end

end RHTower
