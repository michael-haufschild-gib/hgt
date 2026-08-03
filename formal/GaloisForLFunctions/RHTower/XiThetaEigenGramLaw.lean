import GaloisForLFunctions.RHTower.XiQuotientRealDecay
import GaloisForLFunctions.RHTower.SlabMassSquareCertificate

/-!
# The unconditional Gram law of the theta eigenfunctions

The removable quotients `u_alpha = i * dslope XiC alpha` attached to the zeros of the centered
completed zeta function are the Fourier images of Hedenmalm's theta eigenfunctions.  Their Weil
polarization is computed here without any hypothesis on the location of the zeros.

The Gram entry of `u_alpha` against `u_beta` vanishes unless `beta` is the complex conjugate of
`alpha`: the sharp involution evaluates the second quotient at the conjugate of the first zero,
which is again a zero of `XiC`, and a quotient based at one zero vanishes at every other.  So the
Gram matrix is carried by the conjugation involution on the divisor rather than by the diagonal.

Two consequences are immediate and unconditional: a nonreal zero makes its own eigenfunction null,
while a real zero gives the multiplicity-weighted squared derivative.  Combined with the finite
sesquilinear expansion, this identifies positive definiteness of the form on every finite span of
eigenfunctions with the conjunction of the Riemann hypothesis and simplicity of the zeros.
-/

open Complex Set Filter Topology

namespace RHTower

noncomputable section


theorem XiC_conj_eq_zero {alpha : ℂ} (halpha : XiC alpha = 0) :
    XiC ((starRingEnd ℂ) alpha) = 0 := by
  rw [XiC] at halpha ⊢
  have harg : 1 / 2 + (starRingEnd ℂ) alpha * I =
      1 - (starRingEnd ℂ) (1 / 2 + alpha * I) := by
    apply Complex.ext
    · simp
      ring
    · simp
  rw [harg, xi_one_sub, xi_conj, halpha, map_zero]

/-- The Hedenmalm--Weil Gram entry of two theta eigenfunction quotients: the pairing is carried by
the conjugation involution on the Xi divisor, not by the diagonal. -/
def xiThetaEigenGram (alpha beta : ℂ) : ℂ :=
  if beta = (starRingEnd ℂ) alpha then
    (xiSpectralMultiplicity alpha : ℂ) * (I * deriv XiC alpha) *
      (starRingEnd ℂ) (I * deriv XiC beta)
  else 0

/-- **The unconditional theta-eigenfunction Gram law.**  For any two zeros of `XiC` the Weil
polarization of the corresponding removable quotients vanishes unless the second zero is the
complex conjugate of the first, in which case it is the multiplicity of the first zero times the
product of the two derivative values.  No hypothesis on the location of the zeros is used. -/
theorem xiWeilPolarization_thetaEigen
    {alpha beta : ℂ} (halpha : XiC alpha = 0) (hbeta : XiC beta = 0) :
    xiWeilPolarization (xiThetaEigenFourier alpha) (xiThetaEigenFourier beta) =
      xiThetaEigenGram alpha beta := by
  classical
  set S : Set XiZeroCopy := {q | xiSpectralPoint q = alpha} with hS
  set T : Finset XiZeroCopy := (finite_xiSpectralPoint_fiber alpha).toFinset with hT
  set v : ℂ := (I * deriv XiC alpha) *
    (starRingEnd ℂ) (xiThetaEigenFourier beta ((starRingEnd ℂ) alpha)) with hv
  have heq : ∀ q : XiZeroCopy,
      xiThetaEigenFourier alpha (xiSpectralPoint q) *
        xiWeilSharp (xiThetaEigenFourier beta) (xiSpectralPoint q) =
      (if q ∈ S then v else 0) := by
    intro q
    by_cases hq : xiSpectralPoint q = alpha
    · rw [xiThetaEigenFourier_spectralPoint halpha q, if_pos hq,
        if_pos (show q ∈ S from hq), xiWeilSharp, hq, hv]
    · rw [xiThetaEigenFourier_spectralPoint halpha q, if_neg hq, zero_mul,
        if_neg (show q ∉ S from hq)]
  have hsum : xiWeilPolarization (xiThetaEigenFourier alpha) (xiThetaEigenFourier beta) =
      (T.card : ℂ) * v := by
    rw [xiWeilPolarization]
    calc ∑' q : XiZeroCopy,
          xiThetaEigenFourier alpha (xiSpectralPoint q) *
            xiWeilSharp (xiThetaEigenFourier beta) (xiSpectralPoint q)
        = ∑' q : XiZeroCopy, (if q ∈ S then v else 0) := tsum_congr heq
      _ = ∑ q ∈ T, (if q ∈ S then v else 0) := by
          refine tsum_eq_sum (fun q hqT => ?_)
          have hqS : q ∉ S := fun hqS => hqT (by simpa only [hT, Set.Finite.mem_toFinset] using hqS)
          rw [if_neg hqS]
      _ = (T.card : ℂ) * v := by
          rw [Finset.sum_congr rfl (fun q hq => if_pos (show q ∈ S by
            simpa only [hT, Set.Finite.mem_toFinset] using hq))]
          simp
  rw [hsum, xiThetaEigenGram]
  have hcard : (T.card : ℂ) = (xiSpectralMultiplicity alpha : ℂ) := rfl
  split_ifs with hcase
  · rw [hcard, hv, hcase]
    rw [xiThetaEigenFourier_self]
    ring
  · have hzero : xiThetaEigenFourier beta ((starRingEnd ℂ) alpha) = 0 :=
      xiThetaEigenFourier_eq_zero_of_XiC_eq_zero hbeta (XiC_conj_eq_zero halpha)
        (fun hcon => hcase hcon.symm)
    rw [hv, hzero]
    simp


/-- **(21)** A nonreal Xi zero makes its own theta eigenfunction null for the Weil form: the sharp
involution evaluates the quotient at the conjugate zero, where it vanishes. -/
theorem xiWeilPolarization_thetaEigen_diagonal_eq_zero_of_im_ne_zero
    {alpha : ℂ} (halpha : XiC alpha = 0) (him : alpha.im ≠ 0) :
    xiWeilPolarization (xiThetaEigenFourier alpha) (xiThetaEigenFourier alpha) = 0 := by
  rw [xiWeilPolarization_thetaEigen halpha halpha, xiThetaEigenGram, if_neg]
  intro hcon
  exact him (Complex.conj_eq_iff_im.mp hcon.symm)

/-- **(22)** A real Xi zero gives the multiplicity-weighted squared derivative, unconditionally. -/
theorem xiWeilPolarization_thetaEigen_diagonal_of_im_eq_zero
    {alpha : ℂ} (halpha : XiC alpha = 0) (him : alpha.im = 0) :
    xiWeilPolarization (xiThetaEigenFourier alpha) (xiThetaEigenFourier alpha) =
      (((xiSpectralMultiplicity alpha : ℝ) * ‖deriv XiC alpha‖ ^ 2 : ℝ) : ℂ) := by
  have hconj : alpha = (starRingEnd ℂ) alpha := (Complex.conj_eq_iff_im.mpr him).symm
  rw [xiWeilPolarization_thetaEigen halpha halpha, xiThetaEigenGram, if_pos hconj.symm.symm]
  rw [mul_assoc, Complex.mul_conj']
  push_cast
  rw [norm_mul, Complex.norm_I, one_mul]

/-- The diagonal of the Hedenmalm--Weil form at a Xi zero is strictly positive exactly when the
zero is real and simple. -/
theorem xiWeilPolarization_thetaEigen_diagonal_re_pos_iff
    {alpha : ℂ} (halpha : XiC alpha = 0) :
    0 < (xiWeilPolarization (xiThetaEigenFourier alpha) (xiThetaEigenFourier alpha)).re ↔
      alpha.im = 0 ∧ deriv XiC alpha ≠ 0 := by
  constructor
  · intro hpos
    by_cases him : alpha.im = 0
    · refine ⟨him, ?_⟩
      intro hderiv
      rw [xiWeilPolarization_thetaEigen_diagonal_of_im_eq_zero halpha him, hderiv] at hpos
      simp at hpos
    · rw [xiWeilPolarization_thetaEigen_diagonal_eq_zero_of_im_ne_zero halpha him] at hpos
      simp at hpos
  · rintro ⟨him, hderiv⟩
    rw [xiWeilPolarization_thetaEigen_diagonal_of_im_eq_zero halpha him, Complex.ofReal_re]
    have hm : 0 < (xiSpectralMultiplicity alpha : ℝ) := by
      exact_mod_cast xiSpectralMultiplicity_pos_of_XiC_eq_zero halpha
    have hd : 0 < ‖deriv XiC alpha‖ ^ 2 := by positivity
    positivity


theorem XiWeilSquareSummable.finsetSum {ι : Type*} {A : Finset ι} {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ A, XiWeilSquareSummable (f i)) (c : ι → ℂ) :
    XiWeilSquareSummable (fun z => ∑ i ∈ A, c i * f i z) := by
  classical
  revert hf
  induction A using Finset.induction_on with
  | empty =>
      intro _
      simp only [Finset.sum_empty, XiWeilSquareSummable, norm_zero]
      simp
  | @insert a s ha ih =>
      intro hf
      have hs : ∀ i ∈ s, XiWeilSquareSummable (f i) :=
        fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have heq : (fun z => ∑ i ∈ insert a s, c i * f i z) =
          (fun z => c a * f a z) + (fun z => ∑ i ∈ s, c i * f i z) := by
        funext z
        simp [Finset.sum_insert ha]
      rw [heq]
      exact ((hf a (Finset.mem_insert_self a s)).const_smul (c a)).add (ih hs)

theorem xiWeilPolarization_finsetSum_left {ι : Type*} {A : Finset ι} {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ A, XiWeilSquareSummable (f i)) (c : ι → ℂ) {G : ℂ → ℂ}
    (hG : XiWeilSquareSummable G) :
    xiWeilPolarization (fun z => ∑ i ∈ A, c i * f i z) G =
      ∑ i ∈ A, c i * xiWeilPolarization (f i) G := by
  classical
  revert hf
  induction A using Finset.induction_on with
  | empty =>
      intro _
      simp only [Finset.sum_empty, xiWeilPolarization, zero_mul, tsum_zero]
  | @insert a s ha ih =>
      intro hf
      have hs : ∀ i ∈ s, XiWeilSquareSummable (f i) :=
        fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have heq : (fun z => ∑ i ∈ insert a s, c i * f i z) =
          (fun z => c a * f a z) + (fun z => ∑ i ∈ s, c i * f i z) := by
        funext z
        simp [Finset.sum_insert ha]
      rw [heq, xiWeilPolarization_add_left
        ((hf a (Finset.mem_insert_self a s)).const_smul (c a))
        (XiWeilSquareSummable.finsetSum hs c) hG,
        xiWeilPolarization_const_smul_left, ih hs, Finset.sum_insert ha]

theorem xiWeilPolarization_finsetSum_right {ι : Type*} {A : Finset ι} {g : ι → ℂ → ℂ}
    (hg : ∀ i ∈ A, XiWeilSquareSummable (g i)) (d : ι → ℂ) {F : ℂ → ℂ}
    (hF : XiWeilSquareSummable F) :
    xiWeilPolarization F (fun z => ∑ i ∈ A, d i * g i z) =
      ∑ i ∈ A, (starRingEnd ℂ) (d i) * xiWeilPolarization F (g i) := by
  classical
  revert hg
  induction A using Finset.induction_on with
  | empty =>
      intro _
      simp only [Finset.sum_empty, xiWeilPolarization, xiWeilSharp, map_zero, mul_zero, tsum_zero]
  | @insert a s ha ih =>
      intro hg
      have hs : ∀ i ∈ s, XiWeilSquareSummable (g i) :=
        fun i hi => hg i (Finset.mem_insert_of_mem hi)
      have heq : (fun z => ∑ i ∈ insert a s, d i * g i z) =
          (fun z => d a * g a z) + (fun z => ∑ i ∈ s, d i * g i z) := by
        funext z
        simp [Finset.sum_insert ha]
      rw [heq, xiWeilPolarization_add_right hF
        ((hg a (Finset.mem_insert_self a s)).const_smul (d a))
        (XiWeilSquareSummable.finsetSum hs d),
        xiWeilPolarization_const_smul_right, ih hs, Finset.sum_insert ha]

/-- **The Hedenmalm--Weil Gram form of a finite eigenfunction combination.**  Unconditionally, the
form is the double sum of the conjugation-carried Gram entries. -/
theorem xiWeilPolarization_thetaEigen_finsetSum {A : Finset ℂ}
    (hA : ∀ α ∈ A, XiC α = 0) (c d : ℂ → ℂ) :
    xiWeilPolarization (fun z => ∑ α ∈ A, c α * xiThetaEigenFourier α z)
        (fun z => ∑ β ∈ A, d β * xiThetaEigenFourier β z) =
      ∑ α ∈ A, ∑ β ∈ A, c α * (starRingEnd ℂ) (d β) * xiThetaEigenGram α β := by
  have hsum : ∀ α ∈ A, XiWeilSquareSummable (xiThetaEigenFourier α) :=
    fun α hα => xiThetaEigenFourier_squareSummable (hA α hα)
  rw [xiWeilPolarization_finsetSum_left hsum c (XiWeilSquareSummable.finsetSum hsum d)]
  refine Finset.sum_congr rfl (fun α hα => ?_)
  rw [xiWeilPolarization_finsetSum_right hsum d (hsum α hα), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun β hβ => ?_)
  rw [xiWeilPolarization_thetaEigen (hA α hα) (hA β hβ)]
  ring


theorem xiThetaEigenGram_of_im_eq_zero {alpha beta : ℂ} (him : alpha.im = 0) :
    xiThetaEigenGram alpha beta =
      if beta = alpha then
        (((xiSpectralMultiplicity alpha : ℝ) * ‖deriv XiC alpha‖ ^ 2 : ℝ) : ℂ) else 0 := by
  have hconj : (starRingEnd ℂ) alpha = alpha := Complex.conj_eq_iff_im.mpr him
  rw [xiThetaEigenGram, hconj]
  split_ifs with h
  · subst h
    rw [mul_assoc, Complex.mul_conj']
    push_cast
    rw [norm_mul, Complex.norm_I, one_mul]
  · rfl

/-- On real zeros the Gram form is diagonal, so a finite eigenfunction combination has the
multiplicity-weighted diagonal energy. -/
theorem xiWeilPolarization_thetaEigen_finsetSum_of_forall_im_eq_zero
    {A : Finset ℂ} (hA : ∀ α ∈ A, XiC α = 0) (him : ∀ α ∈ A, α.im = 0) (c : ℂ → ℂ) :
    xiWeilPolarization (fun z => ∑ α ∈ A, c α * xiThetaEigenFourier α z)
        (fun z => ∑ β ∈ A, c β * xiThetaEigenFourier β z) =
      ((∑ α ∈ A, ‖c α‖ ^ 2 * ((xiSpectralMultiplicity α : ℝ) * ‖deriv XiC α‖ ^ 2) : ℝ) : ℂ) := by
  rw [xiWeilPolarization_thetaEigen_finsetSum hA c c]
  push_cast
  refine Finset.sum_congr rfl (fun α hα => ?_)
  rw [Finset.sum_eq_single α]
  · rw [xiThetaEigenGram_of_im_eq_zero (him α hα), if_pos rfl, Complex.mul_conj']
    push_cast
    ring
  · intro β _ hne
    rw [xiThetaEigenGram_of_im_eq_zero (him α hα), if_neg hne, mul_zero]
  · intro hnot
    exact absurd hα hnot

/-- **Positive definiteness on the eigen-span, under real simple zeros.** -/
theorem xiWeilPolarization_thetaEigen_finsetSum_re_pos
    {A : Finset ℂ} (hA : ∀ α ∈ A, XiC α = 0) (him : ∀ α ∈ A, α.im = 0)
    (hsimple : ∀ α ∈ A, deriv XiC α ≠ 0) (c : ℂ → ℂ) (hc : ∃ α ∈ A, c α ≠ 0) :
    0 < (xiWeilPolarization (fun z => ∑ α ∈ A, c α * xiThetaEigenFourier α z)
          (fun z => ∑ β ∈ A, c β * xiThetaEigenFourier β z)).re := by
  rw [xiWeilPolarization_thetaEigen_finsetSum_of_forall_im_eq_zero hA him c, Complex.ofReal_re]
  obtain ⟨α₀, hα₀, hc₀⟩ := hc
  refine Finset.sum_pos' (fun α _ => by positivity) ⟨α₀, hα₀, ?_⟩
  have h1 : 0 < ‖c α₀‖ := norm_pos_iff.mpr hc₀
  have h2 : 0 < (xiSpectralMultiplicity α₀ : ℝ) := by
    exact_mod_cast xiSpectralMultiplicity_pos_of_XiC_eq_zero (hA α₀ hα₀)
  have h3 : 0 < ‖deriv XiC α₀‖ := norm_pos_iff.mpr (hsimple α₀ hα₀)
  positivity

/-- **(23)/(24) unconditionally.**  The Hedenmalm--Weil form is positive definite on every finite
span of theta eigenfunction quotients if and only if the Riemann hypothesis holds and every zero of
the completed zeta function is simple.  One direction is the diagonal criterion applied to a single
eigenfunction; the other is diagonality of the Gram matrix on real zeros. -/
theorem forall_finsetSum_thetaEigen_re_pos_iff :
    (∀ (A : Finset ℂ) (c : ℂ → ℂ), (∀ α ∈ A, XiC α = 0) → (∃ α ∈ A, c α ≠ 0) →
        0 < (xiWeilPolarization (fun z => ∑ α ∈ A, c α * xiThetaEigenFourier α z)
              (fun z => ∑ β ∈ A, c β * xiThetaEigenFourier β z)).re) ↔
      RiemannHypothesis ∧ ∀ α : ℂ, XiC α = 0 → deriv XiC α ≠ 0 := by
  constructor
  · intro hpos
    have hall : ∀ α : ℂ, XiC α = 0 → α.im = 0 ∧ deriv XiC α ≠ 0 := by
      intro α hα
      have hmem : ∀ β ∈ ({α} : Finset ℂ), XiC β = 0 := by
        intro β hβ
        rw [Finset.mem_singleton] at hβ
        exact hβ ▸ hα
      have h := hpos {α} (fun _ => 1) hmem ⟨α, Finset.mem_singleton_self α, one_ne_zero⟩
      have hfun : (fun z => ∑ β ∈ ({α} : Finset ℂ), (1 : ℂ) * xiThetaEigenFourier β z) =
          xiThetaEigenFourier α := by
        funext z
        simp
      rw [hfun] at h
      exact (xiWeilPolarization_thetaEigen_diagonal_re_pos_iff hα).mp h
    exact ⟨SlabMassSquareCertificate.riemannHypothesis_iff_xiC_zero_im_eq_zero.mpr (fun z hz => (hall z hz).1),
      fun α hα => (hall α hα).2⟩
  · rintro ⟨hRH, hsimple⟩ A c hA hc
    exact xiWeilPolarization_thetaEigen_finsetSum_re_pos hA
      (fun α hα => SlabMassSquareCertificate.riemannHypothesis_iff_xiC_zero_im_eq_zero.mp hRH α (hA α hα))
      (fun α hα => hsimple α (hA α hα)) c hc

end

end RHTower
