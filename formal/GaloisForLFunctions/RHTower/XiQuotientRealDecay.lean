import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspComplexStrip
import GaloisForLFunctions.RHTower.XiHorizontalStripDecay
import GaloisForLFunctions.RHTower.Deninger.DeningerDivisorSchwarzMonodromy
import GaloisForLFunctions.RHTower.XiWeilLineConjHilbert
import GaloisForLFunctions.RHTower.XiWeilResolventSource
import GaloisForLFunctions.RHTower.XiHedenmalmFourierEquation

/-!
# Exponential decay of the Hedenmalm removable quotient on the real axis

The centered xi function decays exponentially along the real axis, and at a Xi zero the Hedenmalm
removable quotient is that function divided by a linear factor.  Away from the removed point the
factor is bounded below, so the quotient inherits the decay; near it the quotient is continuous on a
compact set.  This is the admissibility bound that places the eigenfunction quotients in the
Guinand--Weil test class.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- **The Hedenmalm removable quotient decays exponentially on the real axis.**  Away from the
removed point it is `XiC` divided by a factor bounded below; near it the quotient is continuous on a
compact set.  This is the admissibility bound behind the Guinand--Weil test class. -/
theorem exists_norm_xiThetaEigenFourier_ofReal_le {alpha : ℂ} (halpha : XiC alpha = 0)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖xiThetaEigenFourier alpha ((t : ℝ) : ℂ)‖ ≤ C * Real.exp (-(δ * |t|)) := by
  obtain ⟨C₀, hC₀, hXi⟩ := exists_norm_XiC_ofReal_le hδ0 hδ4
  set R : ℝ := ‖alpha‖ + 1 with hR
  have hR1 : 1 ≤ R := by
    rw [hR]
    linarith [norm_nonneg alpha]
  -- bound on the compact core
  have hcont : Continuous (fun t : ℝ => ‖xiThetaEigenFourier alpha ((t : ℝ) : ℂ)‖) :=
    ((continuous_xiThetaEigenFourier alpha).comp Complex.continuous_ofReal).norm
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C₀ (M * Real.exp (δ * R)), le_max_of_le_left hC₀, fun t => ?_⟩
  rcases le_or_gt |t| R with hsmall | hbig
  · -- compact core
    have hmem : t ∈ Set.Icc (-R) R := by
      rw [Set.mem_Icc]
      constructor <;> [linarith [neg_abs_le t]; linarith [le_abs_self t]]
    have hle : ‖xiThetaEigenFourier alpha ((t : ℝ) : ℂ)‖ ≤ M := by
      simpa using hM t hmem
    have hMnn : 0 ≤ M := le_trans (norm_nonneg _) hle
    have hexp : Real.exp (-(δ * R)) ≤ Real.exp (-(δ * |t|)) := by
      refine Real.exp_le_exp.mpr ?_
      have : δ * |t| ≤ δ * R := mul_le_mul_of_nonneg_left hsmall hδ0
      linarith
    calc ‖xiThetaEigenFourier alpha ((t : ℝ) : ℂ)‖ ≤ M := hle
      _ = M * Real.exp (δ * R) * Real.exp (-(δ * R)) := by
          rw [mul_assoc, ← Real.exp_add]
          simp
      _ ≤ M * Real.exp (δ * R) * Real.exp (-(δ * |t|)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ max C₀ (M * Real.exp (δ * R)) * Real.exp (-(δ * |t|)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)
  · -- far field
    have hne : ((t : ℝ) : ℂ) ≠ alpha := by
      intro hc
      have : ‖((t : ℝ) : ℂ)‖ = ‖alpha‖ := by rw [hc]
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      rw [hR] at hbig
      linarith
    have hden : (1 : ℝ) ≤ ‖alpha - ((t : ℝ) : ℂ)‖ := by
      have h1 : ‖((t : ℝ) : ℂ)‖ - ‖alpha‖ ≤ ‖alpha - ((t : ℝ) : ℂ)‖ := by
        rw [norm_sub_rev]
        exact norm_sub_norm_le _ _
      rw [Complex.norm_real, Real.norm_eq_abs] at h1
      rw [hR] at hbig
      linarith
    rw [xiThetaEigenFourier_eq_div halpha hne, norm_div, norm_mul, norm_neg, Complex.norm_I,
      one_mul]
    have hdiv : ‖XiC ((t : ℝ) : ℂ)‖ / ‖alpha - ((t : ℝ) : ℂ)‖ ≤ ‖XiC ((t : ℝ) : ℂ)‖ := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg (XiC ((t : ℝ) : ℂ))]
    calc ‖XiC ((t : ℝ) : ℂ)‖ / ‖alpha - ((t : ℝ) : ℂ)‖ ≤ ‖XiC ((t : ℝ) : ℂ)‖ := hdiv
      _ ≤ C₀ * Real.exp (-(δ * |t|)) := hXi t
      _ ≤ max C₀ (M * Real.exp (δ * R)) * Real.exp (-(δ * |t|)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)


theorem isCompact_reIm_box (R A : ℝ) :
    IsCompact {z : ℂ | |z.re| ≤ R ∧ |z.im| ≤ A} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have h1 : IsClosed {z : ℂ | |z.re| ≤ R} :=
      isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const
    have h2 : IsClosed {z : ℂ | |z.im| ≤ A} :=
      isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const
    exact h1.inter h2
  · refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R + A)) ?_
    intro z hz
    obtain ⟨h1, h2⟩ := hz
    rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ R + A := by linarith

/-- **The Hedenmalm removable quotient decays exponentially on every horizontal substrip.**  This
is the exponential half of the Guinand--Weil admissibility bound `(18a)`. -/
theorem exists_norm_xiThetaEigenFourier_horizontal_le {alpha : ℂ} (halpha : XiC alpha = 0)
    {A δ : ℝ} (hA0 : 0 ≤ A) (hA1 : A < 1) (hδ0 : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t a : ℝ, |a| ≤ A →
      ‖xiThetaEigenFourier alpha ((t : ℂ) + (a : ℂ) * Complex.I)‖ ≤
        C * Real.exp (-(δ * |t|)) := by
  obtain ⟨C₀, hC₀, hXi⟩ := exists_norm_XiC_horizontal_le hA1 hδ0 hδ4
  set R : ℝ := ‖alpha‖ + A + 1 with hR
  obtain ⟨M, hM⟩ := (isCompact_reIm_box R A).exists_bound_of_continuousOn
    ((continuous_xiThetaEigenFourier alpha).continuousOn)
  refine ⟨max C₀ (M * Real.exp (δ * R)), le_max_of_le_left hC₀, fun t a ha => ?_⟩
  set z : ℂ := (t : ℂ) + (a : ℂ) * Complex.I with hz
  have hzre : z.re = t := by rw [hz]; simp
  have hzim : z.im = a := by rw [hz]; simp
  rcases le_or_gt |t| R with hsmall | hbig
  · have hmem : z ∈ {w : ℂ | |w.re| ≤ R ∧ |w.im| ≤ A} := by
      constructor
      · rw [hzre]; exact hsmall
      · rw [hzim]; exact ha
    have hle : ‖xiThetaEigenFourier alpha z‖ ≤ M := hM z hmem
    have hMnn : 0 ≤ M := le_trans (norm_nonneg _) hle
    have hexp : Real.exp (-(δ * R)) ≤ Real.exp (-(δ * |t|)) := by
      refine Real.exp_le_exp.mpr ?_
      have : δ * |t| ≤ δ * R := mul_le_mul_of_nonneg_left hsmall hδ0
      linarith
    calc ‖xiThetaEigenFourier alpha z‖ ≤ M := hle
      _ = M * Real.exp (δ * R) * Real.exp (-(δ * R)) := by
          rw [mul_assoc, ← Real.exp_add]
          simp
      _ ≤ M * Real.exp (δ * R) * Real.exp (-(δ * |t|)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ max C₀ (M * Real.exp (δ * R)) * Real.exp (-(δ * |t|)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)
  · have hznorm : R ≤ ‖z‖ := by
      have : |t| = |z.re| := by rw [hzre]
      calc R ≤ |t| := le_of_lt hbig
        _ = |z.re| := this
        _ ≤ ‖z‖ := Complex.abs_re_le_norm z
    have hne : z ≠ alpha := by
      intro hc
      rw [hc] at hznorm
      rw [hR] at hznorm
      linarith [hA0]
    have hden : (1 : ℝ) ≤ ‖alpha - z‖ := by
      have h1 : ‖z‖ - ‖alpha‖ ≤ ‖alpha - z‖ := by
        rw [norm_sub_rev]
        exact norm_sub_norm_le _ _
      rw [hR] at hznorm
      linarith
    rw [xiThetaEigenFourier_eq_div halpha hne, norm_div, norm_mul, norm_neg, Complex.norm_I,
      one_mul]
    have hdiv : ‖XiC z‖ / ‖alpha - z‖ ≤ ‖XiC z‖ := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg (XiC z)]
    calc ‖XiC z‖ / ‖alpha - z‖ ≤ ‖XiC z‖ := hdiv
      _ ≤ C₀ * Real.exp (-(δ * |t|)) := hXi t a ha
      _ ≤ max C₀ (M * Real.exp (δ * R)) * Real.exp (-(δ * |t|)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)


/-- **Absolute convergence of the Weil polarization from square-summability.**  Unconditional: the
arithmetic--geometric mean bound dominates each polarized term by half the sum of the two squared
divisor evaluations. -/
theorem xiWeilPairSummable_of_squareSummable {F G : ℂ → ℂ}
    (hF : XiWeilSquareSummable F) (hG : XiWeilSquareSummable (xiWeilSharp G)) :
    XiWeilPairSummable F G := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    ((hF.add hG).mul_left (1 / 2))
  rw [norm_mul]
  have hsq := sq_nonneg (‖F (xiSpectralPoint q)‖ - ‖xiWeilSharp G (xiSpectralPoint q)‖)
  nlinarith [hsq]


/-- The star involution on divisor copies: it realises complex conjugation of the centered
spectral points, unconditionally. -/
def xiZeroCopyStarEquiv : XiZeroCopy ≃ XiZeroCopy :=
  xiZeroCopyConjEquiv.trans xiZeroCopyReflectEquiv

theorem xiSpectralPoint_starEquiv (q : XiZeroCopy) :
    xiSpectralPoint (xiZeroCopyStarEquiv q) = (starRingEnd ℂ) (xiSpectralPoint q) := by
  rw [xiZeroCopyStarEquiv, Equiv.trans_apply, xiSpectralPoint_eq_support]
  rw [show (xiZeroCopyReflectEquiv (xiZeroCopyConjEquiv q)).1 =
      xiZeroReflectEquiv (xiZeroCopyConjEquiv q).1 from rfl]
  rw [xiSpectralPointSupport_reflect, ← xiSpectralPoint_eq_support, xiSpectralPoint_copyConj,
    neg_neg]

/-- **Square-summability is stable under the Weil sharp involution**, unconditionally: the Xi
divisor is conjugation stable because `xi` has real Taylor coefficients. -/
theorem XiWeilSquareSummable_sharp {G : ℂ → ℂ} (hG : XiWeilSquareSummable G) :
    XiWeilSquareSummable (xiWeilSharp G) := by
  rw [XiWeilSquareSummable] at hG ⊢
  have hre := (Equiv.summable_iff xiZeroCopyStarEquiv).mpr hG
  refine hre.congr fun q => ?_
  rw [xiWeilSharp]
  simp only [Function.comp_apply, RCLike.norm_conj]
  rw [← xiSpectralPoint_starEquiv q]

/-- **Absolute convergence of the Weil polarization, unconditionally from square-summability.** -/
theorem xiWeilPairSummable_of_squareSummable' {F G : ℂ → ℂ}
    (hF : XiWeilSquareSummable F) (hG : XiWeilSquareSummable G) :
    XiWeilPairSummable F G := by
  have hGs := XiWeilSquareSummable_sharp hG
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    ((hF.add hGs).mul_left (1 / 2))
  rw [norm_mul]
  nlinarith [sq_nonneg (‖F (xiSpectralPoint q)‖ - ‖xiWeilSharp G (xiSpectralPoint q)‖)]


theorem XiWeilSquareSummable.add {F G : ℂ → ℂ} (hF : XiWeilSquareSummable F)
    (hG : XiWeilSquareSummable G) : XiWeilSquareSummable (F + G) := by
  rw [XiWeilSquareSummable] at hF hG ⊢
  refine Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_)
    ((hF.add hG).mul_left 2)
  have htri : ‖(F + G) (xiSpectralPoint q)‖ ≤
      ‖F (xiSpectralPoint q)‖ + ‖G (xiSpectralPoint q)‖ := by
    simpa using norm_add_le (F (xiSpectralPoint q)) (G (xiSpectralPoint q))
  nlinarith [sq_nonneg (‖F (xiSpectralPoint q)‖ - ‖G (xiSpectralPoint q)‖),
    norm_nonneg ((F + G) (xiSpectralPoint q)), norm_nonneg (F (xiSpectralPoint q)),
    norm_nonneg (G (xiSpectralPoint q)), htri]

theorem XiWeilSquareSummable.const_smul {F : ℂ → ℂ} (hF : XiWeilSquareSummable F) (c : ℂ) :
    XiWeilSquareSummable (fun z => c * F z) := by
  rw [XiWeilSquareSummable] at hF ⊢
  refine (hF.mul_left (‖c‖ ^ (2 : ℕ))).congr fun q => ?_
  rw [norm_mul, mul_pow]

/-- **Additivity of the Weil polarization on the square-summable class**, unconditionally. -/
theorem xiWeilPolarization_add_left {F₁ F₂ G : ℂ → ℂ} (h₁ : XiWeilSquareSummable F₁)
    (h₂ : XiWeilSquareSummable F₂) (hG : XiWeilSquareSummable G) :
    xiWeilPolarization (F₁ + F₂) G =
      xiWeilPolarization F₁ G + xiWeilPolarization F₂ G := by
  rw [xiWeilPolarization, xiWeilPolarization, xiWeilPolarization,
    ← (xiWeilPairSummable_of_squareSummable' h₁ hG).tsum_add
      (xiWeilPairSummable_of_squareSummable' h₂ hG)]
  refine tsum_congr fun q => ?_
  simp only [Pi.add_apply]
  ring

/-- **Homogeneity of the Weil polarization in the left argument**, unconditionally. -/
theorem xiWeilPolarization_const_smul_left {F G : ℂ → ℂ} (c : ℂ) :
    xiWeilPolarization (fun z => c * F z) G = c * xiWeilPolarization F G := by
  rw [xiWeilPolarization, xiWeilPolarization, ← tsum_mul_left]
  refine tsum_congr fun q => ?_
  ring


theorem XiWeilSquareSummable.sub {F G : ℂ → ℂ} (hF : XiWeilSquareSummable F)
    (hG : XiWeilSquareSummable G) : XiWeilSquareSummable (fun z => F z - G z) := by
  have hneg : XiWeilSquareSummable (fun z => (-1 : ℂ) * G z) := hG.const_smul (-1)
  have hsum := hF.add hneg
  refine hsum.congr fun q => ?_
  simp only [Pi.add_apply]
  ring_nf

/-- **Subtractivity of the Weil polarization in the left argument.** -/
theorem xiWeilPolarization_sub_left {F₁ F₂ G : ℂ → ℂ} (h₁ : XiWeilSquareSummable F₁)
    (h₂ : XiWeilSquareSummable F₂) (hG : XiWeilSquareSummable G) :
    xiWeilPolarization (fun z => F₁ z - F₂ z) G =
      xiWeilPolarization F₁ G - xiWeilPolarization F₂ G := by
  have hneg : XiWeilSquareSummable (fun z => (-1 : ℂ) * F₂ z) := h₂.const_smul (-1)
  have hadd := xiWeilPolarization_add_left h₁ hneg hG
  rw [xiWeilPolarization_const_smul_left (-1)] at hadd
  have hfun : (F₁ + fun z => (-1 : ℂ) * F₂ z) = fun z => F₁ z - F₂ z := by
    funext z
    simp only [Pi.add_apply]
    ring
  rw [hfun] at hadd
  rw [hadd]
  ring

/-- **The Weil polarization is Lipschitz in the left argument for the divisor `ell^(2 : ℕ)` distance.**
This is what lets an identity proved on a subclass pass to its closure. -/
theorem norm_xiWeilPolarization_sub_left_le {F₁ F₂ G : ℂ → ℂ} (h₁ : XiWeilSquareSummable F₁)
    (h₂ : XiWeilSquareSummable F₂) (hG : XiWeilSquareSummable G) :
    ‖xiWeilPolarization F₁ G - xiWeilPolarization F₂ G‖ ≤
      ‖xiWeilEvaluationLp F₁ h₁ - xiWeilEvaluationLp F₂ h₂‖ * ‖xiWeilEvaluationLp G hG‖ := by
  have hsub := (h₁.sub h₂)
  rw [← xiWeilPolarization_sub_left h₁ h₂ hG]
  refine le_trans (norm_xiWeilPolarization_le _ _ hsub hG) ?_
  refine mul_le_mul_of_nonneg_right (le_of_eq ?_) (norm_nonneg _)
  congr 1


/-- **Additivity of the Weil polarization in the right argument**, from Hermitian symmetry. -/
theorem xiWeilPolarization_add_right {F G₁ G₂ : ℂ → ℂ} (hF : XiWeilSquareSummable F)
    (h₁ : XiWeilSquareSummable G₁) (h₂ : XiWeilSquareSummable G₂) :
    xiWeilPolarization F (G₁ + G₂) =
      xiWeilPolarization F G₁ + xiWeilPolarization F G₂ := by
  have hsym := xiWeilPolarization_conj_symm (G₁ + G₂) F
  have hadd := xiWeilPolarization_add_left h₁ h₂ hF
  have h1 := xiWeilPolarization_conj_symm G₁ F
  have h2 := xiWeilPolarization_conj_symm G₂ F
  rw [hadd] at hsym
  rw [hsym, map_add, ← h1, ← h2]

/-- **Conjugate homogeneity of the Weil polarization in the right argument.** -/
theorem xiWeilPolarization_const_smul_right (F G : ℂ → ℂ) (c : ℂ) :
    xiWeilPolarization F (fun z => c * G z) =
      (starRingEnd ℂ) c * xiWeilPolarization F G := by
  have hsym := xiWeilPolarization_conj_symm (fun z => c * G z) F
  rw [xiWeilPolarization_const_smul_left c] at hsym
  have hbase := xiWeilPolarization_conj_symm G F
  rw [hsym, map_mul, ← hbase]


theorem XiWeilSquareSummable_cauchyPacket {s : Finset ℂ} (c : ℂ → ℂ)
    (hreg : ∀ z ∈ s, XiC z ≠ 0) :
    XiWeilSquareSummable (xiWeilCauchyPacket s c) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hz : XiWeilSquareSummable (fun _ : ℂ => (0 : ℂ)) := by
        rw [XiWeilSquareSummable]
        simp
      refine hz.congr fun q => ?_
      simp [xiWeilCauchyPacket]
  | @insert a s ha ih =>
      have hreg' : ∀ z ∈ s, XiC z ≠ 0 := fun z hz => hreg z (Finset.mem_insert_of_mem hz)
      have hterm : XiWeilSquareSummable (fun x => c a * xiWeilCauchyTest a x) :=
        (XiWeilSquareSummable_cauchy a).const_smul (c a)
      have hrest := ih hreg'
      refine (hterm.add hrest).congr fun q => ?_
      simp only [Pi.add_apply, xiWeilCauchyPacket, Finset.sum_insert ha]

/-- **The evaluation vector of a finite Cauchy packet lies in the algebraic Cauchy span.**  This
bridges the function-level packets of the resolvent source with the vector-level Hilbert core. -/
theorem xiWeilEvaluationLp_cauchyPacket_mem {s : Finset ℂ} (c : ℂ → ℂ)
    (hreg : ∀ z ∈ s, XiC z ≠ 0) :
    xiWeilEvaluationLp (xiWeilCauchyPacket s c) (XiWeilSquareSummable_cauchyPacket c hreg) ∈
      xiWeilCauchyAlgebraicSubspace := by
  classical
  have hcomb : xiWeilEvaluationLp (xiWeilCauchyPacket s c)
      (XiWeilSquareSummable_cauchyPacket c hreg) =
      ∑ z ∈ s.attach, c (z : ℂ) • xiWeilCauchyLp ⟨(z : ℂ), hreg (z : ℂ) z.2⟩ := by
    apply lp.ext
    funext q
    rw [xiWeilEvaluationLp_apply]
    rw [lp.coeFn_sum]
    simp only [Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, xiWeilCauchyLp_apply,
      smul_eq_mul, xiWeilCauchyPacket]
    exact (Finset.sum_attach s (fun z => c z * xiWeilCauchyTest z (xiSpectralPoint q))).symm
  rw [hcomb]
  refine Submodule.sum_mem _ fun z _ => ?_
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _))


/-- **The prime-plus-Gamma packet values converge along every `ell^(2 : ℕ)`-convergent sequence of
Cauchy packets.**  The polarization is an inner product against a fixed vector, so it is continuous;
on packets it equals the prime-plus-Gamma double sum. -/
theorem tendsto_primeArchSource_packetSum_of_tendsto
    {sn : ℕ → Finset ℂ} {cn : ℕ → ℂ → ℂ} {t : Finset ℂ} {d : ℂ → ℂ}
    (hreg : ∀ n, ∀ z ∈ sn n, XiC z ≠ 0)
    (hzhalf : ∀ n, ∀ z ∈ sn n, 1 < (1 / 2 + z * I).re)
    (hwhalf : ∀ w ∈ t, 1 < (1 / 2 + (starRingEnd ℂ) w * I).re)
    (hsep : ∀ n, ∀ z ∈ sn n, ∀ w ∈ t, z ≠ (starRingEnd ℂ) w)
    (hd : XiWeilSquareSummable (xiWeilCauchyPacket t d))
    {v : lp (fun _ : XiZeroCopy => ℂ) 2}
    (hconv : Filter.Tendsto
      (fun n => xiWeilEvaluationLp (xiWeilCauchyPacket (sn n) (cn n))
        (XiWeilSquareSummable_cauchyPacket (cn n) (hreg n))) atTop (nhds v)) :
    Filter.Tendsto
      (fun n => ∑ z ∈ sn n, ∑ w ∈ t,
        cn n z * (starRingEnd ℂ) (d w) *
          ((primeArchSourceRelativeTrace ((starRingEnd ℂ) w) -
            primeArchSourceRelativeTrace z) / (z - (starRingEnd ℂ) w)))
      atTop (nhds (inner ℂ (xiWeilLineConjLp (xiWeilEvaluationLp (xiWeilCauchyPacket t d) hd)) v)) := by
  have hpol : ∀ n : ℕ,
      (∑ z ∈ sn n, ∑ w ∈ t,
        cn n z * (starRingEnd ℂ) (d w) *
          ((primeArchSourceRelativeTrace ((starRingEnd ℂ) w) -
            primeArchSourceRelativeTrace z) / (z - (starRingEnd ℂ) w))) =
      inner ℂ (xiWeilLineConjLp (xiWeilEvaluationLp (xiWeilCauchyPacket t d) hd))
        (xiWeilEvaluationLp (xiWeilCauchyPacket (sn n) (cn n))
          (XiWeilSquareSummable_cauchyPacket (cn n) (hreg n))) := by
    intro n
    rw [inner_xiWeilLineConjLp_evaluation_eq_polarization]
    exact (xiWeilPolarization_cauchyPacket_eq_primeArchSource (hzhalf n) hwhalf (hsep n)).symm
  simp only [hpol]
  exact (continuous_inner.continuousAt).tendsto.comp
    (Filter.Tendsto.prodMk_nhds tendsto_const_nhds hconv)

end RHTower
