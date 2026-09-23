import GaloisForLFunctions.RHTower.SuzukiScrewFormExcessLowerBound
import GaloisForLFunctions.RHTower.DeningerDivisorSchwarzMonodromy
import GaloisForLFunctions.RHTower.ReciprocalAtomTestSpaceClosure
import GaloisForLFunctions.RHTower.ScrewCurvatureSumOfSquares

/-!
# The screw form is sampling energy minus a conjugation defect

Every Xi zero copy `q` has a **partner** `q* = reflect (conj q)` whose spectral point is `z̄_q`, and
the reflected ray coefficient is the conjugate of the partner's ray coefficient:
`c̄_q = conj (c_{q*})`.  Writing `w_q = 1/z_q²`, the screw form is `Σ'_q conj(c_{q*}) c_q w_q`, and the
pointwise polarisation identity

`Re(w A conj B) = ½ Re w (|A|² + |B|² − |A − B|²) − Im w · Im(A conj B)`

gives the exact law

`Re Q(φ) = Σ'_q Re(w_q) |c_q|² − ½ Σ'_q Re(w_q) |c_q − c_{q*}|² − Σ'_q Im(w_q) Im(c_q conj c_{q*})`.

On-line copies are their own partners, so the two defect sums vanish there; under RH every copy is
on the line and the form is the sampling energy `Σ'_q |c_q|²/z_q² ≥ 0`.  All Weil negativity is
therefore carried by the conjugation defect `c_q − c_{q*} = ∫ (e^{−iz_q u} − e^{−iz̄_q u}) φ(u) du`
of the off-line copies, together with the small phase term weighted by `Im(1/z_q²)`.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- The partner copy `reflect (conj q)`, whose spectral point is `z̄_q`. -/
def xiZeroCopyPartner : XiZeroCopy ≃ XiZeroCopy :=
  xiZeroCopyConjEquiv.trans xiZeroCopyReflectEquiv

theorem xiZeroCopyPartner_apply (q : XiZeroCopy) :
    xiZeroCopyPartner q = xiZeroCopyReflectEquiv (xiZeroCopyConjEquiv q) := rfl

theorem xiSpectralPoint_partner (q : XiZeroCopy) :
    xiSpectralPoint (xiZeroCopyPartner q) = (starRingEnd ℂ) (xiSpectralPoint q) := by
  rw [xiZeroCopyPartner_apply, xiSpectralPoint_reflect, xiSpectralPoint_conjEquiv, neg_neg]

/-- The partner map is an involution. -/
theorem xiZeroCopyPartner_partner (q : XiZeroCopy) :
    xiZeroCopyPartner (xiZeroCopyPartner q) = q := by
  have hfst : (xiZeroCopyPartner (xiZeroCopyPartner q)).1 = q.1 := by
    apply Subtype.ext
    change (1 : ℂ) - (starRingEnd ℂ) ((1 : ℂ) - (starRingEnd ℂ) (q.1 : ℂ)) = (q.1 : ℂ)
    rw [map_sub, map_one, Complex.conj_conj]
    ring
  apply Sigma.ext hfst
  apply (Fin.heq_ext_iff (congrArg (fun rho : XiDivisorSupport =>
    Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ))) hfst)).2
  simp [xiZeroCopyPartner, xiZeroCopyReflectEquiv, xiZeroCopyConjEquiv, xiZeroReflectEquiv,
    xiZeroConjEquiv, Equiv.sigmaCongr, Equiv.sigmaCongrRight, Equiv.sigmaCongrLeft]
  exact Fin.val_eq_val_of_heq (cast_heq _ q.2)

/-- On-line copies are their own partners. -/
theorem xiZeroCopyPartner_eq_self_of_im_eq_zero (q : XiZeroCopy)
    (h : (xiSpectralPoint q).im = 0) : xiZeroCopyPartner q = q := by
  have hre : ((xiZeroCopyConjEquiv q).1 : ℂ).re = 1 / 2 := by
    change ((starRingEnd ℂ) (q.1 : ℂ)).re = 1 / 2
    rw [Complex.conj_re]
    have him : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by
      simp [xiSpectralPoint, Complex.mul_im]
    linarith
  rw [xiZeroCopyPartner_apply,
    xiZeroCopyReflectEquiv_eq_conjEquiv_of_re_eq_half (xiZeroCopyConjEquiv q) hre,
    xiZeroCopyConjEquiv_apply_apply]

/-- The reflected ray coefficient is the conjugate of the partner's ray coefficient. -/
theorem suzukiTestRayCoefBar_eq_conj_partner {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a)
    (q : XiZeroCopy) :
    suzukiTestRayCoefBar φ q = (starRingEnd ℂ) (suzukiTestRayCoef φ (xiZeroCopyPartner q)) := by
  unfold suzukiTestRayCoef suzukiTestRayCoefBar
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show (Complex.exp (I * xiSpectralPoint q * (u : ℂ)) - 1) * (starRingEnd ℂ) ((φ : ℝ → ℂ) u) =
    (starRingEnd ℂ) ((Complex.exp (-(I * xiSpectralPoint (xiZeroCopyPartner q) * (u : ℂ))) - 1)
      * (φ : ℝ → ℂ) u)
  rw [map_mul, map_sub, map_one, ← Complex.exp_conj, xiSpectralPoint_partner]
  congr 3
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
  ring

/-- Pointwise polarisation: `Re(w A conj B) = ½ Re w (|A|² + |B|² − |A−B|²) − Im w · Im(A conj B)`. -/
theorem re_mul_mul_conj_eq (w A B : ℂ) :
    ((starRingEnd ℂ) B * A * w).re =
      1 / 2 * w.re * (‖A‖ ^ (2 : ℕ) + ‖B‖ ^ (2 : ℕ) - ‖A - B‖ ^ (2 : ℕ)) - w.im * (A * (starRingEnd ℂ) B).im := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im]
  ring

/-- The ray term of the screw form at a copy. -/
def screwRayTerm {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (q : XiZeroCopy) : ℂ :=
  suzukiTestRayCoefBar φ q * suzukiTestRayCoef φ q / xiSpectralPoint q ^ (2 : ℕ)

theorem screwRayTerm_eq {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (q : XiZeroCopy) :
    screwRayTerm φ q = (starRingEnd ℂ) (suzukiTestRayCoef φ (xiZeroCopyPartner q)) *
      suzukiTestRayCoef φ q * (1 / xiSpectralPoint q ^ (2 : ℕ)) := by
  unfold screwRayTerm
  rw [suzukiTestRayCoefBar_eq_conj_partner]
  ring

/-- The `L¹`-type bound on ray coefficients with the universal excess `1/2`. -/
theorem norm_suzukiTestRayCoef_le_half {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (q : XiZeroCopy) :
    ‖suzukiTestRayCoef φ q‖ ≤ (Real.exp (|a| / 2) + 1) * ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖ := by
  have := norm_suzukiTestRayCoef_le_of_im_le (Θ := 1 / 2)
    (fun q => (abs_xiSpectralPoint_im_lt_half q).le) φ q
  rwa [show (1 / 2 : ℝ) * |a| = |a| / 2 by ring] at this

/-- Summability of a real sequence dominated by a multiple of `‖z_q‖⁻²`. -/
theorem summable_of_le_inv_sq {f : XiZeroCopy → ℝ} {M : ℝ}
    (hf : ∀ q, |f q| ≤ M * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) : Summable f :=
  Summable.of_norm_bounded (xiSpectralPoint_inv_sq_summable.mul_left M) fun q => by
    rw [Real.norm_eq_abs]; exact hf q

/-- **The screw form as sampling energy minus conjugation defect.**  With `w_q = 1/z_q²`,
`c_q` the ray coefficients and `c_{q*}` those of the partner copies,
`Re Q(φ) = Σ'_q Re w_q |c_q|² − ½ Σ'_q Re w_q |c_q − c_{q*}|² − Σ'_q Im w_q · Im(c_q conj c_{q*})`. -/
theorem re_suzukiScrewSmoothForm_eq_sampling_sub_defect {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) :
    (suzukiScrewSmoothForm φ φ).re =
      (∑' q : XiZeroCopy, (1 / xiSpectralPoint q ^ (2 : ℕ)).re * ‖suzukiTestRayCoef φ q‖ ^ (2 : ℕ))
        - 1 / 2 * ∑' q : XiZeroCopy, (1 / xiSpectralPoint q ^ (2 : ℕ)).re *
            ‖suzukiTestRayCoef φ q - suzukiTestRayCoef φ (xiZeroCopyPartner q)‖ ^ (2 : ℕ)
        - ∑' q : XiZeroCopy, (1 / xiSpectralPoint q ^ (2 : ℕ)).im *
            (suzukiTestRayCoef φ q *
              (starRingEnd ℂ) (suzukiTestRayCoef φ (xiZeroCopyPartner q))).im := by
  rw [suzukiScrewSmoothForm_eq_tsum]
  set M : ℝ := (Real.exp (|a| / 2) + 1) * ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖ with hM
  have hM0 : 0 ≤ M := by
    have : 0 ≤ ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖ := integral_nonneg fun u => norm_nonneg _
    positivity
  have hc : ∀ q, ‖suzukiTestRayCoef φ q‖ ≤ M := fun q => norm_suzukiTestRayCoef_le_half φ q
  have hw : ∀ q, ‖(1 / xiSpectralPoint q ^ (2 : ℕ) : ℂ)‖ = 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
    intro q
    rw [norm_div, norm_one, norm_pow]
  set A : XiZeroCopy → ℂ := fun q => suzukiTestRayCoef φ q with hA
  set B : XiZeroCopy → ℂ := fun q => suzukiTestRayCoef φ (xiZeroCopyPartner q) with hB
  set w : XiZeroCopy → ℂ := fun q => 1 / xiSpectralPoint q ^ (2 : ℕ) with hwdef
  -- the three real pieces
  set f₁ : XiZeroCopy → ℝ := fun q => (w q).re * ‖A q‖ ^ (2 : ℕ) with hf₁
  set f₂ : XiZeroCopy → ℝ := fun q => (w q).re * ‖B q‖ ^ (2 : ℕ) with hf₂
  set f₃ : XiZeroCopy → ℝ := fun q => (w q).re * ‖A q - B q‖ ^ (2 : ℕ) with hf₃
  set f₄ : XiZeroCopy → ℝ := fun q => (w q).im * (A q * (starRingEnd ℂ) (B q)).im with hf₄
  have hwre : ∀ q, |(w q).re| ≤ 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := fun q =>
    (Complex.abs_re_le_norm _).trans (le_of_eq (hw q))
  have hwim : ∀ q, |(w q).im| ≤ 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := fun q =>
    (Complex.abs_im_le_norm _).trans (le_of_eq (hw q))
  have hAle : ∀ q, ‖A q‖ ≤ M := fun q => hc q
  have hBle : ∀ q, ‖B q‖ ≤ M := fun q => hc _
  have hs₁ : Summable f₁ := summable_of_le_inv_sq (M := M ^ (2 : ℕ)) fun q => by
    simp only [hf₁]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖A q‖ ^ (2 : ℕ))]
    calc |(w q).re| * ‖A q‖ ^ (2 : ℕ) ≤ (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) * M ^ (2 : ℕ) :=
          mul_le_mul (hwre q) (pow_le_pow_left₀ (norm_nonneg _) (hAle q) 2) (by positivity)
            (by positivity)
      _ = M ^ (2 : ℕ) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by ring
  have hs₂ : Summable f₂ := summable_of_le_inv_sq (M := M ^ (2 : ℕ)) fun q => by
    simp only [hf₂]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖B q‖ ^ (2 : ℕ))]
    calc |(w q).re| * ‖B q‖ ^ (2 : ℕ) ≤ (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) * M ^ (2 : ℕ) :=
          mul_le_mul (hwre q) (pow_le_pow_left₀ (norm_nonneg _) (hBle q) 2) (by positivity)
            (by positivity)
      _ = M ^ (2 : ℕ) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by ring
  have hs₃ : Summable f₃ := summable_of_le_inv_sq (M := (2 * M) ^ (2 : ℕ)) fun q => by
    simp only [hf₃]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖A q - B q‖ ^ (2 : ℕ))]
    have hAB : ‖A q - B q‖ ≤ 2 * M := by
      calc ‖A q - B q‖ ≤ ‖A q‖ + ‖B q‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (hAle q) (hBle q)
        _ = 2 * M := by ring
    calc |(w q).re| * ‖A q - B q‖ ^ (2 : ℕ) ≤ (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) * (2 * M) ^ (2 : ℕ) :=
          mul_le_mul (hwre q) (pow_le_pow_left₀ (norm_nonneg _) hAB 2) (by positivity)
            (by positivity)
      _ = (2 * M) ^ (2 : ℕ) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by ring
  have hs₄ : Summable f₄ := summable_of_le_inv_sq (M := M ^ (2 : ℕ)) fun q => by
    simp only [hf₄]
    rw [abs_mul]
    have him : |(A q * (starRingEnd ℂ) (B q)).im| ≤ M ^ (2 : ℕ) := by
      calc |(A q * (starRingEnd ℂ) (B q)).im| ≤ ‖A q * (starRingEnd ℂ) (B q)‖ :=
            Complex.abs_im_le_norm _
        _ = ‖A q‖ * ‖B q‖ := by rw [norm_mul, Complex.norm_conj]
        _ ≤ M * M := mul_le_mul (hAle q) (hBle q) (norm_nonneg _) hM0
        _ = M ^ (2 : ℕ) := by ring
    calc |(w q).im| * |(A q * (starRingEnd ℂ) (B q)).im|
        ≤ (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) * M ^ (2 : ℕ) :=
          mul_le_mul (hwim q) him (abs_nonneg _) (by positivity)
      _ = M ^ (2 : ℕ) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by ring
  -- the complex terms are summable, and their real parts split
  have hterm : ∀ q, screwRayTerm φ q = (starRingEnd ℂ) (B q) * A q * w q := fun q =>
    screwRayTerm_eq φ q
  have hre : ∀ q, (screwRayTerm φ q).re =
      1 / 2 * (f₁ q + f₂ q) - 1 / 2 * f₃ q - f₄ q := by
    intro q
    rw [hterm, re_mul_mul_conj_eq]
    simp only [hf₁, hf₂, hf₃, hf₄]
    ring
  have hsum : Summable (screwRayTerm φ) := by
    refine Summable.of_norm_bounded (xiSpectralPoint_inv_sq_summable.mul_left (M ^ (2 : ℕ))) fun q => ?_
    rw [hterm, norm_mul, norm_mul, Complex.norm_conj, hw]
    calc ‖B q‖ * ‖A q‖ * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))
        ≤ M * M * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul (hBle q) (hAle q) (norm_nonneg _) hM0)
            (by positivity)
      _ = M ^ (2 : ℕ) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by ring
  have hQ : (∑' q, suzukiTestRayCoefBar φ q * suzukiTestRayCoef φ q / xiSpectralPoint q ^ (2 : ℕ)) =
      ∑' q, screwRayTerm φ q := rfl
  rw [hQ, Complex.re_tsum hsum, tsum_congr hre]
  rw [Summable.tsum_sub (by
        exact ((hs₁.add hs₂).mul_left _).sub (hs₃.mul_left _)) hs₄,
    Summable.tsum_sub ((hs₁.add hs₂).mul_left _) (hs₃.mul_left _),
    Summable.tsum_mul_left _ (hs₁.add hs₂), Summable.tsum_mul_left _ hs₃, hs₁.tsum_add hs₂]
  -- symmetrise the partner energy
  have hsym : (∑' q, f₂ q) = ∑' q, f₁ q := by
    have h1 : (∑' q, f₂ q) = ∑' q, f₂ (xiZeroCopyPartner q) :=
      (Equiv.tsum_eq xiZeroCopyPartner f₂).symm
    rw [h1]
    refine tsum_congr fun q => ?_
    simp only [hf₂, hf₁, hB, hA, hwdef]
    rw [xiZeroCopyPartner_partner, xiSpectralPoint_partner]
    have hconj : (1 / (starRingEnd ℂ) (xiSpectralPoint q) ^ (2 : ℕ) : ℂ) =
        (starRingEnd ℂ) (1 / xiSpectralPoint q ^ (2 : ℕ)) := by
      rw [map_div₀, map_one, map_pow]
    rw [hconj, Complex.conj_re]
  rw [hsym]
  simp only [hf₁, hf₃, hf₄, hA, hB, hwdef]
  ring

/-- **Under RH the form is the sampling energy.**  Every copy is its own partner, both defect
sums vanish, and `Re Q(φ) = Σ'_q |c_q|²/z_q² ≥ 0`. -/
theorem re_suzukiScrewSmoothForm_eq_sampling_of_riemannHypothesis (hRH : RiemannHypothesis)
    {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) :
    (suzukiScrewSmoothForm φ φ).re =
      ∑' q : XiZeroCopy, (1 / xiSpectralPoint q ^ (2 : ℕ)).re * ‖suzukiTestRayCoef φ q‖ ^ (2 : ℕ) := by
  rw [re_suzukiScrewSmoothForm_eq_sampling_sub_defect]
  have hself : ∀ q : XiZeroCopy, xiZeroCopyPartner q = q := fun q =>
    xiZeroCopyPartner_eq_self_of_im_eq_zero q (xiSpectralPoint_im_eq_zero_of_riemannHypothesis hRH q)
  have h3 : (∑' q : XiZeroCopy, (1 / xiSpectralPoint q ^ (2 : ℕ)).re *
      ‖suzukiTestRayCoef φ q - suzukiTestRayCoef φ (xiZeroCopyPartner q)‖ ^ (2 : ℕ)) = 0 := by
    calc _ = ∑' _q : XiZeroCopy, (0 : ℝ) := tsum_congr fun q => by
            rw [hself q, sub_self, norm_zero]; ring
      _ = 0 := tsum_zero
  have h4 : (∑' q : XiZeroCopy, (1 / xiSpectralPoint q ^ (2 : ℕ)).im *
      (suzukiTestRayCoef φ q * (starRingEnd ℂ) (suzukiTestRayCoef φ (xiZeroCopyPartner q))).im) = 0 := by
    refine (tsum_congr fun q => ?_).trans (tsum_zero (α := ℝ) (β := XiZeroCopy))
    have him : (1 / xiSpectralPoint q ^ (2 : ℕ) : ℂ).im = 0 := by
      obtain ⟨t, ht⟩ : ∃ t : ℝ, xiSpectralPoint q = (t : ℂ) :=
        ⟨(xiSpectralPoint q).re, by
          apply Complex.ext
          · simp
          · simp [xiSpectralPoint_im_eq_zero_of_riemannHypothesis hRH q]⟩
      rw [ht]
      have hcast : (1 / (t : ℂ) ^ (2 : ℕ)) = ((1 / t ^ (2 : ℕ) : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.ofReal_im]
    rw [him, zero_mul]
  rw [h3, h4]
  ring

end

end RHTower
