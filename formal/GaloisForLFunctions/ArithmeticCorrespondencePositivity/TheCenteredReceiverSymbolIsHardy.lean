import GaloisForLFunctions.RHTower.TheDampedMoebiusMellinQuotientIsHardyRightOfTheZeroAbscissa

/-!
# The centered receiver symbol is Hardy beyond the translated zero abscissa

The pole-cleared symbol of the centered Möbius divisor prefix is
`ζ(s) (1/ζ(s+ε) − 1/ζ(1+ε)) / s`. A divided difference removes the pole at `s=1`.
Convexity and the reciprocal-zeta bound give a common square-integrable majorant
on every half-plane strictly right of both `1/2` and `Θ−ε`.
-/

open Complex Set Filter Topology MeasureTheory
open RHTower RHTower.Sieve GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- The centered Mellin symbol with its removable singularity at `1` filled in. -/
def centeredReceiverSymbol (ε : ℝ) (s : ℂ) : ℂ :=
  zetaResidueUnit s * dslope (fun z : ℂ => invZeta (z + (ε : ℂ))) 1 s / s

/-- Away from `1`, the divided difference is the centered reciprocal zeta. -/
theorem centeredReceiverSymbol_eq {ε : ℝ} {s : ℂ} (hs : s ≠ 1) :
    centeredReceiverSymbol ε s =
      riemannZeta s * (invZeta (s + (ε : ℂ)) - invZeta (1 + (ε : ℂ))) / s := by
  have h := sub_smul_dslope (fun z : ℂ => invZeta (z + (ε : ℂ))) 1 s
  simp only [smul_eq_mul] at h
  rw [centeredReceiverSymbol, zetaResidueUnit, Function.update_of_ne hs]
  calc (s - 1) * riemannZeta s * dslope (fun z : ℂ => invZeta (z + (ε : ℂ))) 1 s / s
      = riemannZeta s * ((s - 1) * dslope (fun z : ℂ => invZeta (z + (ε : ℂ))) 1 s) / s := by ring
    _ = _ := by rw [h]

/-- The shifted reciprocal is holomorphic right of its actual zero frontier. -/
theorem differentiableAt_shiftedInvZeta {ε : ℝ} {s : ℂ}
    (hs : zetaZeroAbscissa < s.re + ε) :
    DifferentiableAt ℂ (fun z : ℂ => invZeta (z + (ε : ℂ))) s := by
  have hunit : zetaResidueUnit (s + (ε : ℂ)) ≠ 0 :=
    zetaResidueUnit_ne_zero_of_zeroFree
      (fun _ hz => riemannZeta_ne_zero_of_zetaZeroAbscissa_lt hz) (by simpa using hs)
  have h := (differentiableAt_id.sub_const (1 : ℂ)).mul
    ((analyticAt_zetaResidueUnit (s + (ε : ℂ))).differentiableAt.inv hunit)
  exact h.comp s (differentiableAt_id.add_const _)

/-- Centering removes the pole without adding an analytic hypothesis. -/
theorem differentiableAt_centeredReceiverSymbol {ε : ℝ} (hε : 0 < ε) {s : ℂ}
    (hs0 : 0 < s.re) (hs : zetaZeroAbscissa < s.re + ε) :
    DifferentiableAt ℂ (centeredReceiverSymbol ε) s := by
  let U : Set ℂ := {z | zetaZeroAbscissa < z.re + ε}
  have hU : IsOpen U := isOpen_lt continuous_const (Complex.continuous_re.add_const ε)
  have h1 : (1 : ℂ) ∈ U := by
    change zetaZeroAbscissa < (1 : ℂ).re + ε
    simp only [Complex.one_re]
    linarith [zetaZeroAbscissa_le_one]
  have hd : DifferentiableOn ℂ (fun z : ℂ => invZeta (z + (ε : ℂ))) U :=
    fun z hz => (differentiableAt_shiftedInvZeta hz).differentiableWithinAt
  have hds := ((Complex.differentiableOn_dslope (hU.mem_nhds h1)).mpr hd).differentiableAt
    (hU.mem_nhds hs)
  have hsne : s ≠ 0 := by
    intro h
    rw [h, zero_re] at hs0
    exact lt_irrefl _ hs0
  exact ((analyticAt_zetaResidueUnit s).differentiableAt.mul hds).div differentiableAt_id hsne

/-- Convexity, conjugation, and the absolutely convergent series control the unbounded region. -/
theorem exists_norm_zeta_le_receiver_majorant :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 1 / 2 ≤ s.re →
      (8 ≤ |s.im| ∨ 9 / 8 ≤ s.re) →
      ‖riemannZeta s‖ ≤ A * (1 + |s.im|) ^ ((5 : ℝ) / 16) := by
  obtain ⟨C, hC, hc⟩ := exists_norm_riemannZeta_le_convexity
    (η := 1 / 8) (by norm_num) (by norm_num)
  have hpos : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 9 / 8 → 8 ≤ s.im →
      ‖riemannZeta s‖ ≤ C * (1 + |s.im|) ^ ((5 : ℝ) / 16) := by
    intro s hs hs1 ht
    have h := hc s.re s.im (by linarith) (by linarith) ht
    rw [Complex.re_add_im] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hC.le)
    calc s.im ^ ((1 + 1 / 8 - s.re) / 2) ≤ s.im ^ ((5 : ℝ) / 16) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ (1 + |s.im|) ^ ((5 : ℝ) / 16) :=
          Real.rpow_le_rpow (by linarith) (by rw [abs_of_nonneg (by linarith)]; linarith)
            (by norm_num)
  refine ⟨C + 9, by positivity, fun s hs hout => ?_⟩
  have hw : 1 ≤ (1 + |s.im|) ^ ((5 : ℝ) / 16) :=
    Real.one_le_rpow (by linarith [abs_nonneg s.im]) (by norm_num)
  rcases le_or_gt (9 / 8 : ℝ) s.re with hr | hr
  · have hz := Sieve.norm_riemannZeta_le (s := s) (by linarith)
    have hi : 1 / (s.re - 1) ≤ 8 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    have h9 : ‖riemannZeta s‖ ≤ 9 := by linarith
    exact h9.trans (by nlinarith [mul_le_mul_of_nonneg_left hw (show 0 ≤ C + 9 by positivity)])
  · have ht : 8 ≤ |s.im| := hout.resolve_right (not_le.mpr hr)
    have hb : ‖riemannZeta s‖ ≤ C * (1 + |s.im|) ^ ((5 : ℝ) / 16) := by
      rcases le_abs.mp ht with hp | hn
      · exact hpos s hs hr.le hp
      · have h := hpos (conj s) (by simpa using hs) (by simpa using hr.le)
          (by simp only [conj_im]; linarith)
        simpa only [riemannZeta_conj, norm_conj, conj_im, abs_neg] using h
    exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

/-- The centered symbol has a square-integrable vertical majorant on every closed
half-plane beyond the translated zero frontier. -/
theorem exists_norm_centeredReceiverSymbol_le {ε σ : ℝ} (hε : 0 < ε)
    (hσ : 1 / 2 ≤ σ) (hΘ : zetaZeroAbscissa < σ + ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, σ ≤ s.re →
      ‖centeredReceiverSymbol ε s‖ ≤ K * (1 + |s.im|) ^ (-(9 / 16 : ℝ)) := by
  obtain ⟨A, hA, hZ⟩ := exists_norm_zeta_le_receiver_majorant
  obtain ⟨B, hB, hI⟩ := exists_norm_invZeta_le_of_zetaZeroAbscissa_lt
    (ε := σ + ε - 1 / 2) (by linarith)
  let D := B * 2 ^ ((1 : ℝ) / 8) + ‖invZeta (1 + (ε : ℂ))‖
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hdiff : ∀ s : ℂ, σ ≤ s.re →
      ‖invZeta (s + (ε : ℂ)) - invZeta (1 + (ε : ℂ))‖ ≤
        D * (1 + |s.im|) ^ ((1 : ℝ) / 8) := by
    intro s hs
    have hu : 0 < 1 + |s.im| := by positivity
    have hb := hI (s + (ε : ℂ)) (by simp only [add_re, ofReal_re]; linarith)
    simp only [add_im, ofReal_im, add_zero] at hb
    have hscale : B * (2 + |s.im|) ^ ((1 : ℝ) / 8) ≤
        B * 2 ^ ((1 : ℝ) / 8) * (1 + |s.im|) ^ ((1 : ℝ) / 8) := by
      rw [mul_assoc, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hu.le]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg s.im]) (by norm_num)) hB
    have hanchor := mul_le_mul_of_nonneg_left
      (Real.one_le_rpow (by linarith [abs_nonneg s.im] : 1 ≤ 1 + |s.im|)
        (by norm_num : (0 : ℝ) ≤ 1 / 8)) (norm_nonneg (invZeta (1 + (ε : ℂ))))
    calc ‖invZeta (s + (ε : ℂ)) - invZeta (1 + (ε : ℂ))‖
        ≤ ‖invZeta (s + (ε : ℂ))‖ + ‖invZeta (1 + (ε : ℂ))‖ := norm_sub_le _ _
      _ ≤ D * (1 + |s.im|) ^ ((1 : ℝ) / 8) := by dsimp [D]; nlinarith
  have hlarge : ∀ s : ℂ, σ ≤ s.re → (8 ≤ |s.im| ∨ 9 / 8 ≤ s.re) →
      ‖centeredReceiverSymbol ε s‖ ≤ 4 * A * D * (1 + |s.im|) ^ (-(9 / 16 : ℝ)) := by
    intro s hs hout
    have hsh : 1 / 2 ≤ s.re := hσ.trans hs
    have hs1 : s ≠ 1 := by
      intro heq
      subst s
      norm_num at hout
    have hu : 0 < 1 + |s.im| := by positivity
    have hinv : ‖s‖⁻¹ ≤ 4 * (1 + |s.im|)⁻¹ := by
      have h := inv_anti₀ (by positivity : 0 < (1 + |s.im|) / 4)
        (by linarith [one_add_abs_im_le_four_mul_norm hsh] : (1 + |s.im|) / 4 ≤ ‖s‖)
      rwa [inv_div, div_eq_mul_inv] at h
    rw [centeredReceiverSymbol_eq hs1, norm_div, norm_mul, div_eq_mul_inv]
    calc ‖riemannZeta s‖ * ‖invZeta (s + (ε : ℂ)) - invZeta (1 + (ε : ℂ))‖ * ‖s‖⁻¹
        ≤ (A * (1 + |s.im|) ^ ((5 : ℝ) / 16)) *
            (D * (1 + |s.im|) ^ ((1 : ℝ) / 8)) * (4 * (1 + |s.im|)⁻¹) :=
          mul_le_mul (mul_le_mul (hZ s hsh hout) (hdiff s hs) (norm_nonneg _) (by positivity))
            hinv (by positivity) (by positivity)
      _ = 4 * A * D * ((1 + |s.im|) ^ ((5 : ℝ) / 16) *
          (1 + |s.im|) ^ ((1 : ℝ) / 8) * (1 + |s.im|)⁻¹) := by ring
      _ = _ := by
        rw [← Real.rpow_add hu, ← Real.rpow_neg_one, ← Real.rpow_add hu]
        norm_num
  -- The only region omitted by convexity and the Dirichlet bound is compact.
  let S : Set ℂ := Metric.closedBall 0 10 ∩ {s : ℂ | σ ≤ s.re}
  have hS : IsCompact S := (isCompact_closedBall (0 : ℂ) 10).inter_right
    (isClosed_le continuous_const Complex.continuous_re)
  have hcont : ContinuousOn (centeredReceiverSymbol ε) S := by
    intro s hs
    have hsre : σ ≤ s.re := hs.2
    exact (differentiableAt_centeredReceiverSymbol hε
      (by linarith only [hσ, hsre])
      (by linarith only [hΘ, hsre])).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hcont
  refine ⟨4 * A * D + 9 * max C 0, by positivity, fun s hs => ?_⟩
  by_cases hout : 8 ≤ |s.im| ∨ 9 / 8 ≤ s.re
  · exact (hlarge s hs hout).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (by positivity)) (by positivity))
  · push Not at hout
    have hmem : s ∈ S := by
      refine ⟨?_, hs⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ 10 := by rw [abs_of_nonneg (by linarith)]; linarith [hout.1, hout.2]
    have hu : 0 < 1 + |s.im| := by positivity
    have hp : (1 + |s.im|) ^ ((9 : ℝ) / 16) ≤ 9 := by
      calc (1 + |s.im|) ^ ((9 : ℝ) / 16) ≤ (1 + |s.im|) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg s.im]) (by norm_num)
        _ ≤ 9 := by rw [Real.rpow_one]; linarith [hout.1]
    have hm : max C 0 ≤ 9 * max C 0 * (1 + |s.im|) ^ (-(9 / 16 : ℝ)) := by
      rw [Real.rpow_neg hu.le, ← div_eq_mul_inv,
        le_div_iff₀ (Real.rpow_pos_of_pos hu _)]
      nlinarith [mul_le_mul_of_nonneg_left hp (le_max_right C 0)]
    calc ‖centeredReceiverSymbol ε s‖ ≤ C := hC s hmem
      _ ≤ max C 0 := le_max_left _ _
      _ ≤ 9 * max C 0 * (1 + |s.im|) ^ (-(9 / 16 : ℝ)) := hm
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (by positivity)) (by positivity)

/-- Shifting to any line beyond both frontiers gives a half-plane Hardy function. -/
theorem exists_isHalfPlaneHardy_centeredReceiverSymbol {ε σ : ℝ} (hε : 0 < ε)
    (hσ : 1 / 2 ≤ σ) (hΘ : zetaZeroAbscissa < σ + ε) :
    ∃ M : ℝ, IsHalfPlaneHardy (fun w : ℂ => centeredReceiverSymbol ε (w + (σ : ℂ))) M := by
  obtain ⟨K, hK, hbound⟩ := exists_norm_centeredReceiverSymbol_le hε hσ hΘ
  have hline : ∀ a : ℝ, 0 ≤ a → ∀ ξ : ℝ,
      ‖centeredReceiverSymbol ε (rayLine a ξ + (σ : ℂ))‖ ≤ ‖hardyLineMajorant K ξ‖ := by
    intro a ha ξ
    have h := hbound (rayLine a ξ + (σ : ℂ)) (by simp only [add_re, rayLine_re, ofReal_re]; linarith)
    have him : (rayLine a ξ + (σ : ℂ)).im = 2 * Real.pi * ξ := by simp [rayLine]
    rw [him] at h
    refine h.trans ?_
    rw [hardyLineMajorant, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hK (Real.rpow_nonneg
        (x := 1 + |ξ|) (by positivity) _))]
    refine mul_le_mul_of_nonneg_left ?_ hK
    have h1 : 1 + |ξ| ≤ 1 + |2 * Real.pi * ξ| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      nlinarith [abs_nonneg ξ, Real.pi_gt_three]
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + |ξ|),
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + |2 * Real.pi * ξ|)]
    exact inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_le_rpow (by positivity) h1 (by norm_num))
  have hcont : ∀ a : ℝ, 0 ≤ a →
      Continuous (fun ξ => centeredReceiverSymbol ε (rayLine a ξ + (σ : ℂ))) := by
    intro a ha
    refine continuous_iff_continuousAt.mpr fun ξ => ?_
    have hre : (rayLine a ξ + (σ : ℂ)).re = a + σ := by simp
    have hdiff := differentiableAt_centeredReceiverSymbol hε
      (s := rayLine a ξ + (σ : ℂ)) (by rw [hre]; linarith) (by rw [hre]; linarith)
    have hc : Continuous (fun ξ : ℝ => rayLine a ξ + (σ : ℂ)) := by
      unfold rayLine
      fun_prop
    exact hdiff.continuousAt.comp (f := fun t : ℝ => rayLine a t + (σ : ℂ)) hc.continuousAt
  refine ⟨∫ ξ : ℝ, ‖hardyLineMajorant K ξ‖ ^ (2 : ℕ), ?_⟩
  refine ⟨?_, fun a ha => ?_, fun a ha => ?_⟩
  · intro w hw
    have hw0 : 0 < w.re := hw
    have hre : (w + (σ : ℂ)).re = w.re + σ := by simp
    exact ((differentiableAt_centeredReceiverSymbol hε (s := w + (σ : ℂ))
      (by rw [hre]; linarith) (by rw [hre]; linarith)).comp w
        (differentiableAt_id.add_const _)).differentiableWithinAt
  · exact (memLp_two_hardyLineMajorant K).of_le (hcont a ha.le).aestronglyMeasurable
      (Eventually.of_forall (hline a ha.le))
  · refine integral_mono_of_nonneg (Eventually.of_forall fun ξ => by positivity)
      (integrable_sq_hardyLineMajorant K) (Eventually.of_forall fun ξ => ?_)
    exact pow_le_pow_left₀ (norm_nonneg _) (hline a ha.le ξ) 2

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
