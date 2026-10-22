import GaloisForLFunctions.RHTower.Suzuki.SuzukiDeBrangesVector
import GaloisForLFunctions.RHTower.Suzuki.SuzukiZeroSumIdentity
import GaloisForLFunctions.RHTower.Deninger.DeningerDivisorDefectTrace

noncomputable section

/-!
# The de Branges series is entire

Every element of `E K(Θ_ξ)` is entire.  Expanding in the orthonormal basis, the candidate is the
series `Σ_γ c_γ · E F_γ`, whose terms are the entire de Branges vectors, and the series converges
normally on every ball.

The estimate splits at the ball: only finitely many spectral points lie in a bounded region, and
beyond it the divided slope `A(z)/(z-γ)` is bounded by `2 sup_{|w| ≤ R}|A| / |γ|`.  Against the
square-summable coefficients that is dominated by `(‖c_γ‖² + m_γ/(1+γ²))/2`, and both halves are
summable — the second by the multiplicity-weighted inverse-square spectral sum.

This replaces the source's appeal to nontangential boundary limits and to the Fourier-spectrum
characterisation of Hardy spaces.
-/

open MeasureTheory Set Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The multiplicity-weighted inverse-square spectral sum is summable. -/
theorem summable_xiSupportMult_inv_one_add_sq (hRH : RiemannHypothesis) :
    Summable (fun ρ : XiDivisorSupport =>
      (xiSupportMult ρ : ℝ) / (1 + (xiRealSpectralPointSupport ρ) ^ (2 : ℕ))) := by
  have hI : (0 : ℝ) < (I : ℂ).im := by simp
  have hbase := (hasSum_xiSupport_mult_inv_normSq hRH hI).summable
  refine hbase.congr fun ρ => ?_
  have hnorm : ‖(I : ℂ) - ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)‖ ^ (2 : ℕ)
      = 1 + (xiRealSpectralPointSupport ρ) ^ (2 : ℕ) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [hnorm]

/-- Only finitely many divisor support points lie in a bounded region. -/
theorem finite_setOf_norm_xiRealSpectralPointSupport_le (hRH : RiemannHypothesis) (R : ℝ) :
    {ρ : XiDivisorSupport | ‖((xiRealSpectralPointSupport ρ : ℝ) : ℂ)‖ ≤ R}.Finite := by
  have hcopy := finite_setOf_norm_xiSpectralPoint_le R
  have hmap : {ρ : XiDivisorSupport | ‖((xiRealSpectralPointSupport ρ : ℝ) : ℂ)‖ ≤ R}
      ⊆ (fun q : XiZeroCopy => q.1) ''
        {q : XiZeroCopy | ‖xiSpectralPoint q‖ ≤ R} := by
    intro ρ hρ
    refine ⟨⟨ρ, ⟨0, xiSupportMult_pos ρ⟩⟩, ?_, rfl⟩
    show ‖xiSpectralPoint (⟨ρ, ⟨0, xiSupportMult_pos ρ⟩⟩ : XiZeroCopy)‖ ≤ R
    rw [xiSpectralPoint_eq_support, ← ofReal_xiRealSpectralPointSupport hRH]
    exact hρ
  exact Set.Finite.subset (hcopy.image _) hmap

/-! ## Uniform bounds for the divided slopes on a ball -/

/-- The supremum of a divided slope of `A` on a closed ball. -/
def suzukiDslopeSup (γ R : ℝ) : ℝ :=
  sSup ((fun z : ℂ => ‖dslope XiC ((γ : ℝ) : ℂ) z‖) '' Metric.closedBall 0 R)

theorem continuous_dslope_XiC (γ : ℝ) : Continuous (dslope XiC ((γ : ℝ) : ℂ)) := by
  have hd : Differentiable ℂ (dslope XiC ((γ : ℝ) : ℂ)) := by
    rw [← differentiableOn_univ]
    refine (Complex.differentiableOn_dslope (by simp)).mpr ?_
    exact XiC_differentiable.differentiableOn
  exact hd.continuous

theorem bddAbove_dslope_image (γ R : ℝ) :
    BddAbove ((fun z : ℂ => ‖dslope XiC ((γ : ℝ) : ℂ) z‖) '' Metric.closedBall 0 R) := by
  refine IsCompact.bddAbove ?_
  exact (isCompact_closedBall (0 : ℂ) R).image
    ((continuous_dslope_XiC γ).norm)

theorem le_suzukiDslopeSup {γ R : ℝ} {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    ‖dslope XiC ((γ : ℝ) : ℂ) z‖ ≤ suzukiDslopeSup γ R :=
  le_csSup (bddAbove_dslope_image γ R) ⟨z, hz, rfl⟩

theorem suzukiDslopeSup_nonneg {γ R : ℝ} (hR : 0 ≤ R) : 0 ≤ suzukiDslopeSup γ R := by
  refine le_trans (norm_nonneg (dslope XiC ((γ : ℝ) : ℂ) 0)) ?_
  exact le_suzukiDslopeSup (by simpa using hR)

/-- Far from the ball the divided slope is small: the numerator is bounded and the denominator
is comparable to the spectral point. -/
theorem suzukiDslopeSup_le_of_far {γ R M : ℝ} (hR : 0 < R)
    (hγ0 : XiC ((γ : ℝ) : ℂ) = 0)
    (hM : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖XiC z‖ ≤ M)
    (hfar : 2 * R + 1 ≤ |γ|) :
    suzukiDslopeSup γ R ≤ 2 * M / |γ| := by
  have hγ : 0 < |γ| := by linarith
  refine csSup_le ⟨‖dslope XiC ((γ : ℝ) : ℂ) 0‖, ⟨0, by simpa using hR.le, rfl⟩⟩ ?_
  rintro y ⟨z, hz, rfl⟩
  show ‖dslope XiC ((γ : ℝ) : ℂ) z‖ ≤ 2 * M / |γ|
  have hzR : ‖z‖ ≤ R := by simpa using hz
  have hγn : ‖((γ : ℝ) : ℂ)‖ = |γ| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hne : z ≠ ((γ : ℝ) : ℂ) := by
    intro h
    rw [h, hγn] at hzR
    linarith
  have hden : |γ| / 2 ≤ ‖z - ((γ : ℝ) : ℂ)‖ := by
    have h := norm_sub_norm_le z ((γ : ℝ) : ℂ)
    rw [hγn] at h
    have h2 : ‖z‖ - |γ| ≤ R - |γ| := by linarith
    have : -(‖z - ((γ : ℝ) : ℂ)‖) ≤ R - |γ| := by
      have hrev := norm_sub_norm_le ((γ : ℝ) : ℂ) z
      rw [hγn, norm_sub_rev] at hrev
      linarith
    linarith
  have hzM : ‖XiC z‖ ≤ M := hM z hz
  have hdenpos : (0 : ℝ) < |γ| / 2 := by linarith
  rw [dslope_of_ne _ hne, slope_def_field, norm_div]
  rw [div_le_div_iff₀ (lt_of_lt_of_le hdenpos hden) hγ]
  have hnum : ‖XiC z - XiC ((γ : ℝ) : ℂ)‖ ≤ M := by
    rw [hγ0, sub_zero]
    exact hzM
  nlinarith [norm_nonneg (XiC z - XiC ((γ : ℝ) : ℂ)), hden, hzM]


/-! ## The de Branges series is entire -/

/-- The series `Σ c_γ · E F_γ`, written through the entire de Branges vectors. -/
def suzukiDeBrangesSeries (c : XiDivisorSupport → ℂ) (z : ℂ) : ℂ :=
  ∑' ρ : XiDivisorSupport,
    c ρ * suzukiDeBrangesVector (xiRealSpectralPointSupport ρ) (xiSupportMult ρ) z

theorem norm_suzukiDeBrangesVector_le {γ R : ℝ} {m : ℕ} {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    ‖suzukiDeBrangesVector γ m z‖
      ≤ Real.sqrt ((m : ℝ) / Real.pi) * suzukiDslopeSup γ R := by
  rw [suzukiDeBrangesVector, norm_mul, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (le_suzukiDslopeSup hz) (Real.sqrt_nonneg _)

/-- The dominating series for the de Branges expansion on a ball. -/
theorem summable_deBrangesBound (hRH : RiemannHypothesis)
    {c : XiDivisorSupport → ℂ} (hc : Summable fun ρ : XiDivisorSupport => ‖c ρ‖ ^ (2 : ℕ))
    {R M : ℝ} (hR : 0 < R) (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖XiC z‖ ≤ M) :
    Summable (fun ρ : XiDivisorSupport =>
      ‖c ρ‖ * Real.sqrt ((xiSupportMult ρ : ℝ) / Real.pi)
        * suzukiDslopeSup (xiRealSpectralPointSupport ρ) R) := by
  have hpi := Real.pi_pos
  have hspec := summable_xiSupportMult_inv_one_add_sq hRH
  set u : XiDivisorSupport → ℝ := fun ρ =>
    ‖c ρ‖ * Real.sqrt ((xiSupportMult ρ : ℝ) / Real.pi)
      * suzukiDslopeSup (xiRealSpectralPointSupport ρ) R with hu
  have hunn : ∀ ρ : XiDivisorSupport, 0 ≤ u ρ := by
    intro ρ
    rw [hu]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
      (suzukiDslopeSup_nonneg hR.le)
  refine (summable_subtype_and_compl (f := u) (s := {ρ : XiDivisorSupport |
    ‖((xiRealSpectralPointSupport ρ : ℝ) : ℂ)‖ ≤ 2 * R + 1})).mp ⟨?_, ?_⟩
  · exact (finite_setOf_norm_xiRealSpectralPointSupport_le hRH (2 * R + 1)).summable u
  · set K : ℝ := 2 * Real.sqrt 2 * M / Real.sqrt Real.pi with hK
    have hK0 : 0 ≤ K := by
      rw [hK]
      have := Real.sqrt_nonneg (2 : ℝ)
      have := Real.sqrt_nonneg Real.pi
      positivity
    refine Summable.of_nonneg_of_le (fun ρ => hunn _) ?_
      (((hc.add hspec).mul_left (K / 2)).subtype _)
    rintro ⟨ρ, hρ⟩
    have hfar : 2 * R + 1 ≤ |xiRealSpectralPointSupport ρ| := by
      have hnot : ¬ (‖((xiRealSpectralPointSupport ρ : ℝ) : ℂ)‖ ≤ 2 * R + 1) := hρ
      have hlt : 2 * R + 1 < ‖((xiRealSpectralPointSupport ρ : ℝ) : ℂ)‖ := lt_of_not_ge hnot
      rw [Complex.norm_real, Real.norm_eq_abs] at hlt
      linarith
    have hγ1 : (1 : ℝ) ≤ |xiRealSpectralPointSupport ρ| := by linarith
    have hsup := suzukiDslopeSup_le_of_far hR (XiC_xiRealSpectralPointSupport hRH ρ) hM hfar
    set g : ℝ := xiRealSpectralPointSupport ρ with hg
    set mm : ℝ := (xiSupportMult ρ : ℝ) with hmm
    have hm : (0 : ℝ) ≤ mm := Nat.cast_nonneg _
    have hden : (0 : ℝ) < 1 + g ^ (2 : ℕ) := by positivity
    have habs : (0 : ℝ) < |g| := by linarith
    have hsqle : Real.sqrt (1 + g ^ (2 : ℕ)) ≤ Real.sqrt 2 * |g| := by
      have h1 : (1 : ℝ) + g ^ (2 : ℕ) ≤ 2 * g ^ (2 : ℕ) := by nlinarith [sq_abs g]
      calc Real.sqrt (1 + g ^ (2 : ℕ)) ≤ Real.sqrt (2 * g ^ (2 : ℕ)) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt 2 * |g| := by
            rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq_eq_abs]
    have hinv : 1 / |g| ≤ Real.sqrt 2 / Real.sqrt (1 + g ^ (2 : ℕ)) := by
      rw [div_le_div_iff₀ habs (Real.sqrt_pos.mpr hden), one_mul]
      exact hsqle
    have hsplit : Real.sqrt (mm / Real.pi) = Real.sqrt mm / Real.sqrt Real.pi :=
      Real.sqrt_div hm _
    have hb : Real.sqrt (mm / (1 + g ^ (2 : ℕ))) = Real.sqrt mm / Real.sqrt (1 + g ^ (2 : ℕ)) :=
      Real.sqrt_div hm _
    have hb2 : (Real.sqrt (mm / (1 + g ^ (2 : ℕ)))) ^ (2 : ℕ) = mm / (1 + g ^ (2 : ℕ)) :=
      Real.sq_sqrt (by positivity)
    have hamgm : ‖c ρ‖ * Real.sqrt (mm / (1 + g ^ (2 : ℕ)))
        ≤ (‖c ρ‖ ^ (2 : ℕ) + mm / (1 + g ^ (2 : ℕ))) / 2 := by
      nlinarith [sq_nonneg (‖c ρ‖ - Real.sqrt (mm / (1 + g ^ (2 : ℕ)))), hb2]
    have hP : (0 : ℝ) ≤ ‖c ρ‖ * (Real.sqrt mm / Real.sqrt Real.pi) * (2 * M) := by
      have := Real.sqrt_nonneg mm
      have := Real.sqrt_nonneg Real.pi
      positivity
    have hchain : u ρ ≤ ‖c ρ‖ * (Real.sqrt mm / Real.sqrt Real.pi) * (2 * M / |g|) := by
      show ‖c ρ‖ * Real.sqrt (mm / Real.pi) * suzukiDslopeSup g R
        ≤ ‖c ρ‖ * (Real.sqrt mm / Real.sqrt Real.pi) * (2 * M / |g|)
      rw [hsplit]
      refine mul_le_mul_of_nonneg_left hsup ?_
      have := Real.sqrt_nonneg mm
      have := Real.sqrt_nonneg Real.pi
      positivity
    have hL : ‖c ρ‖ * (Real.sqrt mm / Real.sqrt Real.pi) * (2 * M / |g|)
        = (‖c ρ‖ * (Real.sqrt mm / Real.sqrt Real.pi) * (2 * M)) * (1 / |g|) := by
      field_simp
    have hpine : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpi)
    have hdne : Real.sqrt (1 + g ^ (2 : ℕ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hden)
    have hRr : K * (‖c ρ‖ * Real.sqrt (mm / (1 + g ^ (2 : ℕ))))
        = (‖c ρ‖ * (Real.sqrt mm / Real.sqrt Real.pi) * (2 * M))
          * (Real.sqrt 2 / Real.sqrt (1 + g ^ (2 : ℕ))) := by
      rw [hK, hb]
      field_simp
    have hmid : ‖c ρ‖ * (Real.sqrt mm / Real.sqrt Real.pi) * (2 * M / |g|)
        ≤ K * (‖c ρ‖ * Real.sqrt (mm / (1 + g ^ (2 : ℕ)))) := by
      rw [hL, hRr]
      exact mul_le_mul_of_nonneg_left hinv hP
    have hfinal := mul_le_mul_of_nonneg_left hamgm hK0
    show u ρ ≤ K / 2 * (‖c ρ‖ ^ (2 : ℕ) + mm / (1 + g ^ (2 : ℕ)))
    linarith


/-- **The de Branges series is entire.**  Near a spectral point the divided slope removes the
pole, and far from the ball the terms are dominated by the square-summable weights. -/
theorem differentiable_suzukiDeBrangesSeries (hRH : RiemannHypothesis)
    {c : XiDivisorSupport → ℂ} (hc : Summable fun ρ : XiDivisorSupport => ‖c ρ‖ ^ (2 : ℕ)) :
    Differentiable ℂ (suzukiDeBrangesSeries c) := by
  have hpi := Real.pi_pos
  have hspec := summable_xiSupportMult_inv_one_add_sq hRH
  intro z₀
  set R : ℝ := ‖z₀‖ + 1 with hRdef
  have hR : 0 < R := by
    have := norm_nonneg z₀
    linarith
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    XiC_differentiable.continuous.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (XiC 0)) (hM 0 (by simpa using hR.le))
  set u : XiDivisorSupport → ℝ := fun ρ =>
    ‖c ρ‖ * Real.sqrt ((xiSupportMult ρ : ℝ) / Real.pi)
      * suzukiDslopeSup (xiRealSpectralPointSupport ρ) R with hu
  have hbound : ∀ (ρ : XiDivisorSupport) (w : ℂ), w ∈ Metric.ball (0 : ℂ) R →
      ‖c ρ * suzukiDeBrangesVector (xiRealSpectralPointSupport ρ) (xiSupportMult ρ) w‖
        ≤ u ρ := by
    intro ρ w hw
    have hwc : w ∈ Metric.closedBall (0 : ℂ) R := Metric.ball_subset_closedBall hw
    rw [norm_mul, hu]
    have h1 := norm_suzukiDeBrangesVector_le (γ := xiRealSpectralPointSupport ρ)
      (m := xiSupportMult ρ) hwc
    calc ‖c ρ‖ * ‖suzukiDeBrangesVector (xiRealSpectralPointSupport ρ)
          (xiSupportMult ρ) w‖
        ≤ ‖c ρ‖ * (Real.sqrt ((xiSupportMult ρ : ℝ) / Real.pi)
            * suzukiDslopeSup (xiRealSpectralPointSupport ρ) R) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖c ρ‖ * Real.sqrt ((xiSupportMult ρ : ℝ) / Real.pi)
            * suzukiDslopeSup (xiRealSpectralPointSupport ρ) R := by ring
  have hsummable : Summable u := summable_deBrangesBound hRH hc hR hM0 hM
  refine ((differentiableOn_tsum_of_summable_norm hsummable ?_ Metric.isOpen_ball
    hbound).differentiableAt (Metric.isOpen_ball.mem_nhds ?_))
  · intro ρ
    exact ((differentiable_suzukiDeBrangesVector _ _).const_mul (c ρ)).differentiableOn
  · simp [hRdef]


end RHTower
