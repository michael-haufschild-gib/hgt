import GaloisForLFunctions.RHTower.ThetaCuspKernelLogConcavity

/-!
# Fixed-profile rigidity for center compensation

A correction with fixed displacement profile cannot preserve the source mass and
satisfy the positive-definite two-point bound at every center. Its normalized
coefficient diverges negatively while every reflected source value stays below
the source mass. The quantitative bound also constrains varying profiles.
-/

open Set
namespace RHTower
noncomputable section

/-- The normalized center correction is unbounded below along the positive ray. -/
theorem exists_thetaCuspCenterCompensationSign_lt (B : ℝ) :
    ∃ x : ℝ, 1 ≤ x ∧ (3 + 2*x*deriv thetaCuspLogSource x) < B := by
  have hanti : StrictAnti (deriv thetaCuspLogSource) :=
    strictAntiOn_univ.mp <|
      strictConcaveOn_thetaCuspLogSource.strictAntiOn_deriv fun x _ =>
        (hasDerivAt_thetaCuspLogSource x).differentiableAt
  have hz : deriv thetaCuspLogSource 0 = 0 := by
    have hd : HasDerivAt thetaCuspLogSource (deriv thetaCuspLogSource 0) 0 :=
      (hasDerivAt_thetaCuspLogSource 0).differentiableAt.hasDerivAt
    have hd' : HasDerivAt thetaCuspLogSource (deriv thetaCuspLogSource 0)
        ((-id) (0 : ℝ)) := by simpa using hd
    have hr := hd'.comp 0 ((hasDerivAt_id (0 : ℝ)).neg)
    have he : (fun x : ℝ => thetaCuspLogSource (-x)) = thetaCuspLogSource := by
      funext x
      simp only [thetaCuspLogSource, thetaCuspFullSource_neg]
    change HasDerivAt (fun x : ℝ => thetaCuspLogSource (-x))
      (deriv thetaCuspLogSource 0 * -1) 0 at hr
    rw [he, mul_neg_one] at hr
    have hu := hd.unique hr
    linarith only [hu]
  have hL : deriv thetaCuspLogSource 1 < 0 := by
    simpa only [hz] using hanti (by norm_num : (0 : ℝ) < 1)
  let L := deriv thetaCuspLogSource 1
  have hLn : L < 0 := hL
  let x : ℝ := 1 + (|B| + 4) / (-2 * L)
  have hx : 1 ≤ x := by
    dsimp [x]
    have : 0 ≤ (|B| + 4) / (-2 * L) :=
      div_nonneg (by positivity) (by linarith)
    linarith
  have hp : 2*x*L = 2*L-(|B|+4) := by
    dsimp [x]
    field_simp [ne_of_lt hLn]
    ring
  have hs := mul_le_mul_of_nonneg_left (hanti.antitone hx)
    (show 0 ≤ 2*x by linarith)
  refine ⟨x, hx, ?_⟩
  change 2*x*deriv thetaCuspLogSource x ≤ 2*x*L at hs
  nlinarith only [hs, hp, hLn, neg_abs_le B]

/-- A displacement profile multiplied by the literal center correction. -/
def thetaCuspCenterCorrectedProfile (C : ℝ → ℝ) (x t : ℝ) : ℝ :=
  thetaCuspFullSource (x+t)*thetaCuspFullSource (x-t) +
    (3*thetaCuspFullSource x^2 + 2*x*thetaCuspFullSource x*deriv thetaCuspFullSource x)*C t

/-- Exact admissible interval for one correction value when its center coefficient is negative. -/
theorem thetaCuspCenterCorrection_interval {x t c : ℝ}
    (hg : (3*thetaCuspFullSource x^2 + 2*x*thetaCuspFullSource x*deriv thetaCuspFullSource x) < 0)
    (hbound : |thetaCuspFullSource (x+t)*thetaCuspFullSource (x-t) +
      (3*thetaCuspFullSource x^2 + 2*x*thetaCuspFullSource x*deriv thetaCuspFullSource x)*c| ≤ thetaCuspFullSource x^2) :
    (thetaCuspFullSource (x+t)*thetaCuspFullSource (x-t)-thetaCuspFullSource x^2) /
        (-(3*thetaCuspFullSource x^2 + 2*x*thetaCuspFullSource x*deriv thetaCuspFullSource x)) ≤ c ∧
      c ≤ (thetaCuspFullSource (x+t)*thetaCuspFullSource (x-t)+thetaCuspFullSource x^2) /
        (-(3*thetaCuspFullSource x^2 + 2*x*thetaCuspFullSource x*deriv thetaCuspFullSource x)) := by
  have hab := abs_le.mp hbound
  constructor
  · apply (div_le_iff₀ (neg_pos.mpr hg)).2
    nlinarith only [hab.2]
  · apply (le_div_iff₀ (neg_pos.mpr hg)).2
    nlinarith only [hab.1]

/-- Every mass-preserving two-point bound controls the full normalized correction value. -/
theorem thetaCuspCenterCorrection_normalized_bound {x t c : ℝ}
    (hbound : |thetaCuspFullSource (x+t)*thetaCuspFullSource (x-t) +
      (3*thetaCuspFullSource x^2 + 2*x*thetaCuspFullSource x*deriv thetaCuspFullSource x)*c| ≤ thetaCuspFullSource x^2) :
    |(3 + 2*x*deriv thetaCuspLogSource x)| * |c| ≤ 2 := by
  have hm : 0 < thetaCuspFullSource x^2 :=
    sq_pos_of_pos (thetaCuspFullSource_pos_all x)
  have hP : |thetaCuspFullSource (x+t)*thetaCuspFullSource (x-t)| ≤
      thetaCuspFullSource x^2 := by
    rw [abs_of_pos (mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _))]
    exact thetaCuspFullSource_mul_reflect_le_sq x t
  have hcorr : |(3*thetaCuspFullSource x^2 + 2*x*thetaCuspFullSource x*deriv thetaCuspFullSource x)*c| ≤ 2*thetaCuspFullSource x^2 := by
    calc
      _ = |(thetaCuspFullSource (x+t)*thetaCuspFullSource (x-t) +
          (3*thetaCuspFullSource x^2 + 2*x*thetaCuspFullSource x*deriv thetaCuspFullSource x)*c) -
          thetaCuspFullSource (x+t)*thetaCuspFullSource (x-t)| := by congr 1; ring
      _ ≤ |thetaCuspFullSource (x+t)*thetaCuspFullSource (x-t) +
          (3*thetaCuspFullSource x^2 + 2*x*thetaCuspFullSource x*deriv thetaCuspFullSource x)*c| +
          |thetaCuspFullSource (x+t)*thetaCuspFullSource (x-t)| := abs_sub _ _
      _ ≤ 2*thetaCuspFullSource x^2 := by linarith only [hbound, hP]
  have hfactor :
      3*thetaCuspFullSource x^2 + 2*x*thetaCuspFullSource x*deriv thetaCuspFullSource x =
        thetaCuspFullSource x^2*(3 + 2*x*deriv thetaCuspLogSource x) := by
    rw [(hasDerivAt_thetaCuspLogSource x).deriv]
    simp only [iteratedDeriv_one]
    field_simp [(thetaCuspFullSource_pos_all x).ne']
  rw [hfactor, abs_mul, abs_mul, abs_of_pos hm] at hcorr
  apply (mul_le_mul_iff_right₀ hm).mp
  nlinarith only [hcorr]

/-- A fixed displacement profile preserving the source mass and satisfying every
positive-definite two-point bound must vanish identically. -/
theorem thetaCuspFixedCenterCorrection_eq_zero (C : ℝ → ℝ) (hC : C 0 = 0)
    (hbound : ∀ x : ℝ, 0 ≤ x → ∀ t : ℝ,
      |thetaCuspCenterCorrectedProfile C x t| ≤ thetaCuspCenterCorrectedProfile C x 0) :
    C = 0 := by
  funext t
  change C t = 0
  by_contra hc
  have hcpos : 0 < |C t| := abs_pos.mpr hc
  obtain ⟨x, hx, hg⟩ := exists_thetaCuspCenterCompensationSign_lt (-(2/|C t|+1))
  have hb := hbound x (by linarith) t
  have hb' : |thetaCuspFullSource (x+t)*thetaCuspFullSource (x-t) +
      (3*thetaCuspFullSource x^2 + 2*x*thetaCuspFullSource x*deriv thetaCuspFullSource x)*C t| ≤ thetaCuspFullSource x^2 := by
    simpa only [thetaCuspCenterCorrectedProfile, add_zero, sub_zero, hC, mul_zero,
      add_zero, sq] using hb
  have hn := thetaCuspCenterCorrection_normalized_bound hb'
  have hdiv : 0 < 2/|C t| := div_pos (by norm_num) hcpos
  have hgneg : (3 + 2*x*deriv thetaCuspLogSource x) < 0 := by linarith
  rw [abs_of_neg hgneg] at hn
  have hp := mul_lt_mul_of_pos_right hg hcpos
  have hd : (2/|C t|)* |C t| = 2 := div_mul_cancel₀ 2 hcpos.ne'
  nlinarith only [hn, hp, hd, hcpos]

end
end RHTower
