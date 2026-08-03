import GaloisForLFunctions.HTGeometry.ExponentialFullIndependence
import GaloisForLFunctions.HTGeometry.SpectralMobiusGauge
import GaloisForLFunctions.HTGeometry.FamilyMobiusGauge
import GaloisForLFunctions.HTGeometry.ParabolicCayleyAutomorphism
import GaloisForLFunctions.HTGeometry.ParabolicOrbitCircleClosure

/-!
# Differential independence of the parabolic orbit of a bounded outer map

The outer map attached to a Herglotz function is `O = exp (sigma o cayley)` with
`sigma = (m - i) / (m + i)`, and the parabolic automorphism acts on it by translating the half-plane
variable.  Its orbit powers are therefore

`(O o tau_t) ^ N = exp (N * sigma (cayley + t))`,

so differential independence of the orbit powers follows from that of the translate family by four
gauges: the codomain Mobius map `sigma`, the domain Cayley map, multiplication by the constant `N`,
and the exponential.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Cayley image of a Herglotz function: the bounded exponent of the outer orbit map. -/
def herglotzSigma (m : ℂ → ℂ) (z : ℂ) : ℂ := (m z - Complex.I) / (m z + Complex.I)

/-- The outer orbit map attached to a Herglotz function. -/
def outerOrbitMap (m : ℂ → ℂ) (w : ℂ) : ℂ :=
  Complex.exp (herglotzSigma m (cayleyToUpper w))

/-- **Differential independence of the parabolic orbit powers.**  If the half-plane translates of a
Herglotz function satisfy no differential relation, then for every positive power the parabolic
orbit of the associated bounded outer map satisfies none either. -/
theorem not_familyDifferentiallyAlgebraicOn_parabolicOrbitPow {r : ℕ} (t : Fin r → ℝ)
    {m : ℂ → ℂ} (hmA : AnalyticOnNhd ℂ m {z : ℂ | 0 < z.im})
    (hmPos : ∀ z : ℂ, 0 < z.im → 0 < (m z).im)
    (hIndep : ¬ FamilyDifferentiallyAlgebraicOn
      (fun j z => m (z + (t j : ℂ))) {z : ℂ | 0 < z.im})
    {N : ℕ} (hN : N ≠ 0) :
    ¬ FamilyDifferentiallyAlgebraicOn
      (fun j w => (outerOrbitMap m (parabolicAut (t j) w)) ^ N) openDisc := by
  classical
  have hHo : IsOpen {z : ℂ | 0 < z.im} := isOpen_upperHalf
  have hHc : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  have hshift : ∀ (j : Fin r) (z : ℂ), z ∈ {z : ℂ | 0 < z.im} → z + (t j : ℂ) ∈ {z : ℂ | 0 < z.im} := by
    intro j z hz
    have him : (z + (t j : ℂ)).im = z.im := by simp
    show 0 < (z + (t j : ℂ)).im
    rw [him]
    exact hz
  -- the translated family and its Cayley image
  have hgtA : ∀ j, AnalyticOnNhd ℂ (fun z => m (z + (t j : ℂ))) {z : ℂ | 0 < z.im} := by
    intro j z hz
    have h1 : AnalyticAt ℂ (fun z : ℂ => z + (t j : ℂ)) z := analyticAt_id.add analyticAt_const
    have h2 : AnalyticAt ℂ (m ∘ fun z : ℂ => z + (t j : ℂ)) z :=
      AnalyticAt.comp (hmA _ (hshift j z hz)) h1
    exact h2
  have hgtS : ∀ (j : Fin r), ∀ z ∈ {z : ℂ | 0 < z.im},
      ContDiffAt ℂ (⊤ : ℕ∞) (fun z => m (z + (t j : ℂ))) z :=
    fun j => contDiffAt_of_analyticOnNhd (hgtA j)
  have hden : ∀ (j : Fin r), ∀ z ∈ {z : ℂ | 0 < z.im},
      (1 : ℂ) * m (z + (t j : ℂ)) + Complex.I ≠ 0 := by
    intro j z hz hcon
    have hpos : 0 < (m (z + (t j : ℂ))).im := hmPos _ (hshift j z hz)
    have him : ((1 : ℂ) * m (z + (t j : ℂ)) + Complex.I).im = (m (z + (t j : ℂ))).im + 1 := by
      simp
    rw [hcon] at him
    simp only [Complex.zero_im] at him
    linarith
  have hdet1 : (1 : ℂ) * Complex.I - (-Complex.I) * 1 ≠ 0 := by
    intro hcon
    have : (2 : ℂ) * Complex.I = 0 := by linear_combination hcon
    simp only [mul_eq_zero] at this
    rcases this with h | h
    · exact two_ne_zero h
    · exact Complex.I_ne_zero h
  -- step one: the codomain Mobius map
  have hpsi : ¬ FamilyDifferentiallyAlgebraicOn
      (fun j z => ((1 : ℂ) * m (z + (t j : ℂ)) + (-Complex.I))
        / ((1 : ℂ) * m (z + (t j : ℂ)) + Complex.I)) {z : ℂ | 0 < z.im} := by
    intro hcon
    exact hIndep (familyDifferentiallyAlgebraicOn_of_mobius hHo hgtS hdet1 hden hcon)
  have hsigmaA : ∀ j, AnalyticOnNhd ℂ
      (fun z => ((1 : ℂ) * m (z + (t j : ℂ)) + (-Complex.I))
        / ((1 : ℂ) * m (z + (t j : ℂ)) + Complex.I)) {z : ℂ | 0 < z.im} := by
    intro j z hz
    have h1 : AnalyticAt ℂ (fun z : ℂ => (1 : ℂ) * m (z + (t j : ℂ)) + (-Complex.I)) z :=
      (analyticAt_const.mul (hgtA j z hz)).add analyticAt_const
    have h2 : AnalyticAt ℂ (fun z : ℂ => (1 : ℂ) * m (z + (t j : ℂ)) + Complex.I) z :=
      (analyticAt_const.mul (hgtA j z hz)).add analyticAt_const
    exact h1.div h2 (hden j z hz)
  -- step two: the domain Cayley map
  have hdiscden : ∀ w ∈ openDisc, (-1 : ℂ) * w + 1 ≠ 0 := by
    intro w hw hcon
    have hw1 : ‖w‖ < 1 := by
      rw [openDisc, Metric.mem_ball, dist_zero_right] at hw
      exact hw
    have hweq : w = 1 := by linear_combination -hcon
    rw [hweq] at hw1
    simp at hw1
  have hdiscmap : ∀ w ∈ openDisc,
      ((Complex.I : ℂ) * w + Complex.I) / ((-1 : ℂ) * w + 1) ∈ {z : ℂ | 0 < z.im} := by
    intro w hw
    have hw1 : ‖w‖ < 1 := by
      rw [openDisc, Metric.mem_ball, dist_zero_right] at hw
      exact hw
    have hval : ((Complex.I : ℂ) * w + Complex.I) / ((-1 : ℂ) * w + 1) = cayleyToUpper w := by
      rw [cayleyToUpper]
      congr 1 <;> ring
    rw [hval]
    exact im_cayleyToUpper_pos hw1
  have hdet2 : (Complex.I : ℂ) * 1 - Complex.I * (-1) ≠ 0 := by
    intro hcon
    have : (2 : ℂ) * Complex.I = 0 := by linear_combination hcon
    simp only [mul_eq_zero] at this
    rcases this with h | h
    · exact two_ne_zero h
    · exact Complex.I_ne_zero h
  have hdiscOpen : IsOpen openDisc := Metric.isOpen_ball
  have hzero : (0 : ℂ) ∈ openDisc := by
    rw [openDisc, Metric.mem_ball, dist_self]
    norm_num
  have hcayley : ¬ FamilyDifferentiallyAlgebraicOn
      (fun j w => ((1 : ℂ) * m (cayleyToUpper w + (t j : ℂ)) + (-Complex.I))
        / ((1 : ℂ) * m (cayleyToUpper w + (t j : ℂ)) + Complex.I)) openDisc := by
    intro hcon
    refine not_familyDifferentiallyAlgebraicOn_comp_mobius hHo hHc hsigmaA hdiscOpen hdet2
      hdiscden hdiscmap hzero hpsi ?_
    refine familyDifferentiallyAlgebraicOn_congr_of_isOpen hdiscOpen ?_ hcon
    intro j w hw
    have hval : ((Complex.I : ℂ) * w + Complex.I) / ((-1 : ℂ) * w + 1) = cayleyToUpper w := by
      rw [cayleyToUpper]
      congr 1 <;> ring
    rw [hval]
  -- step three: multiplication by the constant `N`
  have hcayleyS : ∀ w ∈ openDisc, ∀ j : Fin r, ContDiffAt ℂ (⊤ : ℕ∞)
      (fun w => ((1 : ℂ) * m (cayleyToUpper w + (t j : ℂ)) + (-Complex.I))
        / ((1 : ℂ) * m (cayleyToUpper w + (t j : ℂ)) + Complex.I)) w := by
    intro w hw j
    have hcayA : AnalyticAt ℂ cayleyToUpper w := by
      have hden' : (1 : ℂ) - w ≠ 0 := by
        intro hcon
        exact hdiscden w hw (by linear_combination hcon)
      have h1 : AnalyticAt ℂ (fun w : ℂ => Complex.I * (1 + w)) w :=
        analyticAt_const.mul (analyticAt_const.add analyticAt_id)
      have h2 : AnalyticAt ℂ (fun w : ℂ => 1 - w) w := analyticAt_const.sub analyticAt_id
      exact h1.div h2 hden'
    have hmem : cayleyToUpper w ∈ {z : ℂ | 0 < z.im} := by
      have hw1 : ‖w‖ < 1 := by
        rw [openDisc, Metric.mem_ball, dist_zero_right] at hw
        exact hw
      exact im_cayleyToUpper_pos hw1
    have hcomp : AnalyticAt ℂ
        (fun w => ((1 : ℂ) * m (cayleyToUpper w + (t j : ℂ)) + (-Complex.I))
          / ((1 : ℂ) * m (cayleyToUpper w + (t j : ℂ)) + Complex.I)) w :=
      (hsigmaA j _ hmem).comp hcayA
    exact hcomp.contDiffAt
  have hsmul : ¬ FamilyDifferentiallyAlgebraicOn
      (fun j w => (N : ℂ) * (((1 : ℂ) * m (cayleyToUpper w + (t j : ℂ)) + (-Complex.I))
        / ((1 : ℂ) * m (cayleyToUpper w + (t j : ℂ)) + Complex.I))) openDisc := by
    intro hcon
    refine hcayley (familyDifferentiallyAlgebraicOn_of_mul_polynomial _
      (fun _ => Polynomial.C (N : ℂ)) ?_ hcayleyS ?_)
    · intro j
      simp only [ne_eq, Polynomial.C_eq_zero, Nat.cast_eq_zero]
      exact hN
    · refine familyDifferentiallyAlgebraicOn_congr_of_isOpen hdiscOpen ?_ hcon
      intro j w hw
      rw [Polynomial.eval_C]
  -- step four: the exponential
  have hexpA : ∀ j, AnalyticOnNhd ℂ
      (fun w => (N : ℂ) * (((1 : ℂ) * m (cayleyToUpper w + (t j : ℂ)) + (-Complex.I))
        / ((1 : ℂ) * m (cayleyToUpper w + (t j : ℂ)) + Complex.I))) openDisc := by
    intro j w hw
    have hcayA : AnalyticAt ℂ cayleyToUpper w := by
      have hden' : (1 : ℂ) - w ≠ 0 := by
        intro hcon
        exact hdiscden w hw (by linear_combination hcon)
      have h1 : AnalyticAt ℂ (fun w : ℂ => Complex.I * (1 + w)) w :=
        analyticAt_const.mul (analyticAt_const.add analyticAt_id)
      have h2 : AnalyticAt ℂ (fun w : ℂ => 1 - w) w := analyticAt_const.sub analyticAt_id
      exact h1.div h2 hden'
    have hmem : cayleyToUpper w ∈ {z : ℂ | 0 < z.im} := by
      have hw1 : ‖w‖ < 1 := by
        rw [openDisc, Metric.mem_ball, dist_zero_right] at hw
        exact hw
      exact im_cayleyToUpper_pos hw1
    exact analyticAt_const.mul ((hsigmaA j _ hmem).comp hcayA)
  have hexp := not_familyDifferentiallyAlgebraicOn_exp hdiscOpen
    ((convex_ball (0 : ℂ) 1).isPreconnected) ⟨0, hzero⟩ hexpA hsmul
  -- the orbit powers are exactly those exponentials
  intro hcon
  refine hexp (familyDifferentiallyAlgebraicOn_congr_of_isOpen hdiscOpen ?_ hcon)
  intro j w hw
  have hw1 : ‖w‖ < 1 := by
    rw [openDisc, Metric.mem_ball, dist_zero_right] at hw
    exact hw
  have hcay : cayleyToUpper (parabolicAut (t j) w) = cayleyToUpper w + (t j : ℂ) :=
    cayleyToUpper_parabolicAut hw1
  rw [outerOrbitMap, hcay, herglotzSigma, ← Complex.exp_nat_mul]
  congr 1
  congr 1
  ring


/-- **The Stieltjes case.**  For the Cauchy transform of a nonzero finite measure on the line, the
parabolic orbit powers of its outer map inherit differential independence from the translates. -/
theorem not_familyDifferentiallyAlgebraicOn_parabolicOrbitPow_cauchy {r : ℕ} (t : Fin r → ℝ)
    (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hIndep : ¬ FamilyDifferentiallyAlgebraicOn
      (fun j z => cauchyTransform ν (z + (t j : ℂ))) {z : ℂ | 0 < z.im})
    {N : ℕ} (hN : N ≠ 0) :
    ¬ FamilyDifferentiallyAlgebraicOn
      (fun j w => (outerOrbitMap (cauchyTransform ν) (parabolicAut (t j) w)) ^ N) openDisc := by
  refine not_familyDifferentiallyAlgebraicOn_parabolicOrbitPow t
    (analyticOnNhd_cauchyTransform ν isOpen_upperHalf (fun z hz => ne_of_gt hz))
    (fun z hz => im_cauchyTransform_pos_of_ne_zero ν hν hz) hIndep hN

end

end GaloisForLFunctions.HTGeometry
