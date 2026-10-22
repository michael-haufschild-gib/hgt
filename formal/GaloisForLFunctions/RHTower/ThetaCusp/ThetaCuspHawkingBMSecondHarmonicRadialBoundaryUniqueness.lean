import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicContinuousGreenAction

/-!
# Uniqueness and boundary projection of the reduced BM Green response

The forced reduced equation and the regular-horizon/normalizable-AdS phase conditions determine
the response throughout the radial interior. Its normalizable boundary coefficient is the exact
regular-mode source integral. This concerns the reduced second-harmonic boundary problem;
identifying the complete Einstein source, causal time support, and final left-QNM action is separate.
-/

open Complex Real Set Filter Topology

namespace RHTower
noncomputable section

/-- Actual twice differentiable forced BM equation with the two prescribed boundary phase lines.
The anchors lie in the radial interior; no limiting boundary condition is hidden in this predicate. -/
structure d4BMPlusPlusRadialBoundaryProblem
    (n : ℕ) (chi : ℂ) (f : ℝ → ℂ) (a b : ℝ) (y dy ddy : ℝ → ℂ) : Prop where
  first : ∀ z ∈ Ioo (0 : ℝ) 1, HasDerivAt y (dy z) z
  second : ∀ z ∈ Ioo (0 : ℝ) 1, HasDerivAt dy (ddy z) z
  equation : ∀ z ∈ Ioo (0 : ℝ) 1,
    d4BMPlusPlusHypergeometricJet n chi z (y z) (dy z) (ddy z) = f z
  horizon : d4BMPlusPlusNormalizedWronskian n chi
    (fun t => d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ))
    (fun t => d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (t : ℂ)) y dy a = 0
  ads : d4BMPlusPlusNormalizedWronskian n chi y dy
    (d4BMPlusPlusAdSNormalizableSolution n chi)
    (d4BMPlusPlusAdSNormalizableSolutionDerivative n chi) b = 0

/-- A homogeneous response satisfying both boundary lines has zero phase everywhere inside. -/
theorem d4BMPlusPlusRadialBoundaryProblem_homogeneous_eq_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    {y dy ddy : ℝ → ℂ}
    (h : d4BMPlusPlusRadialBoundaryProblem n chi (fun _ => 0) a b y dy ddy)
    {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) : y z = 0 ∧ dy z = 0 := by
  let R := fun t : ℝ => d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ)
  let Rd := fun t : ℝ => d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (t : ℂ)
  let Rdd := fun t : ℝ =>
    d4BMPlusPlusRegularHypergeometricSolutionSecondDerivative n chi (t : ℂ)
  let V := d4BMPlusPlusAdSNormalizableSolution n chi
  let Vd := d4BMPlusPlusAdSNormalizableSolutionDerivative n chi
  let Vdd := d4BMPlusPlusAdSNormalizableSolutionSecondDerivative n chi
  have hR : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt R (Rd t) t := by
    intro t ht
    exact (hasDerivAt_d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ)
      hchi (enorm_ofReal_lt_one ht.1 ht.2)).comp_ofReal
  have hRd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Rd (Rdd t) t := by
    intro t ht
    exact (hasDerivAt_d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (t : ℂ)
      hchi (enorm_ofReal_lt_one ht.1 ht.2)).comp_ofReal
  have hV : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt V (Vd t) t :=
    fun t ht => hasDerivAt_d4BMPlusPlusAdSNormalizableSolution n chi hchi ht.1 ht.2
  have hVd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Vd (Vdd t) t :=
    fun t ht => hasDerivAt_d4BMPlusPlusAdSNormalizableSolutionDerivative n chi hchi ht.1 ht.2
  have hRjet : ∀ t ∈ Ioo (0 : ℝ) 1,
      d4BMPlusPlusHypergeometricJet n chi t (R t) (Rd t) (Rdd t) = 0 :=
    fun t ht => d4BMPlusPlusRegularHypergeometricSolution_real_jet_eq_zero n chi hchi ht.1 ht.2
  have hVjet : ∀ t ∈ Ioo (0 : ℝ) 1,
      d4BMPlusPlusHypergeometricJet n chi t (V t) (Vd t) (Vdd t) = 0 :=
    fun t ht => d4BMPlusPlusAdSNormalizableSolution_jet_eq_zero n chi hchi ht.1 ht.2
  have hRy : d4BMPlusPlusNormalizedWronskian n chi R Rd y dy z = 0 :=
    (d4BMPlusPlusNormalizedWronskian_eq_of_solutionJets n chi R Rd Rdd y dy ddy
      hR hRd h.first h.second hRjet h.equation hz ha).trans h.horizon
  have hyV : d4BMPlusPlusNormalizedWronskian n chi y dy V Vd z = 0 :=
    (d4BMPlusPlusNormalizedWronskian_eq_of_solutionJets n chi y dy ddy V Vd Vdd
      h.first h.second hV hVd h.equation hVjet hz hb).trans h.ads
  have hD : d4BMPlusPlusNormalizedWronskian n chi R Rd V Vd z ≠ 0 :=
    d4BMPlusPlusRegularAdSNormalizableGreenDenominator_ne_zero n chi hchi hz.1 hz.2
  have hc := d4BMPlusPlusNormalizedWronskian_cramer_phase n chi y dy R Rd V Vd z hD
  simpa only [hRy, hyV, zero_div, zero_mul, add_zero] using hc

/-- Any two solutions of the same forced boundary problem have identical interior phase. -/
theorem d4BMPlusPlusRadialBoundaryProblem_unique
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) {f : ℝ → ℂ} {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    {y dy ddy v dv ddv : ℝ → ℂ}
    (hy : d4BMPlusPlusRadialBoundaryProblem n chi f a b y dy ddy)
    (hv : d4BMPlusPlusRadialBoundaryProblem n chi f a b v dv ddv)
    {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) : y z = v z ∧ dy z = dv z := by
  have hd : d4BMPlusPlusRadialBoundaryProblem n chi (fun _ => 0) a b
      (fun t => y t - v t) (fun t => dy t - dv t) (fun t => ddy t - ddv t) := by
    refine ⟨fun t ht => (hy.first t ht).sub (hv.first t ht),
      fun t ht => (hy.second t ht).sub (hv.second t ht), ?_, ?_, ?_⟩
    · intro t ht
      have h1 := hy.equation t ht
      have h2 := hv.equation t ht
      dsimp only [d4BMPlusPlusHypergeometricJet] at h1 h2 ⊢
      linear_combination h1 - h2
    · have h1 := hy.horizon
      have h2 := hv.horizon
      dsimp only [d4BMPlusPlusNormalizedWronskian] at h1 h2 ⊢
      linear_combination h1 - h2
    · have h1 := hy.ads
      have h2 := hv.ads
      dsimp only [d4BMPlusPlusNormalizedWronskian] at h1 h2 ⊢
      linear_combination h1 - h2
  have heq := d4BMPlusPlusRadialBoundaryProblem_homogeneous_eq_zero n chi hchi ha hb hd hz
  exact ⟨sub_eq_zero.mp heq.1, sub_eq_zero.mp heq.2⟩

/-- The constructed integral action satisfies the actual differential and boundary conditions. -/
theorem d4BMPlusPlusContinuousGreenResponse_boundaryProblem
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ioo 0 1)) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    d4BMPlusPlusRadialBoundaryProblem n chi f a b
      (d4BMPlusPlusContinuousGreenResponse n chi f a b)
      (d4BMPlusPlusContinuousGreenResponseDerivative n chi f a b)
      (d4BMPlusPlusContinuousGreenResponseSecondDerivative n chi f a b) := by
  refine ⟨fun z hz => hasDerivAt_d4BMPlusPlusContinuousGreenResponse n chi hchi hf ha hb hz,
    fun z hz => hasDerivAt_d4BMPlusPlusContinuousGreenResponseDerivative n chi hchi hf ha hb hz,
    fun z hz => d4BMPlusPlusContinuousGreenResponse_forcedJet n chi hchi f a b hz, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := d4BMPlusPlusContinuousGreenResponse_leftBoundaryJet n chi f a b
    dsimp only [d4BMPlusPlusNormalizedWronskian]
    rw [h1, h2]
    ring
  · obtain ⟨h1, h2⟩ := d4BMPlusPlusContinuousGreenResponse_rightBoundaryJet n chi f a b
    dsimp only [d4BMPlusPlusNormalizedWronskian]
    rw [h1, h2]
    ring

/-- Every continuous-source solution of the boundary problem equals the constructed Green action. -/
theorem d4BMPlusPlusRadialBoundaryProblem_eq_green
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ioo 0 1)) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    {y dy ddy : ℝ → ℂ} (h : d4BMPlusPlusRadialBoundaryProblem n chi f a b y dy ddy)
    {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    y z = d4BMPlusPlusContinuousGreenResponse n chi f a b z ∧
      dy z = d4BMPlusPlusContinuousGreenResponseDerivative n chi f a b z :=
  d4BMPlusPlusRadialBoundaryProblem_unique n chi hchi ha hb h
    (d4BMPlusPlusContinuousGreenResponse_boundaryProblem n chi hchi hf ha hb) hz

/-- Normalizable phase coefficient extracted by the regular testing solution and fixed Wronskian.
It remains defined when the normalizable solution's value vanishes at the extraction point. -/
def d4BMPlusPlusRadialNormalizableCoefficient
    (n : ℕ) (chi : ℂ) (y dy : ℝ → ℂ) (z : ℝ) : ℂ :=
  d4BMPlusPlusNormalizedWronskian n chi
    (fun t => d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ))
    (fun t => d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (t : ℂ)) y dy z /
      d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi (1 / 2)

/-- Exact local coefficient of the constructed action is its accumulated regular-mode moment. -/
theorem d4BMPlusPlusContinuousGreenResponse_normalizableCoefficient
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) (f : ℝ → ℂ) (a b : ℝ)
    {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    d4BMPlusPlusRadialNormalizableCoefficient n chi
      (d4BMPlusPlusContinuousGreenResponse n chi f a b)
      (d4BMPlusPlusContinuousGreenResponseDerivative n chi f a b) z =
    d4BMPlusPlusContinuousGreenMoment n chi
      (fun t => d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ)) f a z := by
  have hmid : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hD := d4BMPlusPlusRegularAdSNormalizableGreenDenominator_ne_zero
    n chi hchi hmid.1 hmid.2
  have hW : d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi z =
      d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi (1 / 2) := by
    rw [d4BMPlusPlusRegularAdSNormalizableGreenDenominator_eq_neg_half n chi hchi hz.1 hz.2,
      d4BMPlusPlusRegularAdSNormalizableGreenDenominator_eq_neg_half n chi hchi hmid.1 hmid.2]
  rw [d4BMPlusPlusRadialNormalizableCoefficient]
  have hnum : d4BMPlusPlusNormalizedWronskian n chi
      (fun t => d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ))
      (fun t => d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (t : ℂ))
      (d4BMPlusPlusContinuousGreenResponse n chi f a b)
      (d4BMPlusPlusContinuousGreenResponseDerivative n chi f a b) z =
    d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi z *
      d4BMPlusPlusContinuousGreenMoment n chi
        (fun t => d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ)) f a z := by
    dsimp only [d4BMPlusPlusNormalizedWronskian,
      d4BMPlusPlusRegularAdSNormalizableGreenDenominator,
      d4BMPlusPlusContinuousGreenResponse, d4BMPlusPlusContinuousGreenResponseDerivative]
    ring
  rw [hnum, hW, mul_div_cancel_left₀ _ hD]

/-- Every solution has the boundary phase fixed by the same regular-mode source moment. -/
theorem d4BMPlusPlusRadialBoundaryProblem_rightBoundaryJet
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ioo 0 1)) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    {y dy ddy : ℝ → ℂ} (h : d4BMPlusPlusRadialBoundaryProblem n chi f a b y dy ddy) :
    y b = d4BMPlusPlusAdSNormalizableSolution n chi b *
        d4BMPlusPlusContinuousGreenMoment n chi
          (fun t => d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ)) f a b ∧
      dy b = d4BMPlusPlusAdSNormalizableSolutionDerivative n chi b *
        d4BMPlusPlusContinuousGreenMoment n chi
          (fun t => d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ)) f a b := by
  have heq := d4BMPlusPlusRadialBoundaryProblem_eq_green n chi hchi hf ha hb h hb
  have hg := d4BMPlusPlusContinuousGreenResponse_rightBoundaryJet n chi f a b
  exact ⟨heq.1.trans hg.1, heq.2.trans hg.2⟩

/-- The differential equation and boundary conditions derive the projection of any response. -/
theorem d4BMPlusPlusRadialBoundaryProblem_normalizableCoefficient
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ioo 0 1)) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    {y dy ddy : ℝ → ℂ} (h : d4BMPlusPlusRadialBoundaryProblem n chi f a b y dy ddy) :
    d4BMPlusPlusRadialNormalizableCoefficient n chi y dy b =
      d4BMPlusPlusContinuousGreenMoment n chi
        (fun t => d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ)) f a b := by
  have heq := d4BMPlusPlusRadialBoundaryProblem_eq_green n chi hchi hf ha hb h hb
  have hg := d4BMPlusPlusContinuousGreenResponse_normalizableCoefficient n chi hchi f a b hb
  dsimp only [d4BMPlusPlusRadialNormalizableCoefficient, d4BMPlusPlusNormalizedWronskian] at hg ⊢
  rw [heq.1, heq.2]
  exact hg

/-- Boundary phase extinction is exactly cancellation of the derived source moment. -/
theorem d4BMPlusPlusRadialBoundaryProblem_boundary_eq_zero_iff
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ioo 0 1)) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    {y dy ddy : ℝ → ℂ} (h : d4BMPlusPlusRadialBoundaryProblem n chi f a b y dy ddy) :
    (y b = 0 ∧ dy b = 0) ↔
      d4BMPlusPlusContinuousGreenMoment n chi
        (fun t => d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ)) f a b = 0 := by
  constructor
  · rintro ⟨hy, hdy⟩
    rw [← d4BMPlusPlusRadialBoundaryProblem_normalizableCoefficient n chi hchi hf ha hb h]
    simp [d4BMPlusPlusRadialNormalizableCoefficient, d4BMPlusPlusNormalizedWronskian, hy, hdy]
  · intro hm
    have hj := d4BMPlusPlusRadialBoundaryProblem_rightBoundaryJet n chi hchi hf ha hb h
    simpa only [hm, mul_zero] using hj

/-- On every actual Xi fibre, existence and interior phase uniqueness require no supplied
Wronskian nondegeneracy or inverse map. Functions outside the radial interior are unconstrained. -/
theorem d4BMXiPlusPlusRadialBoundaryProblem_exists_unique_phase
    (n : ℕ) (q : XiZeroCopy) {f : ℝ → ℂ} (hf : ContinuousOn f (Ioo 0 1)) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    let chi := d4BMXiMixedHorizonAngularMomentum q
    ∃ y dy ddy : ℝ → ℂ, d4BMPlusPlusRadialBoundaryProblem n chi f a b y dy ddy ∧
      ∀ v dv ddv : ℝ → ℂ, d4BMPlusPlusRadialBoundaryProblem n chi f a b v dv ddv →
        EqOn y v (Ioo 0 1) ∧ EqOn dy dv (Ioo 0 1) := by
  dsimp only
  let chi := d4BMXiMixedHorizonAngularMomentum q
  have hchi : chi.re ≠ 0 := d4BMXiMixedHorizonAngularMomentum_re_ne_zero q
  have hg := d4BMPlusPlusContinuousGreenResponse_boundaryProblem n chi hchi hf ha hb
  refine ⟨_, _, _, hg, ?_⟩
  intro v dv ddv hv
  exact ⟨fun z hz => (d4BMPlusPlusRadialBoundaryProblem_unique n chi hchi ha hb hg hv hz).1,
    fun z hz => (d4BMPlusPlusRadialBoundaryProblem_unique n chi hchi ha hb hg hv hz).2⟩

end
end RHTower
