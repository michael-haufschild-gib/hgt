import GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlgebraicDilationGermIndependence

/-! Physical vertical-line jets of positive algebraic zeta dilations.
Analytic continuation transports rotated-germ independence; absolute convergence
provides the almost periodicity used to separate physical Gamma coefficients. -/

open Complex Filter Set Topology
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Classical Differential UpperEndDifferentialInstances UpperEndComplexTowerInstances
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlgebraicDilationPhysicalJets
open DilationGerms AlgebraicDilationGermIndependence
noncomputable section

/-- A line relation continues across its connected half-plane and gives a zero rotated germ. -/
theorem rotated_germ_zero_of_line {a sigma : ℝ} (has : a < sigma) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {z : ℂ | a < z.re})
    (hline : ∀ t : ℝ, f ((sigma : ℂ)+t*I) = 0) :
    Germ.coeRingHom upperEndFilter (fun z => f (-I*z)) = 0 := by
  let R : ℝ := (sigma-a)/2
  have hR : 0 < R := by dsimp only [R]; linarith only [has]
  have hsub : verticalStrip sigma R ⊆ {z : ℂ | a < z.re} := by
    intro z hz
    have hh := (abs_lt.mp (show |z.re-sigma| < R from hz)).1
    dsimp only [mem_setOf_eq,R] at *
    linarith only [hh,has]
  have hs : EqOn f (fun _ => 0) (verticalStrip sigma R) :=
    eqOn_of_eqOn_line hR (hf.differentiableOn.mono hsub)
      (differentiableOn_const _) hline
  have hc : (sigma : ℂ) ∈ verticalStrip sigma R := by
    change |(sigma : ℂ).re-sigma| < R
    simpa only [ofReal_re,sub_self,abs_zero] using hR
  have he : f =ᶠ[𝓝 (sigma : ℂ)] (fun _ => 0) :=
    Filter.eventuallyEq_of_mem ((isOpen_verticalStrip sigma R).mem_nhds hc) hs
  have hglobal : EqOn f (fun _ => 0) {z : ℂ | a < z.re} :=
    hf.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      (convex_halfSpace_re_gt a).isPreconnected has he
  rw [← map_zero (Germ.coeRingHom upperEndFilter)]
  apply Germ.coe_eq.mpr
  change ∀ᶠ z : ℂ in upperEndFilter, f (-I*z) = 0
  rw [upperEndFilter_basis.eventually_iff]
  refine ⟨a,trivial,fun z hz => hglobal ?_⟩
  simpa [mul_re,upperTail] using hz

private theorem analyticOnNhd_polynomial_family {J : Type*} (F : J → ℂ → ℂ)
    {U : Set ℂ} (hF : ∀ j, AnalyticOnNhd ℂ (F j) U) (P : MvPolynomial J ℂ) :
    AnalyticOnNhd ℂ (fun z => MvPolynomial.eval (fun j => F j z) P) U := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp only [MvPolynomial.eval_C]
      exact analyticOnNhd_const
  | add P Q hP hQ =>
      simp only [MvPolynomial.eval_add]
      exact hP.add hQ
  | mul_X P j hP =>
      simp only [MvPolynomial.eval_mul,MvPolynomial.eval_X]
      exact hP.mul (hF j)

/-- Rotated-germ independence restricts to every line inside a common analytic half-plane. -/
theorem algebraicIndependent_line_of_rotated {J : Type*} {a sigma : ℝ} (has : a < sigma)
    (F : J → ℂ → ℂ) (Psi : J → upperEndAnalyticSubring)
    (hF : ∀ j, AnalyticOnNhd ℂ (F j) {z : ℂ | a < z.re})
    (hPsi : ∀ j, upperEndAnalyticSubring.subtype (Psi j) =
      Germ.coeRingHom upperEndFilter (fun z => F j (-I*z)))
    (hai : AlgebraicIndependent ℂ
      (fun j => algebraMap upperEndAnalyticSubring upperEndMeroField (Psi j))) :
    AlgebraicIndependent ℂ (fun j (t : ℝ) => F j ((sigma : ℂ)+t*I)) := by
  rw [algebraicIndependent_iff]
  intro P hP
  have hline : ∀ t : ℝ, MvPolynomial.eval (fun j => F j ((sigma : ℂ)+t*I)) P = 0 := by
    intro t
    have hp : ∀ Q : MvPolynomial J ℂ,
        (MvPolynomial.aeval (fun j (t : ℝ) => F j ((sigma : ℂ)+t*I)) Q) t =
          MvPolynomial.eval (fun j => F j ((sigma : ℂ)+t*I)) Q := by
      intro Q
      induction Q using MvPolynomial.induction_on with
      | C c => simp
      | add Q R hQ hR => simp [hQ,hR]
      | mul_X Q j hQ => simp [hQ]
    rw [← hp P,hP]
    rfl
  have hzero := rotated_germ_zero_of_line has (analyticOnNhd_polynomial_family F hF P) hline
  have ha : MvPolynomial.eval₂ complexAnalytic Psi P = 0 := by
    apply Subtype.ext
    rw [show ((MvPolynomial.eval₂ complexAnalytic Psi P : upperEndAnalyticSubring) :
        Germ upperEndFilter ℂ) = Germ.coeRingHom upperEndFilter
          (fun z => MvPolynomial.eval (fun j => F j (-I*z)) P) from
      polynomial_analytic_repr Psi (fun j z => F j (-I*z)) hPsi P]
    exact hzero
  apply hai.eq_zero_of_aeval_eq_zero
  have hm := congrArg (algebraMap upperEndAnalyticSubring upperEndMeroField) ha
  rw [map_zero,MvPolynomial.hom_eval₂] at hm
  exact hm

/-- Undoing the rotation of a physical jet requires the inverse chain factor. -/
def rotatedPhysicalJet (r : ℝ) (hr : 0 < r) (k : ℕ) : upperEndAnalyticSubring :=
  complexAnalytic (((-I)^k)⁻¹) * upperEndAnalyticDeriv^[k] (rotatedZetaAnalytic r hr)

theorem rotatedPhysicalJet_repr (r : ℝ) (hr : 0 < r) (k : ℕ) :
    upperEndAnalyticSubring.subtype (rotatedPhysicalJet r hr k) =
      Germ.coeRingHom upperEndFilter (fun z => iteratedDeriv k (dilate r) (-I*z)) := by
  have hh : upperEndAnalyticSubring.subtype
      (upperEndAnalyticDeriv^[k] (rotatedZetaAnalytic r hr)) =
      Germ.coeRingHom upperEndFilter (iteratedDeriv k (fun z => dilate r (-I*z))) :=
    upperEndAnalyticDeriv_iterate_repr k (rotatedZetaAnalytic r hr)
      (fun z => dilate r (-I*z)) rfl
  rw [rotatedPhysicalJet,map_mul,complexAnalytic_repr,hh,← map_mul]
  congr 1
  ext z
  dsimp only [Pi.mul_apply]
  rw [iteratedDeriv_comp_mul_left_uncond]
  rw [← mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr I_ne_zero)),one_mul]

theorem rotatedPhysicalJet_map (r : ℝ) (hr : 0 < r) (k : ℕ) :
    algebraMap upperEndAnalyticSubring upperEndMeroField (rotatedPhysicalJet r hr k) =
      algebraMap ℂ upperEndMeroField (((-I)^k)⁻¹) *
        differentialJet k (rotatedZetaMero r hr) := by
  rw [rotatedPhysicalJet,map_mul,rotatedZetaMero,
    GaloisForLFunctions.HTGeometry.differentialJet_algebraMap]
  rfl

/-- All physical jets of a finite positive algebraic dilation packet are independent
on every line lying strictly inside a common convergence half-plane. -/
theorem dilate_jets_line_algebraicIndependent {ι : Type*} [Fintype ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (ha : ∀ i, IsAlgebraic ℤ (r i))
    (hinj : Function.Injective r) {a sigma : ℝ} (has : a < sigma)
    (hra : ∀ i, 1 < r i*a) :
    AlgebraicIndependent ℂ (fun ik : ι × ℕ => fun t : ℝ =>
      iteratedDeriv ik.2 (dilate (r ik.1)) ((sigma : ℂ)+t*I)) := by
  have hai : AlgebraicIndependent ℂ (fun ik : ι × ℕ =>
      differentialJet ik.2 (rotatedZetaMero (r ik.1) (hr ik.1))) :=
    rotatedZetaMero_differentialIndependent r hr ha hinj
  have hscale := AlgebraicIndependent.const_mul_coordinates hai
    (fun ik : ι × ℕ => (((-I)^ik.2)⁻¹))
    (fun ik => inv_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr I_ne_zero)))
  refine algebraicIndependent_line_of_rotated has
    (fun ik : ι × ℕ => iteratedDeriv ik.2 (dilate (r ik.1)))
    (fun ik => rotatedPhysicalJet (r ik.1) (hr ik.1) ik.2)
    ?_ (fun ik => rotatedPhysicalJet_repr (r ik.1) (hr ik.1) ik.2) ?_
  · intro ik
    apply analyticOnNhd_iteratedDeriv
    intro z hz
    apply dilate_analytic_right (r ik.1)
    exact lt_trans (hra ik.1) (mul_lt_mul_of_pos_left hz (hr ik.1))
  · simpa only [rotatedPhysicalJet_map] using hscale

/-- Positive real dilation preserves almost periodicity of every actual zeta jet. -/
theorem dilate_jet_line (r : ℝ) (hr : 0 < r) (sigma : ℝ)
    (hs : 2 ≤ r*sigma) (k : ℕ) :
    Continuous (fun t : ℝ => iteratedDeriv k (dilate r) ((sigma : ℂ)+t*I)) ∧
    _root_.HTGeometry.IsBohrAlmostPeriodic
      (fun t : ℝ => iteratedDeriv k (dilate r) ((sigma : ℂ)+t*I)) := by
  have hs1 : 1 < r*sigma := lt_of_lt_of_le (by norm_num) hs
  have hR : (1 : ℝ) ≤ r*sigma-1 := by linarith only [hs]
  have hj := isStripAlmostPeriodic_iteratedDeriv
    (differentiableOn_zeta_verticalStrip hs1 hR) (isStripAlmostPeriodic_zeta hR) k
  have hjc := continuous_line_restriction (by norm_num : (0 : ℝ) < 1) hj.1
  have hja := isBohrAlmostPeriodic_line (by norm_num : (0 : ℝ) < 1) hj.2
  have hfun : (fun t : ℝ => iteratedDeriv k (dilate r) ((sigma : ℂ)+t*I)) =
      fun t : ℝ => (r : ℂ)^k * iteratedDeriv k riemannZeta
        (((r*sigma : ℝ) : ℂ)+((r*t : ℝ) : ℂ)*I) := by
    funext t
    change iteratedDeriv k (fun z => riemannZeta ((r : ℂ)*z)) _ = _
    rw [iteratedDeriv_comp_mul_left_uncond]
    congr 1
    congr 1
    push_cast
    ring
  rw [hfun]
  exact ⟨continuous_const.mul (hjc.comp (continuous_const.mul continuous_id)),
    isBohrAlmostPeriodic_const_mul _ (GammaJoint.bohr_comp_pos_mul hja hr)⟩

#print axioms rotated_germ_zero_of_line
#print axioms algebraicIndependent_line_of_rotated
#print axioms rotatedPhysicalJet_repr
#print axioms rotatedPhysicalJet_map
#print axioms dilate_jets_line_algebraicIndependent
#print axioms dilate_jet_line
end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlgebraicDilationPhysicalJets
