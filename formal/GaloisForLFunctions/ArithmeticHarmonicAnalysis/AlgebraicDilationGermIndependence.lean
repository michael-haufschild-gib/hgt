import GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlgebraicDilationJetIndependence
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.PositiveDilationAnalyticGerms
import GaloisForLFunctions.HTGeometry.DifferentialIndependenceHasse

/-! Algebraic independence of actual logarithmic jets passes from convergence lines
to rotated germs. The literal logarithmic differential equation then gives
differential independence of positive algebraic zeta dilations. -/

open Complex Filter Set Topology
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Classical Differential UpperEndDifferentialInstances UpperEndComplexTowerInstances
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlgebraicDilationGermIndependence
open DilatedVonMangoldt DilationGerms AlgebraicDilationJetIndependence
noncomputable section

/-- The analytic representative of the logarithmic derivative of rotated zeta. -/
def logCoordinate (r : ℝ) (hr : 0 < r) : upperEndAnalyticSubring :=
  complexAnalytic I * rotatedSourceAnalytic r hr

theorem logCoordinate_repr (r : ℝ) (hr : 0 < r) :
    upperEndAnalyticSubring.subtype (logCoordinate r hr) =
      Germ.coeRingHom upperEndFilter (fun z => I * source r (-I*z)) := by
  rw [logCoordinate,map_mul,complexAnalytic_repr]
  rfl

/-- Every logarithmic jet retains its exact nonzero rotation factor. -/
theorem logCoordinate_jet_repr (r : ℝ) (hr : 0 < r) (k : ℕ) :
    upperEndAnalyticSubring.subtype (upperEndAnalyticDeriv^[k] (logCoordinate r hr)) =
      Germ.coeRingHom upperEndFilter
        (fun z => (I * (-I)^k) * iteratedDeriv k (source r) (-I*z)) := by
  have hrepr : upperEndAnalyticSubring.subtype
      (upperEndAnalyticDeriv^[k] (logCoordinate r hr)) =
      Germ.coeRingHom upperEndFilter (iteratedDeriv k (fun z => I * source r (-I*z))) :=
    upperEndAnalyticDeriv_iterate_repr k (logCoordinate r hr)
      (fun z => I * source r (-I*z)) (logCoordinate_repr r hr)
  rw [hrepr]
  congr 1
  funext z
  rw [iteratedDeriv_const_mul_field]
  change I * iteratedDeriv k (fun w => source r (-I*w)) z = _
  rw [iteratedDeriv_comp_mul_left_uncond]
  ring

/-- Polynomial evaluation commutes with taking analytic representatives. -/
theorem polynomial_analytic_repr {J : Type*}
    (Psi : J → upperEndAnalyticSubring) (F : J → ℂ → ℂ)
    (hPsi : ∀ j, upperEndAnalyticSubring.subtype (Psi j) =
      Germ.coeRingHom upperEndFilter (F j)) (P : MvPolynomial J ℂ) :
    upperEndAnalyticSubring.subtype (MvPolynomial.eval₂ complexAnalytic Psi P) =
      Germ.coeRingHom upperEndFilter (fun z => MvPolynomial.eval (fun j => F j z) P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [MvPolynomial.eval₂_C,complexAnalytic_repr]
      congr 1
      ext z
      simp
  | add P Q hP hQ =>
      rw [MvPolynomial.eval₂_add,map_add,hP,hQ,← map_add]
      congr 1
      ext z
      simp
  | mul_X P j hP =>
      rw [MvPolynomial.eval₂_mul,MvPolynomial.eval₂_X,map_mul,hP,hPsi j,← map_mul]
      congr 1
      ext z
      simp

/-- A finite rotated logarithmic jet packet is algebraically independent in the actual field. -/
theorem logCoordinate_jets_algebraicIndependent {ι : Type*} [Fintype ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (ha : ∀ i, IsAlgebraic ℤ (r i))
    (hinj : Function.Injective r) (J : ℕ) :
    AlgebraicIndependent ℂ (fun ik : ι × Fin (J+1) =>
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (upperEndAnalyticDeriv^[ik.2.val] (logCoordinate (r ik.1) (hr ik.1)))) := by
  rw [algebraicIndependent_iff]
  intro P hP
  let Psi : (ι × Fin (J+1)) → upperEndAnalyticSubring := fun ik =>
    upperEndAnalyticDeriv^[ik.2.val] (logCoordinate (r ik.1) (hr ik.1))
  let F : (ι × Fin (J+1)) → ℂ → ℂ := fun ik z =>
    (I * (-I)^ik.2.val) * iteratedDeriv ik.2.val (source (r ik.1)) (-I*z)
  have hPsi : ∀ ik, upperEndAnalyticSubring.subtype (Psi ik) =
      Germ.coeRingHom upperEndFilter (F ik) := fun ik =>
    logCoordinate_jet_repr (r ik.1) (hr ik.1) ik.2.val
  have hp : MvPolynomial.eval₂ complexAnalytic Psi P = 0 := by
    apply IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField
    rw [map_zero,MvPolynomial.hom_eval₂]
    exact hP
  have hg := congrArg upperEndAnalyticSubring.subtype hp
  rw [polynomial_analytic_repr Psi F hPsi P,map_zero,
    ← map_zero (Germ.coeRingHom upperEndFilter)] at hg
  have he : ∀ᶠ z in upperEndFilter, MvPolynomial.eval (fun ik => F ik z) P = 0 :=
    Germ.coe_eq.mp hg
  obtain ⟨H,_,hH⟩ := upperEndFilter_basis.eventually_iff.mp he
  obtain ⟨sigma,hHs,_,hs⟩ := exists_common_line r hr H
  have hscale := AlgebraicIndependent.const_mul_coordinates
    (source_jets_line_algebraicIndependent r hr ha hinj J sigma hs)
    (fun ik : ι × Fin (J+1) => I * (-I)^ik.2.val)
    (fun ik => mul_ne_zero I_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr I_ne_zero)))
  apply hscale.eq_zero_of_aeval_eq_zero
  ext t
  have hz : I*((sigma : ℂ)+(t : ℂ)*I) ∈ upperTail H := by
    simpa [upperTail,mul_im] using hHs
  have hrot : -I*(I*((sigma : ℂ)+(t : ℂ)*I)) = (sigma : ℂ)+(t : ℂ)*I := by
    rw [← mul_assoc,neg_mul,I_mul_I,neg_neg,one_mul]
  have hline := hH hz
  dsimp only [F] at hline
  rw [hrot] at hline
  have heval : ∀ Q : MvPolynomial (ι × Fin (J+1)) ℂ,
      (MvPolynomial.aeval (fun ik : ι × Fin (J+1) =>
        algebraMap ℂ (ℝ → ℂ) (I * (-I)^ik.2.val) *
          (fun t : ℝ => iteratedDeriv ik.2.val (source (r ik.1))
            ((sigma : ℂ)+(t : ℂ)*I))) Q) t =
      MvPolynomial.eval (fun ik => (I * (-I)^ik.2.val) *
        iteratedDeriv ik.2.val (source (r ik.1)) ((sigma : ℂ)+(t : ℂ)*I)) Q := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C c => simp
    | add Q R hQ hR =>
        rw [map_add,MvPolynomial.eval_add]
        exact congrArg₂ (fun x y : ℂ => x+y) hQ hR
    | mul_X Q i hQ =>
        rw [map_mul,MvPolynomial.aeval_X,MvPolynomial.eval_mul,MvPolynomial.eval_X]
        exact congrArg (fun x : ℂ => x * ((I * (-I)^i.2.val) *
          iteratedDeriv i.2.val (source (r i.1)) ((sigma : ℂ)+(t : ℂ)*I))) hQ
  rw [heval]
  exact hline

/-- A finite family of distinct positive algebraic zeta dilations is differentially
independent over the constants as actual rotated meromorphic germs. -/
theorem rotatedZetaMero_differentialIndependent {ι : Type*} [Fintype ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (ha : ∀ i, IsAlgebraic ℤ (r i))
    (hinj : Function.Injective r) :
    DifferentialIndependent ℂ (fun i => rotatedZetaMero (r i) (hr i)) := by
  apply (differentialIndependent_deriv_div_self_iff
    (F := ℂ) (fun i => rotatedZetaMero (r i) (hr i))).mpr
  have hlog : (fun i => (rotatedZetaMero (r i) (hr i))′ /
      rotatedZetaMero (r i) (hr i)) =
      fun i => algebraMap upperEndAnalyticSubring upperEndMeroField
        (logCoordinate (r i) (hr i)) := by
    funext i
    rw [rotatedZetaMero_logDeriv,logCoordinate,map_mul]
    rfl
  rw [hlog]
  apply algebraicIndependent_prod_nat_of_all_fin
  intro J
  simpa only [GaloisForLFunctions.HTGeometry.differentialJet_algebraMap] using
    logCoordinate_jets_algebraicIndependent r hr ha hinj J

#print axioms logCoordinate_jet_repr
#print axioms polynomial_analytic_repr
#print axioms logCoordinate_jets_algebraicIndependent
#print axioms rotatedZetaMero_differentialIndependent
end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlgebraicDilationGermIndependence
