import GaloisForLFunctions.RepresentationLifting.Spinor.TheRealHomogeneousPolynomialObstructionInThePlane
import GaloisForLFunctions.RepresentationLifting.Spinor.TheNonlinearInteractionOfNullHarmonics
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Rigidity of the Cartesian planar polynomial p-Laplacian

Restrict a homogeneous form to the line (x,y)=(t+1,−i(t−1)).
Its chart derivative is the difference of the two partials with
multiplier i. Euler's identity gives the complementary sum. Together
these recover the full Cartesian second-order symbol. The chart is
injective in each degree, and real coefficients become conjugate
symmetry under reversal.
-/

noncomputable section
open Complex
open scoped ComplexConjugate
namespace GaloisForLFunctions.RepresentationLifting.Spinor

private abbrev Plane := MvPolynomial (Fin 2) ℂ

private def axes : Fin 2 → ℂ[X] :=
  ![Polynomial.X+1,Polynomial.C (-I)*(Polynomial.X-1)]

private def chart : Plane →ₐ[ℂ] ℂ[X] := MvPolynomial.aeval axes

private lemma chart_C (z : ℂ) : chart (MvPolynomial.C z)=Polynomial.C z := MvPolynomial.aeval_C _
private lemma chart_X (j : Fin 2) : chart (MvPolynomial.X j)=axes j := MvPolynomial.aeval_X _

private theorem chart_derivative (Q : Plane) :
    (chart Q).derivative=chart (MvPolynomial.pderiv 0 Q)-Polynomial.C I*chart (MvPolynomial.pderiv 1 Q) := by
  induction Q using MvPolynomial.induction_on with
  | C z => simp only [chart_C,Polynomial.derivative_C,MvPolynomial.pderiv_C,map_zero,mul_zero,sub_zero]
  | add f g hf hg =>
    simp only [map_add,hf,hg]
    ring
  | mul_X f j hf =>
    simp only [map_mul,Polynomial.derivative_mul,MvPolynomial.pderiv_mul,map_add,chart_X,
      MvPolynomial.pderiv_X,Pi.single_apply,apply_ite chart,map_one,map_zero,hf]
    fin_cases j <;> simp [axes,Polynomial.derivative_C_mul] <;> ring

private theorem chart_second_derivative {n : ℕ} {Q : Plane} (hn : Q.IsHomogeneous n) :
    secondPolarDerivative n (chart Q)=
      chart (MvPolynomial.pderiv 0 Q)+Polynomial.C I*chart (MvPolynomial.pderiv 1 Q) := by
  have h := congrArg chart hn.sum_X_mul_pderiv
  simp only [Fin.sum_univ_two,map_add,map_mul,map_nsmul,nsmul_eq_mul,chart_X] at h
  simp only [axes,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] at h
  rw [secondPolarDerivative,chart_derivative]
  rw [map_natCast] at *
  simp only [map_neg] at h
  linear_combination -h

private theorem mixed_plane_partials (Q : Plane) :
    MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 Q)=MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 Q) := by
  ext m
  simp only [MvPolynomial.coeff_pderiv,Finsupp.add_apply,Finsupp.single_eq_of_ne (by decide : (0:Fin 2)≠1),
    Finsupp.single_eq_of_ne (by decide : (1:Fin 2)≠0),add_zero]
  rw [show m+Finsupp.single 0 1+Finsupp.single 1 1=m+Finsupp.single 1 1+Finsupp.single 0 1 by ac_rfl]
  ring

private theorem symbol_coordinate_identity {R : Type*} [CommRing R]
    (p i a b h k l : R) (hi : i^2= -1) :
    2*p*(a-i*b)*(a+i*b)*(h+l)+(p-2)*((a-i*b)^2*(h+2*i*k-l)+(a+i*b)^2*(h-2*i*k-l))=
      4*((a^2+b^2)*(h+l)+(p-2)*(a^2*h+2*a*b*k+b^2*l)) := by
  linear_combination (-2*p*b^2*(h+l)+(p-2)*(2*b^2*(h-l)-8*a*b*k))*hi

/-- In this chart the polar symbol is four times the physical Cartesian
symbol, for every complex homogeneous form. -/
theorem cartesian_planar_symbol_in_chart {n : ℕ} (hn : 0<n) (p : ℂ) (Q : Plane)
    (hq : Q.IsHomogeneous n) : planarPolarSymbol p n (chart Q)=4*chart (clearedPLaplacian p Q) := by
  let i := Polynomial.C I
  have hi : i^2= -(1:ℂ[X]) := by simp only [i,←map_pow,Complex.I_sq,map_neg,map_one]
  let X := MvPolynomial.pderiv (R:=ℂ) (0:Fin 2)
  let Y := MvPolynomial.pderiv (R:=ℂ) (1:Fin 2)
  let a := chart (X Q)
  let b := chart (Y Q)
  let h := chart (X (X Q))
  let k := chart (X (Y Q))
  let l := chart (Y (Y Q))
  have hmix : chart (Y (X Q))=k := congrArg chart (mixed_plane_partials Q).symm
  have hA : (chart Q).derivative=a-i*b := chart_derivative Q
  have hB : secondPolarDerivative n (chart Q)=a+i*b := chart_second_derivative hq
  have ha : a.derivative=h-i*k := (chart_derivative _).trans (by rw [hmix])
  have hb : b.derivative=k-i*l := chart_derivative _
  have hd (c : ℂ) (f : ℂ[X]) : (Polynomial.C c*f).derivative=Polynomial.C c*f.derivative := Polynomial.derivative_C_mul ..
  have hA' : (chart Q).derivative.derivative=h-2*i*k-l := by
    rw [hA,Polynomial.derivative_sub,hd,ha,hb]
    linear_combination l*hi
  have hB' : (secondPolarDerivative n (chart Q)).derivative=h+l := by
    rw [hB,Polynomial.derivative_add,hd,ha,hb]
    linear_combination -l*hi
  have hnat : ((n-1:ℕ):ℂ)=(n:ℂ)-1 := by rw [Nat.cast_sub hn,Nat.cast_one]
  have hwA := chart_second_derivative (hq.pderiv (i:=0))
  have hwB := chart_second_derivative (hq.pderiv (i:=1))
  change secondPolarDerivative (n-1) a=h+i*chart (Y (X Q)) at hwA
  change secondPolarDerivative (n-1) b=k+i*l at hwB
  rw [hmix] at hwA
  have hD : Polynomial.C ((n:ℂ)-1)*secondPolarDerivative n (chart Q)-
      Polynomial.X*(secondPolarDerivative n (chart Q)).derivative=h+2*i*k-l := by
    rw [hB',hB]
    simp only [secondPolarDerivative,hnat,ha,hb] at hwA hwB
    linear_combination hwA+i*hwB+l*hi-Polynomial.X*l*hi
  simp only [planarPolarSymbol,hD,hB',hA',hA,hB,clearedPLaplacian,euclideanPolynomialLaplacian,
    infinityPolynomial,Fin.sum_univ_two,map_add,map_mul,map_pow,chart_C]
  change Polynomial.C (2*p)*(a-i*b)*(a+i*b)*(h+l)+Polynomial.C (p-2)*((a-i*b)^2*(h+2*i*k-l)+
    (a+i*b)^2*(h-2*i*k-l))=4*((a^2+b^2)*(h+l)+Polynomial.C (p-2)*
    (a*a*h+a*b*k+(b*a*chart (Y (X Q))+b*b*l)))
  rw [hmix]
  simp only [map_mul,map_sub,map_ofNat]
  exact (symbol_coordinate_identity (Polynomial.C p) i a b h k l hi).trans (by ring)

private def polarAxes : Fin 2 → Plane :=
  ![MvPolynomial.X 0+MvPolynomial.X 1,MvPolynomial.C (-I)*(MvPolynomial.X 0-MvPolynomial.X 1)]

private def isotropicChange : Plane →ₐ[ℂ] Plane := MvPolynomial.aeval polarAxes

private theorem change_injective : Function.Injective isotropicChange := by
  let undo : Plane →ₐ[ℂ] Plane := MvPolynomial.aeval
    ![MvPolynomial.C (1/2:ℂ)*(MvPolynomial.X 0+MvPolynomial.C I*MvPolynomial.X 1),
      MvPolynomial.C (1/2:ℂ)*(MvPolynomial.X 0-MvPolynomial.C I*MvPolynomial.X 1)]
  have hi : (MvPolynomial.C I : Plane)^2= -1 := by rw [←map_pow,Complex.I_sq,map_neg,map_one]
  have hhalf : (2:Plane)*MvPolynomial.C (1/2:ℂ)=1 := by
    rw [←map_ofNat MvPolynomial.C 2,←map_mul,show (2:ℂ)*(1/2)=1 by norm_num,map_one]
  have hinv : undo.comp isotropicChange=AlgHom.id ℂ Plane := by
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j <;> simp [undo,isotropicChange,polarAxes,MvPolynomial.aeval_C,←MvPolynomial.C_eq_algebraMap]
    · linear_combination MvPolynomial.X (0:Fin 2)*hhalf
    · linear_combination (-MvPolynomial.X (1:Fin 2)*MvPolynomial.C I^2)*hhalf-MvPolynomial.X (1:Fin 2)*hi
  exact Function.LeftInverse.injective (g:=undo) fun Q => DFunLike.congr_fun hinv Q

private theorem chart_injective_in_degree {n : ℕ} {Q : Plane} (hq : Q.IsHomogeneous n) (hz : chart Q=0) : Q=0 := by
  have haxes (j : Fin 2) : (polarAxes j).IsHomogeneous 1 := by
    fin_cases j
    · exact (MvPolynomial.isHomogeneous_X _ _).add (MvPolynomial.isHomogeneous_X _ _)
    · exact ((MvPolynomial.isHomogeneous_X _ _).sub (MvPolynomial.isHomogeneous_X _ _)).C_mul _
  have hhom : (isotropicChange Q).IsHomogeneous n := by
    simpa only [isotropicChange,one_mul] using hq.aeval polarAxes haxes
  let E : Plane →ₐ[ℂ] ℂ[X] := MvPolynomial.aeval ![Polynomial.X,1]
  have hcomp : E.comp isotropicChange=chart := by
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j <;> simp [E,isotropicChange,polarAxes,chart,axes,Polynomial.C_eq_algebraMap]
  have hp := Polynomial.homogenize_eq_of_isHomogeneous hhom ((DFunLike.congr_fun hcomp Q).trans hz)
  apply change_injective
  simpa only [Polynomial.homogenize_zero,map_zero] using hp.symm

private def reflects (n : ℕ) (F : ℂ[X]) := F.natDegree≤n ∧ Polynomial.reflect n F=F.map (starRingEnd ℂ)

private theorem reflects_add {n : ℕ} {F G : ℂ[X]} (h : reflects n F) (g : reflects n G) : reflects n (F+G) :=
  ⟨(Polynomial.natDegree_add_le _ _).trans (max_le h.1 g.1),by rw [Polynomial.reflect_add,h.2,g.2,Polynomial.map_add]⟩

private theorem reflects_mul {n m : ℕ} {F G : ℂ[X]} (h : reflects n F) (g : reflects m G) : reflects (n+m) (F*G) :=
  ⟨Polynomial.natDegree_mul_le.trans (Nat.add_le_add h.1 g.1),by rw [Polynomial.reflect_mul _ _ h.1 g.1,h.2,g.2,Polynomial.map_mul]⟩

private theorem reflects_real (r : ℝ) : reflects 0 (Polynomial.C (r:ℂ)) := by
  simp [reflects,Polynomial.reflect_C]

private theorem reflects_pow {F : ℂ[X]} (h : reflects 1 F) (n : ℕ) : reflects n (F^n) := by
  induction n with
  | zero => simpa only [pow_zero,Complex.ofReal_one,map_one] using reflects_real 1
  | succ n ih => simpa only [pow_succ] using reflects_mul ih h

private theorem axes_reflect (j : Fin 2) : reflects 1 (axes j) := by
  have hd : (Polynomial.X+1 : ℂ[X]).natDegree≤1 := (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) (by simp))
  have hd' : (Polynomial.X-1 : ℂ[X]).natDegree≤1 := (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) (by simp))
  fin_cases j
  · refine ⟨hd,?_⟩
    simp [axes,Polynomial.reflect_add,add_comm]
  · refine ⟨(Polynomial.natDegree_C_mul_le _ _).trans hd',?_⟩
    simp [axes,Polynomial.reflect_C_mul,Polynomial.reflect_sub]
    ring

private theorem real_chart_coefficients {n : ℕ} (P : MvPolynomial (Fin 2) ℝ) (hP : P.IsHomogeneous n) :
    realPolarCoefficients n (chart (MvPolynomial.map Complex.ofRealHom P)) := by
  classical
  have hS (T : Finset (Fin 2 →₀ ℕ)) (hT : T⊆P.support) :
      reflects n (∑ m ∈ T, chart (MvPolynomial.map Complex.ofRealHom (MvPolynomial.monomial m (P.coeff m)))) := by
    induction T using Finset.induction_on with
    | empty => simp [reflects]
    | @insert m T hm ih =>
      rw [Finset.sum_insert hm]
      apply reflects_add _ (ih (fun j hj => hT (Finset.mem_insert_of_mem hj)))
      have hdeg := hP (Finsupp.mem_support_iff.mp (hT (Finset.mem_insert_self _ _)))
      have hcount : m 0+m 1=n := by simpa [Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_two] using hdeg
      have h := reflects_mul (reflects_real (P.coeff m)) (reflects_mul (reflects_pow (axes_reflect 0) (m 0))
        (reflects_pow (axes_reflect 1) (m 1)))
      simpa only [Nat.zero_add,hcount,MvPolynomial.map_monomial,chart,MvPolynomial.aeval_monomial,
        Finsupp.prod_fintype,Fin.prod_univ_two,Complex.ofRealHom_apply,←Polynomial.C_eq_algebraMap] using h
  have h := hS P.support (fun _ hx => hx)
  rw [←map_sum,←map_sum,←P.as_sum] at h
  refine ⟨h.1,fun j hj => ?_⟩
  have hh := congrArg (fun F : ℂ[X] => F.coeff (n-j)) h.2
  simpa only [Polynomial.coeff_reflect,Polynomial.revAt_le (Nat.sub_le _ _),Nat.sub_sub_self hj,Polynomial.coeff_map] using hh

/-- A homogeneous real Cartesian polynomial of degree at least two with
zero cleared p-Laplacian vanishes. This includes every real binary
homogeneous polynomial and every p>1 other than the Laplace exponent. -/
theorem real_homogeneous_cartesian_p_laplacian {n : ℕ} (hn : 2≤n) (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.IsHomogeneous n) {p : ℝ} (hp : 1<p) (hp₂ : p≠2) :
    clearedPLaplacian (p:ℂ) (MvPolynomial.map Complex.ofRealHom P)=0 ↔ P=0 := by
  constructor
  · intro h
    let Q := MvPolynomial.map Complex.ofRealHom P
    have hQ : Q.IsHomogeneous n := hP.map _
    have hs := cartesian_planar_symbol_in_chart (by omega : 0<n) (p:ℂ) Q hQ
    change clearedPLaplacian (p:ℂ) Q=0 at h
    rw [h,map_zero,mul_zero] at hs
    have hz := (homogeneous_planar_symbol_rigidity hp hp₂ hn (chart Q) (real_chart_coefficients P hP)).mp hs
    exact MvPolynomial.map_injective Complex.ofReal_injective ((chart_injective_in_degree hQ hz).trans (map_zero _).symm)
  · rintro rfl
    simp [clearedPLaplacian,infinityPolynomial,euclideanPolynomialLaplacian]

#print axioms cartesian_planar_symbol_in_chart
#print axioms real_homogeneous_cartesian_p_laplacian

end GaloisForLFunctions.RepresentationLifting.Spinor
