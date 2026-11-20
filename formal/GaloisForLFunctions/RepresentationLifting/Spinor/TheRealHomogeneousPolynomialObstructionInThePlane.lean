import GaloisForLFunctions.HTGeometry.PolynomialCriticalZeroFiber
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The real homogeneous obstruction for the planar p-Laplace symbol

Write a homogeneous binary form in the independent variables z=x+iy
and w=x−iy as w^n F(z/w). The cleared p-Laplace equation implies
that every critical point of F belongs to its zero fiber. Thus F is
a translated power. Conjugate symmetry leaves a power of a real
linear form or a radial monomial. Neither solves the equation in
degree at least two for p>1, p≠2.
-/

noncomputable section
open Polynomial Complex
open scoped ComplexConjugate
namespace GaloisForLFunctions.RepresentationLifting.Spinor

/-- Chart of the w-derivative of w^n F(z/w), evaluated at w=1. -/
def secondPolarDerivative (n : ℕ) (F : ℂ[X]) : ℂ[X] :=
  C (n:ℂ)*F-X*F.derivative

/-- Cleared planar symbol in isotropic coordinates, divided by four.
The terms are 2p H_z H_w H_zw and (p−2)(H_z²H_ww+H_w²H_zz). -/
def planarPolarSymbol (p : ℂ) (n : ℕ) (F : ℂ[X]) : ℂ[X] :=
  let A := F.derivative
  let B := secondPolarDerivative n F
  let D := C ((n:ℂ)-1)*B-X*B.derivative
  C (2*p)*A*B*B.derivative+C (p-2)*(A^2*D+B^2*A.derivative)

/-- A homogeneous polynomial takes real values on w=conj z when its
coefficient list is symmetric under conjugation and reversal. -/
def realPolarCoefficients (n : ℕ) (F : ℂ[X]) : Prop :=
  F.natDegree≤n ∧ ∀ j≤n, F.coeff j=conj (F.coeff (n-j))

/-- The divided symbol forces every critical point into the zero fiber.
Euler's identity recovers F from its two partial derivatives there. -/
theorem polar_critical_points_are_roots {n : ℕ} (hn : 0<n) {p : ℂ} (hp : p≠2)
    {F : ℂ[X]} (hF : 0<F.natDegree) (hs : planarPolarSymbol p n F=0) :
    ∀ z, F.derivative.IsRoot z → F.IsRoot z := by
  let A := F.derivative
  let B := secondPolarDerivative n F
  let D := C ((n:ℂ)-1)*B-X*B.derivative
  change C (2*p)*A*B*B.derivative+C (p-2)*(A^2*D+B^2*A.derivative)=0 at hs
  have hd : A ∣ C (p-2)*(A.derivative*B^2) := by
    refine ⟨-(C (2*p)*B*B.derivative+C (p-2)*A*D),?_⟩
    linear_combination hs
  obtain ⟨W,hW⟩ := hd
  have hd' : A ∣ A.derivative*B^2 := by
    refine ⟨C ((p-2)⁻¹)*W,?_⟩
    calc _ = (C ((p-2)⁻¹)*C (p-2))*(A.derivative*B^2) := by
                rw [←map_mul,inv_mul_cancel₀ (sub_ne_zero.mpr hp),map_one,one_mul]
         _ = _ := by rw [mul_assoc,hW]; ring
  intro z hz
  have hroot := isRoot_of_isRoot_of_dvd_derivative_mul (derivative_ne_zero.mpr hF.ne') hd' hz
  change (B^2).eval z=0 at hroot
  rw [eval_pow,sq_eq_zero_iff] at hroot
  change (C (n:ℂ)*F-X*F.derivative).eval z=0 at hroot
  simp only [eval_sub,eval_mul,eval_C,eval_X,hz.eq_zero,mul_zero,sub_zero] at hroot
  exact (mul_eq_zero.mp hroot).resolve_left (Nat.cast_ne_zero.mpr hn.ne')

/-- Every nonconstant complex chart solving the nonlinear symbol has
just one distinct root, without a reality condition on the form. -/
theorem polar_chart_is_a_translated_power {n : ℕ} (hn : 0<n) {p : ℂ} (hp : p≠2)
    {F : ℂ[X]} (hF : 0<F.natDegree) (hs : planarPolarSymbol p n F=0) :
    ∃ c : ℂ, F=C F.leadingCoeff*(X-C c)^F.natDegree := by
  classical
  have hcard := HTGeometry.card_roots_eq_one_of_critical_roots_zero F hF (polar_critical_points_are_roots hn hp hF hs)
  obtain ⟨_,c,hc⟩ := (Multiset.toFinset_card_eq_one_iff F.roots).mp hcard
  refine ⟨c,?_⟩
  have h := (IsAlgClosed.splits F).eq_prod_roots
  rwa [hc,Multiset.map_nsmul,Multiset.map_singleton,Multiset.prod_nsmul,Multiset.prod_singleton,
    ←(IsAlgClosed.splits F).natDegree_eq_card_roots] at h

private theorem symbol_at_unit_displacement (p a c : ℂ) (n b : ℕ) (hb : 0<b) :
    (planarPolarSymbol p n (C a*(X-C c)^b)).eval (c+1)=
      let N := (n:ℂ)
      let k := (b:ℂ)
      let A := a*k
      let A' := a*k*(k-1)
      let B := N*a-(c+1)*A
      let B' := (N-1)*A-(c+1)*A'
      (2*p)*A*B*B'+(p-2)*(A^2*((N-1)*B-(c+1)*B')+B^2*A') := by
  let F : ℂ[X] := C a*(X-C c)^b
  have hval : (c+1)-c=1 := by ring
  have hj : ((b-1:ℕ):ℂ)=(b:ℂ)-1 := by rw [Nat.cast_sub hb,Nat.cast_one]
  have hF : F.eval (c+1)=a := by simp [F,hval]
  have hder : F.derivative=C a*C (b:ℂ)*(X-C c)^(b-1) := by
    simp only [F,derivative_C_mul,derivative_pow,derivative_sub,derivative_X,derivative_C,sub_zero,mul_one,mul_assoc]
  have hA : F.derivative.eval (c+1)=a*b := by simp only [hder,eval_mul,eval_pow,eval_sub,eval_X,eval_C,hval,one_pow,mul_one]
  have hA' : F.derivative.derivative.eval (c+1)=a*b*((b:ℂ)-1) := by
    rw [hder,←map_mul,derivative_C_mul,derivative_pow]
    simp only [derivative_sub,derivative_X,derivative_C,sub_zero,mul_one,eval_mul,eval_pow,
      eval_C,eval_sub,eval_X,hval,one_pow,hj]
  have hB' : (secondPolarDerivative n F).derivative.eval (c+1)=
      ((n:ℂ)-1)*(a*b)-(c+1)*(a*b*((b:ℂ)-1)) := by
    simp only [secondPolarDerivative,derivative_sub,derivative_C_mul,derivative_mul,derivative_X,
      derivative_C,zero_mul,zero_add,one_mul,eval_sub,eval_add,eval_mul,eval_X,eval_C,hA,hA']
    ring
  have hB : (secondPolarDerivative n F).eval (c+1) = (n:ℂ)*a-(c+1)*(a*b) := by
    simp only [secondPolarDerivative,eval_sub,eval_mul,eval_C,eval_X,hF,hA]
  change (planarPolarSymbol p n F).eval (c+1)=_
  simp only [planarPolarSymbol,eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X,hB',hB,hA,hA']

/-- Lewis's rigidity in the homogeneous polar chart. At degree two and
higher the only conjugate-symmetric solution is identically zero. -/
theorem homogeneous_planar_symbol_rigidity {p : ℝ} (hp : 1<p) (hp₂ : p≠2)
    {n : ℕ} (hn : 2≤n) (F : ℂ[X]) (hreal : realPolarCoefficients n F) :
    planarPolarSymbol (p:ℂ) n F=0 ↔ F=0 := by
  constructor
  · intro hs
    by_contra hF
    let b := F.natDegree
    let a := F.leadingCoeff
    have ha : a≠0 := leadingCoeff_ne_zero.mpr hF
    have hlead : F.coeff b=a := rfl
    have hrev : F.coeff b=conj (F.coeff (n-b)) := hreal.2 b hreal.1
    have href : F.coeff (n-b)≠0 := by
      intro h
      rw [h,map_zero,hlead] at hrev
      exact ha hrev
    have hb : 0<b := by
      by_contra! h
      have hh : b<n-b := by omega
      exact href (coeff_eq_zero_of_natDegree_lt hh)
    have hp₂' : (p:ℂ)≠2 := by exact_mod_cast hp₂
    obtain ⟨c,hc⟩ := polar_chart_is_a_translated_power (by omega : 0<n) hp₂' hb hs
    change F=C a*(X-C c)^b at hc
    have htest : (planarPolarSymbol (p:ℂ) n F).eval (c+1)=0 := by rw [hs,eval_zero]
    rw [hc,symbol_at_unit_displacement _ _ _ _ _ hb] at htest
    have hb' : (b:ℂ)≠0 := Nat.cast_ne_zero.mpr hb.ne'
    have hp' : (p:ℂ)-1≠0 := by exact_mod_cast (sub_pos.mpr hp).ne'
    by_cases hbn : b=n
    · have hc₀ : c≠0 := by
        intro hz
        have h₀ := congrArg (fun Q : ℂ[X] => Q.coeff 0) hc
        change F.coeff 0=(C a*(X-C c)^b).coeff 0 at h₀
        rw [hz,map_zero,sub_zero,coeff_C_mul_X_pow] at h₀
        simp only [if_neg hb.ne',if_neg hb.ne'.symm] at h₀
        exact href (by simpa only [←hbn,Nat.sub_self] using h₀)
      have hbm : (b:ℂ)-1≠0 := sub_ne_zero.mpr (by exact_mod_cast (show b≠1 by omega))
      have hz : 4*((p:ℂ)-1)*a^3*(b:ℂ)^3*((b:ℂ)-1)*c^2=0 := by
        rw [←hbn] at htest
        linear_combination htest
      exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hp')
        (pow_ne_zero _ ha)) (pow_ne_zero _ hb')) hbm) (pow_ne_zero _ hc₀)) hz
    · have hbn' : b<n := lt_of_le_of_ne hreal.1 hbn
      have h₀ := hreal.2 0 (Nat.zero_le _)
      simp only [Nat.sub_zero,coeff_eq_zero_of_natDegree_lt hbn',map_zero] at h₀
      have he : (C a*(X-C c)^b).eval 0=0 := by simpa only [←hc,coeff_zero_eq_eval_zero] using h₀
      simp only [eval_mul,eval_C,eval_pow,eval_sub,eval_X,zero_sub] at he
      have hc₀ : c=0 := by
        by_contra h
        exact (mul_ne_zero ha (pow_ne_zero _ (neg_ne_zero.mpr h))) he
      have hmono : F=C a*X^b := by simpa only [hc₀,map_zero,sub_zero] using hc
      have hindex : n-b=b := by
        by_contra hi
        apply href
        rw [hmono,coeff_C_mul_X_pow]
        simp only [if_neg hi,if_neg (Ne.symm hi)]
      have heq : (n:ℂ)=2*(b:ℂ) := by exact_mod_cast (show n=2*b by omega)
      have hpos : 0<2*(p-1)*(b:ℝ)-(p-2) := by
        have h := mul_nonneg (sub_pos.mpr hp).le (sub_nonneg.mpr (Nat.one_le_cast.mpr hb))
        linarith only [h,hp]
      have hfac : 2*((p:ℂ)-1)*(b:ℂ)-((p:ℂ)-2)≠0 := by exact_mod_cast hpos.ne'
      have hz : 2*a^3*(b:ℂ)^3*(2*((p:ℂ)-1)*(b:ℂ)-((p:ℂ)-2))=0 := by
        rw [hc₀,heq] at htest
        linear_combination htest
      exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ ha)) (pow_ne_zero _ hb')) hfac) hz
  · rintro rfl
    simp [planarPolarSymbol,secondPolarDerivative]

end GaloisForLFunctions.RepresentationLifting.Spinor
