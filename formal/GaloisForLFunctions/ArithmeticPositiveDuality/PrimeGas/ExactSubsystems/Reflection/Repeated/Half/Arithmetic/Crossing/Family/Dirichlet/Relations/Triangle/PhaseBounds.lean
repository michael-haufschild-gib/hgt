import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Triangle.AngleOrder
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Triangle.Exponents

/-! # A common torsion exponent for resonant triangles -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open IntermediateField Real
open scoped ComplexConjugate

/-- The squared cosine follows from the two lengths and the opposite side. -/
private theorem squared_trace_mem (K : IntermediateField ℚ ℂ) {U V : ℂ} {x y : ℝ} {m : ℕ}
    (hm : 0 < m) (u : U^m=1) (v : V^m=1) (nz : x ≠ 0)
    (h : (x : ℂ)*U+(y : ℂ)*V=1) (xm : (x : ℂ)^2 ∈ K) (ym : (y : ℂ)^2 ∈ K) :
    (U+U⁻¹)^2 ∈ K := by
  have un : U ≠ 0 := norm_pos_iff.mp (by rw [phase_norm hm u]; exact zero_lt_one)
  have vn : V ≠ 0 := norm_pos_iff.mp (by rw [phase_norm hm v]; exact zero_lt_one)
  have back := congrArg (starRingEnd ℂ) h
  simp only [map_add,map_mul,map_one,Complex.conj_ofReal,conjugate_torsion hm u,conjugate_torsion hm v] at back
  have h₁ : (y : ℂ)*V=1-(x : ℂ)*U := by linear_combination h
  have h₂ : (y : ℂ)*V⁻¹=1-(x : ℂ)*U⁻¹ := by linear_combination back
  have cosine : (x : ℂ)*(U+U⁻¹)=1+(x : ℂ)^2-(y : ℂ)^2 := by
    have eq := congrArg₂ (· * ·) h₁ h₂
    linear_combination eq-(y : ℂ)^2*(mul_inv_cancel₀ vn)+(x : ℂ)^2*(mul_inv_cancel₀ un)
  have sq : (U+U⁻¹)^2=(1+(x : ℂ)^2-(y : ℂ)^2)^2/(x : ℂ)^2 := by
    rw [← cosine,mul_pow,mul_div_cancel_left₀ _ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr nz))]
  rw [sq]
  exact div_mem (pow_mem (K.sub_mem (K.add_mem K.one_mem xm) ym) _) xm

private theorem degenerate_order {U V : ℂ} {m : ℕ} {x y : ℝ} (hm : 0 < m)
    (u : U^m=1) (v : V^m=1) (h : (x : ℂ)*U+(y : ℂ)*V=1) (zero : phaseDet U V=0) :
    U^2=1 ∧ V^2=1 := by
  obtain ⟨a,b⟩ := triangle_equations hm u v h
  rw [zero,mul_zero] at a b
  have eq {z : ℂ} (hz : z^m=1) (inv : z=z⁻¹) : z^2=1 := by
    have nz : z ≠ 0 := norm_pos_iff.mp (by rw [phase_norm hm hz]; exact zero_lt_one)
    calc z^2 = z*z⁻¹ := by rw [sq,← inv]
         _ = 1 := mul_inv_cancel₀ nz
  exact ⟨eq u (sub_eq_zero.mp b.symm),eq v (sub_eq_zero.mp a.symm).symm⟩

private theorem coordinate_of_triangle {x y : ℝ} {U V : ℂ} {m : ℕ} (hm : 0 < m)
    (u : U^m=1) (v : V^m=1) (eq : (x : ℂ)*U+(y : ℂ)*V=1) (nonzero : phaseDet U V ≠ 0) :
    (x : ℂ)=phaseRatio U V ∧ (y : ℂ)=phaseRatio V U := by
  obtain ⟨a,b⟩ := triangle_equations hm u v eq
  have swap : phaseDet V U= -phaseDet U V := by unfold phaseDet; ring
  have swapped : phaseDet V U ≠ 0 := by rw [swap]; exact neg_ne_zero.mpr nonzero
  refine ⟨(eq_div_iff nonzero).mpr a,(eq_div_iff swapped).mpr ?_⟩
  rw [swap,mul_neg,b,neg_sub]

private theorem phaseRatio_alg {U V : ℂ} {m : ℕ} (hm : 0 < m) (u : U^m=1) (v : V^m=1) :
    IsAlgebraic ℚ (phaseRatio U V) := by
  let A := algebraicClosure ℚ ℂ
  have a : U ∈ A := mem_algebraicClosure_iff.mpr (torsion_algebraic ℚ hm u)
  have b : V ∈ A := mem_algebraicClosure_iff.mpr (torsion_algebraic ℚ hm v)
  exact mem_algebraicClosure_iff.mp (A.div_mem (A.sub_mem (A.inv_mem b) b)
    (A.sub_mem (A.mul_mem a (A.inv_mem b)) (A.mul_mem (A.inv_mem a) b)))

/-- Integer coefficients can be normalized by any nonzero rational weights.
Only finitely many phases occur among all compatible orders and dilations. -/
theorem uniform_triangle_exponent {E F : ℝ} (ind : independentGaps E F) (one : algebraicPair E F 1)
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ N : ℕ, 0<N ∧ ∀ v : ℝ, ∀ U V : ℂ, ∀ m : ℕ, 0 < m → U^m=1 → V^m=1 →
      (a : ℂ)*gapExp E v*U+(b : ℂ)*gapExp F v*V=1 → U^N=1 ∧ V^N=1 := by
  obtain ⟨K,dim,field⟩ := common_radical_field ind one
  letI : FiniteDimensional ℚ K := dim
  let D := (2*(4*Module.finrank ℚ K)).factorial
  refine ⟨2*D,mul_pos zero_lt_two (Nat.factorial_pos _),?_⟩
  intro v U V m hm hu hv eq
  let x := (a : ℝ)*exp (v*E)
  let y := (b : ℝ)*exp (v*F)
  have xx : (x : ℂ)=(a : ℂ)*gapExp E v := by simp only [x,gapExp,Complex.ofReal_mul,Complex.ofReal_ratCast]
  have yy : (y : ℂ)=(b : ℂ)*gapExp F v := by simp only [y,gapExp,Complex.ofReal_mul,Complex.ofReal_ratCast]
  rw [← xx,← yy] at eq
  have twice {z : ℂ} (h : z^2=1) : z^(2*D)=1 := by rw [pow_mul,h,one_pow]
  by_cases zero : phaseDet U V=0
  · have d := degenerate_order hm hu hv eq zero
    exact ⟨twice d.1,twice d.2⟩
  obtain ⟨aEq,bEq⟩ := coordinate_of_triangle hm hu hv eq zero
  have recover (q : ℚ) (hq : q ≠ 0) (z : ℂ) (h : IsAlgebraic ℚ ((q : ℂ)*z)) : IsAlgebraic ℚ z := by
    let A := algebraicClosure ℚ ℂ
    have m' : (q : ℂ)*z ∈ A := mem_algebraicClosure_iff.mpr h
    have q' : (q : ℂ) ∈ A := A.algebraMap_mem q
    apply mem_algebraicClosure_iff.mp
    simpa only [mul_div_cancel_left₀ _ (Rat.cast_ne_zero.mpr hq : (q : ℂ) ≠ 0)] using A.div_mem m' q'
  have alg : algebraicPair E F v := ⟨recover a ha _ (by rw [← xx,aEq]; exact phaseRatio_alg hm hu hv),
    recover b hb _ (by rw [← yy,bEq]; exact phaseRatio_alg hm hv hu)⟩
  obtain ⟨n,hn,A,B⟩ := field v alg
  have sqX : (x : ℂ)^2 ∈ K := by
    rw [aEq]
    apply ratio_square_mem K hm hu hv hn
    rw [← aEq,xx,mul_pow]
    exact K.mul_mem (pow_mem (K.algebraMap_mem a) _) A
  have sqY : (y : ℂ)^2 ∈ K := by
    rw [bEq]
    apply ratio_square_mem K hm hv hu hn
    rw [← bEq,yy,mul_pow]
    exact K.mul_mem (pow_mem (K.algebraMap_mem b) _) B
  have flip : (y : ℂ)*V+(x : ℂ)*U=1 := (add_comm _ _).trans eq
  have bound {z : ℂ} (h : z^D=1) : z^(2*D)=1 := by rw [Nat.mul_comm,pow_mul,h,one_pow]
  exact ⟨bound (angle_order K hm hu (squared_trace_mem K hm hu hv
    (mul_ne_zero (Rat.cast_ne_zero.mpr ha) (exp_pos _).ne') eq sqX sqY)),
    bound (angle_order K hm hv (squared_trace_mem K hm hv hu
    (mul_ne_zero (Rat.cast_ne_zero.mpr hb) (exp_pos _).ne') flip sqY sqX))⟩

#print axioms uniform_triangle_exponent

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
