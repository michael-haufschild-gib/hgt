import GaloisForLFunctions.HTGeometry.ReflectedCubicExponentialModel
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.ComputeDegree

/-!
# Cubic rational maps with three labeled integral fibers

The three distinguished fibers are supported on separate residue classes
modulo three. Their homogeneous coordinates have no common zero and obey
reciprocal symmetry. These exact algebraic models obstruct a proposed
degree-one rigidity argument; they do not settle the transcendental-section
problem or assert a result about Xi.
-/

noncomputable section
open Polynomial Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry.TernaryLatticeCubic

def q (m : ℤ) : ℤ := 5*m+2
def t (m : ℤ) : ℤ := -45*m^2-36*m-8
def omega : ℂ := (-1 + ReflectedCubicExponentialModel.rootThree * I)/2

theorem omega_quadratic : omega^2+omega+1=0 := by
  dsimp [omega]
  linear_combination (I^2/4) * ReflectedCubicExponentialModel.rootThree_sq +
    (3/4 : ℂ) * I_sq

theorem omega_ne_one : omega ≠ 1 := by
  intro h
  have hs := omega_quadratic
  norm_num [h] at hs

theorem omega_sq_ne_one : omega^2 ≠ 1 := by
  intro h
  have hneg : omega = -2 := by linear_combination omega_quadratic-h
  norm_num [hneg] at h

theorem omega_ne_sq : omega ≠ omega^2 := by
  intro h
  have htwo : 2*omega+1=0 := by linear_combination omega_quadratic+h
  have : (3 : ℂ)=0 := by
    linear_combination 4*omega_quadratic-(2*omega+1)*htwo
  norm_num at this

theorem omega_cube : omega^3=1 := by
  linear_combination (omega-1)*omega_quadratic

theorem q_ne_zero (m : ℤ) : q m ≠ 0 := by
  dsimp [q]
  omega

theorem t_mod_three (m : ℤ) : t m % 3 = 1 := by
  have ht : t m=3*(-15*m^2-12*m-3)+1 := by dsimp [t]; ring
  rw [ht]
  omega

theorem t_ne_one (m : ℤ) : t m ≠ 1 := by
  intro h
  have he : 5*m^2+4*m+1=0 := by
    dsimp [t] at h
    linarith
  have hm : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hm with hm | hm | hm <;>
    have hh := congrArg (fun n : ℤ => n % 3) he <;>
    norm_num [pow_two, Int.add_emod, Int.mul_emod, hm] at hh

theorem t_ne_four (m : ℤ) : t m ≠ 4 := by
  intro h
  have he : 15*m^2+12*m+4=0 := by
    dsimp [t] at h
    linarith
  have hh := congrArg (fun n : ℤ => n % 3) he
  norm_num [Int.add_emod, Int.mul_emod] at hh

def A0 (m : ℤ) : ℂ[X] := X*(X-C (3*(q m : ℂ)))*(X+C (3*(q m : ℂ)))
def A1 (m : ℤ) : ℂ[X] := (X-C 1)*(X-C 4)*(X-C (t m : ℂ))
def A2 (m : ℤ) : ℂ[X] := (X+C 1)*(X+C 4)*(X+C (t m : ℂ))
def numerator (m : ℤ) : ℂ[X] := C omega*A2 m-A1 m
def denominator (m : ℤ) : ℂ[X] := A2 m-C omega*A1 m

theorem fiber_sum (m : ℤ) : A1 m+A2 m=2*A0 m := by
  simp only [A0, A1, A2, t, q, Int.cast_sub, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_ofNat, Int.cast_add, map_sub, map_add, map_mul,
    map_neg, map_pow, map_ofNat, map_one]
  ring

theorem eval_A0 (m : ℤ) (w : ℂ) :
    (A0 m).eval w = w*(w-3*(q m : ℂ))*(w+3*(q m : ℂ)) := by simp [A0]
theorem eval_A1 (m : ℤ) (w : ℂ) :
    (A1 m).eval w = (w-1)*(w-4)*(w-(t m : ℂ)) := by simp [A1]
theorem eval_A2 (m : ℤ) (w : ℂ) :
    (A2 m).eval w = (w+1)*(w+4)*(w+(t m : ℂ)) := by simp [A2]

theorem roots_A0 (m : ℤ) (w : ℂ) :
    (A0 m).eval w=0 ↔ w=0 ∨ w=3*(q m : ℂ) ∨ w= -3*(q m : ℂ) := by
  rw [eval_A0]
  simp only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]
  ring_nf
  tauto

theorem roots_A1 (m : ℤ) (w : ℂ) :
    (A1 m).eval w=0 ↔ w=1 ∨ w=4 ∨ w=(t m : ℂ) := by
  rw [eval_A1]
  simp only [mul_eq_zero, sub_eq_zero, or_assoc]

theorem roots_A2 (m : ℤ) (w : ℂ) :
    (A2 m).eval w=0 ↔ w= -1 ∨ w= -4 ∨ w= -(t m : ℂ) := by
  rw [eval_A2]
  simp only [mul_eq_zero, add_eq_zero_iff_eq_neg, or_assoc]

theorem roots_A1_label (m : ℤ) (w : ℂ) (h : (A1 m).eval w=0) :
    ∃ k : ℤ, w=k ∧ k%3=1 := by
  rcases (roots_A1 m w).mp h with h | h | h
  · exact ⟨1, by simpa using h, by norm_num⟩
  · exact ⟨4, by simpa using h, by norm_num⟩
  · exact ⟨t m, h, t_mod_three m⟩

theorem roots_A2_label (m : ℤ) (w : ℂ) (h : (A2 m).eval w=0) :
    ∃ k : ℤ, w=k ∧ k%3=2 := by
  rcases (roots_A2 m w).mp h with h | h | h
  · exact ⟨-1, by simpa using h, by norm_num⟩
  · exact ⟨-4, by simpa using h, by norm_num⟩
  · exact ⟨-t m, by simpa using h, by have := t_mod_three m; omega⟩

theorem disjoint_A1_A2 (m : ℤ) (w : ℂ) :
    ¬ ((A1 m).eval w=0 ∧ (A2 m).eval w=0) := by
  rintro ⟨h1,h2⟩
  obtain ⟨k,hk,hk3⟩ := roots_A1_label m w h1
  obtain ⟨l,hl,hl3⟩ := roots_A2_label m w h2
  have hkl : k=l := by exact_mod_cast hk.symm.trans hl
  omega

theorem fiber_one (m : ℤ) :
    numerator m-denominator m=C (2*(omega-1))*A0 m := by
  dsimp [numerator, denominator]
  have hs := fiber_sum m
  simp only [map_mul, map_sub, map_ofNat, map_one]
  linear_combination (C omega-1)*hs

theorem fiber_omega (m : ℤ) :
    numerator m-C omega*denominator m=C (omega^2-1)*A1 m := by
  simp only [numerator, denominator, map_sub, map_pow, map_one]
  ring

theorem fiber_omega_sq (m : ℤ) :
    numerator m-C (omega^2)*denominator m=C (omega-omega^2)*A2 m := by
  have hc : (C omega : ℂ[X])^3=1 := by rw [← map_pow, omega_cube, map_one]
  simp only [numerator, denominator, map_sub, map_pow]
  linear_combination A1 m*hc

theorem no_common_zero (m : ℤ) (w : ℂ) :
    ¬ ((numerator m).eval w=0 ∧ (denominator m).eval w=0) := by
  rintro ⟨hn,hd⟩
  have he := congrArg (fun p : ℂ[X] => p.eval w) (fiber_omega m)
  simp only [eval_sub, eval_mul, eval_C, hn, hd, mul_zero, sub_zero] at he
  have h1 : (A1 m).eval w=0 :=
    (mul_eq_zero.mp he.symm).resolve_left (sub_ne_zero.mpr omega_sq_ne_one)
  have h2 : (A2 m).eval w=0 := by
    simpa [denominator, h1] using hd
  exact disjoint_A1_A2 m w ⟨h1,h2⟩

theorem roots_A0_label (m : ℤ) (w : ℂ) (h : (A0 m).eval w=0) :
    ∃ k : ℤ, w=k ∧ k%3=0 := by
  rcases (roots_A0 m w).mp h with h | h | h
  · exact ⟨0, by simpa using h, by norm_num⟩
  · exact ⟨3*q m, by simpa using h, by omega⟩
  · exact ⟨-3*q m, by simpa using h, by omega⟩

theorem complete_fiber_one (m : ℤ) (w : ℂ) :
    (numerator m).eval w=(denominator m).eval w ↔
      w=0 ∨ w=3*(q m : ℂ) ∨ w= -3*(q m : ℂ) := by
  rw [← roots_A0, ← sub_eq_zero]
  have he := congrArg (fun p : ℂ[X] => p.eval w) (fiber_one m)
  simp only [eval_sub, eval_mul, eval_C] at he
  rw [he, mul_eq_zero]
  simp [sub_eq_zero, omega_ne_one]

theorem complete_fiber_omega (m : ℤ) (w : ℂ) :
    (numerator m).eval w=omega*(denominator m).eval w ↔
      w=1 ∨ w=4 ∨ w=(t m : ℂ) := by
  rw [← roots_A1, ← sub_eq_zero]
  have he := congrArg (fun p : ℂ[X] => p.eval w) (fiber_omega m)
  simp only [eval_sub, eval_mul, eval_C] at he
  rw [he, mul_eq_zero]
  simp only [sub_eq_zero, omega_sq_ne_one, false_or]

theorem complete_fiber_omega_sq (m : ℤ) (w : ℂ) :
    (numerator m).eval w=omega^2*(denominator m).eval w ↔
      w= -1 ∨ w= -4 ∨ w= -(t m : ℂ) := by
  rw [← roots_A2, ← sub_eq_zero]
  have he := congrArg (fun p : ℂ[X] => p.eval w) (fiber_omega_sq m)
  simp only [eval_sub, eval_mul, eval_C] at he
  rw [he, mul_eq_zero]
  simp [sub_eq_zero, omega_ne_sq]

theorem numerator_neg (m : ℤ) (w : ℂ) :
    (numerator m).eval (-w)=(denominator m).eval w := by
  simp [numerator, denominator, eval_A1, eval_A2]
  ring

theorem denominator_neg (m : ℤ) (w : ℂ) :
    (denominator m).eval (-w)=(numerator m).eval w := by
  simp [numerator, denominator, eval_A1, eval_A2]
  ring

theorem degree_A1 (m : ℤ) : (A1 m).natDegree=3 := by
  dsimp [A1]
  compute_degree <;> norm_num

theorem degree_A2 (m : ℤ) : (A2 m).natDegree=3 := by
  dsimp [A2]
  compute_degree <;> norm_num

theorem monic_A1 (m : ℤ) : (A1 m).Monic :=
  ((monic_X_sub_C 1).mul (monic_X_sub_C 4)).mul (monic_X_sub_C _)

theorem monic_A2 (m : ℤ) : (A2 m).Monic :=
  ((monic_X_add_C 1).mul (monic_X_add_C 4)).mul (monic_X_add_C _)

theorem numerator_degree (m : ℤ) : (numerator m).natDegree=3 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact (natDegree_sub_le _ _).trans (max_le
      ((natDegree_C_mul_le _ _).trans (degree_A2 m).le) (degree_A1 m).le)
  · have h1 : (A1 m).coeff 3=1 := by
      rw [← degree_A1 m, coeff_natDegree, (monic_A1 m).leadingCoeff]
    have h2 : (A2 m).coeff 3=1 := by
      rw [← degree_A2 m, coeff_natDegree, (monic_A2 m).leadingCoeff]
    simpa [numerator, h1, h2] using sub_ne_zero.mpr omega_ne_one

theorem denominator_degree (m : ℤ) : (denominator m).natDegree=3 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact (natDegree_sub_le _ _).trans (max_le (degree_A2 m).le
      ((natDegree_C_mul_le _ _).trans (degree_A1 m).le))
  · have h1 : (A1 m).coeff 3=1 := by
      rw [← degree_A1 m, coeff_natDegree, (monic_A1 m).leadingCoeff]
    have h2 : (A2 m).coeff 3=1 := by
      rw [← degree_A2 m, coeff_natDegree, (monic_A2 m).leadingCoeff]
    simpa [denominator, h1, h2] using sub_ne_zero.mpr omega_ne_one.symm

private theorem simple_triple (a b c : ℂ) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (w : ℂ)
    (hw : ((X-C a)*(X-C b)*(X-C c)).eval w=0) :
    (((X-C a)*(X-C b)*(X-C c)).derivative).eval w ≠ 0 := by
  simp only [eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero] at hw
  rcases hw with (rfl | rfl) | rfl
  · simpa [derivative_mul, derivative_X_sub_C] using
      mul_ne_zero (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hac)
  · simpa [derivative_mul, derivative_X_sub_C] using
      mul_ne_zero (sub_ne_zero.mpr hab.symm) (sub_ne_zero.mpr hbc)
  · simpa [derivative_mul, derivative_X_sub_C] using
      mul_ne_zero (sub_ne_zero.mpr hac.symm) (sub_ne_zero.mpr hbc.symm)

theorem simple_A0 (m : ℤ) (w : ℂ) (hw : (A0 m).eval w=0) :
    ((A0 m).derivative).eval w ≠ 0 := by
  have hq : (q m : ℂ) ≠ 0 := by exact_mod_cast q_ne_zero m
  have h3 : 3*(q m : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hq
  have hab : (0 : ℂ) ≠ 3*(q m : ℂ) := h3.symm
  have hac : (0 : ℂ) ≠ -3*(q m : ℂ) := by
    simpa only [neg_mul] using (neg_ne_zero.mpr h3).symm
  have hbc : 3*(q m : ℂ) ≠ -3*(q m : ℂ) := by
    intro h
    apply hq
    linear_combination (1/6 : ℂ)*h
  have hp : A0 m=(X-C 0)*(X-C (3*(q m : ℂ)))*(X-C (-3*(q m : ℂ))) := by
    simp [A0]
  rw [hp] at hw ⊢
  exact simple_triple _ _ _ hab hac hbc w hw

theorem simple_A1 (m : ℤ) (w : ℂ) (hw : (A1 m).eval w=0) :
    ((A1 m).derivative).eval w ≠ 0 := by
  have h1 : (1 : ℂ) ≠ (t m : ℂ) := by exact_mod_cast (t_ne_one m).symm
  have h4 : (4 : ℂ) ≠ (t m : ℂ) := by exact_mod_cast (t_ne_four m).symm
  exact simple_triple 1 4 _ (by norm_num) h1 h4 w hw

theorem simple_A2 (m : ℤ) (w : ℂ) (hw : (A2 m).eval w=0) :
    ((A2 m).derivative).eval w ≠ 0 := by
  have h1 : (-1 : ℂ) ≠ -(t m : ℂ) := by
    simp only [ne_eq, neg_inj]
    exact_mod_cast (t_ne_one m).symm
  have h4 : (-4 : ℂ) ≠ -(t m : ℂ) := by
    simp only [ne_eq, neg_inj]
    exact_mod_cast (t_ne_four m).symm
  have hp : A2 m=(X-C (-1))*(X-C (-4))*(X-C (-(t m : ℂ))) := by simp [A2]
  rw [hp] at hw ⊢
  exact simple_triple _ _ _ (by norm_num) h1 h4 w hw

theorem family_distinct (m n : ℤ)
    (h : numerator m*denominator n=numerator n*denominator m) : m=n := by
  let w : ℂ := 3*(q m : ℂ)
  have hm : (numerator m).eval w=(denominator m).eval w :=
    (complete_fiber_one m w).mpr (Or.inr (Or.inl rfl))
  have hd : (denominator m).eval w ≠ 0 := by
    intro hz
    exact no_common_zero m w ⟨hm.trans hz,hz⟩
  have he := congrArg (fun p : ℂ[X] => p.eval w) h
  simp only [eval_mul] at he
  have hmul : ((numerator n).eval w-(denominator n).eval w)*
      (denominator m).eval w=0 := by
    rw [hm] at he
    linear_combination -he
  have hn : (numerator n).eval w=(denominator n).eval w :=
    sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hd)
  rcases (complete_fiber_one n w).mp hn with hn | hn | hn
  · have hq : (q m : ℂ)=0 := by change 3*(q m : ℂ)=0 at hn; linear_combination hn/3
    exact False.elim (q_ne_zero m (by exact_mod_cast hq))
  · have hq : (q m : ℂ)=(q n : ℂ) := by change 3*(q m : ℂ)=_ at hn; linear_combination hn/3
    have hi : q m=q n := by exact_mod_cast hq
    dsimp [q] at hi
    omega
  · have hq : (q m : ℂ)= -(q n : ℂ) := by change 3*(q m : ℂ)=_ at hn; linear_combination hn/3
    have hi : q m= -q n := by exact_mod_cast hq
    dsimp [q] at hi
    omega

theorem omega_conj : conj omega=omega^2 := by
  have hc : conj omega= -1-omega := by
    have hc2 : conj (2 : ℂ)=2 := conj_ofReal 2
    have hcr : conj ReflectedCubicExponentialModel.rootThree=
        ReflectedCubicExponentialModel.rootThree := conj_ofReal _
    simp only [omega, map_div₀, map_add, map_neg, map_one, map_mul, hc2, hcr, conj_I]
    ring
  rw [hc]
  linear_combination -omega_quadratic

theorem numerator_conj (m : ℤ) (w : ℂ) :
    (numerator m).eval (conj w)=omega*conj ((denominator m).eval w) := by
  simp only [numerator, denominator, eval_sub, eval_mul, eval_C,
    eval_A1, eval_A2, map_sub, map_add, map_mul, map_one, map_ofNat,
    map_intCast, omega_conj]
  linear_combination ((conj w-1)*(conj w-4)*(conj w-(t m : ℂ)))*omega_cube

theorem denominator_conj (m : ℤ) (w : ℂ) :
    (denominator m).eval (conj w)=omega*conj ((numerator m).eval w) := by
  simp only [numerator, denominator, eval_sub, eval_mul, eval_C,
    eval_A1, eval_A2, map_sub, map_add, map_mul, map_one, map_ofNat,
    map_intCast, omega_conj]
  linear_combination -((conj w+1)*(conj w+4)*(conj w+(t m : ℂ)))*omega_cube

theorem denominator_root_nonreal (m : ℤ) (w : ℂ)
    (hw : (denominator m).eval w=0) : w ≠ conj w := by
  intro hc
  have hn := numerator_conj m w
  rw [← hc, hw, map_zero, mul_zero] at hn
  exact no_common_zero m w ⟨hn, hw⟩

theorem exists_nonreal_pole (m : ℤ) :
    ∃ w : ℂ, (denominator m).eval w=0 ∧ w ≠ conj w := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_root (denominator m) (by
    intro h
    have hn := denominator_degree m
    have hz : (denominator m).natDegree=0 := natDegree_eq_of_degree_eq_some h
    omega)
  exact ⟨w,hw,denominator_root_nonreal m w hw⟩

theorem coprime_coordinates (m : ℤ) : IsCoprime (numerator m) (denominator m) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ
    (numerator m) (denominator m)).mpr
  intro w
  simpa only [coe_aeval_eq_eval] using not_and_or.mp (no_common_zero m w)

/-- Both coordinates have exact degree three and are already coprime. -/
theorem degree_three_family (m : ℤ) :
    (numerator m).natDegree=3 ∧ (denominator m).natDegree=3 ∧
      IsCoprime (numerator m) (denominator m) :=
  ⟨numerator_degree m, denominator_degree m, coprime_coordinates m⟩

/-- Distinct indices remain distinct as rational maps, even after rescaling. -/
theorem rational_map_equality_iff (m n : ℤ) :
    numerator m*denominator n=numerator n*denominator m ↔ m=n := by
  constructor
  · exact family_distinct m n
  · rintro rfl
    rfl

theorem leading_coordinates (m : ℤ) :
    (numerator m).leadingCoeff=omega-1 ∧
      (denominator m).leadingCoeff=1-omega := by
  have h1 : (A1 m).coeff 3=1 := by
    rw [← degree_A1 m, coeff_natDegree, (monic_A1 m).leadingCoeff]
  have h2 : (A2 m).coeff 3=1 := by
    rw [← degree_A2 m, coeff_natDegree, (monic_A2 m).leadingCoeff]
  simp only [leadingCoeff, numerator_degree, denominator_degree]
  simp [numerator, denominator, h1, h2]

/-- No distinguished fiber acquires an extra point at projective infinity. -/
theorem infinity_not_distinguished (m : ℤ) :
    (numerator m).leadingCoeff ≠ (denominator m).leadingCoeff ∧
    (numerator m).leadingCoeff ≠ omega*(denominator m).leadingCoeff ∧
    (numerator m).leadingCoeff ≠ omega^2*(denominator m).leadingCoeff := by
  rw [(leading_coordinates m).1, (leading_coordinates m).2]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply omega_ne_one
    linear_combination h/2
  · intro h
    apply omega_sq_ne_one
    linear_combination h
  · intro h
    apply omega_ne_sq
    linear_combination h-omega_cube

end GaloisForLFunctions.HTGeometry.TernaryLatticeCubic
