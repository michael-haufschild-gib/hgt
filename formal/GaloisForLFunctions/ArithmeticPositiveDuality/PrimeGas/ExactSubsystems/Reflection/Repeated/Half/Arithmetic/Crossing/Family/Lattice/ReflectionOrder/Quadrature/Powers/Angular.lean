import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Fit
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Common

/-! # Exact angular gain of a finite prime-power measurement -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers

open Finset Real Set

variable {I : Type*} [Fintype I] [Nonempty I]

def angular (k : I → ℕ+) (y : ℝ) := peak fun i => |cos ((k i : ℝ)*y)|

def gain (k : I → ℕ+) := sin (π/2*defect k)

private theorem sine_mono {u v : ℝ} (hu : 0≤u) (hv : v≤1) (h : u≤v) :
    sin (π/2*u) ≤ sin (π/2*v) := by
  have hp := Real.pi_pos
  apply strictMonoOn_sin.monotoneOn
  · exact ⟨by nlinarith only [mul_nonneg (le_of_lt hp) hu,hp],
      by nlinarith only [mul_nonneg hp.le (show 0≤1-u by linarith only [h,hv])]⟩
  · exact ⟨by nlinarith only [mul_nonneg hp.le (hu.trans h),hp],
      by nlinarith only [mul_nonneg hp.le (sub_nonneg.mpr hv)]⟩
  · exact mul_le_mul_of_nonneg_left h (by positivity)

private theorem lifted_cos (v : ℝ) (j : ℕ) (h : |v-(2*(j : ℝ)+1)|≤1) :
    |cos (π/2*v)|=sin (π/2*|v-(2*(j : ℝ)+1)|) := by
  let e := v-(2*(j : ℝ)+1)
  have arg : π/2*v=(π/2+π/2*e)+(j : ℝ)*π := by dsimp [e]; ring
  have small : π/2*|e|≤π := by
    have hle := mul_le_mul_of_nonneg_left h (show 0≤π/2 by positivity)
    change π/2*|e|≤π/2*1 at hle
    linarith only [hle,pi_pos]
  have pos := sin_nonneg_of_nonneg_of_le_pi (mul_nonneg (by positivity : 0≤π/2) (abs_nonneg e)) small
  change |cos (π/2*v)|=sin (π/2*|e|)
  rw [arg,cos_add_nat_mul_pi,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    cos_add,cos_pi_div_two,sin_pi_div_two,zero_mul,one_mul,zero_sub,abs_neg]
  rcases le_total 0 e with he | he
  · rw [abs_of_nonneg he] at pos ⊢; exact abs_of_nonneg pos
  · rw [abs_of_nonpos he,mul_neg,sin_neg] at pos ⊢
    exact abs_of_nonpos (by linarith only [pos])

private theorem reduce_phase (n : ℕ) (y : ℝ) :
    |cos ((n : ℝ)*y)|=|cos (π/2*((n : ℝ)*(2*Int.fract (y/π))))| := by
  let b := ⌊y/π⌋
  have eq : (n : ℝ)*y=π/2*((n : ℝ)*(2*Int.fract (y/π)))+((n : ℤ)*b : ℤ)*π := by
    have h := Int.fract_add_floor (y/π)
    have prod := congrArg (fun t : ℝ => t*π) h
    rw [div_mul_cancel₀ _ pi_ne_zero] at prod
    dsimp only [b]
    push_cast
    linear_combination (n : ℝ)*prod.symm
  rw [eq,cos_add_int_mul_pi,abs_mul,abs_zpow,abs_neg,abs_one,one_zpow,one_mul]

omit [Fintype I] [Nonempty I] in
private theorem nearest (k : I → ℕ+) (t : ℝ) (lo : 0≤t) (hi : t<1) :
    ∃ a : Centers k, ∀ i, |(k i : ℝ)*(2*t)-oddCenter k a i|≤1 := by
  have bounds (i : I) : (0 : ℝ)≤(k i : ℝ)*t ∧ (k i : ℝ)*t<(k i : ℝ) := by
    have pos : 0<(k i : ℝ) := Nat.cast_pos.mpr (k i).pos
    exact ⟨mul_nonneg pos.le lo,by simpa only [mul_one] using mul_lt_mul_of_pos_left hi pos⟩
  let a : Centers k := fun i => ⟨⌊(k i : ℝ)*t⌋₊, (Nat.floor_lt (bounds i).1).mpr (bounds i).2⟩
  refine ⟨a,fun i => ?_⟩
  have le := Nat.floor_le (bounds i).1
  have lt := Nat.lt_floor_add_one ((k i : ℝ)*t)
  change |(k i : ℝ)*(2*t)-(2*(⌊(k i : ℝ)*t⌋₊ : ℝ)+1)|≤1
  exact abs_le.mpr ⟨by linarith only [le],by linarith only [lt]⟩

/-- The finite determinant formula bounds every phase from below. -/
theorem gain_le (k : I → ℕ+) (y : ℝ) : gain k ≤ angular k y := by
  let t := Int.fract (y/π)
  obtain ⟨a,near⟩ := nearest k t (Int.fract_nonneg _) (Int.fract_lt_one _)
  let err (i : I) := |(k i : ℝ)*(2*t)-oddCenter k a i|
  have lower : defect k ≤ peak err := (defect_le k a).trans
    ((fit_iff k (oddCenter k a) _).mp ⟨2*t,to_peak err⟩)
  obtain ⟨i,att⟩ := peak_value err
  rw [att] at lower
  have sine := sine_mono (defect_range k).1 (near i) lower
  have trig := lifted_cos ((k i : ℝ)*(2*t)) (a i).val (near i)
  change _=sin (π/2*err i) at trig
  rw [←trig,←reduce_phase] at sine
  exact sine.trans (to_peak (fun j => |cos ((k j : ℝ)*y)|) i)

/-- Some actual phase attains the arithmetic bound. -/
theorem attain_gain (k : I → ℕ+) : ∃ y, angular k y=gain k := by
  obtain ⟨a,u,hu⟩ := defect_witness k
  refine ⟨π/2*u,le_antisymm (peak_le.mpr fun i => ?_) (gain_le k _)⟩
  rw [show (k i : ℝ)*(π/2*u)=π/2*((k i : ℝ)*u) by ring,
    lifted_cos _ (a i).val ((hu i).trans (defect_range k).2)]
  exact sine_mono (abs_nonneg _) (defect_range k).2 (hu i)

theorem angular_zero (k : I → ℕ+) (y : ℝ) :
    angular k y=0 ↔ ∀ i, cos ((k i : ℝ)*y)=0 := by
  constructor
  · intro hz i
    exact abs_nonpos_iff.mp ((to_peak (fun j => |cos ((k j : ℝ)*y)|) i).trans_eq hz)
  · intro h
    obtain ⟨i,hi⟩ := peak_value (fun j => |cos ((k j : ℝ)*y)|)
    exact hi.trans (by rw [h i,abs_zero])

/-- The gain is zero precisely when all the angular zeros can coincide. -/
theorem zero_gain (k : I → ℕ+) :
    gain k=0 ↔ ∀ i j, (k i : ℕ).factorization 2=(k j : ℕ).factorization 2 := by
  obtain ⟨y,hit⟩ := attain_gain k
  constructor
  · intro zero
    exact ((common_phases k y).mp ((angular_zero k y).mp (hit.trans zero))).1
  · intro same
    let g : ℝ := fundamental k
    have pos : 0<g := Nat.cast_pos.mpr (fundamental_pos k)
    have zero := (common_phases k (π/(2*g))).mpr ⟨same,0,by
      change g*(π/(2*g))=(2*((0 : ℤ) : ℝ)+1)*π/2
      push_cast
      field_simp
      ring⟩
    have lo : 0≤angular k y := (abs_nonneg _).trans
      (to_peak (fun j => |cos ((k j : ℝ)*y)|) (Classical.choice inferInstance))
    exact le_antisymm ((gain_le k _).trans_eq ((angular_zero _ _).mpr zero)) (lo.trans_eq hit)

theorem gain_nonneg (k : I → ℕ+) : 0 ≤ gain k := by
  obtain ⟨y,hit⟩ := attain_gain k
  exact ((abs_nonneg _).trans (to_peak (fun j => |cos ((k j : ℝ)*y)|)
    (Classical.choice inferInstance))).trans_eq hit

theorem positive_iff (k : I → ℕ+) :
    0 < gain k ↔ ∃ i j, (k i : ℕ).factorization 2≠(k j : ℕ).factorization 2 := by
  rw [lt_iff_le_and_ne, and_iff_right (gain_nonneg k), ne_comm, ne_eq,zero_gain]
  simp only [not_forall]

#print axioms gain_nonneg
#print axioms positive_iff
#print axioms gain_le
#print axioms attain_gain
#print axioms angular_zero
#print axioms zero_gain

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers
