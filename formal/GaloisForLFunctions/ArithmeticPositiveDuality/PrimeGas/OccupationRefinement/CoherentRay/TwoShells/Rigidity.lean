import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay.Duality
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay.TwoShells.Radical
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay.TwoShells.Periods

/-! # Exact classification of all dual partners on two occupation shells -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay.TwoShells

open ModeCapacities
open scoped ComplexConjugate

def double (w s : ℂ) (u v : ℕ → ℝ) (p : Nat.Primes) :=
  rayOverlap w s u v p 1=1 ∧ rayOverlap w s u v p 2=1

def lattice (z : ℂ) := ∃ k : ℤ, z=1+((2*Real.pi*(k:ℝ)/Real.log 2:ℝ):ℂ)*Complex.I

theorem dyadic_iff (z : ℂ) : power z 2=2 ↔ lattice z := by
  have pos : 0<Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · intro h
    have re := real_part h
    obtain ⟨k,hk⟩ := (locked_iff re (by norm_num : 0<(2:ℝ))).mp (by simpa using h)
    refine ⟨k,Complex.ext ?_ ?_⟩
    · simpa only [Complex.add_re,Complex.one_re,Complex.mul_I_re,Complex.ofReal_im,neg_zero,add_zero] using re
    · simpa only [Complex.add_im,Complex.one_im,Complex.mul_I_im,Complex.ofReal_re,zero_add] using
        (eq_div_iff pos.ne').mpr hk
  · rintro ⟨k,rfl⟩
    let t := 2*Real.pi*(k:ℝ)/Real.log 2
    have re : (1+(t:ℂ)*Complex.I).re=1 := by simp
    have im : (1+(t:ℂ)*Complex.I).im=t := by simp
    have fixed := (locked_iff re (by norm_num : 0<(2:ℝ))).mpr
      ⟨k,by rw [im]; exact div_mul_cancel₀ _ pos.ne'⟩
    simpa only [Complex.ofReal_ofNat] using fixed

private theorem read_iff (w s : ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (p : Nat.Primes) :
    double w s u v p ↔ power (conj w+s) (share u v p)+power (conj w+s) (share v u p)=1 ∧
      power (conj w+s) 2=2 := by
  simp only [double,ray_polynomial w s hu hv,polynomial_one,polynomial_two]
  let a := power (conj w+s) (share u v p)
  let b := power (conj w+s) (share v u p)
  let c := power (conj w+s) 2
  change (a+b=1 ∧ a^2+c*a*b+b^2=1) ↔ a+b=1 ∧ c=2
  constructor
  · rintro ⟨h,j⟩
    have zero : (c-2)*(a*b)=0 := by
      calc _ = (a^2+c*a*b+b^2)-(a+b)^2 := by ring
           _ = 0 := by rw [j,h]; norm_num
    exact ⟨h,sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_right (mul_ne_zero (power_ne _ _) (power_ne _ _)))⟩
  · rintro ⟨h,hc⟩
    refine ⟨h,?_⟩
    rw [hc]
    calc _ = (a+b)^2 := by ring
         _ = 1 := by rw [h,one_pow]

private theorem reciprocal {z : ℂ} {c : ℝ} (hc : 0<c) (h : power z c=(c:ℂ)) :
    power z c⁻¹=(c⁻¹:ℝ) := by
  have eqn := power_mul z hc (inv_pos.mpr hc)
  rw [mul_inv_cancel₀ hc.ne',unit_power,h] at eqn
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne')
  rw [←eqn,Complex.ofReal_inv,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne')]

private theorem equal_shares {z : ℂ} {x y : ℝ} (hx : 0<x) (hy : 0<y) (sum : x+y=1)
    (two : power z 2=2) (read : power z x+power z y=1) (ne : z≠1) : x=y := by
  have re := real_part two
  have ht : z.im≠0 := fun h => ne (Complex.ext re (by simpa only [Complex.one_im] using h))
  obtain ⟨left,right⟩ := aligned_shares re hx hy sum read
  obtain ⟨m,hm,root⟩ := locked_is_power re ht (by norm_num : 1<(2:ℝ)) (by simpa only [Complex.ofReal_ofNat] using two)
  have larger {c : ℝ} (hc : 0<c) (lt : c<1) (fixed : power z c=(c:ℂ)) :
      ∃ j : ℕ, c*radius z^j=1 := by
    have inv : 1<c⁻¹ := (one_lt_inv₀ hc).mpr lt
    obtain ⟨j,_,hj⟩ := locked_is_power re ht inv (reciprocal hc fixed)
    exact ⟨j,by rw [hj,mul_inv_cancel₀ hc.ne']⟩
  obtain ⟨j,hj⟩ := larger hx (by linarith only [sum,hy]) left
  obtain ⟨k,hk⟩ := larger hy (by linarith only [sum,hx]) right
  exact complementary_powers ⟨2,Nat.prime_two⟩ hm (Real.exp_pos _) root sum hj hk

/-- Two occupations already determine the dual at every unbalanced split.
At balance the complete ambiguity is the logarithmic period lattice of two. -/
theorem double_iff (w s : ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (p : Nat.Primes) :
    double w s u v p ↔ w=1-conj s ∨ share u v p=1/2 ∧ lattice (conj w+s) := by
  constructor
  · intro h
    obtain ⟨r,two⟩ := (read_iff w s hu hv p).mp h
    by_cases nz : conj w+s=1
    · have partner : conj w=1-s := eq_sub_of_add_eq nz
      exact Or.inl (by simpa only [map_sub,map_one,Complex.conj_conj] using congrArg conj partner)
    · have eqn := equal_shares (share_pos hu hv p) (share_pos hv hu p) (share_sum hu hv p) two r nz
      exact Or.inr ⟨by linarith only [eqn,share_sum hu hv p],(dyadic_iff _).mp two⟩
  · rintro (partner|⟨half,period⟩)
    · have h := (triple_iff w s hu hv p).mpr partner
      exact ⟨h.1,h.2.1⟩
    · have other : share v u p=1/2 := by linarith only [half,share_sum hu hv p]
      have two := (dyadic_iff _).mpr period
      have halfPower := power_mul (conj w+s) (by norm_num : 0<(2:ℝ)) (by norm_num : 0<(1/2:ℝ))
      rw [show (2:ℝ)*(1/2)=1 by norm_num,unit_power,two] at halfPower
      apply (read_iff w s hu hv p).mpr
      exact ⟨by rw [half,other,←two_mul]; exact halfPower.symm,two⟩

#print axioms dyadic_iff
#print axioms double_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay.TwoShells
