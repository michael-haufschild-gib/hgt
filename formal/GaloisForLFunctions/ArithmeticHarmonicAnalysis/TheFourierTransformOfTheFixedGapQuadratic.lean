import GaloisForLFunctions.RHTower.ReducedFrequencyMobiusAliasCollapse
import GaloisForLFunctions.RHTower.Sieve.KloostermanRamanujanDivisorSum

/-!
# Fourier transform of the fixed-gap quadratic

The roots of x(x+g)=0 are zero-product pairs with difference g.
Fourier inversion of the product constraint replaces it by the dual
linear equation ux=-j. At unit gap frequency j this forces x to be a
unit, giving the literal Ramanujan sum at the difference of the two
frequencies, for every positive modulus.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Finset
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [Fintype R]

/-- On the annihilator of x the Fourier sum is exactly the cardinality
of a linear congruence fibre. Primitive characters identify the two dual
finite groups without choosing coordinates. -/
theorem annihilator_fourier_count (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (x j : R) :
    (∑ s : R, if x*s=0 then ψ (j*s) else 0) = ((univ.filter (fun u : R => u*x+j=0)).card:ℂ) := by
  let q : ℂ := Fintype.card R
  have hq : q≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply (mul_right_inj' hq).mp
  calc
    q*(∑ s : R, if x*s=0 then ψ (j*s) else 0) =
        ∑ s : R, (∑ u : R, ψ (u*(x*s)))*ψ (j*s) := by
      rw [mul_sum]
      refine sum_congr rfl fun s _ => ?_
      rw [AddChar.sum_mulShift _ hψ]
      by_cases h : x*s=0 <;> simp only [h,if_true,if_false,Nat.cast_zero,mul_zero,zero_mul,q]
    _ = ∑ u : R, ∑ s : R, ψ (s*(u*x+j)) := by
      simp only [sum_mul]
      rw [sum_comm]
      exact sum_congr rfl fun u _ => sum_congr rfl fun s _ => by
        rw [←ψ.map_add_eq_mul]
        exact congrArg ψ (by ring)
    _ = ∑ u : R, if u*x+j=0 then q else 0 := by
      refine sum_congr rfl fun u _ => ?_
      rw [AddChar.sum_mulShift _ hψ]
      by_cases h : u*x+j=0 <;> simp [h,q]
    _ = _ := by rw [←sum_filter,sum_const,nsmul_eq_mul,mul_comm]

/-- Twisted joint transform in the gap and the marked quadratic root. -/
def fixedGapQuadraticTransform (ψ : AddChar R ℂ) (j a : R) : ℂ :=
  ∑ g : R, ∑ x : R, if x*(x+g)=0 then ψ (a*x+j*g) else 0

/-- The full joint transform is a one-dimensional weighted sum over
solutions of ux=-j. This holds even at imprimitive frequencies. -/
theorem fixedGapQuadraticTransform_linear_fibres (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (j a : R) :
    fixedGapQuadraticTransform ψ j a =
      ∑ x : R, ((univ.filter (fun u : R => u*x+j=0)).card:ℂ)*ψ ((a-j)*x) := by
  unfold fixedGapQuadraticTransform
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  let F (s : R) := if x*s=0 then ψ (j*s) else 0
  have hmove : ∑ g : R, F (x+g) = ∑ s : R, F s := Equiv.sum_comp (Equiv.addLeft x) F
  calc
    _ = ∑ g : R, F (x+g)*ψ ((a-j)*x) := sum_congr rfl fun g _ => by
      dsimp only [F]
      split_ifs <;> first | rw [←ψ.map_add_eq_mul]; exact congrArg ψ (by ring) | rw [zero_mul]
    _ = _ := by rw [←sum_mul,hmove]; exact congrArg (·*ψ ((a-j)*x)) (annihilator_fourier_count ψ hψ x j)

private theorem unit_frequency_fibre (j : Rˣ) (x : R) :
    (univ.filter (fun u : R => u*x+(j:R)=0)).card = if IsUnit x then 1 else 0 := by
  by_cases hx : IsUnit x
  · let y := (- (j:R))*(↑hx.unit⁻¹:R)
    have hxy : y*x= -(j:R) := by
      calc
        y*x = -(j:R)*((↑hx.unit⁻¹:R)*(↑hx.unit:R)) := by rw [hx.unit_spec]; exact mul_assoc ..
        _ = _ := by rw [Units.inv_mul,mul_one]
    have hs : univ.filter (fun u : R => u*x+(j:R)=0)={y} := by
      ext u
      simp only [mem_filter,mem_univ,true_and,mem_singleton,add_eq_zero_iff_eq_neg,←hxy,hx.mul_left_inj]
    rw [hs,card_singleton,if_pos hx]
  · have h (u : R) : u*x+(j:R)≠0 := by
      intro he
      have hu : IsUnit (u*x) := (add_eq_zero_iff_eq_neg.mp he).symm ▸ j.isUnit.neg
      exact hx (isUnit_of_mul_isUnit_right hu)
    simp [h,hx]

/-- A unit gap frequency collapses every nilpotent contribution to a
single Ramanujan sum over the units. -/
theorem fixedGapQuadraticTransform_unit (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (j : Rˣ) (a : R) :
    fixedGapQuadraticTransform ψ (j:R) a = ∑ x ∈ univ.filter IsUnit, ψ (x*(a-j)) := by
  rw [fixedGapQuadraticTransform_linear_fibres ψ hψ,sum_filter]
  refine sum_congr rfl fun x _ => ?_
  rw [unit_frequency_fibre]
  by_cases hx : IsUnit x <;> simp [hx,mul_comm]

/-- Fourier transforming the arithmetic root response in the gap gives
the joint transform, at every additive frequency. -/
theorem transform_arithmetic_quadratic_root_sum (M : ℕ+) (j : ZMod (M:ℕ)) (a : ℤ) :
    ∑ g : ZMod (M:ℕ), _root_.RHTower.quadraticCongruenceRootSum (M:ℕ) g.val a *
        ZMod.stdAddChar (j*g) = fixedGapQuadraticTransform ZMod.stdAddChar j (a:ZMod (M:ℕ)) := by
  let R := ZMod (M:ℕ)
  have hroot (g : R) : _root_.RHTower.quadraticCongruenceRootSum (M:ℕ) g.val a =
      ∑ x : R, if x*(x+g)=0 then ZMod.stdAddChar ((a:R)*x) else 0 := by
    unfold _root_.RHTower.quadraticCongruenceRootSum
    rw [←sum_filter]
    symm
    exact sum_subtype (p:=fun x : R => x*(x+((g.val:ℤ):R))=0) _
      (fun x => by simp [R]) _
  refine sum_congr rfl fun g _ => ?_
  rw [hroot,sum_mul]
  refine sum_congr rfl fun x _ => ?_
  by_cases h : x*(x+g)=0 <;> simp only [h,if_true,if_false,zero_mul,AddChar.map_add_eq_mul]

/-- The existing fixed-gap root sums at a unit Fourier frequency, with
arbitrary additive twist a on the roots. -/
theorem arithmetic_quadratic_root_sum_fourier (M : ℕ+) (j : (ZMod (M:ℕ))ˣ) (a : ℤ) :
    ∑ g : ZMod (M:ℕ), _root_.RHTower.quadraticCongruenceRootSum (M:ℕ) g.val a *
        ZMod.stdAddChar ((j:ZMod (M:ℕ))*g) =
      _root_.RHTower.cglRamanujanAdditiveSum ⟨M,M.pos⟩ ((a:ZMod (M:ℕ))-j) := by
  refine (transform_arithmetic_quadratic_root_sum M j a).trans ?_
  refine (fixedGapQuadraticTransform_unit ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar (M:ℕ)) j
    (a:ZMod (M:ℕ))).trans ?_
  unfold _root_.RHTower.cglRamanujanAdditiveSum
  apply Finset.sum_congr
  · ext u
    simp only [mem_filter,mem_univ,true_and]
  · intro u _
    rfl

/-- GCD and Möbius inversion evaluate all primitive gap-frequency
columns, including the zero root twist at nonsquarefree moduli. -/
theorem arithmetic_quadratic_root_fourier_divisors (M : ℕ+) (j : (ZMod (M:ℕ))ˣ) (a : ℤ) :
    let m := (a:ZMod (M:ℕ))-j
    ∑ g : ZMod (M:ℕ), _root_.RHTower.quadraticCongruenceRootSum (M:ℕ) g.val a *
        ZMod.stdAddChar ((j:ZMod (M:ℕ))*g) =
      ∑ d ∈ (m.val.gcd M).divisors, (d:ℂ)*((ArithmeticFunction.moebius ((M:ℕ)/d):ℤ):ℂ) :=
  (arithmetic_quadratic_root_sum_fourier M j a).trans
    (_root_.RHTower.Sieve.cglRamanujanAdditiveSum_eq_gcd_mobiusDivisorSum_sieve _ _)

/-- Every primitive Fourier coefficient of the literal root count is
the Möbius function of the modulus. In particular it vanishes at every
modulus divisible by a prime square. -/
theorem primitive_shear_root_count_fourier (M : ℕ+) (j : (ZMod (M:ℕ))ˣ) :
    ∑ g : ZMod (M:ℕ), (_root_.RHTower.quadraticCongruenceRootCountTotal (M:ℕ) g.val:ℂ) *
        ZMod.stdAddChar ((j:ZMod (M:ℕ))*g) = ((ArithmeticFunction.moebius (M:ℕ):ℤ):ℂ) := by
  have zeroTwist (g : ZMod (M:ℕ)) : _root_.RHTower.quadraticCongruenceRootSum (M:ℕ) g.val 0 =
      (_root_.RHTower.quadraticCongruenceRootCountTotal (M:ℕ) g.val:ℂ) := by
    rw [_root_.RHTower.quadraticCongruenceRootCountTotal_of_ne_zero M.pos.ne']
    simp [_root_.RHTower.quadraticCongruenceRootSum,_root_.RHTower.quadraticCongruenceRootCount]
  have cop : (-(j:ZMod (M:ℕ))).val.Coprime (M:ℕ) :=
    (ZMod.isUnit_iff_coprime _ _).mp (by simpa only [ZMod.natCast_zmod_val] using j.isUnit.neg)
  have h := arithmetic_quadratic_root_fourier_divisors M j 0
  simpa only [Int.cast_zero,zero_sub,zeroTwist,cop.gcd_eq_one,Nat.divisors_one,
    sum_singleton,Nat.cast_one,one_mul,Nat.div_one] using h

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
