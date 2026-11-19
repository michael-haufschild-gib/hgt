import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.AlternatingCornersOfTheProperPowerHorizon
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheHalfEndpointChargeOfADilatedLattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The constant term of the proper-power horizon

The leading coefficient is the reciprocal square-root octave. The
floor loss tends to one half of the entire proper-power octave mass,
with an inverse-horizon error uniform across the alternating corners.
-/

noncomputable section
open Filter Finset MeasureTheory GaloisForLFunctions.ClippedLattice
open scoped Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def curve (x : ℝ) := x^(-(1/2:ℝ))-1
private def curve' (x : ℝ) := -(1/2:ℝ)*x^(-(3/2:ℝ))
private def curve'' (x : ℝ) := (3/4:ℝ)*x^(-(5/2:ℝ))

private theorem curve_deriv (x : ℝ) (hx : x ∈ Set.Icc (1/2:ℝ) 1) :
    HasDerivAt curve (curve' x) x := by
  dsimp only [curve,curve']
  convert (Real.hasDerivAt_rpow_const (x:=x) (p:= -(1/2:ℝ)) (Or.inl
    (by linarith only [hx.1] : x ≠ 0))).sub_const 1 using 1 <;> norm_num

private theorem curve_second (x : ℝ) (hx : x ∈ Set.Icc (1/2:ℝ) 1) :
    HasDerivAt curve' (curve'' x) x := by
  dsimp only [curve',curve'']
  convert (Real.hasDerivAt_rpow_const (x:=x) (p:= -(3/2:ℝ)) (Or.inl
    (by linarith only [hx.1] : x ≠ 0))).const_mul (-(1/2:ℝ)) using 1 <;> norm_num <;> ring

private theorem curve_smooth : ContinuousOn curve'' (Set.Icc (1/2:ℝ) 1) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  dsimp only [curve'']
  apply continuousAt_const.mul
  exact (Real.hasDerivAt_rpow_const (Or.inl (by linarith only [hx.1] : x ≠ 0))).continuousAt

private theorem curve_endpoints : curve 1=0 ∧ curve (1/2)=Real.sqrt 2-1 := by
  constructor
  · simp [curve]
  · rw [curve,Real.rpow_neg (by norm_num : (0:ℝ)≤1/2),←Real.sqrt_eq_rpow,
      Real.sqrt_div zero_le_one,Real.sqrt_one,one_div,inv_inv]

private theorem int_sum_nat (a b : ℕ) (f : ℝ → ℝ) :
    ∑ z ∈ Ioc (a:ℤ) (b:ℤ), f z = ∑ j ∈ Ioc a b, f j := by
  symm
  apply sum_bij (fun j _ => (j:ℤ))
  · intro j hj
    have := mem_Ioc.mp hj
    exact mem_Ioc.mpr ⟨by omega,by omega⟩
  · intro _ _ _ _ _; omega
  · intro z hz
    have := mem_Ioc.mp hz
    exact ⟨z.toNat,mem_Ioc.mpr ⟨by omega,by omega⟩,by omega⟩
  · intro _ _; simp only [Int.cast_natCast]

private theorem reading_is_profile {t : ℝ} (ht : 0<t) :
    reading curve t = properHorizonProfile t := by
  let n := ⌊t⌋₊
  have hn : (n:ℝ)≤t := Nat.floor_le ht.le
  have hu : t≤(n:ℝ)+1 := (Nat.lt_floor_add_one t).le
  rw [proper_profile_on_unit_cell n hn hu,reading,curve_endpoints.2,
    ←Int.natCast_floor_eq_floor (by positivity : 0≤t/2),←Int.natCast_floor_eq_floor ht.le,
    Int.cast_natCast,show ⌊t/2⌋₊=n/2 from Nat.floor_div_natCast (a:=t) (n:=2),int_sum_nat]
  have row (j : ℕ) (_ : j∈Ioc (n/2) n) : curve ((j:ℝ)/t) = Real.sqrt t*(Real.sqrt j)⁻¹-1 := by
    rw [curve,Real.rpow_neg (by positivity : 0≤(j:ℝ)/t),←Real.sqrt_eq_rpow,
      Real.sqrt_div (Nat.cast_nonneg j),inv_div,div_eq_mul_inv]
  change _+(∑ j ∈ Ioc (n/2) n,curve ((j:ℝ)/t))=_
  rw [sum_congr rfl row,sum_sub_distrib,←mul_sum,sum_const,Nat.card_Ioc,nsmul_eq_mul,mul_one,properHorizonSlope]
  ring

private theorem curve_density : density curve = 1-1/Real.sqrt 2 := by
  have hi : IntervalIntegrable (fun x : ℝ => x^(-(1/2:ℝ))) volume (1/2:ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    intro x hx
    exact (Real.hasDerivAt_rpow_const (Or.inl (by linarith only [hx.1] : x ≠ 0))).continuousAt.continuousWithinAt
  rw [density,curve_endpoints.2]
  unfold curve
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const,integral_rpow (Or.inl (by norm_num)),
    intervalIntegral.integral_const,smul_eq_mul,show -(1/2:ℝ)+1=1/2 by norm_num,
    ←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow,Real.sqrt_one,Real.sqrt_div zero_le_one,Real.sqrt_one]
  have h := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  field_simp [Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2) |>.ne']
  <;> nlinarith only [h]

/-- The floor loss of the proper-power profile is half the whole
square-root octave mass, with a uniform O(1/t) remainder. -/
theorem proper_horizon_constant_error :
    ∃ K : ℝ, 0≤K ∧ ∀ {t : ℝ}, 0<t →
      |properHorizonProfile t-t*(1-1/Real.sqrt 2)+(Real.sqrt 2-1)/2| ≤ K/t := by
  obtain ⟨K,hK,h⟩ := clipped_lattice_error curve_deriv curve_second curve_smooth
  refine ⟨K,hK,fun {t} ht => ?_⟩
  simpa only [reading_is_profile ht,curve_density,curve_endpoints.1,curve_endpoints.2,zero_mul,sub_zero] using h ht

/-- The constant term persists through arbitrary nonintegral horizons. -/
theorem proper_horizon_constant_term :
    Tendsto (fun t : ℝ => properHorizonProfile t-t*(1-1/Real.sqrt 2)) atTop
      (𝓝 (-(Real.sqrt 2-1)/2)) := by
  have h := clipped_lattice_constant curve_deriv curve_second curve_smooth curve_endpoints.1
  rw [curve_endpoints.2,←neg_div] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  rw [reading_is_profile ht,curve_density]

#print axioms proper_horizon_constant_error
#print axioms proper_horizon_constant_term
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
