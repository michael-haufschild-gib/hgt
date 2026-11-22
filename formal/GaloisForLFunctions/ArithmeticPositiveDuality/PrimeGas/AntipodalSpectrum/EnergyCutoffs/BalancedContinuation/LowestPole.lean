import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedContinuation.PartitionPoles
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ResidueRecovery

/-!
# Recovering the occupation radix from a pole height

The first return is a genuine pole and every other positive pole occurs
at an integer multiple of its height. This one height therefore recovers
the radix, the least rejected product, and the current winding order.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedContinuation

/-- Observable heights of positive simple poles on the isometric split line. -/
def heights (t : ExceptionalTime) (j : ℕ) : Set ℝ :=
  {v | 0 < v ∧ meromorphicOrderAt (continuation t j) ⟨1/2,v⟩ = (-1:ℤ)}

theorem lowest_pole_height (t : ExceptionalTime) (j : ℕ) :
    IsLeast (heights t j) (Real.pi/(logRadix t j).val) := by
  let ω := Real.pi/(logRadix t j).val
  have hω : 0 < ω := div_pos Real.pi_pos (logRadix t j).property
  refine ⟨⟨hω,?_⟩,?_⟩
  · simpa only [clockPoint,Int.cast_one,one_mul] using first_clock_poles t j ⟨1,Or.inr (Or.inl rfl)⟩
  · rintro v ⟨hv,hp⟩
    let z : ℂ := ⟨1/2,v⟩
    have hneg : meromorphicOrderAt (continuation t j) z < 0 := by
      change meromorphicOrderAt (continuation t j) ⟨1/2,v⟩ < 0
      rw [hp]
      exact WithTop.coe_lt_coe.mpr (by norm_num : (-1:ℤ) < 0)
    obtain ⟨k,hk,_⟩ := (pole_locus t j ⟨z,by change -(1/2:ℝ) < 1/2; norm_num⟩).mp hneg
    have he : v = (k:ℝ)*ω := congrArg Complex.im hk
    have hkp : 0 < (k:ℝ) := pos_of_mul_pos_left (he ▸ hv) hω.le
    have hki : (1:ℤ) ≤ k := by
      have : (0:ℤ) < k := by exact_mod_cast hkp
      omega
    rw [he]
    exact le_mul_of_one_le_left hω.le (by exact_mod_cast hki)

/-- Invert the least measured height to recover the radix without a temperature calibration. -/
theorem radix_from_lowest_pole (t : ExceptionalTime) (j : ℕ)
    (v : {v : ℝ // IsLeast (heights t j) v}) :
    Real.exp (Real.pi/v.val) = (radix t j:ℝ) := by
  rw [v.property.unique (lowest_pole_height t j)]
  rw [div_div_cancel₀ Real.pi_ne_zero]
  change Real.exp (Real.log (radix t j:ℝ)) = _
  exact Real.exp_log (by exact_mod_cast (tailRadix t j).pos)

/-- Equal lowest positive pole heights identify the least product and current winding order. -/
theorem lowest_pole_recovers_parameters (t u : ExceptionalTime) (j i : ℕ)
    (v : {v : ℝ // IsLeast (heights t j) v})
    (w : {w : ℝ // IsLeast (heights u i) w}) :
    v.val = w.val ↔ block t = block u ∧ 2^j*windingOrder t = 2^i*windingOrder u := by
  constructor
  · intro h
    have hr := (radix_from_lowest_pole t j v).symm.trans
      ((congrArg (fun x : ℝ => Real.exp (Real.pi/x)) h).trans (radix_from_lowest_pole u i w))
    apply (critical_coefficient_eq_across_levels t u j i).mp
    change 2/((radix t j:ℝ)-1) = 2/((radix u i:ℝ)-1)
    rw [hr]
  · rintro ⟨hb,hm⟩
    rw [v.property.unique (lowest_pole_height t j),w.property.unique (lowest_pole_height u i)]
    simp only [logRadix,energy,tailRadix,(refined_parameters t j).2.2,
      (refined_parameters u i).2.2,hb,hm]

#print axioms lowest_pole_height
#print axioms radix_from_lowest_pole
#print axioms lowest_pole_recovers_parameters

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedContinuation
