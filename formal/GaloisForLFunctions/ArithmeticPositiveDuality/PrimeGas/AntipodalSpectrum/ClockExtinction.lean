import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ClockHalving

/-!
# Detecting the last nonempty clock reading

At dyadic multiples of an exceptional time, one least word detects whether
the entire rejection has disappeared. The first empty level recovers the
winding order as a power of two.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open SampledClocks DyadicAperture DyadicAperture.Binary

private theorem coarse_phase (t : ℝ) (j : ℕ) (x : Word) :
    (binary ((2:ℝ)^j*t)).phase () x = ((binary t).phase () x)^(2^j : ℕ) := by
  change Circle.exp (((2:ℝ)^j*t)*gap (x false) (x true)) =
    (Circle.exp (t*gap (x false) (x true)))^(2^j : ℕ)
  rw [← Circle.exp_natCast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_assoc]

theorem coarsened_rejection (t : ℝ) (j : ℕ) (x : Word) :
    rejected ((2:ℝ)^j*t) x ↔ rejected t x ∧ ((binary t).phase () x)^(2^j : ℕ) ≠ 1 := by
  rw [rejected_iff,rejected_iff,misses_iff_return,misses_iff_return,coarse_phase]
  let z := (binary t).phase () x
  change (DyadicReturn (z^(2^j : ℕ)) ∧ z^(2^j : ℕ) ≠ 1) ↔ (DyadicReturn z ∧ z ≠ 1) ∧ z^(2^j : ℕ) ≠ 1
  constructor
  · rintro ⟨⟨k,hk⟩,hn⟩
    exact ⟨⟨⟨j+k,by rwa [pow_add,pow_mul]⟩,fun he => hn (by rw [he,one_pow])⟩,hn⟩
  · rintro ⟨⟨⟨k,hk⟩,_⟩,hn⟩
    exact ⟨⟨k,by rw [← pow_mul,mul_comm,pow_mul,hk,one_pow]⟩,hn⟩

private theorem primitive_survives (t : ExceptionalTime) (j : ℕ) (x : leastWords t) :
    rejected ((2:ℝ)^j*t.val) x.val ↔ ¬ windingOrder t ∣ 2^j := by
  rw [coarsened_rejection,and_iff_right x.property.1,← least_phase_order t x]
  exact not_congr orderOf_dvd_iff_pow_eq_one.symm

/-- One original least word tests the simultaneous disappearance of every rejected word. -/
theorem least_detects_extinction (t : ExceptionalTime) (j : ℕ) (x : leastWords t) :
    (2:ℝ)^j*t.val ∈ exceptional ↔ rejected ((2:ℝ)^j*t.val) x.val := by
  refine ⟨?_,fun h => ⟨x.val,h⟩⟩
  rintro ⟨y,hy⟩
  obtain ⟨ho,hn⟩ := (coarsened_rejection t.val j y).mp hy
  obtain ⟨r,k,n,he⟩ := (least_support t x y).mp ho
  apply (primitive_survives t j x).mpr
  intro hd
  have hz : ((binary t.val).phase () x.val)^(2^j : ℕ) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rw [least_phase_order t x]; exact hd)
  rw [he,ray_phase] at hn
  let z := (binary t.val).phase () x.val
  have hp : (z^k.val)^(2^j : ℕ) = 1 := by
    rw [← pow_mul,mul_comm,pow_mul,show z^(2^j : ℕ) = 1 from hz,one_pow]
  cases r
  · exact hn hp
  · apply hn
    change ((z^k.val)⁻¹)^(2^j : ℕ) = 1
    rw [inv_pow,hp,inv_one]

theorem clock_extinction (t : ExceptionalTime) :
    ∃ d : ℕ, windingOrder t = 2^d ∧ ∀ j : ℕ, (2:ℝ)^j*t.val ∈ exceptional ↔ j < d := by
  obtain ⟨d,hd⟩ := order_dyadic t
  obtain ⟨x,hx⟩ := leastWords_nonempty t
  refine ⟨d,hd,fun j => ?_⟩
  rw [least_detects_extinction t j ⟨x,hx⟩,primitive_survives,hd]
  constructor
  · intro h
    exact lt_of_not_ge fun hle => h (Nat.pow_dvd_pow 2 hle)
  · intro h hdiv
    exact (Nat.not_le_of_gt (Nat.pow_lt_pow_right (by norm_num : 1 < 2) h))
      (Nat.le_of_dvd (pow_pos (by norm_num) _) hdiv)

#print axioms coarsened_rejection
#print axioms least_detects_extinction
#print axioms clock_extinction

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
