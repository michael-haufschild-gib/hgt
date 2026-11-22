import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.PrimitivePhase
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.AntipodalEigenspace

/-!
# Halving the clock on the lowest shell

Every old rejection lies on a ray of either new least word. Nonempty old
rejection forces that primitive phase to remain nontrivial after squaring.
The least shell is therefore unchanged, and its orbit length doubles.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open SampledClocks DyadicAperture DyadicAperture.Binary

def halfClock (t : ExceptionalTime) : ExceptionalTime := ⟨t.val/2,by
  obtain ⟨x,hx⟩ := t.property
  exact ⟨x,rejected_nested _ _ (by rwa [show 2*(t.val/2) = t.val by ring])⟩⟩

theorem twice_halfClock (t : ExceptionalTime) : 2*(halfClock t).val = t.val := by change 2*(t.val/2) = _; ring

theorem half_inclusion (t : ExceptionalTime) (x : Word) : rejected t.val x → rejected (halfClock t).val x :=
  fun h => rejected_nested _ _ (by rwa [twice_halfClock])

theorem phase_square (t : ExceptionalTime) (x : Word) :
    (binary t.val).phase () x = ((binary (halfClock t).val).phase () x)^2 := by
  change Circle.exp (t.val*gap (x false) (x true)) = (Circle.exp ((t.val/2)*gap (x false) (x true)))^2
  rw [← Circle.exp_natCast_mul]
  congr 1
  push_cast
  ring

private theorem least_survives_squaring (t : ExceptionalTime) (x : leastWords (halfClock t)) : rejected t.val x.val := by
  obtain ⟨y,hy⟩ := t.property
  obtain ⟨r,k,n,he⟩ := (least_support _ x y).mp (half_inclusion t y hy)
  have hz : (binary t.val).phase () x.val ≠ 1 := by
    intro hone
    have hn := ((misses_iff_return _).mp ((rejected_iff _ _).mp hy)).2
    apply hn
    rw [he,ray_phase]
    change (if r then (((binary t.val).phase () x.val)^k.val)⁻¹ else ((binary t.val).phase () x.val)^k.val) = 1
    simp [hone]
  apply (rejected_iff _ _).mpr
  apply (misses_iff_return _).mpr
  refine ⟨?_,hz⟩
  obtain ⟨⟨j,hj⟩,_⟩ := (misses_iff_return _).mp ((rejected_iff _ _).mp x.property.1)
  exact ⟨j,by rw [phase_square,← pow_mul,mul_comm,pow_mul,hj,one_pow]⟩

theorem half_block (t : ExceptionalTime) : block (halfClock t) = block t := by
  obtain ⟨x,hx⟩ := leastWords_nonempty t
  obtain ⟨y,hy⟩ := leastWords_nonempty (halfClock t)
  exact le_antisymm ((block_least _).2 ⟨x,half_inclusion t x hx.1,hx.2⟩)
    ((block_least t).2 ⟨y,least_survives_squaring t ⟨y,hy⟩,hy.2⟩)

/-- Equality of actual least occupations, including their ordered labels. -/
theorem half_leastWords (t : ExceptionalTime) : leastWords (halfClock t) = leastWords t := by
  ext x
  constructor
  · intro hx
    exact ⟨least_survives_squaring t ⟨x,hx⟩,hx.2.trans (half_block t)⟩
  · intro hx
    exact ⟨half_inclusion t _ hx.1,hx.2.trans (half_block t).symm⟩

theorem half_windingOrder (t : ExceptionalTime) : windingOrder (halfClock t) = 2*windingOrder t := by
  obtain ⟨x,hx⟩ := leastWords_nonempty t
  have hh : x ∈ leastWords (halfClock t) := (half_leastWords t).symm ▸ hx
  obtain ⟨j,hj⟩ := order_dyadic (halfClock t)
  have hd : 2 ∣ windingOrder (halfClock t) := by
    cases j with
    | zero => exact ((order_nontrivial _).ne' (hj.trans (pow_zero 2))).elim
    | succ j => exact ⟨2^j,hj.trans (pow_succ' 2 j)⟩
  have hs := (least_phase_order t ⟨x,hx⟩).symm
  change windingOrder t = orderOf ((binary t.val).phase () x) at hs
  rw [phase_square,orderOf_pow' _ two_ne_zero] at hs
  have ho := least_phase_order (halfClock t) ⟨x,hh⟩
  change orderOf ((binary (halfClock t).val).phase () x) = _ at ho
  rw [ho,Nat.gcd_eq_right hd] at hs
  exact (Nat.div_mul_cancel hd).symm.trans ((congrArg (·*2) hs.symm).trans (Nat.mul_comm _ _))

private theorem new_index {m k : ℕ} (hm : 0 < m) : (m ∣ k ∧ ¬2*m ∣ k) ↔ ∃ j : ℕ, k = m*(2*j+1) := by
  have even (l : ℕ) : 2*m ∣ m*l ↔ 2 ∣ l := by rw [Nat.mul_comm 2 m]; exact Nat.mul_dvd_mul_iff_left hm
  constructor
  · rintro ⟨⟨l,rfl⟩,h⟩
    have hodd : ¬2 ∣ l := fun he => h ((even l).mpr he)
    exact ⟨l/2,congrArg (m*·) (by omega)⟩
  · rintro ⟨j,rfl⟩
    exact ⟨dvd_mul_right _ _,fun h => (show ¬2 ∣ 2*j+1 by omega) ((even _).mp h)⟩

/-- Full support of the added antipodal eigenspace in the original primitive coordinates. -/
theorem half_additional_rays (t : ExceptionalTime) (x : leastWords t) (y : Word) :
    additional (halfClock t).val y ↔ ∃ (r : Bool) (j : ℕ) (n : ℕ+),
      y = ray (x.val false) (x.val true) r (windingOrder t*(2*j+1)) n := by
  have hh : x.val ∈ leastWords (halfClock t) := (half_leastWords t).symm ▸ x.property
  let v : leastWords (halfClock t) := ⟨x.val,hh⟩
  have hm : 0 < windingOrder t := Nat.zero_lt_one.trans (order_nontrivial t)
  change rejected (halfClock t).val y ∧ ¬rejected (2*(halfClock t).val) y ↔ _
  rw [twice_halfClock]
  constructor
  · rintro ⟨hy,hn⟩
    obtain ⟨r,k,n,he⟩ := (least_support _ v y).mp hy
    have hd : windingOrder t ∣ k.val := Classical.byContradiction fun h => hn (by rw [he]; exact (least_ray_rejected t x r k.val n).mpr h)
    have hnew := k.property
    change ¬windingOrder (halfClock t) ∣ k.val at hnew
    have hn' : ¬2*windingOrder t ∣ k.val := fun h => hnew ((half_windingOrder t).symm ▸ h)
    obtain ⟨j,hj⟩ := (new_index hm).mp ⟨hd,hn'⟩
    exact ⟨r,j,n,he.trans (congrArg (fun l => ray (x.val false) (x.val true) r l n) hj)⟩
  · rintro ⟨r,j,n,rfl⟩
    obtain ⟨hd,hn⟩ := (new_index hm).mpr ⟨j,rfl⟩
    refine ⟨(least_ray_rejected _ v r _ n).mpr ?_,fun h => ((least_ray_rejected t x r _ n).mp h) hd⟩
    rwa [half_windingOrder]

#print axioms half_block
#print axioms half_leastWords
#print axioms half_windingOrder
#print axioms half_additional_rays

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
