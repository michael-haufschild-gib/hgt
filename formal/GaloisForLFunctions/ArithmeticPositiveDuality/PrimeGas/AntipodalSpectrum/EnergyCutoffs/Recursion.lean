import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.RemainderDensity

/-!
# Finite energy cutoffs of the heat-weighted remainder

Removing one radix factor from every shell root separates the first winding
from a complete copy of the occupied states at the quotient cutoff.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open SampledClocks CopyExchange DyadicAperture.Binary

/-- Heat summed over the actual omitted occupations through product X², at temperature parameter w/2. -/
def shellCutoff (t : ExceptionalTime) (j X : ℕ) (w : ℂ) :=
  ∑' u : countingStates t j X, wordHeat (w/2) u.val.val

/-- Finite radial heat sum of the single-copy gas. -/
def radialCutoff (Y : ℕ) (w : ℂ) := ∑ n ∈ Finset.Icc 1 Y, (n:ℂ)^(-w)

private abbrev Rows (C : ℕ+) (X : ℕ) := {p : TailIndex // C.val^(p.2.1+1)*p.2.2.val ≤ X}
private abbrev Radial (Y : ℕ) := ↥(Finset.Icc 1 Y)

private def physicalRows (t : ExceptionalTime) (j X : ℕ) (x : leastWords t) :
    Rows (tailRadix t j) X ≃ countingStates t j X :=
  (tailBasis t j x).subtypeEquiv fun p => by
    change _ ↔ (tailWord t j x p false*tailWord t j x p true).val ≤ X^2
    rw [tail_square,PNat.pow_coe,PNat.mul_coe,PNat.pow_coe]
    exact (Nat.pow_le_pow_iff_left (by norm_num : (2:ℕ) ≠ 0)).symm

private theorem top_row (C : ℕ+) (n : ℕ+) (X : ℕ) : C.val^(0+1)*n.val ≤ X ↔ n.val ≤ X/C.val := by
  rw [Nat.zero_add,pow_one,Nat.mul_comm,Nat.le_div_iff_mul_le C.pos]

private theorem next_row (C : ℕ+) (i : ℕ) (n : ℕ+) (X : ℕ) :
    C.val^((i+1)+1)*n.val ≤ X ↔ C.val^(i+1)*n.val ≤ X/C.val := by
  rw [pow_succ',Nat.mul_assoc,Nat.mul_comm C.val,Nat.le_div_iff_mul_le C.pos]

private def splitRows (C : ℕ+) (X : ℕ) :
    ((Bool × Radial (X/C.val)) ⊕ Rows C (X/C.val)) ≃ Rows C X where
  toFun u := match u with
    | .inl (r,v) =>
      let n : ℕ+ := ⟨v.val,(Finset.mem_Icc.mp v.property).1⟩
      ⟨(r,0,n),(top_row C n X).mpr (Finset.mem_Icc.mp v.property).2⟩
    | .inr v => ⟨(v.val.1,v.val.2.1+1,v.val.2.2),(next_row C _ _ X).mpr v.property⟩
  invFun u := by
    obtain ⟨⟨r,i,n⟩,h⟩ := u
    cases i with
    | zero => exact .inl (r,⟨n.val,Finset.mem_Icc.mpr ⟨n.pos,(top_row C n X).mp h⟩⟩)
    | succ i => exact .inr ⟨(r,i,n),(next_row C i n X).mp h⟩
  left_inv u := by
    rcases u with ⟨r,⟨n,h⟩⟩ | ⟨⟨r,i,n⟩,h⟩ <;> rfl
  right_inv u := by
    obtain ⟨⟨r,i,n⟩,h⟩ := u
    cases i <;> rfl

private def rowHeat (C : ℕ+) (w : ℂ) (p : TailIndex) := (heat w C)^(p.2.1+1)*heat w p.2.2

private theorem cutoff_rows (t : ExceptionalTime) (j X : ℕ) (w : ℂ) :
    shellCutoff t j X w = ∑' p : Rows (tailRadix t j) X, rowHeat (tailRadix t j) w p.val := by
  obtain ⟨x,hx⟩ := leastWords_nonempty t
  let e := physicalRows t j X ⟨x,hx⟩
  rw [shellCutoff,← e.tsum_eq (fun u : countingStates t j X => wordHeat (w/2) u.val.val)]
  refine tsum_congr fun p => ?_
  change wordHeat (w/2) (ray (x false) (x true) p.val.1
    (windingOrder (refined t j)*(p.val.2.1+1)) p.val.2.2) = _
  rw [ray_heat,hx.2,pow_mul,show 2*(w/2) = w by ring]
  change (windingWeight t j (w/2))^(p.val.2.1+1)*heat w p.val.2.2 = _
  rw [winding_half_temperature]
  rfl

/-- One winding removal gives the exact energy-cutoff recursion at every complex temperature. -/
theorem shell_cutoff_recursion (t : ExceptionalTime) (j X : ℕ) (w : ℂ) :
    let C := tailRadix t j
    shellCutoff t j X w = heat w C*(2*radialCutoff (X/C.val) w + shellCutoff t j (X/C.val) w) := by
  classical
  let C := tailRadix t j
  let Y := X/C.val
  obtain ⟨x,hx⟩ := leastWords_nonempty t
  letI : Finite (Rows C Y) := Finite.of_equiv (countingStates t j Y) (physicalRows t j Y ⟨x,hx⟩).symm
  let e := splitRows C X
  let W (v : Rows C X) := rowHeat C w v.val
  have hl (u : Bool × Radial Y) : W (e (.inl u)) = heat w C*(u.2.val:ℂ)^(-w) := by
    change (heat w C)^(0+1)*heat w (⟨u.2.val,_⟩ : ℕ+) = _
    rw [Nat.zero_add,pow_one]
    exact congrArg (heat w C*·) (heat_eq_cpow w ⟨u.2.val,(Finset.mem_Icc.mp u.2.property).1⟩)
  have hr (u : Rows C Y) : W (e (.inr u)) = heat w C*rowHeat C w u.val := by
    change (heat w C)^((u.val.2.1+1)+1)*heat w u.val.2.2 = _
    rw [pow_succ',mul_assoc]
    rfl
  have hb : (∑' n : Radial Y, (n.val:ℂ)^(-w)) = radialCutoff Y w := by
    rw [tsum_fintype]
    exact Finset.sum_coe_sort (Finset.Icc 1 Y) (fun n : ℕ => (n:ℂ)^(-w))
  have hfirst : (∑' u : Bool × Radial Y, W (e (.inl u))) = 2*(heat w C*radialCutoff Y w) := by
    rw [tsum_congr hl,(Summable.of_finite (f := fun u : Bool × Radial Y => heat w C*(u.2.val:ℂ)^(-w))).tsum_prod]
    simp only [tsum_mul_left,tsum_bool,hb,two_mul,mul_add]
  change shellCutoff t j X w = heat w C*(2*radialCutoff Y w + shellCutoff t j Y w)
  rw [cutoff_rows,cutoff_rows t j Y]
  change (∑' u : Rows C X, W u) = heat w C*(2*radialCutoff Y w + ∑' p : Rows C Y, rowHeat C w p.val)
  rw [← e.tsum_eq W,Summable.tsum_sum (f := fun u => W (e u)) Summable.of_finite Summable.of_finite]
  change (∑' u : Bool × Radial Y, W (e (.inl u))) + (∑' v : Rows C Y, W (e (.inr v))) = _
  rw [hfirst,tsum_congr hr,tsum_mul_left]
  ring

#print axioms shell_cutoff_recursion

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
