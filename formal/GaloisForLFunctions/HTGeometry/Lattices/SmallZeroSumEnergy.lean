import GaloisForLFunctions.HTGeometry.Lattices.IntegralZeroSumEnergy

/-!
# Small zero-sum energies

An integral zero-sum vector of energy at most four has every coordinate in
`{-1, 0, 1}`. Hence three or fewer coordinates cannot have energy four.
With two coordinates the energy is twice a square, which also excludes six.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.IntegralZeroSum
variable {ι : Type*} [Fintype ι]

private theorem sq_add_self_nonneg (z : ℤ) : 0 ≤ z^2 + z := by
  by_cases hz : 0 ≤ z
  · positivity
  · have hz' : z + 1 ≤ 0 := by omega
    have h := mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hz) hz'
    nlinarith only [h]

/-- Each coordinate of a zero-sum vector of energy at most four has absolute value at most one. -/
theorem coordinate_abs_le_one_of_energy_le_four {x : ι → ℤ}
    (hsum : ∑ i, x i = 0) (he : energy x ≤ 4) (i : ι) : -1 ≤ x i ∧ x i ≤ 1 := by
  have hp : (x i)^2 + x i ≤ energy x := by
    have h := Finset.single_le_sum (fun j _ => sq_add_self_nonneg (x j)) (Finset.mem_univ i)
    simpa only [Finset.sum_add_distrib, hsum, add_zero, energy] using h
  have hm : (x i)^2 - x i ≤ energy x := by
    have hn (j : ι) : 0 ≤ (x j)^2 - x j := by
      simpa only [neg_sq, add_neg_cancel, sub_eq_add_neg] using sq_add_self_nonneg (-x j)
    have h := Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)
    simpa only [Finset.sum_sub_distrib, hsum, sub_zero, energy] using h
  constructor
  · by_contra h
    have hx : x i ≤ -2 := by omega
    nlinarith only [hx, hm, he]
  · by_contra h
    have hx : 2 ≤ x i := by omega
    nlinarith only [hx, hp, he]

/-- Energy four requires at least four coordinates. -/
theorem energy_ne_four_of_card_le_three {x : ι → ℤ} (hsum : ∑ i, x i = 0)
    (hn : Fintype.card ι ≤ 3) : energy x ≠ 4 := by
  intro he
  have hb (i : ι) : (x i)^2 ≤ 1 := by
    obtain ⟨hl, hu⟩ := coordinate_abs_le_one_of_energy_le_four hsum he.le i
    nlinarith only [hl, hu]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hb i)
  have h' : energy x ≤ Fintype.card ι := by simpa only [Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, energy] using h
  omega

/-- Two zero-sum integer coordinates cannot have energy six. -/
theorem energy_ne_six_of_card_two {x : ι → ℤ} (hsum : ∑ i, x i = 0)
    (hn : Fintype.card ι = 2) : energy x ≠ 6 := by
  let e : Fin 2 ≃ ι := (Fintype.equivFinOfCardEq hn).symm
  have hs : x (e 0) + x (e 1) = 0 := by
    have h := Fintype.sum_equiv e (fun i => x (e i)) x (fun _ => rfl)
    simpa only [Fin.sum_univ_two, hsum] using h
  have heq : energy x = (x (e 0))^2 + (x (e 1))^2 := by
    exact (Fintype.sum_equiv e (fun i => (x (e i))^2) (fun i => (x i)^2) (fun _ => rfl)).symm.trans
      (Fin.sum_univ_two _)
  intro he
  have hb : x (e 1) = -x (e 0) := by omega
  rw [hb] at heq
  have hz : (x (e 0))^2 = 3 := by nlinarith only [heq, he]
  have hbound : -1 ≤ x (e 0) ∧ x (e 0) ≤ 1 := by
    constructor
    · by_contra h
      have h' : x (e 0) ≤ -2 := by omega
      nlinarith only [h', hz]
    · by_contra h
      have h' : 2 ≤ x (e 0) := by omega
      nlinarith only [h', hz]
  nlinarith only [hbound.1, hbound.2, hz]

#print axioms energy_ne_four_of_card_le_three
#print axioms energy_ne_six_of_card_two
end GaloisForLFunctions.HTGeometry.IntegralZeroSum