import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekFiniteEnergyLocalFEReflectionNoGo

/-!
# Finite positive atomic seam obstruction for Parikh--Wilczek reflection

A finite positive atomic completed seam is allowed to mix every physical
energy into every finite target-energy channel. Its grade-one and grade-two
Mellin moments still cannot implement functional-equation reflection within a
finite physical interval: positivity confines mean target energy below the
endpoint, while the two grades force it to be reciprocal source energy. A
nonzero independent seam contact is explicitly retained.

Proof-chain role:
`finite positive CTP seam + finite-energy contact -> two Mellin reflection
grades` is impossible. Therefore the PW-B source seam must use an infinite
reciprocal tail, signed/complex transport, or a singular spectral mechanism
before it can attempt fixed-grade partner balance and Xi occurrence.
-/

namespace RHTower

noncomputable section

/-- A finite positive, energy-nonlocal candidate CTP seam. `contact` is an
independent finite-energy contact term, kept rather than absorbed into the
reverse kernel. -/
structure PWFiniteEnergyPositiveAtomicFEReflectionData
    (ι : Type*) [Fintype ι] (X : ℝ) where
  energy : ι → ℝ
  energy_mem : ∀ i, 0 < energy i ∧ energy i < X
  weight : ℝ → ι → ℝ
  weight_nonneg : ∀ {x : ℝ}, 0 < x → x < X → ∀ i, 0 ≤ weight x i
  mellinGradeOne : ∀ {x : ℝ}, 0 < x → x < X →
    (∑ i, weight x i) = x⁻¹
  mellinGradeTwo : ∀ {x : ℝ}, 0 < x → x < X →
    (∑ i, weight x i * energy i) = x⁻¹ ^ (2 : ℕ)
  contact : ℂ
  contact_ne_zero : contact ≠ 0

/-- **Finite-positive CTP seam no-go.** No finite-support positive atomic
seam, even with a separate nonzero contact, can realize the two Mellin grades
of functional-equation reflection on a finite physical-energy interval. -/
theorem no_PWFiniteEnergyPositiveAtomicFEReflectionData
    (ι : Type*) [Fintype ι] {X : ℝ} (hX : 0 < X) :
    IsEmpty (PWFiniteEnergyPositiveAtomicFEReflectionData ι X) := by
  classical
  refine ⟨fun D => ?_⟩
  let x : ℝ := X / (X ^ (2 : ℕ) + 1)
  have hden : 0 < X ^ (2 : ℕ) + 1 := by positivity
  have hx0 : 0 < x := div_pos hX hden
  have hxX : x < X := by
    dsimp only [x]
    exact div_lt_self hX (by nlinarith [sq_pos_of_pos hX])
  have hmass := D.mellinGradeOne hx0 hxX
  have hmoment := D.mellinGradeTwo hx0 hxX
  have hweight_nonneg (i : ι) : 0 ≤ D.weight x i :=
    D.weight_nonneg hx0 hxX i
  have hmass_pos : 0 < ∑ i, D.weight x i := by
    rw [hmass]
    exact inv_pos.mpr hx0
  have hweight_exists : ∃ i, 0 < D.weight x i := by
    by_contra h
    push Not at h
    have hzero : ∀ i, D.weight x i = 0 := fun i =>
      le_antisymm (h i) (hweight_nonneg i)
    have : (∑ i, D.weight x i) = 0 := by simp [hzero]
    linarith
  obtain ⟨i, hi⟩ := hweight_exists
  have hterm_le (j : ι) : D.weight x j * D.energy j ≤ D.weight x j * X :=
    mul_le_mul_of_nonneg_left (D.energy_mem j).2.le (hweight_nonneg j)
  have hterm_lt : D.weight x i * D.energy i < D.weight x i * X :=
    mul_lt_mul_of_pos_left (D.energy_mem i).2 hi
  have hsum_lt : (∑ j, D.weight x j * D.energy j) <
      ∑ j, D.weight x j * X := by
    simpa using
      (Finset.sum_lt_sum (s := Finset.univ)
        (fun j _ => hterm_le j) ⟨i, Finset.mem_univ i, hterm_lt⟩)
  have hinv_gt : X < x⁻¹ := by
    have hxinv : x⁻¹ = X + X⁻¹ := by
      dsimp only [x]
      field_simp [hX.ne']
    rw [hxinv]
    exact lt_add_of_pos_right X (inv_pos.mpr hX)
  have hinv_pos : 0 < x⁻¹ := inv_pos.mpr hx0
  have hreciprocal_lt : x⁻¹ * X < x⁻¹ * x⁻¹ :=
    mul_lt_mul_of_pos_left hinv_gt hinv_pos
  rw [hmoment, ← Finset.sum_mul, hmass, pow_two] at hsum_lt
  exact (not_lt_of_ge hreciprocal_lt.le) hsum_lt

end

end RHTower
