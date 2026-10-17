import GaloisForLFunctions.BiScaleUncertainty.DyadicDifferenceSource

/-!
# Exact error of a concrete anchored dyadic producer

Symmetric translation chains of the fixed smooth difference source telescope.
Their average has a sharp error, with an exact squared-distance remainder for
every competing anchored packet and arbitrary signed coefficients.
-/

open MeasureTheory
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.DyadicDifference
open RHTower.ArchimedeanAnomaly
noncomputable section

def dipole (k : ℕ) : Lp ℂ 2 (volume : Measure ℝ) :=
  atom (-(k : ℤ)) - atom ((k : ℤ) + 1)

def plateau (m : ℕ) : Lp ℂ 2 (volume : Measure ℝ) :=
  ∑ k ∈ Finset.range (m + 1), dipole k

/-- All non-origin coefficients are free, including their signs. -/
def anchoredPacket (m : ℕ) (a b : ℕ → ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  edge 0 + Finset.sum (Finset.range m) (fun k =>
    (a k : ℂ) • edge (-((k : ℤ) + 1)) + (b k : ℂ) • edge ((k : ℤ) + 1))

def chain (m : ℕ) : Lp ℂ 2 (volume : Measure ℝ) :=
  anchoredPacket m (fun _ => 1) (fun _ => 1)

/-- An average of explicit symmetric translation chains of the actual source. -/
def producer (m : ℕ) : Lp ℂ 2 (volume : Measure ℝ) :=
  ((((m : ℝ) + 1)⁻¹ : ℝ) : ℂ) • ∑ k ∈ Finset.range (m + 1), chain k

theorem chain_eq_dipole (m : ℕ) : chain m = dipole m := by
  induction m with
  | zero => simp [chain, anchoredPacket, dipole, edge_eq]
  | succ m ih =>
    have he : chain (m + 1) = chain m + edge (-((m : ℤ) + 1)) + edge ((m : ℤ) + 1) := by
      simp only [chain, anchoredPacket, Finset.sum_range_succ, Complex.ofReal_one, one_smul]
      abel
    rw [he, ih]
    simp only [dipole, edge_eq, Nat.cast_add, Nat.cast_one]
    rw [show -((m : ℤ) + 1) + 1 = -(m : ℤ) by omega]
    abel

theorem producer_eq_plateau (m : ℕ) :
    producer m = ((((m : ℝ) + 1)⁻¹ : ℝ) : ℂ) • plateau m := by
  simp only [producer, chain_eq_dipole, plateau]

theorem atom_inner_dipole_left (j k : ℕ) :
    inner ℂ (atom (-(j : ℤ))) (dipole k) =
      if j = k then (autocorr seed 0 : ℂ) else 0 := by
  rw [dipole, inner_sub_right, atom_inner, atom_inner]
  have he : (-(j : ℤ) = -(k : ℤ)) ↔ j = k := by omega
  rw [if_neg (by omega : -(j : ℤ) ≠ (k : ℤ) + 1)]
  simp only [he, sub_zero]

theorem atom_inner_dipole_right (j k : ℕ) :
    inner ℂ (atom ((j : ℤ) + 1)) (dipole k) =
      if j = k then -(autocorr seed 0 : ℂ) else 0 := by
  rw [dipole, inner_sub_right, atom_inner, atom_inner]
  have he : ((j : ℤ) + 1 = (k : ℤ) + 1) ↔ j = k := by omega
  rw [if_neg (by omega : (j : ℤ) + 1 ≠ -(k : ℤ))]
  by_cases h : j = k <;> simp [he, h]

theorem dipole_inner (j k : ℕ) :
    inner ℂ (dipole j) (dipole k) =
      if j = k then (autocorr source 0 : ℂ) else 0 := by
  rw [dipole, inner_sub_left, atom_inner_dipole_left, atom_inner_dipole_right]
  by_cases h : j = k <;> simp [h, source_energy]
  ring

theorem atom_inner_plateau_left (m k : ℕ) (hk : k ≤ m) :
    inner ℂ (atom (-(k : ℤ))) (plateau m) = (autocorr seed 0 : ℂ) := by
  rw [plateau, inner_sum]
  simp_rw [atom_inner_dipole_left]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

theorem atom_inner_plateau_right (m k : ℕ) (hk : k ≤ m) :
    inner ℂ (atom ((k : ℤ) + 1)) (plateau m) = -(autocorr seed 0 : ℂ) := by
  rw [plateau, inner_sum]
  simp_rw [atom_inner_dipole_right]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

theorem dipole_inner_plateau (m k : ℕ) (hk : k ≤ m) :
    inner ℂ (dipole k) (plateau m) = (autocorr source 0 : ℂ) := by
  rw [dipole, inner_sub_left, atom_inner_plateau_left m k hk,
    atom_inner_plateau_right m k hk, source_energy]
  push_cast
  ring

theorem plateau_norm_sq (m : ℕ) : ‖plateau m‖ ^ 2 = ((m : ℝ) + 1) * autocorr source 0 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  have hi : inner ℂ (plateau m) (plateau m) =
      ∑ k ∈ Finset.range (m + 1), (autocorr source 0 : ℂ) := by
    conv_lhs => lhs; unfold plateau
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro k hk
    exact dipole_inner_plateau m k (by have := Finset.mem_range.mp hk; omega)
  rw [hi]
  simp

theorem edge_zero_inner_plateau (m : ℕ) :
    inner ℂ (edge 0) (plateau m) = (autocorr source 0 : ℂ) := by
  have he : edge 0 = dipole 0 := by simp [edge_eq, dipole]
  rw [he]
  exact dipole_inner_plateau m 0 (Nat.zero_le _)

theorem edge_left_inner_plateau (m k : ℕ) (hk : k < m) :
    inner ℂ (edge (-((k : ℤ) + 1))) (plateau m) = 0 := by
  rw [edge_eq, inner_sub_left]
  rw [show -((k : ℤ) + 1) + 1 = -(k : ℤ) by omega]
  have ha := atom_inner_plateau_left m (k + 1) (by omega)
  simp only [Nat.cast_add, Nat.cast_one] at ha
  rw [ha, atom_inner_plateau_left m k (by omega), sub_self]

theorem edge_right_inner_plateau (m k : ℕ) (hk : k < m) :
    inner ℂ (edge ((k : ℤ) + 1)) (plateau m) = 0 := by
  rw [edge_eq, inner_sub_left, atom_inner_plateau_right m k (by omega)]
  have ha := atom_inner_plateau_right m (k + 1) (by omega)
  simp only [Nat.cast_add, Nat.cast_one] at ha
  rw [ha, sub_self]

theorem anchoredPacket_inner_plateau (m : ℕ) (a b : ℕ → ℝ) :
    inner ℂ (anchoredPacket m a b) (plateau m) = (autocorr source 0 : ℂ) := by
  rw [anchoredPacket, inner_add_left, sum_inner, edge_zero_inner_plateau]
  have hz : (∑ k ∈ Finset.range m,
      inner ℂ ((a k : ℂ) • edge (-((k : ℤ) + 1)) + (b k : ℂ) • edge ((k : ℤ) + 1))
        (plateau m)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : k < m := Finset.mem_range.mp hk
    rw [inner_add_left, inner_smul_left, inner_smul_left,
      edge_left_inner_plateau m k hk', edge_right_inner_plateau m k hk']
    simp
  rw [hz, add_zero]

/-- The explicit producer's exact error, rather than an assumed error budget. -/
theorem producer_norm_sq (m : ℕ) : ‖producer m‖ ^ 2 = autocorr source 0 / ((m : ℝ) + 1) := by
  rw [producer_eq_plateau, norm_smul, mul_pow, plateau_norm_sq]
  norm_num only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by positivity : 0 < (m : ℝ) + 1))]
  field_simp

theorem anchoredPacket_inner_producer (m : ℕ) (a b : ℕ → ℝ) :
    inner ℂ (anchoredPacket m a b) (producer m) =
      (autocorr source 0 / ((m : ℝ) + 1) : ℝ) := by
  rw [producer_eq_plateau, inner_smul_right, anchoredPacket_inner_plateau]
  push_cast
  ring

/-- Exact excess over the sharp anchored minimum for arbitrary signed weights. -/
theorem anchoredPacket_exact_error (m : ℕ) (a b : ℕ → ℝ) :
    ‖anchoredPacket m a b‖ ^ 2 = autocorr source 0 / ((m : ℝ) + 1) +
      ‖anchoredPacket m a b - producer m‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), anchoredPacket_inner_producer, producer_norm_sq]
  change ‖anchoredPacket m a b‖ ^ 2 = autocorr source 0 / ((m : ℝ) + 1) +
    (‖anchoredPacket m a b‖ ^ 2 - 2 * (autocorr source 0 / ((m : ℝ) + 1)) +
      autocorr source 0 / ((m : ℝ) + 1))
  ring

theorem anchoredPacket_minimum (m : ℕ) (a b : ℕ → ℝ) :
    autocorr source 0 / ((m : ℝ) + 1) ≤ ‖anchoredPacket m a b‖ ^ 2 := by
  rw [anchoredPacket_exact_error]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem anchoredPacket_strictly_positive (m : ℕ) (a b : ℕ → ℝ) :
    0 < ‖anchoredPacket m a b‖ ^ 2 :=
  (div_pos source_energy_pos (by positivity)).trans_le (anchoredPacket_minimum m a b)

theorem anchoredPacket_minimum_iff (m : ℕ) (a b : ℕ → ℝ) :
    ‖anchoredPacket m a b‖ ^ 2 = autocorr source 0 / ((m : ℝ) + 1) ↔
      anchoredPacket m a b = producer m := by
  rw [anchoredPacket_exact_error]
  constructor
  · intro h
    have hz : ‖anchoredPacket m a b - producer m‖ = 0 := by nlinarith only [h]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  · intro h
    simp only [h, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]

end
end GaloisForLFunctions.BiScaleUncertainty.DyadicDifference
