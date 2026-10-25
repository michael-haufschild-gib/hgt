import GaloisForLFunctions.MultiplicativePositivityGeometry.BoundaryPositivity

/-!
# Classification of boundary divisors with a simple pole

Let `D : ℝ → ℝ` be an integer-valued even positive-definite function with `D 0 = 1`; by the
boundary positivity theorem this is the boundary divisor (pole order minus zero order on
`Re s = 1`) of an Euler product with nonnegative log-coefficients and a simple pole at `1`.

* `boundary_values`: every boundary point is a simple zero, a simple pole or regular
  (`D u ∈ {-1, 0, 1}`).
* `boundary_zero_forces_double_pole`: a boundary zero at height `u` forces a pole at height `2u`.
* `boundary_eq_delta_of_no_pole`: with no boundary pole away from the origin there is no boundary
  zero: `D` is the indicator of `{0}`. This is the boundary forcing law of the prime number theorem,
  recovered from positive definiteness alone.
* `boundary_trichotomy`: if the boundary divisor is locally finite, exactly three shapes occur:
  `D = 1_{0}`, `D = 1_{cℤ}` (periodic poles), or `D(kc) = (-1)^k` on `cℤ` and `0` elsewhere
  (alternating poles and zeros).

For a pole of order `k = D 0`, positive definiteness bounds every zero order by `k` plus the local
pole order (`boundary_zero_order_le`), and the total zero mass along a pole-free progression
`h, 2h, 3h, …` by `k/2` (`boundary_progression_zero_mass_le`).
-/

open Finset

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

variable {D : ℝ → ℝ}

/-- Values of a simple-pole integer boundary divisor. -/
theorem boundary_values (hD : IsEvenPosDef D) (h0 : D 0 = 1) (hint : ∀ u, ∃ n : ℤ, D u = n)
    (u : ℝ) : D u = -1 ∨ D u = 0 ∨ D u = 1 :=
  intValued_values hD h0 hint u

/-- **A boundary zero forces a pole at twice its height.** -/
theorem boundary_zero_forces_double_pole (hD : IsEvenPosDef D) (h0 : D 0 = 1)
    (hint : ∀ u, ∃ n : ℤ, D u = n) {u : ℝ} (hu : D u = -1) : D (2 * u) = 1 := by
  rw [two_mul]
  exact intValued_double hD h0 hint hu

/-- **No boundary pole off the origin ⇒ no boundary zero.** -/
theorem boundary_eq_delta_of_no_pole (hD : IsEvenPosDef D) (h0 : D 0 = 1)
    (hint : ∀ u, ∃ n : ℤ, D u = n) (hnp : ∀ u, u ≠ 0 → D u ≤ 0) (u : ℝ) :
    D u = if u = 0 then 1 else 0 := by
  split_ifs with hu
  · rw [hu, h0]
  · exact intValued_eq_zero_of_nonpos hD h0 hint hnp
      (fun v hv => by linarith [show 2 * v = 0 by linarith]) hu

/-- Along the multiples of a nonvanishing point the divisor is a power character. -/
theorem boundary_mul_natAbs (hD : IsEvenPosDef D) (h0 : D 0 = 1)
    (hint : ∀ u, ∃ n : ℤ, D u = n) {c : ℝ} (hc : D c ≠ 0) (k : ℤ) :
    D (k * c) = D c ^ k.natAbs := by
  have hnat : ∀ n : ℕ, D (n * c) = D c ^ n := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      have : ((n + 1 : ℕ) : ℝ) * c = c + n * c := by push_cast; ring
      rw [this, intValued_mul hD h0 hint hc, ih, pow_succ]
      ring
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [(by simp : ((n : ℤ)).natAbs = n)]
    exact_mod_cast hnat n
  · rw [(by simp : (-(n : ℤ)).natAbs = n)]
    push_cast
    rw [neg_mul, hD.even]
    exact hnat n

/-- A locally finite boundary divisor has a cyclic nonvanishing subgroup. -/
theorem nonvanishingSubgroup_cyclic (hD : IsEvenPosDef D) (h0 : D 0 = 1)
    (hint : ∀ u, ∃ n : ℤ, D u = n) (hfin : ∀ T, {u : ℝ | |u| ≤ T ∧ D u ≠ 0}.Finite) :
    ∃ a : ℝ, nonvanishingSubgroup hD h0 hint = AddSubgroup.zmultiples a := by
  rcases (nonvanishingSubgroup hD h0 hint).dense_or_cyclic with hdense | ⟨a, ha⟩
  · exfalso
    set F := {u : ℝ | |u| ≤ 1 ∧ D u ≠ 0}
    have hsub : Set.Ioo (-1 : ℝ) 1 ⊆ F := by
      have h1 := hdense.open_subset_closure_inter isOpen_Ioo (t := Set.Ioo (-1 : ℝ) 1)
      have h2 : Set.Ioo (-1 : ℝ) 1 ∩ (nonvanishingSubgroup hD h0 hint : Set ℝ) ⊆ F := by
        rintro u ⟨⟨hl, hr⟩, hu⟩
        exact ⟨abs_le.mpr ⟨hl.le, hr.le⟩, hu⟩
      exact h1.trans ((closure_mono h2).trans (hfin 1).isClosed.closure_subset)
    exact Set.Ioo_infinite (by norm_num : (-1 : ℝ) < 1) ((hfin 1).subset hsub)
  · exact ⟨a, by rw [ha, AddSubgroup.zmultiples_eq_closure]⟩

open Classical in
/-- **Boundary trichotomy.** A locally finite simple-pole integer boundary divisor is either the
indicator of `{0}`, the indicator of a lattice `cℤ`, or the alternating character on `cℤ`. -/
theorem boundary_trichotomy (hD : IsEvenPosDef D) (h0 : D 0 = 1)
    (hint : ∀ u, ∃ n : ℤ, D u = n) (hfin : ∀ T, {u : ℝ | |u| ≤ T ∧ D u ≠ 0}.Finite) :
    (∀ u, D u = if u = 0 then 1 else 0) ∨
    (∃ c > 0, ∀ u, D u = if ∃ k : ℤ, u = k * c then 1 else 0) ∨
    (∃ c > 0, (∀ k : ℤ, D (k * c) = (-1) ^ k.natAbs) ∧
      ∀ u, (¬ ∃ k : ℤ, u = k * c) → D u = 0) := by
  obtain ⟨a, ha⟩ := nonvanishingSubgroup_cyclic hD h0 hint hfin
  have hmem : ∀ u, D u ≠ 0 ↔ ∃ k : ℤ, u = k * a := fun u => by
    rw [← mem_nonvanishingSubgroup hD h0 hint, ha, AddSubgroup.mem_zmultiples_iff]
    simp only [zsmul_eq_mul, eq_comm]
  rcases eq_or_ne a 0 with rfl | ha0
  · left
    intro u
    split_ifs with hu
    · rw [hu, h0]
    · by_contra hne
      obtain ⟨k, hk⟩ := (hmem u).mp hne
      exact hu (by rw [hk, mul_zero])
  · set c := |a| with hcdef
    have hc : 0 < c := abs_pos.mpr ha0
    have hmemc : ∀ u, D u ≠ 0 ↔ ∃ k : ℤ, u = k * c := fun u => by
      rw [hmem]
      rcases abs_choice a with h | h
      · rw [hcdef, h]
      · rw [hcdef, h]
        constructor
        · rintro ⟨k, hk⟩
          exact ⟨-k, by rw [hk]; push_cast; ring⟩
        · rintro ⟨k, hk⟩
          exact ⟨-k, by rw [hk]; push_cast; ring⟩
    have hDc : D c ≠ 0 := (hmemc c).mpr ⟨1, by simp⟩
    rcases boundary_values hD h0 hint c with h1 | h1 | h1
    · right; right
      refine ⟨c, hc, fun k => ?_, fun u hu => ?_⟩
      · rw [boundary_mul_natAbs hD h0 hint hDc, h1]
      · by_contra hne
        exact hu ((hmemc u).mp hne)
    · exact absurd h1 hDc
    · right; left
      refine ⟨c, hc, fun u => ?_⟩
      split_ifs with hu
      · obtain ⟨k, rfl⟩ := hu
        rw [boundary_mul_natAbs hD h0 hint hDc, h1, one_pow]
      · by_contra hne
        exact hu ((hmemc u).mp hne)

/-- **Zero orders are bounded by the pole order.** `|D u| ≤ D 0`: a boundary zero not cancelled by a
local pole has order at most the order of the pole at `1`. -/
theorem boundary_zero_order_le (hD : IsEvenPosDef D) (u : ℝ) : -D u ≤ D 0 :=
  (neg_le_abs (D u)).trans (hD.abs_le_apply_zero u)

/-- **Progression zero-mass law.** If the progression `h, 2h, 3h, …` carries no poles
(`D ≤ 0` there), its total zero mass is at most half the pole order at the origin. -/
theorem boundary_progression_zero_mass_le (hD : IsEvenPosDef D) (h : ℝ)
    (hneg : ∀ r : ℕ, D ((r + 1 : ℕ) * h) ≤ 0) (R : ℕ) :
    ∑ r ∈ range R, -D ((r + 1 : ℕ) * h) ≤ D 0 / 2 := by
  have := hD.progression_mass_le h (fun r => by simpa [nsmul_eq_mul] using hneg r) R
  simpa [nsmul_eq_mul] using this

end GaloisForLFunctions.MultiplicativePositivityGeometry
