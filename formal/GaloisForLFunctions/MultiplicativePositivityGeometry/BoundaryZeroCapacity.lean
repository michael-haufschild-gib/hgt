import GaloisForLFunctions.MultiplicativePositivityGeometry.FiniteBoundaryDivisors

/-!
# The boundary zero capacity of a pole of order `k`

Let `D` be an integer-valued even positive-definite function with `D(0) = k` and `D ≤ 0` off the
origin: the boundary divisor of nonnegative weights with integer orders (N), (Z), a pole of order
`k` at `1` and no other boundary pole (I). Then (`isolated_boundary_classification`)

  `D = k δ₀ − Σ_{z ∈ Z} m(z) (δ_z + δ_{−z})`, `Z ⊂ (0, ∞)` finite, `m(z) ∈ ℕ`, `2 Σ_z m(z) ≤ k`,

and every such configuration occurs (`capacity_isBoundaryDivisor`). The realizing weights
`Λ(n) n^{−1−x} (k − 2 Σ_z m(z) cos(z log n)) ≥ 0` are the log-derivative coefficients of the
meromorphic Euler product `ζ(s)^{k − 2M} Π_z (ζ(s)² / (ζ(s + iz) ζ(s − iz)))^{m(z)}`, `M = Σ m(z)`.

* **Capacity.** A pole of order `k` carries at most `⌊k/2⌋` boundary zeros, counted with
  multiplicity and placed at arbitrary heights; every placement within the capacity occurs.
* **Extremal configurations.** Total multiplicity `k/2` needs `k` even; it is reached exactly by
  the products of double-pole quotients, where no factor of `ζ` remains. These are the
  configurations whose Bohr polynomial `k − 2 Σ m(z) cos(zt)` vanishes at `t = 0`.
* A simple pole has capacity `0`: the boundary forcing law `D = δ₀` is the case `k = 1`.
-/

open Finset

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-! ### Values of almost-periodic divisors -/

theorem diracAt_neg (v : ℝ) : diracAt (-v) = diracAt v := by
  simp [diracAt, neg_eq_zero]

theorem apDivisor_neg (c₀ : ℝ) (Z : Finset ℝ) (b : ℝ → ℝ) (u : ℝ) :
    apDivisor c₀ Z b (-u) = apDivisor c₀ Z b u := by
  unfold apDivisor
  rw [diracAt_neg]
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [show -u + z = -(u - z) by ring, show -u - z = -(u + z) by ring, diracAt_neg, diracAt_neg,
    add_comm (diracAt (u - z))]

theorem apDivisor_zero {c₀ : ℝ} {Z : Finset ℝ} (hZ : ∀ z ∈ Z, 0 < z) (b : ℝ → ℝ) :
    apDivisor c₀ Z b 0 = c₀ := by
  unfold apDivisor diracAt
  rw [if_pos rfl, Finset.sum_eq_zero fun z hz => ?_]
  · ring
  · have := hZ z hz
    rw [if_neg (by linarith), if_neg (by linarith)]
    ring

theorem apDivisor_pos {c₀ : ℝ} {Z : Finset ℝ} (hZ : ∀ z ∈ Z, 0 < z) (b : ℝ → ℝ) {u : ℝ}
    (hu : 0 < u) : apDivisor c₀ Z b u = if u ∈ Z then b u / 2 else 0 := by
  classical
  unfold apDivisor diracAt
  have h : ∀ z ∈ Z, b z / 2 * ((if u + z = 0 then (1 : ℝ) else 0) + (if u - z = 0 then 1 else 0)) =
      if z = u then b u / 2 else 0 := by
    intro z hz
    have hz0 := hZ z hz
    have h1 : u + z ≠ 0 := (by linarith : 0 < u + z).ne'
    by_cases hzu : z = u
    · rw [if_pos hzu, if_neg h1, if_pos (by rw [hzu]; ring), hzu]
      ring
    · rw [if_neg hzu, if_neg h1, if_neg (fun h => hzu (by linarith))]
      ring
  rw [if_neg hu.ne', Finset.sum_congr rfl h, Finset.sum_ite_eq' Z u (fun _ => b u / 2)]
  ring

/-! ### The capacity configurations -/

/-- The configuration `k δ₀ − Σ_{z ∈ Z} m(z)(δ_z + δ_{−z})`. -/
noncomputable def capacityDivisor (k : ℕ) (Z : Finset ℝ) (m : ℝ → ℕ) : ℝ → ℝ :=
  apDivisor k Z fun z => -(2 * (m z : ℝ))

theorem capacityDivisor_zero {k : ℕ} {Z : Finset ℝ} (hZ : ∀ z ∈ Z, 0 < z) (m : ℝ → ℕ) :
    capacityDivisor k Z m 0 = k :=
  apDivisor_zero hZ _

theorem capacityDivisor_neg (k : ℕ) (Z : Finset ℝ) (m : ℝ → ℕ) (u : ℝ) :
    capacityDivisor k Z m (-u) = capacityDivisor k Z m u :=
  apDivisor_neg _ _ _ _

theorem capacityDivisor_pos {k : ℕ} {Z : Finset ℝ} (hZ : ∀ z ∈ Z, 0 < z) (m : ℝ → ℕ) {u : ℝ}
    (hu : 0 < u) : capacityDivisor k Z m u = if u ∈ Z then -(m u : ℝ) else 0 := by
  rw [capacityDivisor, apDivisor_pos hZ _ hu]
  split_ifs <;> ring

/-- **Realization.** If `2 Σ m(z) ≤ k`, the configuration is the boundary divisor of
`ζ(s)^{k − 2M} Π_z (ζ(s)²/(ζ(s + iz) ζ(s − iz)))^{m(z)}`. -/
theorem capacity_isBoundaryDivisor {k : ℕ} {Z : Finset ℝ} {m : ℝ → ℕ}
    (hcap : 2 * ∑ z ∈ Z, (m z : ℝ) ≤ k) :
    IsBoundaryDivisor logFrequency (apWeight k Z fun z => -(2 * (m z : ℝ)))
      (capacityDivisor k Z m) := by
  refine ap_isBoundaryDivisor fun t => ?_
  unfold apPoly
  have h : ∀ z ∈ Z, -(m z : ℝ) * 2 ≤ -(2 * (m z : ℝ)) * Real.cos (z * t) := fun z _ => by
    have := Real.cos_le_one (z * t)
    have h0 : (0 : ℝ) ≤ m z := Nat.cast_nonneg _
    nlinarith
  have := Finset.sum_le_sum h
  rw [← Finset.sum_mul, Finset.sum_neg_distrib] at this
  linarith

/-- **Capacity law.** The configuration is positive definite iff `2 Σ m(z) ≤ k`. -/
theorem capacity_isEvenPosDef_iff {k : ℕ} {Z : Finset ℝ} (hZ : ∀ z ∈ Z, 0 < z) (m : ℝ → ℕ) :
    IsEvenPosDef (capacityDivisor k Z m) ↔ 2 * ∑ z ∈ Z, (m z : ℝ) ≤ k := by
  constructor
  · intro hpd
    have hnp : ∀ u, u ≠ 0 → capacityDivisor k Z m u ≤ 0 := by
      intro u hu
      rcases lt_or_gt_of_ne hu with h | h
      · rw [← capacityDivisor_neg, capacityDivisor_pos hZ m (by linarith)]
        split_ifs <;> simp
      · rw [capacityDivisor_pos hZ m h]
        split_ifs <;> simp
    have hmass := total_zero_mass_le hpd hnp hZ
    rw [capacityDivisor_zero hZ m] at hmass
    have hsum : ∑ z ∈ Z, -capacityDivisor k Z m z = ∑ z ∈ Z, (m z : ℝ) :=
      Finset.sum_congr rfl fun z hz => by rw [capacityDivisor_pos hZ m (hZ z hz), if_pos hz, neg_neg]
    rw [hsum] at hmass
    linarith
  · intro hcap
    exact (capacity_isBoundaryDivisor hcap).isEvenPosDef

/-- An integer-valued even `D ≤ 0` off the origin whose zero masses are bounded on finite sets of
heights is a capacity configuration. -/
theorem eq_capacityDivisor_of_mass_le {k : ℕ} {D : ℝ → ℝ} (hint : ∀ u, ∃ n : ℤ, D u = n)
    (h0 : D 0 = k) (hnp : ∀ u, u ≠ 0 → D u ≤ 0) (heven : ∀ u, D (-u) = D u) {C : ℝ}
    (hmass : ∀ T : Finset ℝ, (∀ z ∈ T, 0 < z) → ∑ z ∈ T, -D z ≤ C) :
    ∃ (Z : Finset ℝ) (m : ℝ → ℕ), (∀ z ∈ Z, 0 < z) ∧ D = capacityDivisor k Z m := by
  classical
  -- The positive zero heights form a finite set: each carries mass at least `1`.
  set S := {z : ℝ | 0 < z ∧ D z ≠ 0}
  have hzero : ∀ z ∈ S, 1 ≤ -D z := by
    intro z hz
    obtain ⟨n, hn⟩ := hint z
    have hlt : D z < 0 := lt_of_le_of_ne (hnp z hz.1.ne') hz.2
    rw [hn] at hlt ⊢
    have : n ≤ -1 := by
      have : n < 0 := by exact_mod_cast hlt
      omega
    have : (n : ℝ) ≤ -1 := by exact_mod_cast this
    linarith
  have hS : S.Finite := by
    by_contra hinf
    obtain ⟨T, hTS, hT⟩ := Set.Infinite.exists_subset_card_eq hinf (⌈C⌉₊ + 1)
    have h1 := hmass T fun z hz => (hTS hz).1
    have h2 : (T.card : ℝ) ≤ ∑ z ∈ T, -D z := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      exact Finset.sum_le_sum fun z hz => hzero z (hTS hz)
    rw [hT] at h2
    push_cast at h2
    linarith [Nat.le_ceil C]
  set Z := hS.toFinset
  have hZ : ∀ z ∈ Z, 0 < z := fun z hz => ((Set.Finite.mem_toFinset hS).mp hz).1
  set m : ℝ → ℕ := fun z => (-(Classical.choose (hint z))).toNat
  have hm : ∀ z, 0 < z → (m z : ℝ) = -D z := by
    intro z hz
    simp only [m]
    have hc := Classical.choose_spec (hint z)
    set c := Classical.choose (hint z)
    have hle : c ≤ 0 := by
      have := hnp z hz.ne'
      rw [hc] at this
      exact_mod_cast this
    have h1 : (((-c).toNat : ℤ)) = -c := Int.toNat_of_nonneg (by omega)
    have h2 : ((((-c).toNat : ℕ) : ℤ) : ℝ) = ((-c : ℤ) : ℝ) := by rw [h1]
    push_cast at h2
    rw [hc, h2]
  refine ⟨Z, m, hZ, ?_⟩
  funext u
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · rw [← heven u, ← capacityDivisor_neg, capacityDivisor_pos hZ m (by linarith)]
    split_ifs with hmem
    · rw [hm _ (by linarith)]
      ring
    · by_contra hne
      exact hmem ((Set.Finite.mem_toFinset hS).mpr ⟨by linarith, hne⟩)
  · rw [capacityDivisor_zero hZ m, h0]
  · rw [capacityDivisor_pos hZ m hu]
    split_ifs with hmem
    · rw [hm _ hu]
      ring
    · by_contra hne
      exact hmem ((Set.Finite.mem_toFinset hS).mpr ⟨hu, hne⟩)

/-- **Classification of pole-isolated integral boundary divisors.** An integer-valued `D` with
`D(0) = k` and `D ≤ 0` off the origin is positive definite iff it is a capacity configuration
`k δ₀ − Σ_{z ∈ Z} m(z)(δ_z + δ_{−z})` with `2 Σ m(z) ≤ k`. In particular a pole of order `k` carries
at most `⌊k/2⌋` boundary zeros, counted with multiplicity. -/
theorem isolated_boundary_classification {k : ℕ} {D : ℝ → ℝ} (hint : ∀ u, ∃ n : ℤ, D u = n)
    (h0 : D 0 = k) (hnp : ∀ u, u ≠ 0 → D u ≤ 0) :
    IsEvenPosDef D ↔ ∃ (Z : Finset ℝ) (m : ℝ → ℕ), (∀ z ∈ Z, 0 < z) ∧
      2 * ∑ z ∈ Z, m z ≤ k ∧ D = capacityDivisor k Z m := by
  constructor
  · intro hpd
    obtain ⟨Z, m, hZ, hDeq⟩ := eq_capacityDivisor_of_mass_le hint h0 hnp hpd.even
      fun T hT => total_zero_mass_le hpd hnp hT
    refine ⟨Z, m, hZ, ?_, hDeq⟩
    have := (capacity_isEvenPosDef_iff hZ m).mp (hDeq ▸ hpd)
    exact_mod_cast this
  · rintro ⟨Z, m, hZ, hcap, rfl⟩
    exact (capacity_isEvenPosDef_iff hZ m).mpr (by exact_mod_cast hcap)

end GaloisForLFunctions.MultiplicativePositivityGeometry
