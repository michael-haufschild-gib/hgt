import GaloisForLFunctions.MultiplicativePositivityGeometry.BoundaryZeroCapacity

/-!
# The positivity margin of the boundary forcing law

Measure a failure of (N) against the ζ datum: the log-coefficients satisfy `w(n) ≥ −ε Λ(n)` for some
`ε ≥ 0`, i.e. `w_x(n) ≥ −ε Λ(n) n^{−1−x}`. Adding `ε` copies of the ζ datum restores nonnegativity,
so `D + ε δ₀` is a boundary divisor and positive definite (`margin_isEvenPosDef`).

* **Margin law** (`margin_classification`). An integer-valued `D` with pole order `k`, no off-origin
  pole and defect `ε` is exactly `k δ₀ − Σ_{z ∈ Z} m(z)(δ_z + δ_{−z})` with `2 Σ m(z) ≤ k + ε`. Each
  such configuration occurs with defect `ε`: the weights `Λ(n)(k − 2 Σ_z m(z) cos(z log n))` of
  `ζ(s)^k Π_z (ζ(s + iz) ζ(s − iz))^{−m(z)}` are `≥ −ε Λ(n)`.
* **Threshold** (`simple_pole_margin_threshold`). A simple pole with integer orders and no
  off-origin pole forces `D = δ₀` iff `ε < 1`. At `ε = 1` the quotient `ζ(s)/(ζ(s + i) ζ(s − i))`,
  with weights `Λ(n)(1 − 2 cos(log n)) ≥ −Λ(n)`, has zeros at `1 ± i`.

So the forcing law needs only a fraction of (N): the negative part of the log-coefficients may reach
any `ε < 1` of the von Mangoldt weights, and one full copy is exactly what a boundary zero costs.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-- Signed damped weights, absolutely summable, whose normalized traces converge to `D`. -/
structure IsSignedBoundaryDivisor {ι : Type*} (lam : ι → ℝ) (w : ℝ → ι → ℝ) (D : ℝ → ℝ) :
    Prop where
  summable : ∀ x, 0 < x → Summable fun i => |w x i|
  tendsto : ∀ u, Tendsto (fun x => x * cosineTrace (w x) lam u) (𝓝[>] 0) (𝓝 (D u))

/-- **Margin positivity.** If `w ≥ −ε Λ`, then `D + ε δ₀` is the boundary divisor of the nonnegative
weights `w + ε Λ`, hence positive definite. -/
theorem margin_isBoundaryDivisor {w : ℝ → ℕ → ℝ} {D : ℝ → ℝ} {ε : ℝ}
    (hD : IsSignedBoundaryDivisor logFrequency w D)
    (hw : ∀ x, 0 < x → ∀ n, -(ε * zetaBoundaryWeight x n) ≤ w x n) :
    IsBoundaryDivisor logFrequency (fun x n => w x n + ε * zetaBoundaryWeight x n)
      (fun u => D u + ε * diracAt u) where
  nonneg x hx n := by linarith [hw x hx n]
  summable x hx := (summable_abs_iff.mp (hD.summable x hx)).add
    ((summable_zetaBoundaryWeight hx).mul_left ε)
  tendsto u := by
    have h := (hD.tendsto u).add ((zeta_isBoundaryDivisor.tendsto u).const_mul ε)
    rw [zetaBoundaryDivisor_eq] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hw1 : Summable fun n => w x n * Real.cos (logFrequency n * u) :=
      Summable.of_norm_bounded (hD.summable x hx) fun n => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    have hw2 := summable_cosineTrace_terms (zetaBoundaryWeight_nonneg x)
      (summable_zetaBoundaryWeight hx) logFrequency u
    unfold cosineTrace
    rw [show (fun n => (w x n + ε * zetaBoundaryWeight x n) * Real.cos (logFrequency n * u)) =
        fun n => w x n * Real.cos (logFrequency n * u) +
          ε * (zetaBoundaryWeight x n * Real.cos (logFrequency n * u)) by
        funext n; ring, Summable.tsum_add hw1 (hw2.mul_left ε), tsum_mul_left]
    ring

theorem margin_isEvenPosDef {w : ℝ → ℕ → ℝ} {D : ℝ → ℝ} {ε : ℝ}
    (hD : IsSignedBoundaryDivisor logFrequency w D)
    (hw : ∀ x, 0 < x → ∀ n, -(ε * zetaBoundaryWeight x n) ≤ w x n) :
    IsEvenPosDef fun u => D u + ε * diracAt u :=
  (margin_isBoundaryDivisor hD hw).isEvenPosDef

/-- The almost-periodic twist of the von Mangoldt weights is a signed boundary datum. -/
theorem ap_isSignedBoundaryDivisor (c₀ : ℝ) (Z : Finset ℝ) (b : ℝ → ℝ) :
    IsSignedBoundaryDivisor logFrequency (apWeight c₀ Z b) (apDivisor c₀ Z b) :=
  ⟨fun _ hx => summable_abs_apWeight c₀ Z b hx, tendsto_apTrace c₀ Z b⟩

/-- **Margin law.** For integer orders, pole order `k` and no off-origin pole, a signed datum with
`w ≥ −ε Λ` exists iff `D` is a capacity configuration with `2 Σ m(z) ≤ k + ε`. -/
theorem margin_classification {k : ℕ} {ε : ℝ} {D : ℝ → ℝ}
    (hint : ∀ u, ∃ n : ℤ, D u = n) (h0 : D 0 = k) (hnp : ∀ u, u ≠ 0 → D u ≤ 0) :
    (∃ w : ℝ → ℕ → ℝ, IsSignedBoundaryDivisor logFrequency w D ∧
        ∀ x, 0 < x → ∀ n, -(ε * zetaBoundaryWeight x n) ≤ w x n) ↔
      ∃ (Z : Finset ℝ) (m : ℝ → ℕ), (∀ z ∈ Z, 0 < z) ∧
        2 * ∑ z ∈ Z, (m z : ℝ) ≤ k + ε ∧ D = capacityDivisor k Z m := by
  constructor
  · rintro ⟨w, hw, hmar⟩
    have hpd := margin_isEvenPosDef hw hmar
    set D' := fun u => D u + ε * diracAt u
    have hD'0 : D' 0 = k + ε := by simp [D', diracAt, h0]
    have hD'off : ∀ u, u ≠ 0 → D' u = D u := fun u hu => by simp [D', diracAt, hu]
    have hnp' : ∀ u, u ≠ 0 → D' u ≤ 0 := fun u hu => by rw [hD'off u hu]; exact hnp u hu
    have heven : ∀ u, D (-u) = D u := fun u => by
      rcases eq_or_ne u 0 with rfl | hu
      · rw [neg_zero]
      · have := hpd.even u
        rwa [hD'off _ (neg_ne_zero.mpr hu), hD'off _ hu] at this
    have hmass : ∀ T : Finset ℝ, (∀ z ∈ T, 0 < z) → ∑ z ∈ T, -D z ≤ (k + ε) / 2 := by
      intro T hT
      have h := total_zero_mass_le hpd hnp' hT
      rw [hD'0, Finset.sum_congr rfl fun z hz => by rw [hD'off z (hT z hz).ne']] at h
      exact h
    obtain ⟨Z, m, hZ, hDeq⟩ := eq_capacityDivisor_of_mass_le hint h0 hnp heven hmass
    refine ⟨Z, m, hZ, ?_, hDeq⟩
    have h := hmass Z hZ
    rw [Finset.sum_congr rfl fun z hz => by
      rw [hDeq, capacityDivisor_pos hZ m (hZ z hz), if_pos hz, neg_neg]] at h
    linarith
  · rintro ⟨Z, m, hZ, hcap, rfl⟩
    refine ⟨apWeight k Z fun z => -(2 * (m z : ℝ)), ap_isSignedBoundaryDivisor _ _ _,
      fun x _ n => ?_⟩
    have hP : -ε ≤ apPoly k Z (fun z => -(2 * (m z : ℝ))) (logFrequency n) := by
      unfold apPoly
      have h : ∀ z ∈ Z, -(m z : ℝ) * 2 ≤
          -(2 * (m z : ℝ)) * Real.cos (z * logFrequency n) := fun z _ => by
        have := Real.cos_le_one (z * logFrequency n)
        have h0 : (0 : ℝ) ≤ m z := Nat.cast_nonneg _
        nlinarith
      have := Finset.sum_le_sum h
      rw [← Finset.sum_mul, Finset.sum_neg_distrib] at this
      linarith
    unfold apWeight
    nlinarith [zetaBoundaryWeight_nonneg x n]

/-- **The threshold of the forcing law.** Integer-valued data with a simple pole, no off-origin pole
and log-coefficients `≥ −ε Λ` always have `D = δ₀` iff `ε < 1`. -/
theorem simple_pole_margin_threshold {ε : ℝ} :
    (∀ (D : ℝ → ℝ) (w : ℝ → ℕ → ℝ), (∀ u, ∃ n : ℤ, D u = n) → D 0 = 1 →
        (∀ u, u ≠ 0 → D u ≤ 0) → IsSignedBoundaryDivisor logFrequency w D →
        (∀ x, 0 < x → ∀ n, -(ε * zetaBoundaryWeight x n) ≤ w x n) → ∀ u, u ≠ 0 → D u = 0) ↔
      ε < 1 := by
  constructor
  · intro hforce
    by_contra hge
    push Not at hge
    -- At `ε ≥ 1` the configuration `δ₀ − δ₁ − δ₋₁` has defect `ε`.
    set m : ℝ → ℕ := fun _ => 1
    have hZ : ∀ z ∈ ({1} : Finset ℝ), (0 : ℝ) < z := by simp
    have hcap : 2 * ∑ z ∈ ({1} : Finset ℝ), (m z : ℝ) ≤ ((1 : ℕ) : ℝ) + ε := by
      simp only [m, Finset.sum_singleton, Nat.cast_one]; linarith
    have hval : capacityDivisor 1 {1} m 1 = -1 := by
      rw [capacityDivisor_pos hZ m one_pos, if_pos (Finset.mem_singleton_self 1)]
      simp [m]
    have hint : ∀ u, ∃ n : ℤ, capacityDivisor 1 {1} m u = n := by
      intro u
      rcases lt_trichotomy u 0 with hu | rfl | hu
      · rw [← capacityDivisor_neg, capacityDivisor_pos hZ m (by linarith)]
        split_ifs
        · exact ⟨-1, by simp [m]⟩
        · exact ⟨0, by simp⟩
      · exact ⟨1, by rw [capacityDivisor_zero hZ m]; simp⟩
      · rw [capacityDivisor_pos hZ m hu]
        split_ifs
        · exact ⟨-1, by simp [m]⟩
        · exact ⟨0, by simp⟩
    have hnp : ∀ u, u ≠ 0 → capacityDivisor 1 {1} m u ≤ 0 := by
      intro u hu
      rcases lt_or_gt_of_ne hu with h | h
      · rw [← capacityDivisor_neg, capacityDivisor_pos hZ m (by linarith)]
        split_ifs <;> simp
      · rw [capacityDivisor_pos hZ m h]
        split_ifs <;> simp
    obtain ⟨w, hw, hmar⟩ := (margin_classification (k := 1) hint
      (capacityDivisor_zero hZ m) hnp).mpr ⟨{1}, m, hZ, hcap, rfl⟩
    have := hforce _ w hint (by rw [capacityDivisor_zero hZ m]; simp) hnp hw hmar 1 one_ne_zero
    rw [hval] at this
    norm_num at this
  · intro hlt D w hint h0 hnp hw hmar u hu
    obtain ⟨Z, m, hZ, hcap, rfl⟩ := (margin_classification (k := 1) hint
      (by rw [h0]; norm_num) hnp).mp ⟨w, hw, hmar⟩
    -- `2 Σ m ≤ 1 + ε < 2` forces every `m(z)` to vanish.
    have hm0 : ∀ z ∈ Z, m z = 0 := by
      intro z hz
      by_contra hne
      have h1 : (1 : ℝ) ≤ m z := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
      have h2 : (m z : ℝ) ≤ ∑ z ∈ Z, (m z : ℝ) :=
        Finset.single_le_sum (fun _ _ => Nat.cast_nonneg _) hz
      push_cast at hcap
      linarith
    rcases lt_or_gt_of_ne hu with h | h
    · rw [← capacityDivisor_neg, capacityDivisor_pos hZ m (by linarith)]
      split_ifs with hmem
      · rw [hm0 _ hmem]; simp
      · rfl
    · rw [capacityDivisor_pos hZ m h]
      split_ifs with hmem
      · rw [hm0 _ hmem]; simp
      · rfl

end GaloisForLFunctions.MultiplicativePositivityGeometry
