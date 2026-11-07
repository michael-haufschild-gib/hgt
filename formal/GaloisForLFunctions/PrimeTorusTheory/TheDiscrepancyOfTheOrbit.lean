import GaloisForLFunctions.PrimeTorusTheory.TheFiniteTimeBohrIsometry

/-!
# The discrepancy of the orbit against Haar measure at finite time

How close is the orbit to Haar measure at time `T`, on the primes up to `y`, past the Kronecker scale? It depends entirely on the test.

* **Characters** (`norm_integral_nPhase_sub_le`). The window mean of the character `(a/b)^{it}` is at most `2 max(a,b)/L`, by the integer gap. So every character of degree `k` is equidistributed as soon as
  `y^k ≪ L`: the orbit is `k`-wise uniform up to the last diagonal scale `k ≈ log L / log y`.
* **Boxes** (`card_patterns_le`, `exists_pattern_not_attained`). The sign pattern of the orbit changes only at the zeros of the `cos(t log p)`, and there are `≲ T θ(y)/π` of them on `[0, T]`. There are `2^{π(y)}` sign patterns, each with Haar measure `2^{−π(y)}`. So past the
  mixing time `T θ(y) ≪ 2^{π(y)}` the orbit has visited a set of Haar measure `≲ T θ(y) 2^{−π(y)}`, and its box discrepancy is `1 − o(1)`.

So below the mixing time the orbit is pseudorandom against low-degree characters and completely sparse against boxes. Moments cannot see the difference, and this is the same phenomenon as
`diagonal_data_cannot_exclude_return`. The mixing time lies between `2^{π(y)}/θ(y)` (boxes, this module) and, for half-spaces, `exp(c_m y)` (`exists_column_ge_of_primesUpTo`).
-/

open Finset

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- **Character discrepancy.** On a window of length `L` the mean of a nontrivial integer character is at most `2 max(a,b)/L`. -/
theorem norm_integral_nPhase_sub_le {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (T L : ℝ) :
    ‖∫ t in T..T + L, Complex.exp (Complex.I * (((Real.log a - Real.log b : ℝ) : ℂ) * (t : ℂ)))‖ ≤
      2 * ((max a b : ℕ) : ℝ) := by
  have hgap := HTGeometry.inv_max_le_abs_log_sub_log ha hb hab
  have hmaxpos : (0 : ℝ) < ((max a b : ℕ) : ℝ) := by
    have : 0 < max a b := lt_max_of_lt_left ha
    exact_mod_cast this
  have hγ : Real.log a - Real.log b ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hgap
    exact absurd hgap (not_le.mpr (by positivity))
  refine (TrigSum.norm_integral_exp_I_mul_le _ hγ T L).trans ?_
  have hpos : 0 < |Real.log a - Real.log b| := abs_pos.mpr hγ
  rw [div_le_iff₀ hpos]
  have h3 : (1 : ℝ) ≤ ((max a b : ℕ) : ℝ) * |Real.log a - Real.log b| := by
    have := mul_le_mul_of_nonneg_left hgap hmaxpos.le
    rwa [mul_inv_cancel₀ hmaxpos.ne'] at this
  nlinarith [abs_nonneg (Real.log a - Real.log b)]

/-- The zeros of `cos(t ℓ)` on `[0, T]`. -/
def cosZeros (ℓ T : ℝ) : Finset ℝ :=
  (Finset.range (⌊T * ℓ / Real.pi⌋₊ + 1)).image fun m : ℕ => (Real.pi / 2 + m * Real.pi) / ℓ

theorem card_cosZeros_le (ℓ T : ℝ) : (cosZeros ℓ T).card ≤ ⌊T * ℓ / Real.pi⌋₊ + 1 := by
  unfold cosZeros
  simpa using Finset.card_image_le (s := Finset.range (⌊T * ℓ / Real.pi⌋₊ + 1))
    (f := fun m : ℕ => (Real.pi / 2 + m * Real.pi) / ℓ)

/-- Every zero of `cos(tℓ)` in `[0, T]` is on the list. -/
theorem mem_cosZeros {ℓ T t : ℝ} (hℓ : 0 < ℓ) (ht0 : 0 ≤ t) (htT : t ≤ T) (hz : Real.cos (t * ℓ) = 0) :
    t ∈ cosZeros ℓ T := by
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hz
  have hpi := Real.pi_pos
  have htℓ : 0 ≤ t * ℓ := by positivity
  -- `t ℓ = (2k + 1) π/2`, and it is nonnegative, so `k ≥ 0`.
  have hk0 : 0 ≤ k := by
    by_contra hneg
    have h1 : k ≤ -1 := by omega
    have h2 : ((2 * k + 1 : ℤ) : ℝ) ≤ -1 := by
      have : 2 * k + 1 ≤ -1 := by omega
      exact_mod_cast this
    have h3 : t * ℓ = ((2 * k + 1 : ℤ) : ℝ) * Real.pi / 2 := by
      push_cast
      push_cast at hk
      linarith
    rw [h3] at htℓ
    nlinarith
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
  have hval : t * ℓ = Real.pi / 2 + (m : ℝ) * Real.pi := by
    push_cast at hk
    linarith
  refine Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr ?_, ?_⟩
  · rw [Nat.lt_succ_iff]
    refine Nat.le_floor ?_
    rw [le_div_iff₀ hpi]
    have htle : t * ℓ ≤ T * ℓ := mul_le_mul_of_nonneg_right htT hℓ.le
    nlinarith
  · rw [← hval]
    field_simp

/-- The sign pattern of the orbit on a set of steps. -/
def pattern {ι : Type*} (ℓ : ι → ℝ) (t : ℝ) : ι → Prop := fun i => 0 < Real.cos (t * ℓ i)

open Classical in
/-- All zeros of the coordinates, on `[0, T]`. -/
def allZeros {ι : Type*} [Fintype ι] (ℓ : ι → ℝ) (T : ℝ) : Finset ℝ :=
  Finset.univ.biUnion fun i => cosZeros (ℓ i) T

open Classical in
/-- Between two times with no zero of any coordinate, the pattern does not change. -/
theorem pattern_eq_of_no_zero {ι : Type*} [Fintype ι] {ℓ : ι → ℝ} (hℓ : ∀ i, 0 < ℓ i) {T t₁ t₂ : ℝ}
    (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (hT : t₂ ≤ T)
    (hno : ∀ z ∈ allZeros ℓ T, z ∉ Set.Icc t₁ t₂) : pattern ℓ t₁ = pattern ℓ t₂ := by
  funext i
  simp only [pattern, eq_iff_iff]
  have hnoz : ∀ t ∈ Set.Icc t₁ t₂, Real.cos (t * ℓ i) ≠ 0 := by
    intro t ht hz
    refine hno t ?_ ht
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
      mem_cosZeros (hℓ i) (h0.trans ht.1) (ht.2.trans hT) hz⟩
  have hc : ContinuousOn (fun t => Real.cos (t * ℓ i)) (Set.Icc t₁ t₂) := by fun_prop
  constructor
  · intro h1
    by_contra h2
    have h3 : Real.cos (t₂ * ℓ i) ≤ 0 := not_lt.mp h2
    obtain ⟨t, ht, hz⟩ := intermediate_value_Icc' h12 hc ⟨h3, h1.le⟩
    exact hnoz t ht hz
  · intro h2
    by_contra h1
    have h3 : Real.cos (t₁ * ℓ i) ≤ 0 := not_lt.mp h1
    obtain ⟨t, ht, hz⟩ := intermediate_value_Icc h12 hc ⟨h3, h2.le⟩
    exact hnoz t ht hz

open Classical in
/-- The position of a time among the zeros: twice the number of zeros below it, plus one if it is a zero. -/
def zeroIndex (Z : Finset ℝ) (t : ℝ) : ℕ :=
  2 * (Z.filter (· < t)).card + if t ∈ Z then 1 else 0

open Classical in
/-- Two times with the same index have no zero between them, or coincide. -/
theorem no_zero_of_zeroIndex_eq {Z : Finset ℝ} {t₁ t₂ : ℝ} (h12 : t₁ < t₂)
    (h : zeroIndex Z t₁ = zeroIndex Z t₂) : ∀ z ∈ Z, z ∉ Set.Icc t₁ t₂ := by
  intro z hz hmem
  have hsub : Z.filter (· < t₁) ⊆ Z.filter (· < t₂) := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨h1, h2.trans h12⟩
  have hc := Finset.card_le_card hsub
  unfold zeroIndex at h
  by_cases h1 : z = t₁
  · -- `t₁` is a zero, so it is counted below `t₂`.
    subst h1
    have hstrict : (Z.filter (· < z)).card < (Z.filter (· < t₂)).card := by
      refine Finset.card_lt_card ⟨hsub, fun hall => ?_⟩
      have := hall (Finset.mem_filter.mpr ⟨hz, h12⟩)
      exact lt_irrefl z (Finset.mem_filter.mp this).2
    rw [if_pos hz] at h
    split_ifs at h <;> omega
  · have hlt1 : t₁ < z := lt_of_le_of_ne hmem.1 (Ne.symm h1)
    by_cases h2 : z = t₂
    · -- `t₂` is a zero, and the counts agree only with a parity contradiction.
      subst h2
      rw [if_pos hz] at h
      by_cases h3 : t₁ ∈ Z
      · have hstrict : (Z.filter (· < t₁)).card < (Z.filter (· < z)).card := by
          refine Finset.card_lt_card ⟨hsub, fun hall => ?_⟩
          have := hall (Finset.mem_filter.mpr ⟨h3, h12⟩)
          exact lt_irrefl t₁ (Finset.mem_filter.mp this).2
        rw [if_pos h3] at h
        omega
      · rw [if_neg h3] at h
        omega
    · have hlt2 : z < t₂ := lt_of_le_of_ne hmem.2 h2
      have hstrict : (Z.filter (· < t₁)).card < (Z.filter (· < t₂)).card := by
        refine Finset.card_lt_card ⟨hsub, fun hall => ?_⟩
        have := hall (Finset.mem_filter.mpr ⟨hz, hlt2⟩)
        exact lt_asymm hlt1 (Finset.mem_filter.mp this).2
      split_ifs at h <;> omega

open Classical in
/-- **The orbit visits few sign patterns.** On `[0, T]`, the number of sign patterns visited is at most `2 Σ_i (⌊Tℓ_i/π⌋ + 1) + 1`. -/
theorem card_patterns_le {ι : Type*} [Fintype ι] {ℓ : ι → ℝ} (hℓ : ∀ i, 0 < ℓ i) {T : ℝ}
    (A : Finset ℝ) (hA : ∀ t ∈ A, t ∈ Set.Icc 0 T) :
    (A.image (pattern ℓ)).card ≤ 2 * ∑ i, (⌊T * ℓ i / Real.pi⌋₊ + 1) + 1 := by
  set Z := allZeros ℓ T with hZ
  have hZcard : Z.card ≤ ∑ i, (⌊T * ℓ i / Real.pi⌋₊ + 1) :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun i _ => card_cosZeros_le (ℓ i) T)
  -- The pattern factors through the index.
  have hfactor : ∀ t₁ ∈ A, ∀ t₂ ∈ A, zeroIndex Z t₁ = zeroIndex Z t₂ →
      pattern ℓ t₁ = pattern ℓ t₂ := by
    intro t₁ h₁ t₂ h₂ h
    rcases lt_trichotomy t₁ t₂ with hlt | heq | hgt
    · exact pattern_eq_of_no_zero hℓ (hA t₁ h₁).1 hlt.le (hA t₂ h₂).2
        (no_zero_of_zeroIndex_eq hlt h)
    · rw [heq]
    · exact (pattern_eq_of_no_zero hℓ (hA t₂ h₂).1 hgt.le (hA t₁ h₁).2
        (no_zero_of_zeroIndex_eq hgt h.symm)).symm
  have hbound : ∀ t, zeroIndex Z t ≤ 2 * Z.card := by
    intro t
    unfold zeroIndex
    by_cases ht : t ∈ Z
    · have h1 : (Z.filter (· < t)).card < Z.card := by
        refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun hall => ?_⟩
        exact lt_irrefl t (Finset.mem_filter.mp (hall ht)).2
      rw [if_pos ht]
      omega
    · have h1 : (Z.filter (· < t)).card ≤ Z.card := Finset.card_filter_le _ _
      rw [if_neg ht]
      omega
  have hcard : (A.image (pattern ℓ)).card ≤ (A.image (zeroIndex Z)).card := by
    -- Choose a representative of each pattern; the index is injective on representatives.
    have hchoose : ∀ P ∈ A.image (pattern ℓ), ∃ t ∈ A, pattern ℓ t = P := fun P hP =>
      Finset.mem_image.mp hP
    choose! rep hrep1 hrep2 using hchoose
    refine Finset.card_le_card_of_injOn (fun P => zeroIndex Z (rep P)) (fun P hP => ?_) ?_
    · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨rep P, hrep1 P hP, rfl⟩)
    · intro P hP Q hQ he
      have h := hfactor _ (hrep1 P hP) _ (hrep1 Q hQ) he
      rwa [hrep2 P hP, hrep2 Q hQ] at h
  have hindex : (A.image (zeroIndex Z)).card ≤ 2 * Z.card + 1 := by
    have hsub : A.image (zeroIndex Z) ⊆ Finset.range (2 * Z.card + 1) := by
      intro n hn
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound t))
    simpa using Finset.card_le_card hsub
  have hfin := hcard.trans hindex
  omega

open Classical in
/-- **Below the mixing time the orbit misses a box.** As soon as `2 Σ_i (⌊Tℓ_i/π⌋ + 1) + 1 < 2^{|ι|}`, some sign pattern is not attained on `[0, T]`. -/
theorem exists_pattern_not_attained {ι : Type*} [Fintype ι] {ℓ : ι → ℝ} (hℓ : ∀ i, 0 < ℓ i) {T : ℝ}
    (hlt : 2 * ∑ i, (⌊T * ℓ i / Real.pi⌋₊ + 1) + 1 < 2 ^ Fintype.card ι) :
    ∃ P : ι → Prop, ∀ t ∈ Set.Icc 0 T, pattern ℓ t ≠ P := by
  by_contra hcon
  push Not at hcon
  choose! τ hτ1 hτ2 using hcon
  have hle := card_patterns_le hℓ ((Finset.univ : Finset (ι → Prop)).image τ) (by
    intro t ht
    obtain ⟨P, -, rfl⟩ := Finset.mem_image.mp ht
    exact hτ1 P)
  have hall : ((Finset.univ : Finset (ι → Prop)).image τ).image (pattern ℓ) = Finset.univ := by
    ext P
    simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    exact ⟨τ P, ⟨P, rfl⟩, hτ2 P⟩
  have hProp : Fintype.card Prop = 2 := by simp
  rw [hall, Finset.card_univ, Fintype.card_fun, hProp] at hle
  omega

end

end GaloisForLFunctions.PrimeTorusTheory
