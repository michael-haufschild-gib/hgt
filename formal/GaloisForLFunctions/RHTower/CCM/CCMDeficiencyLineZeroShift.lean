import GaloisForLFunctions.RHTower.CCM.CCMCofinalFloorCriterion

/-!
# The shifted deficiency line reaches zero shift exactly at the floor

Suzuki's boundary construction for the restricted Weil form starts from the shifted form
`T_λ = A - λ` and requires it to be strictly positive, which pins the shift strictly below the
bottom of the spectrum.  This module formalizes the variational content of that constraint.

* `shiftAdmissible_of_lt_floor` and `le_floor_of_shiftAdmissible` are the two unconditional halves:
  a shift below the floor is admissible, and an admissible shift is at most the floor.
* `shiftAdmissible_iff_lt_floor` closes them into an equivalence once the floor is **attained** —
  the compact-resolvent input that makes the floor a lowest eigenvalue rather than a mere infimum.
* `zero_shiftAdmissible_iff_floor_pos` is then the zero-shift case: zero shift is admissible at every
  aperture exactly when every finite-aperture floor is strictly positive.
* `hasCofinalShiftLine_iff_floor_nonneg` is the cofinal equivalence: a shift function strictly below
  the floor at every aperture whose values tend to zero along some apertures tending to infinity
  exists **iff** no floor is negative.  The forward direction is the no-evacuation law — a negative
  floor at one aperture pins the shift below `-δ` cofinally — and the backward direction is the
  explicit line `λ a = -exp (-a)`.

The last statement is the one that retires the shifted determinant line as a shortcut: producing
such a line is not a preliminary step towards positivity, it is equivalent to it.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology Set MeasureTheory

variable {V : Type*}

/-! ## Admissible shifts -/

/-- The shifted form `Q - λ N` is strictly positive on the trial domain. -/
def ShiftAdmissible (Q N : V → ℝ) (D : Set V) (lam : ℝ) : Prop :=
  ∀ v ∈ D, N v ≠ 0 → lam * N v < Q v

/-- A shift strictly below the floor is admissible. -/
theorem shiftAdmissible_of_lt_floor (Q N : V → ℝ) {D : Set V} {lam : ℝ}
    (hbdd : BddBelow (rayleighQuotientSet Q N D)) (hN : ∀ v ∈ D, N v ≠ 0 → 0 < N v)
    (h : lam < rayleighFloor Q N D) : ShiftAdmissible Q N D lam := by
  intro v hv hNv
  have hpos := hN v hv hNv
  have hq : rayleighFloor Q N D ≤ Q v / N v := csInf_le hbdd (mem_rayleighQuotientSet Q N hv hNv)
  have hlt : lam < Q v / N v := lt_of_lt_of_le h hq
  rw [lt_div_iff₀ hpos] at hlt
  exact hlt

/-- An admissible shift is at most the floor, provided the trial set is nonempty.  Without that
the shifted-positivity condition is vacuous and carries no information. -/
theorem le_floor_of_shiftAdmissible (Q N : V → ℝ) {D : Set V} {lam : ℝ}
    (hne : (rayleighQuotientSet Q N D).Nonempty)
    (hN : ∀ v ∈ D, N v ≠ 0 → 0 < N v) (h : ShiftAdmissible Q N D lam) :
    lam ≤ rayleighFloor Q N D := by
  refine le_csInf hne ?_
  rintro r ⟨v, hv, hNv, rfl⟩
  have hpos := hN v hv hNv
  have := h v hv hNv
  rw [le_div_iff₀ hpos]
  linarith

/-- **Admissibility is exactly the strict inequality once the floor is attained.**  Attainment is
the compact-resolvent input: the floor is the lowest eigenvalue, not a mere infimum. -/
theorem shiftAdmissible_iff_lt_floor (Q N : V → ℝ) {D : Set V}
    (hbdd : BddBelow (rayleighQuotientSet Q N D)) (hN : ∀ v ∈ D, N v ≠ 0 → 0 < N v)
    (hatt : ∃ v ∈ D, N v ≠ 0 ∧ Q v / N v = rayleighFloor Q N D) {lam : ℝ} :
    ShiftAdmissible Q N D lam ↔ lam < rayleighFloor Q N D := by
  refine ⟨fun h => ?_, shiftAdmissible_of_lt_floor Q N hbdd hN⟩
  obtain ⟨v, hv, hNv, hval⟩ := hatt
  have hpos := hN v hv hNv
  have hstrict := h v hv hNv
  rw [← hval, lt_div_iff₀ hpos]
  exact hstrict

/-- **Zero shift is admissible at every aperture exactly when every floor is strictly positive.** -/
theorem zero_shiftAdmissible_iff_floor_pos (Q N : V → ℝ) {D : ℝ → Set V}
    (hbdd : ∀ a : ℝ, BddBelow (rayleighQuotientSet Q N (D a)))
    (hN : ∀ a : ℝ, ∀ v ∈ D a, N v ≠ 0 → 0 < N v)
    (hatt : ∀ a : ℝ, ∃ v ∈ D a, N v ≠ 0 ∧ Q v / N v = rayleighFloor Q N (D a)) :
    (∀ a : ℝ, ShiftAdmissible Q N (D a) 0) ↔ ∀ a : ℝ, 0 < rayleighFloor Q N (D a) := by
  constructor
  · intro h a
    exact (shiftAdmissible_iff_lt_floor Q N (hbdd a) (hN a) (hatt a)).mp (h a)
  · intro h a
    exact (shiftAdmissible_iff_lt_floor Q N (hbdd a) (hN a) (hatt a)).mpr (h a)

/-! ## The cofinal shifted line -/

/-- A cofinal shifted line: a shift strictly below the floor at every aperture, whose values tend to
zero along some apertures tending to infinity. -/
def HasCofinalShiftLine (Q N : V → ℝ) (D : ℝ → Set V) : Prop :=
  ∃ lam : ℝ → ℝ, (∀ a : ℝ, lam a < rayleighFloor Q N (D a)) ∧
    ∃ aseq : ℕ → ℝ, Tendsto aseq atTop atTop ∧
      Tendsto (fun j => lam (aseq j)) atTop (nhds 0)

/-- **The cofinal equivalence.**  A cofinal shifted line exists exactly when no floor is negative.
Producing such a line is therefore not a step towards positivity; it is positivity. -/
theorem hasCofinalShiftLine_iff_floor_nonneg (Q N : V → ℝ) {D : ℝ → Set V}
    (hmono : ∀ {b c : ℝ}, b ≤ c → D b ⊆ D c)
    (hbdd : ∀ b : ℝ, BddBelow (rayleighQuotientSet Q N (D b))) :
    HasCofinalShiftLine Q N D ↔ ∀ a : ℝ, 0 ≤ rayleighFloor Q N (D a) := by
  constructor
  · rintro ⟨lam, hlt, aseq, hseq, hlim⟩ a
    by_contra hneg
    rw [not_le] at hneg
    rcases (rayleighQuotientSet Q N (D a)).eq_empty_or_nonempty with hemp | hnea
    · rw [rayleighFloor, hemp, Real.sInf_empty] at hneg
      exact absurd hneg (lt_irrefl 0)
    set δ : ℝ := -rayleighFloor Q N (D a) with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    have h1 : ∀ᶠ j in atTop, a ≤ aseq j := hseq.eventually_ge_atTop a
    have h2 : ∀ᶠ j in atTop, lam (aseq j) < -δ := by
      filter_upwards [h1] with j hj
      have hant := rayleighFloor_antitone Q N (hmono hj) (hbdd (aseq j)) hnea
      have hlam := hlt (aseq j)
      rw [hδ]
      linarith
    have h3 : ∀ᶠ j in atTop, -δ < lam (aseq j) :=
      hlim.eventually (eventually_gt_nhds (show -δ < (0 : ℝ) by linarith))
    obtain ⟨j, hj2, hj3⟩ := (h2.and h3).exists
    linarith
  · intro h
    refine ⟨fun a => -Real.exp (-a), fun a => ?_, fun j => (j : ℝ), tendsto_natCast_atTop_atTop, ?_⟩
    · have hpos : (0 : ℝ) < Real.exp (-a) := Real.exp_pos _
      have := h a
      linarith
    · have hcast : Tendsto (fun j : ℕ => -((j : ℝ))) atTop atBot :=
        tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
      have hexp : Tendsto (fun j : ℕ => Real.exp (-((j : ℝ)))) atTop (nhds 0) :=
        Real.tendsto_exp_atBot.comp hcast
      simpa using hexp.neg

/-- The zero-shift form of the equivalence: a cofinal shifted line coexists with a negative floor
nowhere, so it cannot be produced below an unknown negative floor. -/
theorem not_hasCofinalShiftLine_of_negative_floor (Q N : V → ℝ) {D : ℝ → Set V}
    (hmono : ∀ {b c : ℝ}, b ≤ c → D b ⊆ D c)
    (hbdd : ∀ b : ℝ, BddBelow (rayleighQuotientSet Q N (D b)))
    {a : ℝ} (hneg : rayleighFloor Q N (D a) < 0) : ¬ HasCofinalShiftLine Q N D := by
  intro h
  have := (hasCofinalShiftLine_iff_floor_nonneg Q N hmono hbdd).mp h a
  linarith

/-! ## The aperture-restricted instantiation -/

/-- **The cofinal equivalence for the restricted kernel form.** -/
theorem hasCofinalShiftLine_restrictedKernel_iff (K : ℝ → ℝ)
    (hbdd : ∀ b : ℝ, BddBelow
      (rayleighQuotientSet (fun v => diffBilinForm K v v) sqMass (apertureDomain b))) :
    HasCofinalShiftLine (fun v => diffBilinForm K v v) sqMass apertureDomain
      ↔ ∀ a : ℝ, 0 ≤ restrictedKernelFloor K a :=
  hasCofinalShiftLine_iff_floor_nonneg _ _ (fun h => apertureDomain_mono h) hbdd

/-- One compactly supported test with negative energy destroys every cofinal shifted line. -/
theorem not_hasCofinalShiftLine_restrictedKernel_of_negative_test (K : ℝ → ℝ)
    (hbdd : ∀ b : ℝ, BddBelow
      (rayleighQuotientSet (fun v => diffBilinForm K v v) sqMass (apertureDomain b)))
    {a : ℝ} {v : ℝ → ℝ} (hv : v ∈ apertureDomain a) (hN : 0 < sqMass v)
    (hQ : diffBilinForm K v v < 0) :
    ¬ HasCofinalShiftLine (fun v => diffBilinForm K v v) sqMass apertureDomain := by
  refine not_hasCofinalShiftLine_of_negative_floor _ _ (fun h => apertureDomain_mono h) hbdd
    (a := a) ?_
  refine lt_of_le_of_lt (rayleighFloor_le_of_witness _ _ (hbdd a) hv hN.ne' le_rfl) ?_
  exact div_neg_of_neg_of_pos hQ hN

end GaloisForLFunctions.RHTower

end
