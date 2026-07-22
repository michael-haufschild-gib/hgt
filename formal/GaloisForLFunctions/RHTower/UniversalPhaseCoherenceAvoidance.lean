import GaloisForLFunctions.RHTower.UniversalPhaseCoherenceTargetMeasure

/-!
# Universal finite-time phase-coherence avoidance

The near-diagonal coherence target has exponentially small Haar volume.  Integer
multiplication preserves Haar measure on the phase torus, so a finite union
bound produces a single phase vector whose first `N` iterates all avoid that
target.  No independence or genericity of the iterates is assumed.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace RHTower

/-- The initial `N` orbit hits of the `1 - η` coherence target.  Index `k`
represents the positive clock `k + 1`. -/
def torusCoherenceHitUnion {d : Type*} [Fintype d]
    (N : ℕ) (η : ℝ) : Set (d → UnitAddCircle) :=
  ⋃ k : Fin N,
    (fun x : d → UnitAddCircle ↦ ((k.1 + 1 : ℕ) : ℤ) • x) ⁻¹'
      torusCoherenceTarget (d := d) η

/-- Every nonzero integer clock preserves the Haar volume of the coherence
target on the full phase torus. -/
theorem measureReal_torusCoherenceTarget_zsmul_preimage
    {d : Type*} [Fintype d]
    (η : ℝ) {n : ℤ} (hn : n ≠ 0) :
    volume.real ((fun x : d → UnitAddCircle ↦ n • x) ⁻¹'
        torusCoherenceTarget (d := d) η) =
      volume.real (torusCoherenceTarget (d := d) η) := by
  have hmp := Measure.measurePreserving_zsmul
    (G := d → UnitAddCircle) volume hn
  simp only [measureReal_def]
  rw [← Measure.map_apply hmp.measurable
    (measurableSet_torusCoherenceTarget (d := d) η), hmp.map_eq]

/-- Union bound for the first `N` coherence hits. -/
theorem measureReal_torusCoherenceHitUnion_le
    {d : Type*} [Fintype d]
    (N : ℕ) (η : ℝ) :
    volume.real (torusCoherenceHitUnion (d := d) N η) ≤
      (N : ℝ) * volume.real (torusCoherenceTarget (d := d) η) := by
  calc
    volume.real (torusCoherenceHitUnion (d := d) N η) ≤
        ∑ k : Fin N,
          volume.real ((fun x : d → UnitAddCircle ↦
            ((k.1 + 1 : ℕ) : ℤ) • x) ⁻¹'
              torusCoherenceTarget (d := d) η) := by
      exact measureReal_iUnion_fintype_le _
    _ = ∑ _k : Fin N,
        volume.real (torusCoherenceTarget (d := d) η) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact measureReal_torusCoherenceTarget_zsmul_preimage η (by omega)
    _ = (N : ℝ) * volume.real (torusCoherenceTarget (d := d) η) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]

/-- Explicit first-hit union bound obtained from the optimized Haar target
estimate. -/
theorem measureReal_torusCoherenceHitUnion_le_optimized
    {d : Type*} [Fintype d] [Nonempty d]
    (N : ℕ) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    volume.real (torusCoherenceHitUnion (d := d) N η) ≤
      (N : ℝ) * ((Fintype.card d : ℝ) *
        Real.exp ((Fintype.card d : ℝ) / 2) *
          Real.sqrt (Real.pi * η / 2) ^ (Fintype.card d - 1)) := by
  calc
    volume.real (torusCoherenceHitUnion (d := d) N η) ≤
        (N : ℝ) * volume.real (torusCoherenceTarget (d := d) η) :=
      measureReal_torusCoherenceHitUnion_le N η
    _ ≤ (N : ℝ) * ((Fintype.card d : ℝ) *
        Real.exp ((Fintype.card d : ℝ) / 2) *
          Real.sqrt (Real.pi * η / 2) ^ (Fintype.card d - 1)) := by
      exact mul_le_mul_of_nonneg_left
        (measureReal_torusCoherenceTarget_le_optimized hη0 hη1)
        (Nat.cast_nonneg N)

/-- **Finite-time coherence avoidance law.**  If `N` times the optimized
coherence-target volume bound is below one, one phase vector has no
`1 - η` coherent clock among the first `N` positive clocks. -/
theorem exists_torus_phase_avoiding_coherence_until
    {d : Type*} [Fintype d] [Nonempty d]
    (N : ℕ) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hbudget :
      (N : ℝ) * ((Fintype.card d : ℝ) *
        Real.exp ((Fintype.card d : ℝ) / 2) *
          Real.sqrt (Real.pi * η / 2) ^ (Fintype.card d - 1)) < 1) :
    ∃ x : d → UnitAddCircle, ∀ k : Fin N,
      ‖equalPhaseAmplitude (fun j ↦
        fourier 1 (((k.1 + 1 : ℕ) : ℤ) • x j))‖ < 1 - η := by
  have hhit : volume.real (torusCoherenceHitUnion (d := d) N η) < 1 :=
    (measureReal_torusCoherenceHitUnion_le_optimized N hη0 hη1).trans_lt
      hbudget
  have hexists : ∃ x : d → UnitAddCircle,
      x ∉ torusCoherenceHitUnion (d := d) N η := by
    by_contra h
    push Not at h
    have hsub : (Set.univ : Set (d → UnitAddCircle)) ⊆
        torusCoherenceHitUnion (d := d) N η := fun x _hx ↦ h x
    have hmeasure :
        volume.real (Set.univ : Set (d → UnitAddCircle)) ≤
          volume.real (torusCoherenceHitUnion (d := d) N η) :=
      measureReal_mono hsub
    rw [measureReal_torus_univ] at hmeasure
    exact (not_lt_of_ge hmeasure) hhit
  obtain ⟨x, hx⟩ := hexists
  refine ⟨x, fun k ↦ ?_⟩
  have hnot : ((fun y : d → UnitAddCircle ↦
      ((k.1 + 1 : ℕ) : ℤ) • y) x) ∉
        torusCoherenceTarget (d := d) η := by
    intro hk
    apply hx
    rw [torusCoherenceHitUnion, Set.mem_iUnion]
    exact ⟨k, hk⟩
  rw [torusCoherenceTarget, Set.mem_setOf_eq] at hnot
  simpa only [Pi.smul_apply] using lt_of_not_ge hnot

/-- A canonical real angular frequency representing one additive-circle
coordinate. -/
def torusRealFrequency (x : UnitAddCircle) : ℝ :=
  2 * Real.pi * (AddCircle.equivIoc 1 (-(1 / 2 : ℝ)) x).1

/-- The real representative produces exactly the same positive clocks as the
corresponding torus coordinate. -/
theorem exp_torusRealFrequency_eq_fourier_zsmul
    (x : UnitAddCircle) (n : ℕ) :
    Complex.exp (Complex.I * (((n : ℝ) * torusRealFrequency x : ℝ) : ℂ)) =
      fourier 1 (((n : ℕ) : ℤ) • x) := by
  let y : ℝ := (AddCircle.equivIoc 1 (-(1 / 2 : ℝ)) x).1
  have hy : (y : UnitAddCircle) = x := AddCircle.coe_equivIoc
  have hnsmul : ((n : ℤ) • x) = n • x := by simp
  calc
    Complex.exp (Complex.I * (((n : ℝ) * torusRealFrequency x : ℝ) : ℂ)) =
        fourier 1 (n • (y : UnitAddCircle)) := by
      rw [← AddCircle.coe_nsmul, fourier_coe_apply]
      dsimp only [torusRealFrequency, y]
      push_cast
      congr 1
      ring
    _ = fourier 1 (((n : ℕ) : ℤ) • x) := by rw [hy, hnsmul]

/-- Real-frequency form of finite-time coherence avoidance. -/
theorem exists_real_frequency_avoiding_coherence_until
    {d : Type*} [Fintype d] [Nonempty d]
    (N : ℕ) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hbudget :
      (N : ℝ) * ((Fintype.card d : ℝ) *
        Real.exp ((Fintype.card d : ℝ) / 2) *
          Real.sqrt (Real.pi * η / 2) ^ (Fintype.card d - 1)) < 1) :
    ∃ ω : d → ℝ, ∀ k : Fin N,
      ‖equalPhaseAmplitude (fun j ↦
        Complex.exp (Complex.I *
          ((((k.1 + 1 : ℕ) : ℝ) * ω j : ℝ) : ℂ)))‖ < 1 - η := by
  obtain ⟨x, hx⟩ := exists_torus_phase_avoiding_coherence_until
    N hη0 hη1 hbudget
  refine ⟨fun j ↦ torusRealFrequency (x j), fun k ↦ ?_⟩
  simpa only [exp_torusRealFrequency_eq_fourier_zsmul] using hx k

/-- A finite clock `N` is a universal `1 - η` coherence deadline in
dimension `d` if every real frequency vector has a coherent positive clock no
larger than `N`. -/
def IsUniversalPhaseCoherenceDeadline
    (d : ℕ) (η : ℝ) (N : ℕ) : Prop :=
  ∀ ω : Fin d → ℝ, ∃ n : ℕ, 0 < n ∧ n ≤ N ∧
    1 - η ≤ ‖phaseClockAmplitude ω n‖

/-- The simultaneous-recurrence ceiling is a universal coherence deadline
whenever its quadratic phase defect is at most the requested defect. -/
theorem isUniversalPhaseCoherenceDeadline_recurrence
    {d Q : ℕ} (hd : 0 < d) {η : ℝ}
    (hdefect : (2 * Real.pi / (Q + 1 : ℝ)) ^ 2 / 2 ≤ η) :
    IsUniversalPhaseCoherenceDeadline d η ((Q + 1) ^ d) := by
  intro ω
  obtain ⟨n, hn0, hnQ, hncoh⟩ :=
    exists_phaseClockAmplitude_coherence_quantitative hd ω (Q := Q)
  refine ⟨n, hn0, hnQ, ?_⟩
  exact (sub_le_sub_left hdefect 1).trans hncoh

/-- Below the Haar budget, `N` is not a universal coherence deadline. -/
theorem not_isUniversalPhaseCoherenceDeadline_of_budget
    {d N : ℕ} (hd : 0 < d) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hbudget :
      (N : ℝ) * ((d : ℝ) * Real.exp ((d : ℝ) / 2) *
        Real.sqrt (Real.pi * η / 2) ^ (d - 1)) < 1) :
    ¬ IsUniversalPhaseCoherenceDeadline d η N := by
  letI : NeZero d := ⟨hd.ne'⟩
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  obtain ⟨ω, hω⟩ := exists_real_frequency_avoiding_coherence_until
    (d := Fin d) N hη0 hη1 (by simpa using hbudget)
  intro hdeadline
  obtain ⟨n, hn0, hnN, hncoh⟩ := hdeadline ω
  have hnlt : n - 1 < N := by omega
  let k : Fin N := ⟨n - 1, hnlt⟩
  have hkval : k.1 + 1 = n := by dsimp only [k]; omega
  have havoid := hω k
  rw [hkval] at havoid
  rw [phaseClockAmplitude_eq_equalPhaseAmplitude] at hncoh
  exact (not_lt_of_ge hncoh) havoid

end RHTower
