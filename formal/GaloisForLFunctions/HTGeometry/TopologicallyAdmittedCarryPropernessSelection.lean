import GaloisForLFunctions.HTGeometry.CompactAddGroupMetricReturnLaw
import GaloisForLFunctions.HTGeometry.TopologicallyAdmittedLatticeCarryCurrent

/-!
# Compact-phase carry properness and character selection

A real formation character dominated by lattice-carry traffic cannot survive a local uniform
traffic ceiling in compact phase topology. Compact recurrence supplies returns at arbitrarily large
word length, while the character and its compulsory carry current grow linearly. Every group
element may use its own invariant probability system, potential, and carry.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {K : Type*} [AddCommGroup K]

section CompactPhaseCharacterSelection

variable {A : Type*} [AddGroup A]
variable [PseudoEMetricSpace K] [IsIsometricVAdd Kᵃᵒᵖ K] [CompactSpace K]

/-- A real additive character locally bounded through a compact phase representation vanishes.
Continuity, density of the phase image, and a common gauge are not assumed. -/
theorem addMonoidHom_eq_zero_of_compactPhase_localBound
    (phase : A →+ K) (χ : A →+ ℝ)
    (r : ℝ≥0) (hr : r ≠ 0) (C : ℝ)
    (hlocal : ∀ a : A, edist (phase a) 0 ≤ 2 * r → |χ a| ≤ C) :
    χ = 0 := by
  ext a
  by_contra hχ
  have habs : 0 < |χ a| := abs_pos.mpr hχ
  obtain ⟨N, hN⟩ := exists_nat_gt (C / |χ a|)
  obtain ⟨n, hnN, hnreturn⟩ :=
    exists_large_nsmul_return_le_two_mul (phase a) r hr N
  have hphase : edist (phase (n • a)) 0 ≤ 2 * r := by
    simpa using hnreturn
  have hbound := hlocal (n • a) hphase
  have hscale : |χ (n • a)| = (n : ℝ) * |χ a| := by
    simp [abs_mul]
  have hstrict : C < (n : ℝ) * |χ a| := by
    calc
      C < (N : ℝ) * |χ a| := (div_lt_iff₀ habs).mp hN
      _ ≤ (n : ℝ) * |χ a| :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.le_of_lt hnN)) (abs_nonneg _)
  rw [hscale] at hbound
  exact (not_lt_of_ge hbound) hstrict

/-- Exact linear lower bound forced by current recovery on every natural multiple. -/
theorem carryTraffic_nsmul_current_le
    (χ : A →+ ℝ) (τ : A → ℝ) (L : ℝ)
    (hcurrent : ∀ a : A, |χ a| ≤ L * τ a) (a : A) (n : ℕ) :
    (n : ℝ) * |χ a| ≤ L * τ (n • a) := by
  simpa [abs_mul] using hcurrent (n • a)

/-- **Compact-phase carry-properness selection.** If carry traffic dominates the real formation
current and is uniformly bounded on one compact-phase ball, the formation character is zero. -/
theorem addMonoidHom_eq_zero_of_compactPhase_localTrafficBound
    (phase : A →+ K) (χ : A →+ ℝ)
    (r : ℝ≥0) (hr : r ≠ 0) (L C : ℝ) (hL : 0 < L)
    (τ : A → ℝ)
    (hcurrent : ∀ a : A, |χ a| ≤ L * τ a)
    (htraffic : ∀ a : A, edist (phase a) 0 ≤ 2 * r → τ a ≤ C) :
    χ = 0 := by
  apply addMonoidHom_eq_zero_of_compactPhase_localBound phase χ r hr (L * C)
  intro a ha
  exact (hcurrent a).trans (mul_le_mul_of_nonneg_left (htraffic a ha) hL.le)

/-- Quantitative positive survivor: beyond every word-length threshold there is a compact-phase
return whose carry traffic pays the full linear character current. -/
theorem exists_cofinal_return_with_carryTraffic_linear_lowerBound
    (phase : A →+ K) (χ : A →+ ℝ)
    (r : ℝ≥0) (hr : r ≠ 0) (L : ℝ) (τ : A → ℝ)
    (hcurrent : ∀ a : A, |χ a| ≤ L * τ a)
    (a : A) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ edist (phase (n • a)) 0 ≤ 2 * r ∧
      (n : ℝ) * |χ a| ≤ L * τ (n • a) := by
  obtain ⟨n, hnN, hnreturn⟩ :=
    exists_large_nsmul_return_le_two_mul (phase a) r hr N
  refine ⟨n, hnN, ?_, carryTraffic_nsmul_current_le χ τ L hcurrent a n⟩
  simpa using hnreturn

end CompactPhaseCharacterSelection

/-- One compensated-lift fibre. The carrier, invariant probability system, potential, and carry
are bundled so a family may choose all of them independently at every source element. -/
structure CompensatedLiftFiber (L chi : ℝ) where
  Ω : Type u
  [measurableSpace : MeasurableSpace Ω]
  μ : Measure Ω
  [probabilityMeasure : IsProbabilityMeasure μ]
  T : Ω → Ω
  hT : MeasurePreserving T μ μ
  u : Ω → ℝ
  k : Ω → ℝ
  hu : Integrable u μ
  hk : Integrable k μ
  hlift : (fun x => u (T x) - u x + L * k x) =ᵐ[μ] fun _ => chi

namespace CompensatedLiftFiber

/-- Absolute `L¹` carry traffic of one compensated-lift fibre. -/
def traffic {L chi : ℝ} (F : CompensatedLiftFiber L chi) : ℝ :=
  letI := F.measurableSpace
  ∫ x, |F.k x| ∂F.μ

/-- Exact invariant current recovery bounds character magnitude by absolute carry traffic. -/
theorem abs_character_le_period_mul_traffic {L chi : ℝ} (hL : 0 ≤ L)
    (F : CompensatedLiftFiber L chi) :
    |chi| ≤ L * F.traffic := by
  letI := F.measurableSpace
  letI := F.probabilityMeasure
  have hcurrent :=
    compensatedLift_probability_current F.μ F.T F.hT L chi F.u F.k F.hu F.hk F.hlift
  calc
    |chi| = |L * ∫ x, F.k x ∂F.μ| := congrArg abs hcurrent
    _ = L * |∫ x, F.k x ∂F.μ| := by rw [abs_mul, abs_of_nonneg hL]
    _ ≤ L * ∫ x, |F.k x| ∂F.μ :=
      mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hL
    _ = L * F.traffic := by rfl

end CompensatedLiftFiber

section CompensatedLiftFamilySelection

variable {A : Type*} [AddGroup A]
variable [PseudoEMetricSpace K] [IsIsometricVAdd Kᵃᵒᵖ K] [CompactSpace K]

/-- **Adaptive-fibre selection law.** Every source element may use a separate probability space,
invariant observer, integrable potential, and integrable carry. A single local bound on their
absolute carry traffic still forces the recovered real character to vanish. -/
theorem compensatedLiftFamily_character_eq_zero_of_localTrafficBound
    (phase : A →+ K) (χ : A →+ ℝ)
    (r : ℝ≥0) (hr : r ≠ 0) (L C : ℝ) (hL : 0 < L)
    (F : ∀ a : A, CompensatedLiftFiber L (χ a))
    (htraffic : ∀ a : A, edist (phase a) 0 ≤ 2 * r → (F a).traffic ≤ C) :
    χ = 0 := by
  apply addMonoidHom_eq_zero_of_compactPhase_localTrafficBound
    phase χ r hr L C hL (fun a => (F a).traffic)
  · intro a
    exact (F a).abs_character_le_period_mul_traffic hL.le
  · exact htraffic

/-- Adaptive-fibre quantitative law: a nonzero formation character forces linear traffic on
cofinally large compact-phase returns, regardless of how gauges and observer systems vary. -/
theorem compensatedLiftFamily_exists_cofinal_return_with_linearTraffic
    (phase : A →+ K) (χ : A →+ ℝ)
    (r : ℝ≥0) (hr : r ≠ 0) (L : ℝ) (hL : 0 ≤ L)
    (F : ∀ a : A, CompensatedLiftFiber L (χ a))
    (a : A) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ edist (phase (n • a)) 0 ≤ 2 * r ∧
      (n : ℝ) * |χ a| ≤ L * (F (n • a)).traffic := by
  apply exists_cofinal_return_with_carryTraffic_linear_lowerBound
    phase χ r hr L (fun b => (F b).traffic) _ a N
  intro b
  exact (F b).abs_character_le_period_mul_traffic hL

end CompensatedLiftFamilySelection

end

end GaloisForLFunctions.HTGeometry
