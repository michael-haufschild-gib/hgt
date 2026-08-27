import GaloisForLFunctions.RHTower.XiPhysicalPrimeEndpointActiveMertensUltravioletEnergy
import GaloisForLFunctions.RHTower.XiPhysicalPrimeLogApertureDispersion

/-!
# Physical prime-aperture source-retention wall

Weighted Hilbert Cauchy--Schwarz sharpens the aperture carrier's global `A W²` bound to
`W L`, where `W` is total prime weight and `L` is weighted clipped length. Consequently an
active packet's normalized coherent dispersion is at most raw aperture width `k - m`.

Thus shrinking width is not a free ultraviolet regularization: it forces the normalized physical
FCRJ source itself to vanish. No uniformly positive normalized source floor can survive such a
schedule. This is source-specific; weighted Cauchy--Schwarz and centered-indicator variance are
standard parent Hilbert-space facts.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- One centered clipped prime carrier has squared norm at most its clipped length. -/
theorem norm_sq_xiPhysicalPrimeLogCenteredApertureCarrier_le_length
    {A : ℝ} (hA : 0 < A) (m k : ℝ) (p : Nat.Primes) :
    ‖xiPhysicalPrimeLogCenteredApertureCarrier A m k p‖ ^ 2 ≤
      xiPhysicalPrimeLogApertureLength A m k p := by
  rw [← real_inner_self_eq_norm_sq,
    real_inner_xiPhysicalPrimeLogCenteredApertureCarrier hA,
    xiPhysicalPrimeLogApertureFusionKernel_diagonal]
  have hsq : 0 ≤ xiPhysicalPrimeLogApertureLength A m k p ^ 2 / A := by
    positivity
  linarith

/-- Weighted Hilbert variance bound for the exact coherent physical carrier:
`‖P‖² ≤ W L`. -/
theorem norm_sq_xiPhysicalPrimeLogAggregateApertureCarrier_le
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k : ℝ) :
    ‖xiPhysicalPrimeLogAggregateApertureCarrier P A m k‖ ^ 2 ≤
      xiPhysicalPrimeLogEndpointTotalWeight P *
        xiPhysicalPrimeLogApertureWeightedLengthMass P A m k := by
  let w : Nat.Primes → ℝ := fun p => physicalPrimeEndpointWeight p
  let v : Nat.Primes → XiPhysicalApertureL2 :=
    fun p => xiPhysicalPrimeLogCenteredApertureCarrier A m k p
  let S : ℝ := ∑ p ∈ P, w p * ‖v p‖
  have hw : ∀ p ∈ P, 0 ≤ w p := fun p _ => (physicalPrimeEndpointWeight_pos p).le
  have htri : ‖xiPhysicalPrimeLogAggregateApertureCarrier P A m k‖ ≤ S := by
    rw [xiPhysicalPrimeLogAggregateApertureCarrier]
    calc
      ‖∑ p ∈ P, physicalPrimeEndpointWeight p •
          xiPhysicalPrimeLogCenteredApertureCarrier A m k p‖
          ≤ ∑ p ∈ P, ‖physicalPrimeEndpointWeight p •
            xiPhysicalPrimeLogCenteredApertureCarrier A m k p‖ := norm_sum_le _ _
      _ = S := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw p hp)]
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact Finset.sum_nonneg fun p hp => mul_nonneg (hw p hp) (norm_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq P
    (fun p => Real.sqrt (w p)) (fun p => Real.sqrt (w p) * ‖v p‖)
  have hcs' : S ^ 2 ≤
      (∑ p ∈ P, w p) * ∑ p ∈ P, w p * ‖v p‖ ^ 2 := by
    calc
      S ^ 2 = (∑ p ∈ P,
          Real.sqrt (w p) * (Real.sqrt (w p) * ‖v p‖)) ^ 2 := by
            congr 1
            apply Finset.sum_congr rfl
            intro p hp
            rw [← mul_assoc, Real.mul_self_sqrt (hw p hp)]
      _ ≤ (∑ p ∈ P, Real.sqrt (w p) ^ 2) *
          ∑ p ∈ P, (Real.sqrt (w p) * ‖v p‖) ^ 2 := hcs
      _ = (∑ p ∈ P, w p) * ∑ p ∈ P, w p * ‖v p‖ ^ 2 := by
        congr 1
        · apply Finset.sum_congr rfl
          intro p hp
          exact Real.sq_sqrt (hw p hp)
        · apply Finset.sum_congr rfl
          intro p hp
          rw [mul_pow, Real.sq_sqrt (hw p hp)]
  have hweighted : ∑ p ∈ P, w p * ‖v p‖ ^ 2 ≤
      xiPhysicalPrimeLogApertureWeightedLengthMass P A m k := by
    rw [xiPhysicalPrimeLogApertureWeightedLengthMass]
    apply Finset.sum_le_sum
    intro p hp
    exact mul_le_mul_of_nonneg_left
      (norm_sq_xiPhysicalPrimeLogCenteredApertureCarrier_le_length hA m k p)
      (hw p hp)
  calc
    ‖xiPhysicalPrimeLogAggregateApertureCarrier P A m k‖ ^ 2 ≤ S ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) hS).2 htri
    _ ≤ (∑ p ∈ P, w p) * ∑ p ∈ P, w p * ‖v p‖ ^ 2 := hcs'
    _ ≤ (∑ p ∈ P, w p) *
        xiPhysicalPrimeLogApertureWeightedLengthMass P A m k :=
      mul_le_mul_of_nonneg_left hweighted (Finset.sum_nonneg hw)
    _ = xiPhysicalPrimeLogEndpointTotalWeight P *
        xiPhysicalPrimeLogApertureWeightedLengthMass P A m k := by
      rw [xiPhysicalPrimeLogEndpointTotalWeight]

/-- Exact physical fusion energy obeys `E ≤ W L`. -/
theorem xiPhysicalPrimeLogApertureFusionEnergy_le_weight_mul_weightedLength
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k : ℝ) :
    xiPhysicalPrimeLogApertureFusionEnergy P A m k ≤
      xiPhysicalPrimeLogEndpointTotalWeight P *
        xiPhysicalPrimeLogApertureWeightedLengthMass P A m k := by
  rw [xiPhysicalPrimeLogApertureFusionEnergy_eq_norm_sq P hA]
  exact norm_sq_xiPhysicalPrimeLogAggregateApertureCarrier_le P hA m k

/-- Active physical carrier energy obeys the packet-local width law `E ≤ (k-m)W²`. -/
theorem xiPhysicalPrimeLogApertureFusionEnergy_le_width_mul_totalWeight_sq
    (P : Finset Nat.Primes) {A m k : ℝ} (hA : 0 < A)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p) :
    xiPhysicalPrimeLogApertureFusionEnergy P A m k ≤
      (k - m) * xiPhysicalPrimeLogEndpointTotalWeight P ^ 2 := by
  have hW := xiPhysicalPrimeLogEndpointTotalWeight_nonneg P
  have henergy :=
    xiPhysicalPrimeLogApertureFusionEnergy_le_weight_mul_weightedLength P hA m k
  have hlength :=
    xiPhysicalPrimeLogApertureWeightedLengthMass_le_width_mul_totalWeight P hactive
  calc
    xiPhysicalPrimeLogApertureFusionEnergy P A m k ≤
        xiPhysicalPrimeLogEndpointTotalWeight P *
          xiPhysicalPrimeLogApertureWeightedLengthMass P A m k := henergy
    _ ≤ xiPhysicalPrimeLogEndpointTotalWeight P *
        ((k - m) * xiPhysicalPrimeLogEndpointTotalWeight P) :=
      mul_le_mul_of_nonneg_left hlength hW
    _ = (k - m) * xiPhysicalPrimeLogEndpointTotalWeight P ^ 2 := by ring

/-- Packet-free Mertens form of full physical source-energy control. -/
theorem xiPhysicalPrimeLogApertureFusionEnergy_le_mertens_width
    (P : Finset Nat.Primes) {A m k : ℝ} (hA : 0 < A) (hmk : m ≤ k)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p) :
    xiPhysicalPrimeLogApertureFusionEnergy P A m k ≤
      (k - m) * (k + Real.log 4) ^ 2 := by
  by_cases hPempty : P = ∅
  · subst P
    simp [xiPhysicalPrimeLogApertureFusionEnergy]
    positivity
  have hP : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hPempty
  have hW := xiPhysicalPrimeLogEndpointTotalWeight_le_k_add_log_four_of_active
    P hP hactive
  have hW0 := xiPhysicalPrimeLogEndpointTotalWeight_nonneg P
  have hklog4 : 0 ≤ k + Real.log 4 := hW0.trans hW
  have hsq : xiPhysicalPrimeLogEndpointTotalWeight P ^ 2 ≤ (k + Real.log 4) ^ 2 :=
    (sq_le_sq₀ hW0 hklog4).2 hW
  have hwidth : 0 ≤ k - m := sub_nonneg.mpr hmk
  calc
    xiPhysicalPrimeLogApertureFusionEnergy P A m k ≤
        (k - m) * xiPhysicalPrimeLogEndpointTotalWeight P ^ 2 :=
      xiPhysicalPrimeLogApertureFusionEnergy_le_width_mul_totalWeight_sq P hA hactive
    _ ≤ (k - m) * (k + Real.log 4) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hwidth

/-- Normalized coherent physical source strength is at most raw active-aperture width. -/
theorem xiPhysicalPrimeLogNormalizedApertureDispersion_le_width
    {P : Finset Nat.Primes} (hP : P.Nonempty) {A m k : ℝ} (hA : 0 < A)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p) :
    xiPhysicalPrimeLogNormalizedApertureDispersion P A m k ≤ k - m := by
  let W := xiPhysicalPrimeLogEndpointTotalWeight P
  have hW : 0 < W := by
    dsimp only [W]
    simpa [xiPhysicalPrimeLogEndpointTotalWeight, xiPhysicalPrimeLogTotalWeight] using
      xiPhysicalPrimeLogTotalWeight_pos hP
  have henergy :=
    xiPhysicalPrimeLogApertureFusionEnergy_le_weight_mul_weightedLength P hA m k
  have hlength :=
    xiPhysicalPrimeLogApertureWeightedLengthMass_le_width_mul_totalWeight P hactive
  rw [xiPhysicalPrimeLogNormalizedApertureDispersion_eq_fusionEnergy_div hP hA]
  calc
    xiPhysicalPrimeLogApertureFusionEnergy P A m k / W ^ 2
        ≤ (W * xiPhysicalPrimeLogApertureWeightedLengthMass P A m k) / W ^ 2 :=
      div_le_div_of_nonneg_right henergy (sq_nonneg W)
    _ ≤ (W * ((k - m) * W)) / W ^ 2 := by
      gcongr
    _ = k - m := by field_simp

/-- Every active source in the proper physical chamber has positive normalized strength, but that
strength cannot exceed raw aperture width. -/
theorem xiPhysicalPrimeLogNormalizedApertureDispersion_mem_Ioc_width
    {P : Finset Nat.Primes} (hP : P.Nonempty) {A m k : ℝ}
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (hwidth0 : 0 < k - m) (hwidthA : k - m < A) :
    xiPhysicalPrimeLogNormalizedApertureDispersion P A m k ∈ Set.Ioc 0 (k - m) := by
  have hA : 0 < A := hwidth0.trans hwidthA
  exact ⟨
    xiPhysicalPrimeLogNormalizedApertureDispersion_pos_of_nonempty_active
      hP hactive hwidth0 hwidthA,
    xiPhysicalPrimeLogNormalizedApertureDispersion_le_width hP hA hactive⟩

/-- Shrinking active apertures force normalized coherent physical source itself to vanish. -/
theorem tendsto_xiPhysicalPrimeLogNormalizedApertureDispersion_zero_of_width
    (P : ℕ → Finset Nat.Primes) (A m k : ℕ → ℝ)
    (hP : ∀ n, (P n).Nonempty) (hA : ∀ n, 0 < A n)
    (hactive : ∀ n p, p ∈ P n →
      0 < xiPhysicalPrimeLogApertureLength (A n) (m n) (k n) p)
    (hwidth : Filter.Tendsto (fun n => k n - m n) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => xiPhysicalPrimeLogNormalizedApertureDispersion
        (P n) (A n) (m n) (k n)) Filter.atTop (nhds 0) := by
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun n =>
      xiPhysicalPrimeLogNormalizedApertureDispersion_nonneg (hP n) (hA n) (m n) (k n))
    (Filter.Eventually.of_forall fun n =>
      xiPhysicalPrimeLogNormalizedApertureDispersion_le_width
        (hP n) (hA n) (hactive n))
    hwidth

/-- No positive uniform normalized-source floor survives a shrinking active-aperture schedule. -/
theorem not_exists_uniform_positive_xiPhysicalPrimeLogNormalizedApertureDispersion_of_width
    (P : ℕ → Finset Nat.Primes) (A m k : ℕ → ℝ)
    (hP : ∀ n, (P n).Nonempty) (hA : ∀ n, 0 < A n)
    (hactive : ∀ n p, p ∈ P n →
      0 < xiPhysicalPrimeLogApertureLength (A n) (m n) (k n) p)
    (hwidth : Filter.Tendsto (fun n => k n - m n) Filter.atTop (nhds 0)) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n,
      c ≤ xiPhysicalPrimeLogNormalizedApertureDispersion
        (P n) (A n) (m n) (k n) := by
  rintro ⟨c, hc, hretain⟩
  have hzero :=
    tendsto_xiPhysicalPrimeLogNormalizedApertureDispersion_zero_of_width
      P A m k hP hA hactive hwidth
  have hc0 : c ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hzero
    (Filter.Eventually.of_forall hretain)
  exact (not_lt_of_ge hc0) hc

end

end RHTower
