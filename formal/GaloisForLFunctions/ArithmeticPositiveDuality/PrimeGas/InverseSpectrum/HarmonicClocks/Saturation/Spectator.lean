import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Saturation.TorsionMeasure
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Saturation.WeakConvergence
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Classification

/-! # A second prime separates phase laws with identical clock magnitudes -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology MeasureTheory
open _root_.RHTower.PrimeCoShift

/-- A fixed insertion rotates every harmonic without affecting its magnitude. -/
theorem inserted_harmonic_norm (a : ℕ+) (v : MissingWave) (t : ℝ) (k : ℕ) :
    ‖harmonicReading (insertedWave a v) t k‖ = ‖harmonicReading v t k‖ := by
  rw [harmonicReading,inserted_response]
  change ‖splitPhase ((k:ℝ)*t) a*harmonicReading v t k‖ = _
  rw [norm_mul,splitPhase_norm,one_mul]

theorem inserted_coordinate_limit (a : ℕ+) {v : ℕ → MissingWave} {m : ℕ+ → ℝ}
    (hm : ∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n))) (n : ℕ+) :
    Tendsto (fun j => occupationProbability (insertedWave a (v j)) n) atTop (𝓝 (insertedMass a m n)) := by
  by_cases h : n ∈ Set.range (fun l : ℕ+ => a*l)
  · obtain ⟨k,rfl⟩ := h
    simpa only [insertedWave_probability,insertedMass_at] using hm k
  · simp only [insertedWave_probability,insertedMass_off a n _ h,tendsto_const_nhds]

/-- Every admissible array of maximal mass realizes the explicit cyclic law at the clock of any chosen prime. -/
theorem prescribed_saturated_phase_law (r : ℕ+) (p : Nat.Primes) {δ : ℝ} (h₀ : 0 ≤ δ) (h₁ : δ ≤ 1)
    (m : ℕ+ → ℝ) (hpos : ∀ n, 0 ≤ m n) (hs : HasSum m (retentionCeiling r δ)) :
    ∃ v : ℕ → MissingWave, (∀ j, harmonicTest r δ (v j) (cyclicTime r p j)) ∧
      (∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n))) ∧
      Tendsto (fun j => occupationPhaseLaw (v j) (cyclicTime r p j)) atTop (𝓝 (cyclicPhaseLaw r δ h₀ h₁)) := by
  obtain ⟨v,hv,hm⟩ := (prescribed_harmonic_limits_iff r p h₀ h₁ m).mpr ⟨hpos,hs.summable,hs.tsum_eq.le⟩
  exact ⟨v,hv,hm,saturated_phase_law h₀ h₁ (cyclicTime_tendsto r p) tendsto_const_nhds hv hm hs⟩

/-- Inserting a different prime gives maximal separation of exact phases from both the original law and the weak limit. -/
theorem spectator_phase_singularity (r : ℕ+) (p q : Nat.Primes) (hpq : p ≠ q) {δ : ℝ} (h₀ : 0 ≤ δ)
    (h₁ : δ ≤ 1) (m : ℕ+ → ℝ) (hpos : ∀ n, 0 ≤ m n) (hs : HasSum m (retentionCeiling r δ))
    (hr : raySupportedLaw p m) :
    ∃ v : ℕ → MissingWave, (∀ j, onPrimeRay p (v j).val) ∧
      (∀ j, harmonicTest r δ (v j) (cyclicTime r p j)) ∧
      (∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n))) ∧
      let w := fun j => insertedWave (primePNat q) (v j)
      let μ := fun j => occupationPhaseLaw (v j) (cyclicTime r p j)
      let ν := fun j => occupationPhaseLaw (w j) (cyclicTime r p j)
      let ρ := cyclicPhaseLaw r δ h₀ h₁
      (∀ j k, ‖harmonicReading (w j) (cyclicTime r p j) k‖ = ‖harmonicReading (v j) (cyclicTime r p j) k‖) ∧
      Tendsto μ atTop (𝓝 ρ) ∧ Tendsto ν atTop (𝓝 ρ) ∧
      ∀ j, (ν j : Measure Circle) ⟂ₘ (μ j : Measure Circle) ∧ (ν j : Measure Circle) ⟂ₘ (ρ : Measure Circle) := by
  obtain ⟨v,hv,hc,hm⟩ := (one_prime_harmonic_limits_iff r p h₀ h₁ m).mpr ⟨⟨hpos,hs.summable,hs.tsum_eq.le⟩,hr⟩
  let a := primePNat q
  have hw (j : ℕ) : harmonicTest r δ (insertedWave a (v j)) (cyclicTime r p j) := by
    intro k hk hl
    rw [inserted_harmonic_norm]
    exact hc j k hk hl
  refine ⟨v,hv,hc,hm,fun j k => inserted_harmonic_norm _ _ _ _,
    saturated_phase_law h₀ h₁ (cyclicTime_tendsto r p) tendsto_const_nhds hc hm hs,
    saturated_phase_law h₀ h₁ (cyclicTime_tendsto r p) tendsto_const_nhds hw (inserted_coordinate_limit a hm)
      (insertedMass_hasSum a hs),fun j => ?_⟩
  have hz := other_prime_avoids_torsion r p q hpq j (v j)
  exact ⟨⟨torsionPhases,measurableSet_torsionPhases,hz,prime_ray_carried_by_torsion r p j _ (hv j)⟩,
    ⟨torsionPhases,measurableSet_torsionPhases,hz,cyclic_law_carried_by_torsion r h₀ h₁⟩⟩

/-- A single measurable event separates every spectator preparation from the cyclic limit by probability one. -/
theorem spectator_torsion_event (r : ℕ+) (p q : Nat.Primes) (hpq : p ≠ q) {δ : ℝ}
    (h₀ : 0 ≤ δ) (h₁ : δ ≤ 1) (v : ℕ → MissingWave) :
    ¬ Tendsto (fun j => (occupationPhaseLaw (insertedWave (primePNat q) (v j))
      (cyclicTime r p j) : Measure Circle) torsionPhases) atTop
      (𝓝 ((cyclicPhaseLaw r δ h₀ h₁ : Measure Circle) torsionPhases)) := by
  have h := measure_compl (μ := (cyclicPhaseLaw r δ h₀ h₁ : Measure Circle))
    measurableSet_torsionPhases.compl (measure_ne_top _ _)
  rw [compl_compl,cyclic_law_carried_by_torsion r h₀ h₁,measure_univ,tsub_zero] at h
  simp only [other_prime_avoids_torsion r p q hpq,h]
  intro hl
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds hl)

/-- For every family size there are exactly orthogonal preparations whose phase laws stay singular
with their own weak limit, retaining the entire allowed mass at the occupied shell three. -/
theorem exists_orthogonal_singular_limit (r : ℕ+) :
    ∃ (t : ℕ → ℝ) (v : ℕ → MissingWave), (∀ j, 0 < t j) ∧ Tendsto t atTop (𝓝 0) ∧
      (∀ j (i l : Fin r.val), i < l → inner ℂ (clockSplit (2*(i.val:ℝ)*t j) (v j).val)
        (clockSplit (2*(l.val:ℝ)*t j) (v j).val) = 0) ∧
      Tendsto (fun j => occupationProbability (v j) 3) atTop (𝓝 (1/(r.val:ℝ))) ∧
      Tendsto (fun j => occupationPhaseLaw (v j) (t j)) atTop (𝓝 (cyclicPhaseLaw r 0 le_rfl zero_le_one)) ∧
      ∀ j, (occupationPhaseLaw (v j) (t j) : Measure Circle) ⟂ₘ
        (cyclicPhaseLaw r 0 le_rfl zero_le_one : Measure Circle) := by
  let p : Nat.Primes := ⟨2,Nat.prime_two⟩
  let q : Nat.Primes := ⟨3,Nat.prime_three⟩
  have hpq : p ≠ q := fun h => (by norm_num : (2:ℕ) ≠ 3) (congrArg Subtype.val h)
  let c := retentionCeiling r 0
  let m (n : ℕ+) := if n = 1 then c else 0
  have hs : HasSum m c := hasSum_ite_eq (1:ℕ+) c
  have hpos (n : ℕ+) : 0 ≤ m n := by
    dsimp only [m]
    split
    · exact (retentionCeiling_pos r le_rfl zero_le_one).le
    · exact le_rfl
  have hr : raySupportedLaw p m := by
    intro n hn
    exact if_neg (fun he => hn ⟨0,(show primeRayLabel p 0 = 1 from pow_zero _).trans he.symm⟩)
  obtain ⟨v,_,hc,hm,hmag,_,hweak,hsep⟩ := spectator_phase_singularity r p q hpq le_rfl zero_le_one m hpos hs hr
  refine ⟨cyclicTime r p,fun j => insertedWave (primePNat q) (v j),cyclicTime_pos r p,cyclicTime_tendsto r p,
    fun j => (orthogonal_clock_family_iff _ _ _).mpr (fun k hk hl => (hmag j k).le.trans (hc j k hk hl)),
    ?_,hweak,fun j => (hsep j).2⟩
  have h := inserted_coordinate_limit (primePNat q) hm (primePNat q*1)
  rw [insertedMass_at] at h
  have hq : primePNat q = (3:ℕ+) := PNat.coe_injective rfl
  simpa only [mul_one,hq,m,if_pos rfl,c,retentionCeiling,sub_zero,zero_add] using h

#print axioms spectator_torsion_event
#print axioms exists_orthogonal_singular_limit
#print axioms inserted_harmonic_norm
#print axioms inserted_coordinate_limit
#print axioms prescribed_saturated_phase_law
#print axioms spectator_phase_singularity

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
