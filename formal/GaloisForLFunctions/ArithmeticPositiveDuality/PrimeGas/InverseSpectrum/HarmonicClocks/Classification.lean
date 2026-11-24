import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.ClockGram
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.PrimeClock
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Retention
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RapidZeros.Realization

/-! # All occupation limits at simultaneous fast harmonic cancellations -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

private def scaledTarget (q : ℝ) (m : ℕ+ → ℝ) (n : ℕ+) := m n/(2*q)

private theorem scaled_halfLaw {q : ℝ} {m : ℕ+ → ℝ} (hq : 0 < q) (hm : retainedAt q m) :
    halfLaw (scaledTarget q m) := by
  have hd : 0 < 2*q := mul_pos (by norm_num) hq
  refine ⟨fun n => div_nonneg (hm.1 n) hd.le,hm.2.1.div_const _,?_⟩
  unfold scaledTarget
  rw [tsum_div_const]
  apply (div_le_iff₀ hd).mpr
  linarith only [hm.2.2]

private def harmonicPreparation (r : ℕ+) (p : Nat.Primes) {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1)
    (m : ℕ+ → ℝ) (hm : retainedAt (retentionCeiling r δ) m) (j : ℕ) :=
  cyclicWave r (resonantBlock p j) δ hδ hδ'
    (recoverySeed p _ (scaled_halfLaw (retentionCeiling_pos r hδ hδ') hm) j)

private theorem preparation_limit (r : ℕ+) (p : Nat.Primes) {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1)
    (m : ℕ+ → ℝ) (hm : retainedAt (retentionCeiling r δ) m) (n : ℕ+) :
    Tendsto (fun j => occupationProbability (harmonicPreparation r p hδ hδ' m hm j) n) atTop (𝓝 (m n)) := by
  let q := retentionCeiling r δ
  have hq : 0 < q := retentionCeiling_pos r hδ hδ'
  have h := (recoverySeed_limit p _ (scaled_halfLaw hq hm) n).const_mul q
  have he : q*(2*scaledTarget q m n) = m n := by
    unfold scaledTarget
    field_simp [hq.ne']
  rw [he] at h
  apply h.congr'
  filter_upwards [resonantBlock_escapes p n] with j hj
  exact (cyclic_below r _ hδ hδ' _ n hj).symm

private theorem preparation_support (r : ℕ+) (p : Nat.Primes) {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1)
    (m : ℕ+ → ℝ) (hm : retainedAt (retentionCeiling r δ) m) (hr : raySupportedLaw p m) (j : ℕ) :
    onPrimeRay p (harmonicPreparation r p hδ hδ' m hm j).val := by
  let q := retentionCeiling r δ
  have hs : raySupportedLaw p (scaledTarget q m) := fun n hn => by simp only [scaledTarget,hr n hn,zero_div]
  let hh := scaled_halfLaw (retentionCeiling_pos r hδ hδ') hm
  let v := recoverySeed p _ hh j
  have hv : raySupportedLaw p (occupationProbability v) := recoverySeed_support p _ hh hs j
  apply (raySupportedLaw_iff p _).mp
  intro n hn
  change occupationProbability (cyclicWave r (resonantBlock p j) δ hδ hδ' v) n = 0
  rw [cyclic_probability,cyclicMass,hv n hn,mul_zero,zero_add]
  have hz (k : ℕ) : insertedMass (resonantBlock p j ^ k) (occupationProbability v) n = 0 := by
    have he : resonantBlock p j ^ k = primeRayLabel p ((j+1)*k) := (pow_mul _ _ _).symm
    rw [he]
    exact insertedMass_onPrimeRay hv _ n hn
  simp only [hz,Finset.sum_const_zero,mul_zero]

/-- For every elementary prime clock, the full cone of retained arrays is determined by its mass ceiling. -/
theorem prescribed_harmonic_limits_iff (r : ℕ+) (p : Nat.Primes) {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1)
    (m : ℕ+ → ℝ) :
    (∃ v : ℕ → MissingWave, (∀ j, harmonicTest r δ (v j) (cyclicTime r p j)) ∧
      ∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n))) ↔
      retainedAt (retentionCeiling r δ) m :=
  ⟨fun ⟨_,hc,hm⟩ => harmonic_limit_retained (cyclicTime_tendsto r p) hc hm,
   fun hm => ⟨harmonicPreparation r p hδ hδ' m hm,fun j => cyclic_harmonic_test r p j hδ hδ' _,
     preparation_limit r p hδ hδ' m hm⟩⟩

theorem arbitrary_harmonic_limits_iff (r : ℕ+) {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) (m : ℕ+ → ℝ) :
    (∃ (t : ℕ → ℝ) (v : ℕ → MissingWave), (∀ j, 0 < t j) ∧ Tendsto t atTop (𝓝 0) ∧
      (∀ j, harmonicTest r δ (v j) (t j)) ∧
      ∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n))) ↔
      retainedAt (retentionCeiling r δ) m := by
  refine ⟨fun ⟨_,_,_,ht,hc,hm⟩ => harmonic_limit_retained ht hc hm,fun hm => ?_⟩
  let p : Nat.Primes := ⟨2,Nat.prime_two⟩
  obtain ⟨v,hc,hl⟩ := (prescribed_harmonic_limits_iff r p hδ hδ' m).mpr hm
  exact ⟨cyclicTime r p,v,cyclicTime_pos r p,cyclicTime_tendsto r p,hc,hl⟩

theorem one_prime_harmonic_limits_iff (r : ℕ+) (p : Nat.Primes) {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1)
    (m : ℕ+ → ℝ) :
    (∃ v : ℕ → MissingWave, (∀ j, onPrimeRay p (v j).val) ∧ (∀ j, harmonicTest r δ (v j) (cyclicTime r p j)) ∧
      ∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n))) ↔
      retainedAt (retentionCeiling r δ) m ∧ raySupportedLaw p m := by
  constructor
  · rintro ⟨v,hr,hc,hl⟩
    refine ⟨(prescribed_harmonic_limits_iff r p hδ hδ' m).mp ⟨v,hc,hl⟩,fun n hn => ?_⟩
    have h : (fun j => occupationProbability (v j) n) =ᶠ[atTop] fun _ => 0 :=
      Eventually.of_forall fun j => (raySupportedLaw_iff p _).mpr (hr j) n hn
    exact tendsto_nhds_unique (hl n) h.tendsto
  · rintro ⟨hm,hr⟩
    exact ⟨harmonicPreparation r p hδ hδ' m hm,preparation_support r p hδ hδ' m hm hr,
      fun j => cyclic_harmonic_test r p j hδ hδ' _,preparation_limit r p hδ hδ' m hm⟩

/-- At exact harmonic orthogonality the admissible retained masses form the closed interval from zero to 1/r. -/
theorem orthogonal_harmonic_limits_iff (r : ℕ+) (p : Nat.Primes) (m : ℕ+ → ℝ) :
    (∃ v : ℕ → MissingWave,
      (∀ j (h : ℕ), 0 < h → h < r.val →
        inner ℂ (clockSplit (-((h:ℝ)*cyclicTime r p j)) (v j).val)
          (clockSplit ((h:ℝ)*cyclicTime r p j) (v j).val) = 0) ∧
      ∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n))) ↔ retainedAt (1/(r.val:ℝ)) m := by
  simpa only [harmonic_zero_iff,harmonicReading,split_pair_orthogonal_iff,retentionCeiling,
    sub_zero,zero_add] using prescribed_harmonic_limits_iff r p (le_refl 0) zero_le_one m

/-- An equally spaced family of r mutually orthogonal outgoing states realizes exactly the mass ceiling 1/r. -/
theorem orthogonal_family_limits_iff (r : ℕ+) (p : Nat.Primes) (m : ℕ+ → ℝ) :
    (∃ v : ℕ → MissingWave,
      (∀ j (i l : Fin r.val), i < l → inner ℂ (clockSplit (2*(i.val:ℝ)*cyclicTime r p j) (v j).val)
        (clockSplit (2*(l.val:ℝ)*cyclicTime r p j) (v j).val) = 0) ∧
      ∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n))) ↔ retainedAt (1/(r.val:ℝ)) m := by
  simpa only [orthogonal_clock_family_iff,retentionCeiling,sub_zero,zero_add] using
    prescribed_harmonic_limits_iff r p (le_refl 0) zero_le_one m

/-- The entire sharp retained fraction can occupy the vacuum, using quanta of any one prescribed species. -/
theorem sharp_harmonic_vacuum (r : ℕ+) (p : Nat.Primes) {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) :
    ∃ v : ℕ → MissingWave, (∀ j, onPrimeRay p (v j).val) ∧
      (∀ j, harmonicTest r δ (v j) (cyclicTime r p j)) ∧
      ∀ F : Finset ℕ+, 1 ∈ F → Tendsto (fun j => windowMass (v j) F) atTop (𝓝 (retentionCeiling r δ)) := by
  let q := retentionCeiling r δ
  let m := fun n : ℕ+ => if n = 1 then q else 0
  have hs : HasSum m q := hasSum_ite_eq (1:ℕ+) q
  have hp (n : ℕ+) : 0 ≤ m n := by
    dsimp only [m]
    split
    · exact (retentionCeiling_pos r hδ hδ').le
    · exact le_rfl
  have hm : retainedAt q m := ⟨hp,hs.summable,hs.tsum_eq.le⟩
  have hr : raySupportedLaw p m := by
    intro n hn
    exact if_neg (fun he => hn ⟨0,(show primeRayLabel p 0 = 1 from pow_zero _).trans he.symm⟩)
  obtain ⟨v,hray,hc,hl⟩ := (one_prime_harmonic_limits_iff r p hδ hδ' m).mpr ⟨hm,hr⟩
  refine ⟨v,hray,hc,fun F hF => ?_⟩
  simpa [windowMass,m,hF,q] using tendsto_finsetSum F (fun n _ => hl n)

#print axioms orthogonal_family_limits_iff
#print axioms sharp_harmonic_vacuum
#print axioms prescribed_harmonic_limits_iff
#print axioms arbitrary_harmonic_limits_iff
#print axioms one_prime_harmonic_limits_iff
#print axioms orthogonal_harmonic_limits_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
