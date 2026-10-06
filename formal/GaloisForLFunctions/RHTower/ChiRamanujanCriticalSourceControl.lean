import GaloisForLFunctions.RHTower.ChiRamanujanDistinguishedPrimeLabels
import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicCriticalAtoms

/-!
# Uniform control of the complete projected critical source

At any integer frequency at most one distinguished-prime entry survives.
This bounds the exact critical multiplier by log(1+|n|), independently of
all source cutoffs. The complete rational atom action and both contraction
projectors are controlled by one weighted Schwartz lattice norm. No atom
absolute-mass cost or analytic premise is introduced.

The moving exterior-cone test must still be estimated separately; this
source bound alone does not prove cubic cancellation.
-/

noncomputable section
open scoped BigOperators Topology SchwartzMap
namespace RHTower.BAGTrace

private theorem entry_bound (P : Finset ℕ) {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ramanujanDistinguishedPrimeEntry P p n ≤ Real.log ((n : ℝ) + 1) := by
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  by_cases hsq : p^2 ∣ n
  · have hd : p ∣ n := (dvd_pow_self p (by omega : 2 ≠ 0)).trans hsq
    simpa [ramanujanDistinguishedPrimeEntry, ramanujanTorsionIndicator, hd, hsq] using hlog
  by_cases hd : p ∣ n
  · have hn : 0 < n := Nat.pos_of_ne_zero (by intro hz; simp [hz] at hsq)
    have hpn : (p : ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd hn hd
    have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
    have hprod : (∏ q ∈ (P.filter Nat.Prime).erase p,
        (1 - ramanujanTorsionIndicator q n)) ≤ 1 := by
      apply Finset.prod_le_one <;> intro q hq <;>
        simp only [ramanujanTorsionIndicator] <;> split_ifs <;> norm_num
    calc
      _ = Real.log p * (∏ q ∈ (P.filter Nat.Prime).erase p,
          (1 - ramanujanTorsionIndicator q n)) := by
        simp [ramanujanDistinguishedPrimeEntry, ramanujanTorsionIndicator, hd, hsq]
      _ ≤ Real.log p := by simpa using mul_le_mul_of_nonneg_left hprod hlp
      _ ≤ _ := Real.log_le_log (by exact_mod_cast hp.pos) (by linarith)
  · simpa [ramanujanDistinguishedPrimeEntry, ramanujanTorsionIndicator, hd, hsq] using hlog

/-- Uniform control of the exact critical source at EVERY integer magnitude,
including zero and uncovered frequencies, independent of the prime cutoff. -/
theorem ramanujanDistinguishedPrimeMultiplier_uniform_bound (P : Finset ℕ) (n : ℕ) :
    0 ≤ ramanujanDistinguishedPrimeMultiplier P n ∧
      ramanujanDistinguishedPrimeMultiplier P n ≤ Real.log ((n : ℝ) + 1) := by
  classical
  change 0 ≤ (∑ p ∈ P.filter Nat.Prime, ramanujanDistinguishedPrimeEntry P p n) ∧ _
  refine ⟨Finset.sum_nonneg (fun p hp =>
    ramanujanDistinguishedPrimeEntry_nonneg P (Finset.mem_filter.mp hp).2 n), ?_⟩
  change (∑ p ∈ P.filter Nat.Prime, ramanujanDistinguishedPrimeEntry P p n) ≤ _
  by_cases h : ∃ p ∈ P.filter Nat.Prime, p ∣ n
  · obtain ⟨p, hp, hd⟩ := h
    rw [Finset.sum_eq_single p]
    · exact entry_bound P (Finset.mem_filter.mp hp).2 n
    · intro q hq hqp
      have hz : (∏ s ∈ (P.filter Nat.Prime).erase q,
          (1 - ramanujanTorsionIndicator s n)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hqp.symm, hp⟩)
          (by simp [ramanujanTorsionIndicator, hd])
      simp only [ramanujanDistinguishedPrimeEntry, hz, mul_zero]
    · exact fun hnot => False.elim (hnot hp)
  · have hz : ∀ p ∈ P.filter Nat.Prime, ramanujanDistinguishedPrimeEntry P p n = 0 := by
      intro p hp
      have hd : ¬p ∣ n := fun hd => h ⟨p, hp, hd⟩
      have hsq : ¬p^2 ∣ n := fun hs => hd ((dvd_pow_self p (by omega : 2 ≠ 0)).trans hs)
      simp [ramanujanDistinguishedPrimeEntry, ramanujanTorsionIndicator, hd, hsq]
    rw [Finset.sum_eq_zero hz]
    exact Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

private theorem multiplier_linear_bound (P : Finset ℕ) (n : ℤ) :
    ‖(ramanujanDistinguishedPrimeMultiplier P n.natAbs : ℂ)‖ ≤ 1 + |(n : ℝ)| := by
  obtain ⟨h0,hb⟩ := ramanujanDistinguishedPrimeMultiplier_uniform_bound P n.natAbs
  rw [Complex.norm_of_nonneg h0]
  have hl := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < n.natAbs + 1)
  have hc : (n.natAbs : ℝ) = |(n : ℝ)| := by simp
  calc
    _ ≤ Real.log ((n.natAbs : ℝ) + 1) := hb
    _ ≤ (n.natAbs : ℝ) := by linarith
    _ ≤ _ := by rw [hc]; linarith

private theorem critical_phase (P : Finset ℕ) (n : ℤ × ℤ × ℤ) :
    ramanujanCriticalTripleAtomAction P (ramanujanTripleFourierPhase n) =
      (ramanujanDistinguishedPrimeMultiplier P n.1.natAbs : ℂ) *
      (ramanujanDistinguishedPrimeMultiplier P n.2.1.natAbs : ℂ) *
      (ramanujanDistinguishedPrimeMultiplier P n.2.2.natAbs : ℂ) := by
  classical
  change (∑ a : RamanujanTriplePrimeOnlyAtomIndex P,
    (ramanujanCriticalTripleAtomWeight P a : ℂ) *
      ramanujanTripleFourierPhase n (ramanujanTriplePrimeOnlyAtomNode a)) = _
  rw [← sum_ramanujanCriticalPrimeAtomWeight_fourier_distinguished P n.1,
    ← sum_ramanujanCriticalPrimeAtomWeight_fourier_distinguished P n.2.1,
    ← sum_ramanujanCriticalPrimeAtomWeight_fourier_distinguished P n.2.2]
  conv_rhs => rw [mul_assoc]
  simp only [Fintype.sum_prod_type, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro f hf
  dsimp [ramanujanCriticalTripleAtomWeight, ramanujanTripleFourierPhase,
    ramanujanTriplePrimeOnlyAtomNode]
  push_cast
  ring

private theorem critical_phase_norm (P : Finset ℕ) (n : ℤ × ℤ × ℤ) :
    ‖ramanujanCriticalTripleAtomAction P (ramanujanTripleFourierPhase n)‖ ≤
      ramanujanTripleWeight (ramanujanTripleLattice n) := by
  rw [critical_phase, norm_mul, norm_mul]
  exact mul_le_mul
    (mul_le_mul (multiplier_linear_bound P n.1) (multiplier_linear_bound P n.2.1)
      (norm_nonneg _) (by positivity))
    (multiplier_linear_bound P n.2.2) (norm_nonneg _) (by positivity)

private def sourceCLM (P : Finset ℕ) : ((ℝ × ℝ × ℝ) → ℂ) →L[ℂ] ℂ where
  toLinearMap := ramanujanCriticalTripleAtomAction P
  cont := by
    change Continuous (fun F : (ℝ × ℝ × ℝ) → ℂ =>
      ∑ a : RamanujanTriplePrimeOnlyAtomIndex P,
        (ramanujanCriticalTripleAtomWeight P a : ℂ) * F (ramanujanTriplePrimeOnlyAtomNode a))
    fun_prop

private def averageCLM (D : ℕ) (v : ℝ × ℝ × ℝ) :
    ((ℝ × ℝ × ℝ) → ℂ) →L[ℂ] ((ℝ × ℝ × ℝ) → ℂ) where
  toLinearMap := ramanujanTranslationAverage D v
  cont := by
    change Continuous (fun F : (ℝ × ℝ × ℝ) → ℂ => fun x =>
      (D : ℂ)⁻¹ * ∑ a : Fin D, F (ramanujanTripleTranslate v ((a.val : ℝ)/D) x))
    fun_prop

private def projectedSourceCLM (P : Finset ℕ) (D : ℕ) :
    ((ℝ × ℝ × ℝ) → ℂ) →L[ℂ] ℂ :=
  (sourceCLM P).comp ((ContinuousLinearMap.id ℂ _ - averageCLM D (1,0,-1)).comp
    (ContinuousLinearMap.id ℂ _ - averageCLM D (0,1,-1)))

private theorem projected_phase_norm (P : Finset ℕ) (D : ℕ) (n : ℤ × ℤ × ℤ) :
    ‖projectedSourceCLM P D (ramanujanTripleFourierPhase n)‖ ≤
      ramanujanTripleWeight (ramanujanTripleLattice n) := by
  change ‖ramanujanCriticalTripleAtomAction P
    (ramanujanNoncontractingProjector D (ramanujanTripleFourierPhase n))‖ ≤ _
  by_cases hD : D = 0
  · subst D
    have ha (v : ℝ × ℝ × ℝ) : ramanujanTranslationAverage 0 v = 0 := by
      ext F x
      simp [ramanujanTranslationAverage]
    simpa only [ramanujanNoncontractingProjector, ramanujanContract13,
      ramanujanContract23, ha, sub_zero, LinearMap.id_comp, LinearMap.id_apply] using
      critical_phase_norm P n
  · rw [ramanujanNoncontractingProjector_phase hD]
    split_ifs
    · simp only [map_zero, norm_zero]
      unfold ramanujanTripleWeight
      positivity
    · exact critical_phase_norm P n

/-- The whole growing critical rational source and BOTH literal contraction
projectors admit one cutoff-independent bound on every Schwartz Fourier test.
All integer frequencies, including congruence aliases, remain present. -/
theorem ramanujanCriticalTripleAtomAction_projected_periodic_bound
    (P : Finset ℕ) (D : ℕ) (Φ : 𝓢(ℝ × ℝ × ℝ, ℂ)) :
    ‖ramanujanCriticalTripleAtomAction P
      (ramanujanNoncontractingProjector D (ramanujanTriplePeriodicTest Φ))‖ ≤
      ∑' n : ℤ × ℤ × ℤ, ‖Φ (ramanujanTripleLattice n)‖ *
        ramanujanTripleWeight (ramanujanTripleLattice n) := by
  let T := projectedSourceCLM P D
  have hs : Summable (fun n : ℤ × ℤ × ℤ =>
      Φ (ramanujanTripleLattice n) • ramanujanTripleFourierPhase n) := by
    apply Pi.summable.mpr
    intro x
    exact summable_ramanujanTriplePeriodicTest Φ x
  have he : ramanujanTriplePeriodicTest Φ =
      ∑' n : ℤ × ℤ × ℤ, Φ (ramanujanTripleLattice n) • ramanujanTripleFourierPhase n := by
    ext x
    simp only [tsum_apply hs, Pi.smul_apply, smul_eq_mul, ramanujanTriplePeriodicTest]
  have hp (n : ℤ × ℤ × ℤ) :
      ‖Φ (ramanujanTripleLattice n) * T (ramanujanTripleFourierPhase n)‖ ≤
        ‖Φ (ramanujanTripleLattice n)‖ * ramanujanTripleWeight (ramanujanTripleLattice n) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (projected_phase_norm P D n) (norm_nonneg _)
  have hn := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hp
    (summable_ramanujanTripleSchwartz_weighted Φ)
  change ‖T (ramanujanTriplePeriodicTest Φ)‖ ≤ _
  rw [he, T.map_tsum hs]
  simp only [map_smul, smul_eq_mul]
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum hp
    (summable_ramanujanTripleSchwartz_weighted Φ))

end RHTower.BAGTrace
