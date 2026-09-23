import GaloisForLFunctions.HTGeometry.ProuhetMomentDivisibility

/-!
# Cubic and quadratic vortex charge anomalies

The charge balances of arXiv:2609.09298, equations (2.41)–(2.47), become finite moment
identities. With the canonical R-charge pattern, their simultaneous vanishing classifies all
nonnegative charge magnitudes as zero or one. Separately, the existing Prouhet osculation theorem
constructs signed rational spectra with vanishing charge moments through degree three.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry
noncomputable section

def vortexGaugeAnomaly {r : ℕ} (p : ℕ) (l : Fin r → ℕ) : ℤ :=
  (p : ℤ) - ∑ j, (l j : ℤ) ^ (3 : ℕ)

def vortexCanonicalRAnomaly {r : ℕ} (p : ℕ) (l : Fin r → ℕ) : ℤ :=
  -(p : ℤ) + ∑ j, (l j : ℤ) ^ (2 : ℕ)

/-- The difference between cubic gauge and quadratic R-charge balance is a positive charge
excess; it vanishes only for zero or unit charges. -/
theorem vortex_charge_excess_nonneg (n : ℕ) :
    0 ≤ (n : ℤ) ^ (3 : ℕ) - (n : ℤ) ^ (2 : ℕ) := by
  cases n with
  | zero => simp
  | succ n =>
    have h0 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
    have h3 : (0 : ℤ) ≤ (n : ℤ) ^ (3 : ℕ) := pow_nonneg h0 _
    push_cast
    nlinarith [sq_nonneg (n : ℤ)]

theorem vortex_charge_excess_zero_iff (n : ℕ) :
    (n : ℤ) ^ (3 : ℕ) - (n : ℤ) ^ (2 : ℕ) = 0 ↔ n ≤ 1 := by
  constructor
  · intro h
    by_contra hn
    have h2 : (2 : ℤ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    have hp : (0 : ℤ) < (n : ℤ) ^ (2 : ℕ) * ((n : ℤ) - 1) :=
      mul_pos (sq_pos_of_pos (by omega)) (by omega)
    nlinarith
  · intro h
    interval_cases n <;> simp

/-- Exact classification of the simultaneous anomaly equations with positive fields of
R-charge zero and negative fields of R-charge two. No unproved balance assumption is used. -/
theorem vortex_simultaneous_anomaly_iff {r : ℕ} (p : ℕ) (l : Fin r → ℕ) :
    (vortexGaugeAnomaly p l = 0 ∧ vortexCanonicalRAnomaly p l = 0) ↔
      ((p : ℤ) = ∑ j, (l j : ℤ) ^ (2 : ℕ)) ∧ ∀ j, l j ≤ 1 := by
  constructor
  · rintro ⟨hg, hr⟩
    have hexcess : ∑ j, ((l j : ℤ) ^ (3 : ℕ) - (l j : ℤ) ^ (2 : ℕ)) = 0 := by
      rw [Finset.sum_sub_distrib]
      dsimp [vortexGaugeAnomaly, vortexCanonicalRAnomaly] at hg hr
      omega
    refine ⟨by dsimp [vortexCanonicalRAnomaly] at hr; omega, ?_⟩
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) => vortex_charge_excess_nonneg (l j))).1 hexcess
    intro j
    exact (vortex_charge_excess_zero_iff (l j)).1 (hz j (Finset.mem_univ j))
  · rintro ⟨hp, hl⟩
    have he : ∑ j, (l j : ℤ) ^ (3 : ℕ) = ∑ j, (l j : ℤ) ^ (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro j _
      exact sub_eq_zero.mp ((vortex_charge_excess_zero_iff (l j)).2 (hl j))
    simp [vortexGaugeAnomaly, vortexCanonicalRAnomaly, hp, he]

/-- The paper's canonical paired unit-charge matter content satisfies both anomaly equations
for every multiplicity. -/
theorem vortex_canonical_anomalies (r : ℕ) :
    vortexGaugeAnomaly r (fun _ : Fin r => 1) = 0 ∧
      vortexCanonicalRAnomaly r (fun _ : Fin r => 1) = 0 := by
  simp [vortexGaugeAnomaly, vortexCanonicalRAnomaly]

/-- Inserting even one charge at least two forces a nonzero anomaly in this R-charge pattern. -/
theorem vortex_large_charge_obstruction (r p k : ℕ) (l : Fin r → ℕ) :
    ¬ (vortexGaugeAnomaly p (Fin.cons (k + 2) l) = 0 ∧
      vortexCanonicalRAnomaly p (Fin.cons (k + 2) l) = 0) := by
  intro h
  have hl := (vortex_simultaneous_anomaly_iff p (Fin.cons (k + 2) l)).1 h
  have h0 := hl.2 0
  simp only [Fin.cons_zero] at h0
  omega

/-- A charge-generating polynomial with fourfold contact at one. -/
def vortexProuhetSpectrum (H : Polynomial ℚ) : Polynomial ℚ :=
  (Polynomial.X - 1) ^ (4 : ℕ) * H

/-- The corpus's Prouhet osculation theorem supplies a closed family with zero cubic charge
anomaly, for every polynomial multiplier. -/
theorem vortexProuhet_cubic_anomaly (H : Polynomial ℚ) :
    ∑ i ∈ (vortexProuhetSpectrum H).support,
      (i : ℚ) ^ (3 : ℕ) * (vortexProuhetSpectrum H).coeff i = 0 := by
  apply GaloisForLFunctions.power_moment_eq_zero_of_sub_one_pow_dvd
    (m := 4) (k := 3)
  · exact ⟨H, rfl⟩
  · omega

/-- The same spectrum cancels the quadratic charge moment. -/
theorem vortexProuhet_quadratic_anomaly (H : Polynomial ℚ) :
    ∑ i ∈ (vortexProuhetSpectrum H).support,
      (i : ℚ) ^ (2 : ℕ) * (vortexProuhetSpectrum H).coeff i = 0 := by
  apply GaloisForLFunctions.power_moment_eq_zero_of_sub_one_pow_dvd
    (m := 4) (k := 2)
  · exact ⟨H, rfl⟩
  · omega

/-- The same spectrum also cancels the linear, mixed gauge/gravitational charge moment. -/
theorem vortexProuhet_linear_anomaly (H : Polynomial ℚ) :
    ∑ i ∈ (vortexProuhetSpectrum H).support,
      (i : ℚ) * (vortexProuhetSpectrum H).coeff i = 0 := by
  simpa only [pow_one] using
    (GaloisForLFunctions.power_moment_eq_zero_of_sub_one_pow_dvd
      (R := ℚ) (G := vortexProuhetSpectrum H) (m := 4) (k := 1)
      ⟨H, rfl⟩ (by omega))

end
end GaloisForLFunctions.HTGeometry
