import GaloisForLFunctions.BiScaleUncertainty.HyperbolicVarianceRigidity

/-!
# Support escape and the strict finite-filter Schur residual

The extreme translate of a nonzero compact source escapes its original support.
Consequently the finite hyperbolic filter retains positive energy after both
source and centered-source projections. This residual measures the exact strict
Cauchy--Schwarz slack and returns it to the full odd plastic lower bound.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.FiniteFilterSchurResidual
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open CenteredHyperbolicGram ProjectedHyperbolicGram ArithmeticMultiplierCollisions
open DyadicHyperbolicMoment HyperbolicRay SourceLattice SignedCoherentMoment
open CoherentSourceProjection LocalCoherentFilter HyperbolicVarianceRigidity
noncomputable section

private abbrev qSource (f : C_c(ℝ, ℝ)) := centeredSource f (1 / 2) (sourceMean f (1 / 2))
private abbrev qEnergy (f : C_c(ℝ, ℝ)) := autocorr (qSource f) 0

private theorem sourceFilter_zero : sourceFilter (0 : C_c(ℝ, ℝ)) = 0 := by
  ext u
  rw [sourceFilter_apply]
  simp

private theorem escape_of_ne_zero (f : C_c(ℝ, ℝ)) (hf : f ≠ 0) :
    ∃ v : ℝ, f v = 0 ∧ sourceFilter f v ≠ 0 := by
  classical
  have hn : (Function.support (f : ℝ → ℝ)).Nonempty := by
    change ∃ u : ℝ, f u ≠ 0
    by_contra! h
    apply hf
    ext u
    exact h u
  have hb : BddAbove (Function.support (f : ℝ → ℝ)) := by
    refine ⟨multiplierSourceRadius f, ?_⟩
    intro u hu
    exact (le_abs_self u).trans (abs_le_multiplierSourceRadius f u hu)
  let M := sSup (Function.support (f : ℝ → ℝ))
  let d := Real.log 2
  have hd : 0 < d := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  obtain ⟨u, hu, hum⟩ := exists_lt_of_lt_csSup hn (show M - d < M by linarith)
  have hz (x : ℝ) (hx : M < x) : f x = 0 := by
    by_contra hfx
    have hle : x ≤ M := le_csSup hb hfx
    linarith only [hx, hle]
  cases hL : sourceCutoff f with
  | zero =>
    have hg := sourceCutoff_gap f
    rw [hL] at hg
    have hp := multiplierSourceRadius_pos f
    norm_num at hg
    linarith only [hg, hp]
  | succ n =>
    let v := u + ((n : ℝ) + 1) * d
    have hv : M < v := by
      have hp : 0 ≤ (n : ℝ) * d := mul_nonneg (by positivity) hd.le
      dsimp [v]
      nlinarith only [hum, hp]
    have hplus (k : ℕ) : f (v + ((k : ℝ) + 1) * d) = 0 := by
      apply hz
      have hp : 0 < ((k : ℝ) + 1) * d := mul_pos (by positivity) hd
      linarith only [hv, hp]
    have hminus (k : ℕ) (hk : k ∈ Finset.range n) : f (v - ((k : ℝ) + 1) * d) = 0 := by
      apply hz
      have hkn : k + 1 ≤ n := by have := Finset.mem_range.mp hk; omega
      have hkc : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hkn
      have hm := mul_le_mul_of_nonneg_right hkc hd.le
      dsimp [v]
      nlinarith only [hum, hm]
    have he : sourceFilter f v = f u / (2 * Real.cosh ((((n : ℝ) + 1) * d) / 2)) := by
      rw [sourceFilter_apply, hL]
      change (∑ k ∈ Finset.range (n + 1),
        (f (v + ((k : ℝ) + 1) * d) + f (v - ((k : ℝ) + 1) * d)) /
          (2 * Real.cosh ((((k : ℝ) + 1) * d) / 2))) = _
      simp only [hplus, zero_add]
      rw [Finset.sum_range_succ]
      have hs : (∑ k ∈ Finset.range n, f (v - ((k : ℝ) + 1) * d) /
          (2 * Real.cosh ((((k : ℝ) + 1) * d) / 2))) = 0 := by
        exact Finset.sum_eq_zero fun k hk => by rw [hminus k hk, zero_div]
      rw [hs, zero_add, show v - ((n : ℝ) + 1) * d = u by dsimp [v]; ring]
    refine ⟨v, hz v hv, ?_⟩
    rw [he]
    exact div_ne_zero hu (ne_of_gt (mul_pos (by norm_num) (Real.cosh_pos _)))

/-- Every nonzero actual finite filter is nonzero somewhere outside the original source support. -/
theorem sourceFilter_escape_iff (f : C_c(ℝ, ℝ)) :
    (∃ v : ℝ, f v = 0 ∧ sourceFilter f v ≠ 0) ↔ f ≠ 0 := by
  constructor
  · rintro ⟨v, _, hv⟩ hf
    rw [hf, sourceFilter_zero] at hv
    exact hv rfl
  · exact escape_of_ne_zero f

private def pairing (p q : C_c(ℝ, ℝ)) : ℝ := ∫ u, p u * q u
private theorem pairing_comm (p q : C_c(ℝ, ℝ)) : pairing p q = pairing q p := by
  simp only [pairing, mul_comm]
private theorem pairing_self (p : C_c(ℝ, ℝ)) : pairing p p = autocorr p 0 := by
  simp only [pairing, autocorr, add_zero]
private theorem pairing_sub (p r q : C_c(ℝ, ℝ)) (c : ℝ) :
    pairing p (r - c • q) = pairing p r - c * pairing p q := by
  have hi (g : C_c(ℝ, ℝ)) : Integrable (fun u => p u * g u) :=
    (p.continuous.mul g.continuous).integrable_of_hasCompactSupport p.hasCompactSupport.mul_right
  have he : (fun u => p u * (r - c • q) u) = fun u => p u * r u - c * (p u * q u) := by
    funext u
    change p u * (r u - c * q u) = _
    ring
  unfold pairing
  rw [he, integral_sub (hi r) ((hi q).const_mul c), integral_const_mul]

private theorem energy_sub (r q : C_c(ℝ, ℝ)) (c : ℝ) :
    autocorr (r - c • q : C_c(ℝ, ℝ)) 0 =
      autocorr r 0 - 2 * c * pairing q r + c ^ 2 * autocorr q 0 := by
  rw [← pairing_self, pairing_sub, pairing_comm (r - c • q) r, pairing_sub,
    pairing_comm (r - c • q) q, pairing_sub, pairing_self, pairing_self, pairing_comm r q]
  ring

/-- Exact centered pairing with the actual finite hyperbolic filter. -/
def centeredFilterPairing (f : C_c(ℝ, ℝ)) : ℝ := ∫ u, qSource f u * sourceFilter f u

private theorem pairing_centered_orthogonal (f : C_c(ℝ, ℝ)) :
    pairing (qSource f) (orthogonalFilter f) = centeredFilterPairing f := by
  have hr : orthogonalFilter f = sourceFilter f - (filterCovariance f / autocorr f 0) • f := by
    ext u
    rfl
  have ho : pairing (qSource f) f = 0 := centered_source_orthogonal f (1 / 2)
  rw [hr, pairing_sub, ho, mul_zero, sub_zero]
  rfl

/-- Actual compact residual after removing both source and centered-source components. -/
def schurResidual (f : C_c(ℝ, ℝ)) : C_c(ℝ, ℝ) :=
  orthogonalFilter f - (centeredFilterPairing f / qEnergy f) • qSource f

/-- Measured energy remaining beyond the two source directions. -/
def schurResidualEnergy (f : C_c(ℝ, ℝ)) : ℝ := autocorr (schurResidual f) 0

private theorem pairing_zero_of_qEnergy_zero (f : C_c(ℝ, ℝ)) (hQ : qEnergy f = 0) :
    centeredFilterPairing f = 0 := by
  have hq := (source_energy_eq_zero_iff (qSource f)).mp hQ
  unfold centeredFilterPairing
  rw [hq]
  simp

theorem schurResidual_source_pairing (f : C_c(ℝ, ℝ)) : (∫ u, f u * schurResidual f u) = 0 := by
  have hr : pairing f (orthogonalFilter f) = 0 := orthogonalFilter_source_pairing f
  have hq : pairing f (qSource f) = 0 := by
    rw [pairing_comm]
    exact centered_source_orthogonal f (1 / 2)
  change pairing f (orthogonalFilter f - _ • qSource f) = 0
  rw [pairing_sub, hr, hq, mul_zero, sub_zero]

theorem schurResidual_centered_pairing (f : C_c(ℝ, ℝ)) :
    (∫ u, centeredSource f (1 / 2) (sourceMean f (1 / 2)) u * schurResidual f u) = 0 := by
  change pairing (qSource f) (orthogonalFilter f - _ • qSource f) = 0
  rw [pairing_sub, pairing_centered_orthogonal, pairing_self]
  by_cases hQ : qEnergy f = 0
  · have hβ := pairing_zero_of_qEnergy_zero f hQ
    change centeredFilterPairing f - centeredFilterPairing f / qEnergy f * qEnergy f = 0
    simp [hQ, hβ]
  · change centeredFilterPairing f - centeredFilterPairing f / qEnergy f * qEnergy f = 0
    field_simp
    ring

theorem schurResidual_energy (f : C_c(ℝ, ℝ)) :
    schurResidualEnergy f = filterEnergy f - centeredFilterPairing f ^ 2 /
      autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 := by
  unfold schurResidualEnergy schurResidual
  rw [energy_sub, orthogonalFilter_energy, pairing_centered_orthogonal]
  change filterEnergy f - 2 * (centeredFilterPairing f / qEnergy f) * centeredFilterPairing f +
    (centeredFilterPairing f / qEnergy f) ^ 2 * qEnergy f =
      filterEnergy f - centeredFilterPairing f ^ 2 / qEnergy f
  by_cases hQ : qEnergy f = 0
  · simp [hQ]
  · field_simp
    ring

private theorem q_zero : qSource (0 : C_c(ℝ, ℝ)) = 0 := by
  ext u
  simp [qSource, centeredSource]
private theorem orthogonal_zero : orthogonalFilter (0 : C_c(ℝ, ℝ)) = 0 := by
  ext u
  change sourceFilter (0 : C_c(ℝ, ℝ)) u - _ * 0 = 0
  rw [sourceFilter_zero]
  simp
private theorem residual_zero : schurResidual (0 : C_c(ℝ, ℝ)) = 0 := by
  unfold schurResidual
  rw [orthogonal_zero, q_zero]
  simp

/-- The two projected source directions cannot absorb the escaped translate. -/
theorem schurResidualEnergy_eq_zero_iff (f : C_c(ℝ, ℝ)) : schurResidualEnergy f = 0 ↔ f = 0 := by
  constructor
  · intro h
    have he := (source_energy_eq_zero_iff (schurResidual f)).mp h
    by_contra hf
    obtain ⟨v, hv, hA⟩ := (sourceFilter_escape_iff f).mpr hf
    have hz := congrArg (fun p : C_c(ℝ, ℝ) => p v) he
    change sourceFilter f v - filterCovariance f / autocorr f 0 * f v -
      centeredFilterPairing f / qEnergy f *
        ((Real.cosh (2 * (1 / 2) * v) - sourceMean f (1 / 2)) * f v) = 0 at hz
    rw [hv] at hz
    simp only [mul_zero, sub_zero] at hz
    exact hA hz
  · intro hf
    subst f
    unfold schurResidualEnergy
    rw [residual_zero]
    simp [autocorr]

theorem schurResidualEnergy_pos_iff (f : C_c(ℝ, ℝ)) : 0 < schurResidualEnergy f ↔ f ≠ 0 := by
  constructor
  · intro hp hf
    have hz := (schurResidualEnergy_eq_zero_iff f).mpr hf
    linarith only [hp, hz]
  · intro hf
    apply lt_of_le_of_ne (autocorr_zero_nonneg (schurResidual f))
    intro hz
    exact hf ((schurResidualEnergy_eq_zero_iff f).mp hz.symm)

/-- Exact Cauchy--Schwarz defect carried by the constructed residual. -/
theorem schur_defect_identity (f : C_c(ℝ, ℝ)) :
    autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 * schurResidualEnergy f =
      autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 * filterEnergy f -
        centeredFilterPairing f ^ 2 := by
  rw [schurResidual_energy]
  change qEnergy f * (filterEnergy f - centeredFilterPairing f ^ 2 / qEnergy f) =
    qEnergy f * filterEnergy f - centeredFilterPairing f ^ 2
  by_cases hQ : qEnergy f = 0
  · rw [pairing_zero_of_qEnergy_zero f hQ, hQ]
    simp
  · field_simp

private theorem qEnergy_pos (f : C_c(ℝ, ℝ)) (hf : f ≠ 0) : 0 < qEnergy f := by
  apply lt_of_le_of_ne (autocorr_zero_nonneg _)
  intro hz
  rcases (centered_energy_eq_zero_iff f (1 / 2) (sourceMean f (1 / 2))).mp hz.symm with h | h
  · exact hf h
  · norm_num at h

theorem strict_schur_iff (f : C_c(ℝ, ℝ)) : centeredFilterPairing f ^ 2 <
    autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 * filterEnergy f ↔ f ≠ 0 := by
  have he := schur_defect_identity f
  constructor
  · intro h hf
    have hz := (schurResidualEnergy_eq_zero_iff f).mpr hf
    rw [hz, mul_zero] at he
    linarith only [he, h]
  · intro hf
    have hp := mul_pos (qEnergy_pos f hf) ((schurResidualEnergy_pos_iff f).mpr hf)
    change 0 < autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 *
      schurResidualEnergy f at hp
    linarith only [he, hp]

private theorem pairing_abs_lt_root (f : C_c(ℝ, ℝ)) (hf : f ≠ 0) :
    |centeredFilterPairing f| < Real.sqrt (qEnergy f * filterEnergy f) := by
  have hs := Real.sq_sqrt (mul_nonneg (autocorr_zero_nonneg (qSource f)) (filterEnergy_nonneg f))
  have ht := (strict_schur_iff f).mpr hf
  change centeredFilterPairing f ^ 2 < qEnergy f * filterEnergy f at ht
  apply (sq_lt_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs, hs]
  exact ht

/-- Exact norm-price correction expressed through the energy of the residual producer. -/
def schurResidualGain (f : C_c(ℝ, ℝ)) : ℝ :=
  qEnergy f * schurResidualEnergy f /
    (Real.sqrt (qEnergy f * filterEnergy f) + centeredFilterPairing f)

theorem schurResidualGain_eq (f : C_c(ℝ, ℝ)) : schurResidualGain f =
    Real.sqrt (autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 * filterEnergy f) -
      centeredFilterPairing f := by
  by_cases hf : f = 0
  · subst f
    have hQ : qEnergy (0 : C_c(ℝ, ℝ)) = 0 := by rw [qEnergy, q_zero]; simp [autocorr]
    have hβ := pairing_zero_of_qEnergy_zero (0 : C_c(ℝ, ℝ)) hQ
    change schurResidualGain 0 = Real.sqrt (qEnergy 0 * filterEnergy 0) - centeredFilterPairing 0
    unfold schurResidualGain
    rw [hQ, hβ]
    simp
  · have ht := pairing_abs_lt_root f hf
    have hd : 0 < Real.sqrt (qEnergy f * filterEnergy f) + centeredFilterPairing f := by
      have hb := neg_abs_le (centeredFilterPairing f)
      linarith only [ht, hb]
    have hs := Real.sq_sqrt (mul_nonneg (autocorr_zero_nonneg (qSource f)) (filterEnergy_nonneg f))
    have he := schur_defect_identity f
    change qEnergy f * schurResidualEnergy f = qEnergy f * filterEnergy f - centeredFilterPairing f ^ 2 at he
    apply (div_eq_iff (ne_of_gt hd)).mpr
    nlinarith only [he, hs]

theorem schurResidualGain_pos_iff (f : C_c(ℝ, ℝ)) : 0 < schurResidualGain f ↔ f ≠ 0 := by
  constructor
  · intro hp hf
    subst f
    have hQ : qEnergy (0 : C_c(ℝ, ℝ)) = 0 := by rw [qEnergy, q_zero]; simp [autocorr]
    unfold schurResidualGain at hp
    rw [hQ] at hp
    simp at hp
  · intro hf
    rw [schurResidualGain_eq]
    have ht := pairing_abs_lt_root f hf
    have hb := le_abs_self (centeredFilterPairing f)
    change 0 < Real.sqrt (qEnergy f * filterEnergy f) - centeredFilterPairing f
    linarith only [ht, hb]

theorem schurResidualGain_nonneg (f : C_c(ℝ, ℝ)) : 0 ≤ schurResidualGain f := by
  by_cases hf : f = 0
  · subst f
    have hQ : qEnergy (0 : C_c(ℝ, ℝ)) = 0 := by rw [qEnergy, q_zero]; simp [autocorr]
    unfold schurResidualGain
    rw [hQ]
    simp
  · exact ((schurResidualGain_pos_iff f).mpr hf).le

theorem localBudget_sub_residualGain (f : C_c(ℝ, ℝ)) :
    localBudget f - schurResidualGain f = autocorr (sinhCompact (1 / 2) f) 0 +
      signedCorrectionMass f + centeredFilterPairing f := by
  rw [schurResidualGain_eq]
  unfold localBudget
  ring

/-- Strict recovery of the finite-filter norm slack in the full odd plastic functional. -/
theorem odd_plastic_residual_gain_certificate (f : C_c(ℝ, ℝ)) (N : ℕ) :
    let B := (∫ y in (0 : ℝ)..Real.log 2, optimizedCollar (oddCompactSource f) N (-y)) +
      plasticRemainderEnergy (oddCompactSource f) - 2 * Real.log 2 * localBudget (oddCompactSource f)
    (B < B + 2 * Real.log 2 * schurResidualGain (oddCompactSource f) ↔ ¬ Function.Even (f : ℝ → ℝ)) ∧
      B + 2 * Real.log 2 * schurResidualGain (oddCompactSource f) ≤ plasticCrossover (oddCompactSource f) := by
  dsimp only
  constructor
  · have hd := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hg : 0 < schurResidualGain (oddCompactSource f) ↔ ¬ Function.Even (f : ℝ → ℝ) := by
      rw [schurResidualGain_pos_iff, ne_eq, odd_source_eq_zero_iff_even]
    rw [← hg]
    constructor <;> intro h <;> nlinarith only [h, hd]
  · have hp := odd_plasticCrossover_ge_optimized f N
    have hm := odd_moment_sq_le_filter_pairing f
    have hg := localBudget_sub_residualGain (oddCompactSource f)
    unfold centeredFilterPairing at hg
    have he := congrArg (fun x : ℝ => Real.log 2 * x) hg
    nlinarith only [hp, hm, he]

end
end GaloisForLFunctions.BiScaleUncertainty.FiniteFilterSchurResidual
