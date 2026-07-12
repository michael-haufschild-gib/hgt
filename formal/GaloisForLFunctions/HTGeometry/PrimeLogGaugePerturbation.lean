import GaloisForLFunctions.HTGeometry.PrimeLogHerglotz

/-!
# Positive prime-mass perturbations are bounded logarithmic gauges

Every strictly positive perturbation of finitely many dyadic prime masses has a unique logarithmic
gauge.  The new gauge agrees with the old gauge away from the finite mass support and therefore
preserves boundedness.  This closes the reparametrization gap between additive finite-mass control
and the bounded exponential gauges used by the prime-log Herglotz family.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The logarithmic gauge associated with a strictly positive prime-mass function. -/
def primeLogGaugeOfMass (weight : Nat.Primes → ℝ) (p : Nat.Primes) : ℝ :=
  Real.log (weight p / ((2 : ℝ)⁻¹) ^ (p : ℕ))

/-- Reconstructing the dyadic weight from the logarithmic gauge recovers every positive mass
exactly. -/
theorem primeDyadicWeight_gaugeOfMass
    (weight : Nat.Primes → ℝ) (hweight : ∀ p, 0 < weight p) (p : Nat.Primes) :
    primeDyadicWeight (primeLogGaugeOfMass weight) p = weight p := by
  let b := ((2 : ℝ)⁻¹) ^ (p : ℕ)
  have hb : 0 < b := by positivity
  rw [primeDyadicWeight, primeLogGaugeOfMass, Real.exp_log (div_pos (hweight p) hb)]
  exact mul_div_cancel₀ (weight p) hb.ne'

/-- Additive perturbation of the dyadic prime masses. -/
def primeLogPerturbedMass
    (u : Nat.Primes → ℝ) (a : Nat.Primes →₀ ℝ) (ε : ℝ) (p : Nat.Primes) : ℝ :=
  primeDyadicWeight u p + ε * a p

/-- The logarithmic gauge of the perturbed prime masses. -/
def primeLogPerturbedGauge
    (u : Nat.Primes → ℝ) (a : Nat.Primes →₀ ℝ) (ε : ℝ) : Nat.Primes → ℝ :=
  primeLogGaugeOfMass (primeLogPerturbedMass u a ε)

/-- A positive additive mass perturbation is represented exactly by its perturbed gauge. -/
theorem primeDyadicWeight_perturbedGauge
    (u : Nat.Primes → ℝ) (a : Nat.Primes →₀ ℝ) (ε : ℝ)
    (hpos : ∀ p, 0 < primeLogPerturbedMass u a ε p) (p : Nat.Primes) :
    primeDyadicWeight (primeLogPerturbedGauge u a ε) p =
      primeLogPerturbedMass u a ε p := by
  exact primeDyadicWeight_gaugeOfMass _ hpos p

/-- The perturbed gauge equals the original gauge outside the finite mass support. -/
theorem primeLogPerturbedGauge_eq_of_notMem_support
    (u : Nat.Primes → ℝ) (a : Nat.Primes →₀ ℝ) (ε : ℝ) (p : Nat.Primes)
    (hp : p ∉ a.support) :
    primeLogPerturbedGauge u a ε p = u p := by
  have ha : a p = 0 := by
    simpa only [Finsupp.mem_support_iff, not_not] using hp
  rw [primeLogPerturbedGauge, primeLogGaugeOfMass, primeLogPerturbedMass, ha, mul_zero,
    add_zero, primeDyadicWeight]
  have hb : ((2 : ℝ)⁻¹) ^ (p : ℕ) ≠ 0 := by positivity
  rw [mul_div_cancel_left₀ _ hb, Real.log_exp]

/-- At zero mass time the reconstructed gauge is the original gauge. -/
theorem primeLogPerturbedGauge_zero
    (u : Nat.Primes → ℝ) (a : Nat.Primes →₀ ℝ) (p : Nat.Primes) :
    primeLogPerturbedGauge u a 0 p = u p := by
  rw [primeLogPerturbedGauge, primeLogGaugeOfMass, primeLogPerturbedMass, zero_mul,
    add_zero, primeDyadicWeight]
  have hb : ((2 : ℝ)⁻¹) ^ (p : ℕ) ≠ 0 := by positivity
  rw [mul_div_cancel_left₀ _ hb, Real.log_exp]

/-- Every coordinate of a finitely supported reconstructed gauge varies continuously with the
additive mass parameter at zero. -/
theorem continuousAt_primeLogPerturbedGauge
    (u : Nat.Primes → ℝ) (a : Nat.Primes →₀ ℝ) (p : Nat.Primes) :
    ContinuousAt (fun ε => primeLogPerturbedGauge u a ε p) 0 := by
  simp only [primeLogPerturbedGauge, primeLogGaugeOfMass, primeLogPerturbedMass]
  have hb : 0 < ((2 : ℝ)⁻¹) ^ (p : ℕ) := by positivity
  have hinner : ContinuousAt
      (fun ε : ℝ => (primeDyadicWeight u p + ε * a p) / ((2 : ℝ)⁻¹) ^ (p : ℕ)) 0 :=
    (continuousAt_const.add (continuousAt_id.mul continuousAt_const)).div_const _
  apply hinner.log
  simp only [zero_mul, add_zero]
  exact (div_pos (primeDyadicWeight_pos u p) hb).ne'

/-- A finite family of real functions continuous at zero has one positive radius controlling all
of them. -/
theorem exists_uniform_delta_finset
    {κ : Type*} [DecidableEq κ] (s : Finset κ) (f : κ → ℝ → ℝ)
    (hf : ∀ p ∈ s, ContinuousAt (f p) 0) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε, |ε| < δ → ∀ p ∈ s, |f p ε - f p 0| < η := by
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨1, by norm_num, by simp⟩
  | @insert p s hp ih =>
      have hfp : ContinuousAt (f p) 0 := hf p (Finset.mem_insert_self p s)
      have hfs : ∀ q ∈ s, ContinuousAt (f q) 0 := fun q hq =>
        hf q (Finset.mem_insert_of_mem hq)
      obtain ⟨δs, hδs, hδsprop⟩ := ih hfs
      obtain ⟨δp, hδp, hδpprop⟩ := (Metric.continuousAt_iff.mp hfp) η hη
      refine ⟨min δs δp, lt_min hδs hδp, ?_⟩
      intro ε hε q hq
      rcases Finset.mem_insert.mp hq with rfl | hqs
      · have hedist : dist ε 0 < δp := by
          simpa [Real.dist_eq] using lt_of_lt_of_le hε (min_le_right _ _)
        have hclose := hδpprop hedist
        simpa [Real.dist_eq] using hclose
      · exact hδsprop ε (lt_of_lt_of_le hε (min_le_left _ _)) q hqs

/-- Finitely supported mass perturbations converge uniformly back to the original logarithmic
gauge as the mass parameter tends to zero. -/
theorem primeLogPerturbedGauge_uniformly_small
    (u : Nat.Primes → ℝ) (a : Nat.Primes →₀ ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε, |ε| < δ →
      ∀ p, |primeLogPerturbedGauge u a ε p - u p| < η := by
  obtain ⟨δ, hδ, hprop⟩ := exists_uniform_delta_finset a.support
    (fun p ε => primeLogPerturbedGauge u a ε p)
    (fun p hp => continuousAt_primeLogPerturbedGauge u a p) hη
  refine ⟨δ, hδ, ?_⟩
  intro ε hεδ p
  by_cases hp : p ∈ a.support
  · simpa [primeLogPerturbedGauge_zero] using hprop ε hεδ p hp
  · rw [primeLogPerturbedGauge_eq_of_notMem_support u a ε p hp, sub_self, abs_zero]
    exact hη

/-- Only finitely many gauge coordinates change under a finitely supported mass perturbation. -/
theorem primeLogPerturbedGauge_changeSet_finite
    (u : Nat.Primes → ℝ) (a : Nat.Primes →₀ ℝ) (ε : ℝ) :
    Set.Finite {p | primeLogPerturbedGauge u a ε p ≠ u p} := by
  apply a.support.finite_toSet.subset
  intro p hp
  by_contra hps
  exact hp (primeLogPerturbedGauge_eq_of_notMem_support u a ε p hps)

/-- A gauge bounded above remains bounded above after a finitely supported positive mass
perturbation.  Positivity is needed only when the perturbed gauge is used to reconstruct masses. -/
theorem primeLogPerturbedGauge_bddAbove
    (u : Nat.Primes → ℝ) (a : Nat.Primes →₀ ℝ) (ε C : ℝ)
    (hu : ∀ p, u p ≤ C) :
    ∃ C', ∀ p, primeLogPerturbedGauge u a ε p ≤ C' := by
  let B := a.support.sum fun q => |primeLogPerturbedGauge u a ε q|
  refine ⟨C + B + |C|, ?_⟩
  intro p
  by_cases hp : p ∈ a.support
  · have hle : |primeLogPerturbedGauge u a ε p| ≤ B := by
      refine Finset.single_le_sum (s := a.support)
        (f := fun q => |primeLogPerturbedGauge u a ε q|) ?_ hp
      intro q hq
      exact abs_nonneg _
    have hpB : primeLogPerturbedGauge u a ε p ≤ B := (le_abs_self _).trans hle
    linarith [neg_abs_le C]
  · rw [primeLogPerturbedGauge_eq_of_notMem_support u a ε p hp]
    have hB : 0 ≤ B := Finset.sum_nonneg fun q hq => abs_nonneg _
    linarith [hu p, abs_nonneg C]

/-- A bounded gauge remains bounded after a finitely supported positive mass perturbation. -/
theorem primeLogPerturbedGauge_bounded
    (u : Nat.Primes → ℝ) (a : Nat.Primes →₀ ℝ) (ε C : ℝ)
    (hu : ∀ p, |u p| ≤ C) :
    ∃ C', ∀ p, |primeLogPerturbedGauge u a ε p| ≤ C' := by
  let B := a.support.sum fun q => |primeLogPerturbedGauge u a ε q|
  refine ⟨|C| + B, ?_⟩
  intro p
  have hB : 0 ≤ B := Finset.sum_nonneg fun q hq => abs_nonneg _
  by_cases hp : p ∈ a.support
  · have hle : |primeLogPerturbedGauge u a ε p| ≤ B := by
      refine Finset.single_le_sum (s := a.support)
        (f := fun q => |primeLogPerturbedGauge u a ε q|) ?_ hp
      intro q hq
      exact abs_nonneg _
    linarith [abs_nonneg C]
  · rw [primeLogPerturbedGauge_eq_of_notMem_support u a ε p hp]
    exact (hu p).trans (by linarith [le_abs_self C])

end

end GaloisForLFunctions.HTGeometry
