import Mathlib

/-!
# Polar amplitude, Fisher–phase coupling, and hidden projective history

A full-support complex amplitude on a finite set is exactly a positive probability together with a
relative phase.  Its Fubini–Study line element splits into one quarter of the Fisher–Rao metric plus
the weighted variance of phase velocity, and a loop of pure phase rotation leaves the probability
observer constant while having strictly positive projective length and nontrivial Berry holonomy.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset Complex

section PolarChart

variable {N : ℕ}

/-- The squared norm of a finite amplitude. -/
noncomputable def ampNormSq (v : Fin N → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

/-- The Hermitian inner product of two finite amplitudes. -/
def ampInner (v w : Fin N → ℂ) : ℂ := ∑ i, (starRingEnd ℂ) (v i) * w i

/-- The Fubini–Study speed of a tangent at a normalized amplitude:
`‖dψ‖² − |⟨ψ, dψ⟩|²`. -/
noncomputable def fsSpeedSq (ψ dψ : Fin N → ℂ) : ℝ := ampNormSq dψ - ‖ampInner ψ dψ‖ ^ 2

/-- The normalized polar amplitude `ψᵢ = √pᵢ e^{iφᵢ}`. -/
noncomputable def polarAmp (p φ : Fin N → ℝ) (i : Fin N) : ℂ :=
  ((Real.sqrt (p i) : ℝ) : ℂ) * Complex.exp (Complex.I * (φ i : ℂ))

/-- The polar tangent obtained from velocities `dp` of the probabilities and `dφ` of the phases. -/
noncomputable def polarTangent (p dp φ dφ : Fin N → ℝ) (i : Fin N) : ℂ :=
  (((dp i / (2 * Real.sqrt (p i)) : ℝ) : ℂ)
      + Complex.I * ((Real.sqrt (p i) * dφ i : ℝ) : ℂ))
    * Complex.exp (Complex.I * (φ i : ℂ))

theorem normSq_ofReal_add_I_mul (a b : ℝ) :
    ‖(a : ℂ) + Complex.I * (b : ℂ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  ring

theorem norm_exp_I_mul_ofReal (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I x

theorem normSq_polarTangent {p : Fin N → ℝ} (hp : ∀ i, 0 < p i) (dp φ dφ : Fin N → ℝ) (i : Fin N) :
    ‖polarTangent p dp φ dφ i‖ ^ 2
      = dp i ^ 2 / (4 * p i) + p i * dφ i ^ 2 := by
  have hsq : Real.sqrt (p i) ^ 2 = p i := Real.sq_sqrt (hp i).le
  have hpos : 0 < Real.sqrt (p i) := Real.sqrt_pos.mpr (hp i)
  rw [polarTangent, norm_mul, norm_exp_I_mul_ofReal, mul_one, normSq_ofReal_add_I_mul]
  have h1 : (dp i / (2 * Real.sqrt (p i))) ^ 2 = dp i ^ 2 / (4 * p i) := by
    rw [div_pow, mul_pow, hsq]
    norm_num
  have h2 : (Real.sqrt (p i) * dφ i) ^ 2 = p i * dφ i ^ 2 := by
    rw [mul_pow, hsq]
  rw [h1, h2]

/-- **The magnitude part of (2).** -/
theorem ampNormSq_polarTangent {p : Fin N → ℝ} (hp : ∀ i, 0 < p i) (dp φ dφ : Fin N → ℝ) :
    ampNormSq (polarTangent p dp φ dφ)
      = (∑ i, dp i ^ 2 / (4 * p i)) + ∑ i, p i * dφ i ^ 2 := by
  rw [ampNormSq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => normSq_polarTangent hp dp φ dφ i

/-- **The overlap part of (2).**  The Berry connection value is `i ∑ pᵢ dφᵢ`. -/
theorem ampInner_polarAmp_polarTangent {p : Fin N → ℝ} (hp : ∀ i, 0 < p i)
    {dp : Fin N → ℝ} (hdp : ∑ i, dp i = 0) (φ dφ : Fin N → ℝ) :
    ampInner (polarAmp p φ) (polarTangent p dp φ dφ)
      = Complex.I * ((∑ i, p i * dφ i : ℝ) : ℂ) := by
  have hterm : ∀ i : Fin N, (starRingEnd ℂ) (polarAmp p φ i) * polarTangent p dp φ dφ i
      = ((dp i / 2 : ℝ) : ℂ) + Complex.I * ((p i * dφ i : ℝ) : ℂ) := by
    intro i
    have hsq : Real.sqrt (p i) * Real.sqrt (p i) = p i := Real.mul_self_sqrt (hp i).le
    have hne : (Real.sqrt (p i) : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hp i))
    rw [polarAmp, polarTangent, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    have hc : (starRingEnd ℂ) (Complex.I * (φ i : ℂ)) = -(Complex.I * (φ i : ℂ)) := by
      rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [hc]
    have hexp : Complex.exp (-(Complex.I * (φ i : ℂ))) * Complex.exp (Complex.I * (φ i : ℂ)) = 1 := by
      rw [← Complex.exp_add]
      simp
    calc ((Real.sqrt (p i) : ℝ) : ℂ) * Complex.exp (-(Complex.I * (φ i : ℂ)))
        * ((((dp i / (2 * Real.sqrt (p i)) : ℝ) : ℂ)
            + Complex.I * ((Real.sqrt (p i) * dφ i : ℝ) : ℂ))
          * Complex.exp (Complex.I * (φ i : ℂ)))
        = ((Real.sqrt (p i) : ℝ) : ℂ)
            * (((dp i / (2 * Real.sqrt (p i)) : ℝ) : ℂ)
              + Complex.I * ((Real.sqrt (p i) * dφ i : ℝ) : ℂ))
            * (Complex.exp (-(Complex.I * (φ i : ℂ))) * Complex.exp (Complex.I * (φ i : ℂ))) := by
          ring
      _ = ((Real.sqrt (p i) : ℝ) : ℂ)
            * (((dp i / (2 * Real.sqrt (p i)) : ℝ) : ℂ)
              + Complex.I * ((Real.sqrt (p i) * dφ i : ℝ) : ℂ)) := by
          rw [hexp, mul_one]
      _ = ((dp i / 2 : ℝ) : ℂ) + Complex.I * ((p i * dφ i : ℝ) : ℂ) := by
          have hr : Real.sqrt (p i) * (dp i / (2 * Real.sqrt (p i))) = dp i / 2 := by
            field_simp
          have hi : Real.sqrt (p i) * (Real.sqrt (p i) * dφ i) = p i * dφ i := by
            rw [← mul_assoc, hsq]
          push_cast [← hr, ← hi]
          ring
  rw [ampInner, Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib]
  have h1 : ∑ i : Fin N, ((dp i / 2 : ℝ) : ℂ) = 0 := by
    rw [← Complex.ofReal_sum]
    have hsum : ∑ i : Fin N, dp i / 2 = (∑ i : Fin N, dp i) / 2 := by
      rw [Finset.sum_div]
    rw [hsum, hdp]
    simp
  have h2 : ∑ i : Fin N, Complex.I * ((p i * dφ i : ℝ) : ℂ)
      = Complex.I * ((∑ i, p i * dφ i : ℝ) : ℂ) := by
    rw [← Finset.mul_sum, ← Complex.ofReal_sum]
  rw [h1, h2, zero_add]

/-- **Theorem 2.1, equation (2).**  The Fubini–Study line element is one quarter of the Fisher–Rao
metric plus the weighted variance of the phase velocity. -/
theorem fsSpeedSq_polar {p : Fin N → ℝ} (hp : ∀ i, 0 < p i)
    {dp : Fin N → ℝ} (hdp : ∑ i, dp i = 0) (φ dφ : Fin N → ℝ) :
    fsSpeedSq (polarAmp p φ) (polarTangent p dp φ dφ)
      = (1 / 4) * (∑ i, dp i ^ 2 / p i) + (∑ i, p i * dφ i ^ 2)
        - (∑ i, p i * dφ i) ^ 2 := by
  rw [fsSpeedSq, ampNormSq_polarTangent hp, ampInner_polarAmp_polarTangent hp hdp]
  have hnorm : ‖Complex.I * ((∑ i, p i * dφ i : ℝ) : ℂ)‖ ^ 2 = (∑ i, p i * dφ i) ^ 2 := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hnorm]
  have hquarter : (∑ i, dp i ^ 2 / (4 * p i)) = (1 / 4) * ∑ i, dp i ^ 2 / p i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [hquarter]

/-- The polar tangent really is the derivative of the polar curve. -/
theorem hasDerivAt_polarAmp {P Φ : ℝ → Fin N → ℝ} {dp dφ : Fin N → ℝ} {t : ℝ} (i : Fin N)
    (hpos : 0 < P t i) (hdp : HasDerivAt (fun s => P s i) (dp i) t)
    (hdφ : HasDerivAt (fun s => Φ s i) (dφ i) t) :
    HasDerivAt (fun s => polarAmp (P s) (Φ s) i) (polarTangent (P t) dp (Φ t) dφ i) t := by
  have hsqrt : HasDerivAt (fun s => Real.sqrt (P s i))
      (dp i / (2 * Real.sqrt (P t i))) t := hdp.sqrt (ne_of_gt hpos)
  have hsqrtC : HasDerivAt (fun s => ((Real.sqrt (P s i) : ℝ) : ℂ))
      (((dp i / (2 * Real.sqrt (P t i)) : ℝ) : ℂ)) t := hsqrt.ofReal_comp
  have hphase : HasDerivAt (fun s => Complex.I * ((Φ s i : ℝ) : ℂ))
      (Complex.I * ((dφ i : ℝ) : ℂ)) t := hdφ.ofReal_comp.const_mul _
  have hexp : HasDerivAt (fun s => Complex.exp (Complex.I * ((Φ s i : ℝ) : ℂ)))
      (Complex.exp (Complex.I * ((Φ t i : ℝ) : ℂ)) * (Complex.I * ((dφ i : ℝ) : ℂ))) t :=
    hphase.cexp
  have hmul := hsqrtC.mul hexp
  have heq : ((dp i / (2 * Real.sqrt (P t i)) : ℝ) : ℂ)
        * Complex.exp (Complex.I * ((Φ t i : ℝ) : ℂ))
      + ((Real.sqrt (P t i) : ℝ) : ℂ)
        * (Complex.exp (Complex.I * ((Φ t i : ℝ) : ℂ)) * (Complex.I * ((dφ i : ℝ) : ℂ)))
      = polarTangent (P t) dp (Φ t) dφ i := by
    rw [polarTangent]
    push_cast
    ring
  rw [← heq]
  exact hmul

end PolarChart

/-! ## §3 — a closed loop of pure phase -/

section PhaseLoop

variable {N : ℕ}

/-- The pure-phase loop of equation (3). -/
noncomputable def phaseLoop (p : Fin N → ℝ) (k : Fin N → ℤ) (t : ℝ) : Fin N → ℂ :=
  polarAmp p fun j => (k j : ℝ) * t

/-- The weighted mean of the integer velocities. -/
def velMean (p : Fin N → ℝ) (k : Fin N → ℤ) : ℝ := ∑ i, p i * (k i : ℝ)

/-- The weighted variance of the integer velocities. -/
def velVar (p : Fin N → ℝ) (k : Fin N → ℤ) : ℝ :=
  (∑ i, p i * (k i : ℝ) ^ 2) - (velMean p k) ^ 2

/-- **The probability observer is constant along the loop.** -/
theorem normSq_phaseLoop {p : Fin N → ℝ} (hp : ∀ i, 0 ≤ p i) (k : Fin N → ℤ) (t : ℝ)
    (i : Fin N) : ‖phaseLoop p k t i‖ ^ 2 = p i := by
  rw [phaseLoop, polarAmp, norm_mul, norm_exp_I_mul_ofReal, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hp i)]

/-- **The loop closes at `2π`.** -/
theorem phaseLoop_two_pi (p : Fin N → ℝ) (k : Fin N → ℤ) :
    phaseLoop p k (2 * Real.pi) = phaseLoop p k 0 := by
  funext i
  rw [phaseLoop, phaseLoop, polarAmp, polarAmp]
  congr 1
  have hz : Complex.exp (Complex.I * (((k i : ℝ) * (2 * Real.pi) : ℝ) : ℂ)) = 1 := by
    have hsplit : Complex.I * (((k i : ℝ) * (2 * Real.pi) : ℝ) : ℂ)
        = (k i : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [hsplit, Complex.exp_int_mul_two_pi_mul_I]
  rw [hz]
  norm_num

/-- The velocity of the loop. -/
noncomputable def phaseLoopVelocity (p : Fin N → ℝ) (k : Fin N → ℤ) (t : ℝ) : Fin N → ℂ :=
  polarTangent p 0 (fun j => (k j : ℝ) * t) (fun j => (k j : ℝ))

theorem hasDerivAt_phaseLoop {p : Fin N → ℝ} (hp : ∀ i, 0 < p i) (k : Fin N → ℤ) (t : ℝ)
    (i : Fin N) :
    HasDerivAt (fun s => phaseLoop p k s i) (phaseLoopVelocity p k t i) t := by
  refine hasDerivAt_polarAmp (P := fun _ => p) (Φ := fun s j => (k j : ℝ) * s) (dp := 0)
    (dφ := fun j => (k j : ℝ)) i (hp i) (hasDerivAt_const _ _) ?_
  simpa using (hasDerivAt_id t).const_mul ((k i : ℝ))

/-- **Equation (4).**  The Fubini–Study speed of the loop is the weighted variance of the integer
velocities. -/
theorem fsSpeedSq_phaseLoop {p : Fin N → ℝ} (hp : ∀ i, 0 < p i) (k : Fin N → ℤ) (t : ℝ) :
    fsSpeedSq (phaseLoop p k t) (phaseLoopVelocity p k t) = velVar p k := by
  rw [phaseLoop, phaseLoopVelocity,
    fsSpeedSq_polar hp (dp := 0) (by simp) (fun j => (k j : ℝ) * t) (fun j => (k j : ℝ))]
  rw [velVar, velMean]
  have hzero : (1 / 4 : ℝ) * ∑ i, (0 : Fin N → ℝ) i ^ 2 / p i = 0 := by simp
  rw [hzero, zero_add]

/-- **Equation (5).**  The projective length of the loop. -/
theorem length_phaseLoop (p : Fin N → ℝ) (k : Fin N → ℤ) :
    ∫ _t in (0 : ℝ)..(2 * Real.pi), Real.sqrt (velVar p k)
      = 2 * Real.pi * Real.sqrt (velVar p k) := by
  rw [intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- The variance is a weighted sum of squares about the mean. -/
theorem velVar_eq_sum {p : Fin N → ℝ} (hsum : ∑ i, p i = 1) (k : Fin N → ℤ) :
    velVar p k = ∑ i, p i * ((k i : ℝ) - velMean p k) ^ 2 := by
  have hexp : ∑ i, p i * ((k i : ℝ) - velMean p k) ^ 2
      = (∑ i, p i * (k i : ℝ) ^ 2) - 2 * velMean p k * (∑ i, p i * (k i : ℝ))
        + (velMean p k) ^ 2 * ∑ i, p i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hexp, hsum, ← velMean]
  rw [velVar]
  ring

/-- **The loop has strictly positive length exactly when the integer velocities differ.** -/
theorem velVar_eq_zero_iff {p : Fin N → ℝ} (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (k : Fin N → ℤ) : velVar p k = 0 ↔ ∀ i j, k i = k j := by
  rw [velVar_eq_sum hsum]
  constructor
  · intro h i j
    have hnonneg : ∀ i ∈ Finset.univ, 0 ≤ p i * ((k i : ℝ) - velMean p k) ^ 2 := by
      intro i _
      have := (hp i).le
      positivity
    have hall : ∀ i ∈ Finset.univ, p i * ((k i : ℝ) - velMean p k) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h
    have hki : ∀ i : Fin N, (k i : ℝ) = velMean p k := by
      intro i
      have h1 := hall i (Finset.mem_univ i)
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 (ne_of_gt (hp i))
      · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
        linarith
    have : (k i : ℝ) = (k j : ℝ) := by rw [hki i, hki j]
    exact_mod_cast this
  · intro h
    refine Finset.sum_eq_zero fun i _ => ?_
    have hconst : velMean p k = (k i : ℝ) := by
      rw [velMean]
      have : ∀ j, p j * (k j : ℝ) = p j * (k i : ℝ) := by
        intro j
        rw [h j i]
      rw [Finset.sum_congr rfl fun j _ => this j, ← Finset.sum_mul, hsum, one_mul]
    rw [hconst]
    ring

/-- **Equation (6).**  The Berry connection value along the loop is `∑ pᵢ kᵢ`, so the loop
holonomy is `exp (2πi ∑ pᵢ kᵢ)`. -/
theorem berryConnection_phaseLoop {p : Fin N → ℝ} (hp : ∀ i, 0 < p i) (k : Fin N → ℤ) (t : ℝ) :
    ampInner (phaseLoop p k t) (phaseLoopVelocity p k t)
      = Complex.I * ((velMean p k : ℝ) : ℂ) := by
  rw [phaseLoop, phaseLoopVelocity,
    ampInner_polarAmp_polarTangent hp (dp := 0) (by simp) (fun j => (k j : ℝ) * t)
      (fun j => (k j : ℝ))]
  rw [velMean]

/-- The Berry holonomy of the loop. -/
noncomputable def berryHolonomy (p : Fin N → ℝ) (k : Fin N → ℤ) : ℂ :=
  Complex.exp (Complex.I * ((2 * Real.pi * velMean p k : ℝ) : ℂ))

theorem berryHolonomy_eq_exp_integral (p : Fin N → ℝ) (k : Fin N → ℤ) :
    berryHolonomy p k
      = Complex.exp (Complex.I * ((∫ _t in (0 : ℝ)..(2 * Real.pi), velMean p k : ℝ) : ℂ)) := by
  rw [berryHolonomy, intervalIntegral.integral_const, smul_eq_mul]
  congr 2
  push_cast
  ring

end PhaseLoop

/-! ## §4 — the hidden history and the two-level example -/

section HiddenHistory

variable {N : ℕ}

/-- The positive-probability observer of an amplitude. -/
noncomputable def probObserver (z : Fin N → ℂ) (i : Fin N) : ℝ := ‖z i‖ ^ 2 / ampNormSq z

/-- **The positive observer does not determine the projective class.**  The two amplitudes `(1,1)`
and `(1,−1)` have the same probability vector and are not proportional. -/
theorem probObserver_not_injective :
    probObserver (![1, 1] : Fin 2 → ℂ) = probObserver (![1, -1] : Fin 2 → ℂ)
      ∧ ¬ ∃ c : ℂ, ∀ i, (![1, -1] : Fin 2 → ℂ) i = c * (![1, 1] : Fin 2 → ℂ) i := by
  constructor
  · funext i
    rw [probObserver, probObserver, ampNormSq, ampNormSq, Fin.sum_univ_two, Fin.sum_univ_two]
    fin_cases i <;> norm_num
  · rintro ⟨c, hc⟩
    have h0 := hc 0
    have h1 := hc 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one] at h0 h1
    rw [← h0] at h1
    exact absurd h1 (by norm_num)

/-! ### The two-level example of §3 -/

/-- The balanced two-level probability. -/
noncomputable def twoLevelProb : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- The velocities `(0, 1)`. -/
def twoLevelVel : Fin 2 → ℤ := ![0, 1]

theorem twoLevelProb_pos : ∀ i, 0 < twoLevelProb i := by
  intro i
  fin_cases i <;> norm_num [twoLevelProb]

theorem twoLevelProb_sum : ∑ i, twoLevelProb i = 1 := by
  rw [Fin.sum_univ_two]
  norm_num [twoLevelProb]

theorem velMean_twoLevel : velMean twoLevelProb twoLevelVel = 1 / 2 := by
  rw [velMean, Fin.sum_univ_two]
  norm_num [twoLevelProb, twoLevelVel]

theorem velVar_twoLevel : velVar twoLevelProb twoLevelVel = 1 / 4 := by
  rw [velVar, velMean_twoLevel, Fin.sum_univ_two]
  norm_num [twoLevelProb, twoLevelVel]

/-- **The example of §3.**  The positive observer is stationary, the projective loop has length
`π`, and the Berry holonomy is `−1`. -/
theorem twoLevel_example :
    (∀ (t : ℝ) (i : Fin 2), ‖phaseLoop twoLevelProb twoLevelVel t i‖ ^ 2 = twoLevelProb i)
      ∧ (∀ t : ℝ, fsSpeedSq (phaseLoop twoLevelProb twoLevelVel t)
        (phaseLoopVelocity twoLevelProb twoLevelVel t) = 1 / 4)
      ∧ (∫ _t in (0 : ℝ)..(2 * Real.pi), Real.sqrt (velVar twoLevelProb twoLevelVel))
        = Real.pi
      ∧ berryHolonomy twoLevelProb twoLevelVel = -1 := by
  refine ⟨fun t i => normSq_phaseLoop (fun j => (twoLevelProb_pos j).le) _ _ _, fun t => ?_, ?_, ?_⟩
  · rw [fsSpeedSq_phaseLoop twoLevelProb_pos, velVar_twoLevel]
  · rw [length_phaseLoop, velVar_twoLevel]
    have : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [this]
    ring
  · rw [berryHolonomy, velMean_twoLevel]
    have hpi : Complex.I * ((2 * Real.pi * (1 / 2) : ℝ) : ℂ)
        = ((Real.pi : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hpi, Complex.exp_pi_mul_I]

end HiddenHistory

/-! ## Theorem 1.1 — the polar projective chart -/

section PolarBijection

variable {N : ℕ}

/-- Full-support amplitude vectors. -/
abbrev FullAmp (N : ℕ) : Type := {z : Fin N → ℂ // ∀ i, z i ≠ 0}

/-- Projective equivalence of full-support amplitudes. -/
def projSetoid (N : ℕ) : Setoid (FullAmp N) where
  r z w := ∃ c : ℂˣ, ∀ i, (w : Fin N → ℂ) i = (c : ℂ) * (z : Fin N → ℂ) i
  iseqv :=
    { refl := fun z => ⟨1, fun i => by simp⟩
      symm := fun {z w} ⟨c, hc⟩ => ⟨c⁻¹, fun i => by
        rw [hc i, ← mul_assoc]
        simp⟩
      trans := fun {z w v} ⟨c, hc⟩ ⟨d, hd⟩ => ⟨d * c, fun i => by
        rw [hd i, hc i, Units.val_mul, mul_assoc]⟩ }

/-- Projective classes of full-support amplitudes. -/
def ProjAmp (N : ℕ) : Type := Quotient (projSetoid N)

/-- The open probability simplex. -/
def OpenSimplex (N : ℕ) : Type := {p : Fin N → ℝ // (∀ i, 0 < p i) ∧ ∑ i, p i = 1}

/-- Relative-phase equivalence: two phase vectors differ by one common phase. -/
def phaseSetoid (N : ℕ) : Setoid (Fin N → Circle) where
  r u v := ∃ c : Circle, ∀ i, v i = c * u i
  iseqv :=
    { refl := fun u => ⟨1, fun i => by simp⟩
      symm := fun {u v} ⟨c, hc⟩ => ⟨c⁻¹, fun i => by rw [hc i, ← mul_assoc]; simp⟩
      trans := fun {u v w} ⟨c, hc⟩ ⟨d, hd⟩ => ⟨d * c, fun i => by rw [hd i, hc i, mul_assoc]⟩ }

/-- Relative-phase classes `U(1)^N / U(1)`. -/
def PhaseClass (N : ℕ) : Type := Quotient (phaseSetoid N)

theorem ampNormSq_pos [NeZero N] (z : FullAmp N) : 0 < ampNormSq (z : Fin N → ℂ) := by
  haveI : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩⟩
  obtain ⟨i₀⟩ := ‹Nonempty (Fin N)›
  refine Finset.sum_pos' (fun i _ => by positivity) ⟨i₀, Finset.mem_univ i₀, ?_⟩
  have := z.2 i₀
  positivity

/-- The probability observer of a full-support amplitude. -/
noncomputable def ampProb (z : FullAmp N) : Fin N → ℝ :=
  fun i => ‖(z : Fin N → ℂ) i‖ ^ 2 / ampNormSq (z : Fin N → ℂ)

theorem ampProb_pos [NeZero N] (z : FullAmp N) (i : Fin N) : 0 < ampProb z i := by
  have h1 : (0 : ℝ) < ‖(z : Fin N → ℂ) i‖ ^ 2 := by
    have := z.2 i
    positivity
  exact div_pos h1 (ampNormSq_pos z)

theorem ampProb_sum [NeZero N] (z : FullAmp N) : ∑ i, ampProb z i = 1 := by
  show ∑ i, ‖(z : Fin N → ℂ) i‖ ^ 2 / ampNormSq (z : Fin N → ℂ) = 1
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (ampNormSq_pos z))

/-- The phase of a full-support amplitude. -/
noncomputable def ampPhase (z : FullAmp N) (i : Fin N) : Circle :=
  ⟨(z : Fin N → ℂ) i / (‖(z : Fin N → ℂ) i‖ : ℂ), by
    show _ ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    exact div_self (by simpa using z.2 i)⟩

theorem ampPhase_coe (z : FullAmp N) (i : Fin N) :
    ((ampPhase z i : Circle) : ℂ) = (z : Fin N → ℂ) i / (‖(z : Fin N → ℂ) i‖ : ℂ) := rfl

/-- The polar data of a full-support amplitude. -/
noncomputable def toPolarData [NeZero N] (z : FullAmp N) : OpenSimplex N × (Fin N → Circle) :=
  (⟨ampProb z, ampProb_pos z, ampProb_sum z⟩, ampPhase z)

/-- Scaling multiplies the norm square by `|c|²`. -/
theorem ampNormSq_smul (c : ℂ) (z : Fin N → ℂ) :
    ampNormSq (fun i => c * z i) = ‖c‖ ^ 2 * ampNormSq z := by
  rw [ampNormSq, ampNormSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_mul, mul_pow]

/-- The probability observer is projective. -/
theorem ampProb_of_equiv [NeZero N] {z w : FullAmp N} (h : (projSetoid N).r z w) :
    ampProb w = ampProb z := by
  obtain ⟨c, hc⟩ := h
  have hcne : ‖(c : ℂ)‖ ^ 2 ≠ 0 := by
    have : (c : ℂ) ≠ 0 := c.ne_zero
    positivity
  funext i
  have hnormw : ‖(w : Fin N → ℂ) i‖ ^ 2 = ‖(c : ℂ)‖ ^ 2 * ‖(z : Fin N → ℂ) i‖ ^ 2 := by
    rw [hc i, norm_mul, mul_pow]
  have hM : ampNormSq (w : Fin N → ℂ) = ‖(c : ℂ)‖ ^ 2 * ampNormSq (z : Fin N → ℂ) := by
    rw [ampNormSq, ampNormSq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hc j, norm_mul, mul_pow]
  show ‖(w : Fin N → ℂ) i‖ ^ 2 / ampNormSq (w : Fin N → ℂ)
    = ‖(z : Fin N → ℂ) i‖ ^ 2 / ampNormSq (z : Fin N → ℂ)
  rw [hnormw, hM, mul_div_mul_left _ _ hcne]

/-- The phase class is projective. -/
theorem ampPhase_of_equiv {z w : FullAmp N} (h : (projSetoid N).r z w) :
    (phaseSetoid N).r (ampPhase z) (ampPhase w) := by
  obtain ⟨c, hc⟩ := h
  have hcne : ((c : ℂ)) ≠ 0 := c.ne_zero
  have hnorm : ‖(c : ℂ)‖ ≠ 0 := by simp [hcne]
  refine ⟨⟨(c : ℂ) / (‖(c : ℂ)‖ : ℂ), ?_⟩, fun i => ?_⟩
  · show _ ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    exact div_self hnorm
  · apply Subtype.ext
    show (w : Fin N → ℂ) i / (‖(w : Fin N → ℂ) i‖ : ℂ)
      = ((c : ℂ) / (‖(c : ℂ)‖ : ℂ)) * ((z : Fin N → ℂ) i / (‖(z : Fin N → ℂ) i‖ : ℂ))
    have hzi : ‖(z : Fin N → ℂ) i‖ ≠ 0 := by simp [z.2 i]
    rw [hc i, norm_mul]
    push_cast
    field_simp

/-- The amplitude reconstructed from polar data. -/
noncomputable def ofPolarData (pu : OpenSimplex N × (Fin N → Circle)) : FullAmp N :=
  ⟨fun i => ((Real.sqrt (pu.1.1 i) : ℝ) : ℂ) * ((pu.2 i : Circle) : ℂ), by
    intro i
    have h1 : (0 : ℝ) < Real.sqrt (pu.1.1 i) := Real.sqrt_pos.mpr (pu.1.2.1 i)
    have h2 : ((pu.2 i : Circle) : ℂ) ≠ 0 := by
      intro hcon
      have hone : ‖((pu.2 i : Circle) : ℂ)‖ = 1 := by simp
      rw [hcon] at hone
      simp at hone
    exact mul_ne_zero (by simp [ne_of_gt h1]) h2⟩

theorem ampNormSq_ofPolarData (pu : OpenSimplex N × (Fin N → Circle)) :
    ampNormSq ((ofPolarData pu : FullAmp N) : Fin N → ℂ) = 1 := by
  rw [ampNormSq]
  have hterm : ∀ i : Fin N, ‖((ofPolarData pu : FullAmp N) : Fin N → ℂ) i‖ ^ 2 = pu.1.1 i := by
    intro i
    show ‖((Real.sqrt (pu.1.1 i) : ℝ) : ℂ) * ((pu.2 i : Circle) : ℂ)‖ ^ 2 = pu.1.1 i
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), show ‖((pu.2 i : Circle) : ℂ)‖ = 1 by simp, mul_one,
      Real.sq_sqrt (pu.1.2.1 i).le]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  exact pu.1.2.2

theorem ampProb_ofPolarData [NeZero N] (pu : OpenSimplex N × (Fin N → Circle)) :
    ampProb (ofPolarData pu) = pu.1.1 := by
  funext i
  rw [ampProb, ampNormSq_ofPolarData, div_one]
  show ‖((Real.sqrt (pu.1.1 i) : ℝ) : ℂ) * ((pu.2 i : Circle) : ℂ)‖ ^ 2 = pu.1.1 i
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), show ‖((pu.2 i : Circle) : ℂ)‖ = 1 by simp, mul_one,
    Real.sq_sqrt (pu.1.2.1 i).le]

theorem ampPhase_ofPolarData (pu : OpenSimplex N × (Fin N → Circle)) :
    ampPhase (ofPolarData pu) = pu.2 := by
  funext i
  apply Subtype.ext
  rw [ampPhase_coe]
  have hnorm : ‖((ofPolarData pu : FullAmp N) : Fin N → ℂ) i‖ = Real.sqrt (pu.1.1 i) := by
    show ‖((Real.sqrt (pu.1.1 i) : ℝ) : ℂ) * ((pu.2 i : Circle) : ℂ)‖ = _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), show ‖((pu.2 i : Circle) : ℂ)‖ = 1 by simp, mul_one]
  rw [hnorm]
  show ((Real.sqrt (pu.1.1 i) : ℝ) : ℂ) * ((pu.2 i : Circle) : ℂ)
      / ((Real.sqrt (pu.1.1 i) : ℝ) : ℂ) = _
  have hne : ((Real.sqrt (pu.1.1 i) : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt (Real.sqrt_pos.mpr (pu.1.2.1 i))
  field_simp

/-- **Theorem 1.1, equation (1).**  The polar chart is a bijection between the full-support
projective amplitudes and the pairs (open probability, relative-phase class). -/
noncomputable def polarEquiv [NeZero N] : ProjAmp N ≃ OpenSimplex N × PhaseClass N where
  toFun := Quotient.lift
    (fun z : FullAmp N => ((⟨ampProb z, ampProb_pos z, ampProb_sum z⟩ : OpenSimplex N),
      Quotient.mk (phaseSetoid N) (ampPhase z))) (by
      intro z w h
      refine Prod.ext (Subtype.ext (ampProb_of_equiv h).symm) ?_
      exact Quotient.sound (ampPhase_of_equiv h))
  invFun := fun pu => Quotient.liftOn pu.2
    (fun u => Quotient.mk (projSetoid N) (ofPolarData (pu.1, u))) (by
      rintro u v ⟨c, hc⟩
      refine Quotient.sound ⟨Units.mk0 ((c : Circle) : ℂ) (by
        intro hcon
        have hone : ‖((c : Circle) : ℂ)‖ = 1 := by simp
        rw [hcon] at hone
        simp at hone), fun i => ?_⟩
      show ((Real.sqrt (pu.1.1 i) : ℝ) : ℂ) * ((v i : Circle) : ℂ)
        = ((c : Circle) : ℂ) * (((Real.sqrt (pu.1.1 i) : ℝ) : ℂ) * ((u i : Circle) : ℂ))
      rw [hc i]
      show ((Real.sqrt (pu.1.1 i) : ℝ) : ℂ) * (((c : Circle) : ℂ) * ((u i : Circle) : ℂ)) = _
      ring)
  left_inv := by
    refine Quotient.ind fun z => ?_
    have hM : 0 < ampNormSq (z : Fin N → ℂ) := ampNormSq_pos z
    have hsqrt : 0 < Real.sqrt (ampNormSq (z : Fin N → ℂ)) := Real.sqrt_pos.mpr hM
    refine Quotient.sound ⟨Units.mk0 ((Real.sqrt (ampNormSq (z : Fin N → ℂ)) : ℝ) : ℂ)
      (by simp [ne_of_gt hsqrt]), fun i => ?_⟩
    have hzi : ‖(z : Fin N → ℂ) i‖ ≠ 0 := by simp [z.2 i]
    show (z : Fin N → ℂ) i
      = ((Real.sqrt (ampNormSq (z : Fin N → ℂ)) : ℝ) : ℂ)
        * (((Real.sqrt (ampProb z i) : ℝ) : ℂ) * ((ampPhase z i : Circle) : ℂ))
    have hprob : Real.sqrt (ampProb z i)
        = ‖(z : Fin N → ℂ) i‖ / Real.sqrt (ampNormSq (z : Fin N → ℂ)) := by
      show Real.sqrt (‖(z : Fin N → ℂ) i‖ ^ 2 / ampNormSq (z : Fin N → ℂ)) = _
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (norm_nonneg _)]
    rw [hprob, ampPhase_coe]
    push_cast
    field_simp
    have hne : ((Real.sqrt (ampNormSq (z : Fin N → ℂ)) : ℝ) : ℂ) * ((‖(z : Fin N → ℂ) i‖ : ℝ) : ℂ)
        ≠ 0 := by
      refine mul_ne_zero ?_ ?_
      · simp [ne_of_gt hsqrt]
      · simp [hzi]
    rw [mul_assoc, mul_div_assoc, div_self hne, mul_one]
  right_inv := by
    rintro ⟨p, uc⟩
    induction uc using Quotient.ind with
    | _ u =>
      refine Prod.ext (Subtype.ext (ampProb_ofPolarData (p, u))) ?_
      exact congrArg (Quotient.mk (phaseSetoid N)) (ampPhase_ofPolarData (p, u))

/-- **The exact fibre of the positive observer is the relative-phase torus.**  Under the polar
chart the probability observer is the first projection, so its fibre over any `p` is the whole
relative-phase class space. -/
theorem polarEquiv_fst [NeZero N] (z : FullAmp N) :
    ((polarEquiv (N := N)) (Quotient.mk (projSetoid N) z)).1.1 = ampProb z := rfl

/-- **The law.**  A full-support projective amplitude is exactly probability together with
relative phase; the Fubini–Study line element splits into one quarter of the Fisher–Rao metric plus
the weighted phase variance; and a pure-phase loop keeps the probability observer constant while
having Fubini–Study speed equal to the weighted variance of its integer velocities. -/
theorem polar_amplitude_fisher_phase_law [NeZero N] {p : Fin N → ℝ} (hp : ∀ i, 0 < p i)
    (hsum : ∑ i, p i = 1) (k : Fin N → ℤ) (t : ℝ) :
    (∀ i, ‖phaseLoop p k t i‖ ^ 2 = p i) ∧
      phaseLoop p k (2 * Real.pi) = phaseLoop p k 0 ∧
      fsSpeedSq (phaseLoop p k t) (phaseLoopVelocity p k t) = velVar p k ∧
      (∫ _s in (0 : ℝ)..(2 * Real.pi), Real.sqrt (velVar p k))
        = 2 * Real.pi * Real.sqrt (velVar p k) ∧
      ampInner (phaseLoop p k t) (phaseLoopVelocity p k t)
        = Complex.I * ((velMean p k : ℝ) : ℂ) ∧
      (velVar p k = 0 ↔ ∀ i j, k i = k j) :=
  ⟨fun i => normSq_phaseLoop (fun j => (hp j).le) k t i, phaseLoop_two_pi p k,
    fsSpeedSq_phaseLoop hp k t, length_phaseLoop p k, berryConnection_phaseLoop hp k t,
    velVar_eq_zero_iff hp hsum k⟩

end PolarBijection

end GaloisForLFunctions.HTGeometry
