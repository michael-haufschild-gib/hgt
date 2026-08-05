import GaloisForLFunctions.HTGeometry.KleinGordonTrappedAllTime

/-!
# The Floquet normal form

A Floquet multiplier is a point of the spectrum of the monodromy; when it is *attained*, by an
eigenvector of the monodromy, the corresponding solution is rigid. Restarting the evolution after one
period (the restart law) shows that such a solution reproduces itself up to the multiplier at every
instant:

`v(t + T) = k · v(t)`   for all `t`,

so its stroboscopic growth is exact — `‖v(nT)‖ = |k|ⁿ‖v(0)‖`, with no `ε` and no one-period constant —
and, writing `k = e^{μT}`, the solution splits as

`v(t) = e^{μt} p(t)`,   `p` periodic with period `T`,

which is the classical Floquet normal form. The multiplier is the entire content of the solution's
long-time behaviour: the periodic factor contributes nothing to the rate.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The powers of an operator act on an eigenvector by the powers of its eigenvalue. -/
theorem pow_apply_of_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : F →L[ℂ] F} {k : ℂ} {v : F} (heig : f v = k • v) (n : ℕ) : (f ^ n) v = k ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : (f ^ (n + 1)) v = f ((f ^ n) v) := by
        rw [pow_succ']
        rfl
      rw [hstep, ih, map_smul, heig, smul_smul, ← pow_succ]

section NormalForm

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- **The state is homogeneous in the Cauchy datum.** -/
theorem kgFieldStateT_smul (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (k : ℂ) (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldStateT W (k • g) (k • h) t = k • kgFieldStateT W g h t := by
  rw [kgFieldStateT_eq_kgStateMildT hb0 hWb hWs, kgFieldStateT_eq_kgStateMildT hb0 hWb hWs]
  have hlin := kgStateMildT_linear hb0 hWb hWs k 0 g h g h t
  simpa using hlin

/-- **The shift law**: in a periodic background the solution advanced by one period is the solution
restarted from the state it has reached. -/
theorem kgFieldStateT_shift (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldStateT W g h (t + T)
      = kgFieldStateT W (kgFieldGradT W g h T) (kgFieldVelT W g h T) t := by
  have hshift : (fun ρ : ℝ => W (ρ + T)) = W := funext hper
  have hr := kgFieldStateT_restart hb0 hWb hWs g h t T
  rwa [hshift] at hr

set_option maxHeartbeats 1000000 in
/-- **A Floquet eigen-solution multiplies by its multiplier over every period**, not only at
multiples of the period. -/
theorem kgFieldStateT_eigen_shift (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) {k : ℂ} (g h : Lp ℂ 2 (volume : Measure E))
    (heig : kgMonodromy W b hb0 hWb hWs T (kgPair E (g, h)) = k • kgPair E (g, h)) (t : ℝ) :
    kgFieldStateT W g h (t + T) = k • kgFieldStateT W g h t := by
  have hM : kgFieldStateT W g h T = k • kgPair E (g, h) := by
    rw [← heig, kgMonodromy_apply hb0 hWb hWs, kgPeriodMap_apply]
    simp
  have hg : kgFieldGradT W g h T = k • g := by
    have hc := congrArg (fun v : KGEnergy E => v.fst) hM
    simpa [kgFieldStateT, kgEnergy_fst_smul] using hc
  have hh : kgFieldVelT W g h T = k • h := by
    have hc := congrArg (fun v : KGEnergy E => v.snd) hM
    simpa [kgFieldStateT, kgEnergy_snd_smul] using hc
  rw [kgFieldStateT_shift hb0 hWb hWs hper g h t, hg, hh, kgFieldStateT_smul hb0 hWb hWs]

/-- **The exact stroboscopic law along a Floquet eigen-solution.** -/
theorem kgFieldStateT_eigen_pow (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) {k : ℂ} (g h : Lp ℂ 2 (volume : Measure E))
    (heig : kgMonodromy W b hb0 hWb hWs T (kgPair E (g, h)) = k • kgPair E (g, h)) (n : ℕ) :
    kgFieldStateT W g h ((n : ℝ) * T) = k ^ n • kgPair E (g, h) := by
  rw [kgFieldStateT_monodromy_pow hb0 hWb hWs hper g h n]
  exact pow_apply_of_smul heig n

/-- **The growth of an eigen-solution is exactly geometric**, with ratio the modulus of its
multiplier. -/
theorem norm_kgFieldStateT_eigen (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) {k : ℂ} (g h : Lp ℂ 2 (volume : Measure E))
    (heig : kgMonodromy W b hb0 hWb hWs T (kgPair E (g, h)) = k • kgPair E (g, h)) (n : ℕ) :
    ‖kgFieldStateT W g h ((n : ℝ) * T)‖ = ‖k‖ ^ n * ‖kgPair E (g, h)‖ := by
  rw [kgFieldStateT_eigen_pow hb0 hWb hWs hper g h heig n, norm_smul, norm_pow]

set_option maxHeartbeats 1000000 in
/-- **The energy of an eigen-solution is exactly geometric.** -/
theorem kgFieldEnergyT_eigen (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) {k : ℂ} (g h : Lp ℂ 2 (volume : Measure E))
    (heig : kgMonodromy W b hb0 hWb hWs T (kgPair E (g, h)) = k • kgPair E (g, h)) (n : ℕ) :
    ‖kgFieldGradT W g h ((n : ℝ) * T)‖ ^ 2 + ‖kgFieldVelT W g h ((n : ℝ) * T)‖ ^ 2
      = (‖k‖ ^ 2) ^ n * (‖g‖ ^ 2 + ‖h‖ ^ 2) := by
  have hk : (‖k‖ ^ n) ^ 2 = (‖k‖ ^ 2) ^ n := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [kgFieldEnergyT_eq_norm_sq W g h ((n : ℝ) * T),
    norm_kgFieldStateT_eigen hb0 hWb hWs hper g h heig n, mul_pow, hk, norm_kgPair_sq]

set_option maxHeartbeats 1000000 in
/-- **The Floquet normal form.** An eigen-solution of a periodically driven field is an exponential
times a periodic state. -/
theorem exists_floquet_normal_form (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hT : T ≠ 0) {k : ℂ} (hk : k ≠ 0)
    (g h : Lp ℂ 2 (volume : Measure E))
    (heig : kgMonodromy W b hb0 hWb hWs T (kgPair E (g, h)) = k • kgPair E (g, h)) :
    ∃ μ : ℂ, ∃ p : ℝ → KGEnergy E,
      (∀ t : ℝ, p (t + T) = p t) ∧
        ∀ t : ℝ, kgFieldStateT W g h t = Complex.exp (μ * t) • p t := by
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT
  set μ : ℂ := Complex.log k / (T : ℂ) with hμ
  have hμT : Complex.exp (μ * (T : ℂ)) = k := by
    rw [hμ, div_mul_cancel₀ _ hTc, Complex.exp_log hk]
  have hinv : Complex.exp (-(μ * (T : ℂ))) = k⁻¹ := by
    rw [Complex.exp_neg, hμT]
  refine ⟨μ, fun τ : ℝ => Complex.exp (-(μ * (τ : ℂ))) • kgFieldStateT W g h τ, fun t => ?_,
    fun t => ?_⟩
  · show Complex.exp (-(μ * ((t + T : ℝ) : ℂ))) • kgFieldStateT W g h (t + T)
        = Complex.exp (-(μ * (t : ℂ))) • kgFieldStateT W g h t
    have hcast : ((t + T : ℝ) : ℂ) = (t : ℂ) + (T : ℂ) := by push_cast; ring
    have hsplit : -(μ * ((t : ℂ) + (T : ℂ))) = -(μ * (t : ℂ)) + -(μ * (T : ℂ)) := by ring
    rw [hcast, kgFieldStateT_eigen_shift hb0 hWb hWs hper g h heig t, smul_smul, hsplit,
      Complex.exp_add, hinv, mul_assoc, inv_mul_cancel₀ hk, mul_one]
  · show kgFieldStateT W g h t
        = Complex.exp (μ * (t : ℂ)) • (Complex.exp (-(μ * (t : ℂ))) • kgFieldStateT W g h t)
    rw [smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]

end NormalForm

end GaloisForLFunctions.HTGeometry
