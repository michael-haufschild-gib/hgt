import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonEigenClock

/-!
# The exact envelope of a Floquet eigen-solution

The normal form writes an eigen-solution as `v(t) = e^{μt}p(t)` with `p` continuous and `T`-periodic.
A continuous periodic function is bounded, and — if it never vanishes — bounded away from zero, both
by constants read off a single period. So the eigen-solution has an exact two-sided exponential
envelope, valid at every real time:

`m·e^{(Re μ)t} ≤ ‖v(t)‖ ≤ M·e^{(Re μ)t}`.

There is no `ε` and no one-period loss: the rate is exactly `Re μ = log|k|/T`, the Floquet exponent,
and the only freedom is the pair of constants. For a weak static real potential the multiplier lies on
the unit circle, the exponent vanishes, and the envelope is flat — the clock's state norm is confined
between two positive constants for all time.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## Continuous periodic functions -/

section PeriodicBounds

variable {F : Type*} [NormedAddCommGroup F] {p : ℝ → F} {T : ℝ}

/-- **A continuous periodic function is bounded**, by a bound read off a single period. -/
theorem exists_bound_of_periodic (hp : Continuous p) (hper : Function.Periodic p T) (hT : 0 < T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, ‖p t‖ ≤ M := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hp.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  obtain ⟨y, hy, hval⟩ := hper.exists_mem_Ico₀ hT t
  rw [hval]
  exact le_trans (hC y (Set.Ico_subset_Icc_self hy)) (le_max_left _ _)

/-- **A continuous periodic function that never vanishes is bounded away from zero.** -/
theorem exists_pos_lower_bound_of_periodic (hp : Continuous p) (hper : Function.Periodic p T)
    (hT : 0 < T) (hne : ∀ t : ℝ, p t ≠ 0) : ∃ m : ℝ, 0 < m ∧ ∀ t : ℝ, m ≤ ‖p t‖ := by
  obtain ⟨y₀, _, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_isMinOn
    (Set.nonempty_Icc.mpr hT.le) hp.norm.continuousOn
  refine ⟨‖p y₀‖, norm_pos_iff.mpr (hne y₀), fun t => ?_⟩
  obtain ⟨y, hy, hval⟩ := hper.exists_mem_Ico₀ hT t
  rw [hval]
  exact isMinOn_iff.mp hmin y (Set.Ico_subset_Icc_self hy)

end PeriodicBounds

/-! ## The periodic part of an eigen-solution -/

section Envelope

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- The periodic part of a Floquet eigen-solution with exponent `μ`. -/
def kgFloquetPeriodicPart (W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)))
    (g h : Lp ℂ 2 (volume : Measure E)) (μ : ℂ) : ℝ → KGEnergy E :=
  fun t => Complex.exp (-(μ * (t : ℂ))) • kgFieldStateT W g h t

/-- The solution is its exponential factor times its periodic part. -/
theorem kgFieldStateT_eq_exp_smul (μ : ℂ) (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldStateT W g h t = Complex.exp (μ * (t : ℂ)) • kgFloquetPeriodicPart W g h μ t := by
  rw [kgFloquetPeriodicPart, smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero,
    one_smul]

theorem continuous_kgFloquetPeriodicPart (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (g h : Lp ℂ 2 (volume : Measure E)) (μ : ℂ) :
    Continuous (kgFloquetPeriodicPart W g h μ) := by
  have hexp : Continuous fun t : ℝ => Complex.exp (-(μ * (t : ℂ))) :=
    Complex.continuous_exp.comp (((continuous_const.mul Complex.continuous_ofReal).neg))
  exact hexp.smul (continuous_kgFieldStateT hb0 hWb hWs g h)

/-- **The periodic part of an eigen-solution is periodic.** -/
theorem periodic_kgFloquetPeriodicPart (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) {k μ : ℂ} (hμ : Complex.exp (μ * (T : ℂ)) = k)
    (g h : Lp ℂ 2 (volume : Measure E))
    (heig : kgMonodromy W b hb0 hWb hWs T (kgPair E (g, h)) = k • kgPair E (g, h)) :
    Function.Periodic (kgFloquetPeriodicPart W g h μ) T := by
  have hk : k ≠ 0 := by
    rw [← hμ]
    exact Complex.exp_ne_zero _
  have hinv : Complex.exp (-(μ * (T : ℂ))) = k⁻¹ := by
    rw [Complex.exp_neg, hμ]
  intro t
  show Complex.exp (-(μ * ((t + T : ℝ) : ℂ))) • kgFieldStateT W g h (t + T)
      = Complex.exp (-(μ * (t : ℂ))) • kgFieldStateT W g h t
  have hcast : ((t + T : ℝ) : ℂ) = (t : ℂ) + (T : ℂ) := by push_cast; ring
  have hsplit : -(μ * ((t : ℂ) + (T : ℂ))) = -(μ * (t : ℂ)) + -(μ * (T : ℂ)) := by ring
  rw [hcast, kgFieldStateT_eigen_shift hb0 hWb hWs hper g h heig t, smul_smul, hsplit,
    Complex.exp_add, hinv, mul_assoc, inv_mul_cancel₀ hk, mul_one]

/-- The norm of the solution splits as the real exponential of the rate times the periodic part. -/
theorem norm_kgFieldStateT_eq_exp_mul (μ : ℂ) (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldStateT W g h t‖
      = Real.exp (μ.re * t) * ‖kgFloquetPeriodicPart W g h μ t‖ := by
  have hre : (μ * (t : ℂ)).re = μ.re * t := by simp [Complex.mul_re]
  rw [kgFieldStateT_eq_exp_smul μ g h t, norm_smul, Complex.norm_exp, hre]

/-- **The exponential envelope of an eigen-solution**, above, at every real time. -/
theorem exists_envelope_of_eigen (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hT : 0 < T) {k μ : ℂ}
    (hμ : Complex.exp (μ * (T : ℂ)) = k) (g h : Lp ℂ 2 (volume : Measure E))
    (heig : kgMonodromy W b hb0 hWb hWs T (kgPair E (g, h)) = k • kgPair E (g, h)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, ‖kgFieldStateT W g h t‖ ≤ M * Real.exp (μ.re * t) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_periodic
    (continuous_kgFloquetPeriodicPart hb0 hWb hWs g h μ)
    (periodic_kgFloquetPeriodicPart hb0 hWb hWs hper hμ g h heig) hT
  refine ⟨M, hM0, fun t => ?_⟩
  rw [norm_kgFieldStateT_eq_exp_mul μ g h t, mul_comm M]
  exact mul_le_mul_of_nonneg_left (hM t) (Real.exp_pos _).le

/-- **The exact two-sided envelope of a nonvanishing eigen-solution.** -/
theorem exists_two_sided_envelope_of_eigen (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hT : 0 < T) {k μ : ℂ}
    (hμ : Complex.exp (μ * (T : ℂ)) = k) (g h : Lp ℂ 2 (volume : Measure E))
    (heig : kgMonodromy W b hb0 hWb hWs T (kgPair E (g, h)) = k • kgPair E (g, h))
    (hne : ∀ t : ℝ, kgFieldStateT W g h t ≠ 0) :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧ ∀ t : ℝ,
      m * Real.exp (μ.re * t) ≤ ‖kgFieldStateT W g h t‖
        ∧ ‖kgFieldStateT W g h t‖ ≤ M * Real.exp (μ.re * t) := by
  have hcont := continuous_kgFloquetPeriodicPart (W := W) hb0 hWb hWs g h μ
  have hp := periodic_kgFloquetPeriodicPart hb0 hWb hWs hper hμ g h heig
  have hpne : ∀ t : ℝ, kgFloquetPeriodicPart W g h μ t ≠ 0 := by
    intro t hzero
    refine hne t ?_
    rw [kgFieldStateT_eq_exp_smul μ g h t, hzero, smul_zero]
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_periodic hcont hp hT
  obtain ⟨m, hm0, hm⟩ := exists_pos_lower_bound_of_periodic hcont hp hT hpne
  refine ⟨m, M, hm0, hM0, fun t => ?_⟩
  rw [norm_kgFieldStateT_eq_exp_mul μ g h t, mul_comm m, mul_comm M]
  exact ⟨mul_le_mul_of_nonneg_left (hm t) (Real.exp_pos _).le,
    mul_le_mul_of_nonneg_left (hM t) (Real.exp_pos _).le⟩

end Envelope

/-! ## A weak static potential: a flat envelope -/

section StaticEnvelope

variable {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- **The state of a clock in a weak static real potential is bounded below at every instant.** -/
theorem norm_kgFieldStateT_ge_all_time (hb0 : 0 ≤ b) (hb1 : b < 1) (hW : ‖W₀‖ ≤ b)
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W₀ x) y : ℂ) = inner ℂ x (W₀ y))
    (hWb : ∀ r : ℝ, ‖(fun _ : ℝ => W₀) r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => (fun _ : ℝ => W₀) r x)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgPair E (g, h)‖ / Real.sqrt ((1 + b) / (1 - b))
      ≤ ‖kgFieldStateT (fun _ : ℝ => W₀) g h t‖ := by
  have hmain :=
    norm_kgFieldStateT_ge_of_small_potential (T := t) hb0 hb1 hW hsa hWb hWs g h 1
  have hcast : ((1 : ℕ) : ℝ) * t = t := by push_cast; ring
  rwa [hcast] at hmain

/-- The state of a clock in a weak static real potential never vanishes. -/
theorem kgFieldStateT_ne_zero_of_small_potential (hb0 : 0 ≤ b) (hb1 : b < 1) (hW : ‖W₀‖ ≤ b)
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W₀ x) y : ℂ) = inner ℂ x (W₀ y))
    (hWb : ∀ r : ℝ, ‖(fun _ : ℝ => W₀) r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => (fun _ : ℝ => W₀) r x)
    (g h : Lp ℂ 2 (volume : Measure E)) (hv : kgPair E (g, h) ≠ 0) (t : ℝ) :
    kgFieldStateT (fun _ : ℝ => W₀) g h t ≠ 0 := by
  have hb1' : (0 : ℝ) < 1 - b := by linarith
  have hK : 0 < Real.sqrt ((1 + b) / (1 - b)) := Real.sqrt_pos.mpr (by positivity)
  have hP : 0 < ‖kgPair E (g, h)‖ := norm_pos_iff.mpr hv
  have hge := norm_kgFieldStateT_ge_all_time hb0 hb1 hW hsa hWb hWs g h t
  have hpos : 0 < ‖kgFieldStateT (fun _ : ℝ => W₀) g h t‖ := lt_of_lt_of_le (by positivity) hge
  exact norm_pos_iff.mp hpos

/-- **An eigen-clock in a weak static real potential has a flat envelope**: its state norm is
confined between two positive constants at every real time, with no exponential factor at all. -/
theorem exists_flat_envelope_of_small_potential (hb0 : 0 ≤ b) (hb1 : b < 1) (hW : ‖W₀‖ ≤ b)
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W₀ x) y : ℂ) = inner ℂ x (W₀ y))
    (hWb : ∀ r : ℝ, ‖(fun _ : ℝ => W₀) r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => (fun _ : ℝ => W₀) r x)
    {T : ℝ} (hT : 0 < T) {k μ : ℂ} (hμ : Complex.exp (μ * (T : ℂ)) = k)
    (g h : Lp ℂ 2 (volume : Measure E)) (hv : kgPair E (g, h) ≠ 0)
    (heig : kgMonodromy (fun _ : ℝ => W₀) b hb0 hWb hWs T (kgPair E (g, h))
      = k • kgPair E (g, h)) :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧ ∀ t : ℝ,
      m ≤ ‖kgFieldStateT (fun _ : ℝ => W₀) g h t‖
        ∧ ‖kgFieldStateT (fun _ : ℝ => W₀) g h t‖ ≤ M := by
  have hone : ‖k‖ = 1 :=
    norm_floquet_multiplier_eq_one_of_small_potential hb0 hb1 hW hsa hWb hWs g h hv heig
  have hzero : μ.re = 0 := by
    have hnorm : Real.exp (μ.re * T) = 1 := by
      have hre : (μ * (T : ℂ)).re = μ.re * T := by simp [Complex.mul_re]
      rw [← hre, ← Complex.norm_exp, hμ, hone]
    have hmul : μ.re * T = 0 := (Real.exp_eq_one_iff (μ.re * T)).mp hnorm
    rcases mul_eq_zero.mp hmul with hcase | hcase
    · exact hcase
    · exact absurd hcase hT.ne'
  obtain ⟨m, M, hm0, hM0, hbd⟩ := exists_two_sided_envelope_of_eigen hb0 hWb hWs
    (periodic_const W₀ T) hT hμ g h heig
    (kgFieldStateT_ne_zero_of_small_potential hb0 hb1 hW hsa hWb hWs g h hv)
  refine ⟨m, M, hm0, hM0, fun t => ?_⟩
  have hb := hbd t
  rw [hzero, zero_mul, Real.exp_zero, mul_one, mul_one] at hb
  exact hb

end StaticEnvelope

end GaloisForLFunctions.HTGeometry
