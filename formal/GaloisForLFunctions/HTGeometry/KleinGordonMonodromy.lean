import GaloisForLFunctions.HTGeometry.KleinGordonFloquet

/-!
# The monodromy operator

The period map of the previous file is a map of sets. It is in fact linear and bounded, because the
state solves a Volterra equation in the energy space whose free term is linear in the datum and whose
kernel is linear in the state: superposing two solutions solves the superposed equation, and
uniqueness identifies it with the solution of the superposed datum.

So a periodically driven field carries a **monodromy operator** `M` on the energy space, of norm at
most `e^{b|T|}`, and the state after `n` periods is `Mⁿ` applied to the datum. The whole long-time
behaviour of a periodically driven clock is the behaviour of the powers of one bounded operator.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The energy space, componentwise -/

theorem kgEnergy_fst_add (v w : KGEnergy E) : (v + w).fst = v.fst + w.fst := rfl

theorem kgEnergy_snd_add (v w : KGEnergy E) : (v + w).snd = v.snd + w.snd := rfl

theorem kgEnergy_fst_smul (a : ℂ) (v : KGEnergy E) : (a • v).fst = a • v.fst := rfl

theorem kgEnergy_snd_smul (a : ℂ) (v : KGEnergy E) : (a • v).snd = a • v.snd := rfl

/-! ## The state is linear in the datum -/

section StateLinear

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

theorem kgStateFree_linear (a c : ℂ) (g₁ h₁ g₂ h₂ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgStateFree (E := E) (a • g₁ + c • g₂) (a • h₁ + c • h₂) t
      = a • kgStateFree g₁ h₁ t + c • kgStateFree g₂ h₂ t := by
  have hpair : kgPair E (a • g₁ + c • g₂, a • h₁ + c • h₂)
      = a • kgPair E (g₁, h₁) + c • kgPair E (g₂, h₂) := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
  rw [kgStateFree, kgStateFree, kgStateFree, hpair, map_add, map_smul, map_smul]

theorem kgStateKernelT_linear (t s : ℝ) (a c : ℂ) (v w : KGEnergy E) :
    kgStateKernelT W t s (a • v + c • w)
      = a • kgStateKernelT W t s v + c • kgStateKernelT W t s w := by
  rw [kgStateKernelT_apply, kgStateKernelT_apply, kgStateKernelT_apply, map_add, map_smul,
    map_smul, map_add, map_smul, map_smul]

set_option maxHeartbeats 1000000 in
/-- **The state is linear in the Cauchy datum.** -/
theorem kgStateMildT_linear (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (a c : ℂ) (g₁ h₁ g₂ h₂ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgStateMildT W (a • g₁ + c • g₂) (a • h₁ + c • h₂) t
      = a • kgStateMildT W g₁ h₁ t + c • kgStateMildT W g₂ h₂ t := by
  have hc1 := continuous_kgStateMildT hb0 hWb hWs g₁ h₁
  have hc2 := continuous_kgStateMildT hb0 hWb hWs g₂ h₂
  have hcand : Continuous fun τ : ℝ =>
      a • kgStateMildT W g₁ h₁ τ + c • kgStateMildT W g₂ h₂ τ :=
    ((continuous_const_smul a).comp hc1).add ((continuous_const_smul c).comp hc2)
  have hI1 : ∀ τ : ℝ, IntervalIntegrable
      (fun s : ℝ => kgStateKernelT W τ s (kgStateMildT W g₁ h₁ s)) volume 0 τ := fun τ =>
    (((strongKernel_kgStateKernelT hWb hWs) _ hc1).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 τ
  have hI2 : ∀ τ : ℝ, IntervalIntegrable
      (fun s : ℝ => kgStateKernelT W τ s (kgStateMildT W g₂ h₂ s)) volume 0 τ := fun τ =>
    (((strongKernel_kgStateKernelT hWb hWs) _ hc2).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 τ
  have hduh : ∀ τ : ℝ, a • kgStateMildT W g₁ h₁ τ + c • kgStateMildT W g₂ h₂ τ
      = kgStateFree (a • g₁ + c • g₂) (a • h₁ + c • h₂) τ
        + ∫ s in (0 : ℝ)..τ, kgStateKernelT W τ s
            (a • kgStateMildT W g₁ h₁ s + c • kgStateMildT W g₂ h₂ s) := by
    intro τ
    have hpt : ∀ s ∈ Set.uIcc (0 : ℝ) τ, kgStateKernelT W τ s
        (a • kgStateMildT W g₁ h₁ s + c • kgStateMildT W g₂ h₂ s)
        = a • kgStateKernelT W τ s (kgStateMildT W g₁ h₁ s)
          + c • kgStateKernelT W τ s (kgStateMildT W g₂ h₂ s) := fun s _ =>
      kgStateKernelT_linear τ s a c _ _
    have hint : (∫ s in (0 : ℝ)..τ, kgStateKernelT W τ s
          (a • kgStateMildT W g₁ h₁ s + c • kgStateMildT W g₂ h₂ s))
        = a • (∫ s in (0 : ℝ)..τ, kgStateKernelT W τ s (kgStateMildT W g₁ h₁ s))
          + c • ∫ s in (0 : ℝ)..τ, kgStateKernelT W τ s (kgStateMildT W g₂ h₂ s) := by
      have hIa : IntervalIntegrable
          (fun s : ℝ => a • kgStateKernelT W τ s (kgStateMildT W g₁ h₁ s)) volume 0 τ :=
        (hI1 τ).smul a
      have hIc : IntervalIntegrable
          (fun s : ℝ => c • kgStateKernelT W τ s (kgStateMildT W g₂ h₂ s)) volume 0 τ :=
        (hI2 τ).smul c
      rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add hIa hIc,
        intervalIntegral.integral_smul, intervalIntegral.integral_smul]
    rw [hint, kgStateFree_linear, kgStateMildT_eq hb0 hWb hWs g₁ h₁ τ,
      kgStateMildT_eq hb0 hWb hWs g₂ h₂ τ, smul_add, smul_add]
    abel
  have hfin := eq_kgStateMildT_of_duhamel hb0 hWb hWs (a • g₁ + c • g₂) (a • h₁ + c • h₂)
    hcand hduh
  exact (congrFun hfin t).symm

end StateLinear

/-! ## The monodromy operator -/

section Monodromy

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- The period map, as a linear map on the energy space. -/
def kgPeriodLM (W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)))
    (b : ℝ) (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) (T : ℝ) :
    KGEnergy E →ₗ[ℂ] KGEnergy E where
  toFun v := kgFieldStateT W v.fst v.snd T
  map_add' v w := by
    rw [kgFieldStateT_eq_kgStateMildT hb0 hWb hWs, kgFieldStateT_eq_kgStateMildT hb0 hWb hWs,
      kgFieldStateT_eq_kgStateMildT hb0 hWb hWs, kgEnergy_fst_add, kgEnergy_snd_add]
    have h := kgStateMildT_linear hb0 hWb hWs 1 1 v.fst v.snd w.fst w.snd T
    simpa using h
  map_smul' a v := by
    rw [kgFieldStateT_eq_kgStateMildT hb0 hWb hWs, kgFieldStateT_eq_kgStateMildT hb0 hWb hWs,
      kgEnergy_fst_smul, kgEnergy_snd_smul]
    have h := kgStateMildT_linear hb0 hWb hWs a 0 v.fst v.snd v.fst v.snd T
    simpa using h

/-- **The monodromy operator** of a periodically driven field. -/
def kgMonodromy (W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)))
    (b : ℝ) (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) (T : ℝ) :
    KGEnergy E →L[ℂ] KGEnergy E :=
  LinearMap.mkContinuous (kgPeriodLM W b hb0 hWb hWs T) (Real.exp (b * |T|)) (by
    intro v
    have hle := norm_kgPeriodMap_le (W := W) (T := T) hb0 hWb hWs v
    rw [kgPeriodMap] at hle
    rw [mul_comm]
    exact hle)

theorem kgMonodromy_apply (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) (v : KGEnergy E) :
    kgMonodromy W b hb0 hWb hWs T v = kgPeriodMap W T v := rfl

theorem norm_kgMonodromy_le (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) :
    ‖kgMonodromy W b hb0 hWb hWs T‖ ≤ Real.exp (b * |T|) :=
  LinearMap.mkContinuous_norm_le _ (Real.exp_pos _).le _

/-- The powers of the monodromy are the iterates of the period map. -/
theorem kgMonodromy_pow_apply (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) (n : ℕ)
    (v : KGEnergy E) :
    (kgMonodromy W b hb0 hWb hWs T ^ n) v = (kgPeriodMap W T)^[n] v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Function.iterate_succ_apply]
      have hmul : (kgMonodromy W b hb0 hWb hWs T ^ n * kgMonodromy W b hb0 hWb hWs T) v
          = (kgMonodromy W b hb0 hWb hWs T ^ n) (kgMonodromy W b hb0 hWb hWs T v) := rfl
      rw [hmul, kgMonodromy_apply, ih]

/-- **The state after `n` periods is the `n`-th power of the monodromy applied to the datum.** -/
theorem kgFieldStateT_monodromy_pow (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (g h : Lp ℂ 2 (volume : Measure E)) (n : ℕ) :
    kgFieldStateT W g h (n * T)
      = (kgMonodromy W b hb0 hWb hWs T ^ n) (kgPair E (g, h)) := by
  rw [kgMonodromy_pow_apply hb0 hWb hWs n]
  exact kgFieldStateT_iterate hb0 hWb hWs hper g h n

/-- **Stability from the monodromy alone.** If the powers of the monodromy are bounded, the state is
bounded at every multiple of the period, with no exponential growth. -/
theorem norm_kgFieldStateT_le_of_pow_bound (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) {C : ℝ}
    (hC : ∀ n : ℕ, ‖kgMonodromy W b hb0 hWb hWs T ^ n‖ ≤ C)
    (g h : Lp ℂ 2 (volume : Measure E)) (n : ℕ) :
    ‖kgFieldStateT W g h (n * T)‖ ≤ C * ‖kgPair E (g, h)‖ := by
  rw [kgFieldStateT_monodromy_pow hb0 hWb hWs hper g h n]
  exact (kgMonodromy W b hb0 hWb hWs T ^ n).le_of_opNorm_le (hC n) _

end Monodromy

end GaloisForLFunctions.HTGeometry
