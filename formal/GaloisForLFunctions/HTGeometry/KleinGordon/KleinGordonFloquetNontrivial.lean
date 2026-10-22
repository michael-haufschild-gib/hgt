import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonMonodromyLipschitz

/-!
# The multipliers exist, and the free clock sits on the boundary

Everything said about Floquet multipliers is empty until the spectrum is known to be inhabited, and
that needs the energy space to be nontrivial. It is: the indicator of a ball is a nonzero element of
`L²`, so the energy space and the algebra of operators on it are nontrivial, and every element of a
nontrivial complex Banach algebra has nonempty spectrum. **Every monodromy therefore has at least one
Floquet multiplier.**

With nontriviality the free clock can also be located exactly. Its monodromy is an isometry, so every
power has norm exactly one, and Gelfand's formula gives `spectralRadius M₀ = 1`: the free field sits
precisely on the boundary of the trichotomy — stable, but not decaying, at every period.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology Metric ENNReal

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## Nontriviality -/

/-- **The `L²` space of a finite-dimensional inner product space is nontrivial**: the indicator of
the unit ball is a nonzero element. -/
instance kgLp_nontrivial : Nontrivial (Lp ℂ 2 (volume : Measure E)) :=
  ⟨⟨kgBallFun 0 1, 0, kgBallFun_ne_zero 0 one_pos⟩⟩

/-- The energy space is nontrivial. -/
instance kgEnergy_nontrivial : Nontrivial (KGEnergy E) := by
  refine ⟨⟨kgPair E (kgBallFun (0 : E) 1, 0), 0, ?_⟩⟩
  intro hzero
  have hfst : kgBallFun (0 : E) 1 = (0 : Lp ℂ 2 (volume : Measure E)) := by
    have h := congrArg (kgFst E) hzero
    rw [map_zero] at h
    exact h
  exact kgBallFun_ne_zero 0 one_pos hfst

/-- The identity of the energy space has norm exactly one. -/
theorem norm_one_kgEnergy : ‖(1 : KGEnergy E →L[ℂ] KGEnergy E)‖ = 1 :=
  ContinuousLinearMap.norm_id

section Nonempty

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- **Every monodromy has at least one Floquet multiplier.** -/
theorem spectrum_kgMonodromy_nonempty (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) :
    (spectrum ℂ (kgMonodromy W b hb0 hWb hWs T)).Nonempty :=
  spectrum.nonempty _

/-- **The spectral radius of a monodromy is attained by a multiplier.** -/
theorem exists_multiplier_eq_spectralRadius (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) :
    ∃ k ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T),
      (‖k‖₊ : ℝ≥0∞) = spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T) :=
  spectrum.exists_nnnorm_eq_spectralRadius _

end Nonempty

/-! ## The free clock sits on the boundary -/

section Free

variable {T : ℝ}

/-- Every power of the free monodromy is an isometry. -/
theorem norm_kgMonodromy_zero_pow_apply (hb0 : (0 : ℝ) ≤ 0)
    (hWb : ∀ r : ℝ, ‖(fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
      Lp ℂ 2 (volume : Measure E))) r‖ ≤ 0)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
        Lp ℂ 2 (volume : Measure E))) r x) (n : ℕ) (v : KGEnergy E) :
    ‖(kgMonodromy (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
      Lp ℂ 2 (volume : Measure E))) 0 hb0 hWb hWs T ^ n) v‖ = ‖v‖ := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      have hstep : (kgMonodromy (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
            Lp ℂ 2 (volume : Measure E))) 0 hb0 hWb hWs T ^ (n + 1)) v
          = (kgMonodromy (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
              Lp ℂ 2 (volume : Measure E))) 0 hb0 hWb hWs T ^ n)
            (kgMonodromy (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
              Lp ℂ 2 (volume : Measure E))) 0 hb0 hWb hWs T v) := by
        rw [pow_succ]
        rfl
      rw [hstep, ih, kgMonodromy_apply]
      exact norm_kgMonodromy_zero_apply T v

/-- **Every power of the free monodromy has norm exactly one.** -/
theorem norm_kgMonodromy_zero_pow (hb0 : (0 : ℝ) ≤ 0)
    (hWb : ∀ r : ℝ, ‖(fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
      Lp ℂ 2 (volume : Measure E))) r‖ ≤ 0)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
        Lp ℂ 2 (volume : Measure E))) r x) (n : ℕ) :
    ‖kgMonodromy (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
      Lp ℂ 2 (volume : Measure E))) 0 hb0 hWb hWs T ^ n‖ = 1 := by
  set M := kgMonodromy (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
    Lp ℂ 2 (volume : Measure E))) 0 hb0 hWb hWs T with hM
  have hiso : ∀ v : KGEnergy E, ‖(M ^ n) v‖ = ‖v‖ :=
    norm_kgMonodromy_zero_pow_apply hb0 hWb hWs n
  have hle : ‖M ^ n‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      rw [one_mul]
      exact le_of_eq (hiso v)
  set v₀ : KGEnergy E := kgPair E (kgBallFun (0 : E) 1, 0) with hv₀
  have hv₀ne : v₀ ≠ 0 := by
    rw [hv₀]
    intro hzero
    have hfst : kgBallFun (0 : E) 1 = (0 : Lp ℂ 2 (volume : Measure E)) := by
      have h := congrArg (kgFst E) hzero
      rw [map_zero] at h
      exact h
    exact kgBallFun_ne_zero 0 one_pos hfst
  have hv₀pos : 0 < ‖v₀‖ := norm_pos_iff.mpr hv₀ne
  have hge : 1 ≤ ‖M ^ n‖ := by
    have hb := (M ^ n).le_opNorm v₀
    rw [hiso v₀] at hb
    nlinarith [hb, hv₀pos]
  exact le_antisymm hle hge

/-- **The free clock sits exactly on the boundary of the trichotomy.** Its spectral radius is one:
it neither decays nor breaks. -/
theorem spectralRadius_kgMonodromy_zero (hb0 : (0 : ℝ) ≤ 0)
    (hWb : ∀ r : ℝ, ‖(fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
      Lp ℂ 2 (volume : Measure E))) r‖ ≤ 0)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
        Lp ℂ 2 (volume : Measure E))) r x) :
    spectralRadius ℂ (kgMonodromy (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
      Lp ℂ 2 (volume : Measure E))) 0 hb0 hWb hWs T) = 1 := by
  set M := kgMonodromy (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
    Lp ℂ 2 (volume : Measure E))) 0 hb0 hWb hWs T with hM
  have hgel := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius M
  have hconst : ∀ᶠ n : ℕ in atTop, (1 : ℝ≥0∞) = ENNReal.ofReal (‖M ^ n‖ ^ (1 / n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n _
    rw [hM, norm_kgMonodromy_zero_pow hb0 hWb hWs n, Real.one_rpow, ENNReal.ofReal_one]
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (‖M ^ n‖ ^ (1 / n : ℝ))) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' hconst
  exact (tendsto_nhds_unique hgel hlim)

end Free

end GaloisForLFunctions.HTGeometry
