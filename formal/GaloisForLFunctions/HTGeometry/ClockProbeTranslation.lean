import GaloisForLFunctions.HTGeometry.ClockThreeDimensionalProbe

/-!
# Moving the probe to an arbitrary event

The construction normalises the field at the origin of the null coordinates, so as it stands it
produces a probe at one event. Every other event is reached by translating, and translating costs
nothing: the datum of the construction is translation invariant, and a translated field is again
continuously differentiable with translated derivatives.

Both translations are of *functions*, not of spacetime: the potential is composed with a shift of
its null arguments, and so is the field. That avoids having to prove the translation invariance of
the chart d'Alembertian, which is not needed — the same lift, applied to the shifted field, already
solves the wave equation for the unshifted potential.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

/-- A potential with its null arguments shifted. -/
noncomputable def translatePotential (V : ℝ → ℝ → ℂ → ℂ) (ξ₀ η₀ : ℝ) : ℝ → ℝ → ℂ → ℂ :=
  fun s t z => V (s + ξ₀) (t + η₀) z

/-- A set of triples with its null coordinates shifted. -/
def translateSet (Ω : Set ((ℝ × ℝ) × ℝ)) (ξ₀ η₀ : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  {q | (((q.1.1 - ξ₀, q.1.2 - η₀) : ℝ × ℝ), q.2) ∈ Ω}

theorem continuous_translateMap (ξ₀ η₀ : ℝ) :
    Continuous fun q : (ℝ × ℝ) × ℝ => (((q.1.1 - ξ₀, q.1.2 - η₀) : ℝ × ℝ), q.2) :=
  (((continuous_fst.comp continuous_fst).sub continuous_const).prodMk
    ((continuous_snd.comp continuous_fst).sub continuous_const)).prodMk continuous_snd

theorem isOpen_translateSet {Ω : Set ((ℝ × ℝ) × ℝ)} (hΩ : IsOpen Ω) (ξ₀ η₀ : ℝ) :
    IsOpen (translateSet Ω ξ₀ η₀) :=
  hΩ.preimage (continuous_translateMap ξ₀ η₀)

theorem mem_translateSet {Ω : Set ((ℝ × ℝ) × ℝ)} {ξ₀ η₀ : ℝ} {q : (ℝ × ℝ) × ℝ} :
    q ∈ translateSet Ω ξ₀ η₀ ↔ (((q.1.1 - ξ₀, q.1.2 - η₀) : ℝ × ℝ), q.2) ∈ Ω := Iff.rfl

/-- **A translated field is continuously differentiable with translated derivatives.** -/
theorem IsC1On3.translate {u A B C : ℝ → ℝ → ℝ → ℝ} {Ω : Set ((ℝ × ℝ) × ℝ)}
    (h : IsC1On3 u A B C Ω) (ξ₀ η₀ : ℝ) :
    IsC1On3 (fun s t w => u (s - ξ₀) (t - η₀) w) (fun s t w => A (s - ξ₀) (t - η₀) w)
      (fun s t w => B (s - ξ₀) (t - η₀) w) (fun s t w => C (s - ξ₀) (t - η₀) w)
      (translateSet Ω ξ₀ η₀) where
  isOpen := isOpen_translateSet h.isOpen ξ₀ η₀
  hasDerivFst := by
    intro q hq
    have hbase := h.hasDerivFst (((q.1.1 - ξ₀, q.1.2 - η₀) : ℝ × ℝ), q.2) hq
    exact hbase.comp_sub_const q.1.1 ξ₀
  hasDerivSnd := by
    intro q hq
    have hbase := h.hasDerivSnd (((q.1.1 - ξ₀, q.1.2 - η₀) : ℝ × ℝ), q.2) hq
    exact hbase.comp_sub_const q.1.2 η₀
  hasDerivThd := by
    intro q hq
    exact h.hasDerivThd (((q.1.1 - ξ₀, q.1.2 - η₀) : ℝ × ℝ), q.2) hq
  contFst := h.contFst.comp (continuous_translateMap ξ₀ η₀)
  contSnd := h.contSnd.comp (continuous_translateMap ξ₀ η₀)
  contThd := h.contThd.comp (continuous_translateMap ξ₀ η₀)

/-! ## Translation invariance of the datum -/

theorem stripPotential_translate {V : ℝ → ℝ → ℂ → ℂ} {ρ : ℝ} (hV : StripPotential V ρ)
    (ξ₀ η₀ : ℝ) : StripPotential (translatePotential V ξ₀ η₀) ρ where
  cont := by
    intro q hq
    have hshift : Continuous fun q' : (ℝ × ℝ) × ℂ =>
        (((q'.1.1 + ξ₀, q'.1.2 + η₀) : ℝ × ℝ), q'.2) :=
      (((continuous_fst.comp continuous_fst).add continuous_const).prodMk
        ((continuous_snd.comp continuous_fst).add continuous_const)).prodMk continuous_snd
    have hbase := hV.cont.continuousAt
      (x := (((q.1.1 + ξ₀, q.1.2 + η₀) : ℝ × ℝ), q.2))
      ((isOpen_univ.prod (isOpen_imStrip ρ)).mem_nhds ⟨mem_univ _, hq.2⟩)
    exact (hbase.comp (x := q)
      (f := fun q' : (ℝ × ℝ) × ℂ => (((q'.1.1 + ξ₀, q'.1.2 + η₀) : ℝ × ℝ), q'.2))
      hshift.continuousAt).continuousWithinAt
  holo := fun s t => hV.holo (s + ξ₀) (t + η₀)

theorem stripPotentialC1_translate {V Vs Vt : ℝ → ℝ → ℂ → ℂ} {ρ : ℝ}
    (hV : StripPotentialC1 V Vs Vt ρ) (ξ₀ η₀ : ℝ) :
    StripPotentialC1 (translatePotential V ξ₀ η₀) (translatePotential Vs ξ₀ η₀)
      (translatePotential Vt ξ₀ η₀) ρ where
  base := stripPotential_translate hV.base ξ₀ η₀
  hasDerivFst := by
    intro s t z hz
    have hbase := hV.hasDerivFst (s + ξ₀) (t + η₀) z hz
    exact hbase.comp_add_const s ξ₀
  hasDerivSnd := by
    intro s t z hz
    have hbase := hV.hasDerivSnd (s + ξ₀) (t + η₀) z hz
    exact hbase.comp_add_const t η₀
  contFst := by
    intro q hq
    have hshift : Continuous fun q' : (ℝ × ℝ) × ℂ =>
        (((q'.1.1 + ξ₀, q'.1.2 + η₀) : ℝ × ℝ), q'.2) :=
      (((continuous_fst.comp continuous_fst).add continuous_const).prodMk
        ((continuous_snd.comp continuous_fst).add continuous_const)).prodMk continuous_snd
    have hbase := hV.contFst.continuousAt
      (x := (((q.1.1 + ξ₀, q.1.2 + η₀) : ℝ × ℝ), q.2))
      ((isOpen_univ.prod (isOpen_imStrip ρ)).mem_nhds ⟨mem_univ _, hq.2⟩)
    exact (hbase.comp (x := q)
      (f := fun q' : (ℝ × ℝ) × ℂ => (((q'.1.1 + ξ₀, q'.1.2 + η₀) : ℝ × ℝ), q'.2))
      hshift.continuousAt).continuousWithinAt
  contSnd := by
    intro q hq
    have hshift : Continuous fun q' : (ℝ × ℝ) × ℂ =>
        (((q'.1.1 + ξ₀, q'.1.2 + η₀) : ℝ × ℝ), q'.2) :=
      (((continuous_fst.comp continuous_fst).add continuous_const).prodMk
        ((continuous_snd.comp continuous_fst).add continuous_const)).prodMk continuous_snd
    have hbase := hV.contSnd.continuousAt
      (x := (((q.1.1 + ξ₀, q.1.2 + η₀) : ℝ × ℝ), q.2))
      ((isOpen_univ.prod (isOpen_imStrip ρ)).mem_nhds ⟨mem_univ _, hq.2⟩)
    exact (hbase.comp (x := q)
      (f := fun q' : (ℝ × ℝ) × ℂ => (((q'.1.1 + ξ₀, q'.1.2 + η₀) : ℝ × ℝ), q'.2))
      hshift.continuousAt).continuousWithinAt

theorem ClockDatum.translate {V Vs Vt : ℝ → ℝ → ℂ → ℂ} {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ}
    (hD : ClockDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T) (ξ₀ η₀ : ℝ)
    (hmass : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀,
      ‖V (s + ξ₀) (t + η₀) z‖ ≤ Mv) :
    ClockDatum (translatePotential V ξ₀ η₀) (translatePotential Vs ξ₀ η₀)
      (translatePotential Vt ξ₀ η₀) ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T where
  pos := hD.pos
  potC1 := stripPotentialC1_translate hD.potC1 ξ₀ η₀
  massNonneg := hD.massNonneg
  mass := hmass
  radNonneg := hD.radNonneg
  rad := hD.rad
  sideNonneg := hD.sideNonneg
  small := hD.small
  rad₁Nonneg := hD.rad₁Nonneg
  rad₁ := hD.rad₁
  rad₂Nonneg := hD.rad₂Nonneg
  rad₂ := hD.rad₂
  rad₃Pos := hD.rad₃Pos
  rad₃ := hD.rad₃

/-- **Clock probes at an arbitrary event, for potentials with coupled transverse dependence.** On
Minkowski space of dimension `n + 3`, a potential continuously differentiable in the two null
coordinates, holomorphic and bounded on a strip about the real transverse axis and real there admits
a clock probe on an open neighbourhood of any prescribed event, normalised to `1` there and
nonvanishing on that neighbourhood. -/
theorem ClockDatum.exists_clockProbe_nullTransverse_at {V Vs Vt : ℝ → ℝ → ℂ → ℂ}
    {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hD : ClockDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T)
    (hVreal : ∀ s t w : ℝ, (V s t ((w : ℝ) : ℂ)).im = 0) (hT : 0 < T) (n : ℕ)
    (x : Fin (n + 3) → ℝ)
    (hmass : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀,
      ‖V (s + (x 0 + x 1)) (t + (x 0 - x 1)) z‖ ≤ Mv) :
    ∃ W : Set (Fin (n + 3) → ℝ), IsOpen W ∧ x ∈ W ∧ ∃ U : (Fin (n + 3) → ℝ) → ℝ,
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
            (slabEps_ne_zero (n + 1))).chart.dalembert
          (nullTransLift (fun s t w => (V s t ((w : ℝ) : ℂ)).re) n) U W ∧
        (∀ y ∈ W, U y ≠ 0) ∧ U x = 1 := by
  classical
  set ξ₀ : ℝ := x 0 + x 1 with hξ₀
  set η₀ : ℝ := x 0 - x 1 with hη₀
  have hD' := hD.translate ξ₀ η₀ hmass
  have hVreal' : ∀ s t w : ℝ, (translatePotential V ξ₀ η₀ s t ((w : ℝ) : ℂ)).im = 0 :=
    fun s t w => hVreal (s + ξ₀) (t + η₀) w
  set u₀ : ℝ → ℝ → ℝ → ℝ :=
    fun s t w => probeU (translatePotential V ξ₀ η₀) T (s - ξ₀) (t - η₀) w with hu₀
  have hUcont : Continuous (nullTransLift u₀ n) := by
    rw [nullTransLift_eq_comp]
    exact (hD'.continuous_probeU.comp (continuous_translateMap ξ₀ η₀)).comp
      (nullTransCLM n).continuous
  have hnull : nullTransCLM n x = ((ξ₀, η₀), x 2) := rfl
  have hT0 : |(0 : ℝ)| < T := by simpa using hT
  have hxbox : x ∈ nullTransBox (translateSet (clockBox T) ξ₀ η₀) n := by
    rw [mem_nullTransBox, hnull]
    refine ⟨?_, ?_⟩ <;> simpa using hT
  have hone : nullTransLift u₀ n x = 1 := by
    show probeU (translatePotential V ξ₀ η₀) T (ξ₀ - ξ₀) (η₀ - η₀) (x 2) = 1
    rw [sub_self, sub_self, probeU,
      boxClamp_eq_self (le_of_lt hT0),
      clockSolution_zero_zero hD'.pos hD'.pot hD'.massNonneg hD'.mass hD'.radNonneg hD'.rad
        hD'.sideNonneg hD'.small (hD'.absIm (x 2))]
    norm_num
  refine ⟨nullTransBox (translateSet (clockBox T) ξ₀ η₀) n ∩ {y | nullTransLift u₀ n y ≠ 0},
    (isOpen_nullTransBox (isOpen_translateSet (isOpen_clockBox T) ξ₀ η₀) n).inter
      (isOpen_ne.preimage hUcont),
    ⟨hxbox, by rw [Set.mem_setOf_eq, hone]; exact one_ne_zero⟩, nullTransLift u₀ n,
    ?_, fun y hy => hy.2, hone⟩
  refine solvesPotentialWaveOn_nullTransLift (hD'.isC1On3_probeU.translate ξ₀ η₀)
    (hD'.isC1On3_probeA.translate ξ₀ η₀) (hD'.isC1On3_probeB.translate ξ₀ η₀)
    (hD'.isC1On3_probeC.translate ξ₀ η₀) (fun y hy => hy.1) fun y hy => ?_
  have hybox : nullTransCLM n y ∈ translateSet (clockBox T) ξ₀ η₀ := hy.1
  have hs : |y 0 + y 1 - ξ₀| < T := hybox.1
  have ht : |y 0 - y 1 - η₀| < T := hybox.2
  have hchar := probe_characteristic (V := translatePotential V ξ₀ η₀) (T := T) hVreal'
    hs ht (w := y 2)
  have hVeq : translatePotential V ξ₀ η₀ (y 0 + y 1 - ξ₀) (y 0 - y 1 - η₀) (((y 2 : ℝ)) : ℂ)
      = V (y 0 + y 1) (y 0 - y 1) (((y 2 : ℝ)) : ℂ) := by
    rw [translatePotential, sub_add_cancel, sub_add_cancel]
  rw [hVeq] at hchar
  exact hchar

end GaloisForLFunctions.HTGeometry
