import GaloisForLFunctions.HTGeometry.ClockMultiDimensionalProbe

/-!
# Moving the several-variable probe to an arbitrary event

The construction normalises the field at the origin of the null coordinates, so as it stands it
produces a probe at one event. Every other event is reached by translating, and translating costs
nothing: the datum of the construction is translation invariant, and a translated field is again
continuously differentiable with translated derivatives.

Both translations are of *functions*, not of spacetime: the potential is composed with a shift of its
null arguments, and so is the field. That avoids having to prove the translation invariance of the
chart d'Alembertian, which is not needed — the same lift, applied to the shifted field, already
solves the wave equation for the unshifted potential.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

variable {k : ℕ}

/-- A potential on a tube with its null arguments shifted. -/
noncomputable def translateTubePotential (V : ℝ → ℝ → (Fin k → ℂ) → ℂ) (ξ₀ η₀ : ℝ) :
    ℝ → ℝ → (Fin k → ℂ) → ℂ :=
  fun s t z => V (s + ξ₀) (t + η₀) z

/-- A set of null-and-transverse data with its null coordinates shifted. -/
def translateSetMulti (Ω : Set ((ℝ × ℝ) × (Fin k → ℝ))) (ξ₀ η₀ : ℝ) :
    Set ((ℝ × ℝ) × (Fin k → ℝ)) :=
  {q | (((q.1.1 - ξ₀, q.1.2 - η₀) : ℝ × ℝ), q.2) ∈ Ω}

theorem continuous_translateMapMulti (ξ₀ η₀ : ℝ) :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) =>
      (((q.1.1 - ξ₀, q.1.2 - η₀) : ℝ × ℝ), q.2) :=
  (((continuous_fst.comp continuous_fst).sub continuous_const).prodMk
    ((continuous_snd.comp continuous_fst).sub continuous_const)).prodMk continuous_snd

theorem isOpen_translateSetMulti {Ω : Set ((ℝ × ℝ) × (Fin k → ℝ))} (hΩ : IsOpen Ω) (ξ₀ η₀ : ℝ) :
    IsOpen (translateSetMulti Ω ξ₀ η₀) :=
  hΩ.preimage (continuous_translateMapMulti ξ₀ η₀)

theorem mem_translateSetMulti {Ω : Set ((ℝ × ℝ) × (Fin k → ℝ))} {ξ₀ η₀ : ℝ}
    {q : (ℝ × ℝ) × (Fin k → ℝ)} :
    q ∈ translateSetMulti Ω ξ₀ η₀ ↔ (((q.1.1 - ξ₀, q.1.2 - η₀) : ℝ × ℝ), q.2) ∈ Ω := Iff.rfl

/-- **A translated field is continuously differentiable with translated derivatives.** -/
theorem IsC1OnMulti.translate {u A B : ℝ → ℝ → (Fin k → ℝ) → ℝ}
    {C : Fin k → ℝ → ℝ → (Fin k → ℝ) → ℝ} {Ω : Set ((ℝ × ℝ) × (Fin k → ℝ))}
    (h : IsC1OnMulti u A B C Ω) (ξ₀ η₀ : ℝ) :
    IsC1OnMulti (fun s t y => u (s - ξ₀) (t - η₀) y) (fun s t y => A (s - ξ₀) (t - η₀) y)
      (fun s t y => B (s - ξ₀) (t - η₀) y) (fun i s t y => C i (s - ξ₀) (t - η₀) y)
      (translateSetMulti Ω ξ₀ η₀) where
  isOpen := isOpen_translateSetMulti h.isOpen ξ₀ η₀
  hasDerivFst := by
    intro q hq
    have hbase := h.hasDerivFst (((q.1.1 - ξ₀, q.1.2 - η₀) : ℝ × ℝ), q.2) hq
    exact hbase.comp_sub_const q.1.1 ξ₀
  hasDerivSnd := by
    intro q hq
    have hbase := h.hasDerivSnd (((q.1.1 - ξ₀, q.1.2 - η₀) : ℝ × ℝ), q.2) hq
    exact hbase.comp_sub_const q.1.2 η₀
  hasDerivTrans := by
    intro q hq i
    exact h.hasDerivTrans (((q.1.1 - ξ₀, q.1.2 - η₀) : ℝ × ℝ), q.2) hq i
  contFst := h.contFst.comp (continuous_translateMapMulti ξ₀ η₀)
  contSnd := h.contSnd.comp (continuous_translateMapMulti ξ₀ η₀)
  contTrans := fun i => (h.contTrans i).comp (continuous_translateMapMulti ξ₀ η₀)

/-! ## Translation invariance of the datum -/

theorem tubePotential_translate {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} {ρ : ℝ} (hV : TubePotential V ρ)
    (ξ₀ η₀ : ℝ) : TubePotential (translateTubePotential V ξ₀ η₀) ρ where
  cont := by
    intro q hq
    have hshift : Continuous fun q' : (ℝ × ℝ) × (Fin k → ℂ) =>
        (((q'.1.1 + ξ₀, q'.1.2 + η₀) : ℝ × ℝ), q'.2) :=
      (((continuous_fst.comp continuous_fst).add continuous_const).prodMk
        ((continuous_snd.comp continuous_fst).add continuous_const)).prodMk continuous_snd
    have hbase := hV.cont.continuousAt
      (x := (((q.1.1 + ξ₀, q.1.2 + η₀) : ℝ × ℝ), q.2))
      ((isOpen_univ.prod (isOpen_tube k ρ)).mem_nhds ⟨mem_univ _, hq.2⟩)
    exact (hbase.comp (x := q)
      (f := fun q' : (ℝ × ℝ) × (Fin k → ℂ) => (((q'.1.1 + ξ₀, q'.1.2 + η₀) : ℝ × ℝ), q'.2))
      hshift.continuousAt).continuousWithinAt
  holo := fun s t => hV.holo (s + ξ₀) (t + η₀)

theorem tubePotentialC1_translate {V Vs Vt : ℝ → ℝ → (Fin k → ℂ) → ℂ} {ρ : ℝ}
    (hV : TubePotentialC1 V Vs Vt ρ) (ξ₀ η₀ : ℝ) :
    TubePotentialC1 (translateTubePotential V ξ₀ η₀) (translateTubePotential Vs ξ₀ η₀)
      (translateTubePotential Vt ξ₀ η₀) ρ where
  base := tubePotential_translate hV.base ξ₀ η₀
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
    have hshift : Continuous fun q' : (ℝ × ℝ) × (Fin k → ℂ) =>
        (((q'.1.1 + ξ₀, q'.1.2 + η₀) : ℝ × ℝ), q'.2) :=
      (((continuous_fst.comp continuous_fst).add continuous_const).prodMk
        ((continuous_snd.comp continuous_fst).add continuous_const)).prodMk continuous_snd
    have hbase := hV.contFst.continuousAt
      (x := (((q.1.1 + ξ₀, q.1.2 + η₀) : ℝ × ℝ), q.2))
      ((isOpen_univ.prod (isOpen_tube k ρ)).mem_nhds ⟨mem_univ _, hq.2⟩)
    exact (hbase.comp (x := q)
      (f := fun q' : (ℝ × ℝ) × (Fin k → ℂ) => (((q'.1.1 + ξ₀, q'.1.2 + η₀) : ℝ × ℝ), q'.2))
      hshift.continuousAt).continuousWithinAt
  contSnd := by
    intro q hq
    have hshift : Continuous fun q' : (ℝ × ℝ) × (Fin k → ℂ) =>
        (((q'.1.1 + ξ₀, q'.1.2 + η₀) : ℝ × ℝ), q'.2) :=
      (((continuous_fst.comp continuous_fst).add continuous_const).prodMk
        ((continuous_snd.comp continuous_fst).add continuous_const)).prodMk continuous_snd
    have hbase := hV.contSnd.continuousAt
      (x := (((q.1.1 + ξ₀, q.1.2 + η₀) : ℝ × ℝ), q.2))
      ((isOpen_univ.prod (isOpen_tube k ρ)).mem_nhds ⟨mem_univ _, hq.2⟩)
    exact (hbase.comp (x := q)
      (f := fun q' : (ℝ × ℝ) × (Fin k → ℂ) => (((q'.1.1 + ξ₀, q'.1.2 + η₀) : ℝ × ℝ), q'.2))
      hshift.continuousAt).continuousWithinAt

theorem TubeDatum.translate {V Vs Vt : ℝ → ℝ → (Fin k → ℂ) → ℂ} {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ}
    (hD : TubeDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T) (ξ₀ η₀ : ℝ)
    (hmass : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀,
      ‖V (s + ξ₀) (t + η₀) z‖ ≤ Mv) :
    TubeDatum (translateTubePotential V ξ₀ η₀) (translateTubePotential Vs ξ₀ η₀)
      (translateTubePotential Vt ξ₀ η₀) ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T where
  pos := hD.pos
  potC1 := tubePotentialC1_translate hD.potC1 ξ₀ η₀
  massNonneg := hD.massNonneg
  mass := hmass
  radNonneg := hD.radNonneg
  rad := hD.rad
  sideNonneg := hD.sideNonneg
  small := hD.small
  rad₁Pos := hD.rad₁Pos
  rad₁ := hD.rad₁
  rad₂Pos := hD.rad₂Pos
  rad₂ := hD.rad₂
  rad₃Pos := hD.rad₃Pos
  rad₃ := hD.rad₃

/-- **Clock probes at an arbitrary event, for potentials coupling several transverse
coordinates.** On Minkowski space of dimension `k + n + 2`, a potential continuously differentiable
in the two null coordinates, slice holomorphic and bounded on a tube about the real transverse points
and real there admits a clock probe on an open neighbourhood of any prescribed event, normalised to
`1` there and nonvanishing on that neighbourhood. -/
theorem TubeDatum.exists_clockProbe_nullMulti_at {V Vs Vt : ℝ → ℝ → (Fin k → ℂ) → ℂ}
    {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hD : TubeDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T)
    (hVreal : ∀ (s t : ℝ) (y : Fin k → ℝ), (V s t (realTube y)).im = 0) (hT : 0 < T) (n : ℕ)
    (x : Fin (k + n + 2) → ℝ)
    (hmass : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀,
      ‖V (s + (x 0 + x 1)) (t + (x 0 - x 1)) z‖ ≤ Mv) :
    ∃ W : Set (Fin (k + n + 2) → ℝ), IsOpen W ∧ x ∈ W ∧ ∃ U : (Fin (k + n + 2) → ℝ) → ℝ,
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (k + n))
            (slabEps_ne_zero (k + n))).chart.dalembert
          (nullMultiLift (fun s t y => (V s t (realTube y)).re) n) U W ∧
        (∀ y ∈ W, U y ≠ 0) ∧ U x = 1 := by
  classical
  set ξ₀ : ℝ := x 0 + x 1 with hξ₀
  set η₀ : ℝ := x 0 - x 1 with hη₀
  have hD' := hD.translate ξ₀ η₀ hmass
  have hVreal' : ∀ (s t : ℝ) (y : Fin k → ℝ),
      (translateTubePotential V ξ₀ η₀ s t (realTube y)).im = 0 :=
    fun s t y => hVreal (s + ξ₀) (t + η₀) y
  set u₀ : ℝ → ℝ → (Fin k → ℝ) → ℝ :=
    fun s t y => probeMultiU (translateTubePotential V ξ₀ η₀) T (s - ξ₀) (t - η₀) y with hu₀
  have hUcont : Continuous (nullMultiLift u₀ n) := by
    rw [nullMultiLift_eq_comp]
    exact (hD'.continuous_probeMultiU.comp (continuous_translateMapMulti ξ₀ η₀)).comp
      (nullMultiCLM k n).continuous
  have hnull : nullMultiCLM k n x = ((ξ₀, η₀), fun i : Fin k => x (transIdx k n i)) := rfl
  have hT0 : |(0 : ℝ)| < T := by simpa using hT
  have hxbox : x ∈ nullMultiBox (translateSetMulti (clockMultiBox k T) ξ₀ η₀) n := by
    rw [mem_nullMultiBox, hnull]
    refine ⟨?_, ?_⟩ <;> simpa using hT
  have hone : nullMultiLift u₀ n x = 1 := by
    show probeMultiU (translateTubePotential V ξ₀ η₀) T (ξ₀ - ξ₀) (η₀ - η₀)
      (fun i : Fin k => x (transIdx k n i)) = 1
    rw [sub_self, sub_self, probeMultiU,
      boxClamp_eq_self (le_of_lt hT0),
      tubeSolution_zero_zero hD'.pos hD'.pot hD'.massNonneg hD'.mass hD'.radNonneg hD'.rad
        hD'.sideNonneg hD'.small (hD'.absIm fun i : Fin k => x (transIdx k n i))]
    norm_num
  refine ⟨nullMultiBox (translateSetMulti (clockMultiBox k T) ξ₀ η₀) n
      ∩ {y | nullMultiLift u₀ n y ≠ 0},
    (isOpen_nullMultiBox (isOpen_translateSetMulti (isOpen_clockMultiBox k T) ξ₀ η₀) n).inter
      (isOpen_ne.preimage hUcont),
    ⟨hxbox, by rw [Set.mem_setOf_eq, hone]; exact one_ne_zero⟩, nullMultiLift u₀ n,
    ?_, fun y hy => hy.2, hone⟩
  refine solvesPotentialWaveOn_nullMultiLift (hD'.isC1OnMulti_probeMultiU.translate ξ₀ η₀)
    (hD'.isC1OnMulti_probeMultiA.translate ξ₀ η₀) (hD'.isC1OnMulti_probeMultiB.translate ξ₀ η₀)
    (fun i => (hD'.isC1OnMulti_probeMultiC i).translate ξ₀ η₀) (fun y hy => hy.1) fun y hy => ?_
  have hybox : nullMultiCLM k n y ∈ translateSetMulti (clockMultiBox k T) ξ₀ η₀ := hy.1
  have hs : |y 0 + y 1 - ξ₀| < T := hybox.1
  have ht : |y 0 - y 1 - η₀| < T := hybox.2
  have hchar := probeMulti_characteristic (V := translateTubePotential V ξ₀ η₀) (T := T) hVreal'
    hs ht (y := fun i : Fin k => y (transIdx k n i))
  have hVeq : translateTubePotential V ξ₀ η₀ (y 0 + y 1 - ξ₀) (y 0 - y 1 - η₀)
        (realTube fun i : Fin k => y (transIdx k n i))
      = V (y 0 + y 1) (y 0 - y 1) (realTube fun i : Fin k => y (transIdx k n i)) := by
    rw [translateTubePotential, sub_add_cancel, sub_add_cancel]
  rw [hVeq] at hchar
  exact hchar

end GaloisForLFunctions.HTGeometry
