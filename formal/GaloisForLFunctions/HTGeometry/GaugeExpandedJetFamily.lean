import GaloisForLFunctions.HTGeometry.GaugeProbeJetFamily
import GaloisForLFunctions.HTGeometry.ExpandedEvaluationCompactPatchDensity
import GaloisForLFunctions.HTGeometry.NevanlinnaTranslatedExpandedEvaluationCompactPatch

/-!
# The expanded jet family of a gauged source

The corpus rank-defect calculus reads a jet packet in row coordinates, with one square block of
jet slots per row.  This module converts the jet packet of a gauged source into those coordinates,
both for a finite polynomial probe of the exponent and for the gauge itself, and records that the
first is smooth with surjective probe derivative while the second is jointly continuous.

A finite chart through a point of any parameter space then transports finite-dimensional density
to density in that parameter space.
-/

open MvPolynomial Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Density along a finite chart -/

/-- **A finite chart transports density.**  If through every point of the parameter space there is
a continuous finite-dimensional chart along which the avoidance set is dense, the avoidance set is
dense in the parameter space. -/
theorem compactConfigurationAvoidance_dense_of_finiteChart
    {S : Type*} [TopologicalSpace S] {Hs Y : Type*} [TopologicalSpace Hs]
    (F : S × Hs → Y) (bad : Set Y) (K : Set Hs) (D : ℕ)
    (chart : S → (Fin D → ℂ) → S)
    (hcont : ∀ s, Continuous (chart s)) (hzero : ∀ s, chart s 0 = s)
    (hdense : ∀ s, Dense (compactConfigurationAvoidance
        (fun p : (Fin D → ℂ) × Hs => F (chart s p.1, p.2)) bad K)) :
    Dense (compactConfigurationAvoidance F bad K) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro s
  rw [mem_closure_iff]
  intro V hVopen hsV
  have hpreOpen : IsOpen (chart s ⁻¹' V) := hVopen.preimage (hcont s)
  have hpreNonempty : (chart s ⁻¹' V).Nonempty := ⟨0, by simpa [hzero s] using hsV⟩
  obtain ⟨c, hcgood, hcV⟩ := (hdense s).exists_mem_open hpreOpen hpreNonempty
  exact ⟨chart s c, hcV, fun h hh => hcgood h hh⟩

variable {row ι : Type} [Fintype row] [Fintype ι]

/-! ### Truncating a uniform jet packet to prescribed orders -/

/-- Reading a uniform jet packet at prescribed jet orders. -/
def jetTruncLin (row ι : Type) [Fintype row] [Fintype ι] (orders : ι → ℕ) (m : ℕ)
    (hm : ∀ i, orders i ≤ m) :
    ((row × ι) → Fin m → ℂ) →ₗ[ℝ] ((Σ x : row × ι, Fin (orders x.2)) → ℂ) :=
  LinearMap.pi fun s =>
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℂ)
        ⟨(s.2 : ℕ), lt_of_lt_of_le s.2.2 (hm s.1.2)⟩).comp
      (LinearMap.proj (R := ℝ) (φ := fun _ : row × ι => Fin m → ℂ) s.1)

/-- The same truncation, as a continuous linear map. -/
def jetTruncCLM (row ι : Type) [Fintype row] [Fintype ι] (orders : ι → ℕ) (m : ℕ)
    (hm : ∀ i, orders i ≤ m) :
    ((row × ι) → Fin m → ℂ) →L[ℝ] ((Σ x : row × ι, Fin (orders x.2)) → ℂ) :=
  LinearMap.toContinuousLinearMap (jetTruncLin row ι orders m hm)

theorem jetTruncCLM_apply (orders : ι → ℕ) (m : ℕ) (hm : ∀ i, orders i ≤ m)
    (v : (row × ι) → Fin m → ℂ) (s : Σ x : row × ι, Fin (orders x.2)) :
    jetTruncCLM row ι orders m hm v s
      = v s.1 ⟨(s.2 : ℕ), lt_of_lt_of_le s.2.2 (hm s.1.2)⟩ := rfl

theorem surjective_jetTruncCLM (orders : ι → ℕ) (m : ℕ) (hm : ∀ i, orders i ≤ m) :
    Function.Surjective (jetTruncCLM row ι orders m hm) := by
  classical
  intro y
  refine ⟨fun x k => if h : (k : ℕ) < orders x.2 then y ⟨x, ⟨(k : ℕ), h⟩⟩ else 0, ?_⟩
  funext s
  rw [jetTruncCLM_apply]
  rw [dif_pos s.2.2]

/-! ### The expanded probe family -/

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The jet packet of a probed gauged source, in row coordinates. -/
def gaugeExpandedProbeJetFamily (W g : ℂ → ℂ) {m D : ℕ} (pd : GaugeProbe (row × ι) m D)
    (orders : ι → ℕ) (hm : ∀ i, orders i ≤ m) (nodes : H → row × ι → ℂ)
    (p : (Fin D → ℂ) × H) :
    row × Fin (Fintype.card (Σ i, Fin (orders i))) → ℂ :=
  reshapeCombinedJetsFinCLM row ι orders
    (jetTruncCLM row ι orders m hm (gaugeProbeJetPacket W g pd nodes p))

theorem contDiff_gaugeExpandedProbeJetFamily {W g : ℂ → ℂ} (hW : Differentiable ℂ W)
    (hg : Differentiable ℂ g) {m D : ℕ} (pd : GaugeProbe (row × ι) m D)
    (orders : ι → ℕ) (hm : ∀ i, orders i ≤ m)
    {nodes : H → row × ι → ℂ} (hnodes : ContDiff ℝ ⊤ nodes) :
    ContDiff ℝ ⊤ (gaugeExpandedProbeJetFamily W g pd orders hm nodes) :=
  (reshapeCombinedJetsFinCLM row ι orders).contDiff.comp
    ((jetTruncCLM row ι orders m hm).contDiff.comp
      (contDiff_gaugeProbeJetPacket hW hg pd hnodes))

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
theorem surjective_fderiv_gaugeExpandedProbeJetFamily (W g : ℂ → ℂ) {m D : ℕ}
    (pd : GaugeProbe (row × ι) m D) (orders : ι → ℕ) (hm : ∀ i, orders i ≤ m)
    (nodes : H → row × ι → ℂ) (c : Fin D → ℂ) (h : H)
    (hprobe : Function.Surjective (pd.jet (nodes h)))
    (hWne : ∀ x, W (nodes h x) ≠ 0) :
    Function.Surjective
      (fderiv ℝ (fun v => gaugeExpandedProbeJetFamily W g pd orders hm nodes (v, h)) c) := by
  have hpacket := hasFDerivAt_gaugeProbeJetPacket W g pd nodes c h
  have hfull : HasFDerivAt
      (fun v => gaugeExpandedProbeJetFamily W g pd orders hm nodes (v, h))
      (((reshapeCombinedJetsFinCLM row ι orders).comp
        (jetTruncCLM row ι orders m hm)).comp (gaugeProbeJetCLM W g pd nodes c h)) c := by
    have hstep := (((reshapeCombinedJetsFinCLM row ι orders).comp
      (jetTruncCLM row ι orders m hm)).hasFDerivAt
        (x := gaugeProbeJetPacket W g pd nodes (c, h))).comp c hpacket
    exact hstep
  rw [hfull.fderiv]
  intro y
  obtain ⟨y1, hy1⟩ := reshapeCombinedJetsFinCLM_surjective row ι orders y
  obtain ⟨y2, hy2⟩ := surjective_jetTruncCLM orders m hm y1
  obtain ⟨y3, hy3⟩ := surjective_gaugeProbeJetCLM (W := W) (g := g) pd nodes c h hprobe hWne y2
  refine ⟨y3, ?_⟩
  show reshapeCombinedJetsFinCLM row ι orders
      (jetTruncCLM row ι orders m hm (gaugeProbeJetCLM W g pd nodes c h y3)) = y
  rw [hy3, hy2, hy1]

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set

variable {row ι : Type} [Fintype row] [Fintype ι] {H : Type} [TopologicalSpace H]

/-! ### The probe as a chart on the gauge space -/

/-- The probe polynomial, jointly continuous in its coefficients and the point. -/
def probePolyCM {X : Type*} [Fintype X] {m D : ℕ} (pd : GaugeProbe X m D) :
    C((Fin D → ℂ) × ℂ, ℂ) where
  toFun q := Polynomial.eval q.2 (pd.poly q.1)
  continuous_toFun := by
    have h := (pd.polyJet_contDiff 0).continuous
    simpa only [Function.iterate_zero_apply] using h

theorem probePolyCM_curry_differentiable {X : Type*} [Fintype X] {m D : ℕ}
    (pd : GaugeProbe X m D) (c : Fin D → ℂ) :
    Differentiable ℂ ⇑((ContinuousMap.curry (probePolyCM pd)) c) := by
  have hfun : ⇑((ContinuousMap.curry (probePolyCM pd)) c)
      = fun z => Polynomial.eval z (pd.poly c) := rfl
  rw [hfun]
  exact Polynomial.differentiable _

/-- The probe polynomial as an entire gauge. -/
def probeGaugeElt {X : Type*} [Fintype X] {m D : ℕ} (pd : GaugeProbe X m D)
    (c : Fin D → ℂ) : EntireGauge :=
  ⟨(ContinuousMap.curry (probePolyCM pd)) c, probePolyCM_curry_differentiable pd c⟩

theorem continuous_probeGaugeElt {X : Type*} [Fintype X] {m D : ℕ} (pd : GaugeProbe X m D) :
    Continuous (probeGaugeElt pd) := by
  rw [continuous_induced_rng]
  exact (ContinuousMap.curry (probePolyCM pd)).continuous

/-- Adding the probe polynomial to a gauge. -/
def probeGaugeChart {X : Type*} [Fintype X] {m D : ℕ} (pd : GaugeProbe X m D)
    (g : EntireGauge) (c : Fin D → ℂ) : EntireGauge :=
  g + probeGaugeElt pd c

theorem probeGaugeChart_apply {X : Type*} [Fintype X] {m D : ℕ} (pd : GaugeProbe X m D)
    (g : EntireGauge) (c : Fin D → ℂ) (z : ℂ) :
    (probeGaugeChart pd g c : C(ℂ, ℂ)) z
      = (g : C(ℂ, ℂ)) z + Polynomial.eval z (pd.poly c) := rfl

theorem continuous_probeGaugeChart {X : Type*} [Fintype X] {m D : ℕ} (pd : GaugeProbe X m D)
    (g : EntireGauge) : Continuous (probeGaugeChart pd g) :=
  continuous_const.add (continuous_probeGaugeElt pd)

theorem probeGaugeChart_zero {X : Type*} [Fintype X] {m D : ℕ} (pd : GaugeProbe X m D)
    (g : EntireGauge) : probeGaugeChart pd g 0 = g := by
  have hzero : probeGaugeElt pd (0 : Fin D → ℂ) = 0 := by
    refine Subtype.ext (ContinuousMap.ext fun z => ?_)
    show Polynomial.eval z (pd.poly 0) = 0
    rw [pd.poly_zero, Polynomial.eval_zero]
  rw [probeGaugeChart, hzero, add_zero]

/-! ### The expanded family of the gauge itself -/

/-- The jet packet of a gauged source, in row coordinates, as a function of the gauge. -/
def gaugeExpandedActualJetFamily (W : ℂ → ℂ) (m : ℕ) (orders : ι → ℕ) (hm : ∀ i, orders i ≤ m)
    (nodes : H → row × ι → ℂ) (p : EntireGauge × H) :
    row × Fin (Fintype.card (Σ i, Fin (orders i))) → ℂ :=
  reshapeCombinedJetsFinCLM row ι orders
    (jetTruncCLM row ι orders m hm
      (fun x j => iteratedDeriv (j : ℕ)
        (fun w => W w * Complex.exp ((p.1 : C(ℂ, ℂ)) w)) (nodes p.2 x)))

theorem continuous_gaugeExpandedActualJetFamily {W : ℂ → ℂ} (hW : Differentiable ℂ W)
    (m : ℕ) (orders : ι → ℕ) (hm : ∀ i, orders i ≤ m)
    {nodes : H → row × ι → ℂ} (hnodes : Continuous nodes) :
    Continuous (gaugeExpandedActualJetFamily (row := row) (ι := ι) W m orders hm nodes) := by
  classical
  refine (reshapeCombinedJetsFinCLM row ι orders).continuous.comp
    ((jetTruncCLM row ι orders m hm).continuous.comp ?_)
  rw [continuous_pi_iff]
  intro x
  rw [continuous_pi_iff]
  intro j
  have hnode : Continuous (fun p : EntireGauge × H => nodes p.2 x) :=
    (continuous_apply x).comp (hnodes.comp continuous_snd)
  have hjet : Continuous (fun p : EntireGauge × H =>
      gaugeJetVec m (⇑(p.1 : C(ℂ, ℂ))) (nodes p.2 x)) := by
    rw [continuous_pi_iff]
    intro k
    exact (continuous_gaugeJetEval (k : ℕ)).comp (continuous_fst.prodMk hnode)
  have hexp : Continuous (fun p : EntireGauge × H =>
      expJetMap m (gaugeJetVec m (⇑(p.1 : C(ℂ, ℂ))) (nodes p.2 x))) :=
    (contDiff_real_expJetMap m).continuous.comp hjet
  have hfun : (fun p : EntireGauge × H => iteratedDeriv (j : ℕ)
        (fun w => W w * Complex.exp ((p.1 : C(ℂ, ℂ)) w)) (nodes p.2 x))
      = fun p : EntireGauge × H => ∑ l : Fin m,
          leibnizJetMatrix m (fun r => iteratedDeriv r W (nodes p.2 x)) j l *
            expJetMap m (gaugeJetVec m (⇑(p.1 : C(ℂ, ℂ))) (nodes p.2 x)) l := by
    funext p
    exact iteratedDeriv_gaugeCarrier hW p.1.2 (nodes p.2 x) j
  rw [hfun]
  refine continuous_finsetSum _ fun l _ => ?_
  refine Continuous.mul ?_ ((continuous_apply l).comp hexp)
  have hcoeff : (fun p : EntireGauge × H =>
        leibnizJetMatrix m (fun r => iteratedDeriv r W (nodes p.2 x)) j l)
      = fun p : EntireGauge × H =>
        if (l : ℕ) ≤ (j : ℕ) then ((Nat.choose (j : ℕ) (l : ℕ) : ℂ)) *
          iteratedDeriv ((j : ℕ) - (l : ℕ)) W (nodes p.2 x) else 0 := by
    funext p
    rfl
  rw [hcoeff]
  by_cases hjl : (l : ℕ) ≤ (j : ℕ)
  · simp only [if_pos hjl]
    exact continuous_const.mul
      ((differentiable_iteratedDeriv_of_entire hW _).continuous.comp hnode)
  · simp only [if_neg hjl]
    exact continuous_const

omit [TopologicalSpace H] in
/-- **The probe family is the actual family along any chart realizing the probe.** -/
theorem gaugeExpandedProbeJetFamily_eq_actual {W : ℂ → ℂ} (hW : Differentiable ℂ W)
    {g : EntireGauge} {m D : ℕ} (pd : GaugeProbe (row × ι) m D)
    (orders : ι → ℕ) (hm : ∀ i, orders i ≤ m) (nodes : H → row × ι → ℂ)
    (target : EntireGauge) (c : Fin D → ℂ)
    (hchart : ∀ w, (target : C(ℂ, ℂ)) w = (g : C(ℂ, ℂ)) w + Polynomial.eval w (pd.poly c))
    (h : H) :
    gaugeExpandedProbeJetFamily W (⇑(g : C(ℂ, ℂ))) pd orders hm nodes (c, h)
      = gaugeExpandedActualJetFamily W m orders hm nodes (target, h) := by
  unfold gaugeExpandedProbeJetFamily gaugeExpandedActualJetFamily
  congr 2
  funext x j
  rw [gaugeProbeJetPacket_eq hW g.2 pd nodes (c, h) x j]
  congr 1
  funext w
  rw [hchart w]

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set

/-! ### Compact-patch density for a gauged source -/

variable {row κ ι : Type} [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ]
  [Fintype ι] [DecidableEq ι]
  {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

omit [DecidableEq ι] in
theorem compact_gaugeExpandedProbeEvaluation_avoidance_dense
    (degree : ℕ) (orders : ι → ℕ) {m D : ℕ} (pd : GaugeProbe (row × ι) m D)
    (hm : ∀ i, orders i ≤ m)
    (z : row → ℂ) (hz : Function.Injective z)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree < Fintype.card row)
    {W : ℂ → ℂ} (hW : Differentiable ℂ W) {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (nodes : H → row × ι → ℂ) (hnodes : ContDiff ℝ ⊤ nodes)
    (U K : Set H) (hU : IsOpen U) (hKU : K ⊆ U)
    (hprobe : ∀ h ∈ U, Function.Surjective (pd.jet (nodes h)))
    (hWne : ∀ h ∈ U, ∀ x, W (nodes h x) ≠ 0)
    (hdim : Module.finrank ℝ H <
      2 * (Fintype.card row - Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    Dense (compactConfigurationAvoidance
      (gaugeExpandedProbeJetFamily W g pd orders hm nodes)
      (expandedDifferentialEvaluationRankDefect degree
        (Fintype.card (Σ i, Fin (orders i))) z exponent) K) := by
  apply expandedEvaluation_compactPatchAvoidance_dense
    degree (Fintype.card (Σ i, Fin (orders i))) z hz exponent hexponent hrows
    (gaugeExpandedProbeJetFamily W g pd orders hm nodes) U K hU hKU
  · exact (contDiff_gaugeExpandedProbeJetFamily hW hg pd orders hm hnodes).contDiffOn
  · intro c h hh
    exact surjective_fderiv_gaugeExpandedProbeJetFamily W g pd orders hm nodes c h
      (hprobe h hh) (hWne h hh)
  · exact hdim

omit [DecidableEq ι] in
/-- **Compact-patch density for a gauged source, along a chart of any parameter space.**  Densely
many parameters give full expanded-evaluation rank at every shift of a compact patch, with the
divisor of `W` unchanged. -/
theorem compact_gaugeExpandedActualEvaluation_avoidance_dense_of_chart
    (degree : ℕ) (orders : ι → ℕ) {m D : ℕ} (pd : GaugeProbe (row × ι) m D)
    (hm : ∀ i, orders i ≤ m)
    (z : row → ℂ) (hz : Function.Injective z)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree < Fintype.card row)
    {W : ℂ → ℂ} (hW : Differentiable ℂ W)
    (nodes : H → row × ι → ℂ) (hnodes : ContDiff ℝ ⊤ nodes)
    (U K : Set H) (hU : IsOpen U) (hKU : K ⊆ U)
    (hprobe : ∀ h ∈ U, Function.Surjective (pd.jet (nodes h)))
    (hWne : ∀ h ∈ U, ∀ x, W (nodes h x) ≠ 0)
    (hdim : Module.finrank ℝ H <
      2 * (Fintype.card row - Fintype.card (κ × Fin (degree + 1)) - degree + 1))
    {S : Type} [TopologicalSpace S] (incl : S → EntireGauge)
    (chart : S → (Fin D → ℂ) → S)
    (hcont : ∀ s, Continuous (chart s)) (hzero : ∀ s, chart s 0 = s)
    (hchartApply : ∀ (s : S) (c : Fin D → ℂ) (w : ℂ),
      (incl (chart s c) : C(ℂ, ℂ)) w = (incl s : C(ℂ, ℂ)) w + Polynomial.eval w (pd.poly c)) :
    Dense (compactConfigurationAvoidance
      (fun p : S × H => gaugeExpandedActualJetFamily W m orders hm nodes (incl p.1, p.2))
      (expandedDifferentialEvaluationRankDefect degree
        (Fintype.card (Σ i, Fin (orders i))) z exponent) K) := by
  refine compactConfigurationAvoidance_dense_of_finiteChart _ _ K D chart hcont hzero ?_
  intro s
  have hdenseProbe := compact_gaugeExpandedProbeEvaluation_avoidance_dense
    degree orders pd hm z hz exponent hexponent hrows hW (incl s).2 nodes hnodes U K hU hKU
    hprobe hWne hdim
  have hfamEq : (fun p : (Fin D → ℂ) × H =>
      gaugeExpandedActualJetFamily W m orders hm nodes (incl (chart s p.1), p.2))
      = gaugeExpandedProbeJetFamily W (⇑((incl s : EntireGauge) : C(ℂ, ℂ))) pd orders hm nodes := by
    funext p
    exact (gaugeExpandedProbeJetFamily_eq_actual hW pd orders hm nodes (incl (chart s p.1)) p.1
      (fun w => hchartApply s p.1 w) p.2).symm
  show Dense (compactConfigurationAvoidance
    (fun p : (Fin D → ℂ) × H =>
      gaugeExpandedActualJetFamily W m orders hm nodes (incl (chart s p.1), p.2)) _ K)
  rw [hfamEq]
  exact hdenseProbe

omit [DecidableEq ι] in
/-- Compact-patch density on the full gauge space, along the probe chart. -/
theorem compact_gaugeExpandedActualEvaluation_avoidance_dense
    (degree : ℕ) (orders : ι → ℕ) {m D : ℕ} (pd : GaugeProbe (row × ι) m D)
    (hm : ∀ i, orders i ≤ m)
    (z : row → ℂ) (hz : Function.Injective z)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree < Fintype.card row)
    {W : ℂ → ℂ} (hW : Differentiable ℂ W)
    (nodes : H → row × ι → ℂ) (hnodes : ContDiff ℝ ⊤ nodes)
    (U K : Set H) (hU : IsOpen U) (hKU : K ⊆ U)
    (hprobe : ∀ h ∈ U, Function.Surjective (pd.jet (nodes h)))
    (hWne : ∀ h ∈ U, ∀ x, W (nodes h x) ≠ 0)
    (hdim : Module.finrank ℝ H <
      2 * (Fintype.card row - Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    Dense (compactConfigurationAvoidance
      (gaugeExpandedActualJetFamily (row := row) (ι := ι) W m orders hm nodes)
      (expandedDifferentialEvaluationRankDefect degree
        (Fintype.card (Σ i, Fin (orders i))) z exponent) K) := by
  have h := compact_gaugeExpandedActualEvaluation_avoidance_dense_of_chart
    degree orders pd hm z hz exponent hexponent hrows hW nodes hnodes U K hU hKU
    hprobe hWne hdim (S := EntireGauge) id (probeGaugeChart pd)
    (fun s => continuous_probeGaugeChart pd s) (fun s => probeGaugeChart_zero pd s)
    (fun s c w => probeGaugeChart_apply pd s c w)
  exact h

end

end GaloisForLFunctions.HTGeometry
