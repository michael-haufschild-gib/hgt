import GaloisForLFunctions.HTGeometry.GaugeProbeJetFamily
import GaloisForLFunctions.HTGeometry.ExpandedEvaluationCompactPatchDensity
import GaloisForLFunctions.HTGeometry.NevanlinnaTranslatedExpandedEvaluationCompactPatch

/-!
# The expanded jet family of a gauged source

The corpus rank-defect calculus reads a jet packet in row coordinates, with one square block of
jet slots per row.  This module converts the jet packet of a gauged source into those coordinates,
both for a finite polynomial probe of the exponent and for the gauge itself, and records that the
first is smooth with surjective probe derivative while the second is jointly continuous.
-/

open MvPolynomial Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

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

/-- The probe dimension: one window coefficient per node and jet slot. -/
abbrev gaugeProbeDim (row ι : Type) [Fintype row] [Fintype ι] (m : ℕ) : ℕ :=
  Fintype.card (row × ι) * m

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The jet packet of a probed gauged source, in row coordinates. -/
def gaugeExpandedProbeJetFamily (W g : ℂ → ℂ) (m N : ℕ) (orders : ι → ℕ)
    (hm : ∀ i, orders i ≤ m) (nodes : H → row × ι → ℂ)
    (p : (Fin (gaugeProbeDim row ι m) → ℂ) × H) :
    row × Fin (Fintype.card (Σ i, Fin (orders i))) → ℂ :=
  reshapeCombinedJetsFinCLM row ι orders
    (jetTruncCLM row ι orders m hm
      (gaugeProbeJetPacket W g m N (gaugeProbeDim row ι m) nodes p))

theorem contDiff_gaugeExpandedProbeJetFamily {W g : ℂ → ℂ} (hW : Differentiable ℂ W)
    (hg : Differentiable ℂ g) (m N : ℕ) (orders : ι → ℕ) (hm : ∀ i, orders i ≤ m)
    {nodes : H → row × ι → ℂ} (hnodes : ContDiff ℝ ⊤ nodes) :
    ContDiff ℝ ⊤ (gaugeExpandedProbeJetFamily W g m N orders hm nodes) :=
  (reshapeCombinedJetsFinCLM row ι orders).contDiff.comp
    ((jetTruncCLM row ι orders m hm).contDiff.comp
      (contDiff_gaugeProbeJetPacket hW hg m N (gaugeProbeDim row ι m) hnodes))

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
theorem surjective_fderiv_gaugeExpandedProbeJetFamily [DecidableEq row] [DecidableEq ι]
    (W g : ℂ → ℂ) (m N : ℕ)
    (orders : ι → ℕ) (hm : ∀ i, orders i ≤ m)
    (nodes : H → row × ι → ℂ)
    (c : Fin (gaugeProbeDim row ι m) → ℂ) (h : H)
    (hinj : Function.Injective (nodes h)) (hne : ∀ x, nodes h x ≠ 0)
    (hWne : ∀ x, W (nodes h x) ≠ 0) :
    Function.Surjective
      (fderiv ℝ (fun v => gaugeExpandedProbeJetFamily W g m N orders hm nodes (v, h)) c) := by
  have hpacket := hasFDerivAt_gaugeProbeJetPacket W g m N (gaugeProbeDim row ι m) nodes c h
  have hfull : HasFDerivAt
      (fun v => gaugeExpandedProbeJetFamily W g m N orders hm nodes (v, h))
      (((reshapeCombinedJetsFinCLM row ι orders).comp
        (jetTruncCLM row ι orders m hm)).comp
          (gaugeProbeJetCLM W g m N (gaugeProbeDim row ι m) nodes c h)) c := by
    have := (((reshapeCombinedJetsFinCLM row ι orders).comp
      (jetTruncCLM row ι orders m hm)).hasFDerivAt
        (x := gaugeProbeJetPacket W g m N (gaugeProbeDim row ι m) nodes (c, h))).comp c hpacket
    exact this
  rw [hfull.fderiv]
  intro y
  obtain ⟨y1, hy1⟩ := reshapeCombinedJetsFinCLM_surjective row ι orders y
  obtain ⟨y2, hy2⟩ := surjective_jetTruncCLM orders m hm y1
  obtain ⟨y3, hy3⟩ := surjective_gaugeProbeJetCLM (W := W) (g := g) m N nodes c h hinj hne hWne y2
  refine ⟨y3, ?_⟩
  show reshapeCombinedJetsFinCLM row ι orders
      (jetTruncCLM row ι orders m hm
        (gaugeProbeJetCLM W g m N (gaugeProbeDim row ι m) nodes c h y3)) = y
  rw [hy3, hy2, hy1]

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set

variable {row ι : Type} [Fintype row] [Fintype ι] {H : Type} [TopologicalSpace H]

/-! ### The window chart on the gauge space -/

/-- The window polynomial, jointly continuous in its coefficients and the point. -/
def windowPolyCM (N D : ℕ) : C((Fin D → ℂ) × ℂ, ℂ) where
  toFun q := Polynomial.eval q.2 (windowLin N D q.1)
  continuous_toFun := by
    have hfun : (fun q : (Fin D → ℂ) × ℂ => Polynomial.eval q.2 (windowLin N D q.1))
        = fun q : (Fin D → ℂ) × ℂ => ∑ i : Fin D, q.1 i * q.2 ^ (N + (i : ℕ)) := by
      funext q
      rw [windowLin_apply, Polynomial.eval_finsetSum]
      exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.eval_monomial]
    rw [hfun]
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((continuous_apply i).comp continuous_fst).mul (continuous_snd.pow _)

theorem windowPolyCM_curry_differentiable (N D : ℕ) (c : Fin D → ℂ) :
    Differentiable ℂ ⇑((ContinuousMap.curry (windowPolyCM N D)) c) := by
  have hfun : ⇑((ContinuousMap.curry (windowPolyCM N D)) c)
      = fun z => Polynomial.eval z (windowLin N D c) := rfl
  rw [hfun]
  exact Polynomial.differentiable _

/-- The window polynomial as an entire gauge. -/
def windowGaugeElt (N D : ℕ) (c : Fin D → ℂ) : EntireGauge :=
  ⟨(ContinuousMap.curry (windowPolyCM N D)) c, windowPolyCM_curry_differentiable N D c⟩

theorem continuous_windowGaugeElt (N D : ℕ) : Continuous (windowGaugeElt N D) := by
  rw [continuous_induced_rng]
  exact (ContinuousMap.curry (windowPolyCM N D)).continuous

/-- Adding a window polynomial to a gauge: a continuous finite-dimensional chart. -/
def windowGaugeChart (N D : ℕ) (g : EntireGauge) (c : Fin D → ℂ) : EntireGauge :=
  g + windowGaugeElt N D c

theorem windowGaugeChart_apply (N D : ℕ) (g : EntireGauge) (c : Fin D → ℂ) (z : ℂ) :
    (windowGaugeChart N D g c : C(ℂ, ℂ)) z
      = (g : C(ℂ, ℂ)) z + Polynomial.eval z (windowLin N D c) := rfl

theorem continuous_windowGaugeChart (N D : ℕ) (g : EntireGauge) :
    Continuous (windowGaugeChart N D g) :=
  continuous_const.add (continuous_windowGaugeElt N D)

theorem windowGaugeChart_zero (N D : ℕ) (g : EntireGauge) : windowGaugeChart N D g 0 = g := by
  have hzero : windowGaugeElt N D (0 : Fin D → ℂ) = 0 := by
    refine Subtype.ext (ContinuousMap.ext fun z => ?_)
    show Polynomial.eval z (windowLin N D (0 : Fin D → ℂ)) = 0
    rw [map_zero, Polynomial.eval_zero]
  rw [windowGaugeChart, hzero, add_zero]

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
/-- **The probe family is the actual family along the window chart.** -/
theorem gaugeExpandedProbeJetFamily_eq_actual {W : ℂ → ℂ} (hW : Differentiable ℂ W)
    (g : EntireGauge) (m N : ℕ) (orders : ι → ℕ) (hm : ∀ i, orders i ≤ m)
    (nodes : H → row × ι → ℂ) (p : (Fin (gaugeProbeDim row ι m) → ℂ) × H) :
    gaugeExpandedProbeJetFamily W (⇑(g : C(ℂ, ℂ))) m N orders hm nodes p
      = gaugeExpandedActualJetFamily W m orders hm nodes
          (windowGaugeChart N (gaugeProbeDim row ι m) g p.1, p.2) := by
  unfold gaugeExpandedProbeJetFamily gaugeExpandedActualJetFamily
  congr 2
  funext x j
  rw [gaugeProbeJetPacket_eq hW g.2 m N (gaugeProbeDim row ι m) nodes p x j]
  congr 1

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set

/-! ### Compact-patch density for a gauged source -/

variable {row κ ι : Type} [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ]
  [Fintype ι] [DecidableEq ι]
  {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

theorem compact_gaugeExpandedProbeEvaluation_avoidance_dense
    (degree : ℕ) (orders : ι → ℕ) (m N : ℕ) (hm : ∀ i, orders i ≤ m)
    (z : row → ℂ) (hz : Function.Injective z)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree < Fintype.card row)
    {W : ℂ → ℂ} (hW : Differentiable ℂ W) (g : EntireGauge)
    (nodes : H → row × ι → ℂ) (hnodes : ContDiff ℝ ⊤ nodes)
    (U K : Set H) (hU : IsOpen U) (hKU : K ⊆ U)
    (hinj : ∀ h ∈ U, Function.Injective (nodes h))
    (hne : ∀ h ∈ U, ∀ x, nodes h x ≠ 0)
    (hWne : ∀ h ∈ U, ∀ x, W (nodes h x) ≠ 0)
    (hdim : Module.finrank ℝ H <
      2 * (Fintype.card row - Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    Dense (compactConfigurationAvoidance
      (gaugeExpandedProbeJetFamily W (⇑(g : C(ℂ, ℂ))) m N orders hm nodes)
      (expandedDifferentialEvaluationRankDefect degree
        (Fintype.card (Σ i, Fin (orders i))) z exponent) K) := by
  apply expandedEvaluation_compactPatchAvoidance_dense
    degree (Fintype.card (Σ i, Fin (orders i))) z hz exponent hexponent hrows
    (gaugeExpandedProbeJetFamily W (⇑(g : C(ℂ, ℂ))) m N orders hm nodes) U K hU hKU
  · exact (contDiff_gaugeExpandedProbeJetFamily hW g.2 m N orders hm hnodes).contDiffOn
  · intro c h hh
    exact surjective_fderiv_gaugeExpandedProbeJetFamily W (⇑(g : C(ℂ, ℂ))) m N orders hm nodes
      c h (hinj h hh) (hne h hh) (hWne h hh)
  · exact hdim

/-- **Compact-patch density for a gauged source.**  Densely many entire gauges have full
expanded-evaluation rank at every shift of a compact patch, with the divisor of `W` unchanged. -/
theorem compact_gaugeExpandedActualEvaluation_avoidance_dense
    (degree : ℕ) (orders : ι → ℕ) (m : ℕ) (hm : ∀ i, orders i ≤ m)
    (z : row → ℂ) (hz : Function.Injective z)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree < Fintype.card row)
    {W : ℂ → ℂ} (hW : Differentiable ℂ W)
    (nodes : H → row × ι → ℂ) (hnodes : ContDiff ℝ ⊤ nodes)
    (U K : Set H) (hU : IsOpen U) (hKU : K ⊆ U)
    (hinj : ∀ h ∈ U, Function.Injective (nodes h))
    (hne : ∀ h ∈ U, ∀ x, nodes h x ≠ 0)
    (hWne : ∀ h ∈ U, ∀ x, W (nodes h x) ≠ 0)
    (hdim : Module.finrank ℝ H <
      2 * (Fintype.card row - Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    Dense (compactConfigurationAvoidance
      (gaugeExpandedActualJetFamily W m orders hm nodes)
      (expandedDifferentialEvaluationRankDefect degree
        (Fintype.card (Σ i, Fin (orders i))) z exponent) K) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro g
  rw [mem_closure_iff]
  intro V hVopen hgV
  set D := gaugeProbeDim row ι m with hD
  set chart : (Fin D → ℂ) → EntireGauge := windowGaugeChart 0 D g with hchart
  have hchartCont : Continuous chart := continuous_windowGaugeChart 0 D g
  have hchartZero : chart 0 = g := windowGaugeChart_zero 0 D g
  have hpreOpen : IsOpen (chart ⁻¹' V) := hVopen.preimage hchartCont
  have hpreNonempty : (chart ⁻¹' V).Nonempty := ⟨0, by simpa [hchartZero] using hgV⟩
  have hdenseFinite := compact_gaugeExpandedProbeEvaluation_avoidance_dense
    degree orders m 0 hm z hz exponent hexponent hrows hW g nodes hnodes U K hU hKU
    hinj hne hWne hdim
  obtain ⟨c, hcgood, hcV⟩ := hdenseFinite.exists_mem_open hpreOpen hpreNonempty
  refine ⟨chart c, hcV, ?_⟩
  intro h hh
  have hval := hcgood h hh
  rw [gaugeExpandedProbeJetFamily_eq_actual hW g m 0 orders hm nodes (c, h)] at hval
  exact hval

end

end GaloisForLFunctions.HTGeometry
