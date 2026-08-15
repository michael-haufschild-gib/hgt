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

omit [Fintype row] [Fintype ι] [NormedAddCommGroup H] [NormedSpace ℝ H] in
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
