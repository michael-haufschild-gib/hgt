import GaloisForLFunctions.RHTower.NearestNeighborGaussianSameDrawGrowthPlateauRecurrenceLaw
import GaloisForLFunctions.RHTower.StaticChoiTraceHeapFirstReturnLaw

/-!
# One-draw growth, trace-heap plateau, and complete-circuit first re-entry

The same coefficient draw from the ordinary time-independent nearest-neighbour Gaussian ensemble
supplies the robust laboratory ramp and a continuous late plateau against every circuit of bounded
depth.  Disjoint-gate commutation replaces free-word entropy by intrinsic trace-heap capacity, and
the plateau is bracketed by consecutive visits to the complete bounded-depth circuit set.

The theorem does not bound the first plateau onset.  It is therefore a same-draw regime theorem,
not yet the time-aligned Brown--Susskind growth law.
-/

open MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

noncomputable section

namespace RHTower

/-- Literal first-reentry gaps to the entire gate-word set of length at most `budget` along one
nearest-neighbour static Choi orbit. -/
def NearestNeighborPathTraceHeapFirstReturnGap
    (L budget : ℕ)
    (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ)
    {α : Type*} [Fintype α]
    (act : α →
      EuclideanSpace ℂ
          (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
            Fin (nearestNeighborPathProjectiveDimension L + 1)) →
        EuclideanSpace ℂ
          (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
            Fin (nearestNeighborPathProjectiveDimension L + 1)))
    (chi : EuclideanSpace ℂ
      (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
        Fin (nearestNeighborPathProjectiveDimension L + 1)))
    (eps W : ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ A0 : ℝ, 0 ≤ A0 → ∃ u tExit tReturn : ℝ,
    A0 ≤ u ∧ tExit ∈ Icc (u - B) u ∧
      tReturn ∈ Icc (u + W) (u + W + B) ∧
      (∃ w : List α, w.length ≤ budget ∧
        pureStateTraceDistance
          (fullUniformPhaseChoiVector (nearestNeighborPathProjectiveDimension L + 1)
            (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
              (projectivePhysicalPhaseFlow
                (nearestNeighborPathChoiEnergy L p) tExit)))
          (GaloisForLFunctions.RHTower.wordEval act w chi) ≤ eps) ∧
      (∃ w : List α, w.length ≤ budget ∧
        pureStateTraceDistance
          (fullUniformPhaseChoiVector (nearestNeighborPathProjectiveDimension L + 1)
            (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
              (projectivePhysicalPhaseFlow
                (nearestNeighborPathChoiEnergy L p) tReturn)))
          (GaloisForLFunctions.RHTower.wordEval act w chi) ≤ eps) ∧
      tExit < tReturn ∧ W ≤ tReturn - tExit ∧
      ∀ t ∈ Ioo tExit tReturn,
        ¬ ∃ w : List α, w.length ≤ budget ∧
          pureStateTraceDistance
            (fullUniformPhaseChoiVector (nearestNeighborPathProjectiveDimension L + 1)
              (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
                (projectivePhysicalPhaseFlow
                  (nearestNeighborPathChoiEnergy L p) t)))
            (GaloisForLFunctions.RHTower.wordEval act w chi) ≤ eps

/-- **Same-draw trace-heap growth--plateau--first-reentry law.**  One ordinary nearest-neighbour
Hamiltonian draw has the robust laboratory ramp and, for the same static spectrum, a continuous
depth-bounded circuit-hard plateau inside a literal consecutive-capture excursion of duration at
least `W`. -/
theorem nearestNeighborPath_sameDraw_growth_lateTraceHeapPlateau_firstReturn
    {L : ℕ} {T εGrow : ℝ}
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ nearestNeighborPathGaussianGrowthMaximalEvent L T εGrow)
    {α : Type*} [Fintype α] [LinearOrder α]
    (independent : α → α → Prop)
    (hsymm : ∀ a b, independent a b → independent b a)
    (budget Delta : ℕ)
    (hdegree : ∀ a,
      GaloisForLFunctions.RHTower.incidentEdgeCount independent a ≤ Delta)
    (act : α →
      EuclideanSpace ℂ
          (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
            Fin (nearestNeighborPathProjectiveDimension L + 1)) →
        EuclideanSpace ℂ
          (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
            Fin (nearestNeighborPathProjectiveDimension L + 1)))
    (hcomm : ∀ a b, independent a b → ∀ x, act a (act b x) = act b (act a x))
    (e : α) (he : ∀ x, act e x = x)
    (hnorm : ∀ g x, ‖act g x‖ = ‖x‖)
    (chi : EuclideanSpace ℂ
      (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
        Fin (nearestNeighborPathProjectiveDimension L + 1)))
    (hchi : ‖chi‖ = 1)
    (hinitial : chi =
      fullUniformPhaseChoiVector (nearestNeighborPathProjectiveDimension L + 1)
        (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
          (0 : Fin (nearestNeighborPathProjectiveDimension L) → UnitAddCircle)))
    {epsn epsw W : ℝ} (hepsn : 0 < epsn) (hgap : epsn < epsw) (hW : 0 ≤ W)
    (hpack :
      (traceHeapCapacity α budget Delta : ℝ) *
          (((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) *
            Real.exp (((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * (Real.sqrt 2 * epsw) ^ (2 : ℕ)) / 2) ^
              ((nearestNeighborPathProjectiveDimension L + 1 : ℕ) - 1)) <
        ((epsw - epsn) /
            projectiveChoiSpeed (nearestNeighborPathChoiEnergy L p)) /
          (W + (epsw - epsn) /
            projectiveChoiSpeed (nearestNeighborPathChoiEnergy L p))) :
    (∀ t : ℝ,
      2048 * Real.pi * εGrow ≤ t →
      t ≤ εGrow * L →
      t ≤ T →
      ((⌊t / (256 * Real.pi * εGrow)⌋₊ : ℕ) : ℕ∞) ≤
        operatorTwoGateComplexityTo L εGrow
          (unitaryEvolution (nearestNeighborPathLocalHamiltonian L p) t)) ∧
    NearestNeighborPathTraceHeapFirstReturnGap L budget p act chi epsn W := by
  refine ⟨hp.2, ?_⟩
  change ∃ B : ℝ, 0 ≤ B ∧ ∀ A0 : ℝ, 0 ≤ A0 → ∃ u tExit tReturn : ℝ, _
  exact maximallyProjective_commutingGateWordsAtMost_explicit_consecutiveVisitGap
    (nearestNeighborPathChoiEnergy L p)
    (maximallyProjectiveEnergy_nearestNeighborPathChoiEnergy hp.1)
    independent hsymm budget Delta hdegree act hcomm e he hnorm chi hchi hinitial
    hepsn hgap hW hpack

/-- A completed-occupation bound strictly below one always certifies some strictly positive
continuous hard-block width. -/
theorem exists_positive_hardBlockWidth
    {b m : ℝ} (hb : b < 1) (hm : 0 < m) :
    ∃ W : ℝ, 0 < W ∧ b < m / (W + m) := by
  let W := m * (1 - b) / 2
  have hW : 0 < W := by dsimp [W]; positivity
  refine ⟨W, hW, ?_⟩
  have hden : 0 < W + m := by positivity
  rw [lt_div_iff₀ hden]
  dsimp [W]
  nlinarith [mul_pos (sub_pos.mpr hb) (sub_pos.mpr (show b < 2 by linarith))]

/-- **Inverse-occupation width.**  A positive completed occupation bound `b < 1` certifies a
hard-block width of order `m / b`, where `m` is the orbit's radius-gap traversal time. -/
theorem exists_inverseOccupation_hardBlockWidth
    {b m : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (hm : 0 < m) :
    ∃ W : ℝ, 0 < W ∧ m * (b⁻¹ - 1) / 2 ≤ W ∧ b < m / (W + m) := by
  let W := m * (b⁻¹ - 1) / 2
  have hbinv : 1 < b⁻¹ := (one_lt_inv₀ hb0).2 hb1
  have hW : 0 < W := by dsimp [W]; positivity
  refine ⟨W, hW, le_rfl, ?_⟩
  have hden : 0 < W + m := by positivity
  rw [lt_div_iff₀ hden]
  dsimp [W]
  field_simp [ne_of_gt hb0]
  nlinarith [mul_pos (sub_pos.mpr hb1) hb0]

/-- **Closed one-draw existence law.**  Under the explicit finite-size laboratory parameters and
trace-heap entropy inequality, a draw exists in the ordinary nearest-neighbour product-Gaussian
ensemble for which the robust ramp and a strictly positive complete-circuit first-reentry gap hold
for the same time-independent Hamiltonian. -/
theorem exists_nearestNeighborPath_sameDraw_growth_positiveTraceHeapFirstReturnGap
    {L : ℕ} (hL : 0 < L)
    {T εGrow ρ : ℝ}
    (hT : 0 ≤ T) (hεGrow : 0 < εGrow) (hεGrowMax : εGrow ≤ 1 / 200)
    (hρ : 0 < ρ)
    (hscale : T * (ρ * nearestNeighborPathLocalGeneratorMass L) ≤ εGrow)
    {α : Type*} [Fintype α] [LinearOrder α]
    (independent : α → α → Prop)
    (hsymm : ∀ a b, independent a b → independent b a)
    (budget Delta : ℕ)
    (hdegree : ∀ a,
      GaloisForLFunctions.RHTower.incidentEdgeCount independent a ≤ Delta)
    (act : α →
      EuclideanSpace ℂ
          (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
            Fin (nearestNeighborPathProjectiveDimension L + 1)) →
        EuclideanSpace ℂ
          (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
            Fin (nearestNeighborPathProjectiveDimension L + 1)))
    (hcomm : ∀ a b, independent a b → ∀ x, act a (act b x) = act b (act a x))
    (e : α) (he : ∀ x, act e x = x)
    (hnorm : ∀ g x, ‖act g x‖ = ‖x‖)
    (chi : EuclideanSpace ℂ
      (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
        Fin (nearestNeighborPathProjectiveDimension L + 1)))
    (hchi : ‖chi‖ = 1)
    (hinitial : chi =
      fullUniformPhaseChoiVector (nearestNeighborPathProjectiveDimension L + 1)
        (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
          (0 : Fin (nearestNeighborPathProjectiveDimension L) → UnitAddCircle)))
    {epsn epsw : ℝ} (hepsn : 0 < epsn) (hgap : epsn < epsw)
    (hentropy :
      (traceHeapCapacity α budget Delta : ℝ) *
          (((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) *
            Real.exp (((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * (Real.sqrt 2 * epsw) ^ (2 : ℕ)) / 2) ^
              ((nearestNeighborPathProjectiveDimension L + 1 : ℕ) - 1)) < 1) :
    ∃ p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ,
      p ∈ nearestNeighborPathGaussianGrowthMaximalEvent L T εGrow ∧
      ∃ W : ℝ, 0 < W ∧
        ((epsw - epsn) / projectiveChoiSpeed (nearestNeighborPathChoiEnergy L p)) *
            (((traceHeapCapacity α budget Delta : ℝ) *
              (((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) *
                Real.exp (((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) / 2) *
                Real.sqrt (Real.pi * (2 * (Real.sqrt 2 * epsw) ^ (2 : ℕ)) / 2) ^
                  ((nearestNeighborPathProjectiveDimension L + 1 : ℕ) - 1)))⁻¹ - 1) / 2 ≤ W ∧
        (∀ t : ℝ,
          2048 * Real.pi * εGrow ≤ t →
          t ≤ εGrow * L →
          t ≤ T →
          ((⌊t / (256 * Real.pi * εGrow)⌋₊ : ℕ) : ℕ∞) ≤
            operatorTwoGateComplexityTo L εGrow
              (unitaryEvolution (nearestNeighborPathLocalHamiltonian L p) t)) ∧
        NearestNeighborPathTraceHeapFirstReturnGap L budget p act chi epsn W := by
  have heventPos := measure_nearestNeighborPathGaussianGrowthMaximalEvent_pos
    hL hT hεGrow hεGrowMax hρ hscale
  obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero (ne_of_gt heventPos)
  let b : ℝ := (traceHeapCapacity α budget Delta : ℝ) *
      (((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) *
        Real.exp (((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) / 2) *
        Real.sqrt (Real.pi * (2 * (Real.sqrt 2 * epsw) ^ (2 : ℕ)) / 2) ^
          ((nearestNeighborPathProjectiveDimension L + 1 : ℕ) - 1))
  let m : ℝ := (epsw - epsn) /
    projectiveChoiSpeed (nearestNeighborPathChoiEnergy L p)
  have hm : 0 < m := by
    dsimp only [m]
    exact div_pos (sub_pos.mpr hgap)
      (projectiveChoiSpeed_pos (nearestNeighborPathChoiEnergy L p))
  have hb : b < 1 := by simpa only [b] using hentropy
  letI : Nonempty α := ⟨e⟩
  have hcapacityNat : 0 < traceHeapCapacity α budget Delta := by
    rw [traceHeapCapacity]
    exact Nat.mul_pos (Nat.choose_pos (by
      have hc : 0 < Fintype.card α := Fintype.card_pos
      omega)) (pow_pos (by omega) _)
  have hcapacity : (0 : ℝ) < traceHeapCapacity α budget Delta := by
    exact_mod_cast hcapacityNat
  have hb0 : 0 < b := by
    dsimp only [b]
    have hepsw : 0 < epsw := lt_trans hepsn hgap
    have hrad : 0 < Real.sqrt
        (Real.pi * (2 * (Real.sqrt 2 * epsw) ^ (2 : ℕ)) / 2) :=
      Real.sqrt_pos.2 (by positivity)
    exact mul_pos hcapacity (mul_pos (mul_pos (by positivity) (Real.exp_pos _))
      (pow_pos hrad _))
  obtain ⟨W, hW, hWLower, hpack⟩ :=
    exists_inverseOccupation_hardBlockWidth hb0 hb hm
  refine ⟨p, hp, W, hW, ?_, ?_⟩
  · simpa only [b, m] using hWLower
  apply nearestNeighborPath_sameDraw_growth_lateTraceHeapPlateau_firstReturn
    hp independent hsymm budget Delta hdegree act hcomm e he hnorm chi hchi hinitial
    hepsn hgap hW.le
  simpa only [b, m] using hpack

end RHTower
