import GaloisForLFunctions.HTGeometry.OuterShiftObservation
import GaloisForLFunctions.HTGeometry.StratifiedParametricAvoidance
import GaloisForLFunctions.HTGeometry.RegularLevelSetLinearEquiv
import GaloisForLFunctions.HTGeometry.ProjectiveIncidenceHausdorffDimension
import GaloisForLFunctions.HTGeometry.JetPacketReindex

/-!
# Parametric avoidance for the shifted outer observation

The rank-defect locus of the expanded evaluation matrix carries an unconditional finite regular
stratification of real codimension `2 (rows - columns - degree + 1)`.  Transported to the
sigma-indexed jet coordinates by the fold, it is still stratified, and it is closed.

The observation is smooth and submersive in the mass parameter, so as soon as the shift space has
dimension below that codimension, parametric transversality makes the mass parameters whose whole
compact shift patch avoids the rank defect dense.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Spanning by a fixed finite family is an open condition. -/
theorem isOpen_setOf_span_eq_top {H Y : Type*} [TopologicalSpace H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] {N : ℕ}
    (col : Fin N → H → Y) (hcol : ∀ l, Continuous (col l)) :
    IsOpen {h : H | Submodule.span ℝ (Set.range fun l => col l h) = ⊤} := by
  rw [isOpen_iff_mem_nhds]
  intro h₀ hh₀
  obtain ⟨U, V, hUopen, hhU, -, hVU⟩ :=
    exists_local_finiteProbe_of_continuous_surjectiveControl
      (fun h => columnControl fun l => col l h)
      (continuous_columnControl col hcol) h₀
      ((surjective_columnControl_iff _).mpr hh₀)
  refine Filter.mem_of_superset (hUopen.mem_nhds hhU) fun h hh => ?_
  refine (surjective_columnControl_iff _).mp fun y => ?_
  obtain ⟨v, hv⟩ := hVU h hh y
  exact ⟨v.1, hv⟩

/-- The fold of the sigma-indexed jet coordinates, as a continuous linear equivalence. -/
def sigmaJetCLE (row : Type) [Fintype row] (r d D : ℕ) (h : r * (d + 1) = D) :
    ((Σ _ : row × Fin r, Fin (d + 1)) → ℂ) ≃L[ℝ] ((row × Fin D) → ℂ) :=
  (LinearEquiv.funCongrLeft ℝ ℂ
    (sigmaJetIndexEquiv (row := row) r d D h)).symm.toContinuousLinearEquiv

/-- The rank-defect locus read in the sigma-indexed jet coordinates. -/
def outerShiftBad (row : Type) [Fintype row] {κ : Type} [Fintype κ] [DecidableEq κ]
    (r d D q : ℕ) (h : r * (d + 1) = D) (z : row → ℂ) (exponent : κ → (Fin D →₀ ℕ)) :
    Set ((Σ _ : row × Fin r, Fin (d + 1)) → ℂ) :=
  (sigmaJetCLE row r d D h) ⁻¹' (expandedDifferentialEvaluationRankDefect q D z exponent)

theorem isClosed_outerShiftBad (row : Type) [Fintype row] {κ : Type} [Fintype κ] [DecidableEq κ]
    (r d D q : ℕ) (h : r * (d + 1) = D) (z : row → ℂ) (exponent : κ → (Fin D →₀ ℕ)) :
    IsClosed (outerShiftBad row r d D q h z exponent) :=
  (expandedDifferentialEvaluationRankDefect_isClosed q D z exponent).preimage
    (sigmaJetCLE row r d D h).continuous

/-- **The transported rank defect is still stratified.** -/
noncomputable def outerShiftBad_finiteRegularStratification (row : Type) [Fintype row]
    [DecidableEq row] {κ : Type} [Fintype κ] [DecidableEq κ]
    (r d D q : ℕ) (h : r * (d + 1) = D) {z : row → ℂ} (hz : Function.Injective z)
    {exponent : κ → (Fin D →₀ ℕ)} (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (q + 1)) + q < Fintype.card row) :
    FiniteRegularStratification (outerShiftBad row r d D q h z exponent)
      (2 * (Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1)) := by
  have himg : outerShiftBad row r d D q h z exponent
      = (sigmaJetCLE row r d D h).symm ''
        (expandedDifferentialEvaluationRankDefect q D z exponent) := by
    ext y
    constructor
    · intro hy
      exact ⟨sigmaJetCLE row r d D h y, hy, (sigmaJetCLE row r d D h).symm_apply_apply y⟩
    · rintro ⟨v, hv, rfl⟩
      show sigmaJetCLE row r d D h ((sigmaJetCLE row r d D h).symm v)
          ∈ expandedDifferentialEvaluationRankDefect q D z exponent
      rwa [(sigmaJetCLE row r d D h).apply_symm_apply]
  rw [himg]
  exact (expandedDifferentialEvaluationRankDefect_finiteRegularStratification_unconditional
    q D z hz exponent hexponent hrows).image_continuousLinearEquiv _

/-- **Parametric avoidance for the shifted outer observation.**  Below the codimension of the
rank-defect locus, the mass parameters whose whole compact shift patch stays at full evaluation rank
are dense. -/
theorem dense_avoidance_outerShiftObservation {row : Type} [Fintype row] [DecidableEq row]
    {κ : Type} [Fintype κ] [DecidableEq κ] {z : row → ℂ} (hzinj : Function.Injective z)
    (hupper : ∀ b, 0 < (z b).im) {r d D q : ℕ} (hD : r * (d + 1) = D)
    {exponent : κ → (Fin D →₀ ℕ)} (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (q + 1)) + q < Fintype.card row)
    (hdim : r < 2 * (Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1))
    (x : ℕ → ℝ) {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (hsum : Summable w)
    {K : ℕ} {a : Fin K → ℕ} (ha : Function.Injective a)
    {carrier : (Fin r → ℝ) → ((Σ _ : row × Fin r, Fin (d + 1)) → ℂ)}
    (hcarrier : ContDiff ℝ (⊤ : ℕ∞) carrier)
    {Kset : Set (Fin r → ℝ)}
    (hspan : ∀ t ∈ Kset, Submodule.span ℝ (Set.range fun l =>
      massJetColumn (combinedNodes z t) (fun _ : row × Fin r => d + 1) x w (a l)) = ⊤) :
    Dense (compactConfigurationAvoidance (outerShiftObservation z d x w a carrier)
      (outerShiftBad row r d D q hD z exponent) Kset) := by
  classical
  set U : Set (Fin r → ℝ) := {t | Submodule.span ℝ (Set.range fun l =>
    massJetColumn (combinedNodes z t) (fun _ : row × Fin r => d + 1) x w (a l)) = ⊤} with hUdef
  have hUopen : IsOpen U := by
    refine isOpen_setOf_span_eq_top
      (fun l t => massJetColumn (combinedNodes z t) (fun _ : row × Fin r => d + 1) x w (a l))
      fun l => ?_
    refine continuous_pi fun u => ?_
    exact (contDiff_massJetColumn hupper (fun _ : row × Fin r => d + 1) x w (a l) u).continuous
  have hKU : Kset ⊆ U := hspan
  have hfinrank : Module.finrank ℝ (Fin r → ℝ) = r := by
    simp
  refine compactConfigurationAvoidance_dense_of_finiteRegularStratification
    (outerShiftObservation z d x w a carrier) (outerShiftBad row r d D q hD z exponent)
    (2 * (Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1)) U Kset hUopen hKU
    (contDiffOn_outerShiftObservation hupper d x hw hsum ha hcarrier)
    (fun p t ht => surjective_fderiv_param_outerShiftObservation hupper d x hw hsum ha carrier
      t p ht)
    (outerShiftBad_finiteRegularStratification row r d D q hD hzinj hexponent hrows) ?_
  rw [hfinrank]
  exact hdim

end

end GaloisForLFunctions.HTGeometry
