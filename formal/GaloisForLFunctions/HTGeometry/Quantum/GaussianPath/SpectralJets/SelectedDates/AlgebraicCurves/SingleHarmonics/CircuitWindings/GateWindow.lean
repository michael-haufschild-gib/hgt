import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings.PhysicalCenters
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings.TranslatedSpectators
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons.PhysicalScales

/-! # A finite circuit-net bound covering every time after an extremal antipode -/

open Real Set Filter MeasureTheory Matrix
open scoped ENNReal Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
open AntipodalHorizons SharpOccupation
noncomputable section

/-- A genuine physical budget visit in an interval of L spectral periods
whose initial displacement from the antipode is q₀ periods. -/
def gateWindow (k n s : ℕ) (q₀ L ε : ℝ) : Set PathPauliDisorder :=
  {ω | let u := pathPauliDisorderShell ω (k+1)
    let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) (fun l => u (pathCoeffEquiv (k+1) l))
    ∃ v∈Icc q₀ (q₀+L), HasProjectiveCircuitApproximation (k+3) ε s
      (unitaryEvolution (pathHamiltonian u) (date E (topLevel k) 0 n v))}

/-- Every net element imposes a single short-arc test at each of the
M+1 preceding mesh points. The tests all use the same Hamiltonian. -/
theorem gate_window_bound (k s M : ℕ) (q₀ : ℝ) {ε η δ : ℝ} (hε : 0<ε) (hη : 0<η)
    (he : ε+η<sqrt 2) (hd : 0<δ) (hr : physicalArc (ε+η)+δ≤1/2)
    (F : Finset (unitaryGroup (Fin (k+3)→Bool) ℂ))
    (hnet : ∀ C : TwoQubitCircuit (k+3), C.gateCount ≤ s → ∃ W ∈ F,
      ‖(C.eval:Register (k+3))-(W:Register (k+3))‖≤η)
    {b : ℝ≥0∞} (hb : let d := Fintype.card (Outside (topLevel k) 0)
      (d:ℝ≥0∞)*ENNReal.ofReal (physicalArc (ε+η)+δ)^(d-1)<b) :
    ∀ᶠ n : ℕ in atTop, pathPauliDisorderLaw (gateWindow k n s q₀ ((M:ℝ)*δ) ε) ≤
      (F.card:ℝ≥0∞)*((M+1:ℕ)*b) := by
  classical
  let i := topLevel k
  let j : Level k := 0
  have hji : j < i := top_pos k
  letI : Nonempty (Outside i j) := Fintype.card_pos_iff.mp (by
    rw [outside_card i j hji.ne.symm,Fintype.card_fin]
    have := Nat.lt_two_pow_self (n:=k+3)
    omega)
  let x := physicalArc (ε+η)
  have hεη : ε+η∈Ioo (0:ℝ) (sqrt 2) := ⟨add_pos hε hη,he⟩
  have hx := (physicalArc_spec hεη.1 hεη.2).1.1
  let r : Icc (0:ℝ) (1/2) := ⟨x+δ,add_nonneg hx.le hd.le,hr⟩
  let μ : ProbabilityMeasure (Coupling k) := ⟨centredProductGaussian _ 1,inferInstance⟩
  let X (ω : PathPauliDisorder) : Coupling k := fun l => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) l)
  let B (n : ℕ) (w : ↥F) (h : Fin (M+1)) : Set (Coupling k) :=
    {y | centerOffset i j (lineTurns k w.val.val y)+spectators k i j n (q₀+(h.val:ℝ)*δ) y∈enclosingUnitArc r}
  have htest (w : ↥F) (h : Fin (M+1)) : ∀ᶠ n : ℕ in atTop, (μ:Measure (Coupling k)) (B n w h)<b :=
    translated_spread_bound k i j hji.ne.symm μ (productGaussian_absolutelyContinuous _ one_ne_zero _)
      _ (measurable_centerOffset k w.val.val i j) _ r hb
  filter_upwards [eventually_all.mpr fun w => eventually_all.mpr (htest w)] with n hn
  have hsub : gateWindow k n s q₀ ((M:ℝ)*δ) ε ≤ᵐ[pathPauliDisorderLaw] ⋃ w, ⋃ h, X ⁻¹' B n w h := by
    filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hsimp hvisit
    let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) (X ω)
    let H := pathHamiltonian (pathPauliDisorderShell ω (k+1))
    obtain ⟨v,hv,c,hc,C,hC,heC⟩ := hvisit
    let t := date E i j n v
    obtain ⟨W,hW,hclose⟩ := hnet C hC
    have hfit : ‖unitaryEvolution H t-c • (W:Register (k+3))‖≤ε+η := by
      apply (norm_sub_le_norm_sub_add_norm_sub _ (c • (C.eval:Register (k+3))) _).trans
      rw [←smul_sub,norm_smul,hc,one_mul]
      exact add_le_add heC hclose
    have hcorr := physical_corrected_arc k ω W.val W.property t hc hεη (hsimp k).injective hfit
    obtain ⟨p,hp⟩ := physical_sorted_order k ω (hsimp k).injective
    have hsimple : Function.Injective E := by
      intro a b hh
      apply p.symm.injective
      apply (hsimp k).injective
      rw [hp,hp,p.apply_symm_apply,p.apply_symm_apply]
      exact hh
    have hg : E j < E i := lt_of_le_of_ne (monotone_sortedTuple _ hji.le) (hsimple.ne hji.ne)
    have hall (l : Level k) : E j≤E l ∧ E l≤E i := by
      refine ⟨monotone_sortedTuple _ (Fin.zero_le _),monotone_sortedTuple _ ?_⟩
      change l.val≤2^(k+3)-1
      have := l.isLt
      omega
    have hrel : v-q₀∈Icc (0:ℝ) ((M:ℝ)*δ) := ⟨sub_nonneg.mpr hv.1,by linarith only [hv.2]⟩
    obtain ⟨h,hh,hh'⟩ := preceding_grid_point M hd hrel
    exact mem_iUnion.mpr ⟨⟨W,hW⟩,mem_iUnion.mpr ⟨h,
      centered_prior_spread k i j (X ω) (lineTurns k W.val (X ω)) n hx.le
        (show q₀+(h.val:ℝ)*δ≤v by linarith only [hh])
        (by linarith only [hh']) hg hall hcorr⟩⟩
  apply (measure_mono_ae hsub).trans
  apply (measure_iUnion_fintype_le _ _).trans
  calc ∑ w, pathPauliDisorderLaw (⋃ h, X ⁻¹' B n w h) ≤ ∑ w, ∑ h, pathPauliDisorderLaw (X ⁻¹' B n w h) :=
         Finset.sum_le_sum fun w _ => measure_iUnion_fintype_le _ _
       _ ≤ ∑ _ : ↥F, ∑ _ : Fin (M+1), b := Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun h _ =>
         ((gaussian_pauli_prefix_coordinates_law (k+1)).measure_preimage_le (B n w h)).trans (hn w h).le
       _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Fintype.card_coe,nsmul_eq_mul]

#print axioms gate_window_bound
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
