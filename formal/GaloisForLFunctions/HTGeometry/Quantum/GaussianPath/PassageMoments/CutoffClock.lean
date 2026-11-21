import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.PrefixPhaseHorizon
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.TimedReflection
import GaloisForLFunctions.HTGeometry.NearHilbertContinuousCircuitEntropyLaw
import GaloisForLFunctions.HTGeometry.FintypeSortedSpectrum

/-! # Upper disorder tails of the actual first crossing and return at bounded coupling mass -/
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PassageMoments
noncomputable section
open PrescribedTimes

/-- Total absolute strength of the independent couplings. -/
def couplingMass {n : ℕ} (x : PrefixIndex n → ℝ) : ℝ := ∑ i, |x i|

/-- The larger of the first robust crossing date and the subsequent wait
until a return at the indicated gate budget. -/
def passageMax (k s : ℕ) (x : PrefixIndex (k+1) → ℝ) : ℝ :=
  let P := nearHilbertContinuousCircuitBudget (k+3)
  max (crossingOrigin (k+1) P (9/80) x) (crossingWait (k+1) P s x)

theorem measurable_passageMax (k s : ℕ) : Measurable (passageMax k s) :=
  (measurable_crossingOrigin _ _ _).max (measurable_crossingWait _ _ _)

theorem passageMax_nonneg (k s : ℕ) (x : PrefixIndex (k+1) → ℝ) : 0 ≤ passageMax k s x := by
  apply le_trans _ (le_max_right ..)
  obtain ⟨t,ht,_⟩ := (crossingWait_le_iff (k+1) (nearHilbertContinuousCircuitBudget (k+3)) s x _).mp le_rfl
  linarith only [ht.1,ht.2]

private theorem sorted_reindex {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}
    (e : ι ≃ Fin D) {A : Matrix ι ι ℂ} (h : A.IsHermitian) :
    sortedTuple (h.reindex e).eigenvalues = sortedTuple (h.eigenvalues ∘ e.symm) := by
  obtain rfl : D = Fintype.card ι := (Fintype.card_congr e).trans (Fintype.card_fin D) |>.symm
  exact sortedTuple_eigenvalues_reindex e h

private abbrev spectrum (k : ℕ) (x : PrefixIndex (k+1) → ℝ) :=
  (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k+3)) x).eigenvalues

/-- Sorting gives an exact correspondence between the laboratory spectrum
and the numbered matrix, even on a repeated eigenvalue. -/
private theorem spectral_labels (k : ℕ) (x : PrefixIndex (k+1) → ℝ) :
    let H := prefixGenerator (k+1) x
    ∃ e : (Fin (k+3) → Bool) ≃ Fin (2^(k+3)), H.2.isHermitian.eigenvalues ∘ e.symm =
      spectrum k x ∧ ∀ i, |spectrum k x i| ≤ couplingMass x := by
  classical
  intro H
  let n := k+1
  let q := qubitConfigFin (k+3)
  let u : PathShell n := WithLp.toLp 2 (fun l => x ((pathCoeffEquiv n).symm l))
  have hx : (fun i => u (pathCoeffEquiv n i)) = x := by
    funext i
    simp only [u,Equiv.symm_apply_apply]
  have hH : H.val = pathHamiltonian u := by
    change numberedGenerator n x = _
    simpa only [hx] using numberedGenerator_shell u
  have hre : Matrix.reindex q q H.val = spectralEnsembleMatrix (chainPauliFin (k+3)) x := by
    rw [hH]
    simpa only [hx] using reindex_pathHamiltonian u
  let raw := H.2.isHermitian.eigenvalues ∘ q.symm
  have he := sorted_reindex q H.2.isHermitian
  have hval := isHermitian_eigenvalues_congr (H.2.isHermitian.reindex q)
    (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian _) x) hre
  have eqv : sortedTuple (spectrum k x) = sortedTuple raw := (congrArg sortedTuple hval).symm.trans he
  let e := (q.trans (Tuple.sort raw).symm).trans (Tuple.sort (spectrum k x))
  have hlabel : H.2.isHermitian.eigenvalues ∘ e.symm = spectrum k x := by
    funext i
    have h := congrFun eqv ((Tuple.sort (spectrum k x)).symm i)
    simpa only [raw,e,sortedTuple,Function.comp_apply,Equiv.symm_trans_apply,Equiv.symm_symm,
      Equiv.apply_symm_apply] using h.symm
  refine ⟨e,hlabel,fun i => ?_⟩
  rw [←hlabel]
  apply (abs_eigenvalue_le_l2_opNorm H.2.isHermitian _).trans
  change ‖numberedGenerator n x‖ ≤ _
  unfold numberedGenerator
  apply (norm_sum_le _ _).trans_eq
  calc
    _ = ∑ l : PathLabel n, |x ((pathCoeffEquiv n).symm l)| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul,norm_finitePauliMatrix,Complex.norm_real,Real.norm_eq_abs,mul_one]
    _ = _ := Equiv.sum_comp (pathCoeffEquiv n).symm (fun i => |x i|)

/-- A clock on an energy cutoff bounds both stopping times on that very
draw. The exceptional set costs O(r), with constants depending on the prefix. -/
theorem gaussian_cutoff_first_passage :
    ∀ᶠ k : ℕ in atTop, ∀ s : ℕ, ∀ R r : ℝ, 0 ≤ R → 0 < r → r ≤ 1 →
      let e := prefixPhaseEnergyEquiv k
      let S := phaseClockModes e (1/80)
      let G := gaussianPhaseClock e (1/80) R r
      (Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1)
        {x | couplingMass x ≤ R ∧ G < passageMax k s x} ≤
        S.card*ENNReal.ofReal (2*((2^(k+3):ℕ).factorial:ℝ)*r) := by
  filter_upwards [(tendsto_add_atTop_nat 3).eventually eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier]
    with k hent
  intro s R r hR hr hr' e S G
  apply (measure_mono ?_).trans (gaussian_pauli_phase_clock_failure_le k _ e (ρ := 1/80)
    (by norm_num) (by linarith only [Real.pi_gt_three]) hR hr hr')
  rintro x ⟨hR',hlate⟩
  let H := prefixGenerator (k+1) x
  let P := nearHilbertContinuousCircuitBudget (k+3)
  let a := crossingOrigin (k+1) P (9/80) x
  obtain ⟨q,hlabel,hwidth⟩ := spectral_labels k x
  refine ⟨fun i => (hwidth i).trans hR',?_⟩
  intro allClocks
  let f := q.trans e
  have phase (u : ℝ) (c : Fin (2^(k+3)-1) → ℝ) : ∃ t ∈ Icc u (u+G), ∀ j,
      turnDist (t*RHTower.zeroProjectiveFrequency (H.2.isHermitian.eigenvalues ∘ f.symm) j-c j) < 1/80 := by
    have he : H.2.isHermitian.eigenvalues ∘ f.symm = spectrum k x ∘ e.symm :=
      congrArg (fun g => g ∘ e.symm) hlabel
    rw [he]
    exact allClocks (Equiv.refl _) u c
  obtain ⟨t,ht,hh,_⟩ := phase_horizon_reaches_robust_threshold (n := k+3) f H G (P := P) hent
    (fun c => by simpa only [zero_add,Function.comp_def] using phase 0 c)
  have hle : a ≤ t := csInf_le (show BddBelow {u : ℝ | 0 ≤ u ∧ (9/80:ℝ) ≤ pathGateDistance (k+1) P x u}
    from ⟨0,fun _ hu => hu.1⟩) ⟨ht.1,hh⟩
  obtain ⟨v,hv,z,hz,C,hC,herr⟩ := phase_interval_contains_zero_gate (n := k+3) f H a (a+G) (fun c => by simpa only [Function.comp_def] using phase a c)
  have hw := (crossingWait_le_iff (k+1) P s x G).mpr
    ⟨v,hv,(hasProjectiveCircuitApproximation_iff_infDist _ s _).mp ⟨z,hz,C,hC.trans (Nat.zero_le s),herr⟩⟩
  exact hlate.not_ge (max_le (hle.trans ht.2) hw)

#print axioms gaussian_cutoff_first_passage
end
end GaloisForLFunctions.HTGeometry.PassageMoments
