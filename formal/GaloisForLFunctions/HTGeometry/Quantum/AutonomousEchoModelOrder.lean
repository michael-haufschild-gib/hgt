import GaloisForLFunctions.HTGeometry.Quantum.SpectralDetuningCoverage
import GaloisForLFunctions.RHTower.ExponentialSumMeanSquareLower

/-!
# The optimal autonomous echo of a local Hamiltonian

The echo-frequency distribution of a k-level simulator has a total excess
above unit atom height of at most k−1. Its squared mass therefore costs at
most D+k(k−1). Retaining k selected energies attains the ceiling.
-/

open scoped BigOperators Classical
open MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Mass of one frequency in the unnormalized trace of the relative evolution. -/
def echoAtom {I A : Type*} [Fintype I] [DecidableEq I]
    (E : I → ℝ) (V : Matrix.unitaryGroup I ℂ) (g : I → A) (F : A → ℝ) (d : ℝ) : ℝ :=
  ∑ i, ∑ j, if E i - F (g j) = d then Complex.normSq ((V : Matrix I I ℂ) i j) else 0

private theorem sum_echoAtom_eq_selected {I A : Type*} [Fintype I] [DecidableEq I]
    (E : I → ℝ) (V : Matrix.unitaryGroup I ℂ) (g : I → A) (F : A → ℝ) (s : Finset ℝ) :
    ∑ d ∈ s, echoAtom E V g F d = selectedEchoWeight E V g F (fun d : s => d.val) := by
  classical
  unfold echoAtom selectedEchoWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have he : (∃ b : s, E i = F (g j) + b.val) ↔ E i - F (g j) ∈ s := by
    constructor
    · rintro ⟨b, hb⟩
      rw [hb, add_sub_cancel_left]
      exact b.property
    · intro h
      exact ⟨⟨_, h⟩, by ring⟩
  simp only [he]
  rw [Finset.sum_ite_eq]

/-- The trace-frequency collision mass has a sharp ceiling determined by the
number of model energies. A singleton source atom accounts for one unit of
mass; all excess above singleton height shares one common budget. -/
theorem maximallyProjective_echoCollision_le {I : Type*} [Fintype I] [DecidableEq I]
    (E : I → ℝ) (hE : MaximallyProjectiveEnergy E) (k : ℕ)
    (V : Matrix.unitaryGroup I ℂ) (g : I → Fin (k+1)) (F : Fin (k+1) → ℝ)
    (s : Finset ℝ) :
    ∑ d ∈ s, (echoAtom E V g F d)^2 ≤ (Fintype.card I : ℝ) + (k+1 : ℝ)*k := by
  classical
  let w := echoAtom E V g F
  have hcover (t : Finset ℝ) (ht : t.Nonempty) :
      ∑ d ∈ t, w d ≤ t.card + (k : ℝ) := by
    letI : Nonempty t := ht.to_subtype
    rw [show (∑ d ∈ t, w d) = _ from sum_echoAtom_eq_selected E V g F t]
    apply (selectedEchoWeight_le_covered _ _ _ _ _).trans
    have h := maximallyProjective_detuningCoverage E hE F (fun x : t => x.val)
    simp only [Fintype.card_fin, Fintype.card_coe] at h
    have h' : Nat.card {i // ∃ a b, E i = F a + (b : t).val} ≤ t.card + k := by omega
    exact_mod_cast h'
  have hatom (d : ℝ) : w d ≤ k+1 := by
    have h := hcover {d} (Finset.singleton_nonempty _)
    simpa [add_comm] using h
  let heavy := s.filter (fun d => 1 < w d)
  have hexcess : ∑ d ∈ heavy, (w d - 1) ≤ k := by
    rcases heavy.eq_empty_or_nonempty with h | h
    · simp [h]
    · have h' := hcover heavy h
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      linarith only [h']
  have hterm (d : ℝ) :
      (w d)^2 ≤ w d + (k+1 : ℝ) * (if 1 < w d then w d-1 else 0) := by
    by_cases h : 1 < w d
    · rw [if_pos h]
      nlinarith only [mul_le_mul_of_nonneg_right (hatom d) (sub_nonneg.mpr h.le)]
    · rw [if_neg h]
      have hn : 0 ≤ w d := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
        split <;> first | exact Complex.normSq_nonneg _ | exact le_rfl
      nlinarith only [mul_nonneg hn (sub_nonneg.mpr (le_of_not_gt h))]
  have htotal : ∑ d ∈ s, w d ≤ (Fintype.card I : ℝ) := by
    rw [show (∑ d ∈ s, w d) = _ from sum_echoAtom_eq_selected E V g F s]
    exact (selectedEchoWeight_le_covered _ _ _ _ _).trans (by rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_subtype_le _)
  calc
    _ ≤ ∑ d ∈ s, (w d + (k+1 : ℝ) * (if 1 < w d then w d-1 else 0)) :=
      Finset.sum_le_sum fun d _ => hterm d
    _ = (∑ d ∈ s, w d) + (k+1 : ℝ) * ∑ d ∈ heavy, (w d-1) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_filter]
    _ ≤ _ := add_le_add htotal (mul_le_mul_of_nonneg_left hexcess (by positivity))

/-- Relative trace between the source and an arbitrary k-sector simulator,
written in the energy basis of the source. -/
def modelEchoTrace {I A : Type*} [Fintype I] [DecidableEq I]
    (E : I → ℝ) (V : Matrix.unitaryGroup I ℂ) (g : I → A) (F : A → ℝ) (t : ℝ) : ℂ :=
  Matrix.trace (Matrix.diagonal (fun i => Complex.exp (-Complex.I * (E i : ℂ) * t)) *
    ((V : Matrix I I ℂ) * Matrix.diagonal (fun j => Complex.exp (Complex.I * (F (g j) : ℂ) * t)) *
      star (V : Matrix I I ℂ)))

private def modelDetunings {I A : Type*} [Fintype I]
    (E : I → ℝ) (g : I → A) (F : A → ℝ) : Finset ℝ :=
  Finset.univ.image (fun p : I × I => E p.1 - F (g p.2))

private theorem diagonalTraceExpansion {I : Type*} [Fintype I] [DecidableEq I]
    (V : Matrix.unitaryGroup I ℂ) (u v : I → ℂ) :
    Matrix.trace (Matrix.diagonal u * ((V : Matrix I I ℂ) * Matrix.diagonal v *
        star (V : Matrix I I ℂ))) =
      ∑ i, ∑ j, u i * (((V : Matrix I I ℂ) i j * v j) * (starRingEnd ℂ) ((V : Matrix I I ℂ) i j)) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.star_apply, Complex.star_def, Finset.mul_sum]

private theorem modelEchoTrace_eq_modes {I A : Type*} [Fintype I] [DecidableEq I]
    (E : I → ℝ) (V : Matrix.unitaryGroup I ℂ) (g : I → A) (F : A → ℝ) (t : ℝ) :
    modelEchoTrace E V g F t = RHTower.expSum_exponentialSumMeanSquareLower
      (modelDetunings E g F) (fun d => (echoAtom E V g F d : ℂ)) id t := by
  classical
  unfold modelEchoTrace RHTower.expSum_exponentialSumMeanSquareLower
  rw [diagonalTraceExpansion]
  simp only [id_eq, echoAtom, Complex.ofReal_sum]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm (s := modelDetunings E g F)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm (s := modelDetunings E g F)]
  apply Finset.sum_congr rfl
  intro j _
  have hmem : E i - F (g j) ∈ modelDetunings E g F :=
    Finset.mem_image.mpr ⟨(i,j), Finset.mem_univ _, rfl⟩
  simp only [apply_ite, Complex.ofReal_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq_of_mem _ _ _ hmem, Complex.normSq_eq_conj_mul_self]
  have hphase :
      Complex.exp (-Complex.I * (E i : ℂ) * t) * Complex.exp (Complex.I * (F (g j) : ℂ) * t) =
        Complex.exp (-Complex.I * ((E i - F (g j) : ℝ) : ℂ) * t) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← hphase]
  ring

/-- Almost every ordinary nearest-neighbour chain has a completed-time trace
fidelity ceiling for every autonomous comparison with at most k+1 energies,
including eigenbases and comparison spectra selected after the draw. -/
theorem chainShell_modelEchoMean_ceiling_ae (n : ℕ) :
    ∀ᵐ θ ∂(shellProbability (Fin (Fintype.card (ChainLabel (n+3))))),
      ∀ k : ℕ, ∀ (V : Matrix.unitaryGroup (Fin (2^(n+3))) ℂ)
        (g : Fin (2^(n+3)) → Fin (k+1)) (F : Fin (k+1) → ℝ),
        ∃ L : ℝ, L ≤ (2^(n+3) : ℕ) + (k+1 : ℝ)*k ∧
          Tendsto (fun T : ℝ => (1/T) * ∫ t in (1 : ℝ)..T,
            ‖modelEchoTrace
              (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (n+3)) θ).eigenvalues
              V g F t‖^2) atTop (𝓝 L) := by
  filter_upwards [maximallyProjectiveEnergy_chainShell_ae n] with θ hθ
  intro k V g F
  let E := (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (n+3)) θ).eigenvalues
  let s := modelDetunings E g F
  refine ⟨∑ d ∈ s, (echoAtom E V g F d)^2, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using maximallyProjective_echoCollision_le E hθ k V g F s
  · have h := RHTower.tendsto_cesaro_normSq_expSum s
      (fun d => (echoAtom E V g F d : ℂ)) id (fun _ _ _ _ h => h)
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
    simpa only [modelEchoTrace_eq_modes, E, s] using h

#print axioms chainShell_modelEchoMean_ceiling_ae

/-- Retain each selected source level exactly and map all remaining levels to
one selected energy. This simulator uses only the selected energies. -/
def retainedLabel {I : Type*} [DecidableEq I] (s : Finset I) (a : s) (i : I) : s :=
  if h : i ∈ s then ⟨i,h⟩ else a

private theorem commutingEchoTrace {I A : Type*} [Fintype I] [DecidableEq I]
    (E : I → ℝ) (g : I → A) (F : A → ℝ) (t : ℝ) :
    modelEchoTrace E 1 g F t = ∑ i, Complex.exp (-Complex.I * ((E i - F (g i) : ℝ) : ℂ) * t) := by
  classical
  unfold modelEchoTrace
  simp only [OneMemClass.coe_one, star_one, one_mul, mul_one, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A commuting comparison attains the bound. Only simplicity of the source
is required for this construction. -/
theorem retainedModel_echoMean {I : Type*} [Fintype I] [DecidableEq I]
    (E : I → ℝ) (hE : Function.Injective E) (s : Finset I) (a : s) :
    Tendsto (fun T : ℝ => (1/T) * ∫ t in (1 : ℝ)..T,
      ‖modelEchoTrace E 1 (retainedLabel s a) (fun j : s => E j) t‖^2) atTop
      (𝓝 ((Fintype.card I : ℝ) + (s.card : ℝ) * (s.card-1 : ℝ))) := by
  classical
  let u := insert a.val sᶜ
  let c (i : I) : ℂ := if i = a.val then s.card else 1
  let om (i : I) := E i - E a.val
  have ha : a.val ∉ sᶜ := Finset.notMem_compl.mpr a.property
  have hlim := RHTower.tendsto_cesaro_normSq_expSum u c om
    (fun _ _ _ _ h => hE (sub_left_inj.mp h))
  have heq (t : ℝ) : modelEchoTrace E 1 (retainedLabel s a) (fun j : s => E j) t =
      RHTower.expSum_exponentialSumMeanSquareLower u c om t := by
    rw [commutingEchoTrace, ← Finset.sum_add_sum_compl s]
    unfold RHTower.expSum_exponentialSumMeanSquareLower
    rw [show u = insert a.val sᶜ from rfl, Finset.sum_insert ha]
    have hsel : ∀ i ∈ s, Complex.exp (-Complex.I *
        ((E i - E (retainedLabel s a i) : ℝ) : ℂ) * t) = 1 := by
      intro i hi
      simp [retainedLabel, hi]
    rw [Finset.sum_congr rfl hsel]
    simp only [c, om, if_pos rfl, sub_self, Complex.ofReal_zero, mul_zero, zero_mul,
      Complex.exp_zero, mul_one, Finset.sum_const, nsmul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have ho := Finset.mem_compl.mp hi
    have hn : i ≠ a.val := fun h => ho (h ▸ a.property)
    simp [retainedLabel, ho, hn]
  have hconst : ∑ i ∈ u, ‖c i‖^2 = (Fintype.card I : ℝ) + (s.card : ℝ) * (s.card-1 : ℝ) := by
    rw [show u = insert a.val sᶜ from rfl, Finset.sum_insert ha]
    have hone (i : I) (hi : i ∈ sᶜ) : ‖c i‖^2 = 1 := by
      have hn : i ≠ a.val := fun h => ha (h ▸ hi)
      simp [c, hn]
    rw [Finset.sum_congr rfl hone]
    simp only [c, if_pos rfl, Complex.norm_natCast, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ s)]
    ring
  rw [hconst] at hlim
  simpa only [heq] using hlim

#print axioms retainedModel_echoMean

end
end GaloisForLFunctions.HTGeometry
