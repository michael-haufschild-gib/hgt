import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.HiddenRotatedIsingTube

/-! # Rotating a longitudinal Gaussian sector into strong laboratory coordinates -/

open Set MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open AccuracyScales.TenthPlateau PrescribedTimes DiagonalSynthesis
open private pythUnitary_mem_unitary realizes_conj_pyth prodPyth_conj_pathHamiltonian
  pythShellMap_allCoordStrong pythShellMap_measurePreserving pythShellInv_left pythShellInv_right
  from GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.HiddenRotatedIsingTube

noncomputable section
variable {n : ℕ}

/-- Conjugating each circuit gate on its two wires preserves both gate
budget and projective error for the rotated Hamiltonian. -/
theorem rotated_increment_fit {x : PathLabel n → ℝ} {ε t : ℝ} {B : ℕ}
    (h : HasProjectiveCircuitApproximation (n+2) ε B
      (unitaryEvolution (pathHamiltonian (WithLp.toLp 2 x : PathShell n)) t)) :
    HasProjectiveCircuitApproximation (n+2) ε B
      (unitaryEvolution (pathHamiltonian (WithLp.toLp 2 (pythShellMap n x))) t) := by
  let u : PathShell n := WithLp.toLp 2 x
  let W := prodLocalMatrix (fun _ : Fin (n+2) => pythUnitary)
  have hW : W ∈ unitary (Register (n+2)) :=
    prodLocalMatrix_mem_unitary _ fun _ => pythUnitary_mem_unitary
  let V : Matrix.unitaryGroup (Fin (n+2) → Bool) ℂ := ⟨W,hW⟩
  have hev := unitaryEvolution_conj W (pathHamiltonian u) (Unitary.isUnit_coe (U:=V)) t
  rw [inv_eq_star_of_mem_unitary hW,prodPyth_conj_pathHamiltonian u] at hev
  obtain ⟨z,hz,C,hC,hfit⟩ := h
  have hr : Realizes B (z • C.eval.val) := ⟨z,hz,C,hC,rfl⟩
  obtain ⟨a,ha,D,hD,hrot⟩ := realizes_conj_pyth hr
  refine ⟨a,ha,D,hD,?_⟩
  rw [←hrot,hev,←Matrix.sub_mul,←Matrix.mul_sub,l2_opNorm_unitary_conj_eq hW]
  exact hfit

private theorem rotate_scale (x : PathLabel n → ℝ) (c : ℝ) (l : PathLabel n) :
    pythShellMap n (fun j => c*x j) l = c*pythShellMap n x l := by
  rcases l with ⟨i,a⟩ | ⟨e,⟨a,b⟩⟩
  · simp only [pythShellMap,Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  · simp only [pythShellMap,Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The nonzero third column of the rotation gives every onsite and
bond coefficient magnitude at least one hundredth. -/
theorem rotated_coordinates_strong {x : PathLabel n → ℝ}
    (hd : ∀ l, IsDiagLabel l → 1/2 < x l)
    (ho : ∀ l, ¬IsDiagLabel l → |x l| ≤ 1/20000) :
    (fun i => pythShellMap n x (pathCoeffEquiv n i)) ∈ allCoordStrongEvent n (1/100) := by
  have h := pythShellMap_allCoordStrong (n:=n) (η:=1) (M_η:=27) (δ:=1/200)
    (u_tilde:=fun l => 100*x l) (by norm_num) (by norm_num) le_rfl
    (fun l hl => by linarith only [hd l hl]) (fun l hl => by
      rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 100)]
      linarith only [ho l hl])
  intro i
  have hi := h.1 i
  change 1 ≤ |pythShellMap n (fun l => 100*x l) (pathCoeffEquiv n i)| at hi
  rw [rotate_scale,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 100)] at hi
  change 1/100 ≤ |pythShellMap n x (pathCoeffEquiv n i)|
  linarith only [hi]

/-- The coordinate rotation transports a measurable Gaussian sector
without changing its probability. -/
theorem rotated_sector {E : Set (PathLabel n → ℝ)} (hE : MeasurableSet E) :
    let μ := Measure.pi (fun _ : PathLabel n => gaussianReal 0 1)
    ∃ F : Set (PathLabel n → ℝ), MeasurableSet F ∧ μ.real F = μ.real E ∧
      ∀ x ∈ F, ∃ y ∈ E, pythShellMap n y = x := by
  intro μ
  let F := pythShellInv n ⁻¹' E
  have hInv : Measurable (pythShellInv n) := by
    refine measurable_pi_lambda _ fun l => ?_
    rcases l with ⟨i,b⟩ | ⟨e,⟨a,b⟩⟩
    · exact Finset.measurable_sum _ fun _ _ => measurable_const.mul (measurable_pi_apply _)
    · exact Finset.measurable_sum _ fun _ _ => Finset.measurable_sum _ fun _ _ =>
        measurable_const.mul (measurable_pi_apply _)
  have hF : MeasurableSet F := hE.preimage hInv
  have hpre : pythShellMap n ⁻¹' F = E := by
    ext x
    change pythShellInv n (pythShellMap n x) ∈ E ↔ x ∈ E
    rw [pythShellInv_left]
  refine ⟨F,hF,?_,fun x hx => ⟨_,hx,pythShellInv_right n x⟩⟩
  have hm := (pythShellMap_measurePreserving n).measure_preimage hF.nullMeasurableSet
  rw [hpre] at hm
  exact (congrArg ENNReal.toReal hm).symm

#print axioms rotated_increment_fit
#print axioms rotated_coordinates_strong
#print axioms rotated_sector
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
