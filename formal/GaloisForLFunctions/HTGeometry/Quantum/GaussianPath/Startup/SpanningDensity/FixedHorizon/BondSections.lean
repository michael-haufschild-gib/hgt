import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.AffineSignal
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.BondCalibration
import GaloisForLFunctions.HTGeometry.PauliOperatorNormSandwich

/-! # Detectable path-bond correlations conditional on every exterior -/
open Matrix MeasureTheory ProbabilityTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section
variable {n : ℕ}

/-- Local coordinates are numbered only within the interactions meeting this bond. -/
def localLabels (e : Fin (n+1)) := pathOverlaps (bondLabel e)

def localNumbering (e : Fin (n+1)) : Fin (localLabels e).card ≃ ↥(localLabels e) :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe _)).symm

private theorem central_mem (e : Fin (n+1)) : bondLabel e ∈ localLabels e := by
  apply mem_pathOverlaps.mpr
  apply Finset.not_disjoint_iff.mpr
  have h : e.castSucc ∈ labelSupport (pathWord (bondLabel e)) := by
    rw [mem_labelSupport]
    simp [bondLabel,pathWord,couplingWord]
  exact ⟨_,h,h⟩

/-- On every fixed positive time interval the chance of a near-zero bond
correlation can be made arbitrarily small by a threshold common to all
chain lengths, bonds, and fixed exterior coefficients. -/
theorem gaussian_bond_sections {a T η : ℝ} (ha : 0<a) (hη : 0<η) :
    ∃ r : ℝ, 0<r ∧ ∀ (n : ℕ) (e : Fin (n+1)) (u : PathShell n) (t : ℝ),
      t∈Set.Icc a T →
      let H := pathHamiltonian (exteriorShell u e)
      let P := finitePauliMatrix (pathWord (bondLabel e))
      let Y := finitePauliMatrix (bondReporter e)
      let S := fun i => finitePauliMatrix (pathWord ((localNumbering e i).val))
      (Measure.pi (fun _ : Fin (localLabels e).card => gaussianReal 0 1))
        {x | |signal (affineHamiltonian H S x) Y (Complex.I • (P*Y)) t|≤r} ≤ ENNReal.ofReal η := by
  classical
  let A := π/(4*a)
  choose r hr h using fun m => affine_gaussian_signal (a:=A) (h:=1) (T:=T) m zero_lt_one hη
  let I := Finset.range 43
  have hI : I.Nonempty := ⟨0,by decide⟩
  refine ⟨I.inf' hI r,(Finset.lt_inf'_iff hI).mpr (fun i _ => hr i),?_⟩
  intro n e u t ht H P Y S
  let m := (localLabels e).card
  let q := (localNumbering e).symm ⟨bondLabel e,central_mem e⟩
  let v (i : Fin m) : ℝ := if i=q then π/(4*t) else 0
  have ht' : 0<t := ha.trans_le ht.1
  have hv (i : Fin m) : |v i|≤A := by
    by_cases hi : i=q
    · rw [v,if_pos hi,abs_of_pos (by positivity)]
      exact div_le_div_of_nonneg_left pi_pos.le (by positivity) (mul_le_mul_of_nonneg_left ht.1 (by norm_num))
    · simp only [v,if_neg hi,abs_zero]
      exact div_nonneg pi_pos.le (by positivity)
  have hq : S q=P := by
    change finitePauliMatrix (pathWord (((localNumbering e) ((localNumbering e).symm _)).val))=_
    rw [Equiv.apply_symm_apply]
  have hK : affineHamiltonian H S v=H+((π/(4*t):ℝ):ℂ) • P := by
    unfold affineHamiltonian
    rw [Finset.sum_eq_single q]
    · simp only [v,if_pos rfl,hq]
    · intro i _ hi
      simp only [v,if_neg hi,Complex.ofReal_zero,zero_smul]
    · simp
  have hsig : 1≤|signal (affineHamiltonian H S v) Y (Complex.I • (P*Y)) t| := by
    rw [hK]
    have hc := congrArg Complex.re (path_bond_calibration u e t ht'.ne').2
    change signal (H+((π/(4*t):ℝ):ℂ) • P) Y (Complex.I • (P*Y)) t=1 at hc
    rw [hc,abs_one]
  have hY : Y.IsHermitian := finitePauliMatrix_isHermitian (bondReporter e)
  have hP : P.IsHermitian := finitePauliMatrix_isHermitian (pathWord (bondLabel e))
  have haP : P*Y=-(Y*P) := bond_reporter_anticommutes e
  have he : Y*P=-(P*Y) := by rw [haP,neg_neg]
  have hB : (Complex.I • (P*Y)).IsHermitian := by
    change (Complex.I • (P*Y))ᴴ=_
    rw [Matrix.conjTranspose_smul,Matrix.conjTranspose_mul,hY.eq,hP.eq,he,Complex.star_def,Complex.conj_I,neg_smul,smul_neg,neg_neg]
  have hnP : ‖P‖=1 := norm_finitePauliMatrix _
  have hnY : ‖Y‖=1 := norm_finitePauliMatrix _
  have hnB : ‖Complex.I • (P*Y)‖≤1 := by
    rw [norm_smul,Complex.norm_I,one_mul]
    exact (norm_mul_le _ _).trans (by rw [hnP,hnY,one_mul])
  have hb := h m (Fin (n+2) → Bool) H Y (Complex.I • (P*Y)) S
    (isSelfAdjoint_pathHamiltonian _) hY hB hnY.le hnB
    (fun i => (finitePauliMatrix_isHermitian _).isSelfAdjoint) (fun i => (norm_finitePauliMatrix _).le)
    t (by simpa only [abs_of_pos ht'] using ht.2) v hv hsig
  have hm : m∈I := Finset.mem_range.mpr (Nat.lt_succ_of_le (pathOverlaps_card_le _))
  exact (measure_mono fun x hx => hx.trans (Finset.inf'_le r hm)).trans hb

#print axioms gaussian_bond_sections
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
