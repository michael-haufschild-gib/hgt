import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.ConnectedGates.CutMinor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.ConnectedGates.BondFlip
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.BondStep

/-! # Exact short-time gate count at intermediate precision -/
open Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ConnectedGates
noncomputable section

/-- A circuit below the connected budget misses at least one physical
bond's flip amplitude. The quadratic remainder is uniform in the
architecture, phase and signed time. -/
theorem bond_flip_error_floor {n : ℕ} (H : Register (n+2)) (hH : IsSelfAdjoint H)
    (t : ℝ) (C : TwoQubitCircuit (n+2)) (hC : C.gateCount<n+1) (z : ℂ) (hz : ‖z‖=1)
    (δ : ℝ) (hδ : ∀ x, ‖(unitaryEvolution H t-z • C.eval.val) x (fun _ => false)‖ ≤ δ) :
    ∃ e : Fin (n+1), |t| * ‖H (corner e.castSucc e.succ true true) (fun _ => false)‖ ≤
      4*δ+(5/2)*(|t| * ‖H‖)^2 := by
  obtain ⟨e,he⟩ := disconnected_minor C hC z
  refine ⟨e,?_⟩
  let U := unitaryEvolution H t
  let V := z • C.eval.val
  let a := ((t:ℂ)*(-Complex.I))*H (corner e.castSucc e.succ true true) (fun _ => false)
  let f := amplitudeMinor e.castSucc e.succ U
  have hU : ‖U‖≤1 := (CStarRing.norm_of_mem_unitary (unitaryEvolution_mem_unitary hH t)).le
  have hV : ‖V‖≤1 := by rw [show ‖V‖=‖z‖*‖C.eval.val‖ from norm_smul ..,hz,CStarRing.norm_of_mem_unitary C.eval.2,one_mul]
  have hsmall := minor_column_error e.castSucc e.succ U V hU hV δ hδ
  rw [show amplitudeMinor e.castSucc e.succ V=0 from he,sub_zero] at hsmall
  have hlin : ‖f-a‖≤(5/2)*(|t| * ‖H‖)^2 := minor_linear_error _ _ (BondProducts.endpoints_ne e) H hH t
  have ha : ‖a‖=|t| * ‖H (corner e.castSucc e.succ true true) (fun _ => false)‖ := by
    dsimp only [a]
    rw [norm_mul,norm_mul,norm_neg,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  calc _ = ‖f-(f-a)‖ := by rw [←ha]; congr 1; abel
       _ ≤ ‖f‖+‖f-a‖ := norm_sub_le _ _
       _ ≤ _ := add_le_add hsmall hlin

/-- The lower bound already holds for preparing one state, measured by
entrywise error on the all-zero input column. The upper bound
approximates the full unitary and works at every signed time. -/
theorem gaussian_minimum_bond_count :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n,
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∃ A c : ℝ, 0<A ∧ 0<c ∧
        (∀ t : ℝ, HasProjectiveCircuitApproximation (n+2) (A*t^2) (n+1) (unitaryEvolution H t)) ∧
        ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ C : TwoQubitCircuit (n+2), C.gateCount<n+1 → ∀ z : ℂ, ‖z‖=1 →
          ∃ x : Bits (n+2), c*|t| < ‖(unitaryEvolution H t-z • C.eval.val) x (fun _ => false)‖ := by
  filter_upwards [gaussian_bond_flip] with ω hω n
  intro H
  let k (e : Fin (n+1)) := ‖H (corner e.castSucc e.succ true true) (fun _ => false)‖
  let m := Finset.univ.inf' Finset.univ_nonempty k
  have hm : 0 < m := (Finset.lt_inf'_iff _).mpr fun e _ => norm_pos_iff.mpr (hω n e)
  obtain ⟨K,hK,hfit⟩ := BondProducts.exists_bond_step (pathPauliDisorderShell ω n)
  refine ⟨K+1,m/8,by linarith only [hK],by positivity,?_,?_⟩
  · intro t
    obtain ⟨z,hz,C,hC,he⟩ := hfit t
    exact ⟨z,hz,C,hC.le,he.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))⟩
  · have hmin (e : Fin (n+1)) := eventual_minor_lower e.castSucc e.succ
      (BondProducts.endpoints_ne e) H (isSelfAdjoint_pathHamiltonian _) (hω n e)
    filter_upwards [eventually_all.mpr hmin] with t ht
    intro C hC z hz
    obtain ⟨e,he⟩ := disconnected_minor C hC z
    let U := unitaryEvolution H t
    let V := z • C.eval.val
    have hu : ‖U‖≤1 := (CStarRing.norm_of_mem_unitary (unitaryEvolution_mem_unitary
      (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)) t)).le
    have hv : ‖V‖≤1 := by rw [show ‖V‖=‖z‖*‖C.eval.val‖ from norm_smul ..,hz,CStarRing.norm_of_mem_unitary C.eval.2,one_mul]
    by_contra! hsmall
    have hb := minor_column_error e.castSucc e.succ U V hu hv _ hsmall
    rw [show amplitudeMinor e.castSucc e.succ V=0 from he,sub_zero] at hb
    have he' : k e/2*|t| < ‖amplitudeMinor e.castSucc e.succ U‖ := ht e
    have hm' : m*|t| ≤ k e*|t| := mul_le_mul_of_nonneg_right
      (Finset.inf'_le k (Finset.mem_univ e)) (abs_nonneg _)
    linarith only [he',hb,hm']

#print axioms gaussian_minimum_bond_count
end
end GaloisForLFunctions.HTGeometry.ConnectedGates
