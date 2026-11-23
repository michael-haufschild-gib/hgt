import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IsolatedFieldApproximation
import GaloisForLFunctions.HTGeometry.DiagonalRotationCompiler

/-! # All magnetizations of an isolated longitudinal packet -/
open Matrix Finset
namespace GaloisForLFunctions.HTGeometry.MaximalError
noncomputable section

/-- A packet of m equal fields has one computational phase for each
Hamming weight j from zero through m, regardless of all outside bits. -/
theorem packet_weight_phase {n : ℕ} (S : Finset (Fin (n+2))) (q t : ℝ) {j : ℕ} (hj : j ≤ S.card) :
    ∃ w, (unitaryEvolution (pathHamiltonian (longitudinalPacket S q)) t) w w =
      Complex.exp (((-(t*(q*((S.card:ℝ)-2*j))):ℝ):ℂ)*Complex.I) := by
  classical
  obtain ⟨J,hsub,hcard⟩ := exists_subset_card_eq hj
  let w (i : Fin (n+2)) := decide (i ∈ J)
  let u := longitudinalPacket S q
  have hdiag : ∀ l : PathLabel n, ¬IsDiagLabel l → u l=0 := by
    rintro (⟨i,a⟩|e) hl
    · change a≠2 at hl
      simp [u,longitudinalPacket,hl]
    · rfl
  have he (i : Fin (n+2)) :
      u (.inl (i,2))*zSetSign {i} w =
        (if i ∈ S then q else 0) - (if i ∈ J then 2*q else 0) := by
    by_cases hi : i∈J
    · simp [u,longitudinalPacket,zSetSign_singleton,w,hi,hsub hi]
      ring
    · simp [u,longitudinalPacket,zSetSign_singleton,w,hi]
  have hn : pathDiagEnergy u w=q*((S.card:ℝ)-2*j) := by
    simp only [pathDiagEnergy,he,show ∀ e : Fin (n+1), u (.inr (e,2,2))=0 from fun _ => rfl,
      zero_mul,sum_const_zero,add_zero,sum_sub_distrib]
    simp only [←sum_filter,filter_mem_eq_inter,univ_inter,sum_const,nsmul_eq_mul,hcard]
    ring
  refine ⟨w,?_⟩
  change (unitaryEvolution (pathHamiltonian u) t) w w=_
  rw [pathHamiltonian_eq_diagonal _ hdiag,unitaryEvolution_diagonal_phase,diagonal_apply_eq,hn]

#print axioms packet_weight_phase
end
end GaloisForLFunctions.HTGeometry.MaximalError
