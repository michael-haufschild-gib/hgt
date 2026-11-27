import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.MarkedReflections.MarkedMass
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.MarkedReflections.ProjectionAngle

/-! # Exact spectral-phase feasibility for a reflection about one ray -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation.MarkedReflections
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ
local instance : CStarAlgebra (Mat I) where

private def atom (j : I) : Mat I := diagonal fun a => if a=j then 1 else 0

omit [Nonempty I] in
private theorem compress_atom (i : I) (A : Mat I) : atom i*A*atom i=A i i • atom i := by
  ext a b
  by_cases ha : a=i <;> by_cases hb : b=i <;>
    simp_all [atom,Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.diagonal_apply,Matrix.smul_apply]
  exact fun h => (hb h.symm).elim

private theorem atom_square (i : I) : atom i*atom i=atom i := by
  have h := compress_atom i (1:Mat I)
  simpa only [mul_one,Matrix.one_apply_eq,one_smul] using h

omit [Fintype I] [Nonempty I] in
private theorem atom_star (i : I) : star (atom i)=atom i := by
  ext a b
  by_cases hab : a=b
  · subst b
    by_cases ha : a=i <;> simp [atom,ha]
  · simp [atom,hab,Ne.symm hab]

omit [Nonempty I] in
private theorem atom_diagonal (V : Mat I) (i j : I) :
    (V*atom j*star V) i i=(‖V i j‖^2:ℝ) := by
  rw [Matrix.mul_apply]
  simp [atom,Matrix.mul_diagonal,mul_ite,ite_mul,Complex.mul_conj',Complex.ofReal_pow]

omit [Fintype I] [Nonempty I] in
private theorem flip_eq (i : I) : diagonal (markSign {i})=1-(2:ℝ) • atom i := by
  ext a b
  by_cases hab : a=b
  · subst b
    by_cases ha : a=i <;> norm_num [atom,markSign,ha]
  · simp [atom,hab]

/-- Flipping one energy coordinate approximates the ray reflection with
squared error at most four times the infidelity of that coordinate. -/
theorem ray_flip_bound (V : unitaryGroup I ℂ) (i j : I) :
    ‖diagonal (markSign {i})-reflection V {j}‖^2 ≤ 4*(1-‖V.val i j‖^2) := by
  let Q := atom i
  let P := V.val*atom j*star V.val
  let p := ‖V.val i j‖^2
  have hV := Unitary.mem_iff.mp V.property
  have hp : p≤1 := by
    have h := (norm_entry_le_l2_opNorm V.val i j).trans_eq (CStarRing.norm_of_mem_unitary V.property)
    exact pow_le_one₀ (norm_nonneg _) h
  have hPP : P*P=P := by
    calc _ = V.val*(atom j*(star V.val*V.val)*atom j)*star V.val := by simp only [P,mul_assoc]
         _ = _ := by rw [hV.1,mul_one,atom_square]
  have hPs : star P=P := by simp only [P,star_mul,star_star,atom_star,mul_assoc]
  have hQP : Q*P*Q=p • Q := by
    rw [show Q*P*Q=P i i • Q from compress_atom i P,show P i i=(p:ℂ) from atom_diagonal _ _ _,Complex.coe_smul]
  have hj : (star V.val*Q*V.val) j j=(p:ℂ) := by
    have h := atom_diagonal (star V.val) j i
    rw [star_star] at h
    simpa only [Q,p,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,norm_star] using h
  have hPQ : P*Q*P=p • P := by
    calc _ = V.val*(atom j*(star V.val*Q*V.val)*atom j)*star V.val := by simp only [P,mul_assoc]
         _ = _ := by rw [compress_atom,hj,Complex.coe_smul,Matrix.mul_smul,Matrix.smul_mul]
  have he := projection_angle P Q hPP (atom_square i) hPs (atom_star i) hp hPQ hQP
  have href : reflection V {j}=1-(2:ℝ) • P := by
    rw [reflection,flip_eq,Matrix.mul_sub,Matrix.sub_mul,mul_one,hV.2,Matrix.mul_smul,Matrix.smul_mul]
  rw [href,flip_eq,show 1-(2:ℝ) • atom i-(1-(2:ℝ) • P)=(2:ℝ) • (P-Q) by
    rw [smul_sub]; dsimp only [Q]; abel,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2),mul_pow]
  exact (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤2^2)).trans_eq (by norm_num [p])

/-- A marked ray can be fitted by spectral phases at error e exactly when
the scalar quarter turn fits, or a single energy level has fidelity at
least 1 − e²/4. In the latter case one sign flip suffices. -/
theorem ray_phase_fit_iff (V : unitaryGroup I ℂ) (j : I) {e : ℝ} (he : 0≤e) :
    (∃ f : I → ℂ, (∀ i, ‖f i‖=1) ∧ ‖diagonal f-reflection V {j}‖≤e) ↔
      Real.sqrt 2≤e ∨ ∃ i, 1-e^2/4 ≤ ‖V.val i j‖^2 := by
  constructor
  · rintro ⟨f,hf,h⟩
    rcases marked_witness V {j} (singleton_nonempty _) f hf with hbig | ⟨i,hi⟩
    · exact Or.inl (hbig.trans h)
    · have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
      simp only [rowWeight,sum_singleton] at hi
      exact Or.inr ⟨i,by linarith only [hi,hs]⟩
  · rintro (h | ⟨i,hi⟩)
    · exact ⟨fun _ => Complex.I,fun _ => Complex.norm_I,(imaginary_distance_le V {j}).trans h⟩
    · refine ⟨markSign {i},fun k => ?_,(sq_le_sq₀ (norm_nonneg _) he).mp ?_⟩
      · by_cases hk : k=i <;> simp [markSign,hk]
      · linarith only [ray_flip_bound V i j,hi]

#print axioms ray_phase_fit_iff
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation.MarkedReflections
