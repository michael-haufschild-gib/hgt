import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.FreeAxis.GaussianAction
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.FreeAxis.QubitFrame
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.HiddenRotatedIsingTube

/-! # A common qubit frame preserves every circuit budget on the path -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut.FreeAxis
open AccuracyScales.TenthPlateau DiagonalSynthesis
open private sum4_comm realizes_conj_prodLocal from GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.HiddenRotatedIsingTube
noncomputable section

private theorem expand_path (F : SpinFrame) {n : ℕ} (W : Register (n + 2))
    (u : PathShell n)
    (honsite : ∀ (v : Fin (n + 2)) (b : Fin 3),
      W * finitePauliMatrix (onsiteWord v b) * star W =
        ∑ a : Fin 3, ((F.R a b : ℝ) : ℂ) • finitePauliMatrix (onsiteWord v a))
    (hcoupling : ∀ (e : Fin (n + 1)) (b₁ b₂ : Fin 3),
      W * finitePauliMatrix (couplingWord e (b₁, b₂)) * star W =
        ∑ a₁ : Fin 3, ∑ a₂ : Fin 3,
          ((F.R a₁ b₁ * F.R a₂ b₂ : ℝ) : ℂ) •
            finitePauliMatrix (couplingWord e (a₁, a₂))) :
    W * pathHamiltonian u * star W = pathHamiltonian (WithLp.toLp 2 (rotateLabels F.R n u.ofLp)) := by
  rw [pathHamiltonian_eq_sum, pathHamiltonian_eq_sum, Matrix.mul_sum, Matrix.sum_mul]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun v _ => ?_
    trans (∑ b : Fin 3, ∑ a : Fin 3,
      (((F.R a b * u (.inl (v, b)) : ℝ) : ℂ) • finitePauliMatrix (onsiteWord v a)))
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul, show pathWord (.inl (v, b)) = onsiteWord v b from rfl,
        honsite v b, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_smul, Complex.ofReal_mul, mul_comm]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_smul, ← Complex.ofReal_sum]
      rfl
  · refine Finset.sum_congr rfl fun e _ => ?_
    trans (∑ b₁ : Fin 3, ∑ b₂ : Fin 3, ∑ a₁ : Fin 3, ∑ a₂ : Fin 3,
      (((F.R a₁ b₁ * F.R a₂ b₂ * u (.inr (e, (b₁, b₂))) : ℝ) : ℂ) •
        finitePauliMatrix (couplingWord e (a₁, a₂))))
    · refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul,
        show pathWord (.inr (e, (b₁, b₂))) = couplingWord e (b₁, b₂) from rfl,
        hcoupling e b₁ b₂, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a₁ _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun a₂ _ => ?_
      rw [smul_smul]
      refine congrArg (· • finitePauliMatrix (couplingWord e (a₁, a₂))) ?_
      push_cast; ring
    · rw [sum4_comm]
      refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ => ?_
      simp_rw [← Finset.sum_smul, ← Complex.ofReal_sum]
      rfl


private theorem bond_product {n : ℕ} (e : Fin (n+1)) (a b : Fin 3) :
    finitePauliMatrix (couplingWord e (a,b)) =
      finitePauliMatrix (onsiteWord e.castSucc a)*finitePauliMatrix (onsiteWord e.succ b) := by
  change prodLocalMatrix _=prodLocalMatrix _*prodLocalMatrix _
  rw [prodLocalMatrix_mul]
  apply congrArg prodLocalMatrix
  funext s
  by_cases h : s=e.castSucc
  · subst s; simp [couplingWord,onsiteWord,boolPauliOption,e.castSucc_lt_succ.ne]
  · by_cases h' : s=e.succ
    · subst s; simp [couplingWord,onsiteWord,e.castSucc_lt_succ.ne.symm,boolPauliOption]
    · simp [couplingWord,onsiteWord,h,h',boolPauliOption]

private theorem conjugate_path (F : SpinFrame) {n : ℕ} (u : PathShell n) :
    let W := prodLocalMatrix (fun _ : Fin (n+2) => F.U)
    W*pathHamiltonian u*star W = pathHamiltonian (WithLp.toLp 2 (rotateLabels F.R n u.ofLp)) := by
  intro W
  have honsite (v : Fin (n + 2)) (b : Fin 3) :
      W * finitePauliMatrix (onsiteWord v b) * star W =
        ∑ a : Fin 3, ((F.R a b : ℝ) : ℂ) • finitePauliMatrix (onsiteWord v a) := by
    rw [prodLocalMatrix_conj_pauli]
    ext x y
    rw [Matrix.sum_apply]
    simp only [prodLocalMatrix]
    rw [← Finset.prod_mul_prod_compl ({v} : Finset (Fin (n + 2))), Finset.prod_singleton]
    have hrest : (∏ s ∈ ({v} : Finset (Fin (n + 2)))ᶜ,
        (F.U * boolPauliOption (onsiteWord v b s) * star F.U) (x s) (y s)) =
        ∏ s ∈ ({v} : Finset (Fin (n + 2)))ᶜ, boolPauliOptionEntry none (x s, y s) := by
      refine Finset.prod_congr rfl fun s hs => ?_
      have hsv : s ≠ v := by simpa using hs
      simp [onsiteWord, hsv, boolPauliOption, boolPauliOptionEntry,
        F.unitary.2, Matrix.one_apply]
    have hv_eq : boolPauliOption (onsiteWord v b v) = finiteQubitPauli b := by
      simp [onsiteWord, boolPauliOption]
    rw [hv_eq, F.conjugates b, hrest, Matrix.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]
    congr 1
    unfold finitePauliMatrix
    rw [← Finset.prod_mul_prod_compl ({v} : Finset (Fin (n + 2))), Finset.prod_singleton]
    congr 1
    · simp [onsiteWord, boolPauliOptionEntry, boolPauliOption]
    · refine Finset.prod_congr rfl fun s hs => ?_
      have hsv : s ≠ v := by simpa using hs
      simp [onsiteWord, hsv]

  have hW : W ∈ unitary (DiagonalSynthesis.Register (n+2)) :=
    prodLocalMatrix_mem_unitary _ fun _ => F.unitary
  apply expand_path F W u honsite
  intro e b c
  let X := finitePauliMatrix (onsiteWord e.castSucc b)
  let Y := finitePauliMatrix (onsiteWord e.succ c)
  rw [bond_product]
  change W*(X*Y)*star W=_
  calc
    _ = (W*X*star W)*(W*Y*star W) := by
      calc _ = W*X*(star W*W)*Y*star W := by rw [hW.1,mul_one]; simp only [mul_assoc]
           _ = _ := by simp only [mul_assoc]
    _ = _ := by
      rw [show X=finitePauliMatrix (onsiteWord e.castSucc b) from rfl,
        show Y=finitePauliMatrix (onsiteWord e.succ c) from rfl,honsite,honsite,Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Matrix.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [bond_product,smul_mul_smul_comm,Complex.ofReal_mul]

/-- Every original circuit gate can be conjugated on its own two
wires, so no gates are added by the change of laboratory frame. -/
theorem frame_fit (F : SpinFrame) {n B : ℕ} {x : PathLabel n→ℝ} {ε t : ℝ}
    (h : HasProjectiveCircuitApproximation (n+2) ε B
      (unitaryEvolution (pathHamiltonian (WithLp.toLp 2 x : PathShell n)) t)) :
    HasProjectiveCircuitApproximation (n+2) ε B
      (unitaryEvolution (pathHamiltonian (WithLp.toLp 2 (rotateLabels F.R n x))) t) := by
  let w : PathShell n := WithLp.toLp 2 x
  let W := prodLocalMatrix (fun _ : Fin (n+2) => F.U)
  have hW : W ∈ unitary (DiagonalSynthesis.Register (n+2)) :=
    prodLocalMatrix_mem_unitary _ fun _ => F.unitary
  let V : Matrix.unitaryGroup (Fin (n+2)→Bool) ℂ := ⟨W,hW⟩
  have hev := unitaryEvolution_conj W (pathHamiltonian w) (Unitary.isUnit_coe (U:=V)) t
  rw [inv_eq_star_of_mem_unitary hW,conjugate_path F w] at hev
  obtain ⟨z,hz,C,hC,hfit⟩ := h
  have hr : Realizes B (z • C.eval.val) := ⟨z,hz,C,hC,rfl⟩
  obtain ⟨a,ha,D,hD,hrot⟩ := realizes_conj_prodLocal F.U F.unitary hr
  refine ⟨a,ha,D,hD,?_⟩
  rw [←hrot,hev,←Matrix.sub_mul,←Matrix.mul_sub,l2_opNorm_unitary_conj_eq hW]
  exact hfit

#print axioms frame_fit
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut.FreeAxis
