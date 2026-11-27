import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Frames.AxisExchange
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Frames.WireConjugation
import GaloisForLFunctions.HTGeometry.Quantum.PathPauliSpectralWidth

/-! # Axis-selected longitudinal couplings in a product frame -/

open Matrix Finset
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section
variable {n : ℕ}

private def permute (a : Fin (n+2)→Fin 3) : PathLabel n→PathLabel n
  | .inl (v,b) => .inl (v,Equiv.swap (a v) 2 b)
  | .inr (e,b,c) => .inr (e,(Equiv.swap (a e.castSucc) 2 b,Equiv.swap (a e.succ) 2 c))

private def axesEquiv (a : Fin (n+2)→Fin 3) : PathLabel n ≃ PathLabel n :=
  Function.Involutive.toPerm (permute a) (by rintro (⟨v,b⟩|⟨e,b,c⟩) <;> simp [permute])

private theorem permute_word (a : Fin (n+2)→Fin 3) (l : PathLabel n) (v : Fin (n+2)) :
    pathWord (permute a l) v=(pathWord l v).map (Equiv.swap (a v) 2) := by
  rcases l with ⟨w,b⟩ | ⟨e,b,c⟩
  · by_cases h : v=w <;> simp [permute,pathWord,onsiteWord,h]
  · by_cases hl : v=e.castSucc
    · simp [permute,pathWord,couplingWord,hl]
    · by_cases hr : v=e.succ <;> simp_all [permute,pathWord,couplingWord]

private def signAt (a : Fin 3) : Option (Fin 3)→ℝ
  | none => 1
  | some b => axisSign a b

private def wordSign (a : Fin (n+2)→Fin 3) (l : PathLabel n) : ℝ :=
  ∏ i, signAt (a i) (pathWord l i)

private theorem abs_sign (a : Fin (n+2)→Fin 3) (l : PathLabel n) : |wordSign a l|=1 := by
  unfold wordSign
  rw [Finset.abs_prod]
  apply prod_eq_one
  intro i _
  rcases pathWord l i with _|b
  · norm_num [signAt]
  · simp only [signAt,axisSign]; split <;> norm_num

/-- Real Pauli coefficients seen after rotating the chosen axis on each
site to Z. The action is a signed permutation on both onsite and bond terms. -/
def rotatedShell (a : Fin (n+2)→Fin 3) (u : PathShell n) : PathShell n :=
  WithLp.toLp 2 fun l => wordSign a ((axesEquiv a).symm l)*u ((axesEquiv a).symm l)

theorem rotatedShell_norm (a : Fin (n+2)→Fin 3) (u : PathShell n) : ‖rotatedShell a u‖=‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  calc
    _ = ∑ l, (u ((axesEquiv a).symm l))^2 := by
      apply sum_congr rfl
      intro l _
      change (wordSign a _*u _)^2=_
      rw [←sq_abs,abs_mul,abs_sign,one_mul,sq_abs]
    _ = _ := (axesEquiv a).symm.sum_comp (fun l => (u l)^2)

theorem rotatedShell_longitudinal (a : Fin (n+2)→Fin 3) (u : PathShell n) (e : Fin (n+1)) :
    |rotatedShell a u (.inr (e,2,2))|=|u (.inr (e,a e.castSucc,a e.succ))| := by
  change |wordSign a _*u (permute a (.inr (e,2,2)))|=_
  simp only [abs_mul,abs_sign,one_mul,permute,Equiv.swap_apply_right]

theorem rotatedShell_hamiltonian (a : Fin (n+2)→Fin 3) (u : PathShell n) :
    let V := (localFrame (fun i => axisFrame (a i))).val
    V*pathHamiltonian u*Vᴴ=pathHamiltonian (rotatedShell a u) := by
  intro V
  have hword (l : PathLabel n) : V*finitePauliMatrix (pathWord l)*Vᴴ=
      (wordSign a l:ℂ) • finitePauliMatrix (pathWord (permute a l)) := by
    change finiteLocalMatrix _ * finitePauliMatrix _ * (finiteLocalMatrix _)ᴴ=_
    rw [finiteLocalMatrix_conjTranspose,finitePauliMatrix_eq_finiteLocalMatrix,
      finiteLocalMatrix_mul,finiteLocalMatrix_mul,finitePauliMatrix_eq_finiteLocalMatrix]
    have h (i : Fin (n+2)) : (axisFrame (a i)).val*boolPauliOption (pathWord l i)*(axisFrame (a i)).valᴴ=
        (signAt (a i) (pathWord l i):ℂ) • boolPauliOption (pathWord (permute a l) i) := by
      rw [permute_word]
      cases he : pathWord l i with
      | none => simpa only [signAt,Option.map_none,boolPauliOption,mul_one,Complex.ofReal_one,one_smul] using
          (show (axisFrame (a i)).val*(axisFrame (a i)).valᴴ=1 from
            (Unitary.mem_iff.mp (axisFrame (a i)).2).2)
      | some b => exact axisFrame_pauli (a i) b
    simp_rw [h]
    rw [finiteLocalMatrix_pointwise_smul,wordSign,Complex.ofReal_prod]
  rw [pathHamiltonian_eq_sum,Finset.mul_sum,Finset.sum_mul,pathHamiltonian_eq_sum,
    ←(axesEquiv a).sum_comp (fun l => ((rotatedShell a u l:ℝ):ℂ) • finitePauliMatrix (pathWord l))]
  apply sum_congr rfl
  intro l _
  rw [Matrix.mul_smul,Matrix.smul_mul,hword,smul_smul]
  have hc : rotatedShell a u (axesEquiv a l)=wordSign a l*u l := by
    change wordSign a ((axesEquiv a).symm _)*u ((axesEquiv a).symm _)=_
    rw [Equiv.symm_apply_apply]
  rw [hc,Complex.ofReal_mul,mul_comm]
  rfl

#print axioms rotatedShell_hamiltonian
#print axioms rotatedShell_norm
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
