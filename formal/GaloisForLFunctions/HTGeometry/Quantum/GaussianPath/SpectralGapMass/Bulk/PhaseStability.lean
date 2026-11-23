import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.SpectralCoupling
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension
import GaloisForLFunctions.HTGeometry.TorsionPolygonRecurrenceShadowing

/-! # Mean-square phase stability under deletion of physical couplings -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
noncomputable section

private theorem phase_lipschitz (t a b : ℝ) :
    ‖Complex.exp (-(Complex.I*((t:ℂ)*a)))-Complex.exp (-(Complex.I*((t:ℂ)*b)))‖ ≤
      |t| *‖(a:ℂ)-(b:ℂ)‖ := by
  have he (s : ℝ) : ((-(t*s):ℝ):ℂ)*Complex.I = -(Complex.I*((t:ℂ)*s)) := by push_cast; ring
  have h := norm_exp_ofReal_mul_I_sub_le (-(t*a)) (-(t*b))
  rw [he,he,show -(t*a)- -(t*b)=-(t*(a-b)) by ring,abs_neg,abs_mul] at h
  simpa only [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using h

/-- In normalized or unnormalized Hilbert–Schmidt distance the physical
evolution is |t|-Lipschitz in its full Hamiltonian at signed time t. -/
theorem evolution_displacement {I : Type*} [Fintype I] [DecidableEq I]
    {H K : Matrix I I ℂ} (hH : H.IsHermitian) (hK : K.IsHermitian) (t : ℝ) :
    hsNormSq (unitaryEvolution H t-unitaryEvolution K t) ≤ |t|^2*hsNormSq (H-K) := by
  let U : Matrix I I ℂ := hH.eigenvectorUnitary
  let V : Matrix I I ℂ := hK.eigenvectorUnitary
  let x (i : I) : ℂ := hH.eigenvalues i
  let y (i : I) : ℂ := hK.eigenvalues i
  let f (i : I) := Complex.exp (-(Complex.I*((t:ℂ)*x i)))
  let g (i : I) := Complex.exp (-(Complex.I*((t:ℂ)*y i)))
  have hf : unitaryEvolution H t=U*diagonal f*Uᴴ := unitaryEvolution_spectral hH t
  have hg : unitaryEvolution K t=V*diagonal g*Vᴴ := unitaryEvolution_spectral hK t
  have hx : H=U*diagonal x*Uᴴ := isHermitian_eq_conj_diagonal hH
  have hy : K=V*diagonal y*Vᴴ := isHermitian_eq_conj_diagonal hK
  have h := spectral_lipschitz U V hH.eigenvectorUnitary.2 hK.eigenvectorUnitary.2 x y f g
    (abs_nonneg t) (fun i j => phase_lipschitz t _ _)
  rwa [←hf,←hg,←hx,←hy] at h

/-- Each deleted or changed Pauli coupling contributes its squared
change to the normalized mean-square displacement. -/
theorem path_evolution_displacement {n : ℕ} (u v : PathShell n) (t : ℝ) :
    hsNormSq (unitaryEvolution (pathHamiltonian u) t-unitaryEvolution (pathHamiltonian v) t) ≤
      |t|^2*((2:ℝ)^(n+2)*∑ l : PathLabel n, (u l-v l)^2) := by
  have h := evolution_displacement (isSelfAdjoint_pathHamiltonian u).isHermitian
    (isSelfAdjoint_pathHamiltonian v).isHermitian t
  have hd : pathHamiltonian (u-v)=pathHamiltonian u-pathHamiltonian v :=
    (pathHamiltonianLM n).map_sub u v
  rw [←hd,pathHamiltonian_eq_sum (u-v),hsNormSq_pauliCombination pathWord_injective] at h
  exact h

private theorem trace_sq_le_energy {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) :
    ‖A.trace‖^2 ≤ Fintype.card I*hsNormSq A := by
  have hn : ‖A.trace‖≤∑ i, ‖A i i‖ := norm_sum_le _ _
  have hs := sq_sum_abs_le_card_mul_sum_sq (fun i => ‖A i i‖)
  simp only [abs_of_nonneg (norm_nonneg _)] at hs
  have he : (∑ i, ‖A i i‖^2)≤hsNormSq A :=
    Finset.sum_le_sum fun i _ => Finset.single_le_sum (fun j _ => sq_nonneg ‖A j i‖) (Finset.mem_univ i)
  exact ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun i _ => norm_nonneg _)).mpr hn).trans
    (hs.trans (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)))

/-- Against any fixed unitary, changing squared Pauli mass M perturbs
the normalized trace overlap by at most |t|√M. -/
theorem path_overlap_stability {n : ℕ} (u v : PathShell n) (t : ℝ)
    (W : unitaryGroup (Fin (n+2) → Bool) ℂ) :
    let D := (2:ℝ)^(n+2)
    ‖(W.valᴴ*unitaryEvolution (pathHamiltonian u) t).trace-
      (W.valᴴ*unitaryEvolution (pathHamiltonian v) t).trace‖ ≤
        D*|t| *Real.sqrt (∑ l : PathLabel n, (u l-v l)^2) := by
  intro D
  let U := unitaryEvolution (pathHamiltonian u) t
  let V := unitaryEvolution (pathHamiltonian v) t
  let m := ∑ l : PathLabel n, (u l-v l)^2
  have hm : 0≤m := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hD : 0≤D := by dsimp only [D]; positivity
  have hcard : (Fintype.card (Fin (n+2) → Bool):ℝ)=D := by simp [D]
  have ht := trace_sq_le_energy (W.valᴴ*(U-V))
  have heq : hsNormSq (W.valᴴ*(U-V))=hsNormSq (U-V) := by
    simpa only [mul_one] using translate_frob W.valᴴ (U-V) 1
      (by simpa only [Matrix.conjTranspose_conjTranspose] using W.2.2)
      (by rw [Matrix.conjTranspose_one,mul_one])
  rw [hcard,heq,mul_sub,Matrix.trace_sub] at ht
  have he : hsNormSq (U-V)≤|t|^2*(D*m) := path_evolution_displacement u v t
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg hD (abs_nonneg t)) (Real.sqrt_nonneg m))).mp
  apply ht.trans ((mul_le_mul_of_nonneg_left he hD).trans_eq ?_)
  rw [mul_pow,mul_pow,Real.sq_sqrt hm]
  ring

/-- Deleting seams of squared coefficient mass M changes the empirical
spectral characteristic function by at most |t|√M. -/
theorem path_characteristic_stability {n : ℕ} (u v : PathShell n) (t : ℝ) :
    let D := (2:ℝ)^(n+2)
    ‖(unitaryEvolution (pathHamiltonian u) t).trace-
      (unitaryEvolution (pathHamiltonian v) t).trace‖ ≤
        D*|t| *Real.sqrt (∑ l : PathLabel n, (u l-v l)^2) := by
  simpa only [OneMemClass.coe_one,Matrix.conjTranspose_one,one_mul] using
    path_overlap_stability u v t 1

#print axioms path_evolution_displacement
#print axioms path_characteristic_stability
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
