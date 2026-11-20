import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ModeDetuning
import GaloisForLFunctions.HTGeometry.TorusInvariantField
import GaloisForLFunctions.HTGeometry.AnalyticEscapeGenericityTransfer
import GaloisForLFunctions.HTGeometry.SortedEnsembleSpectrumScaling

/-! # Exact degree of a balanced spectral mode obstruction

Doubling all Pauli couplings doubles every eigenvalue. The product over all
D! labelings scales by 2^(D!), which determines its polynomial degree.
-/
open MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem modeOrbit_perm {I : Type*} [Fintype I] (m : I → ℤ) (E : I → ℝ) (s : Equiv.Perm I) :
    spectralRelationOrbitValue m (E ∘ s) = spectralRelationOrbitValue m E := by
  classical
  exact Equiv.prod_comp (Equiv.mulLeft s) (fun σ : Equiv.Perm I => ∑ i, (m i:ℝ)*E (σ i))

private theorem modeOrbit_scale {I : Type*} [Fintype I] (m : I → ℤ) (E : I → ℝ) (t : ℝ) :
    spectralRelationOrbitValue m (fun i => t*E i) = t^((Fintype.card I).factorial)*spectralRelationOrbitValue m E := by
  classical
  unfold spectralRelationOrbitValue
  simp only [show ∀ x y : ℝ, x*(t*y) = t*(x*y) from fun x y => by ring,← Finset.mul_sum,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_perm]

/-- The degrees in a nonzero homogeneous polynomial are detected by doubling
every real coordinate. Real points determine the complex polynomial. -/
private theorem homogeneous_of_doubling {n d : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (h : ∀ x : Fin n → ℝ, MvPolynomial.eval (fun i => (2:ℂ)*(x i:ℂ)) f =
      (2:ℂ)^d * MvPolynomial.eval (fun i => (x i:ℂ)) f) : f.IsHomogeneous d := by
  classical
  let g := scaleMvPolynomial (fun _ : Fin n => (2:ℂ)) f
  have hpoly : g = MvPolynomial.C ((2:ℂ)^d)*f := by
    apply sub_eq_zero.mp
    apply eq_zero_of_eval_real_eq_zero
    intro x
    rw [MvPolynomial.eval₂_id,map_sub,map_mul,MvPolynomial.eval_C,sub_eq_zero]
    have hres := aeval_scaleMvPolynomial (fun _ : Fin n => (2:ℂ)) (fun i => (x i:ℂ)) f
    change MvPolynomial.eval (fun i => (x i:ℂ)) (scaleMvPolynomial _ f) = _
    exact hres.trans (h x)
  intro a ha
  have hc := congrArg (MvPolynomial.coeff a) hpoly
  rw [coeff_scaleMvPolynomial,MvPolynomial.coeff_C_mul,Finset.prod_pow_eq_pow_sum] at hc
  have he : (2:ℂ)^(∑ i, a i) = (2:ℂ)^d := mul_right_cancel₀ ha hc
  have hreal : (2:ℝ)^(∑ i, a i) = (2:ℝ)^d := by exact_mod_cast he
  have hn' := (pow_right_injective₀ (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)) hreal
  simpa [Finsupp.weight_apply,Finsupp.sum_fintype] using hn'

/-- Every nonzero balanced mode obstruction on the N-site path has degree
exactly (2ᴺ)!, the number of labelings of its eigenvalues. -/
theorem pauliSpectralModePolynomial_totalDegree (k : ℕ) (m : Fin (2^(k+3)) → ℤ)
    (hbal : SpectralCharacterBalanced m) (hm : m ≠ 0) :
    (pauliSpectralModePolynomial k m).totalDegree = (2^(k+3)).factorial := by
  let hP := chainPauliFin_isHermitian (k+3)
  have hev (x : Fin (Fintype.card (ChainLabel (k+3))) → ℝ) :
      MvPolynomial.eval (fun i => (x i : ℂ)) (pauliSpectralModePolynomial k m) =
        (spectralRelationOrbitValue m (sortedEnsembleSpectrum hP x) : ℂ) := by
    rw [pauliSpectralModePolynomial_eval]
    exact congrArg Complex.ofReal (modeOrbit_perm m _ (Tuple.sort (isHermitian_spectralEnsembleMatrix hP x).eigenvalues)).symm
  apply MvPolynomial.IsHomogeneous.totalDegree _ (pauliSpectralModePolynomial_ne_zero k m hbal hm)
  apply homogeneous_of_doubling
  intro x
  have hs := hev (fun i => 2*x i)
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat] at hs
  rw [hs,hev,sortedEnsembleSpectrum_const_mul hP (by norm_num : (0:ℝ)<2),modeOrbit_scale,Fintype.card_fin]
  push_cast
  rfl

#print axioms pauliSpectralModePolynomial_totalDegree
end
end GaloisForLFunctions.HTGeometry
