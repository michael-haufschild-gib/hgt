import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.PolynomialSublevel
import GaloisForLFunctions.HTGeometry.ChainShellMaximalProjectivity
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! # Gaussian-integer coefficients of the path discriminant -/
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem localPauli_mem_gaussianInt (p : Option (Fin 3)) (x y : Bool) :
    boolPauliOptionEntry p (x,y) ∈ GaussianInt.toComplex.range := by
  let S := GaussianInt.toComplex.range
  have hI : Complex.I ∈ S := ⟨⟨0,1⟩, by change (((⟨0,1⟩ : GaussianInt) : ℂ)) = Complex.I; simp [GaussianInt.toComplex_def']⟩
  have h0 := S.zero_mem
  have h1 := S.one_mem
  have hm1 := S.neg_mem h1
  have hmI := S.neg_mem hI
  change boolPauliOption p x y ∈ S
  cases p with
  | none => cases x <;> cases y <;> simp [boolPauliOption,h0,h1]
  | some i =>
    fin_cases i <;> cases x <;> cases y <;> simp [boolPauliOption,finiteQubitPauli,h0,h1,hm1,hI,hmI]

/-- Every matrix entry in the numbered path Pauli family is a Gaussian integer. -/
theorem chainPauliFin_entry_mem_gaussianInt (N : ℕ) (a i j) :
    chainPauliFin N a i j ∈ GaussianInt.toComplex.range := by
  unfold chainPauliFin
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,finitePauliMatrix]
  exact GaussianInt.toComplex.range.prod_mem fun t _ => localPauli_mem_gaussianInt _ _ _

/-- The generic Hamiltonian has coefficients in the Gaussian integers. -/
theorem exists_integral_path_pauli_matrix (N : ℕ) :
    ∃ M : Matrix (Fin (2^N)) (Fin (2^N)) (MvPolynomial (Fin (Fintype.card (ChainLabel N))) GaussianInt),
      M.map (MvPolynomial.map GaussianInt.toComplex) = spectralGenericMatrix (chainPauliFin N) := by
  classical
  choose v hv using chainPauliFin_entry_mem_gaussianInt N
  refine ⟨fun i j => ∑ a, MvPolynomial.X a * MvPolynomial.C (v a i j),?_⟩
  ext i j : 2
  simp only [Matrix.map_apply,spectralGenericMatrix,map_sum,map_mul,MvPolynomial.map_C,MvPolynomial.map_X,hv]

private theorem path_discriminant_integral (N : ℕ) :
    spectralDiscriminantC (chainPauliFin N) ∈ (MvPolynomial.map GaussianInt.toComplex).range := by
  obtain ⟨M,hM⟩ := exists_integral_path_pauli_matrix N
  let φ := MvPolynomial.map (σ := Fin (Fintype.card (ChainLabel N))) GaussianInt.toComplex
  let H : Matrix (Fin (2^N)) (Fin (2^N)) (MvPolynomial _ GaussianInt) :=
    fun i j => (M^(i.val+j.val)).trace
  refine ⟨H.det,?_⟩
  change φ H.det = _
  rw [RingHom.map_det]
  apply congrArg Matrix.det
  refine Matrix.ext fun i j => ?_
  change φ (M^(i.val+j.val)).trace = _
  rw [← trace_mapMatrix,map_pow]
  exact congrArg (fun Q => (Q^(i.val+j.val)).trace) hM

/-- Each nonzero Gaussian integer has complex modulus at least one. -/
theorem one_le_gaussianInt_norm (z : GaussianInt) (hz : (z:ℂ) ≠ 0) : 1 ≤ ‖(z:ℂ)‖ := by
  have hp : 0 < z.norm := GaussianInt.norm_pos.mpr (fun h => hz (by rw [h,GaussianInt.toComplex_zero]))
  have h1 : 1 ≤ (z.norm:ℝ) := by exact_mod_cast (show 1 ≤ z.norm by omega)
  rw [GaussianInt.intCast_real_norm,← Complex.sq_norm] at h1
  nlinarith only [h1,norm_nonneg (z:ℂ)]

/-- In D dimensions the discriminant of a single standard Gaussian path draw
is below r^(D(D−1)) with probability at most 2D(D−1)r. -/
theorem gaussian_pauli_discriminant_lower_tail (k : ℕ) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) :
    let P := chainPauliFin (k+3)
    let d := spectralDiscriminantDegree (2^(k+3))
    (Measure.pi fun _ : Fin (Fintype.card (ChainLabel (k+3))) => gaussianReal 0 1)
      {x | MvPolynomial.eval x (spectralDiscriminantPoly P) < r^d} ≤ ENNReal.ofReal (2*d*r) := by
  let P := chainPauliFin (k+3)
  let hP := chainPauliFin_isHermitian (k+3)
  let f := spectralDiscriminantC P
  obtain ⟨x₀,hx₀⟩ := exists_chainShell_maximallyProjective_witness k
  have hf : f ≠ 0 := by
    rw [show f = MvPolynomial.map Complex.ofRealHom (spectralDiscriminantPoly P) from (map_spectralDiscriminantPoly hP).symm]
    exact fun h => spectralDiscriminantPoly_ne_zero hP hx₀.injective
      ((MvPolynomial.map_injective _ Complex.ofReal_injective) (h.trans (map_zero _).symm))
  have hd : f.totalDegree = spectralDiscriminantDegree (2^(k+3)) :=
    (isHomogeneous_spectralDiscriminantC P).totalDegree hf
  obtain ⟨g,hg⟩ := path_discriminant_integral (k+3)
  obtain ⟨m,hm⟩ := lexHeadCoefficient_is_coeff f
  have hL : GaussianInt.toComplex (g.coeff m) = lexHeadCoefficient f := by
    rw [← hm,show f = MvPolynomial.map GaussianInt.toComplex g from hg.symm,MvPolynomial.coeff_map]
  have ha := one_le_gaussianInt_norm (g.coeff m) (by rw [hL]; exact lexHeadCoefficient_ne_zero f hf)
  change 1 ≤ ‖GaussianInt.toComplex (g.coeff m)‖ at ha
  rw [hL] at ha
  have h := gaussian_mvPolynomial_sublevel f hf hr hr'
  rw [hd] at h
  refine (measure_mono ?_).trans h
  intro x hx
  change ‖MvPolynomial.eval (fun i => (x i : ℂ)) f‖ < _
  have he := ofReal_eval_eq_eval_map (spectralDiscriminantPoly P) x
  rw [map_spectralDiscriminantPoly hP] at he
  rw [← he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (spectralDiscriminantPoly_nonneg hP x)]
  exact hx.trans_le (le_mul_of_one_le_left (pow_nonneg hr.le _) ha)

#print axioms gaussian_pauli_discriminant_lower_tail

/-- The Vandermonde discriminant has one factor per ordered pair of distinct indices. -/
theorem spectralDiscriminantDegree_eq_mul_pred (D : ℕ) : spectralDiscriminantDegree D = D*(D-1) := by
  rw [spectralDiscriminantDegree,mul_comm,Fin.sum_univ_eq_sum_range (fun i => i) D,Finset.sum_range_id_mul_two]

private theorem abs_gap_product_le {D : ℕ} (E : Fin D → ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hE : ∀ i j, |E j-E i| ≤ B) {i j : Fin D} (hij : i < j) :
    |∏ a, ∏ b ∈ Finset.Ioi a, (E b-E a)| ≤ |E j-E i| *B^(D*D) := by
  classical
  let s := (Finset.univ : Finset (Fin D)).sigma (fun a => Finset.Ioi a)
  let c : (a : Fin D) × Fin D := ⟨i,j⟩
  let F (p : (a : Fin D) × Fin D) := |E p.2-E p.1|
  have hc : c ∈ s := Finset.mem_sigma.mpr ⟨Finset.mem_univ _,Finset.mem_Ioi.mpr hij⟩
  have hcard : s.card ≤ D*D := by
    dsimp only [s]; rw [Finset.card_sigma]
    calc
      _ ≤ ∑ _a : Fin D, D := Finset.sum_le_sum fun a _ => (Finset.card_le_univ _).trans_eq (Fintype.card_fin D)
      _ = _ := by simp
  have hremaining : ∏ p ∈ s.erase c, F p ≤ B^(D*D) := by
    refine (Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun p _ => hE p.1 p.2)).trans ?_
    rw [Finset.prod_const]
    exact pow_le_pow_right₀ hB ((Finset.card_le_card (Finset.erase_subset c s)).trans hcard)
  calc
    _ = ∏ p ∈ s, F p := by simp only [s,F,Finset.abs_prod,Finset.prod_sigma]
    _ = (∏ p ∈ s.erase c, F p)*F c := (Finset.prod_erase_mul s F hc).symm
    _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hremaining (abs_nonneg _)

/-- At fixed spectral diameter B, all eigenvalue gaps on the same draw obey
a lower-tail estimate with degree D(D−1), simultaneously over all pairs. -/
theorem gaussian_pauli_minimum_gap_lower_tail (k : ℕ) {r B : ℝ}
    (hr : 0 < r) (hr' : r ≤ 1) (hB : 1 ≤ B) :
    let D : ℕ := 2^(k+3)
    let d : ℕ := D*(D-1)
    (Measure.pi fun _ : Fin (Fintype.card (ChainLabel (k+3))) => gaussianReal 0 1)
      {x | let E := (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k+3)) x).eigenvalues
           (∀ i j, |E j-E i| ≤ B) ∧ ∃ i j, i < j ∧ (|E j-E i| *B^(D*D))^2 < r^d} ≤
      ENNReal.ofReal (2*d*r) := by
  intro D d
  have hprob := gaussian_pauli_discriminant_lower_tail k hr hr'
  dsimp only at hprob
  rw [spectralDiscriminantDegree_eq_mul_pred] at hprob
  refine (measure_mono ?_).trans hprob
  rintro x ⟨hE,i,j,hij,hsmall⟩
  change MvPolynomial.eval x (spectralDiscriminantPoly (chainPauliFin (k+3))) < _
  rw [eval_spectralDiscriminantPoly (chainPauliFin_isHermitian (k+3))]
  have h := abs_gap_product_le _ hB hE hij
  have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs] at hs
  exact hs.trans_lt hsmall

#print axioms gaussian_pauli_minimum_gap_lower_tail
end
end GaloisForLFunctions.HTGeometry
