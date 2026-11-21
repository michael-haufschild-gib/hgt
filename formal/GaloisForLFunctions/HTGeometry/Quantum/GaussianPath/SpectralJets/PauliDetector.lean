import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SimpleBranches
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.Discriminant
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPauliPrefixPhaseLaw

/-! # Integral spectral derivative detectors on Gaussian Pauli chains -/
open MvPolynomial Matrix Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

abbrev Coordinates (N : ℕ) := Fin (Fintype.card (ChainLabel N))

/-- A Gaussian-integer representative of each entry of a path Pauli generator. -/
def integralGenerators (N : ℕ) (a : Coordinates N) : Matrix (Fin (2^N)) (Fin (2^N)) GaussianInt :=
  fun i j => Classical.choose (chainPauliFin_entry_mem_gaussianInt N a i j)

theorem generators_map (N : ℕ) (a : Coordinates N) :
    (integralGenerators N a).map GaussianInt.toComplex = chainPauliFin N a := by
  ext i j
  exact Classical.choose_spec (chainPauliFin_entry_mem_gaussianInt N a i j)

/-- The order-L cleared determinant as a polynomial in the actual Pauli couplings. -/
def pathDetector (N L : ℕ) (rows : Fin (2^N) → Option (List (Coordinates N))) :=
  jetGram (integralGenerators N) L rows

theorem pathDetector_degree (N L : ℕ) (rows : Fin (2^N) → Option (List (Coordinates N)))
    (hw : ∀ j v, v ∈ rows j → v.length ≤ L) :
    (pathDetector N L rows).totalDegree ≤ 2^N*(2*(1+2*L*2^N)) :=
  jetGram_degree _ _ _ hw

private theorem numbered_simple :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let θ := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
      Function.Injective (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k+3)) θ).eigenvalues := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  intro k θ
  let u := pathPauliDisorderShell ω (k+1)
  let e := qubitConfigFin (k+3)
  have hH := (isSelfAdjoint_pathHamiltonian u).isHermitian
  have h : ∃ h : (Matrix.reindex e e (pathHamiltonian u)).IsHermitian,
      MaximallyProjectiveEnergy h.eigenvalues :=
    ⟨hH.reindex e,Matrix.IsHermitian.maximallyProjective_reindexAlgEquiv e hH (hω k)⟩
  rw [reindex_pathHamiltonian] at h
  exact h.choose_spec.injective

/-- Analytic branches realize the complete family of cleared determinants
at a specialization of a linear matrix pencil. -/
def BranchJetData {n D : ℕ} {R : Type*} [CommRing R]
    (A : Fin n → Matrix (Fin D) (Fin D) R) (φ : R →+* ℂ)
    (P : Fin n → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → ℂ) (E : Fin D → ℝ) : Prop :=
  ∃ (f : Fin D → (Fin n → ℂ) → ℂ) (h : Fin D → ℂ),
    (∀ j, h j ≠ 0 ∧ AnalyticAt ℂ (f j) x ∧ f j x = (E j : ℂ) ∧
      ∀ᶠ z in 𝓝 x, matrixCharpolyRelation (∑ a, z a • P a, f j z) = 0) ∧
    ∀ (L : ℕ) (rows : Fin D → Option (List (Fin n))),
      (∀ j v, v ∈ rows j → v.length ≤ L) →
      eval₂Hom φ x (jetGram A L rows) =
        ((Matrix.of fun i j => rowValue (rows i) (f j) x).det * ∏ j, (h j)^(2*L))^2

private theorem branches_of_generators {n D : ℕ} {R : Type*} [CommRing R]
    (A : Fin n → Matrix (Fin D) (Fin D) R) (φ : R →+* ℂ)
    (P : Fin n → Matrix (Fin D) (Fin D) ℂ) (hm : (fun a => (A a).map φ) = P)
    (θ : Fin n → ℝ) (hH : (spectralEnsembleMatrix P θ).IsHermitian)
    (hi : Function.Injective hH.eigenvalues) :
    BranchJetData A φ P (fun i => (θ i : ℂ)) hH.eigenvalues := by
  subst P
  let x : Fin n → ℂ := fun i => (θ i : ℂ)
  obtain ⟨f,hf,hs,hv⟩ := simple_pencil_branch_detector A φ x hH hi
  let s (j : Fin D) : ℂ := onRoot (MvPolynomial.pderiv none (MvPolynomial.map φ (characteristic A))) (f j) x
  unfold BranchJetData
  exact ⟨f,s, fun j => ⟨hs j,hf j⟩,hv⟩

/-- All mixed derivative determinants at one real Pauli specialization. -/
def HasPathJetBranches (N : ℕ) (θ : Coordinates N → ℝ) : Prop :=
  BranchJetData (integralGenerators N) GaussianInt.toComplex (chainPauliFin N)
    (fun i => (θ i : ℂ)) (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian N) θ).eigenvalues

private theorem path_branches_at_simple (N : ℕ) (θ : Coordinates N → ℝ)
    (hi : Function.Injective (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian N) θ).eigenvalues) :
    HasPathJetBranches N θ :=
  branches_of_generators (integralGenerators N) GaussianInt.toComplex (chainPauliFin N)
    (funext (generators_map N)) θ (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian N) θ) hi

/-- Almost surely on every prefix, the same local analytic eigenbranches realize
all the integral polynomials, with a nonzero column factor for each energy. -/
theorem gaussian_path_mixed_spectral_jet_detectors :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, HasPathJetBranches (k+3)
      (fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)) := by
  filter_upwards [numbered_simple] with ω hω
  exact fun k => path_branches_at_simple _ _ (hω k)

private theorem integral_sublevel {n : ℕ} (g : MvPolynomial (Fin n) GaussianInt) (B : ℕ)
    (hg : g.totalDegree ≤ B) (hnz : map GaussianInt.toComplex g ≠ 0)
    {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1)
      {x | ‖eval₂Hom GaussianInt.toComplex (fun i => (x i : ℂ)) g‖ < r^B} ≤
        ENNReal.ofReal (2*(B:ℝ)*r) := by
  let f := map GaussianInt.toComplex g
  have hd : f.totalDegree ≤ B := (show f.totalDegree ≤ g.totalDegree from
    Finset.sup_mono (support_map_subset GaussianInt.toComplex g)).trans hg
  have hev (x : Fin n → ℝ) : eval₂Hom GaussianInt.toComplex (fun i => (x i : ℂ)) g =
      eval (fun i => (x i : ℂ)) f := (eval_map ..).symm
  obtain ⟨a,ha⟩ := lexHeadCoefficient_is_coeff f
  have hc : GaussianInt.toComplex (g.coeff a) = lexHeadCoefficient f := by rw [← ha,show f = map GaussianInt.toComplex g from rfl,coeff_map]
  have hnorm := one_le_gaussianInt_norm (g.coeff a) (by rw [hc]; exact lexHeadCoefficient_ne_zero f hnz)
  change 1 ≤ ‖GaussianInt.toComplex (g.coeff a)‖ at hnorm
  rw [hc] at hnorm
  have hsmall := gaussian_mvPolynomial_sublevel f hnz hr hr'
  apply (measure_mono ?_).trans (hsmall.trans (ENNReal.ofReal_le_ofReal ?_))
  · intro x hx
    change ‖eval (fun i => (x i : ℂ)) f‖ < _
    rw [← hev]
    exact hx.trans_le ((pow_le_pow_of_le_one hr.le hr' hd).trans
      (le_mul_of_one_le_left (pow_nonneg hr.le _) hnorm))
  · gcongr

/-- A nonzero detector has a Gaussian lower-tail bound at its degree budget. -/
theorem pathDetector_lower_tail_of_nonzero (N L : ℕ)
    (rows : Fin (2^N) → Option (List (Coordinates N))) (hw : ∀ j v, v ∈ rows j → v.length ≤ L)
    (hnz : map GaussianInt.toComplex (pathDetector N L rows) ≠ 0)
    {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) :
    let B : ℕ := 2^N*(2*(1+2*L*2^N))
    (Measure.pi fun _ : Coordinates N => gaussianReal 0 1)
      {x | let z := eval₂Hom GaussianInt.toComplex (fun i => (x i : ℂ)) (pathDetector N L rows)
           ‖z‖ < r^B} ≤ ENNReal.ofReal (2*(B:ℝ)*r) := by
  exact integral_sublevel _ _ (pathDetector_degree N L rows hw) hnz hr hr'

/-- Small nonzero detector values have a Gaussian lower-tail bound with the
polynomial degree budget. This statement also covers identically zero minors. -/
theorem gaussian_path_detector_small_nonzero (N L : ℕ)
    (rows : Fin (2^N) → Option (List (Coordinates N))) (hw : ∀ j v, v ∈ rows j → v.length ≤ L)
    {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) :
    let B : ℕ := 2^N*(2*(1+2*L*2^N))
    (Measure.pi fun _ : Coordinates N => gaussianReal 0 1)
      {x | let z := eval₂Hom GaussianInt.toComplex (fun i => (x i : ℂ)) (pathDetector N L rows)
           z ≠ 0 ∧ ‖z‖ < r^B} ≤ ENNReal.ofReal (2*(B:ℝ)*r) := by
  intro B
  by_cases hz : map GaussianInt.toComplex (pathDetector N L rows) = 0
  · have hempty : {x : Coordinates N → ℝ |
        let z := eval₂Hom GaussianInt.toComplex (fun i => (x i : ℂ)) (pathDetector N L rows)
        z ≠ 0 ∧ ‖z‖ < r^B} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      apply hx.1
      change eval₂ GaussianInt.toComplex _ _ = 0
      rw [← eval_map,hz,map_zero]
    rw [hempty,measure_empty]
    exact bot_le
  · exact (measure_mono fun _ hx => hx.2).trans (pathDetector_lower_tail_of_nonzero N L rows hw hz hr hr')

#print axioms gaussian_path_mixed_spectral_jet_detectors
#print axioms gaussian_path_detector_small_nonzero
end
end GaloisForLFunctions.HTGeometry.SpectralJets
