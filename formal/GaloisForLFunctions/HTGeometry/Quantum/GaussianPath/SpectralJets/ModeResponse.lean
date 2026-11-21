import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Nonvanishing
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Rank.IntegerResponse

/-! # A common quantitative derivative response for every balanced integer mode -/
open Matrix MvPolynomial Filter MeasureTheory Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- At a real specialization, each nonzero integral combination of energies
is detected by one of the fixed rows. A balanced combination has zero
response in every constant row. -/
def DetectsBalancedModes (N L : ℕ) (rows : Fin (2^N) → Option (List (Coordinates N)))
    (θ : Coordinates N → ℝ) (lower : ℝ) : Prop :=
  let x := fun i => (θ i : ℂ)
  let p := MvPolynomial.map GaussianInt.toComplex (characteristic (integralGenerators N))
  ∃ f : Fin (2^N) → (Coordinates N → ℂ) → ℂ,
    (∀ j, AnalyticAt ℂ (f j) x ∧
      ∀ᶠ z in 𝓝 x, matrixCharpolyRelation (∑ a, z a • chainPauliFin N a,f j z) = 0) ∧
    Function.Injective (fun j => f j x) ∧
    let A := Matrix.of fun i j => rowValue (rows i) (f j) x
    let s := fun j => onRoot (MvPolynomial.pderiv none p) (f j) x ^ (2*L)
    (∀ i j, A i j * s j = onRoot (jetRow p L (rows i)) (f j) x) ∧
    ∀ m : Fin (2^N) → ℤ, m ≠ 0 → ∑ j, m j = 0 →
      ∃ i w, rows i = some w ∧
        lower ≤ (responseScale A s * ((2^N : ℕ) : ℝ) * ‖∑ j, mixed w (f j) x * (m j : ℂ)‖)^2

private theorem simple_of_nonzero {n D : ℕ} {R : Type*} [CommRing R]
    (A : Fin n → Matrix (Fin D) (Fin D) R) (φ : R →+* ℂ) (P : Fin n → Matrix (Fin D) (Fin D) ℂ)
    (hm : (fun j => (A j).map φ) = P) (θ : Fin n → ℝ) (hH : (spectralEnsembleMatrix P θ).IsHermitian)
    (L : ℕ) (rows : Fin D → Option (List (Fin n)))
    (hn : eval₂Hom φ (fun i => (θ i : ℂ)) (jetGram A L rows) ≠ 0) :
    Function.Injective hH.eigenvalues := by
  subst P
  let x : Fin n → ℂ := fun i => (θ i : ℂ)
  let E (j : Fin D) := (hH.eigenvalues j : ℂ)
  have ht (k : ℕ) : eval₂Hom φ x ((pencil A)^k).trace = ∑ j, E j^k := by
    rw [← trace_mapMatrix,map_pow,eval_pencil]
    exact trace_pow_eq_sum_eigenvalues_pow hH k
  rw [jetGram,eval_gram _ φ x E ht] at hn
  intro i j he
  by_contra h
  have hE : E i = E j := congrArg Complex.ofReal he
  apply hn
  rw [Matrix.det_zero_of_column_eq h (fun l => by simp only [Matrix.of_apply,hE])]
  norm_num

private theorem row_on_chart {n D : ℕ} {R : Type*} [CommRing R]
    (A : Fin n → Matrix (Fin D) (Fin D) R) (φ : R →+* ℂ) (P : Fin n → Matrix (Fin D) (Fin D) ℂ)
    (hm : (fun a => (A a).map φ) = P) {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (f : (Fin n → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f U)
    (hr : ∀ z ∈ U, matrixCharpolyRelation (∑ a, z a • P a,f z) = 0)
    (hs : ∀ z ∈ U, onRoot (MvPolynomial.pderiv none (MvPolynomial.map φ (characteristic A))) f z ≠ 0)
    {x : Fin n → ℂ} (hx : x ∈ U) (L : ℕ) (w : Option (List (Fin n))) (hw : ∀ v ∈ w, v.length ≤ L) :
    let p := MvPolynomial.map φ (characteristic A)
    rowValue w f x * onRoot (MvPolynomial.pderiv none p) f x ^ (2*L) = onRoot (jetRow p L w) f x := by
  subst P
  intro p
  apply (row_eval p L w hw f hU (fun z hz => (hf z hz).differentiableAt.differentiableWithinAt) _ hs x hx).symm
  intro z hz
  rw [onRoot,show p = MvPolynomial.map φ (characteristic A) from rfl,eval_map]
  exact (eval_characteristic A φ z (f z)).trans (hr z hz)

private theorem detect_at_sample (N L : ℕ) (rows : Fin (2^N) → Option (List (Coordinates N)))
    (hw : ∀ i w, w ∈ rows i → w.length ≤ L) (θ : Coordinates N → ℝ) {a : ℝ} (ha : 0 < a)
    (he : a ≤ ‖eval₂Hom GaussianInt.toComplex (fun i => (θ i : ℂ)) (pathDetector N L rows)‖) :
    DetectsBalancedModes N L rows θ a := by
  let x := fun i => (θ i : ℂ)
  let P := integralGenerators N
  let φ := GaussianInt.toComplex
  let H := isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian N) θ
  have hne : eval₂Hom φ x (jetGram P L rows) ≠ 0 := norm_pos_iff.mp (ha.trans_le he)
  have hi := simple_of_nonzero P φ (chainPauliFin N) (funext (generators_map N)) θ H L rows hne
  obtain ⟨r,hr,f,hf,hinj,hroot,hs⟩ := exists_simple_real_pencil_ball P φ (chainPauliFin N)
    (funext (generators_map N)) θ H hi
  have hx : x ∈ Metric.ball x r := Metric.mem_ball_self hr
  refine ⟨f,fun j => ⟨hf j x hx,Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hx) (fun z hz => hroot z hz j)⟩,
    hinj x hx,?_⟩
  intro A s
  constructor
  · intro i j
    exact row_on_chart P φ (chainPauliFin N) (funext (generators_map N)) Metric.isOpen_ball (f j)
      (hf j) (fun z hz => hroot z hz j) (fun z hz => hs z hz j) hx L (rows i) (hw i)
  intro m hm hbal
  have hval := eval_jetGram_on_chart_of_generators P φ (chainPauliFin N) (funext (generators_map N))
    Metric.isOpen_ball f hf hinj hroot hs hx L rows hw
  have hbound : a ≤ ‖A.det * ∏ j, s j‖^2 := by
    exact he.trans_eq ((congrArg norm hval).trans (norm_pow _ 2))
  obtain ⟨i,hi⟩ := exists_cleared_det_response A s (fun j => pow_ne_zero _ (hs x hx j)) m hm
  have hb := hbound.trans (pow_le_pow_left₀ (norm_nonneg _) hi 2)
  cases hv : rows i with
  | none =>
    have hsum : ∑ j, A i j * (m j : ℂ) = 0 := by
      simpa only [A,Matrix.of_apply,hv,rowValue,Option.elim_none,one_mul] using
        (show ∑ j, (m j : ℂ) = 0 by exact_mod_cast hbal)
    rw [hsum,norm_zero,mul_zero,zero_pow (by decide)] at hb
    exact (ha.not_ge hb).elim
  | some w => exact ⟨i,w,hv,by simpa only [A,Matrix.of_apply,hv,rowValue,Option.elim_some] using hb⟩

/-- On one iid path, all sufficiently long prefixes admit a deterministic family
of orders at most D−2 which responds to every balanced nonzero integer mode.
The prefactor is computed from the cleared entries at the sample. -/
theorem gaussian_path_eventually_detects_balanced_modes :
    ∃ rows : (k : ℕ) → Fin (2^(k+3)) → Option (List (Coordinates (k+3))),
      (∀ k i w, w ∈ rows k i → w.length ≤ 2^(k+3)-2) ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
        let B := prefixDetectorDegree k
        let θ := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
        DetectsBalancedModes (k+3) (2^(k+3)-2) (rows k) θ (((1/2:ℝ)^k/(1+2*B))^B) := by
  obtain ⟨rows,hw,hg⟩ := gaussian_path_eventually_large_detector
  refine ⟨rows,hw,?_⟩
  filter_upwards [hg] with ω hω
  filter_upwards [hω] with k hk
  exact detect_at_sample _ _ (rows k) (hw k) _ (by positivity) hk

#print axioms gaussian_path_eventually_detects_balanced_modes
end
end GaloisForLFunctions.HTGeometry.SpectralJets
