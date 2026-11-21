import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.PauliDetector
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.ComplexChart
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Rank.LocalRank
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Rank.RealSlice
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Rank.Border
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCoordinates
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # A nonzero polynomial detector of bounded order for each Pauli path -/
open MvPolynomial Matrix Set Metric MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- Specialization with separate integral and complex matrix generators. -/
theorem eval_jetGram_on_chart_of_generators {n D : ℕ} {R : Type*} [CommRing R]
    (A : Fin n → Matrix (Fin D) (Fin D) R) (φ : R →+* ℂ) (P : Fin n → Matrix (Fin D) (Fin D) ℂ)
    (hm : (fun a => (A a).map φ) = P) {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (f : Fin D → (Fin n → ℂ) → ℂ) (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hi : ∀ z ∈ U, Function.Injective fun j => f j z)
    (hr : ∀ z ∈ U, ∀ j, matrixCharpolyRelation (∑ a, z a • P a,f j z) = 0)
    (hs : ∀ z ∈ U, ∀ j, onRoot (MvPolynomial.pderiv none (MvPolynomial.map φ (characteristic A))) (f j) z ≠ 0)
    {x : Fin n → ℂ} (hx : x ∈ U) (L : ℕ) (rows : Fin D → Option (List (Fin n)))
    (hw : ∀ i v, v ∈ rows i → v.length ≤ L) :
    eval₂Hom φ x (jetGram A L rows) =
      ((Matrix.of fun i j => rowValue (rows i) (f j) x).det *
        ∏ j, (onRoot (MvPolynomial.pderiv none (MvPolynomial.map φ (characteristic A))) (f j) x)^(2*L))^2 := by
  subst P
  exact eval_jetGram_on_chart A φ hU f hf hi hr hs hx L rows hw

/-- For each chain there is one fixed choice of derivative rows, of orders at most
D−2, whose cleared squared determinant is a nonzero polynomial in the couplings. -/
theorem exists_pathDetector_ne_zero (k : ℕ) :
    let N := k+3
    let D := 2^N
    ∃ rows : Fin D → Option (List (Coordinates N)),
      (∀ i w, w ∈ rows i → w.length ≤ D-2) ∧
      map GaussianInt.toComplex (pathDetector N (D-2) rows) ≠ 0 := by
  intro N D
  let d := D-1
  have hD : d+1 = D := Nat.sub_add_cancel (Nat.two_pow_pos N)
  let e : Fin (d+1) ≃ Fin D := finCongr hD
  let A := integralGenerators N
  let φ := GaussianInt.toComplex
  obtain ⟨θ,hθ⟩ := exists_chainShell_maximallyProjective_witness k
  let x := realPoint θ
  obtain ⟨r,hr,f,hf,hi,hroo,hs⟩ := exists_simple_real_pencil_ball A φ (chainPauliFin N)
    (funext (generators_map N)) θ (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian N) θ) hθ.injective
  let U := ball x r
  let F (j : Fin d) (z : Coordinates N → ℂ) := f (e j.succ) z - f (e 0) z
  have hfree : locallyIndependent U F := by
    intro V hVU hV hne c hrel
    apply path_gap_chart_independent k d (e 0) (fun j => e j.succ) (e.injective.comp (Fin.succ_injective d))
      (fun j h => Fin.succ_ne_zero j (e.injective h)) θ hr f hf hi hroo hVU hV hne c hrel
  obtain ⟨z,hz,w,hw,hdet⟩ := exists_full_mixed_rank d F U isOpen_ball ⟨x,mem_ball_self hr⟩
    (fun j y hy => (hf _ y hy).sub (hf _ y hy)) hfree
  let v : Fin (d+1) → Option (List (Coordinates N)) := Fin.cons none (fun i => some (w i))
  let rows := fun i => v (e.symm i)
  have hv (i t) (ht : t ∈ rows i) : t.length ≤ D-2 := by
    have hl : d-1 = D-2 := by dsimp [d]; omega
    rw [← hl]
    change t ∈ v (e.symm i) at ht
    revert ht
    refine Fin.cases (by simp [v]) (fun j => ?_) (e.symm i)
    simp only [v,Fin.cons_succ]
    intro ht
    have hh := Option.some.inj ht
    subst t
    exact hw j
  refine ⟨rows,hv,?_⟩
  let M := Matrix.of fun i j => rowValue (rows i) (f j) z
  let R : Matrix (Fin d) (Fin (d+1)) ℂ := fun i j => mixed (w i) (f (e j)) z
  have hg : (Matrix.of fun i j => mixed (w i) (F j) z) =
      Matrix.of (fun i j => R i j.succ - R i 0) := by
    ext i j
    exact mixed_sub (w i) (hf _ z hz) (hf _ z hz)
  have hmixed : M.det ≠ 0 := by
    rw [← Matrix.det_submatrix_equiv_self e M]
    have hj : M.submatrix e e = Matrix.of (Fin.cons (fun _ => (1:ℂ)) R) := by
      ext i j
      refine Fin.cases ?_ (fun l => ?_) i <;> simp [M,rows,v,R,rowValue]
    rw [hj]
    rw [hg] at hdet
    exact det_cons_one_ne_zero R hdet
  have heval := eval_jetGram_on_chart_of_generators A φ (chainPauliFin N) (funext (generators_map N))
    (U := U) isOpen_ball f hf hi hroo hs hz (D-2) rows hv
  have hprod := Finset.prod_ne_zero_iff.mpr (fun j (_ : j ∈ Finset.univ) => pow_ne_zero (2*(D-2)) (hs z hz j))
  intro hzero
  have hz' := congrArg (eval z) hzero
  rw [eval_map,map_zero] at hz'
  exact (pow_ne_zero 2 (mul_ne_zero hmixed hprod)) (heval.symm.trans hz')

/-- With D=2^N the detector has degree at most 2D(1+2D(D−2)).
Its Gaussian lower tail costs the same degree, uniformly for all 0 < r ≤ 1. -/
theorem gaussian_path_nonvanishing_detector_lower_tail (k : ℕ) :
    let N := k+3
    let D := 2^N
    let B := D*(2*(1+2*(D-2)*D))
    ∃ rows : Fin D → Option (List (Coordinates N)),
      (∀ i w, w ∈ rows i → w.length ≤ D-2) ∧
      map GaussianInt.toComplex (pathDetector N (D-2) rows) ≠ 0 ∧
      (pathDetector N (D-2) rows).totalDegree ≤ B ∧
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        (Measure.pi fun _ : Coordinates N => gaussianReal 0 1)
        {x | ‖eval₂Hom GaussianInt.toComplex (fun i => (x i : ℂ)) (pathDetector N (D-2) rows)‖ < r^B}
          ≤ ENNReal.ofReal (2*(B:ℝ)*r) := by
  intro N D B
  obtain ⟨rows,hw,hn⟩ := exists_pathDetector_ne_zero k
  exact ⟨rows,hw,hn,pathDetector_degree N (D-2) rows hw,
    fun _ hr hr' => pathDetector_lower_tail_of_nonzero N (D-2) rows hw hn hr hr'⟩

/-- Degree bound for the nonzero detector on the prefix of k+3 sites. -/
def prefixDetectorDegree (k : ℕ) : ℕ :=
  let D := 2^(k+3)
  D*(2*(1+2*(D-2)*D))

/-- One deterministic choice of rows per length has an explicit lower bound on
every sufficiently long prefix of a single infinite Gaussian chain. -/
theorem gaussian_path_eventually_large_detector :
    ∃ rows : (k : ℕ) → Fin (2^(k+3)) → Option (List (Coordinates (k+3))),
      (∀ k i w, w ∈ rows k i → w.length ≤ 2^(k+3)-2) ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
        let B := prefixDetectorDegree k
        let θ := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
        ((1/2:ℝ)^k/(1+2*B))^B ≤
          ‖eval₂Hom GaussianInt.toComplex (fun i => (θ i : ℂ))
            (pathDetector (k+3) (2^(k+3)-2) (rows k))‖ := by
  choose rows hw _ _ hb using gaussian_path_nonvanishing_detector_lower_tail
  refine ⟨rows,hw,?_⟩
  let B := prefixDetectorDegree
  let r (k : ℕ) := (1/2:ℝ)^k/(1+2*(B k:ℝ))
  let bad (k : ℕ) : Set (Coordinates (k+3) → ℝ) := {x |
    ‖eval₂Hom GaussianInt.toComplex (fun i => (x i : ℂ)) (pathDetector (k+3) (2^(k+3)-2) (rows k))‖ < (r k)^(B k)}
  let coords (k : ℕ) (ω : PathPauliDisorder) := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  have hm (k : ℕ) : pathPauliDisorderLaw (coords k ⁻¹' bad k) ≤ (1/2:ℝ≥0∞)^k := by
    have hden : 0 < 1+2*(B k:ℝ) := by positivity
    have hr : 0 < r k := by dsimp [r]; positivity
    have hhalf : (1/2:ℝ)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hr' : r k ≤ 1 := by
      apply (div_le_iff₀ hden).mpr
      linarith only [hhalf,Nat.cast_nonneg (α := ℝ) (B k)]
    have hmp := gaussian_pauli_prefix_coordinates_law (k+1)
    refine (Measure.le_map_apply hmp.measurable.aemeasurable (bad k)).trans ?_
    rw [hmp.map_eq]
    refine (hb k (r k) hr hr').trans ?_
    have hprice : 2*(B k:ℝ)*r k ≤ (1/2:ℝ)^k := by
      change 2*(B k:ℝ)*(_/_) ≤ _
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).mpr
      linarith only [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) k]
    exact (ENNReal.ofReal_le_ofReal hprice).trans_eq (by
      rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/2),one_div,
        ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<2)]
      norm_num)
  have hfin : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, ω ∉ coords k ⁻¹' bad k := by
    apply ae_eventually_notMem
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hm)
    simp only [one_div,ENNReal.tsum_geometric_two]
    norm_num
  filter_upwards [hfin] with ω hω
  filter_upwards [hω] with k hk
  exact le_of_not_gt hk

#print axioms gaussian_path_nonvanishing_detector_lower_tail
#print axioms gaussian_path_eventually_large_detector
end
end GaloisForLFunctions.HTGeometry.SpectralJets
