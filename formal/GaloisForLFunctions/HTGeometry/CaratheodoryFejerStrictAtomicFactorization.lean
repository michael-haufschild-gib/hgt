import GaloisForLFunctions.HTGeometry.FiniteAtomicCubature
import GaloisForLFunctions.HTGeometry.BernsteinSzegoProbabilityApproximation
import GaloisForLFunctions.HTGeometry.CaratheodoryFejerAtomicGramFactorization
import Mathlib.Analysis.Convex.Integral

/-!
# Strict Carathéodory--Fejér atomic factorization

For a normalized Hermitian Toeplitz sequence with a one-step positive-definite
extension, this module constructs an exact finite unit-circle atomic measure
with the required Fourier prefix.  It combines the actual Bernstein--Szegő
probability law with finite-dimensional Carathéodory cubature, then identifies
the resulting Toeplitz matrix literally as the weighted Vandermonde Gram matrix
`Bᴴ B`.

This is the strict positive-definite branch.  The singular PSD/rank-defect
branch is deliberately not claimed here.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Set Topology
open scoped BigOperators ComplexOrder

noncomputable section

/-- Real coordinate vector containing real and imaginary parts of the first
`N` circle Fourier monomials. -/
def circleFourierCoordinate (N : ℕ) (z : Circle) : Fin (N + N) → ℝ :=
  Fin.addCases
    (fun k => ((z : ℂ) ^ (-(((k : ℕ) + 1 : ℕ) : ℤ))).re)
    (fun k => ((z : ℂ) ^ (-(((k : ℕ) + 1 : ℕ) : ℤ))).im)

theorem circleFourierCoordinate_real (N : ℕ) (z : Circle) (k : Fin N) :
    circleFourierCoordinate N z (Fin.castAdd N k) =
      ((z : ℂ) ^ (-(((k : ℕ) + 1 : ℕ) : ℤ))).re := by
  unfold circleFourierCoordinate Fin.addCases
  simp

theorem circleFourierCoordinate_imag (N : ℕ) (z : Circle) (k : Fin N) :
    circleFourierCoordinate N z (Fin.natAdd N k) =
      ((z : ℂ) ^ (-(((k : ℕ) + 1 : ℕ) : ℤ))).im := by
  unfold circleFourierCoordinate Fin.addCases
  simp

theorem continuous_circleFourierMonomial (n : ℕ) :
    Continuous (fun z : Circle => (z : ℂ) ^ (-((n : ℕ) : ℤ))) := by
  rw [show (fun z : Circle => (z : ℂ) ^ (-((n : ℕ) : ℤ))) =
      fun z : Circle => ((z : ℂ) ^ n)⁻¹ by
        funext z
        rw [zpow_neg, zpow_natCast]]
  exact (by fun_prop : Continuous fun z : Circle => (z : ℂ) ^ n).inv₀
    (fun z => pow_ne_zero _ (Circle.coe_ne_zero z))

theorem integrable_circleFourierMonomial (n : ℕ) (mu : Measure Circle)
    [IsProbabilityMeasure mu] :
    Integrable (fun z : Circle => (z : ℂ) ^ (-((n : ℕ) : ℤ))) mu := by
  refine Integrable.of_bound (continuous_circleFourierMonomial n).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun z => ?_)
  simp

theorem sum_real_mul_re_eq_re_sum {r : ℕ} (weight : Fin r → ℝ) (u : Fin r → ℂ) :
    (∑ i, weight i * (u i).re) = (∑ i, (weight i : ℂ) * u i).re := by
  calc
    (∑ i, weight i * (u i).re) =
        ∑ i, Complex.reCLM ((weight i : ℂ) * u i) := by
          apply Finset.sum_congr rfl
          intro i _
          simp [Complex.reCLM, Complex.mul_re]
    _ = Complex.reCLM (∑ i, (weight i : ℂ) * u i) :=
      (map_sum Complex.reCLM _ _).symm
    _ = (∑ i, (weight i : ℂ) * u i).re := rfl

theorem sum_real_mul_im_eq_im_sum {r : ℕ} (weight : Fin r → ℝ) (u : Fin r → ℂ) :
    (∑ i, weight i * (u i).im) = (∑ i, (weight i : ℂ) * u i).im := by
  calc
    (∑ i, weight i * (u i).im) =
        ∑ i, Complex.imCLM ((weight i : ℂ) * u i) := by
          apply Finset.sum_congr rfl
          intro i _
          simp [Complex.imCLM, Complex.mul_im]
    _ = Complex.imCLM (∑ i, (weight i : ℂ) * u i) :=
      (map_sum Complex.imCLM _ _).symm
    _ = (∑ i, (weight i : ℂ) * u i).im := rfl

theorem continuous_circleFourierCoordinate (N : ℕ) :
    Continuous (circleFourierCoordinate N) := by
  apply continuous_pi
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro k
    have hfun : (fun a : Circle => circleFourierCoordinate N a (Fin.castAdd N k)) =
        fun a : Circle => ((a : ℂ) ^ (-(((k : ℕ) + 1 : ℕ) : ℤ))).re := by
      funext a
      exact circleFourierCoordinate_real N a k
    rw [hfun]
    exact Complex.continuous_re.comp
      (continuous_circleFourierMonomial ((k : ℕ) + 1))
  · intro k
    have hfun : (fun a : Circle => circleFourierCoordinate N a
        (Fin.natAdd N k)) =
        fun a : Circle => ((a : ℂ) ^ (-(((k : ℕ) + 1 : ℕ) : ℤ))).im := by
      funext a
      exact circleFourierCoordinate_imag N a k
    rw [hfun]
    exact Complex.continuous_im.comp (continuous_circleFourierMonomial ((k : ℕ) + 1))

theorem integrable_circleFourierCoordinate (N : ℕ) (mu : Measure Circle)
    [IsProbabilityMeasure mu] :
    Integrable (circleFourierCoordinate N) mu := by
  rw [← integrableOn_univ]
  exact (continuous_circleFourierCoordinate N).continuousOn.integrableOn_compact isCompact_univ

theorem integral_circleFourierCoordinate_castAdd (mu : Measure Circle)
    [IsProbabilityMeasure mu] (N : ℕ) (k : Fin N) :
    (∫ z : Circle, circleFourierCoordinate N z ∂mu) (Fin.castAdd N k) =
      (circleMeasureMomentZ mu ((k : ℕ) + 1)).re := by
  change (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (N + N) => ℝ)
    (Fin.castAdd N k) : (Fin (N + N) → ℝ) →ₗ[ℝ] ℝ)
      (∫ z : Circle, circleFourierCoordinate N z ∂mu) = _
  calc
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (N + N) => ℝ)
      (Fin.castAdd N k))
        (∫ z : Circle, circleFourierCoordinate N z ∂mu) =
        ∫ z : Circle,
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (N + N) => ℝ)
            (Fin.castAdd N k)) (circleFourierCoordinate N z) ∂mu := by
          symm
          exact ContinuousLinearMap.integral_comp_comm _
            (integrable_circleFourierCoordinate N mu)
    _ = ∫ z : Circle,
      ((z : ℂ) ^ (-(((k : ℕ) + 1 : ℕ) : ℤ))).re ∂mu := by
        simp [circleFourierCoordinate]
    _ = (circleMeasureMomentZ mu ((k : ℕ) + 1)).re := by
      simpa [circleMeasureMomentZ] using
        (integral_re (integrable_circleFourierMonomial ((k : ℕ) + 1) mu))

theorem integral_circleFourierCoordinate_natAdd (mu : Measure Circle)
    [IsProbabilityMeasure mu] (N : ℕ) (k : Fin N) :
    (∫ z : Circle, circleFourierCoordinate N z ∂mu) (Fin.natAdd N k) =
      (circleMeasureMomentZ mu ((k : ℕ) + 1)).im := by
  change (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (N + N) => ℝ)
    (Fin.natAdd N k) : (Fin (N + N) → ℝ) →ₗ[ℝ] ℝ)
      (∫ z : Circle, circleFourierCoordinate N z ∂mu) = _
  calc
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (N + N) => ℝ)
      (Fin.natAdd N k))
        (∫ z : Circle, circleFourierCoordinate N z ∂mu) =
        ∫ z : Circle,
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (N + N) => ℝ)
            (Fin.natAdd N k)) (circleFourierCoordinate N z) ∂mu := by
          symm
          exact ContinuousLinearMap.integral_comp_comm _
            (integrable_circleFourierCoordinate N mu)
    _ = ∫ z : Circle,
      ((z : ℂ) ^ (-(((k : ℕ) + 1 : ℕ) : ℤ))).im ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with z
        change circleFourierCoordinate N z (Fin.natAdd N k) = _
        exact circleFourierCoordinate_imag N z k
    _ = (circleMeasureMomentZ mu ((k : ℕ) + 1)).im := by
      simpa [circleMeasureMomentZ] using
        (integral_im (integrable_circleFourierMonomial ((k : ℕ) + 1) mu))

/-- Finite exact cubature for the first `N` Fourier moments of any circle
probability measure. -/
theorem exists_atomic_circleFourier_prefix (mu : ProbabilityMeasure Circle) (N : ℕ) :
    ∃ (weight : Fin ((N + N) + 1) → ℝ) (node : Fin ((N + N) + 1) → Circle),
      (∀ i, 0 ≤ weight i) ∧ (∑ i, weight i = 1) ∧
        ∀ k : Fin N,
          circleMeasureMomentZ (mu : Measure Circle) ((k : ℕ) + 1) =
            ∑ i, (weight i : ℂ) * (node i : ℂ) ^ (-(((k : ℕ) + 1 : ℕ) : ℤ)) := by
  let f : Circle → Fin (N + N) → ℝ := circleFourierCoordinate N
  let K : Set (Fin (N + N) → ℝ) := Set.range f
  have hK : IsCompact K := by
    simpa only [K, f] using isCompact_range (continuous_circleFourierCoordinate N)
  have hKne : K.Nonempty := Set.range_nonempty _
  have hfi : Integrable f (mu : Measure Circle) := integrable_circleFourierCoordinate N mu
  have hmem : (∫ z : Circle, f z ∂(mu : Measure Circle)) ∈
      closure (convexHull ℝ K) := by
    have hpoint : ∀ z : Circle, f z ∈ closure (convexHull ℝ K) := by
      intro z
      exact subset_closure (subset_convexHull ℝ K ⟨z, rfl⟩)
    exact (convex_convexHull ℝ K).closure.integral_mem isClosed_closure
      (Filter.Eventually.of_forall hpoint) hfi
  obtain ⟨weight, node, hweight, hsum, hnode, hmoment⟩ :=
    exists_atomic_of_mem_closure_convexHull hK hKne hmem
  change ∀ i, node i ∈ Set.range f at hnode
  have hnode' : ∀ i, ∃ z : Circle, f z = node i := by
    intro i
    exact hnode i
  choose atom hatom using hnode'
  refine ⟨weight, atom, hweight, hsum, ?_⟩
  intro k
  have hreal :
      (circleMeasureMomentZ (mu : Measure Circle) ((k : ℕ) + 1)).re =
        (∑ i, weight i *
          ((atom i : ℂ) ^ (-(((k : ℕ) + 1 : ℕ) : ℤ))).re) := by
    rw [← integral_circleFourierCoordinate_castAdd (mu : Measure Circle) N k]
    calc
      (∫ z : Circle, circleFourierCoordinate N z ∂(mu : Measure Circle))
          (Fin.castAdd N k) =
        (∑ i, weight i • node i) (Fin.castAdd N k) :=
          (congrFun hmoment (Fin.castAdd N k)).symm
      _ = ∑ i, weight i *
          ((atom i : ℂ) ^ (-(((k : ℕ) + 1 : ℕ) : ℤ))).re := by
          simp_rw [← hatom]
          simp [Finset.sum_apply, Pi.smul_apply, f, circleFourierCoordinate]
  have himag :
      (circleMeasureMomentZ (mu : Measure Circle) ((k : ℕ) + 1)).im =
        (∑ i, weight i *
          ((atom i : ℂ) ^ (-(((k : ℕ) + 1 : ℕ) : ℤ))).im) := by
    rw [← integral_circleFourierCoordinate_natAdd (mu : Measure Circle) N k]
    calc
      (∫ z : Circle, circleFourierCoordinate N z ∂(mu : Measure Circle))
          (Fin.natAdd N k) =
        (∑ i, weight i • node i) (Fin.natAdd N k) :=
          (congrFun hmoment (Fin.natAdd N k)).symm
      _ = ∑ i, weight i *
          ((atom i : ℂ) ^ (-(((k : ℕ) + 1 : ℕ) : ℤ))).im := by
          simp_rw [← hatom]
          simp only [Finset.sum_apply, Pi.smul_apply, f]
          apply Finset.sum_congr rfl
          intro i _
          change weight i * circleFourierCoordinate N (atom i) (Fin.natAdd N k) = _
          rw [circleFourierCoordinate_imag]
  apply Complex.ext
  · rw [hreal]
    exact sum_real_mul_re_eq_re_sum weight
      (fun i => (atom i : ℂ) ^ (-(((k : ℕ) + 1 : ℕ) : ℤ)))
  · rw [himag]
    exact sum_real_mul_im_eq_im_sum weight
      (fun i => (atom i : ℂ) ^ (-(((k : ℕ) + 1 : ℕ) : ℤ)))

/-- Two-sided moment sequence of a weighted finite unit-circle configuration. -/
def circleAtomicMoment {r : ℕ} (node : Fin r → ℂ) (weight : Fin r → ℝ) (q : ℤ) : ℂ :=
  ∑ i, (weight i : ℂ) * node i ^ (-q)

/-- A finite configuration supported on the unit circle has Hermitian moments. -/
theorem circleAtomicMoment_isHermitian {r : ℕ} (node : Fin r → ℂ) (weight : Fin r → ℝ)
    (hCircle : ∀ i, ‖node i‖ = 1) :
    IsHermitianMoment (circleAtomicMoment node weight) := by
  intro q
  unfold circleAtomicMoment
  change (∑ i, (weight i : ℂ) * node i ^ (-(-(q : ℤ))) ) =
    (starRingEnd ℂ) (∑ i, (weight i : ℂ) * node i ^ (-(q : ℤ)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hstar (m : ℤ) : star (node i ^ (-m)) = node i ^ m := by
    change (starRingEnd ℂ) (node i ^ (-m)) = _
    calc
      (starRingEnd ℂ) (node i ^ (-m)) = (node i)⁻¹ ^ (-m) := by
        rw [map_zpow₀, ← Complex.inv_eq_conj (hCircle i)]
      _ = (node i ^ (-m))⁻¹ := by rw [_root_.inv_zpow]
      _ = node i ^ (-(-m)) := (_root_.zpow_neg _ (-m)).symm
      _ = node i ^ m := by ring_nf
  change (weight i : ℂ) * node i ^ (-(-(q : ℤ)) : ℤ) =
    star ((weight i : ℂ) * node i ^ (-(q : ℤ)))
  rw [neg_neg, star_mul, hstar]
  simp
  ring

/-- The atomic moment Toeplitz section is literally the `Bᴴ B` Gram matrix. -/
theorem caratheodoryFejerAtomicGram_eq_circleAtomicToeplitz
    {n r : ℕ} (node : Fin r → ℂ) (weight : Fin r → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (hCircle : ∀ i, ‖node i‖ = 1) :
    caratheodoryFejerAtomicGram (n := n) node weight =
      circleToeplitzGram n (circleAtomicMoment node weight) := by
  ext j k
  simp only [caratheodoryFejerAtomicGram, caratheodoryFejerAtomicFactor,
    Matrix.mul_apply, Matrix.conjTranspose_apply, circleToeplitzGram, circleAtomicMoment]
  rw [Finset.sum_congr rfl]
  intro i _
  have hsqrt : ((Real.sqrt (weight i) : ℂ) * (Real.sqrt (weight i) : ℂ)) = weight i := by
    exact_mod_cast (Real.mul_self_sqrt (hweight i))
  have hstarz : star (node i ^ (j : ℕ)) =
      node i ^ (-((j : ℕ) : ℤ)) := by
    change (starRingEnd ℂ) (node i ^ (j : ℕ)) = _
    rw [map_pow, ← Complex.inv_eq_conj (hCircle i), inv_pow, ← zpow_natCast]
    exact (_root_.zpow_neg _ _).symm
  rw [star_mul, hstarz]
  have hne : node i ≠ 0 := by
    intro hi
    have : ‖node i‖ = 0 := by rw [hi, norm_zero]
    rw [hCircle i] at this
    norm_num at this
  have hpow : node i ^ (-((j : ℕ) : ℤ)) * node i ^ (k : ℕ) =
      node i ^ (-(((j : ℕ) : ℤ) - ((k : ℕ) : ℤ))) := by
    rw [← zpow_natCast]
    calc
      node i ^ (-((j : ℕ) : ℤ)) * node i ^ ((k : ℕ) : ℤ) =
          node i ^ (-((j : ℕ) : ℤ) + ((k : ℕ) : ℤ)) :=
        (zpow_add₀ hne _ _).symm
      _ = node i ^ (-(((j : ℕ) : ℤ) - ((k : ℕ) : ℤ))) := by
        congr 1
        ring
  have hreal : star (Real.sqrt (weight i) : ℂ) = Real.sqrt (weight i) := by simp
  rw [hreal]
  calc
    node i ^ (-((j : ℕ) : ℤ)) * (Real.sqrt (weight i) : ℂ) *
          ((Real.sqrt (weight i) : ℂ) * node i ^ (k : ℕ)) =
        ((Real.sqrt (weight i) : ℂ) * (Real.sqrt (weight i) : ℂ)) *
          (node i ^ (-((j : ℕ) : ℤ)) * node i ^ (k : ℕ)) := by ring
    _ = (weight i : ℂ) * node i ^ (-(((j : ℕ) : ℤ) - ((k : ℕ) : ℤ))) := by
      rw [hsqrt, hpow]

/-- **Strict Carathéodory--Fejér factorization.**  A normalized Hermitian Toeplitz
section with a one-step positive-definite extension has an exact finite atomic factorization.
The atoms have nonnegative real weights and lie on the unit circle. -/
theorem exists_atomic_caratheodoryFejer_strict_factorization
    {N : ℕ} (c : ℤ → ℂ) (hc : IsHermitianMoment c) (hc0 : c 0 = 1)
    (hG : (circleToeplitzGram (N + 1) c).PosDef) :
    ∃ (weight : Fin ((N + N) + 1) → ℝ)
      (node : Fin ((N + N) + 1) → ℂ),
      (∀ i, 0 ≤ weight i) ∧ (∀ i, ‖node i‖ = 1) ∧
        circleToeplitzGram N c = caratheodoryFejerAtomicGram (n := N) node weight := by
  let mu : ProbabilityMeasure Circle :=
    ⟨bernsteinSzegoMeasure c hG,
      IsProbabilityMeasure.mk (bernsteinSzegoMeasure_univ c hG hc0)⟩
  obtain ⟨weight, atom, hweight, hsum, hprefix⟩ :=
    exists_atomic_circleFourier_prefix mu N
  refine ⟨weight, fun i => (atom i : ℂ), hweight,
    fun i => Circle.norm_coe (atom i), ?_⟩
  have hatomic : IsHermitianMoment (circleAtomicMoment (fun i => (atom i : ℂ)) weight) :=
    circleAtomicMoment_isHermitian _ _ (fun i => Circle.norm_coe (atom i))
  have hpositive : ∀ r ≤ N,
      c (r : ℤ) = circleAtomicMoment (fun i => (atom i : ℂ)) weight (r : ℤ) := by
    intro r hr
    cases r with
    | zero =>
        change c 0 = circleAtomicMoment (fun i => (atom i : ℂ)) weight 0
        rw [hc0]
        unfold circleAtomicMoment
        calc
          (1 : ℂ) = ∑ i, (weight i : ℂ) := by
            calc
              (1 : ℂ) = Complex.ofRealHom 1 := rfl
              _ = Complex.ofRealHom (∑ i, weight i) := congrArg _ hsum.symm
              _ = ∑ i, Complex.ofRealHom (weight i) :=
                map_sum Complex.ofRealHom (fun i => weight i) Finset.univ
          _ = ∑ i, (weight i : ℂ) * (atom i : ℂ) ^ (-(0 : ℤ)) := by simp
    | succ r =>
        let k : Fin N := ⟨r, by omega⟩
        have hk : (k : ℕ) + 1 = r + 1 := rfl
        have hsource : circleMeasureMomentZ (mu : Measure Circle) ((r + 1 : ℕ) : ℤ) =
            c ((r + 1 : ℕ) : ℤ) := by
          change circleMeasureMomentZ (bernsteinSzegoMeasure c hG) ((r + 1 : ℕ) : ℤ) = _
          rw [circleMeasureMomentZ_bernsteinSzegoMeasure]
          exact (bernsteinSzegoMoment_prefix c hG ⟨r + 1, by omega⟩).1
        calc
          c ((r + 1 : ℕ) : ℤ) =
              circleMeasureMomentZ (mu : Measure Circle) ((r + 1 : ℕ) : ℤ) := hsource.symm
          _ = ∑ i, (weight i : ℂ) * (atom i : ℂ) ^ (-((r + 1 : ℕ) : ℤ)) := by
              convert hprefix k using 1
              · simp [k]
          _ = circleAtomicMoment (fun i => (atom i : ℂ)) weight ((r + 1 : ℕ) : ℤ) := by
              rfl
  calc
    circleToeplitzGram N c =
        circleToeplitzGram N (circleAtomicMoment (fun i => (atom i : ℂ)) weight) :=
      (circleToeplitzGram_eq_iff_positiveMoment_eq hc hatomic).2 hpositive
    _ = caratheodoryFejerAtomicGram (n := N) (fun i => (atom i : ℂ)) weight :=
      (caratheodoryFejerAtomicGram_eq_circleAtomicToeplitz _ _ hweight
        (fun i => Circle.norm_coe (atom i))).symm

end

end GaloisForLFunctions.HTGeometry
