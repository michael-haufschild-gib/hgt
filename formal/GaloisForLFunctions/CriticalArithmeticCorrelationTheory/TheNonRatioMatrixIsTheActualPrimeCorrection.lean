import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTouchingCrossMatrixHasAUniformErrorBudget
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheBoundaryPrimeStarVanishesAfterNormalization
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheRowsAtBoundedOverlap
import Mathlib.Analysis.Matrix.Spectrum

/-!
# The actual non-ratio prime matrix

Finite prime-pairing linearity identifies the literal atom matrix with the
prime sum of its synthesized test. Subtracting the ratio kernel therefore
leaves exactly the non-ratio source form, with the actual atom mass retained.
-/

noncomputable section

open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open ArithmeticLorentzianGeometry ArithmeticElectrostatics ArithmeticEffectivityTheory
  SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory
open _root_.RHTower (vonMangoldtAtom)

private theorem primePair_self (f : ℝ → ℝ) : primePair f f = primeSum f := rfl

/-- Compact support turns the prime pairing into a finite sum before linearity is used. -/
theorem primePair_finsetSum_right {ι : Type*} (s : Finset ι) {R : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfR : SupportedIn R f)
    {d : ι → ℝ → ℝ} (hd : ∀ i, Continuous (d i)) (hdR : ∀ i, SupportedIn R (d i))
    (x : ι → ℝ) :
    primePair f (fun u => ∑ i ∈ s, x i * d i u) = ∑ i ∈ s, x i * primePair f (d i) := by
  rw [primePair_eq_sum_of_supportedIn hfR (supportedIn_sum s hdR x)]
  simp_rw [primePair_eq_sum_of_supportedIn hfR (hdR _)]
  have e : ∀ c : ℝ, ∫ t, f t * ∑ i ∈ s, x i * d i (t + c) =
      ∑ i ∈ s, x i * ∫ t, f t * d i (t + c) := by
    intro c
    simp_rw [mul_sum]
    rw [integral_finsetSum _ fun i _ => by
      simpa [mul_left_comm] using (integrable_mul_shift hf hfc (hd i) c).const_mul (x i)]
    apply sum_congr rfl
    intro i hi
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
  simp_rw [sub_eq_add_neg, e, mul_sum, ← sum_add_distrib, mul_sum]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun k _ => by ring

/-- The actual prime sum of a finite smooth family is its prime-pairing quadratic form. -/
theorem primeSum_finsetSum_eq {ι : Type*} (s : Finset ι) {R : ℝ} {e : ι → ℝ → ℝ}
    (he : ∀ i, ContDiff ℝ 2 (e i)) (heR : ∀ i, SupportedIn R (e i)) (x : ι → ℝ) :
    primeSum (fun u => ∑ i ∈ s, x i * e i u) =
      ∑ i ∈ s, ∑ j ∈ s, x i * x j * primePair (e i) (e j) := by
  have hF : ContDiff ℝ 2 fun u => ∑ i ∈ s, x i * e i u :=
    ContDiff.sum fun i _ => contDiff_const.mul (he i)
  have hFc : HasCompactSupport fun u => ∑ i ∈ s, x i * e i u :=
    HasCompactSupport.intro (K := Set.Icc (-R) R) isCompact_Icc fun u hu =>
      supportedIn_sum s heR x u (by
        by_contra h
        push Not at h
        exact hu (abs_le.mp h))
  have hec : ∀ i, HasCompactSupport (e i) := by
    intro i
    exact HasCompactSupport.intro (K := Set.Icc (-R) R) isCompact_Icc fun u hu =>
      heR i u (by
        by_contra h
        push Not at h
        exact hu (abs_le.mp h))
  rw [← primePair_self, primePair_finsetSum_right s hF.continuous hFc (supportedIn_sum s heR x)
    (fun i => (he i).continuous) heR]
  apply sum_congr rfl
  intro i hi
  rw [primePair_comm, primePair_finsetSum_right s (he i).continuous (hec i) (heR i)
    (fun j => (he j).continuous) heR, mul_sum]
  exact sum_congr rfl fun j _ => by ring

/-- The horizon matrix of literal prime pairings is the actual synthesized prime form. -/
theorem horizonPrimePair_inner_eq_primeSum {g : ℝ → ℝ} {w : ℝ}
    (hg : ContDiff ℝ 2 g) (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w)
    (N : ℕ) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin (horizonKernelMatrix (fun m n => primePair (atom g m) (atom g n)) N) x, x⟫ =
      primeSum (atomicTest N (primeHorizonExtension x) g) := by
  have heq : atomicTest N (primeHorizonExtension x) g =
      fun u => ∑ n : PrimeHorizonIndex N, x n * atom g n u := by
    funext u
    rw [atomicTest, ← sum_coe_sort (Icc 1 N) (fun n => primeHorizonExtension x n * g (u - Real.log n))]
    apply sum_congr rfl
    intro n hn
    simp only [primeHorizonExtension_coe, atom]
  have hsum := primeSum_finsetSum_eq (univ : Finset (PrimeHorizonIndex N))
    (fun n => contDiff_atom hg (n : ℕ))
    (fun n => supportedIn_atom hsupp hw n.property) (fun n => x n)
  rw [heq, hsum, EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ n : PrimeHorizonIndex N, x n *
    (∑ j : PrimeHorizonIndex N, primePair (atom g n) (atom g j) * x j)) =
      ∑ n : PrimeHorizonIndex N, ∑ j : PrimeHorizonIndex N,
        x n * x j * primePair (atom g n) (atom g j)
  apply sum_congr rfl
  intro n hn
  rw [mul_sum]
  exact sum_congr rfl fun j _ => by ring

/-- The literal normalized prime matrix after its exact-ratio part is removed. -/
def fullWeilNonRatioMatrix (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ :=
  (∫ u, atomDilate φ (c / N) u ^ 2)⁻¹ •
    horizonKernelMatrix (fun m n => primePair (atom (atomDilate φ (c / N)) m)
      (atom (atomDilate φ (c / N)) n)) N - fullPrimeMatrix N

theorem fullWeilNonRatioMatrix_apply (φ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    (n j : PrimeHorizonIndex N) :
    fullWeilNonRatioMatrix φ c N n j =
      primePair (atom (atomDilate φ (c / N)) n) (atom (atomDilate φ (c / N)) j) /
        (∫ u, atomDilate φ (c / N) u ^ 2) - weilPrimeKernel n j := by
  simp only [fullWeilNonRatioMatrix, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    horizonKernelMatrix, fullPrimeMatrix]
  ring

theorem fullWeilNonRatioMatrix_isHermitian (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    (fullWeilNonRatioMatrix φ c N).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro n j
  change fullWeilNonRatioMatrix φ c N j n = fullWeilNonRatioMatrix φ c N n j
  rw [fullWeilNonRatioMatrix_apply, fullWeilNonRatioMatrix_apply, primePair_comm, weilPrimeKernel_comm]

/-- Every vector reads exactly the normalized non-ratio prime source, at every width. -/
theorem fullWeilNonRatioMatrix_inner_eq {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) x, x⟫ =
      nonRatioForm (atomDilate φ (c / N)) N (primeHorizonExtension x) /
        (∫ u, atomDilate φ (c / N) u ^ 2) := by
  have hw : 0 < c / (N : ℝ) := div_pos hc (by exact_mod_cast hN)
  obtain ⟨hg, hgsupp, hgc⟩ := atomDilate_facts hφ hsupp hw
  have hG : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw hM
  rw [fullWeilNonRatioMatrix, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    inner_sub_left, real_inner_smul_left,
    horizonPrimePair_inner_eq_primeSum hg hgsupp hw.le,
    primeSum_atomicTest_eq_ratio_add hg.continuous hgc hgsupp hw.le,
    atomicWeilForm_primeHorizonExtension]
  field_simp [hG.ne']

/-- One horizon makes the whole actual non-ratio matrix small for every ratio up to one. -/
theorem eventually_fullWeilNonRatioMatrix_small_uniformly {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ 1 →
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        |⟪Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) x, x⟫| ≤ ε * ‖x‖ ^ 2 := by
  filter_upwards [eventually_normalized_nonRatioForm_small_uniformly hφ hsupp hM hε,
    eventually_ge_atTop 1] with N hsmall hN
  intro c hc0 hc1 x
  have hw : 0 < c / (N : ℝ) := div_pos hc0 (by exact_mod_cast hN)
  have hG : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw hM
  rw [fullWeilNonRatioMatrix_inner_eq hφ hsupp hM hc0 hN x, abs_div, abs_of_pos hG]
  have h := hsmall c hc0 hc1 (primeHorizonExtension x)
  rwa [sum_primeHorizonExtension_sq] at h

private theorem hermitian_action_le_of_abs_form_le {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℝ} (hA : A.IsHermitian) {ε : ℝ} (hε : 0 ≤ ε)
    (hform : ∀ x : EuclideanSpace ℝ I, |⟪Matrix.toEuclideanLin A x, x⟫| ≤ ε * ‖x‖ ^ 2)
    (x : EuclideanSpace ℝ I) : ‖Matrix.toEuclideanLin A x‖ ≤ ε * ‖x‖ := by
  have happ (i : I) : Matrix.toEuclideanLin A (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    ext j
    exact congrFun (hA.mulVec_eigenvectorBasis i) j
  have heig (i : I) : |hA.eigenvalues i| ≤ ε := by
    have hi : ⟪hA.eigenvectorBasis i, hA.eigenvectorBasis i⟫ = (1 : ℝ) := by
      simpa only [ite_true] using (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i i
    have hn : ‖hA.eigenvectorBasis i‖ ^ 2 = (1 : ℝ) := by
      rwa [real_inner_self_eq_norm_sq] at hi
    simpa only [happ, real_inner_smul_left, hi, hn, mul_one] using hform (hA.eigenvectorBasis i)
  have hinner (i : I) : ⟪Matrix.toEuclideanLin A x, hA.eigenvectorBasis i⟫ =
      hA.eigenvalues i * ⟪x, hA.eigenvectorBasis i⟫ := by
    rw [(Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) x (hA.eigenvectorBasis i),
      happ, real_inner_smul_right]
  have hs : ‖Matrix.toEuclideanLin A x‖ ^ 2 ≤ ε ^ 2 * ‖x‖ ^ 2 := by
    rw [← hA.eigenvectorBasis.sum_sq_inner_left (Matrix.toEuclideanLin A x),
      ← hA.eigenvectorBasis.sum_sq_inner_left x, mul_sum]
    apply sum_le_sum
    intro i hi
    rw [hinner, mul_pow]
    have hb := mul_self_le_mul_self (abs_nonneg (hA.eigenvalues i)) (heig i)
    rw [← sq, sq_abs, ← sq] at hb
    exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  have hprod : 0 ≤ ε * ‖x‖ := mul_nonneg hε (norm_nonneg x)
  nlinarith only [hs, hprod, norm_nonneg (Matrix.toEuclideanLin A x)]

/-- The actual boundary correction also vanishes in operator action, uniformly in ratio. -/
theorem eventually_fullWeilNonRatioMatrix_action_small_uniformly {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ 1 →
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        ‖Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) x‖ ≤ ε * ‖x‖ := by
  filter_upwards [eventually_fullWeilNonRatioMatrix_small_uniformly hφ hsupp hM hε] with N hN
  intro c hc0 hc1 x
  exact hermitian_action_le_of_abs_form_le (fullWeilNonRatioMatrix_isHermitian φ c N)
    hε.le (hN c hc0 hc1) x

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.fullWeilNonRatioMatrix_inner_eq

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_fullWeilNonRatioMatrix_small_uniformly
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_fullWeilNonRatioMatrix_action_small_uniformly
