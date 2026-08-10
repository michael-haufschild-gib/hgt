import GaloisForLFunctions.RHTower.XiShiftedHankelLagrangeCapacity
import GaloisForLFunctions.HTGeometry.FiniteWeightedMonomialFrame

open Matrix Polynomial

namespace RHTower

noncomputable section

open scoped BigOperators

/-- Capacity of one polynomial-independent redundant reconstruction vector. -/
def weightedRedundantSamplingCapacity {N : ℕ}
    (x : Fin N → ℝ) (a : Fin N → ℂ) (z : ℂ) : ℝ :=
  ‖z‖ * ∑ i : Fin N, ‖a i‖ ^ 2 / x i

theorem weightedRedundantSamplingCapacity_nonneg
    {N : ℕ} (x : Fin N → ℝ) (hx : ∀ i, 0 < x i)
    (a : Fin N → ℂ) (z : ℂ) :
    0 ≤ weightedRedundantSamplingCapacity x a z := by
  apply mul_nonneg (norm_nonneg _)
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (sq_nonneg _) (hx i).le

/-- At a packet node, canonical redundant capacity is exactly that node's leverage. -/
theorem weightedRedundantSamplingCapacity_canonical_at_node
    {N n : ℕ} (x : Fin N → ℝ) (hx : ∀ r, 0 < x r)
    (hcard : n ≤ ((Finset.univ : Finset (Fin N)).image x).card) (s : Fin N) :
    weightedRedundantSamplingCapacity x
        (HTGeometry.canonicalMonomialReconstruction x n (x s : ℂ)) (x s : ℂ) =
      HTGeometry.weightedMonomialLeverage x n s := by
  have hunit : IsUnit (HTGeometry.weightedMonomialGram x n).det :=
    isUnit_iff_ne_zero.mpr
      (HTGeometry.weightedMonomialGram_posDef x hx hcard).det_pos.ne'
  simp only [weightedRedundantSamplingCapacity,
    HTGeometry.canonicalMonomialReconstruction_ofReal,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, abs_of_pos (hx s),
    HTGeometry.weightedMonomialLeverage_eq_mul_kernel]
  rw [HTGeometry.canonicalMonomialReconstructionReal_energy_eq_kernel x hx hunit]

/-- Exact capacity-budget law for a positive redundant packet: canonical capacities at all packet
nodes sum to polynomial feature-space dimension. -/
theorem sum_weightedRedundantSamplingCapacity_canonical_at_nodes_eq_dimension
    {N n : ℕ} (x : Fin N → ℝ) (hx : ∀ r, 0 < x r)
    (hcard : n ≤ ((Finset.univ : Finset (Fin N)).image x).card) :
    ∑ s : Fin N, weightedRedundantSamplingCapacity x
        (HTGeometry.canonicalMonomialReconstruction x n (x s : ℂ)) (x s : ℂ) = n := by
  have hunit : IsUnit (HTGeometry.weightedMonomialGram x n).det :=
    isUnit_iff_ne_zero.mpr
      (HTGeometry.weightedMonomialGram_posDef x hx hcard).det_pos.ne'
  simp_rw [weightedRedundantSamplingCapacity_canonical_at_node x hx hcard]
  exact HTGeometry.sum_weightedMonomialLeverage_eq_dimension x hunit

/-- Finite canonical capacity of arbitrary complex targets is exactly a relative moment-matrix
trace.  This compresses atomwise Route-U control into one finite-dimensional Hermitian statistic. -/
theorem ofReal_sum_canonicalRedundantSamplingCapacity_eq_trace
    {N n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Fin N → ℝ) (hx : ∀ r, 0 < x r)
    (hcard : n ≤ ((Finset.univ : Finset (Fin N)).image x).card)
    (z : ι → ℂ) :
    ((∑ q : ι, weightedRedundantSamplingCapacity x
      (HTGeometry.canonicalMonomialReconstruction x n (z q)) (z q) : ℝ) : ℂ) =
      Matrix.trace
        (((HTGeometry.weightedMonomialGram x n)⁻¹.map (algebraMap ℝ ℂ)) *
          HTGeometry.complexTargetMonomialMomentMatrix z (fun q => ‖z q‖) n) := by
  have hunit : IsUnit (HTGeometry.weightedMonomialGram x n).det :=
    isUnit_iff_ne_zero.mpr
      (HTGeometry.weightedMonomialGram_posDef x hx hcard).det_pos.ne'
  calc
    ((∑ q : ι, weightedRedundantSamplingCapacity x
        (HTGeometry.canonicalMonomialReconstruction x n (z q)) (z q) : ℝ) : ℂ) =
        ∑ q : ι, (weightedRedundantSamplingCapacity x
          (HTGeometry.canonicalMonomialReconstruction x n (z q)) (z q) : ℂ) := by
      push_cast
      rfl
    _ = ∑ q : ι, (‖z q‖ : ℂ) *
          HTGeometry.complexWeightedMonomialKernelDiagonal x n (z q) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [weightedRedundantSamplingCapacity]
      push_cast
      have henergy :=
        HTGeometry.canonicalMonomialReconstruction_energy_eq_complexKernelDiagonal
          x hx hunit (z q)
      push_cast at henergy
      rw [henergy]
    _ = _ := HTGeometry.sum_mul_complexKernelDiagonal_eq_trace x z (fun q => ‖z q‖)

/-- Positive-real targets—precisely critical-line reciprocal squares—contribute an ordinary
relative Hankel trace.  Nonreal Hermitian target mass is therefore the distinct obstruction. -/
theorem ofReal_sum_canonicalCapacity_positiveTargets_eq_relativeHankelTrace
    {N M n : ℕ} (x : Fin N → ℝ) (hx : ∀ r, 0 < x r)
    (hcard : n ≤ ((Finset.univ : Finset (Fin N)).image x).card)
    (t : Fin M → ℝ) (ht : ∀ q, 0 < t q) :
    ((∑ q : Fin M, weightedRedundantSamplingCapacity x
      (HTGeometry.canonicalMonomialReconstruction x n (t q : ℂ)) (t q : ℂ) : ℝ) : ℂ) =
      Matrix.trace
        (((HTGeometry.weightedMonomialGram x n)⁻¹.map (algebraMap ℝ ℂ)) *
          (HTGeometry.weightedMonomialGram t n).map (algebraMap ℝ ℂ)) := by
  rw [ofReal_sum_canonicalRedundantSamplingCapacity_eq_trace x hx hcard]
  rw [HTGeometry.complexTargetMonomialMomentMatrix_ofReal_pos t ht]

/-- Quantitative absorption of positive-real targets: their canonical capacity is controlled by
first reciprocal mass times finite inverse-Gram size. -/
theorem sum_canonicalCapacity_positiveTargets_le_inverseEntryL1_mul_mass
    {N M n : ℕ} (x : Fin N → ℝ) (hx : ∀ r, 0 < x r)
    (hcard : n ≤ ((Finset.univ : Finset (Fin N)).image x).card)
    (t : Fin M → ℝ) (ht : ∀ q, 0 < t q) (ht1 : ∀ q, t q ≤ 1) :
    (∑ q : Fin M, weightedRedundantSamplingCapacity x
      (HTGeometry.canonicalMonomialReconstruction x n (t q : ℂ)) (t q : ℂ)) ≤
      HTGeometry.weightedMonomialInverseEntryL1 x n * ∑ q : Fin M, t q := by
  have hid := ofReal_sum_canonicalCapacity_positiveTargets_eq_relativeHankelTrace
    x hx hcard t ht
  have hre := congrArg Complex.re hid
  have htraceMap :
      (Matrix.trace
        (((HTGeometry.weightedMonomialGram x n)⁻¹.map (algebraMap ℝ ℂ)) *
          (HTGeometry.weightedMonomialGram t n).map (algebraMap ℝ ℂ))).re =
        Matrix.trace ((HTGeometry.weightedMonomialGram x n)⁻¹ *
          HTGeometry.weightedMonomialGram t n) := by
    rw [← Matrix.map_mul]
    change (Matrix.trace (((HTGeometry.weightedMonomialGram x n)⁻¹ *
      HTGeometry.weightedMonomialGram t n).map Complex.ofRealHom)).re = _
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply]
    simp [Complex.ofRealHom]
  have heq : (∑ q : Fin M, weightedRedundantSamplingCapacity x
      (HTGeometry.canonicalMonomialReconstruction x n (t q : ℂ)) (t q : ℂ)) =
      Matrix.trace ((HTGeometry.weightedMonomialGram x n)⁻¹ *
        HTGeometry.weightedMonomialGram t n) := by
    rw [htraceMap] at hre
    simpa only [Complex.ofReal_re] using hre
  rw [heq]
  exact HTGeometry.trace_inv_mul_positiveWeightedMonomialGram_le_inverseEntryL1_mul_mass
    x t (fun q => (ht q).le) ht1

/-- Single positive-real target capacity is at most inverse-Gram entrywise size times target mass. -/
theorem canonicalCapacity_positiveTarget_le_inverseEntryL1_mul
    {N n : ℕ} (x : Fin N → ℝ) (hx : ∀ r, 0 < x r)
    (hcard : n ≤ ((Finset.univ : Finset (Fin N)).image x).card)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    weightedRedundantSamplingCapacity x
        (HTGeometry.canonicalMonomialReconstruction x n (t : ℂ)) (t : ℂ) ≤
      HTGeometry.weightedMonomialInverseEntryL1 x n * t := by
  have hunit : IsUnit (HTGeometry.weightedMonomialGram x n).det :=
    isUnit_iff_ne_zero.mpr
      (HTGeometry.weightedMonomialGram_posDef x hx hcard).det_pos.ne'
  simp only [weightedRedundantSamplingCapacity,
    HTGeometry.canonicalMonomialReconstruction_ofReal,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, abs_of_pos ht]
  rw [HTGeometry.canonicalMonomialReconstructionReal_energy_eq_kernel x hx hunit]
  rw [mul_comm]
  gcongr
  simp only [HTGeometry.weightedMonomialKernel,
    HTGeometry.weightedMonomialInverseEntryL1]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have hfactor0 : 0 ≤ t ^ (i : ℕ) * t ^ (j : ℕ) := by positivity
  have hfactor1 : t ^ (i : ℕ) * t ^ (j : ℕ) ≤ 1 := by
    have hi : t ^ (i : ℕ) ≤ 1 := pow_le_one₀ ht.le ht1
    have hj : t ^ (j : ℕ) ≤ 1 := pow_le_one₀ ht.le ht1
    exact mul_le_one₀ hi (pow_nonneg ht.le _) hj
  calc
    t ^ (i : ℕ) * (HTGeometry.weightedMonomialGram x n)⁻¹ i j * t ^ (j : ℕ) =
        (HTGeometry.weightedMonomialGram x n)⁻¹ i j *
          (t ^ (i : ℕ) * t ^ (j : ℕ)) := by ring
    _ ≤ |(HTGeometry.weightedMonomialGram x n)⁻¹ i j| *
          (t ^ (i : ℕ) * t ^ (j : ℕ)) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hfactor0
    _ ≤ |(HTGeometry.weightedMonomialGram x n)⁻¹ i j| :=
      mul_le_of_le_one_right (abs_nonneg _) hfactor1

/-- Absolute inverse-Gram power majorant for one positive-real target. -/
def canonicalPositiveTargetCapacityMajorant {N : ℕ}
    (x : Fin N → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    |(HTGeometry.weightedMonomialGram x n)⁻¹ i j| *
      t ^ ((i : ℕ) + (j : ℕ) + 1)

/-- Positive-real canonical capacity is bounded by a finite absolute inverse-Gram power sum, with
no upper restriction on the target. -/
theorem canonicalCapacity_positiveTarget_le_majorant
    {N n : ℕ} (x : Fin N → ℝ) (hx : ∀ r, 0 < x r)
    (hcard : n ≤ ((Finset.univ : Finset (Fin N)).image x).card)
    (t : ℝ) (ht : 0 < t) :
    weightedRedundantSamplingCapacity x
        (HTGeometry.canonicalMonomialReconstruction x n (t : ℂ)) (t : ℂ) ≤
      canonicalPositiveTargetCapacityMajorant x n t := by
  have hunit : IsUnit (HTGeometry.weightedMonomialGram x n).det :=
    isUnit_iff_ne_zero.mpr
      (HTGeometry.weightedMonomialGram_posDef x hx hcard).det_pos.ne'
  simp only [weightedRedundantSamplingCapacity,
    HTGeometry.canonicalMonomialReconstruction_ofReal,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, abs_of_pos ht]
  rw [HTGeometry.canonicalMonomialReconstructionReal_energy_eq_kernel x hx hunit]
  simp only [HTGeometry.weightedMonomialKernel,
    canonicalPositiveTargetCapacityMajorant]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  calc
    t * (t ^ (i : ℕ) * (HTGeometry.weightedMonomialGram x n)⁻¹ i j *
        t ^ (j : ℕ)) =
        (HTGeometry.weightedMonomialGram x n)⁻¹ i j *
          t ^ ((i : ℕ) + (j : ℕ) + 1) := by
      rw [pow_succ, pow_add]
      ring
    _ ≤ |(HTGeometry.weightedMonomialGram x n)⁻¹ i j| *
          t ^ ((i : ℕ) + (j : ℕ) + 1) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg ht.le _)

/-- Summable positive power tails make canonical positive-target capacity summable. -/
theorem canonicalCapacity_positiveTargets_summable_of_power_summable
    {N n : ℕ} {ι : Type*} (x : Fin N → ℝ) (hx : ∀ r, 0 < x r)
    (hcard : n ≤ ((Finset.univ : Finset (Fin N)).image x).card)
    (t : ι → ℝ) (ht : ∀ q, 0 < t q)
    (hpow : ∀ i j : Fin n,
      Summable (fun q : ι => t q ^ ((i : ℕ) + (j : ℕ) + 1))) :
    Summable (fun q : ι => weightedRedundantSamplingCapacity x
        (HTGeometry.canonicalMonomialReconstruction x n (t q : ℂ)) (t q : ℂ)) := by
  have hmajor : Summable (fun q : ι => canonicalPositiveTargetCapacityMajorant x n (t q)) := by
    simp only [canonicalPositiveTargetCapacityMajorant]
    apply summable_sum
    intro i _
    apply summable_sum
    intro j _
    exact (hpow i j).mul_left _
  exact Summable.of_nonneg_of_le
    (fun q => weightedRedundantSamplingCapacity_nonneg x hx _ _)
    (fun q => canonicalCapacity_positiveTarget_le_majorant x hx hcard (t q) (ht q))
    hmajor

/-- Any summable positive-real tail in `(0,1]` has summable canonical capacity, with an explicit
first-mass bound.  Critical-line tails are therefore absorbable for every fixed sampling frame. -/
theorem canonicalCapacity_positiveTargets_tsum_le_inverseEntryL1_mul_tsum
    {N n : ℕ} {ι : Type*} (x : Fin N → ℝ) (hx : ∀ r, 0 < x r)
    (hcard : n ≤ ((Finset.univ : Finset (Fin N)).image x).card)
    (t : ι → ℝ) (ht : ∀ q, 0 < t q) (ht1 : ∀ q, t q ≤ 1)
    (hsumm : Summable t) :
    Summable (fun q : ι => weightedRedundantSamplingCapacity x
        (HTGeometry.canonicalMonomialReconstruction x n (t q : ℂ)) (t q : ℂ)) ∧
      (∑' q : ι, weightedRedundantSamplingCapacity x
        (HTGeometry.canonicalMonomialReconstruction x n (t q : ℂ)) (t q : ℂ)) ≤
        HTGeometry.weightedMonomialInverseEntryL1 x n * ∑' q : ι, t q := by
  let f : ι → ℝ := fun q => weightedRedundantSamplingCapacity x
    (HTGeometry.canonicalMonomialReconstruction x n (t q : ℂ)) (t q : ℂ)
  let g : ι → ℝ := fun q => HTGeometry.weightedMonomialInverseEntryL1 x n * t q
  have hf0 : ∀ q, 0 ≤ f q := fun q =>
    weightedRedundantSamplingCapacity_nonneg x hx _ _
  have hfg : ∀ q, f q ≤ g q := fun q =>
    canonicalCapacity_positiveTarget_le_inverseEntryL1_mul x hx hcard (t q) (ht q) (ht1 q)
  have hg : Summable g := hsumm.mul_left _
  have hf : Summable f := Summable.of_nonneg_of_le hf0 hfg hg
  refine ⟨hf, ?_⟩
  calc
    ∑' q : ι, f q ≤ ∑' q : ι, g q := Summable.tsum_le_tsum hfg hf hg
    _ = HTGeometry.weightedMonomialInverseEntryL1 x n * ∑' q : ι, t q :=
      hsumm.tsum_mul_left _

/-- Uniform finite relative-trace control automatically supplies infinite canonical capacity
summability and the strict subunit bound. -/
theorem canonicalRedundantSamplingCapacity_summable_tsum_lt_one_of_uniform_finite_trace
    {N n : ℕ} {ι : Type*} (x : Fin N → ℝ) (hx : ∀ r, 0 < x r)
    (hcard : n ≤ ((Finset.univ : Finset (Fin N)).image x).card)
    (z : ι → ℂ) (C : ℝ) (hC : C < 1)
    (htrace : ∀ F : Finset ι,
      (Matrix.trace
        (((HTGeometry.weightedMonomialGram x n)⁻¹.map (algebraMap ℝ ℂ)) *
          HTGeometry.complexTargetMonomialMomentMatrix
            (fun q : ↥F => z (q : ι)) (fun q => ‖z (q : ι)‖) n)).re ≤ C) :
    Summable (fun q : ι => weightedRedundantSamplingCapacity x
        (HTGeometry.canonicalMonomialReconstruction x n (z q)) (z q)) ∧
      (∑' q : ι, weightedRedundantSamplingCapacity x
        (HTGeometry.canonicalMonomialReconstruction x n (z q)) (z q)) < 1 := by
  classical
  let f : ι → ℝ := fun q => weightedRedundantSamplingCapacity x
    (HTGeometry.canonicalMonomialReconstruction x n (z q)) (z q)
  have hf : ∀ q, 0 ≤ f q := fun q =>
    weightedRedundantSamplingCapacity_nonneg x hx _ _
  have hsum : ∀ F : Finset ι, ∑ q ∈ F, f q ≤ C := by
    intro F
    have hid := ofReal_sum_canonicalRedundantSamplingCapacity_eq_trace
      x hx hcard (fun q : ↥F => z (q : ι))
    have hre := congrArg Complex.re hid
    have hsub : (∑ q : ↥F, f (q : ι)) ≤ C := by
      calc
        ∑ q : ↥F, f (q : ι) =
            (Matrix.trace
              (((HTGeometry.weightedMonomialGram x n)⁻¹.map (algebraMap ℝ ℂ)) *
                HTGeometry.complexTargetMonomialMomentMatrix
                  (fun q : ↥F => z (q : ι)) (fun q => ‖z (q : ι)‖) n)).re := by
              simpa only [Complex.ofReal_re, f] using hre
        _ ≤ C := htrace F
    rw [Finset.sum_subtype F (fun _ => Iff.rfl) f]
    exact hsub
  have hsumm : Summable f := summable_of_sum_le hf hsum
  refine ⟨hsumm, ?_⟩
  exact (Real.tsum_le_of_sum_le hf hsum).trans_lt hC

/-- Monomial reproduction through degree `d` reconstructs every real polynomial of degree at most
`d` at the same complex target. -/
theorem evalRealPolynomial_eq_sum_of_reproduces_monomials
    {N d : ℕ} (x : Fin N → ℝ) (a : Fin N → ℂ) (z : ℂ)
    (hrepro : ∀ j ≤ d, ∑ i : Fin N, a i * (x i : ℂ) ^ j = z ^ j)
    (p : Polynomial ℝ) (hdegree : p.natDegree ≤ d) :
    evalRealPolynomial p z =
      ∑ i : Fin N, a i * ((Polynomial.eval (x i) p : ℝ) : ℂ) := by
  change (p.map Complex.ofRealHom).eval z = _
  rw [Polynomial.eval_eq_sum_range]
  calc
    ∑ j ∈ Finset.range (p.map Complex.ofRealHom).natDegree.succ,
        (p.map Complex.ofRealHom).coeff j * z ^ j =
        ∑ j ∈ Finset.range p.natDegree.succ,
          (p.coeff j : ℂ) * z ^ j := by
      rw [Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective]
      simp only [Polynomial.coeff_map, Complex.ofRealHom_eq_coe]
    _ = ∑ j ∈ Finset.range p.natDegree.succ,
          (p.coeff j : ℂ) * ∑ i : Fin N, a i * (x i : ℂ) ^ j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hrepro j ((Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hdegree)]
    _ = ∑ j ∈ Finset.range p.natDegree.succ, ∑ i : Fin N,
          (p.coeff j : ℂ) * (a i * (x i : ℂ) ^ j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = ∑ i : Fin N, ∑ j ∈ Finset.range p.natDegree.succ,
          (p.coeff j : ℂ) * (a i * (x i : ℂ) ^ j) := Finset.sum_comm
    _ = ∑ i : Fin N, a i * ((Polynomial.eval (x i) p : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Polynomial.eval_eq_sum_range]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Weighted Cauchy bound for any redundant reconstruction vector. -/
theorem norm_evalRealPolynomial_sq_le_redundantSampling_energy
    {N : ℕ} (x : Fin N → ℝ) (hx : ∀ i, 0 < x i)
    (a : Fin N → ℂ) (p : Polynomial ℝ) (z : ℂ)
    (hreconstruct : evalRealPolynomial p z =
      ∑ i : Fin N, a i * ((Polynomial.eval (x i) p : ℝ) : ℂ)) :
    ‖evalRealPolynomial p z‖ ^ 2 ≤
      (∑ i : Fin N, ‖a i‖ ^ 2 / x i) *
        ∑ i : Fin N, x i * Polynomial.eval (x i) p ^ 2 := by
  have htri : ‖evalRealPolynomial p z‖ ≤
      ∑ i : Fin N, ‖a i‖ * |Polynomial.eval (x i) p| := by
    rw [hreconstruct]
    calc
      ‖∑ i : Fin N, a i * ((Polynomial.eval (x i) p : ℝ) : ℂ)‖ ≤
          ∑ i : Fin N, ‖a i * ((Polynomial.eval (x i) p : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
  have hsumNonneg : 0 ≤ ∑ i : Fin N, ‖a i‖ * |Polynomial.eval (x i) p| := by
    positivity
  have hsq : ‖evalRealPolynomial p z‖ ^ 2 ≤
      (∑ i : Fin N, ‖a i‖ * |Polynomial.eval (x i) p|) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hsumNonneg).2 htri
  have hcauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset (Fin N))
    (r := fun i => ‖a i‖ * |Polynomial.eval (x i) p|)
    (f := fun i => ‖a i‖ ^ 2 / x i)
    (g := fun i => x i * Polynomial.eval (x i) p ^ 2)
    (fun i _ => div_nonneg (sq_nonneg _) (hx i).le)
    (fun i _ => mul_nonneg (hx i).le (sq_nonneg _))
    (fun i _ => by
      rw [mul_pow]
      simp only [sq_abs]
      field_simp [(hx i).ne']
      exact le_rfl)
  exact hsq.trans (by simpa only [mul_comm] using hcauchy)

theorem norm_weighted_evalRealPolynomial_sq_le_redundantCapacity_mul_energy
    {N d : ℕ} (x : Fin N → ℝ) (hx : ∀ i, 0 < x i)
    (a : Fin N → ℂ) (z : ℂ)
    (hrepro : ∀ j ≤ d, ∑ i : Fin N, a i * (x i : ℂ) ^ j = z ^ j)
    (p : Polynomial ℝ) (hdegree : p.natDegree ≤ d) :
    ‖z‖ * ‖evalRealPolynomial p z‖ ^ 2 ≤
      weightedRedundantSamplingCapacity x a z *
        ∑ i : Fin N, x i * Polynomial.eval (x i) p ^ 2 := by
  rw [weightedRedundantSamplingCapacity, mul_assoc]
  gcongr
  exact norm_evalRealPolynomial_sq_le_redundantSampling_energy x hx a p z
    (evalRealPolynomial_eq_sum_of_reproduces_monomials x a z hrepro p hdegree)

/-- Distinct-node count, not sample count, is the exact positivity condition for redundant energy. -/
theorem weighted_redundant_nodal_energy_pos
    {N : ℕ} (x : Fin N → ℝ) (hx : ∀ i, 0 < x i)
    (p : Polynomial ℝ) (hp : p ≠ 0)
    (hcard : p.natDegree < ((Finset.univ : Finset (Fin N)).image x).card) :
    0 < ∑ i : Fin N, x i * Polynomial.eval (x i) p ^ 2 := by
  have hnonneg : 0 ≤ ∑ i : Fin N, x i * Polynomial.eval (x i) p ^ 2 := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hx i).le (sq_nonneg _)
  refine lt_of_le_of_ne hnonneg ?_
  intro hzero
  have heach : ∀ i : Fin N, x i * Polynomial.eval (x i) p ^ 2 = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) =>
      mul_nonneg (hx j).le (sq_nonneg (Polynomial.eval (x j) p))).mp
        (by simpa only using hzero.symm) i (Finset.mem_univ i)
  let T : Finset ℝ := (Finset.univ : Finset (Fin N)).image x
  have heval : ∀ t : T, Polynomial.eval (t : ℝ) p = 0 := by
    intro t
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp t.property
    have hxi := heach i
    have hpi : Polynomial.eval (x i) p = 0 := by
      rcases mul_eq_zero.mp hxi with hxi | hsquare
      · exact False.elim ((hx i).ne' hxi)
      · exact sq_eq_zero_iff.mp hsquare
    simpa only [hi] using hpi
  have hpzero := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    p (f := fun t : T => (t : ℝ)) Subtype.val_injective heval
      (by simpa [T] using hcard)
  exact hp hpzero

/-- One adverse Xi atom is controlled by redundant positive-node energy. -/
theorem neg_xiShiftedHankelPairTerm_le_redundantCapacity
    {N d : ℕ} (x : Fin N → ℝ) (hx : ∀ i, 0 < x i)
    (a : Fin N → ℂ) (y : ℝ) (q : XiZeroCopy)
    (hrepro : ∀ j ≤ d, ∑ i : Fin N, a i * (x i : ℂ) ^ j =
      xiShiftedReciprocalSquare y q ^ j)
    (p : Polynomial ℝ) (hdegree : p.natDegree ≤ d) :
    -xiShiftedApertureHankelPairTerm y p p q ≤
      weightedRedundantSamplingCapacity x a (xiShiftedReciprocalSquare y q) *
        ∑ i : Fin N, x i * Polynomial.eval (x i) p ^ 2 := by
  let z := xiShiftedReciprocalSquare y q
  let w := evalRealPolynomial p z
  have hreal : -(z * w * w).re ≤ ‖z * w * w‖ := by
    have h := Complex.abs_re_le_norm (z * w * w)
    have hlower := (abs_le.mp h).1
    linarith
  have hnorm : ‖z * w * w‖ = ‖z‖ * ‖w‖ ^ 2 := by
    rw [norm_mul, norm_mul]
    ring
  rw [xiShiftedApertureHankelPairTerm]
  exact hreal.trans_eq hnorm |>.trans
    (norm_weighted_evalRealPolynomial_sq_le_redundantCapacity_mul_energy
      x hx a z hrepro p hdegree)

/-- **Redundant-frame Route-U criterion.**  A finite injective packet of positive Xi copies may
contain repeated reciprocal-square nodes (reflection and multiplicity).  If its distinct-node count
beats the polynomial degree and polynomial-independent dual vectors reconstruct every complementary
Xi atom with total capacity below one, then the full shifted Hankel square is strictly positive. -/
theorem full_xiShiftedHankelPair_tsum_pos_of_redundantSamplingCapacity_lt_one
    {N d : ℕ} {y : ℝ} (hy : 0 < y)
    (x : Fin N → ℝ) (qsample : Fin N → XiZeroCopy)
    (hx : ∀ i, 0 < x i) (hqinj : Function.Injective qsample)
    (hcoord : ∀ i, xiShiftedReciprocalSquare y (qsample i) = (x i : ℂ))
    (hcard : d < ((Finset.univ : Finset (Fin N)).image x).card)
    (p : Polynomial ℝ) (hp : p ≠ 0) (hdegree : p.natDegree ≤ d)
    (a : ↥((↑((Finset.univ : Finset (Fin N)).image qsample) :
        Set XiZeroCopy)ᶜ) → Fin N → ℂ)
    (hrepro : ∀ q j, j ≤ d →
      ∑ i : Fin N, a q i * (x i : ℂ) ^ j =
        xiShiftedReciprocalSquare y (q : XiZeroCopy) ^ j)
    (hcapSummable : Summable (fun q => weightedRedundantSamplingCapacity x (a q)
      (xiShiftedReciprocalSquare y (q : XiZeroCopy))))
    (hcap : (∑' q, weightedRedundantSamplingCapacity x (a q)
      (xiShiftedReciprocalSquare y (q : XiZeroCopy))) < 1) :
    0 < ∑' q : XiZeroCopy, xiShiftedApertureHankelPairTerm y p p q := by
  classical
  let S : Finset XiZeroCopy := (Finset.univ : Finset (Fin N)).image qsample
  let E := ∑ i : Fin N, x i * Polynomial.eval (x i) p ^ 2
  have hE : 0 < E := by
    exact weighted_redundant_nodal_energy_pos x hx p hp (hdegree.trans_lt hcard)
  have hprefix :
      (∑ q ∈ S, xiShiftedApertureHankelPairTerm y p p q) = E := by
    dsimp only [S, E]
    rw [Finset.sum_image (fun i _ j _ hij => hqinj hij),
      sum_xiShiftedHankelPairTerm_eq_weighted_nodal_energy x qsample p y hcoord]
  have hterm : Summable (xiShiftedApertureHankelPairTerm y p p) := by
    have h := (summable_xiShiftedApertureHilbertPairTerm hy p p).sub
      (summable_xiShiftedApertureTransversePairTerm hy p p)
    exact h.congr fun q =>
      (xiShiftedApertureHankelPairTerm_eq_hilbert_sub_transverse hy p p q).symm
  have htermCompl : Summable (fun q : ↥((↑S : Set XiZeroCopy)ᶜ) =>
      xiShiftedApertureHankelPairTerm y p p (q : XiZeroCopy)) :=
    hterm.subtype _
  have htailBound :
      -(∑' q : ↥((↑S : Set XiZeroCopy)ᶜ),
          xiShiftedApertureHankelPairTerm y p p (q : XiZeroCopy)) ≤
        (∑' q : ↥((↑S : Set XiZeroCopy)ᶜ),
          weightedRedundantSamplingCapacity x (a q)
            (xiShiftedReciprocalSquare y (q : XiZeroCopy))) * E := by
    rw [← tsum_neg, ← tsum_mul_right]
    exact Summable.tsum_le_tsum
      (fun q => neg_xiShiftedHankelPairTerm_le_redundantCapacity
        x hx (a q) y (q : XiZeroCopy) (hrepro q) p hdegree)
      htermCompl.neg (hcapSummable.mul_right E)
  have hsplit := hterm.sum_add_tsum_compl (s := S)
  rw [hprefix] at hsplit
  change (∑' q : ↥((↑S : Set XiZeroCopy)ᶜ),
      weightedRedundantSamplingCapacity x (a q)
        (xiShiftedReciprocalSquare y (q : XiZeroCopy))) < 1 at hcap
  nlinarith

/-- **Canonical redundant-frame Route-U criterion.** Enough distinct positive sample nodes make the
weighted monomial Gram matrix strict, so its inverse constructs all dual vectors automatically.
Only summability and a subunit total canonical capacity of complementary Xi atoms remain. -/
theorem full_xiShiftedHankelPair_tsum_pos_of_canonicalRedundantSamplingCapacity_lt_one
    {N d : ℕ} {y : ℝ} (hy : 0 < y)
    (x : Fin N → ℝ) (qsample : Fin N → XiZeroCopy)
    (hx : ∀ i, 0 < x i) (hqinj : Function.Injective qsample)
    (hcoord : ∀ i, xiShiftedReciprocalSquare y (qsample i) = (x i : ℂ))
    (hcard : d < ((Finset.univ : Finset (Fin N)).image x).card)
    (p : Polynomial ℝ) (hp : p ≠ 0) (hdegree : p.natDegree ≤ d)
    (hcapSummable : Summable (fun q : ↥((↑((Finset.univ : Finset (Fin N)).image
        qsample) : Set XiZeroCopy)ᶜ) =>
      weightedRedundantSamplingCapacity x
        (HTGeometry.canonicalMonomialReconstruction x (d + 1)
          (xiShiftedReciprocalSquare y (q : XiZeroCopy)))
        (xiShiftedReciprocalSquare y (q : XiZeroCopy))))
    (hcap : (∑' q : ↥((↑((Finset.univ : Finset (Fin N)).image qsample) :
        Set XiZeroCopy)ᶜ),
      weightedRedundantSamplingCapacity x
        (HTGeometry.canonicalMonomialReconstruction x (d + 1)
          (xiShiftedReciprocalSquare y (q : XiZeroCopy)))
        (xiShiftedReciprocalSquare y (q : XiZeroCopy))) < 1) :
    0 < ∑' q : XiZeroCopy, xiShiftedApertureHankelPairTerm y p p q := by
  have hgram : (HTGeometry.weightedMonomialGram x (d + 1)).PosDef :=
    HTGeometry.weightedMonomialGram_posDef x hx (Nat.succ_le_iff.mpr hcard)
  have hunit : IsUnit (HTGeometry.weightedMonomialGram x (d + 1)).det :=
    isUnit_iff_ne_zero.mpr hgram.det_pos.ne'
  apply full_xiShiftedHankelPair_tsum_pos_of_redundantSamplingCapacity_lt_one
    hy x qsample hx hqinj hcoord hcard p hp hdegree
    (a := fun q => HTGeometry.canonicalMonomialReconstruction x (d + 1)
      (xiShiftedReciprocalSquare y (q : XiZeroCopy)))
  · intro q j hj
    let k : Fin (d + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    simpa only [k] using
      HTGeometry.canonicalMonomialReconstruction_reproduces_monomial x hunit
        (xiShiftedReciprocalSquare y (q : XiZeroCopy)) k
  · exact hcapSummable
  · exact hcap

/-- **Canonical base frame with a positive absorber.** Reconstruction uses one fixed canonical
frame, while any larger finite positive Xi packet is absorbed into prefix energy.  This decouples
critical-line tail removal from inverse-Gram conditioning. -/
theorem full_xiShiftedHankelPair_tsum_pos_of_canonicalBaseFrame_positiveAbsorber
    {N d : ℕ} {y : ℝ} (hy : 0 < y)
    (x : Fin N → ℝ) (qbase : Fin N → XiZeroCopy)
    (hx : ∀ i, 0 < x i) (hqinj : Function.Injective qbase)
    (hcoord : ∀ i, xiShiftedReciprocalSquare y (qbase i) = (x i : ℂ))
    (hcard : d < ((Finset.univ : Finset (Fin N)).image x).card)
    (S : Finset XiZeroCopy)
    (hinclude : ∀ i, qbase i ∈ S)
    (hpositive : ∀ q ∈ S, ∃ t : ℝ, 0 < t ∧
      xiShiftedReciprocalSquare y q = (t : ℂ))
    (p : Polynomial ℝ) (hp : p ≠ 0) (hdegree : p.natDegree ≤ d)
    (hcapSummable : Summable (fun q : ↥((↑S : Set XiZeroCopy)ᶜ) =>
      weightedRedundantSamplingCapacity x
        (HTGeometry.canonicalMonomialReconstruction x (d + 1)
          (xiShiftedReciprocalSquare y (q : XiZeroCopy)))
        (xiShiftedReciprocalSquare y (q : XiZeroCopy))))
    (hcap : (∑' q : ↥((↑S : Set XiZeroCopy)ᶜ),
      weightedRedundantSamplingCapacity x
        (HTGeometry.canonicalMonomialReconstruction x (d + 1)
          (xiShiftedReciprocalSquare y (q : XiZeroCopy)))
        (xiShiftedReciprocalSquare y (q : XiZeroCopy))) < 1) :
    0 < ∑' q : XiZeroCopy, xiShiftedApertureHankelPairTerm y p p q := by
  classical
  let B : Finset XiZeroCopy := (Finset.univ : Finset (Fin N)).image qbase
  let E := ∑ i : Fin N, x i * Polynomial.eval (x i) p ^ 2
  have hE : 0 < E :=
    weighted_redundant_nodal_energy_pos x hx p hp (hdegree.trans_lt hcard)
  have hbase : (∑ q ∈ B, xiShiftedApertureHankelPairTerm y p p q) = E := by
    dsimp only [B, E]
    rw [Finset.sum_image (fun i _ j _ hij => hqinj hij),
      sum_xiShiftedHankelPairTerm_eq_weighted_nodal_energy x qbase p y hcoord]
  have hBS : B ⊆ S := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact hinclude i
  have hprefix : E ≤ ∑ q ∈ S, xiShiftedApertureHankelPairTerm y p p q := by
    rw [← hbase]
    apply Finset.sum_le_sum_of_subset_of_nonneg hBS
    intro q hqS _
    obtain ⟨t, ht, hq⟩ := hpositive q hqS
    rw [xiShiftedApertureHankelPairTerm, hq]
    simp only [evalRealPolynomial_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    nlinarith [sq_nonneg (Polynomial.eval t p)]
  have hgram : (HTGeometry.weightedMonomialGram x (d + 1)).PosDef :=
    HTGeometry.weightedMonomialGram_posDef x hx (Nat.succ_le_iff.mpr hcard)
  have hunit : IsUnit (HTGeometry.weightedMonomialGram x (d + 1)).det :=
    isUnit_iff_ne_zero.mpr hgram.det_pos.ne'
  have hrepro : ∀ (q : ↥((↑S : Set XiZeroCopy)ᶜ)) j, j ≤ d →
      ∑ i : Fin N, HTGeometry.canonicalMonomialReconstruction x (d + 1)
          (xiShiftedReciprocalSquare y (q : XiZeroCopy)) i * (x i : ℂ) ^ j =
        xiShiftedReciprocalSquare y (q : XiZeroCopy) ^ j := by
    intro q j hj
    let k : Fin (d + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    simpa only [k] using
      HTGeometry.canonicalMonomialReconstruction_reproduces_monomial x hunit
        (xiShiftedReciprocalSquare y (q : XiZeroCopy)) k
  have hterm : Summable (xiShiftedApertureHankelPairTerm y p p) := by
    have h := (summable_xiShiftedApertureHilbertPairTerm hy p p).sub
      (summable_xiShiftedApertureTransversePairTerm hy p p)
    exact h.congr fun q =>
      (xiShiftedApertureHankelPairTerm_eq_hilbert_sub_transverse hy p p q).symm
  have htermCompl : Summable (fun q : ↥((↑S : Set XiZeroCopy)ᶜ) =>
      xiShiftedApertureHankelPairTerm y p p (q : XiZeroCopy)) := hterm.subtype _
  have htailBound :
      -(∑' q : ↥((↑S : Set XiZeroCopy)ᶜ),
          xiShiftedApertureHankelPairTerm y p p (q : XiZeroCopy)) ≤
        (∑' q : ↥((↑S : Set XiZeroCopy)ᶜ),
          weightedRedundantSamplingCapacity x
            (HTGeometry.canonicalMonomialReconstruction x (d + 1)
              (xiShiftedReciprocalSquare y (q : XiZeroCopy)))
            (xiShiftedReciprocalSquare y (q : XiZeroCopy))) * E := by
    rw [← tsum_neg, ← tsum_mul_right]
    exact Summable.tsum_le_tsum
      (fun q => neg_xiShiftedHankelPairTerm_le_redundantCapacity
        x hx _ y (q : XiZeroCopy) (hrepro q) p hdegree)
      htermCompl.neg (hcapSummable.mul_right E)
  have hsplit := hterm.sum_add_tsum_compl (s := S)
  nlinarith

/-- Uniform inverse-Gram trace bound for every finite packet outside a selected Xi sample. -/
def XiCanonicalComplementTraceBound {N : ℕ}
    (x : Fin N → ℝ) (qsample : Fin N → XiZeroCopy) (y : ℝ) (n : ℕ) (C : ℝ) : Prop :=
  ∀ F : Finset ↥((↑((Finset.univ : Finset (Fin N)).image qsample) : Set XiZeroCopy)ᶜ),
    (Matrix.trace
      (((HTGeometry.weightedMonomialGram x n)⁻¹.map (algebraMap ℝ ℂ)) *
        HTGeometry.complexTargetMonomialMomentMatrix
          (fun q : ↥F => xiShiftedReciprocalSquare y ((q : ↥((↑((Finset.univ :
            Finset (Fin N)).image qsample) : Set XiZeroCopy)ᶜ)) : XiZeroCopy))
          (fun q => ‖xiShiftedReciprocalSquare y ((q : ↥((↑((Finset.univ :
            Finset (Fin N)).image qsample) : Set XiZeroCopy)ᶜ)) : XiZeroCopy)‖) n)).re ≤ C

/-- **Finite-trace Route-U criterion.** A uniform subunit inverse-Gram trace bound over every
finite complementary Xi packet automatically closes summability and proves strict full positivity.
This is the matrix form of the canonical capacity condition. -/
theorem full_xiShiftedHankelPair_tsum_pos_of_uniformFiniteCanonicalCapacityTrace_lt_one
    {N d : ℕ} {y : ℝ} (hy : 0 < y)
    (x : Fin N → ℝ) (qsample : Fin N → XiZeroCopy)
    (hx : ∀ i, 0 < x i) (hqinj : Function.Injective qsample)
    (hcoord : ∀ i, xiShiftedReciprocalSquare y (qsample i) = (x i : ℂ))
    (hcard : d < ((Finset.univ : Finset (Fin N)).image x).card)
    (p : Polynomial ℝ) (hp : p ≠ 0) (hdegree : p.natDegree ≤ d)
    (C : ℝ) (hC : C < 1)
    (htrace : XiCanonicalComplementTraceBound x qsample y (d + 1) C) :
    0 < ∑' q : XiZeroCopy, xiShiftedApertureHankelPairTerm y p p q := by
  let z : ↥((↑((Finset.univ : Finset (Fin N)).image qsample) :
      Set XiZeroCopy)ᶜ) → ℂ :=
    fun q => xiShiftedReciprocalSquare y (q : XiZeroCopy)
  obtain ⟨hcapSummable, hcap⟩ :=
    canonicalRedundantSamplingCapacity_summable_tsum_lt_one_of_uniform_finite_trace
      x hx (Nat.succ_le_iff.mpr hcard) z C hC (by
        simpa only [XiCanonicalComplementTraceBound, z] using htrace)
  exact full_xiShiftedHankelPair_tsum_pos_of_canonicalRedundantSamplingCapacity_lt_one
    hy x qsample hx hqinj hcoord hcard p hp hdegree hcapSummable hcap

end

end RHTower
