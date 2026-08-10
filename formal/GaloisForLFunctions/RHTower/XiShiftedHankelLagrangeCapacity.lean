import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryHilbertChargeFlow
import GaloisForLFunctions.HTGeometry.PolynomialGrowthBound
import Mathlib.LinearAlgebra.Lagrange

open Matrix Polynomial

namespace RHTower

noncomputable section

open scoped BigOperators

/-- Sharp weighted Lagrange evaluation capacity at a complex point. -/
def weightedLagrangeEvaluationCapacity {k : ℕ}
    (x : Fin k → ℝ) (z : ℂ) : ℝ :=
  ‖z‖ * ∑ i : Fin k,
    ‖(Lagrange.basis Finset.univ (fun j => (x j : ℂ)) i).eval z‖ ^ 2 / x i

/-- Uniform disk bound for weighted Lagrange capacity. -/
def weightedLagrangeEvaluationCapacityBound {k : ℕ} (x : Fin k → ℝ) : ℝ :=
  ∑ i : Fin k,
    (GaloisForLFunctions.HTGeometry.coeffNormSum
      (Lagrange.basis Finset.univ (fun j => (x j : ℂ)) i) *
        2 ^ (Lagrange.basis Finset.univ (fun j => (x j : ℂ)) i).natDegree) ^ 2 / x i

theorem weightedLagrangeEvaluationCapacity_nonneg
    {k : ℕ} (x : Fin k → ℝ) (hx : ∀ i, 0 < x i) (z : ℂ) :
    0 ≤ weightedLagrangeEvaluationCapacity x z := by
  apply mul_nonneg (norm_nonneg _)
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (sq_nonneg _) (hx i).le

theorem weightedLagrangeEvaluationCapacity_le_norm_mul_bound
    {k : ℕ} (x : Fin k → ℝ) (hx : ∀ i, 0 < x i) (z : ℂ)
    (hz : ‖z‖ ≤ 1) :
    weightedLagrangeEvaluationCapacity x z ≤
      ‖z‖ * weightedLagrangeEvaluationCapacityBound x := by
  unfold weightedLagrangeEvaluationCapacity weightedLagrangeEvaluationCapacityBound
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  apply div_le_div_of_nonneg_right _ (hx i).le
  let L := Lagrange.basis Finset.univ (fun j => (x j : ℂ)) i
  have hbase : 1 + ‖z‖ ≤ 2 := by linarith
  have hpow : (1 + ‖z‖) ^ L.natDegree ≤ 2 ^ L.natDegree := by
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hcoeff : 0 ≤ GaloisForLFunctions.HTGeometry.coeffNormSum L :=
    GaloisForLFunctions.HTGeometry.coeffNormSum_nonneg L
  have heval : ‖L.eval z‖ ≤
      GaloisForLFunctions.HTGeometry.coeffNormSum L * 2 ^ L.natDegree := by
    exact (GaloisForLFunctions.HTGeometry.norm_eval_le_coeffNormSum L z).trans
      (mul_le_mul_of_nonneg_left hpow hcoeff)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hcoeff (by positivity))).2 heval

/-- Capacity is exactly one at every selected interpolation node. -/
theorem weightedLagrangeEvaluationCapacity_at_node
    {k : ℕ} (x : Fin k → ℝ) (hx : ∀ i, 0 < x i)
    (hinj : Function.Injective x) (i : Fin k) :
    weightedLagrangeEvaluationCapacity x (x i : ℂ) = 1 := by
  classical
  let xc : Fin k → ℂ := fun j => (x j : ℂ)
  have hcinj : Function.Injective xc := Complex.ofReal_injective.comp hinj
  unfold weightedLagrangeEvaluationCapacity
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hx i)]
  have hsum : (∑ j : Fin k,
      ‖(Lagrange.basis Finset.univ xc j).eval (x i : ℂ)‖ ^ 2 / x j) =
      1 / x i := by
    rw [Finset.sum_eq_single i]
    · rw [Lagrange.eval_basis_self hcinj.injOn (Finset.mem_univ i)]
      norm_num
    · intro j _ hji
      change ‖(Lagrange.basis Finset.univ xc j).eval (xc i)‖ ^ 2 / x j = 0
      rw [Lagrange.eval_basis_of_ne hji (Finset.mem_univ i)]
      norm_num
    · simp
  change x i * (∑ j : Fin k,
      ‖(Lagrange.basis Finset.univ xc j).eval (x i : ℂ)‖ ^ 2 / x j) = 1
  rw [hsum, mul_div_cancel₀ _ (hx i).ne']

/-- Total shifted-Xi Lagrange capacity is automatically summable. -/
theorem summable_weightedLagrangeEvaluationCapacity_xiShifted
    {k : ℕ} {y : ℝ} (hy : 0 ≤ y) (x : Fin k → ℝ) (hx : ∀ i, 0 < x i) :
    Summable (fun q : XiZeroCopy =>
      weightedLagrangeEvaluationCapacity x (xiShiftedReciprocalSquare y q)) := by
  have hnorm : Summable (fun q : XiZeroCopy => ‖xiShiftedReciprocalSquare y q‖) := by
    simpa only [zero_add, pow_one] using
      (summable_xiShiftedReciprocalSquare_pow hy 0).norm
  have hbound := hnorm.mul_right (weightedLagrangeEvaluationCapacityBound x)
  apply Summable.of_nonneg_of_le
    (fun q => weightedLagrangeEvaluationCapacity_nonneg x hx _)
    (fun q => weightedLagrangeEvaluationCapacity_le_norm_mul_bound x hx _ ?_)
    hbound
  exact (norm_xiShiftedReciprocalSquare_le hy q).trans
    ((norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne q).le.trans (by norm_num))

theorem norm_evalRealPolynomial_sq_le_weightedLagrange_energy
    {k : ℕ} (x : Fin k → ℝ) (hx : ∀ i, 0 < x i)
    (hinj : Function.Injective x) (p : Polynomial ℝ) (hp : p ≠ 0)
    (hdegree : p.natDegree < k) (z : ℂ) :
    ‖evalRealPolynomial p z‖ ^ 2 ≤
      (∑ i : Fin k,
          ‖(Lagrange.basis Finset.univ (fun j => (x j : ℂ)) i).eval z‖ ^ 2 / x i) *
        ∑ i : Fin k, x i * Polynomial.eval (x i) p ^ 2 := by
  classical
  let pc : Polynomial ℂ := p.map Complex.ofRealHom
  let xc : Fin k → ℂ := fun i => (x i : ℂ)
  have hcinj : Function.Injective xc := Complex.ofReal_injective.comp hinj
  have hpcdeg : pc.degree < (((Finset.univ : Finset (Fin k)).card : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_map_eq_of_injective Complex.ofReal_injective]
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Polynomial.natDegree_lt_iff_degree_lt hp).mp hdegree
  have hpoly := Lagrange.eq_interpolate (s := Finset.univ) (v := xc)
    hcinj.injOn hpcdeg
  have hrepr : evalRealPolynomial p z =
      ∑ i : Fin k, ((Polynomial.eval (x i) p : ℝ) : ℂ) *
        (Lagrange.basis Finset.univ xc i).eval z := by
    change pc.eval z = _
    rw [hpoly, Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    change evalRealPolynomial p (x i : ℂ) = ((Polynomial.eval (x i) p : ℝ) : ℂ)
    exact evalRealPolynomial_ofReal p (x i)
  have htri : ‖evalRealPolynomial p z‖ ≤
      ∑ i : Fin k, |Polynomial.eval (x i) p| *
        ‖(Lagrange.basis Finset.univ xc i).eval z‖ := by
    rw [hrepr]
    calc
      ‖∑ i : Fin k, ((Polynomial.eval (x i) p : ℝ) : ℂ) *
          (Lagrange.basis Finset.univ xc i).eval z‖
          ≤ ∑ i : Fin k, ‖((Polynomial.eval (x i) p : ℝ) : ℂ) *
            (Lagrange.basis Finset.univ xc i).eval z‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hsum_nonneg : 0 ≤ ∑ i : Fin k, |Polynomial.eval (x i) p| *
      ‖(Lagrange.basis Finset.univ xc i).eval z‖ := by positivity
  have hsq : ‖evalRealPolynomial p z‖ ^ 2 ≤
      (∑ i : Fin k, |Polynomial.eval (x i) p| *
        ‖(Lagrange.basis Finset.univ xc i).eval z‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hsum_nonneg).2 htri
  have hcauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset (Fin k))
    (r := fun i => |Polynomial.eval (x i) p| *
      ‖(Lagrange.basis Finset.univ xc i).eval z‖)
    (f := fun i => ‖(Lagrange.basis Finset.univ xc i).eval z‖ ^ 2 / x i)
    (g := fun i => x i * Polynomial.eval (x i) p ^ 2)
    (fun i _ => div_nonneg (sq_nonneg _) (hx i).le)
    (fun i _ => mul_nonneg (hx i).le (sq_nonneg _))
    (fun i _ => by
      rw [mul_pow]
      simp only [sq_abs]
      field_simp [(hx i).ne']
      exact le_rfl)
  exact hsq.trans (by simpa only using hcauchy)

theorem norm_weighted_evalRealPolynomial_sq_le_capacity_mul_energy
    {k : ℕ} (x : Fin k → ℝ) (hx : ∀ i, 0 < x i)
    (hinj : Function.Injective x) (p : Polynomial ℝ) (hp : p ≠ 0)
    (hdegree : p.natDegree < k) (z : ℂ) :
    ‖z‖ * ‖evalRealPolynomial p z‖ ^ 2 ≤
      weightedLagrangeEvaluationCapacity x z *
        ∑ i : Fin k, x i * Polynomial.eval (x i) p ^ 2 := by
  rw [weightedLagrangeEvaluationCapacity, mul_assoc]
  gcongr
  exact norm_evalRealPolynomial_sq_le_weightedLagrange_energy
    x hx hinj p hp hdegree z

/-- Every adverse shifted-Xi atom is dominated by critical sampling energy times scalar capacity. -/
theorem neg_xiShiftedHankelPairTerm_le_weightedLagrange_capacity
    {k : ℕ} (x : Fin k → ℝ) (hx : ∀ i, 0 < x i)
    (hinj : Function.Injective x) (p : Polynomial ℝ) (hp : p ≠ 0)
    (hdegree : p.natDegree < k) (y : ℝ) (q : XiZeroCopy) :
    -xiShiftedApertureHankelPairTerm y p p q ≤
      weightedLagrangeEvaluationCapacity x (xiShiftedReciprocalSquare y q) *
        ∑ i : Fin k, x i * Polynomial.eval (x i) p ^ 2 := by
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
    (norm_weighted_evalRealPolynomial_sq_le_capacity_mul_energy
      x hx hinj p hp hdegree z)

/-- Critical-line sample energy is exactly the weighted real nodal energy. -/
theorem sum_xiShiftedHankelPairTerm_eq_weighted_nodal_energy
    {k : ℕ} (x : Fin k → ℝ) (qcrit : Fin k → XiZeroCopy) (p : Polynomial ℝ)
    (y : ℝ) (hcoord : ∀ i, xiShiftedReciprocalSquare y (qcrit i) = (x i : ℂ)) :
    (∑ i : Fin k, xiShiftedApertureHankelPairTerm y p p (qcrit i)) =
      ∑ i : Fin k, x i * Polynomial.eval (x i) p ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  rw [xiShiftedApertureHankelPairTerm, hcoord i]
  simp only [evalRealPolynomial_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- Route-U pointwise capacity law relative to a chosen critical-line sampling family. -/
theorem neg_xiShiftedHankelPairTerm_le_capacity_mul_criticalPrefix
    {k : ℕ} (x : Fin k → ℝ) (qcrit : Fin k → XiZeroCopy)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x)
    (p : Polynomial ℝ) (hp : p ≠ 0) (hdegree : p.natDegree < k)
    (y : ℝ) (hcoord : ∀ i, xiShiftedReciprocalSquare y (qcrit i) = (x i : ℂ))
    (q : XiZeroCopy) :
    -xiShiftedApertureHankelPairTerm y p p q ≤
      weightedLagrangeEvaluationCapacity x (xiShiftedReciprocalSquare y q) *
        ∑ i : Fin k, xiShiftedApertureHankelPairTerm y p p (qcrit i) := by
  rw [sum_xiShiftedHankelPairTerm_eq_weighted_nodal_energy x qcrit p y hcoord]
  exact neg_xiShiftedHankelPairTerm_le_weightedLagrange_capacity
    x hx hinj p hp hdegree y q

/-- Weighted energy on enough distinct positive nodes is strictly positive for every nonzero
polynomial below the sampling cardinality. -/
theorem weighted_nodal_energy_pos
    {k : ℕ} (x : Fin k → ℝ) (hx : ∀ i, 0 < x i)
    (hinj : Function.Injective x) (p : Polynomial ℝ) (hp : p ≠ 0)
    (hdegree : p.natDegree < k) :
    0 < ∑ i : Fin k, x i * Polynomial.eval (x i) p ^ 2 := by
  have hnonneg : 0 ≤ ∑ i : Fin k, x i * Polynomial.eval (x i) p ^ 2 := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hx i).le (sq_nonneg _)
  refine lt_of_le_of_ne hnonneg ?_
  intro hzero
  have heach : ∀ i : Fin k, x i * Polynomial.eval (x i) p ^ 2 = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) =>
      mul_nonneg (hx j).le (sq_nonneg (Polynomial.eval (x j) p))).mp
        (by simpa only using hzero.symm)
      i (Finset.mem_univ i)
  have heval : ∀ i : Fin k, Polynomial.eval (x i) p = 0 := by
    intro i
    have hi := heach i
    rcases mul_eq_zero.mp hi with hxi | hpi
    · exact False.elim ((hx i).ne' hxi)
    · exact sq_eq_zero_iff.mp hpi
  have hpzero := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    p (f := x) hinj heval (by simpa only [Fintype.card_fin] using hdegree)
  exact hp hpzero

/-- Finite adverse mass is bounded by total scalar capacity times critical-prefix energy. -/
theorem neg_finite_xiShiftedTail_le_capacity_mul_criticalPrefix
    {k : ℕ} (x : Fin k → ℝ) (qcrit : Fin k → XiZeroCopy)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x)
    (p : Polynomial ℝ) (hp : p ≠ 0) (hdegree : p.natDegree < k)
    (y : ℝ) (hcoord : ∀ i, xiShiftedReciprocalSquare y (qcrit i) = (x i : ℂ))
    (T : Finset XiZeroCopy) :
    -(∑ q ∈ T, xiShiftedApertureHankelPairTerm y p p q) ≤
      (∑ q ∈ T, weightedLagrangeEvaluationCapacity x
          (xiShiftedReciprocalSquare y q)) *
        ∑ i : Fin k, xiShiftedApertureHankelPairTerm y p p (qcrit i) := by
  let E := ∑ i : Fin k, xiShiftedApertureHankelPairTerm y p p (qcrit i)
  calc
    -(∑ q ∈ T, xiShiftedApertureHankelPairTerm y p p q) =
        ∑ q ∈ T, -xiShiftedApertureHankelPairTerm y p p q := by
      simp only [Finset.sum_neg_distrib]
    _ ≤ ∑ q ∈ T, weightedLagrangeEvaluationCapacity x
          (xiShiftedReciprocalSquare y q) * E := by
      apply Finset.sum_le_sum
      intro q hq
      exact neg_xiShiftedHankelPairTerm_le_capacity_mul_criticalPrefix
        x qcrit hx hinj p hp hdegree y hcoord q
    _ = (∑ q ∈ T, weightedLagrangeEvaluationCapacity x
          (xiShiftedReciprocalSquare y q)) * E := by
      rw [Finset.sum_mul]

/-- Scalar capacity below one forbids exact cancellation of critical sampling energy by any
finite adverse tail, uniformly over every polynomial below sampling degree. -/
theorem finite_tail_capacity_lt_one_excludes_null
    {k : ℕ} (x : Fin k → ℝ) (qcrit : Fin k → XiZeroCopy)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x)
    (p : Polynomial ℝ) (hp : p ≠ 0) (hdegree : p.natDegree < k)
    (y : ℝ) (hcoord : ∀ i, xiShiftedReciprocalSquare y (qcrit i) = (x i : ℂ))
    (T : Finset XiZeroCopy)
    (hcap : (∑ q ∈ T, weightedLagrangeEvaluationCapacity x
      (xiShiftedReciprocalSquare y q)) < 1)
    (hnull : (∑ i : Fin k, xiShiftedApertureHankelPairTerm y p p (qcrit i)) +
      ∑ q ∈ T, xiShiftedApertureHankelPairTerm y p p q = 0) : False := by
  have hE : 0 < ∑ i : Fin k,
      xiShiftedApertureHankelPairTerm y p p (qcrit i) := by
    rw [sum_xiShiftedHankelPairTerm_eq_weighted_nodal_energy x qcrit p y hcoord]
    exact weighted_nodal_energy_pos x hx hinj p hp hdegree
  have hbound := neg_finite_xiShiftedTail_le_capacity_mul_criticalPrefix
    x qcrit hx hinj p hp hdegree y hcoord T
  nlinarith

/-- **Infinite Route-U capacity criterion.**  If scalar Lagrange capacity of every Xi copy outside
the selected positive sampling family totals less than one, then the complete shifted Hankel square
is strictly positive for every nonzero polynomial below sampling degree.  Capacity summability is
automatic from reciprocal-square summability. -/
theorem full_xiShiftedHankelPair_tsum_pos_of_compl_capacity_lt_one
    {k : ℕ} {y : ℝ} (hy : 0 < y)
    (x : Fin k → ℝ) (qcrit : Fin k → XiZeroCopy)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x)
    (p : Polynomial ℝ) (hp : p ≠ 0) (hdegree : p.natDegree < k)
    (hcoord : ∀ i, xiShiftedReciprocalSquare y (qcrit i) = (x i : ℂ))
    (hcap : (∑' q : ↥((↑((Finset.univ : Finset (Fin k)).image qcrit) :
        Set XiZeroCopy)ᶜ),
      weightedLagrangeEvaluationCapacity x
        (xiShiftedReciprocalSquare y (q : XiZeroCopy))) < 1) :
    0 < ∑' q : XiZeroCopy, xiShiftedApertureHankelPairTerm y p p q := by
  classical
  let S : Finset XiZeroCopy := (Finset.univ : Finset (Fin k)).image qcrit
  let E := ∑ i : Fin k, xiShiftedApertureHankelPairTerm y p p (qcrit i)
  have hqinj : Function.Injective qcrit := by
    intro i j hij
    apply hinj
    apply Complex.ofReal_injective
    rw [← hcoord i, ← hcoord j, hij]
  have hE : 0 < E := by
    dsimp only [E]
    rw [sum_xiShiftedHankelPairTerm_eq_weighted_nodal_energy x qcrit p y hcoord]
    exact weighted_nodal_energy_pos x hx hinj p hp hdegree
  have hprefix :
      (∑ q ∈ S, xiShiftedApertureHankelPairTerm y p p q) = E := by
    dsimp only [S, E]
    rw [Finset.sum_image (fun i _ j _ hij => hqinj hij)]
  have hterm : Summable (xiShiftedApertureHankelPairTerm y p p) := by
    have h := (summable_xiShiftedApertureHilbertPairTerm hy p p).sub
      (summable_xiShiftedApertureTransversePairTerm hy p p)
    exact h.congr fun q =>
      (xiShiftedApertureHankelPairTerm_eq_hilbert_sub_transverse hy p p q).symm
  have htermCompl : Summable (fun q : ↥((↑S : Set XiZeroCopy)ᶜ) =>
      xiShiftedApertureHankelPairTerm y p p (q : XiZeroCopy)) :=
    hterm.subtype _
  have hcapAll := summable_weightedLagrangeEvaluationCapacity_xiShifted hy.le x hx
  have hcapCompl : Summable (fun q : ↥((↑S : Set XiZeroCopy)ᶜ) =>
      weightedLagrangeEvaluationCapacity x
        (xiShiftedReciprocalSquare y (q : XiZeroCopy))) :=
    hcapAll.subtype _
  have htailBound :
      -(∑' q : ↥((↑S : Set XiZeroCopy)ᶜ),
          xiShiftedApertureHankelPairTerm y p p (q : XiZeroCopy)) ≤
        (∑' q : ↥((↑S : Set XiZeroCopy)ᶜ),
          weightedLagrangeEvaluationCapacity x
            (xiShiftedReciprocalSquare y (q : XiZeroCopy))) * E := by
    rw [← tsum_neg, ← tsum_mul_right]
    exact Summable.tsum_le_tsum
      (fun q => neg_xiShiftedHankelPairTerm_le_capacity_mul_criticalPrefix
        x qcrit hx hinj p hp hdegree y hcoord (q : XiZeroCopy))
      htermCompl.neg (hcapCompl.mul_right E)
  have hsplit := hterm.sum_add_tsum_compl (s := S)
  rw [hprefix] at hsplit
  change (∑' q : ↥((↑S : Set XiZeroCopy)ᶜ),
      weightedLagrangeEvaluationCapacity x
        (xiShiftedReciprocalSquare y (q : XiZeroCopy))) < 1 at hcap
  nlinarith

/-- **Fiber-saturated infinite Route-U criterion.**  The finite selected set may contain every
multiplicity/reflection copy over the interpolation nodes, and may contain further positive real
Xi atoms.  Complementary capacity below one still forces strict positivity of the full Hankel
square. -/
theorem full_xiShiftedHankelPair_tsum_pos_of_saturated_capacity_lt_one
    {k : ℕ} {y : ℝ} (hy : 0 < y)
    (x : Fin k → ℝ) (qcrit : Fin k → XiZeroCopy)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x)
    (p : Polynomial ℝ) (hp : p ≠ 0) (hdegree : p.natDegree < k)
    (hcoord : ∀ i, xiShiftedReciprocalSquare y (qcrit i) = (x i : ℂ))
    (S : Finset XiZeroCopy) (hinclude : ∀ i, qcrit i ∈ S)
    (hpositive : ∀ q ∈ S, ∃ t : ℝ, 0 < t ∧
      xiShiftedReciprocalSquare y q = (t : ℂ))
    (hcap : (∑' q : ↥((↑S : Set XiZeroCopy)ᶜ),
      weightedLagrangeEvaluationCapacity x
        (xiShiftedReciprocalSquare y (q : XiZeroCopy))) < 1) :
    0 < ∑' q : XiZeroCopy, xiShiftedApertureHankelPairTerm y p p q := by
  classical
  let T : Finset XiZeroCopy := (Finset.univ : Finset (Fin k)).image qcrit
  let E := ∑ i : Fin k, xiShiftedApertureHankelPairTerm y p p (qcrit i)
  have hqinj : Function.Injective qcrit := by
    intro i j hij
    apply hinj
    apply Complex.ofReal_injective
    rw [← hcoord i, ← hcoord j, hij]
  have hE : 0 < E := by
    dsimp only [E]
    rw [sum_xiShiftedHankelPairTerm_eq_weighted_nodal_energy x qcrit p y hcoord]
    exact weighted_nodal_energy_pos x hx hinj p hp hdegree
  have hTsum :
      (∑ q ∈ T, xiShiftedApertureHankelPairTerm y p p q) = E := by
    dsimp only [T, E]
    rw [Finset.sum_image (fun i _ j _ hij => hqinj hij)]
  have hTsub : T ⊆ S := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact hinclude i
  have htermNonneg : ∀ q ∈ S,
      0 ≤ xiShiftedApertureHankelPairTerm y p p q := by
    intro q hq
    obtain ⟨t, ht, htcoord⟩ := hpositive q hq
    rw [xiShiftedApertureHankelPairTerm, htcoord]
    simp only [evalRealPolynomial_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    calc
      0 ≤ t * Polynomial.eval t p ^ 2 := mul_nonneg ht.le (sq_nonneg _)
      _ = t * Polynomial.eval t p * Polynomial.eval t p := by ring
  have hprefixLower : E ≤
      ∑ q ∈ S, xiShiftedApertureHankelPairTerm y p p q := by
    rw [← hTsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hTsub
      (fun q hq _ => htermNonneg q hq)
  have hterm : Summable (xiShiftedApertureHankelPairTerm y p p) := by
    have h := (summable_xiShiftedApertureHilbertPairTerm hy p p).sub
      (summable_xiShiftedApertureTransversePairTerm hy p p)
    exact h.congr fun q =>
      (xiShiftedApertureHankelPairTerm_eq_hilbert_sub_transverse hy p p q).symm
  have htermCompl : Summable (fun q : ↥((↑S : Set XiZeroCopy)ᶜ) =>
      xiShiftedApertureHankelPairTerm y p p (q : XiZeroCopy)) :=
    hterm.subtype _
  have hcapAll := summable_weightedLagrangeEvaluationCapacity_xiShifted hy.le x hx
  have hcapCompl : Summable (fun q : ↥((↑S : Set XiZeroCopy)ᶜ) =>
      weightedLagrangeEvaluationCapacity x
        (xiShiftedReciprocalSquare y (q : XiZeroCopy))) :=
    hcapAll.subtype _
  have htailBound :
      -(∑' q : ↥((↑S : Set XiZeroCopy)ᶜ),
          xiShiftedApertureHankelPairTerm y p p (q : XiZeroCopy)) ≤
        (∑' q : ↥((↑S : Set XiZeroCopy)ᶜ),
          weightedLagrangeEvaluationCapacity x
            (xiShiftedReciprocalSquare y (q : XiZeroCopy))) * E := by
    rw [← tsum_neg, ← tsum_mul_right]
    exact Summable.tsum_le_tsum
      (fun q => neg_xiShiftedHankelPairTerm_le_capacity_mul_criticalPrefix
        x qcrit hx hinj p hp hdegree y hcoord (q : XiZeroCopy))
      htermCompl.neg (hcapCompl.mul_right E)
  have hsplit := hterm.sum_add_tsum_compl (s := S)
  nlinarith

/-- **Reflection-fold no-go for an unsaturated sampling set.**  If the selected set contains only
one representative per distinct reciprocal-square node, FE reflection leaves a distinct copy in
the complement at a selected node.  Its capacity is exactly one, so complementary capacity can
never be below one. -/
theorem one_le_compl_capacity_of_reflection_fold
    {k : ℕ} (x : Fin k → ℝ) (qcrit : Fin k → XiZeroCopy)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x)
    (y : ℝ) (hy : 0 ≤ y)
    (hcoord : ∀ i, xiShiftedReciprocalSquare y (qcrit i) = (x i : ℂ))
    (i : Fin k) :
    1 ≤ ∑' q : ↥((↑((Finset.univ : Finset (Fin k)).image qcrit) :
        Set XiZeroCopy)ᶜ),
      weightedLagrangeEvaluationCapacity x
        (xiShiftedReciprocalSquare y (q : XiZeroCopy)) := by
  classical
  let S : Finset XiZeroCopy := (Finset.univ : Finset (Fin k)).image qcrit
  have hreflect_ne (q : XiZeroCopy) : xiZeroCopyReflectEquiv q ≠ q := by
    intro h
    have hspectral := congrArg xiSpectralPoint h
    rw [xiSpectralPoint_reflect] at hspectral
    have hzero : xiSpectralPoint q = 0 := by
      linear_combination (-1 / 2 : ℂ) * hspectral
    exact xiSpectralPoint_ne_zero q hzero
  have hreflectCoord (q : XiZeroCopy) :
      xiShiftedReciprocalSquare y (xiZeroCopyReflectEquiv q) =
        xiShiftedReciprocalSquare y q := by
    simp [xiShiftedReciprocalSquare, xiZeroCopyReciprocalSquare,
      xiSpectralPoint_reflect]
  have hnot : xiZeroCopyReflectEquiv (qcrit i) ∉ S := by
    intro hmem
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
    have hxij : x j = x i := by
      apply Complex.ofReal_injective
      rw [← hcoord j, hj, hreflectCoord, hcoord i]
    have hji : j = i := hinj hxij
    subst j
    exact hreflect_ne (qcrit i) hj.symm
  let r : ↥((↑S : Set XiZeroCopy)ᶜ) :=
    ⟨xiZeroCopyReflectEquiv (qcrit i), by simpa only [Set.mem_compl_iff,
      Finset.mem_coe, not_false_eq_true] using hnot⟩
  have hsum := (summable_weightedLagrangeEvaluationCapacity_xiShifted
    (y := y) hy x hx).subtype ((↑S : Set XiZeroCopy)ᶜ)
  have hterm : weightedLagrangeEvaluationCapacity x
      (xiShiftedReciprocalSquare y (r : XiZeroCopy)) = 1 := by
    dsimp only [r]
    rw [hreflectCoord, hcoord i,
      weightedLagrangeEvaluationCapacity_at_node x hx hinj i]
  have hle := hsum.le_tsum r (fun q _ =>
    weightedLagrangeEvaluationCapacity_nonneg x hx
      (xiShiftedReciprocalSquare y (q : XiZeroCopy)))
  change weightedLagrangeEvaluationCapacity x
      (xiShiftedReciprocalSquare y (r : XiZeroCopy)) ≤
    ∑' q : ↥((↑S : Set XiZeroCopy)ᶜ), weightedLagrangeEvaluationCapacity x
      (xiShiftedReciprocalSquare y (q : XiZeroCopy)) at hle
  rw [hterm] at hle
  simpa only [S] using hle

end

end RHTower
