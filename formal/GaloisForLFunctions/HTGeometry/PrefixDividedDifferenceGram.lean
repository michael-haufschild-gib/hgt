import GaloisForLFunctions.HTGeometry.MixedTranslationDividedDifference
import GaloisForLFunctions.HTGeometry.PositiveDefiniteMatrixLimit

/-!
# Uniform clustered Gram positivity through prefix divided differences

The prefix transform is exactly triangular and invertible at distinct ordered nodes. Its
congruence entries are mixed divided differences. Their mean-value identity gives convergence
to the factorial-normalized derivative matrix as every node approaches zero, independently of
all spacing ratios. A strict limiting jet matrix therefore gives one positive-definite chamber
covering every ordered cluster shape.
-/

open Matrix Finset Set Filter Topology
namespace GaloisForLFunctions.HTGeometry
open HilbertIrreducibility
noncomputable section

def prefixNodeIndex {N : ℕ} (p : Fin N) (k : Fin (p.val+1)) : Fin N :=
  ⟨k.val, lt_of_lt_of_le k.isLt (Nat.succ_le_of_lt p.isLt)⟩

def prefixNodes {N : ℕ} (t : Fin N → ℝ) (p : Fin N) (k : Fin (p.val+1)) : ℝ :=
  t (prefixNodeIndex p k)

theorem strictMono_prefixNodes {N : ℕ} {t : Fin N → ℝ} (ht : StrictMono t) (p : Fin N) :
    StrictMono (prefixNodes t p) := by
  intro i j hij
  exact ht (show prefixNodeIndex p i < prefixNodeIndex p j from hij)

def prefixNodeDenominator {N : ℕ} (t : Fin N → ℝ) (p : Fin N) (k : Fin (p.val+1)) : ℝ :=
  ∏ j ∈ Finset.univ.erase k, (prefixNodes t p k-prefixNodes t p j)

/-- Prefix divided differences as a square triangular coordinate transform. -/
def prefixDividedDifferenceTransform {N : ℕ} (t : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun p i => ∑ k : Fin (p.val+1),
    if prefixNodeIndex p k = i then (prefixNodeDenominator t p k)⁻¹ else 0

/-- Action of a transform row is precisely a divided difference of the sampled values. -/
theorem prefixDividedDifferenceTransform_sum {N : ℕ} (t : Fin N → ℝ) (p : Fin N)
    (g : Fin N → ℝ) :
    (∑ i, prefixDividedDifferenceTransform t p i * g i) =
      ∑ k : Fin (p.val+1), g (prefixNodeIndex p k) / prefixNodeDenominator t p k := by
  unfold prefixDividedDifferenceTransform
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp [div_eq_mul_inv, mul_comm]

theorem prefixDividedDifferenceTransform_diag {N : ℕ} (t : Fin N → ℝ) (p : Fin N) :
    prefixDividedDifferenceTransform t p p = (prefixNodeDenominator t p (Fin.last p.val))⁻¹ := by
  have heq (k : Fin (p.val+1)) : prefixNodeIndex p k = p ↔ k = Fin.last p.val := by
    constructor
    · intro h
      apply Fin.ext
      exact congrArg (fun z : Fin N => z.val) h
    · rintro rfl
      rfl
  simp [prefixDividedDifferenceTransform, heq]

/-- Distinct ordered nodes make the exact prefix transform invertible, however small their gaps. -/
theorem isUnit_prefixDividedDifferenceTransform {N : ℕ} {t : Fin N → ℝ} (ht : StrictMono t) :
    IsUnit (prefixDividedDifferenceTransform t) := by
  have htri : (prefixDividedDifferenceTransform t).BlockTriangular OrderDual.toDual := by
    intro i j hij
    change i < j at hij
    apply Finset.sum_eq_zero
    intro k _
    have hne : prefixNodeIndex i k ≠ j := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp only [prefixNodeIndex] at hval
      have hk := k.isLt
      have hijv : i.val < j.val := hij
      omega
    simp only [if_neg hne]
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_lowerTriangular _ htri, isUnit_iff_ne_zero]
  apply Finset.prod_ne_zero_iff.mpr
  intro p _
  rw [prefixDividedDifferenceTransform_diag]
  exact inv_ne_zero (prod_erase_ne_zero (strictMono_prefixNodes ht p).injective _)

/-- Literal finite Gram matrix of a translation kernel. -/
def translationSampleGram {N : ℕ} (f : ℝ → ℝ) (t : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => f (t i-t j)

/-- Exact normalized Gram matrix in prefix divided-difference coordinates. -/
def prefixDividedDifferenceGram {N : ℕ} (f : ℝ → ℝ) (t : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  prefixDividedDifferenceTransform t * translationSampleGram f t *
    (prefixDividedDifferenceTransform t)ᵀ

theorem prefixDividedDifferenceGram_apply {N : ℕ} (f : ℝ → ℝ) (t : Fin N → ℝ) (p q : Fin N) :
    prefixDividedDifferenceGram f t p q =
      mixedTranslationDividedDiff f (prefixNodes t p) (prefixNodes t q) := by
  unfold prefixDividedDifferenceGram
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  have hinner (i : Fin N) :
      (∑ j, translationSampleGram f t i j * prefixDividedDifferenceTransform t q j) =
        ∑ k : Fin (q.val+1),
          translationSampleGram f t i (prefixNodeIndex q k) / prefixNodeDenominator t q k := by
    simpa only [mul_comm] using prefixDividedDifferenceTransform_sum t q
      (fun j => translationSampleGram f t i j)
  simp_rw [hinner]
  rw [prefixDividedDifferenceTransform_sum]
  rfl

theorem translationSampleGram_isHermitian {N : ℕ} {f : ℝ → ℝ} (hf : Function.Even f)
    (t : Fin N → ℝ) : (translationSampleGram f t).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [translationSampleGram, star_trivial]
  simpa only [neg_sub] using hf (t i-t j)

theorem prefixDividedDifferenceGram_isHermitian {N : ℕ} {f : ℝ → ℝ} (hf : Function.Even f)
    (t : Fin N → ℝ) : (prefixDividedDifferenceGram f t).IsHermitian := by
  simpa only [prefixDividedDifferenceGram, conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_mul_mul_conjTranspose (prefixDividedDifferenceTransform t)
      (translationSampleGram_isHermitian hf t)

/-- Congruence transports normalized strict positivity back to the literal sampled kernel. -/
theorem translationSampleGram_posDef_of_prefix {N : ℕ} {f : ℝ → ℝ} {t : Fin N → ℝ}
    (ht : StrictMono t) (hpos : (prefixDividedDifferenceGram f t).PosDef) :
    (translationSampleGram f t).PosDef := by
  apply (isUnit_prefixDividedDifferenceTransform ht).posDef_star_right_conjugate_iff.mp
  simpa only [prefixDividedDifferenceGram, Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hpos


/-- Factorial-normalized signed derivative matrix at total coalescence. -/
def translationJetMatrix (N : ℕ) (f : ℝ → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun p q => (-1 : ℝ)^q.val * iteratedDeriv (p.val+q.val) f 0 /
    ((p.val.factorial : ℝ) * (q.val.factorial : ℝ))

/-- The prefix-normalized entries converge uniformly over all ordered node shapes. -/
theorem tendsto_prefixDividedDifferenceGram_apply {N : ℕ} {f : ℝ → ℝ}
    (p q : Fin N) (hf : ContDiff ℝ (p.val+q.val : ℕ) f) :
    Tendsto (fun t : Fin N → ℝ => prefixDividedDifferenceGram f t p q)
      (𝓝[{t : Fin N → ℝ | StrictMono t}] 0) (𝓝 (translationJetMatrix N f p q)) := by
  let g : ℝ → ℝ := fun z => (-1 : ℝ)^q.val * iteratedDeriv (p.val+q.val) f z /
    ((p.val.factorial : ℝ) * (q.val.factorial : ℝ))
  have hcont : ContinuousAt g 0 :=
    (((hf.continuous_iteratedDeriv' (p.val+q.val)).const_mul _).div_const _).continuousAt
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hcont ε hε
  refine ⟨δ/2, half_pos hδ, ?_⟩
  intro t ht hsmall
  have htNorm : ‖t‖ < δ/2 := by simpa only [dist_zero_right] using hsmall
  obtain ⟨u, hu, v, hv, heq⟩ := exists_mixedTranslationDividedDiff_eq hf
    (prefixNodes t p) (strictMono_prefixNodes ht p)
    (prefixNodes t q) (strictMono_prefixNodes ht q)
  have hnode (i : Fin N) : -‖t‖ ≤ t i ∧ t i ≤ ‖t‖ := by
    apply abs_le.mp
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm t i
  have huBound : -‖t‖ ≤ u ∧ u ≤ ‖t‖ :=
    ⟨(hnode (prefixNodeIndex p 0)).1.trans hu.1,
      hu.2.trans (hnode (prefixNodeIndex p (Fin.last p.val))).2⟩
  have hvBound : -‖t‖ ≤ v ∧ v ≤ ‖t‖ :=
    ⟨(hnode (prefixNodeIndex q 0)).1.trans hv.1,
      hv.2.trans (hnode (prefixNodeIndex q (Fin.last q.val))).2⟩
  have huv : dist (u-v) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith only [huBound.1, huBound.2, hvBound.1, hvBound.2, htNorm]
  rw [prefixDividedDifferenceGram_apply, heq]
  exact hclose huv

/-- A strict derivative Gram matrix opens one local chamber for every ordered node shape. -/
theorem eventually_translationSampleGram_posDef_of_jet {N : ℕ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ (2*(N-1) : ℕ) f) (heven : Function.Even f)
    (hjet : (translationJetMatrix N f).PosDef) :
    ∀ᶠ t : Fin N → ℝ in 𝓝[{t : Fin N → ℝ | StrictMono t}] 0,
      (translationSampleGram f t).PosDef := by
  have hlim (p q : Fin N) := tendsto_prefixDividedDifferenceGram_apply p q
    (hf.of_le (by
      have hp := p.isLt
      have hq := q.isLt
      exact_mod_cast (show p.val+q.val ≤ 2*(N-1) by omega)))
  have hp := posDef_eventually_of_tendsto hjet
    (Filter.Eventually.of_forall (prefixDividedDifferenceGram_isHermitian heven)) hlim
  filter_upwards [hp, self_mem_nhdsWithin] with t hpt ht
  exact translationSampleGram_posDef_of_prefix ht hpt

/-- Quantified cluster radius independent of the smallest gap. -/
theorem exists_translationSampleGram_posDef_radius {N : ℕ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ (2*(N-1) : ℕ) f) (heven : Function.Even f)
    (hjet : (translationJetMatrix N f).PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : Fin N → ℝ, StrictMono t → ‖t‖ < δ →
      (translationSampleGram f t).PosDef := by
  have hev := eventually_translationSampleGram_posDef_of_jet hf heven hjet
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp hev
  exact ⟨δ, hδ, fun t ht hsmall => hball ⟨by simpa only [Metric.mem_ball,
    dist_zero_right] using hsmall, ht⟩⟩

end
end GaloisForLFunctions.HTGeometry
