import GaloisForLFunctions.HilbertMetric.RankOneSchurGaussianConcavity
import GaloisForLFunctions.HilbertMetric.DegreeFiveGaussianCurvature

/-!
# Gaussian metric rank-one concavity and higher-rank fracture

This module gives the invariant finite-Hilbert form of the rank-one Schur--Gaussian law.
Appending one weighted scalar feature is a rank-one update of the squared Hilbert metric, so its
Gaussian log-volume has exact negative self-commutator curvature.  The already formalized
degree-five configuration supplies the complementary higher-rank positive-curvature witness.
-/

open Filter
open scoped BigOperators Matrix MatrixOrder

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Gaussian Gram matrix obtained by appending one scalar feature with squared weight `t` to a
finite Euclidean feature family. -/
def gaussianMetricRankOneExtensionGram {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (a : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Real.exp
    (-(∑ k, (y i k - y j k) ^ (2 : ℕ) + t * (a i - a j) ^ (2 : ℕ)))

/-- Appending one metric feature is literally Schur multiplication of the background Gaussian
Gram by the one-dimensional Gaussian semigroup. -/
theorem gaussianMetricRankOneExtensionGram_eq_rankOneSchurGaussianPath {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (a : Fin n → ℝ) (t : ℝ) :
    gaussianMetricRankOneExtensionGram y a t =
      rankOneSchurGaussianPath (finiteGaussianDistanceGram y 1) a t := by
  ext i j
  simp only [gaussianMetricRankOneExtensionGram, rankOneSchurGaussianPath,
    finiteGaussianDistanceGram]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The unit-scale Gaussian distance Gram of every injective finite Euclidean family is positive
definite.  This supplies the unconditional positive background required by the metric law. -/
theorem finiteGaussianDistanceGram_one_posDef_of_injective {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (hy : Function.Injective y) :
    (finiteGaussianDistanceGram y 1).PosDef := by
  let z : Fin n → Fin d → ℝ := fun i k => Real.sqrt 2 * y i k
  let B : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (finiteGaussianGauge z 1)
  have hsqrt : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hsquare : Real.sqrt 2 ^ (2 : ℕ) = 2 := Real.sq_sqrt (by norm_num)
  have hz : Function.Injective z := by
    intro i j hij
    apply hy
    funext k
    exact mul_left_cancel₀ hsqrt (congrFun hij k)
  have hmetric : finiteGaussianDistanceGram y 1 =
      finiteHalfGaussianDistanceGram z 1 := by
    ext i j
    simp only [finiteGaussianDistanceGram, finiteHalfGaussianDistanceGram,
      one_div, z]
    congr 1
    rw [Finset.sum_congr rfl (fun k _ => show
      (Real.sqrt 2 * y i k - Real.sqrt 2 * y j k) ^ (2 : ℕ) =
        2 * (y i k - y j k) ^ (2 : ℕ) by
          rw [show Real.sqrt 2 * y i k - Real.sqrt 2 * y j k =
            Real.sqrt 2 * (y i k - y j k) by ring]
          rw [mul_pow, hsquare])]
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  have hinnerEq : finiteExponentialInnerGram z 1 = gaussianCoherentGram z := by
    ext i j
    simp [finiteExponentialInnerGram, gaussianCoherentGram, coordinateDot]
  have hinner : (finiteExponentialInnerGram z 1).PosDef := by
    rw [hinnerEq]
    exact (gaussianCoherentGram_posDef_iff_injective z).2 hz
  have hB : B.PosDef := by
    dsimp [B]
    exact Matrix.PosDef.diagonal fun i => Real.exp_pos _
  have hBinj : Function.Injective B.mulVec :=
    Matrix.mulVec_injective_of_isUnit hB.isUnit
  have hcong := hinner.conjTranspose_mul_mul_same (B := B) hBinj
  rw [hmetric, finiteHalfGaussianDistanceGram_eq_gauge]
  change (B * finiteExponentialInnerGram z 1 * B).PosDef
  simpa [B, Matrix.conjTranspose_eq_transpose_of_trivial] using hcong

/-- Every positive Gaussian bandwidth gives a positive-definite distance Gram on an injective
finite Euclidean family.  Thus unit bandwidth is a normalization, not an extra hypothesis. -/
theorem finiteGaussianDistanceGram_posDef_of_injective_of_pos {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (hy : Function.Injective y)
    {t : ℝ} (ht : 0 < t) :
    (finiteGaussianDistanceGram y t).PosDef := by
  let z : Fin n → Fin d → ℝ := fun i k => Real.sqrt t * y i k
  have hsqrt : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have hsquare : Real.sqrt t ^ (2 : ℕ) = t := Real.sq_sqrt ht.le
  have hz : Function.Injective z := by
    intro i j hij
    apply hy
    funext k
    exact mul_left_cancel₀ hsqrt (congrFun hij k)
  have hmetric : finiteGaussianDistanceGram y t =
      finiteGaussianDistanceGram z 1 := by
    ext i j
    simp only [finiteGaussianDistanceGram, z]
    congr 1
    rw [Finset.sum_congr rfl (fun k _ => show
      (Real.sqrt t * y i k - Real.sqrt t * y j k) ^ (2 : ℕ) =
        t * (y i k - y j k) ^ (2 : ℕ) by
          rw [show Real.sqrt t * y i k - Real.sqrt t * y j k =
            Real.sqrt t * (y i k - y j k) by ring]
          rw [mul_pow, hsquare])]
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  rw [hmetric]
  exact finiteGaussianDistanceGram_one_posDef_of_injective z hz

/-- At every positive bandwidth, strict Gaussian positivity fails exactly at repeated feature
vectors. -/
theorem finiteGaussianDistanceGram_posDef_iff_injective_of_pos {n d : ℕ}
    (y : Fin n → Fin d → ℝ) {t : ℝ} (ht : 0 < t) :
    (finiteGaussianDistanceGram y t).PosDef ↔ Function.Injective y := by
  constructor
  · intro hgram i j hij
    by_contra hne
    have hrows : finiteGaussianDistanceGram y t i =
        finiteGaussianDistanceGram y t j := by
      funext k
      simp [finiteGaussianDistanceGram, hij]
    exact hgram.det_pos.ne' (Matrix.det_zero_of_row_eq hne hrows)
  · intro hy
    exact finiteGaussianDistanceGram_posDef_of_injective_of_pos y hy ht

/-- The positive-bandwidth Gaussian collision classification is independent of the chosen finite
index type. -/
theorem finiteGaussianDistanceGram_posDef_iff_injective_of_pos_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (y : ι → Fin d → ℝ) {t : ℝ} (ht : 0 < t) :
    (finiteGaussianDistanceGram y t).PosDef ↔ Function.Injective y := by
  constructor
  · intro hgram i j hij
    by_contra hne
    have hrows : finiteGaussianDistanceGram y t i =
        finiteGaussianDistanceGram y t j := by
      funext k
      simp [finiteGaussianDistanceGram, hij]
    exact hgram.det_pos.ne' (Matrix.det_zero_of_row_eq hne hrows)
  · intro hy
    let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    let yf : Fin (Fintype.card ι) → Fin d → ℝ := fun i => y (e.symm i)
    have hyf : Function.Injective yf := by
      intro i j hij
      apply e.symm.injective
      apply hy
      exact hij
    have hfin := finiteGaussianDistanceGram_posDef_of_injective_of_pos yf hyf ht
    have hsub := hfin.submatrix e.injective
    have hmetric : finiteGaussianDistanceGram y t =
        (finiteGaussianDistanceGram yf t).submatrix e e := by
      ext i j
      simp [finiteGaussianDistanceGram, yf, e]
    rw [hmetric]
    exact hsub

/-- **Exact positive-bandwidth Gaussian rank law.** The rank of a finite Gaussian distance Gram is
the number of distinct feature vectors. Repeated inputs create all and only its rank defect. -/
theorem finiteGaussianDistanceGram_rank_eq_image_card_of_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (y : ι → Fin d → ℝ) {t : ℝ} (ht : 0 < t) :
    (finiteGaussianDistanceGram y t).rank = (Finset.univ.image y).card := by
  classical
  let S : Finset (Fin d → ℝ) := Finset.univ.image y
  let witness (a : S) : ∃ i ∈ (Finset.univ : Finset ι), y i = a :=
    Finset.mem_image.mp a.2
  let rep : S → ι := fun a => (witness a).choose
  have hrep (a : S) : y (rep a) = a := (witness a).choose_spec.2
  let label : ι → S := fun i => ⟨y i, by simp [S]⟩
  have hrep_label (i : ι) : y (rep (label i)) = y i := by
    simpa [label] using hrep (label i)
  have hrep_injective : Function.Injective rep := by
    intro a b hab
    apply Subtype.ext
    rw [← hrep a, ← hrep b, hab]
  let yr : S → Fin d → ℝ := fun a => y (rep a)
  have hyr : Function.Injective yr := by
    intro a b hab
    apply Subtype.ext
    rw [← hrep a, ← hrep b]
    exact hab
  let M : Matrix ι ι ℝ := finiteGaussianDistanceGram y t
  have hsub : M.submatrix rep rep = finiteGaussianDistanceGram yr t := by
    rfl
  have hpos : (finiteGaussianDistanceGram yr t).PosDef :=
    (finiteGaussianDistanceGram_posDef_iff_injective_of_pos_fintype yr ht).2 hyr
  have hsubrank : (M.submatrix rep rep).rank = Fintype.card S := by
    rw [hsub]
    exact Matrix.rank_of_isUnit _ hpos.isUnit
  have hlower : S.card ≤ M.rank := by
    calc
      S.card = Fintype.card S := by simp
      _ = (M.submatrix rep rep).rank := hsubrank.symm
      _ ≤ M.rank := Matrix.rank_submatrix_le M rep rep
  have hrow (i : ι) : M.row i = M.row (rep (label i)) := by
    funext j
    change finiteGaussianDistanceGram y t i j =
      finiteGaussianDistanceGram y t (rep (label i)) j
    simp only [finiteGaussianDistanceGram]
    rw [hrep_label]
  have hrange : Set.range M.row =
      Set.range (fun a : S => M.row (rep a)) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨label i, (hrow i).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨rep a, rfl⟩
  have hupper : M.rank ≤ S.card := by
    rw [M.rank_eq_finrank_span_row, hrange]
    simpa only [Set.finrank, Fintype.card_coe] using
      (finrank_range_le_card (R := ℝ) (fun a : S => M.row (rep a)))
  change M.rank = S.card
  exact le_antisymm hupper hlower

/-- Exact Legendre--Hadamard curvature of finite Gaussian log-volume under one rank-one Hilbert
metric extension. -/
theorem gaussianMetricRankOneExtension_logDet_secondDerivative_eq {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (a : Fin n → ℝ)
    (hy : Function.Injective y) (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s =>
      Real.log (gaussianMetricRankOneExtensionGram y a s).det)) t =
        -2 * matrixHilbertSchmidtEnergy
          (matrixSelfCommutator
            (matrixSqrtSimilarity
              (rankOneSchurExponentialPath (finiteGaussianDistanceGram y 1) a (2 * t))
              (rankOneLabelDiagonal a))) := by
  have hfun :
      (fun s => Real.log (gaussianMetricRankOneExtensionGram y a s).det) =
        fun s => Real.log
          (rankOneSchurGaussianPath (finiteGaussianDistanceGram y 1) a s).det := by
    funext s
    rw [gaussianMetricRankOneExtensionGram_eq_rankOneSchurGaussianPath]
  rw [hfun]
  exact rankOneSchurGaussian_logDet_secondDerivative_eq
    (finiteGaussianDistanceGram y 1) a
    (finiteGaussianDistanceGram_one_posDef_of_injective y hy) t ht

/-- Gaussian log-volume is globally concave along every rank-one finite-Hilbert metric extension. -/
theorem gaussianMetricRankOneExtension_logDet_concaveOn {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (a : Fin n → ℝ)
    (hy : Function.Injective y) :
    ConcaveOn ℝ (Set.Ici 0)
      (fun t => Real.log (gaussianMetricRankOneExtensionGram y a t).det) := by
  have hfun :
      (fun t => Real.log (gaussianMetricRankOneExtensionGram y a t).det) =
        fun t => Real.log
          (rankOneSchurGaussianPath (finiteGaussianDistanceGram y 1) a t).det := by
    funext t
    rw [gaussianMetricRankOneExtensionGram_eq_rankOneSchurGaussianPath]
  rw [hfun]
  exact rankOneSchurGaussian_logDet_concaveOn
    (finiteGaussianDistanceGram y 1) a
    (finiteGaussianDistanceGram_one_posDef_of_injective y hy)

/-- Rank-one metric curvature vanishes exactly when the appended scalar feature is constant. -/
theorem gaussianMetricRankOneExtension_logDet_secondDerivative_eq_zero_iff_constant {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (a : Fin n → ℝ)
    (hy : Function.Injective y) (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s =>
      Real.log (gaussianMetricRankOneExtensionGram y a s).det)) t = 0 ↔
        ∀ i j, a i = a j := by
  have hfun :
      (fun s => Real.log (gaussianMetricRankOneExtensionGram y a s).det) =
        fun s => Real.log
          (rankOneSchurGaussianPath (finiteGaussianDistanceGram y 1) a s).det := by
    funext s
    rw [gaussianMetricRankOneExtensionGram_eq_rankOneSchurGaussianPath]
  rw [hfun]
  have hbase := finiteGaussianDistanceGram_one_posDef_of_injective y hy
  constructor
  · intro hzero i j
    have hblock :=
      (rankOneSchurGaussian_logDet_secondDerivative_eq_zero_iff_block
        (finiteGaussianDistanceGram y 1) a hbase t ht).1 hzero
    by_contra hij
    have hentry := hblock i j hij
    simp [finiteGaussianDistanceGram] at hentry
  · intro hconstant
    apply (rankOneSchurGaussian_logDet_secondDerivative_eq_zero_iff_block
      (finiteGaussianDistanceGram y 1) a hbase t ht).2
    intro i j hij
    exact (hij (hconstant i j)).elim

/-- A nonconstant added metric feature makes the rank-one curvature strictly negative at every
nonnegative scale. -/
theorem gaussianMetricRankOneExtension_logDet_secondDerivative_lt_zero {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (a : Fin n → ℝ)
    (hy : Function.Injective y) (t : ℝ) (ht : 0 ≤ t)
    (hlabels : ∃ i j, a i ≠ a j) :
    deriv (deriv (fun s =>
      Real.log (gaussianMetricRankOneExtensionGram y a s).det)) t < 0 := by
  have hfun :
      (fun s => Real.log (gaussianMetricRankOneExtensionGram y a s).det) =
        fun s => Real.log
          (rankOneSchurGaussianPath (finiteGaussianDistanceGram y 1) a s).det := by
    funext s
    rw [gaussianMetricRankOneExtensionGram_eq_rankOneSchurGaussianPath]
  rw [hfun]
  apply rankOneSchurGaussian_logDet_secondDerivative_lt_zero
    (finiteGaussianDistanceGram y 1) a
    (finiteGaussianDistanceGram_one_posDef_of_injective y hy) t ht
  · intro i j
    exact Real.exp_ne_zero _
  · exact hlabels

/-- **Gaussian metric rank-one/full-rank fracture.**  Every one-feature metric extension is
log-volume concave, while an injective finite Euclidean Gaussian family exists whose isotropic
higher-rank metric scaling has strictly positive log-volume curvature. -/
theorem gaussianMetricRankOneConcavity_and_higherRankFracture :
    (∀ (n d : ℕ) (y : Fin n → Fin d → ℝ) (a : Fin n → ℝ),
      Function.Injective y →
        ConcaveOn ℝ (Set.Ici 0)
          (fun t => Real.log (gaussianMetricRankOneExtensionGram y a t).det)) ∧
      ∃ x : DegreeFiveIndex 16 → (Fin 16 ⊕ DegreeFiveTopIndex 16 → ℝ),
        Function.Injective x ∧
        (finiteGaussianDistanceGram x 1).det ≠ 0 ∧
        0 < deriv (deriv
          (fun t => Real.log (finiteGaussianDistanceGram x t).det)) 1 := by
  constructor
  · intro n d y a hy
    exact gaussianMetricRankOneExtension_logDet_concaveOn y a hy
  · exact exists_finiteGaussianDistanceGram_positiveLogDetCurvature

end

end GaloisForLFunctions.HilbertMetric
