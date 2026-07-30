import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureTangentLoewnerLimit

/-!
# Strict dyadic innovation law for continuous Möbius apertures

The dyadic aperture-refinement increment was realized as an `ell²` Gram and hence shown positive
semidefinite.  Its explicit depth feature is a nonzero column weight times a geometric sequence.
For every finite packet of distinct positive apertures, the first `N` depth coordinates form a
weighted Vandermonde matrix.  They have full rank already at one prime, so both the one-prime and
completed all-prime innovation Grams are positive definite with positive determinant.
-/

open scoped BigOperators
open Matrix

namespace RHTower

noncomputable section

/-- First `N` depth coordinates of one prime's dyadic innovation feature packet. -/
def xiMobiusPrimeContinuousApertureDyadicInnovationSamplingMatrix
    {N : ℕ} (h : ℝ) (aperture : Fin N → ℝ) (p : Nat.Primes) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun e j => xiMobiusPrimeContinuousApertureDyadicInnovationFeature
    h (aperture j) p e

/-- The finite innovation sampling matrix is a diagonally weighted Vandermonde on squared disk
nodes. -/
theorem xiMobiusPrimeContinuousApertureDyadicInnovationSamplingMatrix_factorization
    {N : ℕ} (h : ℝ) (aperture : Fin N → ℝ) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureDyadicInnovationSamplingMatrix h aperture p =
      (Matrix.vandermonde (fun j =>
        xiMobiusContinuousApertureDiskNode ((h / 2) * aperture j) p ^ 2))ᵀ *
      Matrix.diagonal (fun j =>
        (xiTransversePrimeApertureDiskNode 1 p /
          (1 + xiTransversePrimeApertureDiskNode 1 p)) *
        (1 - xiMobiusContinuousApertureDiskNode
          ((h / 2) * aperture j) p) ^ 2) := by
  classical
  ext e j
  rw [Matrix.mul_diagonal]
  simp [xiMobiusPrimeContinuousApertureDyadicInnovationSamplingMatrix,
    xiMobiusPrimeContinuousApertureDyadicInnovationFeature,
    Matrix.vandermonde]
  ring

/-- **Exact finite dyadic nondegeneracy classification.** The innovation sampler is invertible
exactly when the mesh-scaled apertures are distinct and avoid zero. This includes either mesh
orientation and the zero-mesh boundary. -/
theorem
    xiMobiusPrimeContinuousApertureDyadicInnovationSamplingMatrix_det_ne_zero_iff_scaled_injective_ne_zero
    {N : ℕ} (h : ℝ) (aperture : Fin N → ℝ) (p : Nat.Primes) :
    (xiMobiusPrimeContinuousApertureDyadicInnovationSamplingMatrix
      h aperture p).det ≠ 0 ↔
      Function.Injective (fun j => h * aperture j) ∧
        ∀ j, h * aperture j ≠ 0 := by
  rw [xiMobiusPrimeContinuousApertureDyadicInnovationSamplingMatrix_factorization,
    Matrix.det_mul, Matrix.det_transpose]
  constructor
  · intro hdet
    obtain ⟨hvandermonde, hdiagonal⟩ := mul_ne_zero_iff.mp hdet
    have hnodes : Function.Injective (fun j =>
        xiMobiusContinuousApertureDiskNode ((h / 2) * aperture j) p ^ 2) :=
      Matrix.det_vandermonde_ne_zero_iff.mp hvandermonde
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff] at hdiagonal
    constructor
    · intro i j hij
      apply hnodes
      have hhalf :
          (h / 2) * aperture i = (h / 2) * aperture j := by
        change h * aperture i = h * aperture j at hij
        linarith
      change
        xiMobiusContinuousApertureDiskNode ((h / 2) * aperture i) p ^ 2 =
          xiMobiusContinuousApertureDiskNode ((h / 2) * aperture j) p ^ 2
      rw [hhalf]
    · intro j hj
      have hentry := hdiagonal j (Finset.mem_univ j)
      have hhalf : (h / 2) * aperture j = 0 := by linarith
      simp [hhalf, xiMobiusContinuousApertureDiskNode] at hentry
  · rintro ⟨hinjective, hne⟩
    apply mul_ne_zero
    · apply Matrix.det_vandermonde_ne_zero_iff.mpr
      intro i j hij
      have hi := xiMobiusContinuousApertureDiskNode_pos
        ((h / 2) * aperture i) p
      have hj := xiMobiusContinuousApertureDiskNode_pos
        ((h / 2) * aperture j) p
      have hnode :
          xiMobiusContinuousApertureDiskNode ((h / 2) * aperture i) p =
            xiMobiusContinuousApertureDiskNode ((h / 2) * aperture j) p := by
        nlinarith
      apply hinjective
      have hhalf := xiMobiusContinuousApertureDiskNode_injective p hnode
      linarith
    · rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
      intro j _
      apply mul_ne_zero
      · exact div_ne_zero
          (xiTransversePrimeApertureDiskNode_pos 1 p).ne'
          (by
            have hq := xiTransversePrimeApertureDiskNode_pos 1 p
            linarith)
      · apply pow_ne_zero
        apply sub_ne_zero.mpr
        intro hr
        apply hne j
        have hhalf :
            (h / 2) * aperture j = 0 := by
          apply xiMobiusContinuousApertureDiskNode_injective p
          simpa [xiMobiusContinuousApertureDiskNode] using hr.symm
        linarith

/-- Distinct positive apertures make the finite innovation sampling matrix invertible. -/
theorem xiMobiusPrimeContinuousApertureDyadicInnovationSamplingMatrix_det_ne_zero
    {N : ℕ} {h : ℝ} (hh : 0 < h) {aperture : Fin N → ℝ}
    (haperture : Function.Injective aperture) (hpos : ∀ j, 0 < aperture j)
    (p : Nat.Primes) :
    (xiMobiusPrimeContinuousApertureDyadicInnovationSamplingMatrix
      h aperture p).det ≠ 0 := by
  apply
    (xiMobiusPrimeContinuousApertureDyadicInnovationSamplingMatrix_det_ne_zero_iff_scaled_injective_ne_zero
      h aperture p).2
  constructor
  · intro i j hij
    exact haperture (mul_left_cancel₀ hh.ne' hij)
  · exact fun j => mul_ne_zero hh.ne' (hpos j).ne'

/-- The genuine one-prime `ell²` innovation features are linearly independent on every finite
injective positive aperture packet. -/
theorem xiMobiusPrimeContinuousApertureDyadicInnovationFeatureLp_linearIndependent
    {N : ℕ} {h : ℝ} (hh : 0 < h) {aperture : Fin N → ℝ}
    (haperture : Function.Injective aperture) (hpos : ∀ j, 0 < aperture j)
    (p : Nat.Primes) :
    LinearIndependent ℝ (fun j =>
      xiMobiusPrimeContinuousApertureDyadicInnovationFeatureLp
        h (aperture j) p hh (hpos j)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let A := xiMobiusPrimeContinuousApertureDyadicInnovationSamplingMatrix h aperture p
  have hAc : A.mulVec c = 0 := by
    funext e
    have he := congrArg
      (fun v : lp (fun _ : ℕ => ℝ) 2 => (v : ℕ → ℝ) (e : ℕ)) hc
    simp only [lp.coeFn_sum, lp.coeFn_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, lp.coeFn_zero, Pi.zero_apply] at he
    simpa [A, xiMobiusPrimeContinuousApertureDyadicInnovationSamplingMatrix,
      xiMobiusPrimeContinuousApertureDyadicInnovationFeatureLp,
      Matrix.mulVec, dotProduct, mul_comm] using he
  have hunit : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact xiMobiusPrimeContinuousApertureDyadicInnovationSamplingMatrix_det_ne_zero
      hh haperture hpos p
  have hc0 : c = 0 :=
    (Matrix.mulVec_injective_of_isUnit hunit)
      (hAc.trans (Matrix.mulVec_zero A).symm)
  exact fun i => congrFun hc0 i

/-- One prime already makes the dyadic innovation Gram positive definite. -/
theorem xiMobiusPrimeContinuousApertureDyadicInnovationGram_posDef
    {N : ℕ} {h : ℝ} (hh : 0 < h) {aperture : Fin N → ℝ}
    (haperture : Function.Injective aperture) (hpos : ∀ j, 0 < aperture j)
    (p : Nat.Primes) :
    (xiMobiusPrimeContinuousApertureDyadicInnovationGram h aperture p).PosDef := by
  have hgram :
      xiMobiusPrimeContinuousApertureDyadicInnovationGram h aperture p =
        Matrix.gram ℝ (fun i =>
          xiMobiusPrimeContinuousApertureDyadicInnovationFeatureLp
            h (aperture i) p hh (hpos i)) := by
    ext i j
    simp only [xiMobiusPrimeContinuousApertureDyadicInnovationGram, Matrix.gram]
    simpa only [Matrix.of_apply] using
      (inner_xiMobiusPrimeContinuousApertureDyadicInnovationFeatureLp_eq
        hh (hpos i) (hpos j) p).symm
  rw [hgram]
  exact Matrix.posDef_gram_of_linearIndependent
    (xiMobiusPrimeContinuousApertureDyadicInnovationFeatureLp_linearIndependent
      hh haperture hpos p)

/-- The completed direct-sum innovation features remain linearly independent because restriction
to the prime `2` recovers a linearly independent one-prime packet. -/
theorem xiMobiusContinuousApertureDyadicInnovationFeatureLp_linearIndependent
    {N : ℕ} {h : ℝ} (hh : 0 < h) {aperture : Fin N → ℝ}
    (haperture : Function.Injective aperture) (hpos : ∀ j, 0 < aperture j) :
    LinearIndependent ℝ (fun j =>
      xiMobiusContinuousApertureDyadicInnovationFeatureLp
        h (aperture j) hh (hpos j)) := by
  classical
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hprime :=
    xiMobiusPrimeContinuousApertureDyadicInnovationFeatureLp_linearIndependent
      hh haperture hpos p
  rw [Fintype.linearIndependent_iff] at hprime ⊢
  intro c hc
  apply hprime c
  apply Subtype.ext
  funext e
  have he := congrArg
    (fun v : lp (fun _ : Nat.Primes × ℕ => ℝ) 2 =>
      (v : Nat.Primes × ℕ → ℝ) (p, e)) hc
  simp only [lp.coeFn_sum, lp.coeFn_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, lp.coeFn_zero, Pi.zero_apply] at he ⊢
  simpa [xiMobiusContinuousApertureDyadicInnovationFeatureLp,
    xiMobiusContinuousApertureDyadicInnovationFeature,
    xiMobiusPrimeContinuousApertureDyadicInnovationFeatureLp] using he

/-- **Universal strict dyadic innovation law.**  The completed all-prime refinement increment is
positive definite on every finite packet of distinct positive apertures. -/
theorem xiMobiusContinuousApertureDyadicInnovationGram_posDef
    {N : ℕ} {h : ℝ} (hh : 0 < h) {aperture : Fin N → ℝ}
    (haperture : Function.Injective aperture) (hpos : ∀ j, 0 < aperture j) :
    (xiMobiusContinuousApertureDyadicInnovationGram h aperture).PosDef := by
  have hgram : xiMobiusContinuousApertureDyadicInnovationGram h aperture =
      Matrix.gram ℝ (fun i =>
        xiMobiusContinuousApertureDyadicInnovationFeatureLp
          h (aperture i) hh (hpos i)) := by
    ext i j
    simp only [xiMobiusContinuousApertureDyadicInnovationGram, Matrix.gram]
    simpa only [Matrix.of_apply] using
      (inner_xiMobiusContinuousApertureDyadicInnovationFeatureLp_eq
        hh (hpos i) (hpos j)).symm
  rw [hgram]
  exact Matrix.posDef_gram_of_linearIndependent
    (xiMobiusContinuousApertureDyadicInnovationFeatureLp_linearIndependent
      hh haperture hpos)

/-- One-prime dyadic self-innovation is the half-mesh Szegő self-metric times an explicit
nonnegative orientation factor. The identity remains valid at zero and for either mesh
orientation. -/
theorem xiMobiusPrimeContinuousApertureDyadicInnovation_self_eq_szegoMetric_mul
    (h a : ℝ) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureDyadicInnovation h a a p =
      xiMobiusPrimeContinuousApertureSzegoMetric ((h / 2) * a) ((h / 2) * a) p *
        ((1 - xiMobiusContinuousApertureDiskNode ((h / 2) * a) p) ^ 2 /
          (1 + xiMobiusContinuousApertureDiskNode ((h / 2) * a) p ^ 2)) := by
  by_cases hha : h * a = 0
  · have hhalf : (h / 2) * a = 0 := by linarith
    simp [xiMobiusPrimeContinuousApertureDyadicInnovation,
      xiMobiusPrimeContinuousApertureSzegoMetric, hha, hhalf,
      xiMobiusContinuousApertureDiskNode]
  · have hhalf : (h / 2) * a ≠ 0 := by
      intro hz
      apply hha
      linarith
    rw [xiMobiusPrimeContinuousApertureDyadicInnovation,
      xiMobiusPrimeContinuousApertureSzegoMetric_self_eq_of_ne_zero hhalf p,
      xiMobiusPrimeContinuousApertureSzegoMetric_self_eq_of_ne_zero hha p,
      xiMobiusContinuousApertureDiskNode_mul_eq_half_sq h a p]
    let q := xiTransversePrimeApertureDiskNode 1 p
    let r := xiMobiusContinuousApertureDiskNode ((h / 2) * a) p
    have hr : 0 < r := xiMobiusContinuousApertureDiskNode_pos _ p
    change
      2 * ((q / (1 + q)) ^ 2 * ((1 - r) / (1 + r))) -
          (q / (1 + q)) ^ 2 * ((1 - r ^ 2) / (1 + r ^ 2)) =
        (q / (1 + q)) ^ 2 * ((1 - r) / (1 + r)) *
          ((1 - r) ^ 2 / (1 + r ^ 2))
    field_simp [show 1 + r ≠ 0 by positivity, show 1 + r ^ 2 ≠ 0 by positivity]
    ring

/-- **Universal scalar orientation law.** One-prime dyadic self-innovation is positive exactly
when the mesh-scaled aperture points into the positive chamber. -/
theorem xiMobiusPrimeContinuousApertureDyadicInnovation_self_pos_iff_scaled_pos
    (h a : ℝ) (p : Nat.Primes) :
    0 < xiMobiusPrimeContinuousApertureDyadicInnovation h a a p ↔
      0 < h * a := by
  rw [xiMobiusPrimeContinuousApertureDyadicInnovation_self_eq_szegoMetric_mul]
  let t := (h / 2) * a
  let r := xiMobiusContinuousApertureDiskNode t p
  change
    0 < xiMobiusPrimeContinuousApertureSzegoMetric t t p *
      ((1 - r) ^ 2 / (1 + r ^ 2)) ↔ 0 < h * a
  by_cases hha : h * a = 0
  · have ht : t = 0 := by
      dsimp [t]
      linarith
    rw [ht]
    simp [hha, r, xiMobiusPrimeContinuousApertureSzegoMetric,
      xiMobiusContinuousApertureDiskNode]
  · have ht : t ≠ 0 := by
      intro hz
      apply hha
      dsimp [t] at hz
      linarith
    have hrne : r ≠ 1 := by
      intro hr
      apply ht
      apply xiMobiusContinuousApertureDiskNode_injective p
      simpa [r, xiMobiusContinuousApertureDiskNode] using hr
    have hfactor : 0 < (1 - r) ^ 2 / (1 + r ^ 2) := by
      exact div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm hrne))) (by positivity)
    constructor
    · intro hinnovation
      have hmetric : 0 < xiMobiusPrimeContinuousApertureSzegoMetric t t p :=
        pos_of_mul_pos_left hinnovation hfactor.le
      have htpos :=
        (xiMobiusPrimeContinuousApertureSzegoMetric_self_pos_iff t p).mp hmetric
      dsimp [t] at htpos
      nlinarith
    · intro hprod
      have htpos : 0 < t := by
        dsimp [t]
        nlinarith
      exact mul_pos
        ((xiMobiusPrimeContinuousApertureSzegoMetric_self_pos_iff t p).mpr htpos)
        hfactor

/-- Dyadic innovation depends only on the mesh-scaled aperture pair. -/
theorem xiMobiusPrimeContinuousApertureDyadicInnovation_rescale
    (h a b : ℝ) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureDyadicInnovation h a b p =
      xiMobiusPrimeContinuousApertureDyadicInnovation 1 (h * a) (h * b) p := by
  simp only [xiMobiusPrimeContinuousApertureDyadicInnovation]
  congr 2 <;> ring_nf

/-- Completed dyadic innovation is invariant under moving the common mesh scale into both
apertures. -/
theorem xiMobiusContinuousApertureDyadicInnovation_rescale (h a b : ℝ) :
    xiMobiusContinuousApertureDyadicInnovation h a b =
      xiMobiusContinuousApertureDyadicInnovation 1 (h * a) (h * b) := by
  apply tsum_congr
  exact fun p => xiMobiusPrimeContinuousApertureDyadicInnovation_rescale h a b p

/-- The completed innovation Gram at arbitrary mesh is the unit-mesh Gram of the scaled aperture
packet. -/
theorem xiMobiusContinuousApertureDyadicInnovationGram_rescale
    {N : ℕ} (h : ℝ) (aperture : Fin N → ℝ) :
    xiMobiusContinuousApertureDyadicInnovationGram h aperture =
      xiMobiusContinuousApertureDyadicInnovationGram 1
        (fun j => h * aperture j) := by
  ext i j
  exact xiMobiusContinuousApertureDyadicInnovation_rescale
    h (aperture i) (aperture j)

/-- **Exact universal strict dyadic phase.** The completed innovation Gram is positive definite
exactly when the mesh-scaled apertures are distinct and lie in the positive chamber. Thus the
statement includes positive mesh, negative mesh, and the singular zero-mesh boundary without an
external sign hypothesis. -/
theorem xiMobiusContinuousApertureDyadicInnovationGram_posDef_iff_scaled_injective_pos
    {N : ℕ} (h : ℝ) (aperture : Fin N → ℝ) :
    (xiMobiusContinuousApertureDyadicInnovationGram h aperture).PosDef ↔
      Function.Injective (fun j => h * aperture j) ∧
        ∀ j, 0 < h * aperture j := by
  rw [xiMobiusContinuousApertureDyadicInnovationGram_rescale]
  let scaled : Fin N → ℝ := fun j => h * aperture j
  change
    (xiMobiusContinuousApertureDyadicInnovationGram 1 scaled).PosDef ↔
      Function.Injective scaled ∧ ∀ j, 0 < scaled j
  constructor
  · intro hgram
    constructor
    · intro i j hij
      by_contra hne
      have hrows :
          xiMobiusContinuousApertureDyadicInnovationGram 1 scaled i =
            xiMobiusContinuousApertureDyadicInnovationGram 1 scaled j := by
        funext k
        simp only [xiMobiusContinuousApertureDyadicInnovationGram]
        rw [hij]
      have hdetZero := Matrix.det_zero_of_row_eq hne hrows
      exact hgram.det_pos.ne' hdetZero
    · intro j
      have hdiag :
          0 < xiMobiusContinuousApertureDyadicInnovation 1 (scaled j) (scaled j) := by
        simpa only [xiMobiusContinuousApertureDyadicInnovationGram] using
          hgram.diag_pos (i := j)
      by_contra hpos
      have hlocal : ∀ p : Nat.Primes,
          xiMobiusPrimeContinuousApertureDyadicInnovation
            1 (scaled j) (scaled j) p ≤ 0 := by
        intro p
        apply le_of_not_gt
        intro hp
        apply hpos
        simpa using
          (xiMobiusPrimeContinuousApertureDyadicInnovation_self_pos_iff_scaled_pos
            1 (scaled j) p).mp hp
      exact (not_lt_of_ge (tsum_nonpos hlocal)) hdiag
  · rintro ⟨hinjective, hpos⟩
    exact xiMobiusContinuousApertureDyadicInnovationGram_posDef
      zero_lt_one hinjective hpos

/-- **Exact-recovery/strict-innovation phase.** The completed dyadic innovation is strict exactly
when the original aperture packet admits canonical finite coefficient recovery and every
mesh-scaled aperture has positive orientation. No mesh-sign hypothesis remains. -/
theorem
    xiMobiusContinuousApertureDyadicInnovationGram_posDef_iff_canonicalReconstruction_and_scaled_pos
    {N : ℕ} (h : ℝ) (aperture : Fin N → ℝ) (p : Nat.Primes) :
    (xiMobiusContinuousApertureDyadicInnovationGram h aperture).PosDef ↔
      XiMobiusPrimeContinuousApertureCanonicalReconstruction aperture p ∧
        ∀ j, 0 < h * aperture j := by
  rw [xiMobiusContinuousApertureDyadicInnovationGram_posDef_iff_scaled_injective_pos,
    xiMobiusPrimeContinuousApertureCanonicalReconstruction_iff_injective_ne_zero]
  constructor
  · rintro ⟨hscaled, hpos⟩
    refine ⟨⟨?_, ?_⟩, hpos⟩
    · intro i j hij
      apply hscaled
      change h * aperture i = h * aperture j
      rw [hij]
    · intro j hj
      simpa [hj] using hpos j
  · rintro ⟨⟨hinjective, _hne⟩, hpos⟩
    refine ⟨?_, hpos⟩
    intro i j hij
    apply hinjective
    have hh : h ≠ 0 := by
      intro hh
      simpa [hh] using hpos i
    exact mul_left_cancel₀ hh hij

/-- **Innovation/completion equivalence.** Strict completed dyadic refinement at arbitrary mesh is
equivalent to strict one-prime Szegő geometry of the mesh-scaled packet. -/
theorem xiMobiusContinuousApertureDyadicInnovationGram_posDef_iff_scaled_szegoGram_posDef
    {N : ℕ} (h : ℝ) (aperture : Fin N → ℝ) (p : Nat.Primes) :
    (xiMobiusContinuousApertureDyadicInnovationGram h aperture).PosDef ↔
      (xiMobiusPrimeContinuousApertureSzegoGramMatrix
        (fun j => h * aperture j) p).PosDef := by
  rw [xiMobiusContinuousApertureDyadicInnovationGram_posDef_iff_scaled_injective_pos,
    xiMobiusPrimeContinuousApertureSzegoGramMatrix_posDef_iff_injective_pos]

/-- Determinant form of strict dyadic refinement. -/
theorem det_xiMobiusContinuousApertureDyadicInnovationGram_pos
    {N : ℕ} {h : ℝ} (hh : 0 < h) {aperture : Fin N → ℝ}
    (haperture : Function.Injective aperture) (hpos : ∀ j, 0 < aperture j) :
    0 < (xiMobiusContinuousApertureDyadicInnovationGram h aperture).det :=
  (xiMobiusContinuousApertureDyadicInnovationGram_posDef
    hh haperture hpos).det_pos

end

end RHTower
