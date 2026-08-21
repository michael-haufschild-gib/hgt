/-
# Eigenvectors of a near-diagonal Hamiltonian have flat overlaps with the uniform superposition

A Hermitian operator whose diagonal part has pairwise-separated entries pins each of its
eigenvectors to a single computational basis direction: the residual `(H₀-μ)e = -Ve` forces the
weight outside the one basis vector whose energy is within half a gap of `μ` to be at most
`2δ/γ`.  The uniform superposition has the same modulus on every basis vector, so its overlap with
any eigenvector of the perturbed operator exceeds the flat value `D^{-1/2}` by at most `2δ/γ`, and
the spectral collision of the seed is therefore `O(1/D)` for every Hamiltonian of the tube.

No contour integral, no eigenvector labelling and no Davis--Kahan theorem is used: the argument is a
two-term split of one Parseval identity.

Main results:
* `sum_sq_far_le` — the eigenvector's weight on the far basis vectors.
* `norm_inner_eigenvector_uniform_le` — **the flat-overlap bound**.
* `spectralCollision_le_of_near_diagonal` — **the collision bound `(22)`**.
-/
import GaloisForLFunctions.HTGeometry.SingleOrbitPlateauWindow
import GaloisForLFunctions.HTGeometry.SpectralCollisionCovariance
import GaloisForLFunctions.HTGeometry.GaussianEnsembleCircuitDensity
import GaloisForLFunctions.HTGeometry.CircuitDictionaryCounting

open Matrix Finset
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The basis directions whose energy is at least half a gap away from a given value. -/
def farSet (En : I → ℝ) (gap mu : ℝ) : Finset I :=
  Finset.univ.filter fun k => gap / 2 ≤ |En k - mu|

theorem card_compl_farSet_le_one {En : I → ℝ} {gap : ℝ}
    (hsep : ∀ k l : I, k ≠ l → gap ≤ |En k - En l|) (mu : ℝ) :
    (Finset.univ \ farSet En gap mu).card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr fun k hk l hl => ?_
  by_contra hkl
  simp only [Finset.mem_sdiff, farSet, Finset.mem_filter, Finset.mem_univ, true_and,
    not_le] at hk hl
  have hlt : |En k - En l| < gap := by
    have := abs_sub_abs_le_abs_sub (En k - mu) (En l - mu)
    have htri : |En k - En l| ≤ |En k - mu| + |En l - mu| := by
      have : En k - En l = (En k - mu) - (En l - mu) := by ring
      rw [this]
      exact abs_sub _ _
    linarith [hk, hl]
  exact absurd (hsep k l hkl) (not_le.mpr hlt)

/-- **The eigenvector's weight on the far basis directions.**  A unit eigenvector of a `δ`-nearby
operator carries at most `4δ²/γ²` of its weight on directions whose energy misses the eigenvalue
by half a gap. -/
theorem sum_sq_far_le {En : I → ℝ} {gap : ℝ} (hgap : 0 < gap)
    {H : Matrix I I ℂ} {delta : ℝ} (hdelta : 0 ≤ delta)
    (hnear : ‖H - Matrix.diagonal (fun k => ((En k : ℝ) : ℂ))‖ ≤ delta)
    {e : I → ℂ} (hunit : ‖eucVec e‖ = 1) {mu : ℝ} (heig : H *ᵥ e = (mu : ℂ) • e) :
    ∑ k ∈ farSet En gap mu, ‖e k‖ ^ 2 ≤ (2 * delta / gap) ^ 2 := by
  classical
  have hres : ∀ k, ((H - Matrix.diagonal (fun k => ((En k : ℝ) : ℂ))) *ᵥ e) k
      = ((mu : ℂ) - (En k : ℂ)) * e k := by
    intro k
    rw [Matrix.sub_mulVec, Pi.sub_apply, heig]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal]
    ring
  have hbound : ‖eucVec ((H - Matrix.diagonal (fun k => ((En k : ℝ) : ℂ))) *ᵥ e)‖ ≤ delta := by
    refine le_trans (Matrix.l2_opNorm_mulVec _ (eucVec e)) ?_
    rw [hunit, mul_one]
    exact hnear
  have hsum : ∑ k, ‖((mu : ℂ) - (En k : ℂ)) * e k‖ ^ 2 ≤ delta ^ 2 := by
    have hnormsq := norm_eucVec ((H - Matrix.diagonal (fun k => ((En k : ℝ) : ℂ))) *ᵥ e)
    have hnn : (0 : ℝ) ≤ ∑ k, ‖((H - Matrix.diagonal (fun k => ((En k : ℝ) : ℂ))) *ᵥ e) k‖ ^ 2 := by
      positivity
    have hsq : Real.sqrt (∑ k, ‖((H - Matrix.diagonal (fun k => ((En k : ℝ) : ℂ))) *ᵥ e) k‖ ^ 2)
        ≤ delta := by rw [← hnormsq]; exact hbound
    have := Real.sq_sqrt hnn
    nlinarith [hsq, Real.sqrt_nonneg
      (∑ k, ‖((H - Matrix.diagonal (fun k => ((En k : ℝ) : ℂ))) *ᵥ e) k‖ ^ 2),
      Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => congrArg (fun z : ℂ => ‖z‖ ^ 2)
        (hres k))]
  have hfar : (gap / 2) ^ 2 * ∑ k ∈ farSet En gap mu, ‖e k‖ ^ 2 ≤ delta ^ 2 := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum fun k hk => ?_)
      (le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (farSet En gap mu))
        (fun k _ _ => by positivity)) hsum)
    have hk' : gap / 2 ≤ |En k - mu| := by
      simpa [farSet] using hk
    have hcoef : ‖((mu : ℂ) - (En k : ℂ))‖ = |En k - mu| := by
      rw [show ((mu : ℂ) - (En k : ℂ)) = ((mu - En k : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    rw [norm_mul, mul_pow, hcoef]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact pow_le_pow_left₀ (by positivity) hk' 2
  have hgap2 : (0 : ℝ) < (gap / 2) ^ 2 := by positivity
  rw [div_pow, le_div_iff₀ (by positivity)]
  nlinarith [hfar]


/-- **The flat-overlap bound.**  A unit eigenvector of a `δ`-nearby operator overlaps a vector of
constant modulus `c` by at most `c + 2δ/γ`. -/
theorem norm_inner_eigenvector_uniform_le {En : I → ℝ} {gap : ℝ} (hgap : 0 < gap)
    (hsep : ∀ k l : I, k ≠ l → gap ≤ |En k - En l|)
    {H : Matrix I I ℂ} {delta : ℝ} (hdelta : 0 ≤ delta)
    (hnear : ‖H - Matrix.diagonal (fun k => ((En k : ℝ) : ℂ))‖ ≤ delta)
    {e : I → ℂ} (hunit : ‖eucVec e‖ = 1) {mu : ℝ} (heig : H *ᵥ e = (mu : ℂ) • e)
    {chi : I → ℂ} {c : ℝ} (hc : 0 ≤ c) (hchi : ∀ k, ‖chi k‖ ≤ c)
    (hchiunit : ‖eucVec chi‖ = 1) :
    ‖finiteComplexInner e chi‖ ≤ c + 2 * delta / gap := by
  classical
  have hesq : ∑ k, ‖e k‖ ^ 2 = 1 := by
    have := norm_eucVec e
    rw [hunit] at this
    have hnn : (0 : ℝ) ≤ ∑ k, ‖e k‖ ^ 2 := by positivity
    nlinarith [Real.sq_sqrt hnn, this]
  have hchisq : ∑ k, ‖chi k‖ ^ 2 = 1 := by
    have := norm_eucVec chi
    rw [hchiunit] at this
    have hnn : (0 : ℝ) ≤ ∑ k, ‖chi k‖ ^ 2 := by positivity
    nlinarith [Real.sq_sqrt hnn, this]
  have hek : ∀ k, ‖e k‖ ≤ 1 := by
    intro k
    have hle : ‖e k‖ ^ 2 ≤ ∑ j, ‖e j‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖e j‖ ^ 2) (fun j _ => by positivity)
        (Finset.mem_univ k)
    rw [hesq] at hle
    nlinarith [norm_nonneg (e k)]
  have hsplit : ‖finiteComplexInner e chi‖
      ≤ ∑ k ∈ Finset.univ \ farSet En gap mu, ‖e k‖ * ‖chi k‖
        + ∑ k ∈ farSet En gap mu, ‖e k‖ * ‖chi k‖ := by
    rw [finiteComplexInner]
    refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
    rw [← Finset.sum_sdiff (Finset.subset_univ (farSet En gap mu))]
    refine congrArg₂ (· + ·) ?_ ?_ <;>
      exact Finset.sum_congr rfl fun k _ => by rw [norm_mul, RCLike.norm_conj]
  have hnear' : ∑ k ∈ Finset.univ \ farSet En gap mu, ‖e k‖ * ‖chi k‖ ≤ c := by
    have hbound : ∀ k ∈ Finset.univ \ farSet En gap mu, ‖e k‖ * ‖chi k‖ ≤ c := by
      intro k _
      calc ‖e k‖ * ‖chi k‖ ≤ 1 * c :=
            mul_le_mul (hek k) (hchi k) (norm_nonneg _) zero_le_one
        _ = c := one_mul c
    refine le_trans (Finset.sum_le_card_nsmul _ _ c hbound) ?_
    have hcard := card_compl_farSet_le_one (En := En) (gap := gap) hsep mu
    calc ((Finset.univ \ farSet En gap mu).card : ℕ) • c ≤ (1 : ℕ) • c := by
          refine nsmul_le_nsmul_left hc hcard
      _ = c := one_smul _ _
  have hfar' : ∑ k ∈ farSet En gap mu, ‖e k‖ * ‖chi k‖ ≤ 2 * delta / gap := by
    have hcs := sum_mul_sq_le_sq_mul_sq (farSet En gap mu) (fun k => ‖e k‖) (fun k => ‖chi k‖)
    have hA := sum_sq_far_le (En := En) (gap := gap) hgap hdelta hnear hunit heig
    have hB : ∑ k ∈ farSet En gap mu, ‖chi k‖ ^ 2 ≤ 1 := by
      rw [← hchisq]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun k _ _ => by positivity)
    have hquot : (0 : ℝ) ≤ 2 * delta / gap := by positivity
    have hAnn : (0 : ℝ) ≤ ∑ k ∈ farSet En gap mu, ‖e k‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hBnn : (0 : ℝ) ≤ ∑ k ∈ farSet En gap mu, ‖chi k‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hprod : (∑ k ∈ farSet En gap mu, ‖e k‖ * ‖chi k‖) ^ 2
        ≤ (2 * delta / gap) ^ 2 := by
      refine le_trans hcs ?_
      nlinarith [hA, hB, hAnn, hBnn]
    exact le_of_pow_le_pow_left₀ (by norm_num) hquot hprod
  linarith [hsplit, hnear', hfar']

/-- **`(22)`.**  On the tube around a separated diagonal carrier the spectral collision of a
constant-modulus seed is at most the square of the flat overlap bound. -/
theorem spectralCollision_le_of_near_diagonal {En : I → ℝ} {gap : ℝ} (hgap : 0 < gap)
    (hsep : ∀ k l : I, k ≠ l → gap ≤ |En k - En l|)
    {H : Matrix I I ℂ} {delta : ℝ} (hdelta : 0 ≤ delta)
    (hnear : ‖H - Matrix.diagonal (fun k => ((En k : ℝ) : ℂ))‖ ≤ delta)
    {ebasis : I → I → ℂ} {lam : I → ℝ} (heb : IsOrthoEigenBasis H ebasis lam)
    {chi : I → ℂ} {c : ℝ} (hc : 0 ≤ c) (hchi : ∀ k, ‖chi k‖ ≤ c)
    (hchiunit : ‖eucVec chi‖ = 1) :
    spectralCollision ebasis chi ≤ (c + 2 * delta / gap) ^ 2 := by
  classical
  have hunit : ∀ j, ‖eucVec (ebasis j)‖ = 1 := by
    intro j
    have h := heb.orth j j
    rw [if_pos rfl] at h
    exact norm_eucVec_eq_one h
  have hparseval : ∑ j, ‖finiteComplexInner (ebasis j) chi‖ ^ 2 = 1 := by
    have hpar := parseval_finiteComplexInner heb chi chi
    have hchi1 : finiteComplexInner chi chi = 1 := by
      have := norm_eucVec chi
      rw [hchiunit] at this
      have hnn : (0 : ℝ) ≤ ∑ k, ‖chi k‖ ^ 2 := by positivity
      have hsum : ∑ k, ‖chi k‖ ^ 2 = 1 := by nlinarith [Real.sq_sqrt hnn, this]
      rw [finiteComplexInner_self_eq_sum_normSq, hsum]
      norm_num
    rw [hchi1] at hpar
    have : (1 : ℂ) = ((∑ j, ‖finiteComplexInner (ebasis j) chi‖ ^ 2 : ℝ) : ℂ) := by
      rw [hpar, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.sq_norm]
      exact (Complex.normSq_eq_conj_mul_self).symm
    exact_mod_cast this.symm
  have hbound : ∀ j, ‖finiteComplexInner (ebasis j) chi‖ ^ 2 ≤ (c + 2 * delta / gap) ^ 2 := by
    intro j
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    exact norm_inner_eigenvector_uniform_le hgap hsep hdelta hnear (hunit j) (heb.eigen j)
      hc hchi hchiunit
  calc spectralCollision ebasis chi
      = ∑ j, (‖finiteComplexInner (ebasis j) chi‖ ^ 2) ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [finitePureStateFidelity]
    _ ≤ ∑ j, (c + 2 * delta / gap) ^ 2 * ‖finiteComplexInner (ebasis j) chi‖ ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        have := hbound j
        nlinarith [sq_nonneg ‖finiteComplexInner (ebasis j) chi‖]
    _ = (c + 2 * delta / gap) ^ 2 := by
        rw [← Finset.mul_sum, hparseval, mul_one]

end GaloisForLFunctions.HTGeometry

end
