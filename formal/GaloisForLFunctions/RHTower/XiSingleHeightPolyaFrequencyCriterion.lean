import GaloisForLFunctions.RHTower.XiReciprocalSliceCriterion
import GaloisForLFunctions.RHTower.XiReciprocalCentreUnconditionalRung
import GaloisForLFunctions.RHTower.XiReciprocalSlicePolyaFrequency
import GaloisForLFunctions.RHTower.XiHorizontalSlicePolyaFrequencyCriterion
import GaloisForLFunctions.HTGeometry.JacobiComplementaryMinor

/-!
# RH as total positivity of one coefficient sequence

**Centre** (`riemannHypothesis_iff_forall_pfSeq_centre`).  RH holds iff the Taylor coefficients
`a_k` of `ξ(½ + x) = Σ a_k x^{2k}` form a Pólya frequency sequence of every order.

**Any single height** (`riemannHypothesis_iff_forall_pfSeq_xiSliceCoeff_at`).  For every `t` with
`Ξ(t) ≠ 0`, RH holds iff the slice coefficients `c_{2k}(t)` of `|ξ(½ + x + it)|²` form a Pólya
frequency sequence of every order.  The earlier criterion
`riemannHypothesis_iff_forall_pfSeq_xiSliceCoeff` quantifies over all heights.

* `⟹`: under RH every zero lies in every cone, so the cone law gives `PF_k` for every `k`.
* `⟸`: Jacobi's complementary minor theorem (`toeplitzMinor_reciprocal_nonneg_of_pfSeq`) passes
  `PF_∞` to the reciprocal coefficients.  Reciprocal total positivity then locates every zero on
  the real line (`riemannHypothesis_of_reciprocalTP_xiCentreLift`,
  `riemannHypothesis_of_reciprocalTP_xiSliceLift`).

**Unconditional window** (`toeplitzMinor_evenRecipCoeff_XiC_nonneg_of_window`).  Let `β` be the
coefficients of `1/Ξ(σ)` in `σ²`.  Every Toeplitz minor of `β` whose complement in some window
`{0, …, N−1}` has at most `37` elements is nonnegative.  This follows from the computer-free `PF_37`
of the centre coefficients.  It contains the 38-coefficient rung and every minor of `β` within
`37` of full size in its window.
-/

open Complex Filter Topology Metric
open scoped ComplexOrder Nat
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Reciprocal total positivity of an even-square lift from `PF_∞` of the even reciprocal
coefficients. -/
theorem reciprocalTP_evenSquareLift_of_forall_pfSeq {u : ℂ → ℂ} (hu : Differentiable ℂ u)
    (heven : ∀ z, u (-z) = u z) (h0 : u 0 ≠ 0)
    (hreal : ∀ m, (((2 * m).factorial : ℂ))⁻¹ * iteratedDeriv (2 * m) (fun σ => (u σ)⁻¹) 0 =
      ((evenRecipCoeff u m : ℝ) : ℂ))
    (hpf : ∀ k, PFSeq k (evenRecipCoeff u)) :
    ReciprocalTP (fun y => evenSquareLift u (-y)) := by
  set F : ℂ → ℂ := fun y => evenSquareLift u (-y) with hF
  have hdiff : Differentiable ℂ F := (differentiable_evenSquareLift hu).comp differentiable_neg
  have hsq : ∀ σ : ℂ, F (-(σ ^ 2)) = u σ := by
    intro σ
    simp only [hF, neg_neg]
    exact evenSquareLift_sq hu heven σ
  have hF0 : F 0 ≠ 0 := by
    have h := hsq 0
    rw [show -((0 : ℂ) ^ 2) = 0 by ring] at h
    rw [h]
    exact h0
  set g : ℂ → ℂ := recipNeg F with hg
  have hgsq : (fun σ => g (σ ^ 2)) = fun σ => (u σ)⁻¹ := by
    funext σ
    simp only [hg, recipNeg]
    rw [hsq]
  have hgan : AnalyticAt ℂ g 0 := by
    have hne : F (-0) ≠ 0 := by simpa using hF0
    exact ((hdiff.comp differentiable_neg).analyticAt 0).inv hne
  have hcoef : ∀ n, ((n ! : ℂ))⁻¹ * iteratedDeriv n g 0 = ((evenRecipCoeff u n : ℝ) : ℂ) := by
    intro n
    rw [← iteratedDeriv_comp_sq hgan n, hgsq]
    exact hreal n
  have hnn : ∀ n, 0 ≤ evenRecipCoeff u n := by
    intro n
    have := hpf 1 1 le_rfl (fun _ => 0) (fun _ => n) (Subsingleton.strictMono _)
      (Subsingleton.strictMono _)
    simpa [toeplitzMinor, Matrix.det_unique, zext_natCast] using this
  refine ⟨hdiff, hF0, fun n => ?_, ?_⟩
  · have hD : iteratedDeriv n g 0 = ((n ! : ℂ)) * ((evenRecipCoeff u n : ℝ) : ℂ) := by
      rw [← hcoef n]
      have : (n ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
      field_simp
    show 0 ≤ iteratedDeriv n g 0
    rw [hD]
    exact mul_nonneg (Nat.cast_nonneg _) (Complex.zero_le_real.mpr (hnn n))
  · have heq : recipCoeff F = evenRecipCoeff u := by
      funext n
      unfold recipCoeff
      rw [← hg, hcoef n, Complex.ofReal_re]
    rw [heq]
    intro m i₀ j hj
    exact hpf m m le_rfl _ j (fun a b hab => by simpa using hab) hj

/-- **RH is `PF_∞` of the centre coefficients.** -/
theorem riemannHypothesis_iff_forall_pfSeq_centre :
    RiemannHypothesis ↔ ∀ k, PFSeq k (evenTaylorRe (fun x => xi (1 / 2 + x))) := by
  constructor
  · intro hRH k
    have h1 : ∀ k, 1 ≤ k → PFSeq k (evenTaylorRe (fun x => xi (1 / 2 + x))) := by
      intro k hk
      refine xi_centre_pfSeq_of_cone hk fun q => ?_
      rw [xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q, sub_self]
      have hc : Real.cos (Real.pi / ((k : ℝ) + 1)) ≤ 1 := Real.cos_le_one _
      nlinarith [sq_nonneg ((q.1 : ℂ).im)]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact (h1 1 le_rfl).of_le (Nat.zero_le 1)
    · exact h1 k hk
  · intro h
    have hβ := pfSeq_reciprocal_of_forall_pfSeq h evenTaylorRe_xi_half_zero_pos
      sum_centre_mul_evenRecipCoeff_XiC
    have hXi0 : XiC 0 ≠ 0 := by
      have : XiC 0 = xi (((1 / 2 : ℝ)) : ℂ) := by simp [XiC]
      rw [this]
      exact xi_ne_zero_of_real _
    exact riemannHypothesis_of_reciprocalTP_xiCentreLift
      (reciprocalTP_evenSquareLift_of_forall_pfSeq XiC_differentiable XiC_even hXi0
        factorial_inv_mul_iteratedDeriv_inv_XiC_even hβ)

/-- **RH is `PF_∞` of the slice coefficients at any single height off the zeros.** -/
theorem riemannHypothesis_iff_forall_pfSeq_xiSliceCoeff_at {t : ℝ} (h0 : XiC t ≠ 0) :
    RiemannHypothesis ↔ ∀ k, PFSeq k (fun n => (xiSliceCoeff t (2 * n)).re) := by
  constructor
  · intro hRH k
    exact riemannHypothesis_iff_forall_pfSeq_xiSliceCoeff.mp hRH t k
  · intro h
    have hreal : ∀ m, (((2 * m).factorial : ℂ))⁻¹ *
        iteratedDeriv (2 * m) (fun σ => (xiHorizontalPair t σ)⁻¹) 0 =
          ((evenRecipCoeff (xiHorizontalPair t) m : ℝ) : ℂ) := by
      intro m
      apply Complex.ext
      · simp [evenRecipCoeff]
      · rw [Complex.mul_im, im_iteratedDeriv_inv_xiHorizontalPair, mul_zero, zero_add,
          Complex.ofReal_im]
        have : ((((2 * m).factorial : ℂ))⁻¹).im = 0 := by
          rw [show (((2 * m).factorial : ℂ))⁻¹ = ((((2 * m).factorial : ℝ))⁻¹ : ℝ) by
            push_cast; rfl]
          exact Complex.ofReal_im _
        rw [this, zero_mul]
    have hβ := pfSeq_reciprocal_of_forall_pfSeq (β := evenRecipCoeff (xiHorizontalPair t)) h
      (xiSliceCoeff_zero_re_pos h0) (sum_xiSliceCoeff_mul_inv_even h0)
    have hh0 : xiHorizontalPair t 0 ≠ 0 := by
      unfold xiHorizontalPair
      simpa using mul_ne_zero h0 h0
    exact riemannHypothesis_of_reciprocalTP_xiSliceLift
      (reciprocalTP_evenSquareLift_of_forall_pfSeq (differentiable_xiHorizontalPair t)
        (xiHorizontalPair_neg' t) hh0 hreal hβ)

/-- **The computer-free window of the centre criterion.**  Every Toeplitz minor of the
reciprocal centre coefficients `β = evenRecipCoeff XiC`, with indices in a window
`{0, …, N−1}` whose complement has at most `37` elements, is nonnegative. -/
theorem toeplitzMinor_evenRecipCoeff_XiC_nonneg_of_window {N m : ℕ} {i j : Fin m → ℕ}
    (hi : StrictMono i) (hj : StrictMono j) (hiN : ∀ r, i r < N) (hjN : ∀ c, j c < N)
    (hNm : N - m ≤ 37) : 0 ≤ toeplitzMinor (evenRecipCoeff XiC) m i j :=
  toeplitzMinor_reciprocal_nonneg_of_pfSeq xi_centre_pfSeq_thirtySeven
    evenTaylorRe_xi_half_zero_pos sum_centre_mul_evenRecipCoeff_XiC hi hj hiN hjN hNm

end

end RHTower
