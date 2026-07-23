import GaloisForLFunctions.RHTower.DirichletPolynomialSincEnergy
import GaloisForLFunctions.RHTower.SeamMoments

/-!
# Exact finite-window seam laws

The mixed second moment of two finite Dirichlet carriers was previously identified only after an
infinite-time limit.  Multiplicativity turns both the deterministic product and its independent
Steinhaus model into the same convolution carrier.  The finite-window sinc theory therefore gives
an exact seam kernel at every observation scale and an explicit near-collision error, without
passing to a limit.
-/

open Complex MeasureTheory intervalIntegral Filter Topology Finset
open scoped Classical

namespace RHTower

open SteinhausModel

noncomputable section

/-- The independent mixed seam moment is exactly the diagonal mass of the multiplicative
convolution coefficients. -/
theorem mixedSteinhausSecondMoment_eq_convolutionDiagonal
    (a b : ℕ → ℝ) (s t : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n) (ht : ∀ n ∈ t, 1 ≤ n) :
    ∫ ω,
        ‖(∑ n ∈ s, (a n : ℂ) * X n ω) *
          (∑ n ∈ t, (b n : ℂ) * X n ω)‖ ^ 2 ∂steinhausMeasure =
      ∑ k ∈ prodSupport s t, dpolyConv a b s t k ^ 2 := by
  have hsne : ∀ n ∈ s, n ≠ 0 :=
    fun n hn => Nat.one_le_iff_ne_zero.mp (hs n hn)
  have htne : ∀ n ∈ t, n ≠ 0 :=
    fun n hn => Nat.one_le_iff_ne_zero.mp (ht n hn)
  have hsupport : ∀ k ∈ prodSupport s t, 1 ≤ k :=
    fun k hk => one_le_of_mem_prodSupport hs ht hk
  have hrw : ∀ ω : Omega,
      ‖(∑ n ∈ s, (a n : ℂ) * X n ω) *
          (∑ n ∈ t, (b n : ℂ) * X n ω)‖ ^ 2 =
        ‖∑ k ∈ prodSupport s t,
          (dpolyConv a b s t k : ℂ) * X k ω‖ ^ 2 := by
    intro ω
    rw [model_mul a b s t hsne htne ω]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hrw)]
  exact integral_normSq_dpoly (dpolyConv a b s t) (prodSupport s t)
    (fun k hk => Nat.one_le_iff_ne_zero.mp (hsupport k hk))

/-- **Exact shifted-window seam kernel.**  Every finite mixed second moment is the independent
convolution diagonal plus the finite-window Fourier transform of its multiplicative collision
spectrum. -/
theorem mixedSecondMoment_window_kernel
    (a b : ℕ → ℝ) (s t : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n) (ht : ∀ n ∈ t, 1 ≤ n)
    (A U : ℝ) (hU : 0 < U) :
    (∫ τ in A..(A + U), ‖dpoly a s τ * dpoly b t τ‖ ^ 2) / U =
      (∑ k ∈ prodSupport s t, dpolyConv a b s t k ^ 2) +
        ∑ m ∈ prodSupport s t, ∑ n ∈ (prodSupport s t).erase m,
          dpolyConv a b s t m * dpolyConv a b s t n *
            (cosInt (Real.log n - Real.log m) A U / U) := by
  have hsne : ∀ n ∈ s, n ≠ 0 :=
    fun n hn => Nat.one_le_iff_ne_zero.mp (hs n hn)
  have htne : ∀ n ∈ t, n ≠ 0 :=
    fun n hn => Nat.one_le_iff_ne_zero.mp (ht n hn)
  have hrw : ∀ τ : ℝ,
      ‖dpoly a s τ * dpoly b t τ‖ ^ 2 =
        ‖dpoly (dpolyConv a b s t) (prodSupport s t) τ‖ ^ 2 := by
    intro τ
    rw [dpoly_mul a b s t hsne htne τ]
  rw [intervalIntegral.integral_congr (fun τ _ => hrw τ)]
  exact secondMoment_window_kernel
    (dpolyConv a b s t) (prodSupport s t) A U hU

/-- **Finite-window seam universality.**  On every shifted observation window, the complete
deterministic mixed-moment error relative to the independent seam model is bounded by one explicit
near-collision energy of the convolution coefficients.  Window location affects the exact kernel
but not this envelope. -/
theorem mixedSecondMoment_window_independence_error_le
    (a b : ℕ → ℝ) (s t : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n) (ht : ∀ n ∈ t, 1 ≤ n)
    (A U : ℝ) (hU : 0 < U) :
    |(∫ τ in A..(A + U), ‖dpoly a s τ * dpoly b t τ‖ ^ 2) / U -
        ∫ ω,
          ‖(∑ n ∈ s, (a n : ℂ) * X n ω) *
            (∑ n ∈ t, (b n : ℂ) * X n ω)‖ ^ 2 ∂steinhausMeasure| ≤
      dpolyWindowOffDiagonalEnergy
        (dpolyConv a b s t) (prodSupport s t) U := by
  have hsne : ∀ n ∈ s, n ≠ 0 :=
    fun n hn => Nat.one_le_iff_ne_zero.mp (hs n hn)
  have htne : ∀ n ∈ t, n ≠ 0 :=
    fun n hn => Nat.one_le_iff_ne_zero.mp (ht n hn)
  have hsupport : ∀ k ∈ prodSupport s t, 1 ≤ k :=
    fun k hk => one_le_of_mem_prodSupport hs ht hk
  have hrw : ∀ τ : ℝ,
      ‖dpoly a s τ * dpoly b t τ‖ ^ 2 =
        ‖dpoly (dpolyConv a b s t) (prodSupport s t) τ‖ ^ 2 := by
    intro τ
    rw [dpoly_mul a b s t hsne htne τ]
  rw [mixedSteinhausSecondMoment_eq_convolutionDiagonal a b s t hs ht,
    intervalIntegral.integral_congr (fun τ _ => hrw τ)]
  exact secondMoment_window_independence_error_le
    (dpolyConv a b s t) (prodSupport s t) A U hU hsupport

/-- **Exact symmetric seam sinc law.**  On `[-T,T]`, the finite mixed second moment is the
independent convolution diagonal plus its sinc-weighted multiplicative collision spectrum. -/
theorem mixedSecondMoment_symmetric_sinc
    (a b : ℕ → ℝ) (s t : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n) (ht : ∀ n ∈ t, 1 ≤ n)
    (T : ℝ) (hT : 0 < T) :
    (∫ τ in (-T)..T, ‖dpoly a s τ * dpoly b t τ‖ ^ 2) / (2 * T) =
      (∑ k ∈ prodSupport s t, dpolyConv a b s t k ^ 2) +
        ∑ m ∈ prodSupport s t, ∑ n ∈ (prodSupport s t).erase m,
          dpolyConv a b s t m * dpolyConv a b s t n *
            Real.sinc ((Real.log n - Real.log m) * T) := by
  have hsne : ∀ n ∈ s, n ≠ 0 :=
    fun n hn => Nat.one_le_iff_ne_zero.mp (hs n hn)
  have htne : ∀ n ∈ t, n ≠ 0 :=
    fun n hn => Nat.one_le_iff_ne_zero.mp (ht n hn)
  have hrw : ∀ τ : ℝ,
      ‖dpoly a s τ * dpoly b t τ‖ ^ 2 =
        ‖dpoly (dpolyConv a b s t) (prodSupport s t) τ‖ ^ 2 := by
    intro τ
    rw [dpoly_mul a b s t hsne htne τ]
  rw [intervalIntegral.integral_congr (fun τ _ => hrw τ)]
  exact secondMoment_symmetric_sinc
    (dpolyConv a b s t) (prodSupport s t) T hT

/-- Symmetric finite-time seam error is bounded by the convolution sinc near-collision energy. -/
theorem mixedSecondMoment_symmetric_sinc_error_le
    (a b : ℕ → ℝ) (s t : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n) (ht : ∀ n ∈ t, 1 ≤ n)
    (T : ℝ) (hT : 0 < T) :
    |(∫ τ in (-T)..T, ‖dpoly a s τ * dpoly b t τ‖ ^ 2) / (2 * T) -
        ∫ ω,
          ‖(∑ n ∈ s, (a n : ℂ) * X n ω) *
            (∑ n ∈ t, (b n : ℂ) * X n ω)‖ ^ 2 ∂steinhausMeasure| ≤
      dpolySincOffDiagonalEnergy
        (dpolyConv a b s t) (prodSupport s t) T := by
  have hsne : ∀ n ∈ s, n ≠ 0 :=
    fun n hn => Nat.one_le_iff_ne_zero.mp (hs n hn)
  have htne : ∀ n ∈ t, n ≠ 0 :=
    fun n hn => Nat.one_le_iff_ne_zero.mp (ht n hn)
  have hsupport : ∀ k ∈ prodSupport s t, 1 ≤ k :=
    fun k hk => one_le_of_mem_prodSupport hs ht hk
  have hrw : ∀ τ : ℝ,
      ‖dpoly a s τ * dpoly b t τ‖ ^ 2 =
        ‖dpoly (dpolyConv a b s t) (prodSupport s t) τ‖ ^ 2 := by
    intro τ
    rw [dpoly_mul a b s t hsne htne τ]
  rw [mixedSteinhausSecondMoment_eq_convolutionDiagonal a b s t hs ht,
    intervalIntegral.integral_congr (fun τ _ => hrw τ)]
  exact secondMoment_symmetric_sinc_error_le
    (dpolyConv a b s t) (prodSupport s t) T hT hsupport

end

end RHTower
