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
          (∑ n ∈ t, (b n : ℂ) * X n ω)‖ ^ (2 : ℕ) ∂steinhausMeasure =
      ∑ k ∈ prodSupport s t, dpolyConv a b s t k ^ (2 : ℕ) := by
  have hsne : ∀ n ∈ s, n ≠ 0 :=
    fun n hn => Nat.one_le_iff_ne_zero.mp (hs n hn)
  have htne : ∀ n ∈ t, n ≠ 0 :=
    fun n hn => Nat.one_le_iff_ne_zero.mp (ht n hn)
  have hsupport : ∀ k ∈ prodSupport s t, 1 ≤ k :=
    fun k hk => one_le_of_mem_prodSupport hs ht hk
  have hrw : ∀ ω : Omega,
      ‖(∑ n ∈ s, (a n : ℂ) * X n ω) *
          (∑ n ∈ t, (b n : ℂ) * X n ω)‖ ^ (2 : ℕ) =
        ‖∑ k ∈ prodSupport s t,
          (dpolyConv a b s t k : ℂ) * X k ω‖ ^ (2 : ℕ) := by
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
    (∫ τ in A..(A + U), ‖dpoly a s τ * dpoly b t τ‖ ^ (2 : ℕ)) / U =
      (∑ k ∈ prodSupport s t, dpolyConv a b s t k ^ (2 : ℕ)) +
        ∑ m ∈ prodSupport s t, ∑ n ∈ (prodSupport s t).erase m,
          dpolyConv a b s t m * dpolyConv a b s t n *
            (cosInt (Real.log n - Real.log m) A U / U) := by
  have hsne : ∀ n ∈ s, n ≠ 0 :=
    fun n hn => Nat.one_le_iff_ne_zero.mp (hs n hn)
  have htne : ∀ n ∈ t, n ≠ 0 :=
    fun n hn => Nat.one_le_iff_ne_zero.mp (ht n hn)
  have hrw : ∀ τ : ℝ,
      ‖dpoly a s τ * dpoly b t τ‖ ^ (2 : ℕ) =
        ‖dpoly (dpolyConv a b s t) (prodSupport s t) τ‖ ^ (2 : ℕ) := by
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
    |(∫ τ in A..(A + U), ‖dpoly a s τ * dpoly b t τ‖ ^ (2 : ℕ)) / U -
        ∫ ω,
          ‖(∑ n ∈ s, (a n : ℂ) * X n ω) *
            (∑ n ∈ t, (b n : ℂ) * X n ω)‖ ^ (2 : ℕ) ∂steinhausMeasure| ≤
      dpolyWindowOffDiagonalEnergy
        (dpolyConv a b s t) (prodSupport s t) U := by
  have hsne : ∀ n ∈ s, n ≠ 0 :=
    fun n hn => Nat.one_le_iff_ne_zero.mp (hs n hn)
  have htne : ∀ n ∈ t, n ≠ 0 :=
    fun n hn => Nat.one_le_iff_ne_zero.mp (ht n hn)
  have hsupport : ∀ k ∈ prodSupport s t, 1 ≤ k :=
    fun k hk => one_le_of_mem_prodSupport hs ht hk
  have hrw : ∀ τ : ℝ,
      ‖dpoly a s τ * dpoly b t τ‖ ^ (2 : ℕ) =
        ‖dpoly (dpolyConv a b s t) (prodSupport s t) τ‖ ^ (2 : ℕ) := by
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
    (∫ τ in (-T)..T, ‖dpoly a s τ * dpoly b t τ‖ ^ (2 : ℕ)) / (2 * T) =
      (∑ k ∈ prodSupport s t, dpolyConv a b s t k ^ (2 : ℕ)) +
        ∑ m ∈ prodSupport s t, ∑ n ∈ (prodSupport s t).erase m,
          dpolyConv a b s t m * dpolyConv a b s t n *
            Real.sinc ((Real.log n - Real.log m) * T) := by
  have hsne : ∀ n ∈ s, n ≠ 0 :=
    fun n hn => Nat.one_le_iff_ne_zero.mp (hs n hn)
  have htne : ∀ n ∈ t, n ≠ 0 :=
    fun n hn => Nat.one_le_iff_ne_zero.mp (ht n hn)
  have hrw : ∀ τ : ℝ,
      ‖dpoly a s τ * dpoly b t τ‖ ^ (2 : ℕ) =
        ‖dpoly (dpolyConv a b s t) (prodSupport s t) τ‖ ^ (2 : ℕ) := by
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
    |(∫ τ in (-T)..T, ‖dpoly a s τ * dpoly b t τ‖ ^ (2 : ℕ)) / (2 * T) -
        ∫ ω,
          ‖(∑ n ∈ s, (a n : ℂ) * X n ω) *
            (∑ n ∈ t, (b n : ℂ) * X n ω)‖ ^ (2 : ℕ) ∂steinhausMeasure| ≤
      dpolySincOffDiagonalEnergy
        (dpolyConv a b s t) (prodSupport s t) T := by
  have hsne : ∀ n ∈ s, n ≠ 0 :=
    fun n hn => Nat.one_le_iff_ne_zero.mp (hs n hn)
  have htne : ∀ n ∈ t, n ≠ 0 :=
    fun n hn => Nat.one_le_iff_ne_zero.mp (ht n hn)
  have hsupport : ∀ k ∈ prodSupport s t, 1 ≤ k :=
    fun k hk => one_le_of_mem_prodSupport hs ht hk
  have hrw : ∀ τ : ℝ,
      ‖dpoly a s τ * dpoly b t τ‖ ^ (2 : ℕ) =
        ‖dpoly (dpolyConv a b s t) (prodSupport s t) τ‖ ^ (2 : ℕ) := by
    intro τ
    rw [dpoly_mul a b s t hsne htne τ]
  rw [mixedSteinhausSecondMoment_eq_convolutionDiagonal a b s t hs ht,
    intervalIntegral.integral_congr (fun τ _ => hrw τ)]
  exact secondMoment_symmetric_sinc_error_le
    (dpolyConv a b s t) (prodSupport s t) T hT hsupport

end

end RHTower

namespace RHTower

open SteinhausModel

noncomputable section

/-! ### The near-collision energies vanish at large observation scale -/

private theorem tendsto_min_one_const_div (c : ℝ) (hc : 0 < c) (d : ℝ) (hd : 0 < d) :
    Tendsto (fun U : ℝ => min 1 (c / (U * d))) atTop (nhds 0) := by
  have hdiv : Tendsto (fun U : ℝ => c / (U * d)) atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds
      (Filter.Tendsto.atTop_mul_const hd tendsto_id)
  refine squeeze_zero' ?_ ?_ hdiv
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with U hU
    exact le_min_iff.mpr ⟨by norm_num, by positivity⟩
  · filter_upwards with U
    exact min_le_right _ _

/-- **The windowed near-collision energy vanishes at large window length.** -/
theorem tendsto_dpolyWindowOffDiagonalEnergy (a : ℕ → ℝ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n) :
    Tendsto (fun U : ℝ => dpolyWindowOffDiagonalEnergy a s U) atTop (nhds 0) := by
  have hterm : ∀ m ∈ s, Tendsto (fun U : ℝ => ∑ n ∈ s.erase m,
      |a m * a n| * min 1 (2 / (U * |Real.log n - Real.log m|))) atTop (nhds 0) := by
    intro m hm
    have hinner : ∀ n ∈ s.erase m, Tendsto (fun U : ℝ =>
        |a m * a n| * min 1 (2 / (U * |Real.log n - Real.log m|))) atTop (nhds 0) := by
      intro n hn
      rw [Finset.mem_erase] at hn
      have hlog : Real.log n - Real.log m ≠ 0 :=
        log_diff_ne_zero m n (hs m hm) (hs n hn.2) hn.1
      have habs : 0 < |Real.log n - Real.log m| := abs_pos.mpr hlog
      have h := tendsto_min_one_const_div 2 (by norm_num) _ habs
      have := h.const_mul |a m * a n|
      simpa using this
    have := tendsto_finsetSum (s.erase m) hinner
    simpa using this
  have := tendsto_finsetSum s hterm
  simpa [dpolyWindowOffDiagonalEnergy] using this

/-- **The sinc near-collision energy vanishes at large observation time.** -/
theorem tendsto_dpolySincOffDiagonalEnergy (a : ℕ → ℝ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n) :
    Tendsto (fun T : ℝ => dpolySincOffDiagonalEnergy a s T) atTop (nhds 0) := by
  have hterm : ∀ m ∈ s, Tendsto (fun T : ℝ => ∑ n ∈ s.erase m,
      |a m * a n| * min 1 (1 / (T * |Real.log n - Real.log m|))) atTop (nhds 0) := by
    intro m hm
    have hinner : ∀ n ∈ s.erase m, Tendsto (fun T : ℝ =>
        |a m * a n| * min 1 (1 / (T * |Real.log n - Real.log m|))) atTop (nhds 0) := by
      intro n hn
      rw [Finset.mem_erase] at hn
      have hlog : Real.log n - Real.log m ≠ 0 :=
        log_diff_ne_zero m n (hs m hm) (hs n hn.2) hn.1
      have habs : 0 < |Real.log n - Real.log m| := abs_pos.mpr hlog
      have h := tendsto_min_one_const_div 1 (by norm_num) _ habs
      have := h.const_mul |a m * a n|
      simpa using this
    have := tendsto_finsetSum (s.erase m) hinner
    simpa using this
  have := tendsto_finsetSum s hterm
  simpa [dpolySincOffDiagonalEnergy] using this

/-! ### The seam limits are discharged by the finite-window laws -/

/-- **Shifted-window seam limit.**  For every fixed window location the normalized mixed second
moment converges to the independent Steinhaus seam moment.  This is the finite-window law of this
file plus the vanishing of its explicit error envelope; no separate limit argument is used. -/
theorem tendsto_mixedSecondMoment_window_steinhaus
    (a b : ℕ → ℝ) (s t : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n) (ht : ∀ n ∈ t, 1 ≤ n) (A : ℝ) :
    Tendsto (fun U : ℝ => (∫ τ in A..(A + U), ‖dpoly a s τ * dpoly b t τ‖ ^ (2 : ℕ)) / U) atTop
      (nhds (∫ ω, ‖(∑ n ∈ s, (a n : ℂ) * X n ω) *
        (∑ n ∈ t, (b n : ℂ) * X n ω)‖ ^ (2 : ℕ) ∂steinhausMeasure)) := by
  have hsupport : ∀ k ∈ prodSupport s t, 1 ≤ k :=
    fun k hk => one_le_of_mem_prodSupport hs ht hk
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_
    (tendsto_dpolyWindowOffDiagonalEnergy (dpolyConv a b s t) (prodSupport s t) hsupport)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with U hU
  rw [Real.norm_eq_abs]
  exact mixedSecondMoment_window_independence_error_le a b s t hs ht A U hU

/-- **Symmetric seam limit.**  The symmetric normalized mixed second moment converges to the same
independent Steinhaus seam moment. -/
theorem tendsto_mixedSecondMoment_symmetric_steinhaus
    (a b : ℕ → ℝ) (s t : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n) (ht : ∀ n ∈ t, 1 ≤ n) :
    Tendsto (fun T : ℝ => (∫ τ in (-T)..T, ‖dpoly a s τ * dpoly b t τ‖ ^ (2 : ℕ)) / (2 * T)) atTop
      (nhds (∫ ω, ‖(∑ n ∈ s, (a n : ℂ) * X n ω) *
        (∑ n ∈ t, (b n : ℂ) * X n ω)‖ ^ (2 : ℕ) ∂steinhausMeasure)) := by
  have hsupport : ∀ k ∈ prodSupport s t, 1 ≤ k :=
    fun k hk => one_le_of_mem_prodSupport hs ht hk
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_
    (tendsto_dpolySincOffDiagonalEnergy (dpolyConv a b s t) (prodSupport s t) hsupport)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [Real.norm_eq_abs]
  exact mixedSecondMoment_symmetric_sinc_error_le a b s t hs ht T hT

/-- The corpus seam limit is the window seam limit at the origin: the infinite-time law of
`SeamMoments` is discharged by the exact finite-window law. -/
theorem tendsto_mixedSecondMoment_average_steinhaus_of_window
    (a b : ℕ → ℝ) (s t : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n) (ht : ∀ n ∈ t, 1 ≤ n) :
    Tendsto (fun U : ℝ => (∫ τ in (0 : ℝ)..U, ‖dpoly a s τ * dpoly b t τ‖ ^ (2 : ℕ)) / U) atTop
      (nhds (∫ ω, ‖(∑ n ∈ s, (a n : ℂ) * X n ω) *
        (∑ n ∈ t, (b n : ℂ) * X n ω)‖ ^ (2 : ℕ) ∂steinhausMeasure)) := by
  have h := tendsto_mixedSecondMoment_window_steinhaus a b s t hs ht 0
  simpa using h

end

end RHTower
