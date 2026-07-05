/-
Higher Bohr moments via the convolution square: fourth moment = second moment of `F²`.

The second-moment Bohr transfer (`tendsto_secondMoment_average_steinhaus`) equates the
vertical time average of `‖F‖²` with the Steinhaus-model second moment. Every even moment
reduces to it: `‖F‖^{2k} = ‖F^k‖²`, and a power of a Dirichlet polynomial is again a
Dirichlet polynomial with the (multiplicative) convolution coefficients. This file builds
the degree-two rung — the fourth moment.

* `convSq a s k = ∑_{mn=k, m,n∈s} aₘ aₙ`, `sqSupport s = {mn : m,n ∈ s}`.
* `dpoly_sq` — on the line, `F(τ)² = dpoly (convSq a s) (sqSupport s) τ`, via
  `e^{-iτ log m}·e^{-iτ log n} = e^{-iτ log(mn)}` grouped fiberwise over the product `mn`.
* `model_sq` — the same for the model, via multiplicativity `X_{mn} = X_m X_n`.
* `tendsto_fourthMoment_average` / `integral_normSq_sq_dpoly` — both `‖F‖⁴` averages equal
  the convolution diagonal `∑ (convSq)²`, by applying the second-moment machinery to `F²`.
* `tendsto_fourthMoment_average_steinhaus` — the degree-two Bohr identity: the time average
  of `‖F‖⁴` equals the model fourth moment `E‖∑ aₙ Xₙ‖⁴`. Squaring commutes with the
  line ↔ character-model correspondence.
-/
import GaloisForLFunctions.RHTower.BohrTransfer

open MeasureTheory intervalIntegral Filter Topology Complex Finset
open scoped Classical

namespace RHTower

/-- Convolution (Dirichlet product) coefficient of the square of a Dirichlet polynomial:
`convSq a s k = ∑_{mn=k, m,n∈s} aₘ aₙ`. -/
noncomputable def convSq (a : ℕ → ℝ) (s : Finset ℕ) (k : ℕ) : ℝ :=
  ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 * p.2 = k), a p.1 * a p.2

/-- Support of the square: products of pairs from `s`. -/
def sqSupport (s : Finset ℕ) : Finset ℕ := (s ×ˢ s).image (fun p => p.1 * p.2)

/-- Per-term product of two `cterm`s merges the frequencies multiplicatively. -/
theorem cterm_mul (a : ℕ → ℝ) (τ : ℝ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    cterm a τ m * cterm a τ n
      = ((a m * a n : ℝ) : ℂ) * Complex.exp (-(τ : ℂ) * Complex.I * (Real.log (↑(m * n)) : ℂ)) := by
  have hlogR : Real.log (↑(m * n) : ℝ) = Real.log ↑m + Real.log ↑n := by
    rw [Nat.cast_mul]
    exact Real.log_mul (by exact_mod_cast hm) (by exact_mod_cast hn)
  have hexp : Complex.exp (-(τ : ℂ) * Complex.I * (Real.log ↑m : ℂ))
        * Complex.exp (-(τ : ℂ) * Complex.I * (Real.log ↑n : ℂ))
      = Complex.exp (-(τ : ℂ) * Complex.I * (Real.log (↑(m * n)) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [show (Real.log (↑(m * n)) : ℂ) = (Real.log ↑m : ℂ) + (Real.log ↑n : ℂ) by
          rw [hlogR]; push_cast; ring]
    ring
  unfold cterm
  rw [mul_mul_mul_comm, hexp]
  push_cast
  ring

/-- **The square of a Dirichlet polynomial is a Dirichlet polynomial** with the convolution
coefficients on the square support. -/
theorem dpoly_sq (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, n ≠ 0) (τ : ℝ) :
    (dpoly a s τ) ^ 2 = dpoly (convSq a s) (sqSupport s) τ := by
  rw [sq, dpoly, Finset.sum_mul_sum, ← Finset.sum_product']
  have hmap : ∀ p ∈ s ×ˢ s, p.1 * p.2 ∈ sqSupport s := fun p hp =>
    Finset.mem_image.mpr ⟨p, hp, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun p => cterm a τ p.1 * cterm a τ p.2)]
  rw [dpoly]
  apply Finset.sum_congr rfl
  intro k hk
  have hcterm_k : cterm (convSq a s) τ k
      = ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 * p.2 = k),
          ((a p.1 * a p.2 : ℝ) : ℂ)
            * Complex.exp (-(τ : ℂ) * Complex.I * (Real.log (↑k) : ℂ)) := by
    unfold cterm convSq
    rw [Complex.ofReal_sum, Finset.sum_mul]
  rw [hcterm_k]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨hp1, hp2⟩, hprod⟩ := hp
  rw [cterm_mul a τ (hs p.1 hp1) (hs p.2 hp2), hprod]

open SteinhausModel

/-- Every element of the square support is `≥ 1`. -/
theorem one_le_of_mem_sqSupport {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n)
    {k : ℕ} (hk : k ∈ sqSupport s) : 1 ≤ k := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
  simp only [Finset.mem_product] at hp
  simpa using Nat.mul_le_mul (hs p.1 hp.1) (hs p.2 hp.2)

/-- **The square of the model Dirichlet polynomial** carries the convolution coefficients
on the square support, via multiplicativity `X_{mn} = X_m X_n`. -/
theorem model_sq (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, n ≠ 0) (ω : Omega) :
    (∑ n ∈ s, (a n : ℂ) * X n ω) ^ 2
      = ∑ k ∈ sqSupport s, (convSq a s k : ℂ) * X k ω := by
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
  have hmap : ∀ p ∈ s ×ˢ s, p.1 * p.2 ∈ sqSupport s := fun p hp =>
    Finset.mem_image.mpr ⟨p, hp, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun p => (a p.1 : ℂ) * X p.1 ω * ((a p.2 : ℂ) * X p.2 ω))]
  apply Finset.sum_congr rfl
  intro k hk
  have hxk : (convSq a s k : ℂ) * X k ω
      = ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 * p.2 = k),
          ((a p.1 * a p.2 : ℝ) : ℂ) * X k ω := by
    unfold convSq
    rw [Complex.ofReal_sum, Finset.sum_mul]
  rw [hxk]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨hp1, hp2⟩, hprod⟩ := hp
  rw [← hprod, X_mul (hs p.1 hp1) (hs p.2 hp2)]
  push_cast
  ring

/-- **Fourth-moment time average.** The vertical time average of `‖F‖⁴` converges to the
diagonal `∑ (convSq)²`, by applying the second-moment mean value to `F² = dpoly convSq`. -/
theorem tendsto_fourthMoment_average (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) :
    Tendsto (fun U : ℝ => (∫ t in (0:ℝ)..U, ‖dpoly a s t‖ ^ 4) / U) atTop
      (𝓝 (∑ k ∈ sqSupport s, convSq a s k ^ 2)) := by
  have hsne : ∀ n ∈ s, n ≠ 0 := fun n hn => Nat.one_le_iff_ne_zero.mp (hs n hn)
  have hrw : ∀ t : ℝ,
      ‖dpoly a s t‖ ^ 4 = ‖dpoly (convSq a s) (sqSupport s) t‖ ^ 2 := by
    intro t
    rw [← dpoly_sq a s hsne t, norm_pow]
    ring
  simp_rw [hrw]
  have := tendsto_secondMoment_average (convSq a s) (sqSupport s) 0
    (fun k hk => one_le_of_mem_sqSupport hs hk)
  simpa only [zero_add] using this

/-- **Fourth-moment model identity.** `E‖∑ aₙ Xₙ‖⁴ = ∑ (convSq)²`, via the model square
identity and the second-moment identity. -/
theorem integral_normSq_sq_dpoly (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) :
    ∫ ω, ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ 4 ∂steinhausMeasure
      = ∑ k ∈ sqSupport s, convSq a s k ^ 2 := by
  have hsne : ∀ n ∈ s, n ≠ 0 := fun n hn => Nat.one_le_iff_ne_zero.mp (hs n hn)
  have hrw : ∀ ω : Omega,
      ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ 4
        = ‖∑ k ∈ sqSupport s, (convSq a s k : ℂ) * X k ω‖ ^ 2 := by
    intro ω
    rw [← model_sq a s hsne ω, norm_pow]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hrw)]
  exact integral_normSq_dpoly (convSq a s) (sqSupport s)
    (fun k hk => Nat.one_le_iff_ne_zero.mp (one_le_of_mem_sqSupport hs hk))

/-- **The degree-two Bohr moment identity.** The vertical time average of `‖F‖⁴` equals the
Steinhaus-model fourth moment `E‖∑ aₙ Xₙ‖⁴`. Both collapse to the convolution diagonal
`∑ (convSq)²`: the fourth moment is the second moment of the square, and squaring commutes
with the deterministic-line ↔ character-model correspondence. -/
theorem tendsto_fourthMoment_average_steinhaus
    (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) :
    Tendsto (fun U : ℝ => (∫ t in (0:ℝ)..U, ‖dpoly a s t‖ ^ 4) / U) atTop
      (𝓝 (∫ ω, ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ 4 ∂steinhausMeasure)) := by
  rw [integral_normSq_sq_dpoly a s hs]
  exact tendsto_fourthMoment_average a s hs

end RHTower
