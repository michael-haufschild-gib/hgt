import GaloisForLFunctions.RHTower.PrimeWindowBinomialBound
import GaloisForLFunctions.RHTower.PsiRemainderSignChange
import Mathlib.NumberTheory.Chebyshev

/-!
# The `ψ`-window upper bound and pointwise two-sided slow variation

For `x < y ≤ 2x`,

`ψ(y) − ψ(x) ≤ (y−x)(log y − log(y−x) + 1) + 2√y·log y`:

the prime part is the binomial window bound, and the prime-power part is
mathlib's `Chebyshev.psi_sub_theta_le` (`ψ − θ ≤ 2√x log x`).  Combined
with the down-Lipschitz bound `R(t) − R(m₀) ≥ −(t−m₀)`, the remainder
satisfies a **two-sided pointwise** estimate around any point:

`|R(t)| ≤ |R(m₀)| + (t−m₀)(log t − log(t−m₀) + 2) + 2√t·log t`,

which at small-value points `m₀` makes `|R|` pointwise small on whole
relative-width windows — the input of the Erdős–Selberg contraction.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- The `θ`-window is the window prime log-sum. -/
theorem theta_window_eq {x y : ℕ} (hxy : x ≤ y) :
    Chebyshev.theta y - Chebyshev.theta x
      = ∑ p ∈ (Finset.Ioc x y).filter Nat.Prime, Real.log p := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
  have hsub : Nat.primesLE x ⊆ Nat.primesLE y := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨le_trans hp.1 hxy, hp.2⟩
  rw [← Finset.sum_sdiff_eq_sub hsub]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext p
  rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE,
    Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hpy, hp⟩, hnx⟩
    refine ⟨⟨?_, hpy⟩, hp⟩
    by_contra hle
    exact hnx ⟨by omega, hp⟩
  · rintro ⟨⟨hxp, hpy⟩, hp⟩
    exact ⟨⟨hpy, hp⟩, fun h => by omega⟩

/-- **`ψ`-window upper bound**: for `x < y ≤ 2x`,
`ψ(y) − ψ(x) ≤ (y−x)(log y − log(y−x) + 1) + 2√y·log y`. -/
theorem chebyshevPsi_window_le {x y : ℕ} (hx : 1 ≤ x) (hxy : x < y)
    (hy2 : y ≤ 2 * x) :
    chebyshevPsi y - chebyshevPsi x
      ≤ ((y - x : ℕ) : ℝ)
          * (Real.log y - Real.log ((y - x : ℕ) : ℝ) + 1)
        + 2 * Real.sqrt y * Real.log y := by
  have hy1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (by omega : 1 ≤ y)
  rw [chebyshevPsi_eq_psi, chebyshevPsi_eq_psi]
  have hθ := theta_window_eq (le_of_lt hxy)
  have hbin := sum_primes_log_window_le hx hxy hy2
  have hψθy := Chebyshev.psi_sub_theta_le hy1
  have hψθx := Chebyshev.theta_le_psi (x : ℝ)
  have hkey : Chebyshev.psi y - Chebyshev.psi x
      = (Chebyshev.theta y - Chebyshev.theta x)
        + (Chebyshev.psi y - Chebyshev.theta y)
        - (Chebyshev.psi x - Chebyshev.theta x) := by
    ring
  rw [hkey, hθ]
  linarith [hbin, hψθy, hψθx]

/-- **Two-sided pointwise slow variation**: for `m₀ ≤ t ≤ 2m₀`,
`|R(t)| ≤ |R(m₀)| + (t−m₀)(log t − log(t−m₀) + 2) + 2√t·log t`. -/
theorem abs_psiRemainder_le_of_window {m₀ t : ℕ} (hm : 1 ≤ m₀)
    (hmt : m₀ ≤ t) (ht2 : t ≤ 2 * m₀) :
    |psiRemainder t| ≤ |psiRemainder m₀|
      + ((t - m₀ : ℕ) : ℝ)
          * (Real.log t - Real.log ((t - m₀ : ℕ) : ℝ) + 2)
      + 2 * Real.sqrt t * Real.log t := by
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (by omega : 1 ≤ t)
  have hsqrt0 : 0 ≤ 2 * Real.sqrt t * Real.log t := by
    have := Real.log_nonneg ht1
    positivity
  rcases Nat.eq_or_lt_of_le hmt with rfl | hlt
  · simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
    linarith
  -- lower: slow variation
  have hlow := psiRemainder_sub_ge (le_of_lt hlt)
  -- upper: the ψ-window bound
  have hup : psiRemainder t - psiRemainder m₀
      ≤ ((t - m₀ : ℕ) : ℝ)
          * (Real.log t - Real.log ((t - m₀ : ℕ) : ℝ) + 1)
        + 2 * Real.sqrt t * Real.log t := by
    have hψ := chebyshevPsi_window_le hm hlt ht2
    have hexp : psiRemainder t - psiRemainder m₀
        = (chebyshevPsi t - chebyshevPsi m₀) - ((t : ℝ) - m₀) := by
      simp only [psiRemainder]
      ring
    have hcast : ((t - m₀ : ℕ) : ℝ) = (t : ℝ) - m₀ := by
      rw [Nat.cast_sub (le_of_lt hlt)]
    have hnn : (0 : ℝ) ≤ (t : ℝ) - m₀ := by
      have : (m₀ : ℝ) ≤ t := by exact_mod_cast le_of_lt hlt
      linarith
    rw [hexp]
    linarith [hψ, hnn]
  -- combine: `|R t − R m₀| ≤ sum of the one-sided bounds`
  have hcast : ((t - m₀ : ℕ) : ℝ) = (t : ℝ) - m₀ := by
    rw [Nat.cast_sub (le_of_lt hlt)]
  have hnn : (0 : ℝ) ≤ (t : ℝ) - m₀ := by
    have : (m₀ : ℝ) ≤ t := by exact_mod_cast le_of_lt hlt
    linarith
  have hwid0 : 0 ≤ ((t - m₀ : ℕ) : ℝ)
      * (Real.log t - Real.log ((t - m₀ : ℕ) : ℝ) + 1) := by
    apply mul_nonneg (by rw [hcast]; linarith)
    have h1 : Real.log ((t - m₀ : ℕ) : ℝ) ≤ Real.log t := by
      rcases Nat.eq_zero_or_pos (t - m₀) with h0 | h0
      · rw [h0]
        simp only [Nat.cast_zero, Real.log_zero]
        exact Real.log_nonneg ht1
      · apply Real.log_le_log (by exact_mod_cast h0)
        exact_mod_cast (by omega : t - m₀ ≤ t)
    linarith
  have htri : |psiRemainder t| ≤ |psiRemainder m₀|
      + |psiRemainder t - psiRemainder m₀| := by
    calc |psiRemainder t|
        = |psiRemainder m₀ + (psiRemainder t - psiRemainder m₀)| := by
          ring_nf
      _ ≤ |psiRemainder m₀| + |psiRemainder t - psiRemainder m₀| :=
          abs_add_le _ _
  have habs : |psiRemainder t - psiRemainder m₀|
      ≤ ((t - m₀ : ℕ) : ℝ)
          * (Real.log t - Real.log ((t - m₀ : ℕ) : ℝ) + 1)
        + 2 * Real.sqrt t * Real.log t + ((t : ℝ) - m₀) := by
    rw [abs_le]
    constructor
    · have := hlow
      rw [hcast] at *
      linarith [hwid0, hsqrt0]
    · linarith [hup, hnn]
  calc |psiRemainder t|
      ≤ |psiRemainder m₀| + |psiRemainder t - psiRemainder m₀| := htri
    _ ≤ |psiRemainder m₀|
        + (((t - m₀ : ℕ) : ℝ)
            * (Real.log t - Real.log ((t - m₀ : ℕ) : ℝ) + 1)
          + 2 * Real.sqrt t * Real.log t + ((t : ℝ) - m₀)) := by
        linarith [habs]
    _ ≤ |psiRemainder m₀|
        + ((t - m₀ : ℕ) : ℝ)
            * (Real.log t - Real.log ((t - m₀ : ℕ) : ℝ) + 2)
        + 2 * Real.sqrt t * Real.log t := by
        rw [hcast]
        ring_nf
        nlinarith [hnn]

end RHTower
