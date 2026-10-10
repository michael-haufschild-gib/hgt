import GaloisForLFunctions.RHTower.XiHorizontalAbsoluteMonotonicityStrip
import GaloisForLFunctions.RHTower.XiSliceCoeffPositivitySharpWindow

/-!
# Zero-free strips reduce to logarithmically many coefficients per height

The Taylor coefficients of the slice `g_t` at an off-centre point `x₀ ≥ 0` are nonnegative
combinations of its centre coefficients (`iteratedDeriv_xiSliceProduct_eq_tsum`):

  `g_t^{(n)}(x₀) = Σ_k (x₀^k / k!) · g_t^{(n+k)}(0)`.

The centre coefficients are positive above the quarter-log edge
(`exists_xiSliceCoeff_pos_above_quarter_log`), so every coefficient of order
`n ≥ 2 max(K, (¼ + ε) log t)` at `x₀` is positive automatically, for every `x₀ ≥ 0`.  Together with
the strip criterion (`XiHorizontalAbsoluteMonotonicityStrip`), for every `ε > 0` there is `K` such
that, for every `x₀ ≥ 0`, the strip `|Re ρ − ½| ≤ x₀` holds iff `g_t^{(n)}(x₀) ≥ 0` for all `t ≥ 0` and
`n < 2 max(K, (¼ + ε) log t)` (`exists_strip_iff_low_order_horizontalAbsMono`).  The zero-free strip
`Θ ≤ ½ + x₀` thus reduces to `O(log t)` explicit derivative inequalities at each height, with a
window that does not depend on `x₀`.
-/

open Complex Filter Topology
open scoped ComplexOrder Nat

namespace RHTower

noncomputable section

theorem iteratedDeriv_iteratedDeriv_comm (f : ℂ → ℂ) (n k : ℕ) :
    iteratedDeriv k (iteratedDeriv n f) = iteratedDeriv (n + k) f := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    ← Function.iterate_add_apply, add_comm]

/-- **Taylor shift.**  `g_t^{(n)}(x₀) = Σ_k (k!)⁻¹ x₀^k g_t^{(n+k)}(0)`. -/
theorem hasSum_iteratedDeriv_xiSliceProduct (t : ℝ) (n : ℕ) (x₀ : ℂ) :
    HasSum (fun k : ℕ => ((k ! : ℂ))⁻¹ * (x₀ ^ k * iteratedDeriv (n + k) (xiSliceProduct t) 0))
      (iteratedDeriv n (xiSliceProduct t) x₀) := by
  have hG : Differentiable ℂ (iteratedDeriv n (xiSliceProduct t)) :=
    ((differentiable_xiSliceProduct t).contDiff (n := ⊤)).differentiable_iteratedDeriv n
      (WithTop.coe_lt_top _)
  have h := Complex.hasSum_taylorSeries_of_entire hG 0 x₀
  simp only [sub_zero, smul_eq_mul, iteratedDeriv_iteratedDeriv_comm] at h
  exact h

/-- Above the doubled quarter-log edge every Taylor coefficient of the slice at a point `x₀ ≥ 0`
is nonnegative. -/
theorem iteratedDeriv_xiSliceProduct_nonneg_of_high_order {t x₀ : ℝ} (hx₀ : 0 ≤ x₀) {N : ℕ}
    (hc : ∀ m : ℕ, N ≤ m → 0 ≤ xiSliceCoeff t m) {n : ℕ} (hn : N ≤ n) :
    0 ≤ iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ) := by
  have h := hasSum_iteratedDeriv_xiSliceProduct t n (x₀ : ℂ)
  set T : ℕ → ℂ := fun k => ((k ! : ℂ))⁻¹ * ((x₀ : ℂ) ^ k *
    iteratedDeriv (n + k) (xiSliceProduct t) 0) with hT
  have hterm : ∀ k, 0 ≤ T k := by
    intro k
    have hck := hc (n + k) (by omega)
    have hD : iteratedDeriv (n + k) (xiSliceProduct t) 0 =
        (((n + k) ! : ℂ)) * xiSliceCoeff t (n + k) := by
      unfold xiSliceCoeff
      have : (((n + k) ! : ℂ)) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
      field_simp
    have h1 : (0 : ℂ) ≤ ((k ! : ℂ))⁻¹ := by
      rw [show ((k ! : ℂ))⁻¹ = ((((k ! : ℝ))⁻¹ : ℝ) : ℂ) by push_cast; rfl]
      exact Complex.zero_le_real.mpr (by positivity)
    have h2 : (0 : ℂ) ≤ (x₀ : ℂ) ^ k := by
      rw [← Complex.ofReal_pow]
      exact Complex.zero_le_real.mpr (pow_nonneg hx₀ k)
    have h3 : (0 : ℂ) ≤ (((n + k) ! : ℂ)) := by
      rw [show (((n + k) ! : ℂ)) = ((((n + k) ! : ℝ)) : ℂ) by push_cast; rfl]
      exact Complex.zero_le_real.mpr (by positivity)
    show 0 ≤ ((k ! : ℂ))⁻¹ * ((x₀ : ℂ) ^ k * iteratedDeriv (n + k) (xiSliceProduct t) 0)
    rw [hD]
    exact mul_nonneg h1 (mul_nonneg h2 (mul_nonneg h3 hck))
  have hre : HasSum (fun k => (T k).re) (iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ)).re := by
    have := h.mapL Complex.reCLM
    simpa using this
  have him : HasSum (fun k => (T k).im) (iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ)).im := by
    have := h.mapL Complex.imCLM
    simpa using this
  have himz : ∀ k, (T k).im = 0 := fun k => (Complex.nonneg_iff.mp (hterm k)).2.symm
  rw [show (fun k => (T k).im) = fun _ => (0 : ℝ) from funext himz] at him
  refine Complex.nonneg_iff.mpr ⟨hre.nonneg fun k => (Complex.nonneg_iff.mp (hterm k)).1, ?_⟩
  exact (him.unique hasSum_zero).symm

/-- **Strip criterion with a logarithmic window.**  For every `ε > 0` there is `K` such that for
every `x₀ ≥ 0`, all zeros satisfy `|Re ρ − ½| ≤ x₀` iff the Taylor coefficients of the slice `g_t` at
`x₀` of order `n < 2 max(K, (¼ + ε) log t)` are nonnegative at every height `t ≥ 0`. -/
theorem exists_strip_iff_low_order_horizontalAbsMono {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, ∀ x₀ : ℝ, 0 ≤ x₀ →
      ((∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ x₀) ↔
        ∀ t : ℝ, 0 ≤ t → ∀ n : ℕ, (n : ℝ) < 2 * max K ((1 / 4 + ε) * Real.log t) →
          0 ≤ iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ)) := by
  obtain ⟨K, hK⟩ := exists_xiSliceCoeff_pos_above_quarter_log hε
  refine ⟨K, fun x₀ hx₀ => ⟨fun h t _ n _ => horizontalAbsMono_of_abs_re_sub_half_le hx₀ h t n,
    fun h => ?_⟩⟩
  have hfull : ∀ t : ℝ, 0 ≤ t → XiHorizontalAbsMono x₀ t := by
    intro t ht n
    rcases lt_or_ge (n : ℝ) (2 * max K ((1 / 4 + ε) * Real.log t)) with hlt | hge
    · exact h t ht n hlt
    · refine iteratedDeriv_xiSliceProduct_nonneg_of_high_order hx₀ (N := n) (fun m hm => ?_)
        le_rfl
      rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
      · have hj : max K ((1 / 4 + ε) * Real.log t) ≤ (j : ℝ) := by
          have : ((2 * j : ℕ) : ℝ) ≥ (n : ℝ) := by exact_mod_cast hm
          push_cast at this
          linarith
        exact (hK t ht j hj).le
      · rw [xiSliceCoeff_odd_eq_zero]
  intro q
  rcases le_or_gt 0 (q.1 : ℂ).im with him | him
  · exact abs_re_sub_half_le_of_horizontalAbsMono_at q (hfull _ him)
  · have hq' := abs_re_sub_half_le_of_horizontalAbsMono_at (xiZeroCopyConjEquiv q)
      (hfull _ (by rw [xiZeroCopyConjEquiv_coe, Complex.conj_im]; linarith))
    rwa [xiZeroCopyConjEquiv_coe, Complex.conj_re] at hq'

end

end RHTower
