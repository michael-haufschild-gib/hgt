/-
Off-line floor extension for the two-dimensional finite Dirichlet carrier.

The one-dimensional density/cofinality results control the carrier on a single vertical line. To
feed the certificate's floor on annulus charts, the line floor must extend off the line. This is a
Lipschitz-in-real-part phenomenon: at a fixed height the carrier changes by at most
`∑ |aₙ| · |n^{-σ₁} − n^{-σ₂}|` between real parts `σ₁, σ₂`, since the shared phase `n^{-iτ}` has
modulus one. Hence a line floor `‖F(σ₂+iτ)‖ > t₀` extends to `‖F(σ₁+iτ)‖ > ε` whenever the
variation budget is at most `t₀ − ε`, and — applied at cofinally many heights — gives a floor on the
whole `σ`-shifted strip over an unbounded height set. `dpoly2_line_eq` identifies the on-line carrier
with the one-dimensional `dpoly` (rescaled coefficients), so the density machinery transfers.
-/
import GaloisForLFunctions.RHTower.FloorFailureCofinal

open Complex Finset

namespace RHTower

/-- The two-dimensional finite Dirichlet carrier `∑_{n∈s} aₙ n^{-z}` on `ℂ`. Its restriction to a
vertical line is the one-dimensional carrier `dpoly`. -/
noncomputable def dpoly2 (a : ℕ → ℝ) (s : Finset ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ s, (a n : ℂ) * (n : ℂ) ^ (-z)

/-- **The 2-D carrier on a vertical line is a 1-D carrier.** At real part `σ`, `dpoly2 a s (σ+iτ)`
equals `dpoly` with coefficients rescaled by `n^{-σ}` — so the density and cofinality machinery for
`dpoly` transfers verbatim to any vertical line of the 2-D carrier. -/
theorem dpoly2_line_eq (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (σ τ : ℝ) :
    dpoly2 a s ((σ : ℂ) + (τ : ℂ) * I) = dpoly (fun n => a n * (n : ℝ) ^ (-σ)) s τ := by
  rw [dpoly2, dpoly]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp (hs n hn)
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (hs n hn)
  rw [cterm]
  have hfac : (n : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * I))
      = ((n : ℝ) ^ (-σ) : ℝ) * Complex.exp (-(τ : ℂ) * I * (Real.log n : ℂ)) := by
    rw [show -((σ : ℂ) + (τ : ℂ) * I) = (-(σ : ℂ)) + (-((τ : ℂ) * I)) by ring,
      Complex.cpow_add _ _ hn0]
    congr 1
    · rw [show (-(σ : ℂ)) = ((-σ : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_cpow (le_of_lt hnpos), Complex.ofReal_natCast]
    · rw [Complex.cpow_def_of_ne_zero hn0,
        show Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) by
          rw [show ((n : ℂ)) = (((n : ℝ)) : ℂ) by push_cast; ring]
          exact (Complex.ofReal_log (le_of_lt hnpos)).symm]
      congr 1; ring
  rw [hfac]; push_cast; ring

/-- On a common height `τ`, the modulus of `n^{-(σ₁+iτ)} − n^{-(σ₂+iτ)}` depends only on the real
parts: it equals `|n^{-σ₁} − n^{-σ₂}|`. The shared phase `n^{-iτ}` has modulus one. -/
theorem cpow_line_diff_norm (n : ℕ) (hn : 1 ≤ n) (σ₁ σ₂ τ : ℝ) :
    ‖(n : ℂ) ^ (-((σ₁ : ℂ) + (τ : ℂ) * I)) - (n : ℂ) ^ (-((σ₂ : ℂ) + (τ : ℂ) * I))‖
      = |(n : ℝ) ^ (-σ₁) - (n : ℝ) ^ (-σ₂)| := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hfac : ∀ ρ : ℝ, (n : ℂ) ^ (-((ρ : ℂ) + (τ : ℂ) * I))
      = ((n : ℝ) ^ (-ρ) : ℝ) * (n : ℂ) ^ (-((τ : ℂ) * I)) := by
    intro ρ
    rw [show -((ρ : ℂ) + (τ : ℂ) * I) = (-(ρ : ℂ)) + (-((τ : ℂ) * I)) by ring,
      Complex.cpow_add _ _ hn0]
    congr 1
    rw [show (-(ρ : ℂ)) = ((-ρ : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_cpow (le_of_lt hnpos), Complex.ofReal_natCast]
  rw [hfac σ₁, hfac σ₂,
    show ((n : ℝ) ^ (-σ₁) : ℝ) * (n : ℂ) ^ (-((τ : ℂ) * I))
          - ((n : ℝ) ^ (-σ₂) : ℝ) * (n : ℂ) ^ (-((τ : ℂ) * I))
        = (((n : ℝ) ^ (-σ₁) - (n : ℝ) ^ (-σ₂) : ℝ) : ℂ) * (n : ℂ) ^ (-((τ : ℂ) * I)) by
      push_cast; ring,
    norm_mul, Complex.norm_real]
  have hph : ‖(n : ℂ) ^ (-((τ : ℂ) * I))‖ = 1 := by
    rw [show ((n : ℂ)) = (((n : ℝ)) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    simp
  rw [hph, mul_one, Real.norm_eq_abs]

/-- **Off-line variation bound.** Between two real parts at a common height, the finite Dirichlet
carrier changes by at most `∑ |aₙ| · |n^{-σ₁} − n^{-σ₂}|`. -/
theorem norm_dpoly2_offline_le (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n)
    (σ₁ σ₂ τ : ℝ) :
    ‖dpoly2 a s ((σ₁ : ℂ) + (τ : ℂ) * I) - dpoly2 a s ((σ₂ : ℂ) + (τ : ℂ) * I)‖
      ≤ ∑ n ∈ s, |a n| * |(n : ℝ) ^ (-σ₁) - (n : ℝ) ^ (-σ₂)| := by
  rw [dpoly2, dpoly2, ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intro n hn
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    cpow_line_diff_norm n (hs n hn) σ₁ σ₂ τ]

/-- **Off-line floor extension.** A line floor `‖F(σ₂+iτ)‖ > t₀` extends to the real part `σ₁`
provided the off-line variation `∑ |aₙ| · |n^{-σ₁} − n^{-σ₂}|` is at most `t₀ − ε`: then
`‖F(σ₁+iτ)‖ > ε`. Lifting the line floor to a chart is a matter of choosing the shell radius
`|σ₁ − σ₂|` small enough that the variation budget holds. -/
theorem dpoly2_chart_floor (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n)
    (σ₁ σ₂ τ t₀ ε : ℝ)
    (hline : t₀ < ‖dpoly2 a s ((σ₂ : ℂ) + (τ : ℂ) * I)‖)
    (hoff : ∑ n ∈ s, |a n| * |(n : ℝ) ^ (-σ₁) - (n : ℝ) ^ (-σ₂)| ≤ t₀ - ε) :
    ε < ‖dpoly2 a s ((σ₁ : ℂ) + (τ : ℂ) * I)‖ := by
  have hb := norm_dpoly2_offline_le a s hs σ₁ σ₂ τ
  have hrev : ‖dpoly2 a s ((σ₂ : ℂ) + (τ : ℂ) * I)‖ - ‖dpoly2 a s ((σ₁ : ℂ) + (τ : ℂ) * I)‖
      ≤ ‖dpoly2 a s ((σ₂ : ℂ) + (τ : ℂ) * I) - dpoly2 a s ((σ₁ : ℂ) + (τ : ℂ) * I)‖ :=
    norm_sub_norm_le _ _
  rw [norm_sub_rev] at hrev
  linarith

/-- **Cofinal chart floor.** If the 2-D carrier's floor holds on the critical line at cofinally
many heights, and the (height-independent) off-line variation budget to real part `σ` is at most
`t₀ − ε`, then the floor `‖F(σ+iτ)‖ > ε` holds at cofinally many heights — a floor on the whole
`σ`-shifted strip over an unbounded height set. This is the height-level datum a window-placement
argument turns into a floor on the certificate charts. -/
theorem chart_floor_cofinal_of_line_cofinal (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n)
    (σ t₀ ε : ℝ)
    (hoff : ∑ n ∈ s, |a n| * |(n : ℝ) ^ (-σ) - (n : ℝ) ^ (-(1/2 : ℝ))| ≤ t₀ - ε)
    (hline : ∀ M : ℝ, ∃ τ, M < τ ∧
      t₀ < ‖dpoly2 a s (((1/2 : ℝ)) + (τ : ℂ) * I)‖) :
    ∀ M : ℝ, ∃ τ, M < τ ∧ ε < ‖dpoly2 a s ((σ : ℂ) + (τ : ℂ) * I)‖ := by
  intro M
  obtain ⟨τ, hτM, hτfloor⟩ := hline M
  exact ⟨τ, hτM, dpoly2_chart_floor a s hs σ (1/2) τ t₀ ε hτfloor hoff⟩

end RHTower
