import GaloisForLFunctions.HTGeometry.CentralIndexSpreadSelection
import GaloisForLFunctions.HTGeometry.WimanValironWindowEstimate
import GaloisForLFunctions.HTGeometry.CircleMaximumExistence

/-!
# A radius at which the Wiman--Valiron estimate holds

The two halves meet: the measure bound for monotone increments produces a radius at which the
central index barely moves, and at such a radius the window estimate applies with the Lipschitz
constant that radius supplies.

The statement below is the whole chain in one place.  Its hypotheses are arithmetic — a sampling
interval long enough for the measure argument, and a window half-width `N` inside the range
`[2 L v₀, 2 L H]` — and its conclusion is the explicit bound, with no regularity assumption anywhere
and no quantity on the right-hand side except `N` and `L`.
-/

open MeasureTheory Complex Set

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ}

/-- **The Wiman--Valiron estimate at a selected radius.**  If the total rise of the central index
across the sampling interval, scaled by `2H / s`, is shorter than that interval, then some radius in
it carries the estimate with Lipschitz constant `L`, for every window half-width `N` in
`[2 L v₀, 2 L H]`. -/
theorem exists_radius_norm_mul_logDeriv_sub_centralIndex_le
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {c d H v₀ s L : ℝ}
    (hcd : c ≤ d) (hH : 0 < H) (hv₀ : 0 < v₀) (hs : 0 < s) (hL : 0 < L) (hsL : s ≤ L * v₀)
    (hsmall : 2 * H * ((centralIndex a (Real.exp (d + 2 * H)) : ℝ)
        - (centralIndex a (Real.exp c) : ℝ)) / s < d - c)
    {N : ℕ} (hN0 : 0 < N) (hNv : 2 * L * v₀ ≤ (N : ℝ)) (hNK : (N : ℝ) ≤ 2 * L * H) :
    ∃ x ∈ Icc (c + H) (d + H),
      ∀ z : ℂ, ‖z‖ = Real.exp x →
        maxTerm a (Real.exp x) ≤ ‖coeffFun a z‖ →
        (∀ θ : ℝ, ‖coeffFun a (circleMap 0 (Real.exp x) θ)‖ ≤ ‖coeffFun a z‖) →
        (z * deriv (coeffFun a) z / coeffFun a z).im = 0 →
        ∀ u : ℂ, ‖u‖ = 1 →
          (∑' n : ℕ, normalisedCoeff a (Real.exp x) z n
            = ((‖∑' n : ℕ, normalisedCoeff a (Real.exp x) z n‖ : ℝ) : ℂ) * u) →
          ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp x) : ℂ)‖
            ≤ (Real.sqrt (2 * (N : ℝ) + 1)
                + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
                    / (1 - Real.exp (-((N : ℝ) / (4 * L))))))
                * |meanIndex a (Real.exp x) - (centralIndex a (Real.exp x) : ℝ)|
              + Real.sqrt (2 * ((N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
                    + 2 * (2 * ((N : ℝ) + 1) ^ 2 * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
                        / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3))
                  * (Real.sqrt (2 * (N : ℝ) + 1)
                    + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
                        / (1 - Real.exp (-((N : ℝ) / (4 * L))))))) := by
  obtain ⟨y, hy, hspread⟩ := exists_small_centralIndexSpread ha hn₀ hcd hH hs hsmall
  refine ⟨y + H, ⟨by linarith [hy.1], by linarith [hy.2]⟩, ?_⟩
  intro z hz hfz hmax hcrit u hu hWdir
  have hLge : centralIndexSpread a (y + H) H / v₀ ≤ L := by
    rw [div_le_iff₀ hv₀]
    linarith
  exact norm_mul_logDeriv_sub_centralIndex_le_explicit_window ha hn₀ hH hL hN0 hNK hNv
    (centralIndex_le_add_of_spread_le ha hn₀ hv₀ hLge)
    (sub_of_spread_le_le_centralIndex ha hn₀ hv₀ hLge)
    hz hfz hmax hcrit hu hWdir

/-- **The Wiman--Valiron estimate with no side conditions.**  The maximum-modulus point of the
selected circle exists and supplies every hypothesis the window estimate asks of it, so the
statement reduces to the arithmetic conditions on the parameters. -/
theorem exists_radius_point_norm_mul_logDeriv_sub_centralIndex_le
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {c d H v₀ s L : ℝ}
    (hcd : c ≤ d) (hH : 0 < H) (hv₀ : 0 < v₀) (hs : 0 < s) (hL : 0 < L) (hsL : s ≤ L * v₀)
    (hsmall : 2 * H * ((centralIndex a (Real.exp (d + 2 * H)) : ℝ)
        - (centralIndex a (Real.exp c) : ℝ)) / s < d - c)
    {N : ℕ} (hN0 : 0 < N) (hNv : 2 * L * v₀ ≤ (N : ℝ)) (hNK : (N : ℝ) ≤ 2 * L * H) :
    ∃ x ∈ Icc (c + H) (d + H), ∃ z : ℂ, ‖z‖ = Real.exp x ∧
      ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp x) : ℂ)‖
        ≤ (Real.sqrt (2 * (N : ℝ) + 1)
            + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
                / (1 - Real.exp (-((N : ℝ) / (4 * L))))))
            * |meanIndex a (Real.exp x) - (centralIndex a (Real.exp x) : ℝ)|
          + Real.sqrt (2 * ((N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
                + 2 * (2 * ((N : ℝ) + 1) ^ 2 * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
                    / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3))
              * (Real.sqrt (2 * (N : ℝ) + 1)
                + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
                    / (1 - Real.exp (-((N : ℝ) / (4 * L))))))) := by
  obtain ⟨x, hx, hest⟩ := exists_radius_norm_mul_logDeriv_sub_centralIndex_le ha hn₀ hcd hH hv₀
    hs hL hsL hsmall hN0 hNv hNK
  have hr : (0 : ℝ) < Real.exp x := Real.exp_pos x
  obtain ⟨z, hz, hmax⟩ := exists_max_on_circle ha hr
  have hfz := maxTerm_le_norm_of_max_on_circle ha hr hz hmax
  obtain ⟨-, -, hμpos⟩ := exists_maxTerm_eq ha hr hn₀
  have hfpos : 0 < ‖coeffFun a z‖ := lt_of_lt_of_le hμpos hfz
  have hfne : coeffFun a z ≠ 0 := norm_pos_iff.mp hfpos
  have hcrit := im_mul_deriv_div_eq_zero_of_max_on_circle ha hr hz hfne hmax
  have hfac : coeffFun a z
      = (a (centralIndex a (Real.exp x)) * z ^ centralIndex a (Real.exp x))
        * ∑' n : ℕ, normalisedCoeff a (Real.exp x) z n :=
    coeffFun_eq_central_term_mul_tsum ha hr hn₀ hz
  have hWne : (∑' n : ℕ, normalisedCoeff a (Real.exp x) z n) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hfac
    exact hfne hfac
  obtain ⟨u, hu, hWdir⟩ := exists_unit_dir hWne
  exact ⟨x, hx, z, hz, hest z hz hfz hmax hcrit u hu hWdir⟩

end GaloisForLFunctions.HTGeometry
