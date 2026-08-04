import GaloisForLFunctions.HTGeometry.CentralIndexSpreadSelection
import GaloisForLFunctions.HTGeometry.WimanValironWindowEstimate
import GaloisForLFunctions.HTGeometry.CircleMaximumExistence
import GaloisForLFunctions.HTGeometry.MeanIndexLipschitz

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

set_option maxHeartbeats 400000 in
/-- **The Wiman--Valiron estimate with the mean-minus-mode gap eliminated.**  The same Lipschitz data
that drives the Gaussian decay also bounds the gap between the mean and the modal index, so the
estimate becomes a closed expression in the parameters and the central index alone. -/
theorem exists_radius_point_norm_mul_logDeriv_sub_centralIndex_le_closed
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {c d H v₀ s L h : ℝ}
    (hcd : c ≤ d) (hH : 0 < H) (hv₀ : 0 < v₀) (hs : 0 < s) (hL : 0 < L) (hsL : s ≤ L * v₀)
    (hh : 0 < h) (hv₀h : v₀ ≤ h) (hhH : 2 * h ≤ H)
    (hsmall : 2 * H * ((centralIndex a (Real.exp (d + 2 * H)) : ℝ)
        - (centralIndex a (Real.exp c) : ℝ)) / s < d - c)
    {N : ℕ} (hN0 : 0 < N) (hNv : 2 * L * v₀ ≤ (N : ℝ)) (hNK : (N : ℝ) ≤ 2 * L * H) :
    ∃ x ∈ Icc (c + H) (d + H), ∃ z : ℂ, ‖z‖ = Real.exp x ∧
      maxTerm a (Real.exp x) ≤ ‖coeffFun a z‖ ∧
      ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp x) : ℂ)‖
        ≤ (Real.sqrt (2 * (N : ℝ) + 1)
            + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
                / (1 - Real.exp (-((N : ℝ) / (4 * L))))))
            * (2 * L * h
              + 2 * Real.log ((centralIndex a (Real.exp x) : ℝ) + 2 * L * h + 1
                  + 1 / (Real.exp h - 1)) / h)
          + Real.sqrt (2 * ((N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
                + 2 * (2 * ((N : ℝ) + 1) ^ 2 * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
                    / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3))
              * (Real.sqrt (2 * (N : ℝ) + 1)
                + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
                    / (1 - Real.exp (-((N : ℝ) / (4 * L))))))) := by
  obtain ⟨x, hx, hlipA0, hlipB0⟩ :=
    exists_radius_lipschitz_centralIndex ha hn₀ hcd hH hv₀ hs hsmall
  have hupg : ∀ v : ℝ, v₀ ≤ v → s / v₀ * v ≤ L * v := by
    intro v hv
    refine mul_le_mul_of_nonneg_right ?_ (le_trans hv₀.le hv)
    rw [div_le_iff₀ hv₀]
    exact hsL
  have hA : ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp (x + v)) : ℝ) ≤ (centralIndex a (Real.exp x) : ℝ) + L * v := by
    intro v hv hvH
    have h1 := hlipA0 v hv hvH
    have h2 := hupg v hv
    linarith
  have hB : ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp x) : ℝ) - L * v ≤ (centralIndex a (Real.exp (x - v)) : ℝ) := by
    intro v hv hvH
    have h1 := hlipB0 v hv hvH
    have h2 := hupg v hv
    linarith
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
    intro hzero
    rw [hzero, mul_zero] at hfac
    exact hfne hfac
  obtain ⟨u, hu, hWdir⟩ := exists_unit_dir hWne
  have hest := norm_mul_logDeriv_sub_centralIndex_le_explicit_window ha hn₀ hH hL hN0 hNK hNv
    hA hB hz hfz hmax hcrit hu hWdir
  have hgap := abs_meanIndex_sub_centralIndex_le_lipschitz ha hn₀ hL hh hhH hv₀h hA hB
  refine ⟨x, hx, z, hz, hfz, le_trans hest ?_⟩
  have hq0 : (0 : ℝ) < Real.exp (-((N : ℝ) / (4 * L))) := Real.exp_pos _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hq1 : Real.exp (-((N : ℝ) / (4 * L))) < 1 := by
    rw [Real.exp_lt_one_iff]
    have : (0 : ℝ) < (N : ℝ) / (4 * L) := by positivity
    linarith
  have hAnn : (0 : ℝ) ≤ Real.sqrt (2 * (N : ℝ) + 1)
      + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
          / (1 - Real.exp (-((N : ℝ) / (4 * L))))) := by
    have hden : (0 : ℝ) < 1 - Real.exp (-((N : ℝ) / (4 * L))) := by linarith
    have h1 : (0 : ℝ) ≤ Real.sqrt (2 * (N : ℝ) + 1) := Real.sqrt_nonneg _
    have h2 : (0 : ℝ) ≤ Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
        / (1 - Real.exp (-((N : ℝ) / (4 * L)))) := by positivity
    linarith
  have hstep := mul_le_mul_of_nonneg_left hgap hAnn
  linarith

/-- **The estimate with the free parameters tied together.**  Taking the sampling scale and the
lower scale bound both equal to `H / 2` and the Lipschitz constant `2 s / H` — the smallest value
compatible with a spread of `s` — leaves only the window `[2s, 4s]` for the half-width `N`. -/
theorem exists_radius_point_wiman_valiron_bound
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {c d H s L h : ℝ}
    (hcd : c ≤ d) (hH : 0 < H) (hs : 0 < s)
    (hLdef : L = 2 * s / H) (hhdef : h = H / 2)
    (hsmall : 2 * H * ((centralIndex a (Real.exp (d + 2 * H)) : ℝ)
        - (centralIndex a (Real.exp c) : ℝ)) / s < d - c)
    {N : ℕ} (hN2s : 2 * s ≤ (N : ℝ)) (hN4s : (N : ℝ) ≤ 4 * s) :
    ∃ x ∈ Icc (c + H) (d + H), ∃ z : ℂ, ‖z‖ = Real.exp x ∧
      maxTerm a (Real.exp x) ≤ ‖coeffFun a z‖ ∧
      ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp x) : ℂ)‖
        ≤ (Real.sqrt (2 * (N : ℝ) + 1)
            + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
                / (1 - Real.exp (-((N : ℝ) / (4 * L))))))
            * (2 * L * h
              + 2 * Real.log ((centralIndex a (Real.exp x) : ℝ) + 2 * L * h + 1
                  + 1 / (Real.exp h - 1)) / h)
          + Real.sqrt (2 * ((N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
                + 2 * (2 * ((N : ℝ) + 1) ^ 2 * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
                    / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3))
              * (Real.sqrt (2 * (N : ℝ) + 1)
                + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
                    / (1 - Real.exp (-((N : ℝ) / (4 * L))))))) := by
  subst hLdef
  subst hhdef
  have hHne : H ≠ 0 := ne_of_gt hH
  have hN0 : 0 < N := by
    by_contra hcon
    have hN : N = 0 := by omega
    rw [hN] at hN2s
    simp at hN2s
    linarith
  refine exists_radius_point_norm_mul_logDeriv_sub_centralIndex_le_closed ha hn₀ (v₀ := H / 2)
    hcd hH (by positivity) hs (by positivity) ?_ (by positivity) le_rfl (by linarith) hsmall
    hN0 ?_ ?_
  · have heq : 2 * s / H * (H / 2) = s := by field_simp
    exact le_of_eq heq.symm
  · calc 2 * (2 * s / H) * (H / 2) = 2 * s := by field_simp
      _ ≤ (N : ℝ) := hN2s
  · calc (N : ℝ) ≤ 4 * s := hN4s
      _ = 2 * (2 * s / H) * H := by
          field_simp
          norm_num

end GaloisForLFunctions.HTGeometry
