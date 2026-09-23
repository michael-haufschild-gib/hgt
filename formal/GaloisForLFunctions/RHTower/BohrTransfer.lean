/-
# The Bohr transfer at the second moment: time average = ensemble average

For a Dirichlet polynomial `F(t) = ∑_{n∈s} a n · n^{-it}` with support in
`[1,∞)`, the long-window time average of `‖F‖²` converges to the diagonal
`∑ (a n)²`: the off-diagonal remainder of the window integral is bounded
uniformly in the window length (`offDiagonal_abs_le`), so dividing by the
length kills it.  The same diagonal is the exact Steinhaus-model second
moment `E‖∑ aₙ Xₙ‖²` (`integral_normSq_dpoly`).  Composing the two:

    lim_{U→∞} (1/U)·∫_T^{T+U} ‖F(t)‖² dt  =  E_ω ‖∑ aₙ Xₙ(ω)‖²

for every basepoint `T` — the vertical-line time average of the squared
carrier equals its random-model ensemble average.  This is the second-moment
case of the Bohr correspondence between the deterministic `t`-line and the
Steinhaus character model, effective: the gap between window average and
ensemble moment is at most `B/U` with the explicit off-diagonal constant
`B = ∑∑ 2|aₘaₙ|/|log(n/m)|`.
-/
import GaloisForLFunctions.RHTower.SecondMoment
import GaloisForLFunctions.RHTower.SteinhausModel

namespace RHTower

open Filter Topology

/-- **Effective window-average control**: the window average of `‖F‖²` is
within `B/U` of the diagonal `∑ (a n)²`, where
`B = ∑∑ 2|aₘaₙ|/|log(n/m)|` is the `U`-independent off-diagonal constant. -/
theorem abs_secondMoment_average_sub_diagonal_le
    (a : ℕ → ℝ) (s : Finset ℕ) (T U : ℝ) (hU : 0 < U)
    (hs : ∀ n ∈ s, 1 ≤ n) :
    |(∫ t in T..(T + U), ‖dpoly a s t‖ ^ (2 : ℕ)) / U - ∑ n ∈ s, (a n) ^ (2 : ℕ)|
      ≤ (∑ m ∈ s, ∑ n ∈ s.erase m,
          2 * |a m * a n| / |Real.log n - Real.log m|) / U := by
  rw [secondMoment_meanValue]
  have heq : (U * (∑ m ∈ s, (a m) ^ (2 : ℕ))
        + ∑ m ∈ s, ∑ n ∈ s.erase m,
            a m * a n * cosInt (Real.log n - Real.log m) T U) / U
        - ∑ n ∈ s, (a n) ^ (2 : ℕ)
      = (∑ m ∈ s, ∑ n ∈ s.erase m,
          a m * a n * cosInt (Real.log n - Real.log m) T U) / U := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hU]
  gcongr
  exact offDiagonal_abs_le a s T U hs

/-- **The mean-value limit**: the vertical time average of `‖F‖²` over
`[T, T+U]` tends to the diagonal `∑ (a n)²` as `U → ∞`, at every basepoint
`T`. -/
theorem tendsto_secondMoment_average
    (a : ℕ → ℝ) (s : Finset ℕ) (T : ℝ) (hs : ∀ n ∈ s, 1 ≤ n) :
    Tendsto (fun U => (∫ t in T..(T + U), ‖dpoly a s t‖ ^ (2 : ℕ)) / U) atTop
      (nhds (∑ n ∈ s, (a n) ^ (2 : ℕ))) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hlim : Tendsto (fun U : ℝ =>
      (∑ m ∈ s, ∑ n ∈ s.erase m,
        2 * |a m * a n| / |Real.log n - Real.log m|) / U) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  apply squeeze_zero' (Eventually.of_forall fun U => dist_nonneg) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with U hU
  rw [Real.dist_eq]
  exact abs_secondMoment_average_sub_diagonal_le a s T U hU hs

open SteinhausModel in
/-- **The Bohr transfer at the second moment**: the long-run vertical time
average of the squared Dirichlet polynomial equals the Steinhaus-model
ensemble second moment of the same coefficients, at every basepoint `T`.
The deterministic `t`-line and the random character model agree exactly at
the second-moment observable. -/
theorem tendsto_secondMoment_average_steinhaus
    (a : ℕ → ℝ) (s : Finset ℕ) (T : ℝ) (hs : ∀ n ∈ s, 1 ≤ n) :
    Tendsto (fun U => (∫ t in T..(T + U), ‖dpoly a s t‖ ^ (2 : ℕ)) / U) atTop
      (nhds (∫ ω, ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ (2 : ℕ) ∂steinhausMeasure)) := by
  rw [integral_normSq_dpoly a s (fun n hn => Nat.one_le_iff_ne_zero.mp (hs n hn))]
  exact tendsto_secondMoment_average a s T hs

end RHTower
