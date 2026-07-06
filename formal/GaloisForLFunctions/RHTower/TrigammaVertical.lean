/-
Vertical bound for the trigamma layer `ψ′`.

The digamma recurrence differentiates to `ψ′(z+N) = ψ′(z) − Σ_{n<N} (z+n)⁻²`, and the
far-field anchor `ψ′(z+N) → 0` follows from the Gauss-limit shift bound through the Schwarz
quotient estimate on unit-scale disks: `ψ − ψ(N+1)` is uniformly `O(1/N)` there, so its
derivative at the center is too.  Hence `ψ′(σ+it)` is the limit of the partial sums
`Σ (z+n)⁻²`, and the arctan comparison gives the same vertical bound as for the digamma
itself: `‖ψ′(σ+it)‖ ≤ 1/t² + π/(2t)` — the curvature-scale datum of the archimedean winding.
-/
import GaloisForLFunctions.RHTower.ArchEnvelope
import GaloisForLFunctions.RHTower.DigammaAsymptotic

open Complex Filter Metric

namespace RHTower

/-- **Far-field decay of trigamma.**  `ψ′(z+N) → 0`: on the ball of radius `1/2` around
`z+N` the recentred digamma `ψ − ψ(N+1)` is uniformly `O(1/N)` by the shift bound, so the
Schwarz quotient estimate bounds its derivative at the center by `O(1/N)`. -/
theorem deriv_digamma_add_nat_tendsto (z : ℂ) :
    Tendsto (fun N : ℕ => deriv Complex.digamma (z + (N : ℂ))) atTop (nhds 0) := by
  set K : ℝ := ‖z - 1‖ + 1 / 2 with hK_def
  have hK0 : 0 < K := by
    rw [hK_def]
    positivity
  refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat (8 * K))
  filter_upwards [eventually_ge_atTop 1,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * K),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop (-z.re + 1)]
    with N hN1 hthr hre
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
  have hball_re : ∀ ζ ∈ ball (z + (N : ℂ)) (1 / 2), 0 < ζ.re := by
    intro ζ hζ
    have hd : ‖ζ - (z + (N : ℂ))‖ < 1 / 2 := by
      rw [← dist_eq_norm]
      exact hζ
    have h1 := abs_le.mp (le_of_lt (lt_of_le_of_lt
      (Complex.abs_re_le_norm (ζ - (z + (N : ℂ)))) hd))
    have h2 : (ζ - (z + (N : ℂ))).re = ζ.re - (z.re + N) := by
      simp [Complex.sub_re, Complex.add_re]
    rw [h2] at h1
    linarith [h1.1]
  have hsup : ∀ ζ ∈ ball (z + (N : ℂ)) (1 / 2),
      ‖Complex.digamma ζ - Complex.digamma ((N : ℂ) + 1)‖ ≤ 2 * K / N := by
    intro ζ hζ
    have hd : ‖ζ - (z + (N : ℂ))‖ < 1 / 2 := by
      rw [← dist_eq_norm]
      exact hζ
    have hwz : ‖(ζ - (N : ℂ)) - z‖ < 1 / 2 := by
      rw [show (ζ - (N : ℂ)) - z = ζ - (z + (N : ℂ)) from by ring]
      exact hd
    have hw1 : ‖(ζ - (N : ℂ)) - 1‖ ≤ K := by
      rw [hK_def]
      calc ‖(ζ - (N : ℂ)) - 1‖ = ‖((ζ - (N : ℂ)) - z) + (z - 1)‖ := by ring_nf
        _ ≤ ‖(ζ - (N : ℂ)) - z‖ + ‖z - 1‖ := norm_add_le _ _
        _ ≤ ‖z - 1‖ + 1 / 2 := by linarith
    have hwre : 0 < ((ζ - (N : ℂ)) + (N : ℂ)).re := by
      rw [sub_add_cancel]
      exact hball_re ζ hζ
    have hthr' : 2 * ‖(ζ - (N : ℂ)) - 1‖ ≤ (N : ℝ) := by
      linarith
    have happ := digamma_shift_diff_bound hN1 hwre hthr'
    rw [sub_add_cancel] at happ
    exact le_trans happ (div_le_div₀ (by linarith) (by linarith) hN0 le_rfl)
  have hc_mem : (z + (N : ℂ)) ∈ ball (z + (N : ℂ)) (1 / 2) :=
    mem_ball_self (by norm_num)
  have hdiff : DifferentiableOn ℂ
      (fun ζ => Complex.digamma ζ - Complex.digamma ((N : ℂ) + 1))
      (ball (z + (N : ℂ)) (1 / 2)) := fun ζ hζ =>
    ((digamma_analyticOnNhd_re_pos ζ (hball_re ζ hζ)).differentiableAt.sub_const
      _).differentiableWithinAt
  have hmaps : Set.MapsTo
      (fun ζ => Complex.digamma ζ - Complex.digamma ((N : ℂ) + 1))
      (ball (z + (N : ℂ)) (1 / 2))
      (closedBall (Complex.digamma (z + (N : ℂ)) - Complex.digamma ((N : ℂ) + 1))
        (4 * K / N)) := by
    intro ζ hζ
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖(Complex.digamma ζ - Complex.digamma ((N : ℂ) + 1)) -
          (Complex.digamma (z + (N : ℂ)) - Complex.digamma ((N : ℂ) + 1))‖
        ≤ ‖Complex.digamma ζ - Complex.digamma ((N : ℂ) + 1)‖ +
          ‖Complex.digamma (z + (N : ℂ)) - Complex.digamma ((N : ℂ) + 1)‖ :=
          norm_sub_le _ _
      _ ≤ 2 * K / N + 2 * K / N :=
          add_le_add (hsup ζ hζ) (hsup _ hc_mem)
      _ = 4 * K / N := by ring
  have hds := Complex.norm_dslope_le_div_of_mapsTo_ball hdiff hmaps hc_mem
  rw [dslope_same, deriv_sub_const] at hds
  calc ‖deriv Complex.digamma (z + (N : ℂ))‖
      ≤ (4 * K / N) / (1 / 2) := hds
    _ = 8 * K / N := by ring

/-- **Differentiated digamma recurrence**: `ψ′(z+N) = ψ′(z) − Σ_{n<N} (z+n)⁻²` on the right
half plane. -/
theorem deriv_digamma_apply_add_nat {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    deriv Complex.digamma (z + (N : ℂ)) =
      deriv Complex.digamma z - ∑ n ∈ Finset.range N, ((z + (n : ℂ)) ^ 2)⁻¹ := by
  have hUopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hψdiff : ∀ {w : ℂ}, 0 < w.re → HasDerivAt Complex.digamma (deriv Complex.digamma w) w :=
    fun hw => (digamma_analyticOnNhd_re_pos _ hw).differentiableAt.hasDerivAt
  have hzN : 0 < (z + (N : ℂ)).re := by
    rw [Complex.add_re, Complex.natCast_re]
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hL : HasDerivAt (fun w : ℂ => Complex.digamma (w + (N : ℂ)))
      (deriv Complex.digamma (z + (N : ℂ))) z := by
    have hcomp := HasDerivAt.comp z (hψdiff hzN) ((hasDerivAt_id z).add_const (N : ℂ))
    simpa [Function.comp] using hcomp
  have hne : ∀ n : ℕ, z + (n : ℂ) ≠ 0 := by
    intro n h0
    have h := congrArg Complex.re h0
    rw [Complex.add_re, Complex.natCast_re, Complex.zero_re] at h
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hsum : HasDerivAt (fun w : ℂ => ∑ n ∈ Finset.range N, (w + (n : ℂ))⁻¹)
      (∑ n ∈ Finset.range N, -1 / (z + (n : ℂ)) ^ 2) z := by
    have hfun : (fun w : ℂ => ∑ n ∈ Finset.range N, (w + (n : ℂ))⁻¹) =
        ∑ n ∈ Finset.range N, fun w : ℂ => (w + (n : ℂ))⁻¹ := by
      funext w
      simp
    rw [hfun]
    refine HasDerivAt.sum fun n _ => ?_
    have h := ((hasDerivAt_id z).add_const (n : ℂ)).inv (hne n)
    simpa using h
  have hR := (hψdiff hz).add hsum
  have hEq : (fun w : ℂ => Complex.digamma (w + (N : ℂ))) =ᶠ[nhds z]
      (fun w : ℂ => Complex.digamma w + ∑ n ∈ Finset.range N, (w + (n : ℂ))⁻¹) := by
    filter_upwards [hUopen.mem_nhds hz] with w hw
    refine digamma_apply_add_nat w (fun m hc => ?_) N
    have h := congrArg Complex.re hc
    simp only [Complex.neg_re, Complex.natCast_re] at h
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have huniq := hL.unique (hR.congr_of_eventuallyEq hEq)
  rw [huniq, show ∑ n ∈ Finset.range N, (-1 : ℂ) / (z + (n : ℂ)) ^ 2 =
    -∑ n ∈ Finset.range N, ((z + (n : ℂ)) ^ 2)⁻¹ from by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun n _ => by rw [neg_div, one_div]]
  ring

/-- **Vertical trigamma bound.**  For `σ > 0`, `t > 0`:
`‖ψ′(σ+it)‖ ≤ 1/t² + π/(2t)` — the partial sums `Σ (z+n)⁻²` converge to `ψ′(σ+it)` by the
differentiated recurrence and the far-field anchor, and each is bounded by the arctan
comparison. -/
theorem norm_deriv_digamma_vertical_le {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    ‖deriv Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      1 / t ^ 2 + Real.pi / (2 * t) := by
  set z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hz_def
  have hzre : 0 < z.re := by
    rw [hz_def]
    simp [Complex.add_re, Complex.mul_re]
    linarith
  have hpart : ∀ N : ℕ, (∑ n ∈ Finset.range N, ((z + (n : ℂ)) ^ 2)⁻¹) =
      deriv Complex.digamma z - deriv Complex.digamma (z + (N : ℂ)) := by
    intro N
    rw [deriv_digamma_apply_add_nat hzre N]
    ring
  have htend : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, ((z + (n : ℂ)) ^ 2)⁻¹)
      atTop (nhds (deriv Complex.digamma z)) := by
    have h1 : Tendsto (fun N : ℕ =>
        deriv Complex.digamma z - deriv Complex.digamma (z + (N : ℂ)))
        atTop (nhds (deriv Complex.digamma z - 0)) :=
      tendsto_const_nhds.sub (deriv_digamma_add_nat_tendsto z)
    rw [sub_zero] at h1
    exact h1.congr fun N => (hpart N).symm
  have hbound : ∀ N : ℕ, ‖∑ n ∈ Finset.range N, ((z + (n : ℂ)) ^ 2)⁻¹‖ ≤
      1 / t ^ 2 + Real.pi / (2 * t) := by
    intro N
    have hterm : ∀ n : ℕ, ‖((z + (n : ℂ)) ^ 2)⁻¹‖ = 1 / ((σ + n) ^ 2 + t ^ 2) := by
      intro n
      have hzn : z + (n : ℂ) = ((σ + n : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I := by
        rw [hz_def]
        push_cast
        ring
      rw [norm_inv, norm_pow, inv_eq_one_div]
      congr 1
      rw [← Complex.normSq_eq_norm_sq, hzn, Complex.normSq_add_mul_I]
    calc ‖∑ n ∈ Finset.range N, ((z + (n : ℂ)) ^ 2)⁻¹‖
        ≤ ∑ n ∈ Finset.range N, ‖((z + (n : ℂ)) ^ 2)⁻¹‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.range N, 1 / ((σ + n) ^ 2 + t ^ 2) :=
          Finset.sum_congr rfl fun n _ => hterm n
      _ ≤ 1 / t ^ 2 + Real.pi / (2 * t) := sum_inv_sq_add_le hσ.le ht N
  exact le_of_tendsto' htend.norm hbound

end RHTower
