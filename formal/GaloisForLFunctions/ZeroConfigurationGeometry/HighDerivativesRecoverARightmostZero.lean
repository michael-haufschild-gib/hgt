import GaloisForLFunctions.HTGeometry.EntireMultiplicityFactor
import Mathlib.Analysis.Calculus.LogDeriv
import GaloisForLFunctions.RHTower.PositiveRealResolventChart
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# High derivatives recover a rightmost zero

A disk tangent to the rightmost zero line meets that line only at its tangency point.
After peeling the zero there, the analytic cofactor is nonzero on the closed disk and
therefore on a larger disk. Cauchy's bound makes its normalized jets vanish geometrically;
the remaining simple pole recovers the exact multiplicity.
-/

open Complex Filter Metric Set Topology

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- Analytic remainders disappear after normalization by a strictly smaller radius. -/
theorem tendsto_normalized_analytic_jets {g : ℂ → ℂ} {s a : ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall s R)) (ha : ‖a‖ < R) :
    Tendsto (fun k : ℕ => a ^ (k + 1) * iteratedDeriv k g s /
      ((-1 : ℂ) ^ k * (k.factorial : ℂ))) atTop (𝓝 0) := by
  have hR : 0 < R := (norm_nonneg a).trans_lt ha
  obtain ⟨C, hC⟩ := (isCompact_closedBall s R).exists_bound_of_continuousOn
    hg.continuousOn
  have hjet (k : ℕ) : ‖iteratedDeriv k g s‖ ≤ k.factorial * C / R ^ k :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR
      (hg.differentiableOn.diffContOnCl_ball (Subset.refl _))
      (fun z hz => hC z (sphere_subset_closedBall hz))
  have hbound (k : ℕ) :
      ‖a ^ (k + 1) * iteratedDeriv k g s /
        ((-1 : ℂ) ^ k * (k.factorial : ℂ))‖ ≤
      ‖a‖ * C * (‖a‖ / R) ^ k := by
    have hfac : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      Complex.norm_natCast, one_mul]
    calc
      _ ≤ ‖a‖ ^ (k + 1) * (k.factorial * C / R ^ k) / k.factorial :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hjet k) (by positivity)) hfac.le
      _ = _ := by rw [pow_succ, div_pow]; field_simp
  have hlim : Tendsto (fun k : ℕ => ‖a‖ * C * (‖a‖ / R) ^ k) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (div_nonneg (norm_nonneg _) hR.le) ((div_lt_one hR).mpr ha)).const_mul (‖a‖ * C)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) hbound hlim)

/-- A simple pole dominates all high derivatives when its remainder is analytic
on a disk of larger radius. -/
theorem tendsto_normalized_jets_of_simple_pole
    {F g : ℂ → ℂ} {s ρ m : ℂ} {R : ℝ}
    (hs : s ≠ ρ) (hR : ‖s - ρ‖ < R)
    (hg : AnalyticOnNhd ℂ g (closedBall s R))
    (hF : F =ᶠ[𝓝 s] fun z => m / (z - ρ) + g z) :
    Tendsto (fun k : ℕ => (s - ρ) ^ (k + 1) * iteratedDeriv k F s /
      ((-1 : ℂ) ^ k * (k.factorial : ℂ))) atTop (𝓝 m) := by
  have hRpos : 0 < R := (norm_nonneg _).trans_lt hR
  have hgs := hg s (mem_closedBall_self hRpos.le)
  have heq (k : ℕ) :
      (s - ρ) ^ (k + 1) * iteratedDeriv k F s /
        ((-1 : ℂ) ^ k * (k.factorial : ℂ)) =
      m + (s - ρ) ^ (k + 1) * iteratedDeriv k g s /
        ((-1 : ℂ) ^ k * (k.factorial : ℂ)) := by
    have hterm : ContDiffAt ℂ k (fun z : ℂ => m * (z - ρ)⁻¹) s := by
      have hne : s - ρ ≠ 0 := sub_ne_zero.mpr hs
      fun_prop
    have hlocal : F =ᶠ[𝓝 s] fun z => m * (z - ρ)⁻¹ + g z := by
      simpa only [div_eq_mul_inv] using hF
    rw [hlocal.iteratedDeriv_eq, iteratedDeriv_fun_add hterm hgs.contDiffAt]
    rw [_root_.iteratedDeriv_const_mul_field,
      RHTower.iteratedDeriv_inv_sub ρ k s (sub_ne_zero.mpr hs)]
    have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    field_simp
  have hlim := (tendsto_normalized_analytic_jets hg hR).const_add m
  simpa only [add_zero, ← heq] using hlim

/-- A closed disk tangent to a vertical line meets its left half-plane at one point. -/
theorem eq_tangency_point_of_mem_closedBall {ρ z : ℂ} {d : ℝ}
    (hz : z ∈ closedBall (ρ + (d : ℂ)) d) (hre : z.re ≤ ρ.re) : z = ρ := by
  have hn : ‖z - (ρ + (d : ℂ))‖ ≤ d := by
    simpa only [mem_closedBall, dist_eq_norm] using hz
  have hs := Complex.sq_norm (z - (ρ + (d : ℂ)))
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.sub_im, Complex.add_im, Complex.ofReal_im, add_zero] at hs
  have hsq := pow_le_pow_left₀ (norm_nonneg (z - (ρ + (d : ℂ)))) hn 2
  have hreeq : z.re = ρ.re := by
    have hnre := (abs_le.mp (Complex.abs_re_le_norm (z - (ρ + (d : ℂ))))).1
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re] at hnre
    linarith
  have himeq : z.im = ρ.im := by
    rw [hreeq] at hs
    nlinarith [sq_nonneg (z.im - ρ.im)]
  exact Complex.ext hreeq himeq

/-- At a rightmost zero of an entire function, a tangent disk contains no other zero.
Peeling its exact multiplicity therefore gives an analytic remainder on a larger disk. -/
theorem exists_tangent_disk_logDeriv_remainder {f : ℂ → ℂ} {ρ : ℂ} {m : ℕ}
    (hf : ∀ z, AnalyticAt ℂ f z) (hm : analyticOrderAt f ρ = m)
    (hmax : ∀ z, f z = 0 → z.re ≤ ρ.re) {d : ℝ} (hd : 0 < d) :
    ∃ R > d, ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (closedBall (ρ + (d : ℂ)) R) ∧
      logDeriv f =ᶠ[𝓝 (ρ + (d : ℂ))] fun z => (m : ℂ) / (z - ρ) + g z := by
  obtain ⟨u, hu, huρ, hfac⟩ :=
    RHTower.exists_entire_factor_of_analyticOrderAt_eq hf ρ m hm
  have hucont : Continuous u := continuous_iff_continuousAt.mpr fun z => (hu z).continuousAt
  have hopen : IsOpen {z : ℂ | u z ≠ 0} :=
    isOpen_compl_singleton.preimage hucont
  have hclosed : closedBall (ρ + (d : ℂ)) d ⊆ {z : ℂ | u z ≠ 0} := by
    intro z hz hzu
    have hfz : f z = 0 := by rw [hfac z, hzu, mul_zero]
    have hzeq := eq_tangency_point_of_mem_closedBall hz (hmax z hfz)
    exact huρ (hzeq ▸ hzu)
  obtain ⟨ε, hε, hεsub⟩ := (isCompact_closedBall (ρ + (d : ℂ)) d).exists_thickening_subset_open hopen hclosed
  rw [thickening_closedBall hε hd.le] at hεsub
  have hR : d < d + ε / 2 := by linarith
  have hsub : closedBall (ρ + (d : ℂ)) (d + ε / 2) ⊆ {z : ℂ | u z ≠ 0} := by
    exact Subset.trans (closedBall_subset_ball (by linarith)) hεsub
  refine ⟨d + ε / 2, hR, logDeriv u, ?_, ?_⟩
  · intro z hz
    exact (hu z).deriv.div (hu z) (hsub hz)
  · have hs : ρ + (d : ℂ) ≠ ρ := by
      intro heq
      have := congrArg Complex.re heq
      simp only [Complex.add_re, Complex.ofReal_re] at this
      linarith
    have hus : u (ρ + (d : ℂ)) ≠ 0 := hclosed (mem_closedBall_self hd.le)
    filter_upwards [eventually_ne_nhds hs, hucont.continuousAt.eventually_ne hus] with z hz hzu
    have hfeq : f = fun w => (w - ρ) ^ m * u w := funext hfac
    rw [hfeq, logDeriv_mul (f := fun w : ℂ => (w - ρ) ^ m) (g := u) z
      (pow_ne_zero _ (sub_ne_zero.mpr hz)) hzu
      (((differentiableAt_id.sub_const ρ).pow m)) (hu z).differentiableAt,
      logDeriv_fun_pow (by fun_prop) m]
    have hlinear : logDeriv (fun w : ℂ => w - ρ) z = (z - ρ)⁻¹ := by
      have hlinearDeriv : HasDerivAt (fun w : ℂ => w - ρ) 1 z :=
        (hasDerivAt_id z).sub_const ρ
      rw [logDeriv_apply, hlinearDeriv.deriv, one_div]
    rw [hlinear, div_eq_mul_inv]

/-- High logarithmic-derivative jets recover the multiplicity of a rightmost zero
at every centre horizontally to its right. -/
theorem tendsto_logDeriv_jets_at_rightmost_zero {f : ℂ → ℂ} {ρ : ℂ} {m : ℕ}
    (hf : ∀ z, AnalyticAt ℂ f z) (hm : analyticOrderAt f ρ = m)
    (hmax : ∀ z, f z = 0 → z.re ≤ ρ.re) {d : ℝ} (hd : 0 < d) :
    Tendsto (fun k : ℕ => (d : ℂ) ^ (k + 1) *
      iteratedDeriv k (logDeriv f) (ρ + (d : ℂ)) /
      ((-1 : ℂ) ^ k * (k.factorial : ℂ))) atTop (𝓝 (m : ℂ)) := by
  obtain ⟨R, hR, g, hg, heq⟩ := exists_tangent_disk_logDeriv_remainder hf hm hmax hd
  have hdiff : ρ + (d : ℂ) - ρ = (d : ℂ) := by ring
  have hs : ρ + (d : ℂ) ≠ ρ := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re] at this
    linarith
  have hnorm : ‖ρ + (d : ℂ) - ρ‖ < R := by
    simpa only [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd] using hR
  simpa only [hdiff] using tendsto_normalized_jets_of_simple_pole hs hnorm hg heq

#print axioms tendsto_logDeriv_jets_at_rightmost_zero
end GaloisForLFunctions.ZeroConfigurationGeometry
