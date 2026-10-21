import GaloisForLFunctions.RHTower.ZetaVoroninUniversalityOnSmallDiscs
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionUnrestricted
import GaloisForLFunctions.RHTower.BacklundLindelofConverse
import GaloisForLFunctions.RHTower.XiWardCapGlobalIntegrability

/-!
# Recurrence of `ζ` at every point of the strip, modulo its zeros

The fixed-base recurrence of `ζ` on a disc about a point `z₀` of the strip `1/2 < Re z₀ < 1` was
proved under a zero-free premise on a neighbourhood of the disc.  This file measures that premise
exactly and discharges it wherever the corpus allows.

1. **The premise is one point** (`exists_zetaDiscStronglyRecurrentOn_iff_ne_zero`).  A point of
   the strip carries a disc on which `ζ` is strongly recurrent if and only if `ζ(z₀) ≠ 0`.  A
   nonzero value gives a zero-free ball by continuity; conversely self-returns about a zero have
   density zero.  The head-target form carries the margins (`…_headTarget_iff_ne_zero`).
2. **An explicit recurrence region** (`zetaDiscStronglyRecurrentOn_of_mem_zeroFreeRegion`).  With
   `a = 1/(58 log(|Im z₀| + 5))` and `1 − a < Re z₀ < 1`, the ball of radius `(Re z₀ − 1 + a)/2`
   about `z₀` is zero-free, and `ζ` is strongly recurrent on an explicit closed disc about `z₀`.
3. **All but countably many heights** (`countable_setOf_not_exists_zetaDiscStronglyRecurrentOn`).
   On every vertical line `Re z = σ` of the strip the heights without a recurrent disc are the
   heights of zeros, a countable set; the heights with a recurrent disc fill `[0, T]` up to
   measure zero.
4. **Recurrence modulo the local zero divisor** (`exists_zeta_recurrence_modulo_zeros`).  At every
   point `z₀` of the strip, with no zero-free premise: there are a radius `r`, the finite set `S`
   of zeros of `ζ` near `z₀` with multiplicities `D`, and an analytic nonvanishing cofactor `g`
   with `ζ = ∏_{u ∈ S}(z − u)^{D(u)} · g` on `|z − z₀| ≤ r`, such that `ζ(· + iτ)` approaches `g`
   on the disc within any `ε` on a set of heights of positive lower density.  The factorization
   is the corpus disc factorization of `ζ` about a nearby nonvanishing point; the approximation is
   the universality theorem applied to `g`.  At a zero `ρ₀` the set `S` contains `ρ₀`
   (`exists_zeta_recurrence_modulo_zeros_of_zero`): the orbit erases the local zero divisor and
   returns to the cofactor, while the self-target is returned to only on a density-zero set.

5. **The Dirichlet heads approximate the zero-erased target, uniformly in the cutoff**
   (`exists_uniform_pos_density_headTarget_cofactor`).  Subtracting the Carlson tail-bad set from
   the return set of the cofactor gives, at every point of the strip, a positive lower density of
   heights at which the head `Σ_{n ≤ M} n^{−z−iτ}` is within `ε` of `g` on the disc, with one
   constant for all large `M`.  This is the cutoff-uniform head-target density that is equivalent
   to fixed-base recurrence, obtained for the base target with its local zero divisor erased.

Together: strong recurrence at `z₀` holds exactly when the local zero divisor is trivial, and the
Riemann hypothesis is the statement that the divisor `S` is empty at every point of the strip.
-/

open Complex Filter Topology Finset Metric MeasureTheory Set
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal

noncomputable section

namespace RHTower

/-! ## 1. Recurrence at a point is nonvanishing at the point -/

/-- **The zero-free premise is one point.**  A point `z₀` of the strip carries a closed disc on
which `ζ` is strongly recurrent iff `ζ(z₀) ≠ 0`. -/
theorem exists_zetaDiscStronglyRecurrentOn_iff_ne_zero {z₀ : ℂ} (h1 : 1 / 2 < z₀.re)
    (h2 : z₀.re < 1) :
    (∃ r > 0, ZetaDiscStronglyRecurrentOn (closedBall z₀ r)) ↔ riemannZeta z₀ ≠ 0 := by
  constructor
  · exact riemannZeta_ne_zero_of_exists_zetaDiscStronglyRecurrentOn h1 h2
  · intro hz
    have hne1 : z₀ ≠ 1 := by
      intro h
      rw [h] at h2
      simp at h2
    have hcont : ContinuousAt riemannZeta z₀ := (differentiableAt_riemannZeta hne1).continuousAt
    obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually_ne hz)
    obtain ⟨r, hr, -, -, hrec⟩ := exists_zetaDiscStronglyRecurrentOn_of_zeroFree h1 h2 hR
      fun z hz' => hball (by rwa [mem_ball] at hz')
    exact ⟨r, hr, hrec⟩

/-- **Head-target form with margins.**  A point `z₀` of the strip carries a closed disc with the
margins `1/2 < Re z₀ − 2r`, `Re z₀ + 2r < 1` on which the head-target heights have cutoff-uniform
positive lower density iff `ζ(z₀) ≠ 0`. -/
theorem exists_headTargetUniformlyDense_iff_ne_zero {z₀ : ℂ} (h1 : 1 / 2 < z₀.re)
    (h2 : z₀.re < 1) :
    (∃ r > 0, 1 / 2 < z₀.re - 2 * r ∧ z₀.re + 2 * r < 1 ∧
      HeadTargetUniformlyDense (closedBall z₀ r)) ↔ riemannZeta z₀ ≠ 0 := by
  constructor
  · rintro ⟨r, hr, hr0, hr1, hdense⟩
    exact riemannZeta_ne_zero_of_exists_zetaDiscStronglyRecurrentOn h1 h2
      ⟨r, hr, (zetaDiscStronglyRecurrentOn_iff_headTargetUniformlyDense hr hr0 hr1).mpr hdense⟩
  · intro hz
    have hne1 : z₀ ≠ 1 := by
      intro h
      rw [h] at h2
      simp at h2
    have hcont : ContinuousAt riemannZeta z₀ := (differentiableAt_riemannZeta hne1).continuousAt
    obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually_ne hz)
    exact exists_headTargetUniformlyDense_of_zeroFree h1 h2 hR
      fun z hz' => hball (by rwa [mem_ball] at hz')

/-! ## 2. An explicit recurrence region -/

/-- **Explicit recurrence radius from a zero-free ball.**  If `ζ` has no zero on `|z − z₀| < R`,
then `ζ` is strongly recurrent on the closed disc of radius
`min(R/4, (Re z₀ − 1/2)/4, (1 − Re z₀)/8)/2` about `z₀`. -/
theorem zetaDiscStronglyRecurrentOn_explicit_of_zeroFree {z₀ : ℂ} (h1 : 1 / 2 < z₀.re)
    (h2 : z₀.re < 1) {R : ℝ} (hR : 0 < R) (hζ : ∀ z ∈ ball z₀ R, riemannZeta z ≠ 0) :
    ZetaDiscStronglyRecurrentOn (closedBall z₀
      (min (R / 4) (min ((z₀.re - 1 / 2) / 4) ((1 - z₀.re) / 8)) * (1 / 2))) := by
  set ρ : ℝ := min (R / 4) (min ((z₀.re - 1 / 2) / 4) ((1 - z₀.re) / 8)) with hρdef
  have hρ : 0 < ρ := lt_min (by positivity) (lt_min (by linarith) (by linarith))
  have hρR : ρ ≤ R / 4 := min_le_left _ _
  have hρ1 : ρ ≤ (z₀.re - 1 / 2) / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hρ2 : ρ ≤ (1 - z₀.re) / 8 := (min_le_right _ _).trans (min_le_right _ _)
  exact zetaDiscStronglyRecurrentOn_of_zeroFree z₀ hρ h1.le (by linarith) (by linarith)
    (R₂ := 2) (by norm_num) (by linarith)
    (fun z hz => hζ z (ball_subset_ball (by linarith) hz))
    (by norm_num) (by norm_num) (by linarith) (by linarith)

/-- **The explicit zero-free ball of a point of the zero-free region.**  With
`a = 1/(58 log(|Im z₀| + 5))` and `1 − a < Re z₀ < 1`, every `z` with `|z − z₀| < (Re z₀ − 1 + a)/2`
has `Re z > 1 − 1/(58 log(|Im z| + 4))`, so `ζ(z) ≠ 0`. -/
theorem riemannZeta_ne_zero_on_ball_of_mem_zeroFreeRegion {z₀ : ℂ} (h1 : 1 / 2 < z₀.re)
    (h2 : z₀.re < 1) (hreg : 1 - 1 / 58 / Real.log (|z₀.im| + 5) < z₀.re) :
    ∀ z ∈ ball z₀ ((z₀.re - 1 + 1 / 58 / Real.log (|z₀.im| + 5)) / 2), riemannZeta z ≠ 0 := by
  intro z hz
  set a : ℝ := 1 / 58 / Real.log (|z₀.im| + 5) with ha
  have hlog5 : 0 < Real.log (|z₀.im| + 5) := Real.log_pos (by linarith [abs_nonneg z₀.im])
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 / 2 := by
    have hl : 1 ≤ Real.log (|z₀.im| + 5) := by
      rw [Real.le_log_iff_exp_le (by linarith [abs_nonneg z₀.im])]
      linarith [Real.exp_one_lt_d9, abs_nonneg z₀.im]
    rw [ha, div_div, div_le_iff₀ (by positivity)]
    linarith
  rw [mem_ball, dist_eq_norm] at hz
  have hre := abs_le.mp (Complex.abs_re_le_norm (z - z₀))
  have him := abs_le.mp (Complex.abs_im_le_norm (z - z₀))
  rw [Complex.sub_re] at hre
  rw [Complex.sub_im] at him
  have hR : (z₀.re - 1 + a) / 2 < 1 / 2 := by linarith
  have himz : |z.im| < |z₀.im| + 1 := by
    have h := abs_sub_abs_le_abs_sub z.im z₀.im
    have h' : |z.im - z₀.im| ≤ ‖z - z₀‖ := Complex.abs_im_le_norm (z - z₀) |>.trans_eq' (by
      rw [Complex.sub_im])
    linarith
  have hlogz : 0 < Real.log (|z.im| + 4) := Real.log_pos (by linarith [abs_nonneg z.im])
  have hloglt : Real.log (|z.im| + 4) < Real.log (|z₀.im| + 5) :=
    Real.log_lt_log (by linarith [abs_nonneg z.im]) (by linarith)
  have hb : a < 1 / 58 / Real.log (|z.im| + 4) := by
    rw [ha]
    exact div_lt_div_of_pos_left (by norm_num) hlogz hloglt
  have hrez : 1 - 1 / 58 / Real.log (|z.im| + 4) < z.re := by linarith
  exact riemannZeta_ne_zero_of_lt_re (by linarith) hrez

/-- **Explicit recurrence region.**  Every `z₀` with
`1 − 1/(58 log(|Im z₀| + 5)) < Re z₀ < 1` carries an explicit closed disc on which `ζ` is strongly
recurrent, unconditionally. -/
theorem zetaDiscStronglyRecurrentOn_of_mem_zeroFreeRegion {z₀ : ℂ} (h1 : 1 / 2 < z₀.re)
    (h2 : z₀.re < 1) (hreg : 1 - 1 / 58 / Real.log (|z₀.im| + 5) < z₀.re) :
    ZetaDiscStronglyRecurrentOn (closedBall z₀
      (min ((z₀.re - 1 + 1 / 58 / Real.log (|z₀.im| + 5)) / 2 / 4)
        (min ((z₀.re - 1 / 2) / 4) ((1 - z₀.re) / 8)) * (1 / 2))) :=
  zetaDiscStronglyRecurrentOn_explicit_of_zeroFree h1 h2 (by linarith)
    (riemannZeta_ne_zero_on_ball_of_mem_zeroFreeRegion h1 h2 hreg)

/-- **Points of the explicit zero-free region carry a recurrent disc** (the form with the
unshifted region `1 − 1/(58 log(|Im z₀| + 4)) < Re z₀`). -/
theorem exists_zetaDiscStronglyRecurrentOn_of_mem_zeroFreeRegion {z₀ : ℂ} (h1 : 1 / 2 < z₀.re)
    (h2 : z₀.re < 1) (hreg : 1 - 1 / 58 / Real.log (|z₀.im| + 4) < z₀.re) :
    ∃ r > 0, ZetaDiscStronglyRecurrentOn (closedBall z₀ r) :=
  (exists_zetaDiscStronglyRecurrentOn_iff_ne_zero h1 h2).mpr
    (riemannZeta_ne_zero_of_lt_re (by linarith) hreg)

/-! ## 3. All but countably many heights carry a recurrent disc -/

/-- **The exceptional heights of a vertical line are countable.**  On `Re z = σ`, `1/2 < σ < 1`,
the heights `t` such that no disc about `σ + it` is strongly recurrent are the heights of the zeros
of `ζ` on the line, a countable set. -/
theorem countable_setOf_not_exists_zetaDiscStronglyRecurrentOn {σ : ℝ} (h1 : 1 / 2 < σ)
    (h2 : σ < 1) :
    {t : ℝ | ¬ ∃ r > 0, ZetaDiscStronglyRecurrentOn (closedBall ((σ : ℂ) + t * I) r)}.Countable := by
  refine (countable_setOf_riemannZeta_line_eq_zero (by linarith) h2).mono fun t ht => ?_
  simp only [Set.mem_setOf_eq] at ht ⊢
  by_contra hne
  have hre : ((σ : ℂ) + t * I).re = σ := by simp
  exact ht ((exists_zetaDiscStronglyRecurrentOn_iff_ne_zero (by rw [hre]; exact h1)
    (by rw [hre]; exact h2)).mpr hne)

/-- The exceptional heights have Lebesgue measure zero. -/
theorem volume_setOf_not_exists_zetaDiscStronglyRecurrentOn {σ : ℝ} (h1 : 1 / 2 < σ)
    (h2 : σ < 1) :
    volume {t : ℝ | ¬ ∃ r > 0, ZetaDiscStronglyRecurrentOn (closedBall ((σ : ℂ) + t * I) r)}
      = 0 :=
  (countable_setOf_not_exists_zetaDiscStronglyRecurrentOn h1 h2).measure_zero _

/-- **Almost every height carries a recurrent disc.**  On every window `[0, T]` the heights `t`
with a strongly recurrent disc about `σ + it` have full measure `T`. -/
theorem volume_setOf_exists_zetaDiscStronglyRecurrentOn_inter_Icc {σ : ℝ} (h1 : 1 / 2 < σ)
    (h2 : σ < 1) (T : ℝ) :
    volume ({t : ℝ | ∃ r > 0, ZetaDiscStronglyRecurrentOn (closedBall ((σ : ℂ) + t * I) r)}
      ∩ Icc 0 T) = ENNReal.ofReal T := by
  set G : Set ℝ := {t : ℝ | ∃ r > 0, ZetaDiscStronglyRecurrentOn (closedBall ((σ : ℂ) + t * I) r)}
    with hG
  have hbad := volume_setOf_not_exists_zetaDiscStronglyRecurrentOn h1 h2
  apply le_antisymm
  · exact (measure_mono inter_subset_right).trans (by rw [Real.volume_Icc, sub_zero])
  · calc ENNReal.ofReal T = volume (Icc (0 : ℝ) T) := by rw [Real.volume_Icc, sub_zero]
      _ ≤ volume ((G ∩ Icc 0 T) ∪ {t : ℝ | ¬ ∃ r > 0,
            ZetaDiscStronglyRecurrentOn (closedBall ((σ : ℂ) + t * I) r)}) := by
          refine measure_mono fun t ht => ?_
          by_cases h : ∃ r > 0, ZetaDiscStronglyRecurrentOn (closedBall ((σ : ℂ) + t * I) r)
          · exact Or.inl ⟨h, ht⟩
          · exact Or.inr h
      _ ≤ volume (G ∩ Icc 0 T) + volume {t : ℝ | ¬ ∃ r > 0,
            ZetaDiscStronglyRecurrentOn (closedBall ((σ : ℂ) + t * I) r)} := measure_union_le _ _
      _ = volume (G ∩ Icc 0 T) := by rw [hbad, add_zero]

/-! ## 4. Recurrence modulo the local zero divisor -/

/-- **Recurrence modulo the local zero divisor, at every point of the strip.**  For
`1/2 < Re z₀ < 1`, without any zero-free premise, there are `r > 0` with `1/2 < Re z₀ − 4r`,
`Re z₀ + 4r < 1`, a finite set `S` of zeros of `ζ` in `|z − z₀| < 8r` with multiplicities `D ≥ 1`,
and an analytic nonvanishing cofactor `g` with `ζ(z) = ∏_{u ∈ S}(z − u)^{D(u)} · g(z)` on the closed
disc `|z − z₀| ≤ r` (every zero of `ζ` on that disc lies in `S`), such that for every `ε > 0` the
heights at which `ζ(· + iτ)` is within `ε` of `g` on the disc have positive lower density. -/
theorem exists_zeta_recurrence_modulo_zeros {z₀ : ℂ} (h1 : 1 / 2 < z₀.re) (h2 : z₀.re < 1) :
    ∃ r > 0, 1 / 2 < z₀.re - 4 * r ∧ z₀.re + 4 * r < 1 ∧
      ∃ (S : Finset ℂ) (D : ℂ → ℕ) (g : ℂ → ℂ),
        (∀ u ∈ S, u ∈ ball z₀ (8 * r) ∧ riemannZeta u = 0 ∧ 1 ≤ D u) ∧
        (∀ z ∈ closedBall z₀ r, g z ≠ 0 ∧
          riemannZeta z = (∏ u ∈ S, (z - u) ^ D u) * g z) ∧
        (∀ z ∈ closedBall z₀ r, riemannZeta z = 0 → z ∈ S) ∧
        ∀ ε > 0, ∃ c > 0, ∀ᶠ T : ℝ in atTop,
          ENNReal.ofReal (c * T) ≤ volume (zetaTargetReturnSet g (closedBall z₀ r) ε ∩ Icc 0 T) := by
  classical
  -- the Pechersky scale of the point
  set ρ : ℝ := min ((z₀.re - 1 / 2) / 4) ((1 - z₀.re) / 8) with hρdef
  have hρ : 0 < ρ := lt_min (by linarith) (by linarith)
  have hρ1 : ρ ≤ (z₀.re - 1 / 2) / 4 := min_le_left _ _
  have hρ2 : ρ ≤ (1 - z₀.re) / 8 := min_le_right _ _
  -- an isolating circle of radius `r' ≤ ρ` with a positive floor, hence a nonvanishing point
  obtain ⟨r', hr', hr'ρ, -, -, m, hm0, hm⟩ := exists_zetaIsolatingDisc_le h1 h2 hρ
  set c' : ℂ := z₀ + (r' : ℂ) with hc'
  have hc'sphere : c' ∈ sphere z₀ r' := by
    rw [mem_sphere, dist_eq_norm, hc', add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg hr'.le]
  have hc'ne : riemannZeta c' ≠ 0 := by
    intro h
    have := hm c' hc'sphere
    rw [h, norm_zero] at this
    linarith
  have hc're : c'.re = z₀.re + r' := by simp [hc']
  -- the disc factorization of `ζ` about the nonvanishing point `c'`
  have hB : ∀ z ∈ ball c' (4 * r'), 0 < z.re ∧ z ≠ 1 := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have hre := abs_le.mp (Complex.abs_re_le_norm (z - c'))
    rw [Complex.sub_re, hc're] at hre
    refine ⟨by linarith, fun h => ?_⟩
    subst h
    rw [Complex.one_re] at hre
    linarith [hre.2]
  obtain ⟨S, D, g, hS, hgan, hg0, hfac⟩ :=
    BacklundConverse.exists_zeta_factor_ball (c := c') (R := 3 * r') (R₂ := 4 * r')
      (by positivity) (by linarith) hB hc'ne
  -- the small disc about `z₀` lies in the factorization disc
  have hsub : ∀ z, ‖z - z₀‖ < 2 * r' → z ∈ ball c' (3 * r') := by
    intro z hz
    rw [mem_ball, dist_eq_norm]
    calc ‖z - c'‖ = ‖(z - z₀) - (r' : ℂ)‖ := by rw [hc']; ring_nf
      _ ≤ ‖z - z₀‖ + ‖(r' : ℂ)‖ := norm_sub_le _ _
      _ < 2 * r' + r' := by
          rw [Complex.norm_real, Real.norm_of_nonneg hr'.le]
          linarith
      _ = 3 * r' := by ring
  refine ⟨r' * (1 / 2), by positivity, by linarith, by linarith, S, D, g, ?_, ?_, ?_, ?_⟩
  · -- the zeros of the divisor
    intro u hu
    obtain ⟨huball, hu0, hD, -⟩ := hS u hu
    refine ⟨?_, hu0, hD⟩
    rw [mem_ball, dist_eq_norm] at huball ⊢
    calc ‖u - z₀‖ = ‖(u - c') + (r' : ℂ)‖ := by rw [hc']; ring_nf
      _ ≤ ‖u - c'‖ + ‖(r' : ℂ)‖ := norm_add_le _ _
      _ < 3 * r' + r' := by
          rw [Complex.norm_real, Real.norm_of_nonneg hr'.le]
          linarith
      _ = 8 * (r' * (1 / 2)) := by ring
  · -- the factorization on the small disc
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have hz' : z ∈ ball c' (3 * r') := hsub z (by linarith)
    exact ⟨hg0 z hz', hfac z hz'⟩
  · -- every zero of `ζ` on the small disc lies in `S`
    intro z hz hζz
    rw [mem_closedBall, dist_eq_norm] at hz
    have hz' : z ∈ ball c' (3 * r') := hsub z (by linarith)
    have hprod : (∏ u ∈ S, (z - u) ^ D u) = 0 := by
      have h := hfac z hz'
      rw [hζz] at h
      exact (mul_eq_zero.mp h.symm).resolve_right (hg0 z hz')
    obtain ⟨u, hu, hzu⟩ := Finset.prod_eq_zero_iff.mp hprod
    have hD : D u ≠ 0 := by
      have := (hS u hu).2.2.1
      omega
    rw [pow_eq_zero_iff hD, sub_eq_zero] at hzu
    rw [hzu]
    exact hu
  · -- universality with the cofactor as target
    intro ε hε
    have hgan' : AnalyticOnNhd ℂ g (ball z₀ (r' * 2)) := hgan.mono fun z hz => by
      rw [mem_ball, dist_eq_norm] at hz
      exact hsub z (by linarith)
    have hg0' : ∀ z ∈ ball z₀ (r' * 2), g z ≠ 0 := fun z hz => by
      rw [mem_ball, dist_eq_norm] at hz
      exact hg0 z (hsub z (by linarith))
    exact exists_pos_density_zetaTargetReturnSet_of_analyticOnNhd z₀ hr' h1.le (by linarith)
      (by linarith) (R₂ := 2) (by norm_num) hgan' hg0' (r₁ := 1 / 2) (by norm_num)
      (by norm_num) (by linarith) (by linarith) hε

/-- **At an off-line zero the orbit erases the zero divisor.**  If `ζ(ρ₀) = 0` with
`1/2 < Re ρ₀ < 1`, the divisor `S` of the local factorization contains `ρ₀`, and `ζ(· + iτ)`
approaches the nonvanishing cofactor `g` on the disc about `ρ₀` at positive lower density of
heights, while it approaches `ζ` itself there only on a density-zero set. -/
theorem exists_zeta_recurrence_modulo_zeros_of_zero {ρ₀ : ℂ} (h1 : 1 / 2 < ρ₀.re)
    (h2 : ρ₀.re < 1) (hρ₀ : riemannZeta ρ₀ = 0) :
    ∃ r > 0, ∃ (S : Finset ℂ) (D : ℂ → ℕ) (g : ℂ → ℂ), ρ₀ ∈ S ∧
      (∀ u ∈ S, riemannZeta u = 0 ∧ 1 ≤ D u) ∧
      (∀ z ∈ closedBall ρ₀ r, g z ≠ 0 ∧
        riemannZeta z = (∏ u ∈ S, (z - u) ^ D u) * g z) ∧
      ∀ ε > 0, ∃ c > 0, ∀ᶠ T : ℝ in atTop,
        ENNReal.ofReal (c * T) ≤ volume (zetaTargetReturnSet g (closedBall ρ₀ r) ε ∩ Icc 0 T) := by
  obtain ⟨r, hr, -, -, S, D, g, hS, hfac, hmem, huniv⟩ := exists_zeta_recurrence_modulo_zeros h1 h2
  exact ⟨r, hr, S, D, g, hmem ρ₀ (mem_closedBall_self hr.le) hρ₀,
    fun u hu => ⟨(hS u hu).2.1, (hS u hu).2.2⟩, hfac, huniv⟩

/-! ## 5. The Dirichlet heads approximate the zero-erased target at every point -/

/-- Target heights of `ζ` that are tail-good are head-target heights, for any target `g`. -/
theorem zetaTargetReturnSet_diff_discTailBadSet_subset_headTarget (M : ℕ) (g : ℂ → ℂ) (c : ℂ)
    (r ε ε' : ℝ) :
    zetaTargetReturnSet g (closedBall c r) ε \ discTailBadSet M c r ε' ⊆
      {τ : ℝ | ∀ z ∈ closedBall c r,
        ‖edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I) - g z‖ < ε' + ε} := by
  rintro τ ⟨hret, hgood⟩ z hz
  have htail : ‖zetaTailFun M (z + τ * I)‖ < ε' := by
    by_contra hcon
    exact hgood ⟨z, hz, not_lt.mp hcon⟩
  have hr := hret z hz
  have hid : edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I) - g z =
      -(zetaTailFun M (z + τ * I)) + (riemannZeta (z + τ * I) - g z) := by
    unfold zetaTailFun
    ring
  rw [hid]
  refine (norm_add_le _ _).trans_lt ?_
  rw [norm_neg]
  exact add_lt_add htail hr

/-- **The Dirichlet heads approximate the zero-erased `ζ` at every point, uniformly in the
cutoff.**  At every `z₀` of the strip, with the local factorization `ζ = P · g` on `|z − z₀| ≤ r`
(`S` the local zeros, `g` analytic and nonvanishing): for every `ε > 0` there is `c > 0` such that
for all large `M` the heights at which the head `Σ_{n ≤ M} n^{−z−iτ}` is within `ε` of `g` on the
disc have lower density at least `c`.  This is the cutoff-uniform head-target density equivalent to
fixed-base recurrence, for the base target with its local zero divisor erased. -/
theorem exists_uniform_pos_density_headTarget_cofactor {z₀ : ℂ} (h1 : 1 / 2 < z₀.re)
    (h2 : z₀.re < 1) :
    ∃ r > 0, ∃ (S : Finset ℂ) (D : ℂ → ℕ) (g : ℂ → ℂ),
      (∀ u ∈ S, riemannZeta u = 0 ∧ 1 ≤ D u) ∧
      (∀ z ∈ closedBall z₀ r, g z ≠ 0 ∧
        riemannZeta z = (∏ u ∈ S, (z - u) ^ D u) * g z) ∧
      ∀ ε > 0, ∃ c > 0, ∀ᶠ M : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
        ENNReal.ofReal (c * T) ≤ volume ({τ : ℝ | ∀ z ∈ closedBall z₀ r,
          ‖edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I) - g z‖ < ε} ∩ Icc 0 T) := by
  obtain ⟨r, hr, hr0, hr1, S, D, g, hS, hfac, -, huniv⟩ :=
    exists_zeta_recurrence_modulo_zeros h1 h2
  refine ⟨r, hr, S, D, g, fun u hu => ⟨(hS u hu).2.1, (hS u hu).2.2⟩, hfac, fun ε hε => ?_⟩
  obtain ⟨c, hc, hev⟩ := huniv (ε / 2) (half_pos hε)
  refine ⟨c / 2, half_pos hc, ?_⟩
  have hbad := eventually_eventually_volume_discTailBadSet_le (c := z₀) hr (by linarith)
    (by linarith) (half_pos hε) (half_pos hc)
  filter_upwards [hbad] with M hM
  filter_upwards [hev, hM, eventually_ge_atTop (0 : ℝ)] with T hT1 hT2 hT0
  have hsub := zetaTargetReturnSet_diff_discTailBadSet_subset_headTarget M g z₀ r (ε / 2) (ε / 2)
  rw [add_halves] at hsub
  exact (ofReal_half_le_volume_diff_inter hc hT0 hT1 hT2).trans
    (measure_mono (inter_subset_inter_left _ hsub))

end RHTower
