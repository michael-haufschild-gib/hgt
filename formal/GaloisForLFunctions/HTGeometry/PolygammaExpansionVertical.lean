import GaloisForLFunctions.HTGeometry.TrigammaExpansionVertical
import GaloisForLFunctions.HTGeometry.PolygammaShift
import GaloisForLFunctions.HTGeometry.DigammaAsymptotic

/-!
# The polygamma expansions to any order on a vertical line

Every positive-order digamma jet satisfies `ψ⁽ʲ⁾(z+1) − ψ⁽ʲ⁾(z) = (−1)ʲ j!/z^{j+1}`, so an
approximation `Q(1/z)` has the general defect with the monomial seed `(−1)ʲ j! w^{j+1}`, which
vanishes to second order as soon as `j ≥ 1`.  The far-field decay of the jets along a horizontal
orbit follows from the digamma shift bound by Cauchy's estimate on a small disc.

The telescoping estimate then gives, for every jet order and every prescribed order of accuracy, an
expansion in powers of `1/s` valid uniformly in the abscissa.
-/

open Filter Topology Complex Metric

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **Far-field decay of the digamma jets.**  Every positive-order jet tends to zero along a
horizontal shift orbit. -/
theorem iteratedDeriv_succ_digamma_add_nat_tendsto (j : ℕ) (z : ℂ) :
    Tendsto (fun N : ℕ => iteratedDeriv (j + 1) Complex.digamma (z + (N : ℂ)))
      atTop (nhds 0) := by
  set K : ℝ := ‖z - 1‖ + 1 / 2 with hK_def
  have hK0 : 0 < K := by
    rw [hK_def]
    positivity
  set A : ℝ := ((j + 1).factorial : ℝ) * (2 * K) / (1 / 4) ^ (j + 1) with hA_def
  refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat A)
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
    have happ := RHTower.digamma_shift_diff_bound hN1 hwre hthr'
    rw [sub_add_cancel] at happ
    exact le_trans happ (div_le_div₀ (by linarith) (by linarith) hN0 le_rfl)
  set f : ℂ → ℂ := fun ζ => Complex.digamma ζ - Complex.digamma ((N : ℂ) + 1) with hf_def
  have hdiffOn : DifferentiableOn ℂ f (ball (z + (N : ℂ)) (1 / 2)) := fun ζ hζ =>
    ((RHTower.digamma_analyticOnNhd_re_pos ζ (hball_re ζ hζ)).differentiableAt.sub_const
      _).differentiableWithinAt
  have hdcc : DiffContOnCl ℂ f (ball (z + (N : ℂ)) (1 / 4)) := by
    refine ⟨hdiffOn.mono (ball_subset_ball (by norm_num)), ?_⟩
    rw [closure_ball _ (by norm_num)]
    exact (hdiffOn.mono (closedBall_subset_ball (by norm_num))).continuousOn
  have hC : ∀ ζ ∈ sphere (z + (N : ℂ)) (1 / 4), ‖f ζ‖ ≤ 2 * K / N := by
    intro ζ hζ
    refine hsup ζ ?_
    have hmem : ζ ∈ closedBall (z + (N : ℂ)) (1 / 4) := sphere_subset_closedBall hζ
    exact closedBall_subset_ball (by norm_num) hmem
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (j + 1)
    (by norm_num : (0 : ℝ) < 1 / 4) hdcc hC
  have hjet : iteratedDeriv (j + 1) f = iteratedDeriv (j + 1) Complex.digamma := by
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    congr 1
    funext ζ
    rw [hf_def]
    exact deriv_sub_const _
  rw [hjet] at hcauchy
  refine le_trans hcauchy (le_of_eq ?_)
  rw [hA_def]
  have hpow : ((1 : ℝ) / 4) ^ (j + 1) ≠ 0 := by positivity
  field_simp

/-- **The polygamma expansion to any prescribed order on a vertical line.**  For every jet order and
every `N` there is a polynomial `Q` with zero constant term such that
`ψ⁽ʲ⁺¹⁾(σ+it) = Q(1/(σ+it)) + O(t^{-(N+1)})`, uniformly in the abscissa. -/
theorem exists_iteratedDeriv_digamma_expansion (j N : ℕ) :
    ∃ (Q : Polynomial ℂ) (C T : ℝ), Q.eval 0 = 0 ∧ 0 ≤ C ∧ 2 ≤ T ∧
      ∀ σ t : ℝ, 0 < σ → T ≤ t →
        ‖iteratedDeriv (j + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
            - Q.eval (1 / ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C / t ^ (N + 1) := by
  set c : ℂ := (-1) ^ (j + 1) * (((j + 1).factorial : ℕ) : ℂ) with hc_def
  have hseed : ∀ᶠ w in nhds (0 : ℂ),
      (fun w : ℂ => c * w ^ (j + 2)) w = w ^ (2 : ℕ) * (fun w : ℂ => c * w ^ j) w := by
    filter_upwards with w
    ring
  obtain ⟨Q, g, hQ0, hg, hfac⟩ :=
    exists_genDefect_factor (F := fun w : ℂ => c * w ^ (j + 2))
      (g₀ := fun w : ℂ => c * w ^ j) (analyticAt_const.mul (analyticAt_id.pow j)) hseed N
  obtain ⟨C, r, hC, hr, hbound⟩ := exists_bound_of_factor hg hfac
  refine ⟨Q, 4 * C, max 2 (1 / r), hQ0, by positivity, le_max_left _ _, ?_⟩
  intro σ t hσ ht
  have ht2 : (2 : ℝ) ≤ t := le_trans (le_max_left _ _) ht
  have htr : 1 / r ≤ t := le_trans (le_max_right _ _) ht
  set R : ℂ → ℂ :=
    fun z => iteratedDeriv (j + 1) Complex.digamma z - Q.eval (1 / z) with hR
  set E : ℂ → ℂ := fun z => genDefect (fun w : ℂ => c * w ^ (j + 2)) Q (1 / z) with hE
  have hzre : ∀ n : ℕ, (0 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).re := by
    intro n
    have hval : ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).re = σ + n := by simp
    rw [hval]
    positivity
  have hznorm : ∀ n : ℕ, (2 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ :=
    fun n => le_trans ht2 (norm_vertical_add_nat_ge_im (σ := σ) t n)
  have hzbig : ∀ n : ℕ, 1 / r ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ :=
    fun n => le_trans htr (norm_vertical_add_nat_ge_im (σ := σ) t n)
  have hmain := norm_le_of_shift_defect (R := R) (E := E) (C := C) hσ hC
    (p := N + 2) (by omega) ht2 ?_ ?_ ?_
  · have hpow : (N + 2) - 1 = N + 1 := by omega
    rw [hpow] at hmain
    simpa [hR] using hmain
  · intro n
    set z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) with hz_def
    have hzre' : 0 < z.re := hzre n
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0] at hzre'
      simp at hzre'
    have hz1 : z + 1 ≠ 0 := by
      intro h0
      have hzr : (z + 1).re = 0 := by rw [h0]; simp
      simp only [Complex.add_re, Complex.one_re] at hzr
      linarith
    have hpole : ∀ p : ℕ, z ≠ -(p : ℂ) := by
      intro p hp
      have hzr : z.re = -(p : ℝ) := by rw [hp]; simp
      have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
      linarith
    have hrec := _root_.HTGeometry.iteratedDeriv_digamma_add_nat (j + 1) z hpole 1
    simp only [Nat.cast_one, Finset.sum_range_one, Nat.cast_zero, add_zero] at hrec
    have hshift : (σ : ℂ) + (t : ℂ) * Complex.I + ((n : ℂ) + 1) = z + 1 := by
      rw [hz_def]; ring
    have hquot : 1 / (z + 1) = (1 / z) / (1 + 1 / z) := by
      field_simp
    rw [hshift]
    show (iteratedDeriv (j + 1) Complex.digamma (z + 1) - Q.eval (1 / (z + 1)))
        - (iteratedDeriv (j + 1) Complex.digamma z - Q.eval (1 / z))
      = genDefect (fun w : ℂ => c * w ^ (j + 2)) Q (1 / z)
    rw [hrec, hquot, genDefect]
    have hmon : c * (1 / z) ^ (j + 2) = (-1) ^ (j + 1) * (((j + 1).factorial : ℕ) : ℂ) / z ^ (j + 2)
        := by
      rw [hc_def, div_pow, one_pow]
      field_simp
    rw [hmon]
    ring
  · intro n
    have hwnorm : ‖1 / ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))‖
        = 1 / ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := by
      rw [norm_div, norm_one]
    have hzpos : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := by
      have := hznorm n
      linarith
    have hwle : ‖1 / ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))‖ ≤ r := by
      rw [hwnorm, div_le_iff₀ hzpos]
      have hb := hzbig n
      rw [div_le_iff₀ hr] at hb
      nlinarith
    have hb := hbound _ hwle
    rw [hE]
    refine le_trans hb ?_
    rw [hwnorm, div_pow, one_pow, mul_one_div]
  · have hjet : Tendsto (fun n : ℕ =>
        iteratedDeriv (j + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)))
        atTop (nhds 0) := iteratedDeriv_succ_digamma_add_nat_tendsto j _
    have hinv : Tendsto (fun n : ℕ => 1 / ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)))
        atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _)
        (g := fun n : ℕ => 1 / (σ + n)) (fun n => ?_) ?_
      · have hge : σ + n ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := by
          simpa using norm_vertical_add_nat_ge_re (σ := σ) t n
        have hpos : (0 : ℝ) < σ + n := by positivity
        rw [norm_div, norm_one]
        rw [div_le_div_iff₀ (by linarith) hpos]
        nlinarith
      · have hdiv : Tendsto (fun n : ℕ => σ + (n : ℝ)) atTop atTop :=
          tendsto_atTop_add_const_left _ σ tendsto_natCast_atTop_atTop
        exact Tendsto.congr (fun n => by simp [one_div]) hdiv.inv_tendsto_atTop
    have hpoly : Tendsto (fun n : ℕ => Q.eval (1 / ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))))
        atTop (nhds 0) := by
      have hcont : ContinuousAt (fun z : ℂ => Q.eval z) 0 :=
        (analyticAt_polyEval Q 0).continuousAt
      have hcomp := hcont.tendsto.comp hinv
      rw [hQ0] at hcomp
      simpa [Function.comp_def] using hcomp
    have hcomb := hjet.sub hpoly
    rw [sub_zero] at hcomb
    refine hcomb.congr fun n => ?_
    rw [hR]

end

end GaloisForLFunctions.HTGeometry
