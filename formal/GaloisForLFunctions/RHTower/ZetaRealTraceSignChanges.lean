import GaloisForLFunctions.RHTower.ZetaHorizontalArgument
import GaloisForLFunctions.HTGeometry.DistinctZerosLeDivisor

/-!
# The sign changes of `Re ζ` at a fixed height are `O(log T)`

The real trace `F_T` is analytic on a disc about `2` and nonzero at the centre, so its order is
finite everywhere on the disc and its zero set there is finite.  Every sign change of
`Re ζ(σ + iT)` on `[1/2, 2]` is such a zero, and distinct zeros are counted by the divisor, which
Jensen bounds by `O(log T)`.
-/

open Complex Metric Set MeromorphicOn
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

theorem zetaRealTrace_order_ne_top {T : ℝ} (hT : 2 < T) {z : ℂ}
    (hz : z ∈ Metric.ball (2 : ℂ) (7 / 4)) :
    analyticOrderAt (zetaRealTrace T) z ≠ ⊤ := by
  have hball : AnalyticOnNhd ℂ (zetaRealTrace T) (Metric.ball (2 : ℂ) (7 / 4)) := by
    intro w hw
    refine analyticAt_zetaRealTrace hT ?_
    have h := Complex.abs_im_le_norm (w - 2)
    have him : (w - 2).im = w.im := by simp
    rw [him] at h
    have hlt : ‖w - 2‖ < 7 / 4 := by
      rw [mem_ball, dist_eq_norm] at hw
      exact hw
    linarith
  intro htop
  have hev : zetaRealTrace T =ᶠ[nhds z] 0 := analyticOrderAt_eq_top.mp htop
  have hconn : IsPreconnected (Metric.ball (2 : ℂ) (7 / 4)) :=
    (convex_ball (2 : ℂ) (7 / 4)).isPreconnected
  have hopen : IsOpen (Metric.ball (2 : ℂ) (7 / 4)) := isOpen_ball
  have hzero := hball.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz hev
  have h2 : (2 : ℂ) ∈ Metric.ball (2 : ℂ) (7 / 4) := by
    rw [mem_ball, dist_self]
    norm_num
  exact zetaRealTrace_two_ne_zero T (hzero h2)

/-- The real zeros of the real trace in the counting disc form a finite set. -/
theorem zetaRealTrace_real_zeros_finite {T : ℝ} (hT : 2 < T) :
    {x : ℝ | (x : ℂ) ∈ closedBall (2 : ℂ) |(3 / 2 : ℝ)| ∧ zetaRealTrace T (x : ℂ) = 0}.Finite := by
  have hKsub : closedBall (2 : ℂ) |(3 / 2 : ℝ)| ⊆ Metric.ball (2 : ℂ) (7 / 4) := by
    intro w hw
    rw [mem_closedBall, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hw
    rw [mem_ball]
    linarith
  have hK : AnalyticOnNhd ℂ (zetaRealTrace T) (closedBall (2 : ℂ) |(3 / 2 : ℝ)|) :=
    analyticOnNhd_zetaRealTrace hT |>.mono (by
      intro w hw
      rw [mem_closedBall, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hw
      rw [mem_closedBall, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 4)]
      linarith)
  have hfin := (MeromorphicOn.divisor (zetaRealTrace T)
    (closedBall (2 : ℂ) |(3 / 2 : ℝ)|)).finiteSupport (isCompact_closedBall ..)
  have hcplx : {u : ℂ | u ∈ closedBall (2 : ℂ) |(3 / 2 : ℝ)| ∧ zetaRealTrace T u = 0}.Finite := by
    refine hfin.subset ?_
    intro u hu
    rw [Function.mem_support]
    have h1 := one_le_divisor_of_zero hK hu.1 hu.2
      (zetaRealTrace_order_ne_top hT (hKsub hu.1))
    omega
  refine Set.Finite.ofFinset (hcplx.toFinset.preimage (fun x : ℝ => (x : ℂ))
    (fun a _ b _ h => Complex.ofReal_inj.mp h)) ?_
  intro x
  rw [Finset.mem_preimage, Set.Finite.mem_toFinset]
  rfl

/-! ## The horizontal bound -/

/-- **`S(T) = O(log T)` in integral form.**  The argument increment of `ζ` across the segment
`[1/2, 2]` at height `T` is `O(log T)`. -/
theorem exists_horizontal_zeta_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 4 ≤ T →
      (∀ x : ℝ, xi ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      |∫ u in (1 / 2 : ℝ)..2, (logDeriv riemannZeta ((u : ℂ) + (T : ℂ) * I)).im|
        ≤ c * Real.log T := by
  classical
  obtain ⟨c₀, hc₀, hcount⟩ := exists_zetaRealTrace_count_bound
  refine ⟨(c₀ + 1) * Real.pi, by positivity, fun T hT hne => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have hT2 : (2 : ℝ) < T := by linarith
  have hTne : T ≠ 0 := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have hζne : ∀ x : ℝ, riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0 :=
    zeta_horizontal_ne_zero hTne hne
  set Z : Finset ℝ := (zetaRealTrace_real_zeros_finite hT2).toFinset with hZdef
  have hZmem : ∀ x ∈ Set.Ioo (1 / 2 : ℝ) 2,
      (riemannZeta ((x : ℂ) + (T : ℂ) * I)).re = 0 → x ∈ Z := by
    intro x hx hzero
    rw [hZdef, Set.Finite.mem_toFinset]
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2), Complex.dist_eq]
      have hx1 : (1 : ℝ) / 2 < x := hx.1
      have hx2 : x < 2 := hx.2
      have hval : ‖((x : ℂ) - 2)‖ = |x - 2| := by
        rw [show ((x : ℂ) - 2) = ((x - 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs]
      rw [hval, abs_le]
      constructor <;> linarith
    · rw [zetaRealTrace_ofReal, hzero]
      norm_num
  have hbound := abs_integral_im_logDeriv_zeta_le hTne hζne hZmem
  have hcard : ((Z.filter (fun z => z ∈ Set.Ioo (1 / 2 : ℝ) 2)).card : ℝ) ≤ c₀ * Real.log T := by
    have hsub : (Z.filter (fun z => z ∈ Set.Ioo (1 / 2 : ℝ) 2)).card ≤ Z.card :=
      Finset.card_filter_le _ _
    have himg : (Z.image (fun x : ℝ => (x : ℂ))).card = Z.card :=
      Finset.card_image_of_injective _ (fun a b h => Complex.ofReal_inj.mp h)
    have hKcompact : IsCompact (closedBall (2 : ℂ) |(3 / 2 : ℝ)|) := isCompact_closedBall ..
    have hKana : AnalyticOnNhd ℂ (zetaRealTrace T) (closedBall (2 : ℂ) |(3 / 2 : ℝ)|) :=
      (analyticOnNhd_zetaRealTrace hT2).mono (by
        intro w hw
        rw [mem_closedBall, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hw
        rw [mem_closedBall, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 4)]
        linarith)
    have hKord : ∀ z ∈ closedBall (2 : ℂ) |(3 / 2 : ℝ)|,
        analyticOrderAt (zetaRealTrace T) z ≠ ⊤ := by
      intro z hz
      refine zetaRealTrace_order_ne_top hT2 ?_
      rw [mem_closedBall, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hz
      rw [mem_ball]
      linarith
    have hS : ∀ z ∈ Z.image (fun x : ℝ => (x : ℂ)),
        z ∈ closedBall (2 : ℂ) |(3 / 2 : ℝ)| ∧ zetaRealTrace T z = 0 := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      rw [hZdef, Set.Finite.mem_toFinset] at hx
      exact hx
    have hle := card_le_divisor_sum hKcompact hKana hKord _ hS
    rw [himg] at hle
    have hcnt := hcount T hT
    have hcast : ((Z.card : ℤ) : ℝ) ≤ ((∑ᶠ u, MeromorphicOn.divisor (zetaRealTrace T)
        (closedBall (2 : ℂ) |(3 / 2 : ℝ)|) u : ℤ) : ℝ) := by exact_mod_cast hle
    have hsubcast : ((Z.filter (fun z => z ∈ Set.Ioo (1 / 2 : ℝ) 2)).card : ℝ) ≤ (Z.card : ℝ) := by
      exact_mod_cast hsub
    push_cast at hcast
    linarith
  refine le_trans hbound ?_
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  nlinarith [hcard, hlog1, hπ]

end RHTower
