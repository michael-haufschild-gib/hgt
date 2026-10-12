import GaloisForLFunctions.RHTower.JointAncestryWeightedLag
import GaloisForLFunctions.RHTower.WeilLagFunctionGrowth

/-!
# Exponential growth of a dressed lag function bounds the zeros

**Theorem** (`re_le_half_add_of_dLagReal_le_exp`).  For every dressing `g`, if
`Φ_g(L) ≤ M e^{aL}` for all `L ≥ 0` with `0 ≤ a < ½`, every zero has real part at most `½ + a`.

The proof is the one-sided Landau argument of the undressed lag function, with the pole series
`G_g(s) = Σ_ρ g(ρ)/(ρ(1−ρ)(s − (ρ−½)))`.  The nonnegative density `M e^{au} − Φ_g(u)` plus
`e^{au} du` has Laplace transform `(M+1)/(s−a) − G_g(s)` on `Re s > ½`; Landau's theorem puts the
abscissa at `a`, so `G_g` extends analytically to `Re s > a`.  At the rightmost zero `ρ₀` of a
horizontal segment the residue of `G_g` is `m(ρ₀) g(ρ₀)/(ρ₀(1−ρ₀)) ≠ 0`, because the dressed weight
is constant on the copies of `ρ₀` and `g(ρ₀) ≠ 0`.  This excludes `Re ρ₀ > ½ + a`.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

variable (D : LagDressing)

/-- `G_g(s) = Σ_ρ g(ρ)(ρ(1−ρ))^{−1}/(s − (ρ − ½))`. -/
def dPoleSeries (s : ℂ) : ℂ := ∑' q : XiZeroCopy, D.weight q / (s - lagPole q)

/-- Away from the poles the series is differentiable. -/
theorem differentiableAt_dPoleSeries {s₁ : ℂ} (h : xi (s₁ + 1 / 2) ≠ 0) :
    DifferentiableAt ℂ (dPoleSeries D) s₁ := by
  have hopen : IsOpen {z : ℂ | xi z ≠ 0} := isOpen_ne_fun xi_differentiable.continuous continuous_const
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen (s₁ + 1 / 2) h
  -- every pole is at distance ≥ δ/2 from every point of `ball s₁ (δ/2)`
  have hfar : ∀ s ∈ Metric.ball s₁ (δ / 2), ∀ q : XiZeroCopy, δ / 2 ≤ ‖s - lagPole q‖ := by
    intro s hs q
    have hq : (q.1 : ℂ) ∉ Metric.ball (s₁ + 1 / 2) δ := fun hmem =>
      hball hmem (xi_xiZeroCopy_eq_zero q)
    rw [Metric.mem_ball, not_lt, Complex.dist_eq] at hq
    rw [Metric.mem_ball, Complex.dist_eq] at hs
    have e : s - lagPole q = ((q.1 : ℂ) - (s₁ + 1 / 2)) * (-1) + (s - s₁) := by
      unfold lagPole; ring
    rw [e]
    have := norm_add_le (((q.1 : ℂ) - (s₁ + 1 / 2)) * (-1)) (s - s₁)
    rw [norm_mul, norm_neg, norm_one, mul_one] at this
    have h2 := norm_sub_norm_le (((q.1 : ℂ) - (s₁ + 1 / 2)) * (-1)) (-(s - s₁))
    rw [norm_mul, norm_neg, norm_one, mul_one, norm_neg, sub_neg_eq_add] at h2
    linarith
  have hdiff : DifferentiableOn ℂ (dPoleSeries D) (Metric.ball s₁ (δ / 2)) := by
    unfold dPoleSeries
    refine differentiableOn_tsum_of_summable_norm
      (u := fun q => ‖D.weight q‖ * (2 / δ)) (D.summable_norm_weight.mul_right _) (fun q => ?_)
      Metric.isOpen_ball (fun q s hs => ?_)
    · refine (differentiableOn_const _).div (differentiableOn_id.sub (differentiableOn_const _))
        fun s hs => ?_
      have := hfar s hs q
      intro h0
      rw [h0, norm_zero] at this
      linarith
    · rw [norm_div]
      have := hfar s hs q
      have hpos : 0 < ‖s - lagPole q‖ := by linarith
      rw [div_le_iff₀ hpos]
      calc ‖D.weight q‖ = ‖D.weight q‖ * (2 / δ) * (δ / 2) := by field_simp
        _ ≤ ‖D.weight q‖ * (2 / δ) * ‖s - lagPole q‖ := by gcongr
  exact hdiff.differentiableAt (Metric.ball_mem_nhds _ (by positivity))


/-- Near a pole the series is unbounded: `‖G(p₀ + t)‖ ≥ ‖w₀‖/t − C` for small `t > 0`. -/
theorem norm_dPoleSeries_ge (q₀ : XiZeroCopy) :
    ∃ ε > 0, ∃ C : ℝ, ∀ t : ℝ, 0 < t → t < ε →
      ‖D.weight q₀‖ / t - C ≤ ‖dPoleSeries D (lagPole q₀ + t)‖ := by
  obtain ⟨ε, hε, hiso⟩ := xi_zero_isolated (xi_xiZeroCopy_eq_zero q₀)
  refine ⟨ε / 2, by positivity, (2 / ε) * ∑' q : XiZeroCopy, ‖D.weight q‖, fun t ht htε => ?_⟩
  set S : Set XiZeroCopy := {q | q.1 = q₀.1} with hS
  -- distances: copies off `S` have poles at distance ≥ ε/2 from `p₀ + t`
  have hoff : ∀ q : XiZeroCopy, q ∉ S → ε / 2 ≤ ‖lagPole q₀ + t - lagPole q‖ := by
    intro q hq
    have hne : (q.1 : ℂ) ≠ (q₀.1 : ℂ) := fun h => hq (Subtype.ext h)
    have hdist : ε ≤ dist (q.1 : ℂ) (q₀.1 : ℂ) := by
      by_contra hlt
      exact hne (hiso _ (xi_xiZeroCopy_eq_zero q) (not_le.mp hlt))
    rw [Complex.dist_eq] at hdist
    have e : lagPole q₀ + t - lagPole q = -((q.1 : ℂ) - (q₀.1 : ℂ)) + t := by unfold lagPole; ring
    rw [e]
    have h2 := norm_sub_norm_le (-((q.1 : ℂ) - (q₀.1 : ℂ))) (-(t : ℂ))
    rw [norm_neg, norm_neg, sub_neg_eq_add, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht] at h2
    linarith
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  -- summability of the full series at `p₀ + t`
  have hsumm : Summable (fun q : XiZeroCopy => D.weight q / (lagPole q₀ + t - lagPole q)) := by
    refine Summable.of_norm_bounded
      (g := fun q => ‖D.weight q‖ * max (1 / t) (2 / ε)) (D.summable_norm_weight.mul_right _)
      fun q => ?_
    rw [norm_div]
    by_cases hq : q ∈ S
    · have hq' : (q.1 : ℂ) = (q₀.1 : ℂ) := congrArg (fun r : XiDivisorSupport => (r : ℂ)) hq
      have e : lagPole q₀ + t - lagPole q = t := by unfold lagPole; rw [hq']; ring
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, div_eq_mul_one_div]
      gcongr
      exact le_max_left _ _
    · have := hoff q hq
      have hpos : 0 < ‖lagPole q₀ + t - lagPole q‖ := by linarith
      rw [div_le_iff₀ hpos]
      calc ‖D.weight q‖ = ‖D.weight q‖ * (2 / ε) * (ε / 2) := by field_simp
        _ ≤ ‖D.weight q‖ * max (1 / t) (2 / ε) * ‖lagPole q₀ + t - lagPole q‖ := by
            gcongr
            exact le_max_right _ _
  unfold dPoleSeries
  rw [← hsumm.tsum_subtype_add_tsum_subtype_compl S]
  -- the fibre sum is `card S • (w₀/t)`
  have hfib : ∀ q : S, D.weight q.1 / (lagPole q₀ + t - lagPole q.1) = D.weight q₀ / t := by
    intro q
    have hq' : (q.1.1 : ℂ) = (q₀.1 : ℂ) := congrArg (fun r : XiDivisorSupport => (r : ℂ)) q.2
    unfold LagDressing.weight lagPole
    rw [hq']
    ring
  rw [tsum_congr hfib, tsum_const]
  have hfin : Finite S := by
    refine Finite.of_injective
      (fun x : S => (⟨(x.1.2 : ℕ), lt_of_lt_of_eq x.1.2.isLt (by
        rw [show x.1.1 = q₀.1 from x.2])⟩ :
          Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (q₀.1 : ℂ)))))
      fun x y hxy => ?_
    have hv : (x.1.2 : ℕ) = (y.1.2 : ℕ) := by
      have := congrArg Fin.val hxy
      simpa using this
    apply Subtype.ext
    apply Sigma.ext
    · exact x.2.trans y.2.symm
    · have hx : x.1.1 = q₀.1 := x.2
      have hy : y.1.1 = q₀.1 := y.2
      exact (Fin.heq_ext_iff (by rw [hx, hy])).mpr hv
  have hne : Nonempty S := ⟨⟨q₀, rfl⟩⟩
  have hcard : 1 ≤ Nat.card S := Nat.card_pos
  -- the complementary sum is bounded by `C`
  have hcompl : ‖∑' q : ↑Sᶜ, D.weight q.1 / (lagPole q₀ + t - lagPole q.1)‖ ≤
      (2 / ε) * ∑' q : XiZeroCopy, ‖D.weight q‖ := by
    have hb : ∀ q : ↑Sᶜ, ‖D.weight q.1 / (lagPole q₀ + t - lagPole q.1)‖ ≤
        (2 / ε) * ‖D.weight q.1‖ := by
      intro q
      have := hoff q.1 q.2
      have hpos : 0 < ‖lagPole q₀ + t - lagPole q.1‖ := by linarith
      rw [norm_div, div_le_iff₀ hpos]
      calc ‖D.weight q.1‖ = (2 / ε) * ‖D.weight q.1‖ * (ε / 2) := by field_simp
        _ ≤ (2 / ε) * ‖D.weight q.1‖ * ‖lagPole q₀ + t - lagPole q.1‖ := by gcongr
    have hs1 : Summable (fun q : ↑Sᶜ => ‖D.weight q.1 / (lagPole q₀ + t - lagPole q.1)‖) :=
      (hsumm.norm.subtype _)
    have hs2 : Summable (fun q : ↑Sᶜ => (2 / ε) * ‖D.weight q.1‖) :=
      (D.summable_norm_weight.mul_left _).subtype _
    calc ‖∑' q : ↑Sᶜ, D.weight q.1 / (lagPole q₀ + t - lagPole q.1)‖
        ≤ ∑' q : ↑Sᶜ, ‖D.weight q.1 / (lagPole q₀ + t - lagPole q.1)‖ :=
          norm_tsum_le_tsum_norm hs1
      _ ≤ ∑' q : ↑Sᶜ, (2 / ε) * ‖D.weight q.1‖ := hs1.tsum_le_tsum hb hs2
      _ = (2 / ε) * ∑' q : ↑Sᶜ, ‖D.weight q.1‖ := tsum_mul_left
      _ ≤ (2 / ε) * ∑' q : XiZeroCopy, ‖D.weight q‖ := by
          gcongr
          exact Summable.tsum_subtype_le (fun q : XiZeroCopy => ‖D.weight q‖) Sᶜ
            (fun _ => norm_nonneg _) D.summable_norm_weight
  have hmain : ‖D.weight q₀‖ / t ≤ ‖Nat.card S • (D.weight q₀ / t)‖ := by
    rw [nsmul_eq_mul, norm_mul, Complex.norm_natCast, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht]
    have : (1 : ℝ) ≤ Nat.card S := by exact_mod_cast hcard
    calc ‖D.weight q₀‖ / t = 1 * (‖D.weight q₀‖ / t) := by ring
      _ ≤ (Nat.card S : ℝ) * (‖D.weight q₀‖ / t) := by gcongr
  calc ‖D.weight q₀‖ / t - (2 / ε) * ∑' q : XiZeroCopy, ‖D.weight q‖
      ≤ ‖Nat.card S • (D.weight q₀ / t)‖ -
          ‖∑' q : ↑Sᶜ, D.weight q.1 / (lagPole q₀ + t - lagPole q.1)‖ := by linarith
    _ ≤ ‖Nat.card S • (D.weight q₀ / t) +
          ∑' q : ↑Sᶜ, D.weight q.1 / (lagPole q₀ + t - lagPole q.1)‖ := by
        have := norm_sub_norm_le (Nat.card S • (D.weight q₀ / t))
          (-(∑' q : ↑Sᶜ, D.weight q.1 / (lagPole q₀ + t - lagPole q.1)))
        rw [norm_neg, sub_neg_eq_add] at this
        exact this


theorem integral_dLag_mul_cexp {s : ℂ} (hs : 1 / 2 < s.re) :
    ∫ u in Ioi (0:ℝ), dLag D u * Complex.exp (-s * (u : ℂ)) = dPoleSeries D s := by
  unfold dLag dPoleSeries
  have hterm : ∀ (u : ℝ) (q : XiZeroCopy),
      Complex.exp (u * ((q.1 : ℂ) - 1 / 2)) * D.weight q * Complex.exp (-s * (u : ℂ))
        = D.weight q * Complex.exp (-(s - lagPole q) * (u : ℂ)) := by
    intro u q
    unfold lagPole
    rw [mul_comm (Complex.exp _) (D.weight q), mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hre : ∀ q : XiZeroCopy, 0 < (s - lagPole q).re := by
    intro q; rw [Complex.sub_re]; linarith [lagPole_re_lt_half q]
  have hint : ∀ q : XiZeroCopy, Integrable
      (fun u : ℝ => D.weight q * Complex.exp (-(s - lagPole q) * (u : ℂ)))
      (volume.restrict (Ioi (0:ℝ))) := by
    intro q
    have hc : Continuous (fun u : ℝ => Complex.exp (-(s - lagPole q) * (u : ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
    exact ((exp_neg_integrableOn_Ioi 0 (hre q)).mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => le_of_eq (norm_cexp_neg_mul _ u))).const_mul _
  have hnorm : Summable (fun q : XiZeroCopy =>
      ∫ u in Ioi (0:ℝ), ‖D.weight q * Complex.exp (-(s - lagPole q) * (u : ℂ))‖) := by
    have hK : ∀ q : XiZeroCopy,
        ∫ u in Ioi (0:ℝ), ‖D.weight q * Complex.exp (-(s - lagPole q) * (u : ℂ))‖
          ≤ ‖D.weight q‖ * (1 / (s.re - 1 / 2)) := by
      intro q
      rw [← integral_exp_neg_mul_Ioi_real (by linarith : (0:ℝ) < s.re - 1 / 2), ← integral_const_mul]
      refine setIntegral_mono_on ?_ ?_ measurableSet_Ioi fun u hu => ?_
      · exact (hint q).norm
      · exact (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul _
      · rw [norm_mul, norm_cexp_neg_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        apply Real.exp_le_exp.mpr
        have := lagPole_re_lt_half q
        have hu' : (0:ℝ) < u := hu
        rw [Complex.sub_re]
        nlinarith
    exact Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hK
      (D.summable_norm_weight.mul_right _)
  have hfun : (fun u : ℝ => (∑' q : XiZeroCopy,
      Complex.exp (u * ((q.1 : ℂ) - 1 / 2)) * D.weight q) * Complex.exp (-s * (u : ℂ)))
      = fun u : ℝ => ∑' q : XiZeroCopy, D.weight q * Complex.exp (-(s - lagPole q) * (u : ℂ)) := by
    funext u
    rw [← tsum_mul_right]
    exact tsum_congr fun q => hterm u q
  rw [hfun, ← integral_tsum_of_summable_integral_norm hint hnorm]
  refine tsum_congr fun q => ?_
  rw [integral_const_mul, integral_cexp_neg_mul_Ioi (hre q), mul_one_div]

theorem integrable_dLag_mul_cexp {s : ℂ} (hs : 1 / 2 < s.re) :
    IntegrableOn (fun u : ℝ => (dLagReal D u : ℂ) * Complex.exp (-s * (u : ℂ))) (Ioi 0) := by
  refine (integrableOn_growth_majorant (C := D.total) hs).mono' ?_ ?_
  · exact ((Complex.continuous_ofReal.comp_aestronglyMeasurable
      (measurable_dLagReal D).aestronglyMeasurable).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_neg_mul]
    have := abs_dLagReal_le D u
    rw [abs_of_pos (show (0:ℝ) < u from hu)] at this
    calc |dLagReal D u| * Real.exp (-s.re * u)
        ≤ (Real.exp (u / 2) * D.total) * Real.exp (-s.re * u) :=
          mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = D.total * Real.exp (u / 2) * Real.exp (-s.re * u) := by ring

theorem analyticAt_dPoleSeries {z : ℂ} (hz : xi (z + 1 / 2) ≠ 0) : AnalyticAt ℂ (dPoleSeries D) z := by
  have hopen : IsOpen {w : ℂ | xi (w + 1 / 2) ≠ 0} :=
    isOpen_ne_fun (xi_differentiable.continuous.comp (continuous_id.add continuous_const))
      continuous_const
  refine DifferentiableOn.analyticAt (s := {w : ℂ | xi (w + 1 / 2) ≠ 0}) ?_ (hopen.mem_nhds hz)
  exact fun w hw => (differentiableAt_dPoleSeries D hw).differentiableWithinAt


/-- **Analytic extension of the lag pole series to `Re z > a` bounds the real parts of the zeros
by `½ + a`.** -/
theorem re_le_half_add_of_dPoleSeries_extension {a : ℝ} (ha : 0 ≤ a) {F : ℂ → ℂ}
    (hFd : ∀ z : ℂ, a < z.re → z.re < 2 → DifferentiableAt ℂ F z)
    (hFG : ∀ s : ℂ, 1 / 2 < s.re → F s = dPoleSeries D s) (q₁ : XiZeroCopy) :
    (q₁.1 : ℂ).re ≤ 1 / 2 + a := by
  by_contra hq₁'
  have hq₁ : 1 / 2 + a < (q₁.1 : ℂ).re := not_le.mp hq₁'
  set ρ₁ : ℂ := (q₁.1 : ℂ) with hρ₁
  set K : Set ℂ := Set.Icc ρ₁.re 1 ×ℂ Set.Icc ρ₁.im ρ₁.im with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hfin : (xiZeroSet_weilLagFunctionCriterion ∩ K).Finite := finite_xiZeroSet_inter hKc
  have hmem₁ : ρ₁ ∈ xiZeroSet_weilLagFunctionCriterion ∩ K := by
    refine ⟨xi_xiZeroCopy_eq_zero q₁, ?_⟩
    rw [hK, Complex.mem_reProdIm]
    exact ⟨⟨le_rfl, (xiZeroCopy_re_lt_one q₁).le⟩, ⟨le_rfl, le_rfl⟩⟩
  obtain ⟨ρ₀, hρ₀⟩ := hfin.exists_maximalFor Complex.re _ ⟨ρ₁, hmem₁⟩
  have hρ₀mem : ρ₀ ∈ xiZeroSet_weilLagFunctionCriterion ∩ K := hρ₀.1
  have hmax : ∀ z ∈ xiZeroSet_weilLagFunctionCriterion ∩ K, ρ₀.re ≤ z.re → z.re ≤ ρ₀.re := fun z hz h => hρ₀.2 hz h
  obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ₀mem.1
  have hρ₀K := hρ₀mem.2
  rw [hK, Complex.mem_reProdIm] at hρ₀K
  have hre₀ : 1 / 2 + a < ρ₀.re := lt_of_lt_of_le hq₁ hρ₀K.1.1
  have hre₀' : ρ₀.re < 1 := xiZeroCopy_re_lt_one q₀ |> fun h => by rwa [hq₀] at h
  have him₀ : ρ₀.im = ρ₁.im := le_antisymm hρ₀K.2.2 hρ₀K.2.1
  set p₀ : ℂ := lagPole q₀ with hp₀
  have hp₀re : p₀.re = ρ₀.re - 1 / 2 := by
    rw [hp₀]; unfold lagPole; rw [hq₀]; simp
  have hp₀a : a < p₀.re := by rw [hp₀re]; linarith
  have hp₀pos : 0 < p₀.re := by linarith
  have hp₀half : p₀.re < 1 / 2 := by rw [hp₀re]; linarith
  -- the horizontal ray to the right of `p₀` carries no zero of `ξ(· + ½)`
  have hray : ∀ t : ℝ, 0 < t → xi (p₀ + t + 1 / 2) ≠ 0 := by
    intro t ht hzero
    have hval : p₀ + t + 1 / 2 = ρ₀ + t := by rw [hp₀]; unfold lagPole; rw [hq₀]; ring
    rw [hval] at hzero
    by_cases hle : (ρ₀ + t).re ≤ 1
    · have hmemK : ρ₀ + t ∈ xiZeroSet_weilLagFunctionCriterion ∩ K := by
        refine ⟨hzero, ?_⟩
        rw [hK, Complex.mem_reProdIm]
        refine ⟨⟨?_, hle⟩, ?_⟩
        · simp only [Complex.add_re, Complex.ofReal_re]; linarith [hρ₀K.1.1]
        · simp only [Complex.add_im, Complex.ofReal_im, add_zero, him₀]; exact ⟨le_rfl, le_rfl⟩
      have := hmax _ hmemK (by simp only [Complex.add_re, Complex.ofReal_re]; linarith)
      simp only [Complex.add_re, Complex.ofReal_re] at this
      linarith
    · exact xi_ne_zero_of_one_le_re (not_le.mp hle).le hzero
  -- the two analytic functions along the ray
  set ℓ : ℝ → ℂ := fun t => p₀ + t with hℓ
  have hℓan : ∀ t : ℝ, AnalyticAt ℝ ℓ t := fun t =>
    analyticAt_const.add (Complex.ofRealCLM.analyticAt t)
  set V : Set ℂ := {z : ℂ | a < z.re ∧ z.re < 2} with hV
  have hVopen : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hFdiff : DifferentiableOn ℂ F V := fun z hz => (hFd z hz.1 hz.2).differentiableWithinAt
  set U : Set ℝ := Ioo (0:ℝ) (2 - p₀.re) with hU
  have hℓV : ∀ t ∈ U, ℓ t ∈ V := by
    intro t ht
    simp only [hℓ, hV, Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re]
    constructor <;> linarith [ht.1, ht.2]
  have hF : AnalyticOnNhd ℝ (fun t : ℝ => F (ℓ t)) U := by
    intro t ht
    have hFz : AnalyticAt ℂ (F) (ℓ t) :=
      hFdiff.analyticAt (hVopen.mem_nhds (hℓV t ht))
    exact hFz.restrictScalars.comp (hℓan t)
  have hG : AnalyticOnNhd ℝ (fun t : ℝ => dPoleSeries D (ℓ t)) U := by
    intro t ht
    have hGz : AnalyticAt ℂ (dPoleSeries D) (ℓ t) := by
      have hne : xi (ℓ t + 1 / 2) ≠ 0 := hray t ht.1
      have hopen : IsOpen {z : ℂ | xi (z + 1 / 2) ≠ 0} :=
        isOpen_ne_fun (xi_differentiable.continuous.comp (continuous_id.add continuous_const))
          continuous_const
      refine DifferentiableOn.analyticAt (s := {z : ℂ | xi (z + 1 / 2) ≠ 0}) ?_ (hopen.mem_nhds hne)
      exact fun z hz => (differentiableAt_dPoleSeries D hz).differentiableWithinAt
    exact hGz.restrictScalars.comp (hℓan t)
  have hUconn : IsPreconnected U := isPreconnected_Ioo
  have h1U : (1 : ℝ) ∈ U := ⟨one_pos, by linarith⟩
  have hfg : (fun t : ℝ => F (ℓ t)) =ᶠ[𝓝 (1:ℝ)]
      (fun t : ℝ => dPoleSeries D (ℓ t)) := by
    refine Filter.eventuallyEq_of_mem
      (Ioo_mem_nhds (by norm_num : (1/2 : ℝ) < 1) (by norm_num : (1:ℝ) < 3/2)) fun t ht => ?_
    apply hFG
    simp only [hℓ, Complex.add_re, Complex.ofReal_re]
    linarith [ht.1]
  have heq := hF.eqOn_of_preconnected_of_eventuallyEq hG hUconn h1U hfg
  -- continuity of `F` at `p₀`
  have hFcont : ContinuousAt F p₀ := (hFd p₀ hp₀a (by linarith)).continuousAt
  have hℓ0 : Tendsto ℓ (𝓝 0) (𝓝 p₀) := by
    have : Tendsto (fun t : ℝ => p₀ + (t : ℂ)) (𝓝 0) (𝓝 (p₀ + ((0:ℝ) : ℂ))) :=
      tendsto_const_nhds.add (Complex.continuous_ofReal.tendsto 0)
    simpa using this
  have hcomp : Tendsto (fun t : ℝ => F (ℓ t)) (𝓝 0) (𝓝 (F p₀)) :=
    hFcont.tendsto.comp hℓ0
  obtain ⟨δ, hδ, hδF⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp hcomp 1 one_pos)
  -- the pole bound
  obtain ⟨ε, hε, C, hC⟩ := norm_dPoleSeries_ge D q₀
  set C' : ℝ := max C 0 with hC'
  have hC0 : 0 ≤ C' := le_max_right _ _
  have hC'' : ∀ t : ℝ, 0 < t → t < ε →
      ‖D.weight q₀‖ / t - C' ≤ ‖dPoleSeries D (lagPole q₀ + t)‖ :=
    fun t ht htε => le_trans (by linarith [le_max_left C 0]) (hC t ht htε)
  set B : ℝ := ‖F p₀‖ + 1 with hB
  have hw : 0 < ‖D.weight q₀‖ := norm_pos_iff.mpr (D.weight_ne_zero q₀)
  have hBpos : 0 < B + C' + 1 := by positivity
  have h2p : 0 < 2 - p₀.re := by linarith
  have hw' : 0 < ‖D.weight q₀‖ / (B + C' + 1) := div_pos hw hBpos
  set m : ℝ := min (min δ ε) (min (2 - p₀.re) (‖D.weight q₀‖ / (B + C' + 1))) with hm
  have hmpos : 0 < m := lt_min (lt_min hδ hε) (lt_min h2p hw')
  set t₀ : ℝ := m / 2 with ht₀
  have ht₀pos : 0 < t₀ := half_pos hmpos
  have hmδ : m ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hmε : m ≤ ε := (min_le_left _ _).trans (min_le_right _ _)
  have hm2 : m ≤ 2 - p₀.re := (min_le_right _ _).trans (min_le_left _ _)
  have hmw : m ≤ ‖D.weight q₀‖ / (B + C' + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have ht₀δ : t₀ < δ := by rw [ht₀]; linarith
  have ht₀ε : t₀ < ε := by rw [ht₀]; linarith
  have ht₀U : t₀ ∈ U := ⟨ht₀pos, by rw [ht₀]; linarith⟩
  have hFb : ‖F (ℓ t₀)‖ ≤ B := by
    have hd : dist t₀ 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht₀pos]; exact ht₀δ
    have := hδF hd
    rw [dist_eq_norm] at this
    calc ‖F (ℓ t₀)‖
        = ‖(F (ℓ t₀) - F p₀) + F p₀‖ := by
          congr 1; ring
      _ ≤ ‖F (ℓ t₀) - F p₀‖ + ‖F p₀‖ :=
          norm_add_le _ _
      _ ≤ 1 + ‖F p₀‖ := by linarith
      _ = B := by rw [hB]; ring
  have hGb : B < ‖dPoleSeries D (ℓ t₀)‖ := by
    have h1 := hC'' t₀ ht₀pos ht₀ε
    have h2 : 2 * (B + C' + 1) ≤ ‖D.weight q₀‖ / t₀ := by
      rw [le_div_iff₀ ht₀pos]
      calc 2 * (B + C' + 1) * t₀ ≤ 2 * (B + C' + 1) * (‖D.weight q₀‖ / (B + C' + 1) / 2) := by
            gcongr
            rw [ht₀]; linarith
        _ = ‖D.weight q₀‖ := by field_simp
    have hℓt : ℓ t₀ = lagPole q₀ + t₀ := rfl
    rw [hℓt]
    linarith
  have hEq : F (ℓ t₀) = dPoleSeries D (ℓ t₀) := heq ht₀U
  rw [hEq] at hFb
  linarith


/-- The clipped density `max(M e^{au} − Φ(u), 0)`. -/
def dGrowthDensity (a M : ℝ) (u : ℝ) : NNReal :=
  Real.toNNReal (M * Real.exp (a * u) - dLagReal D u)

theorem measurable_dGrowthDensity (a M : ℝ) : Measurable (dGrowthDensity D a M) :=
  ((measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id))).sub
    (measurable_dLagReal D)).real_toNNReal

/-- `(M e^{au} − Φ) du + e^{au} du` on `(0,∞)`. -/
def dGrowthMeasure (a M : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0:ℝ))).withDensity (fun u => (dGrowthDensity D a M u : ENNReal))
    + (volume.restrict (Ioi (0:ℝ))).withDensity (fun u => (growthShiftDensity a u : ENNReal))

/-- The density is at most `(|M| + W) e^{u/2}` for `u > 0`, when `a ≤ ½`. -/
theorem dGrowthDensity_le {a M : ℝ} (ha : a ≤ 1 / 2) {u : ℝ} (hu : 0 < u) :
    ((dGrowthDensity D a M u : ℝ)) ≤ (|M| + D.total) * Real.exp (u / 2) := by
  unfold dGrowthDensity
  rw [Real.coe_toNNReal']
  have h1 := abs_dLagReal_le D u
  rw [abs_of_pos hu] at h1
  have h2 : Real.exp (a * u) ≤ Real.exp (u / 2) := Real.exp_le_exp.mpr (by nlinarith)
  have h3 : M * Real.exp (a * u) ≤ |M| * Real.exp (u / 2) := by
    calc M * Real.exp (a * u) ≤ |M| * Real.exp (a * u) :=
          mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le
      _ ≤ |M| * Real.exp (u / 2) := mul_le_mul_of_nonneg_left h2 (abs_nonneg M)
  have h4 := neg_abs_le (dLagReal D u)
  have hW := D.total_nonneg
  have hE := Real.exp_pos (u / 2)
  rcases le_or_gt (M * Real.exp (a * u) - dLagReal D u) 0 with h | h
  · rw [max_eq_right h]; positivity
  · rw [max_eq_left h.le]; nlinarith

theorem laplaceMass_dGrowth_density_ne_top {a M σ : ℝ} (ha : a ≤ 1 / 2) (hσ : 1 / 2 < σ) :
    laplaceMass ((volume.restrict (Ioi (0:ℝ))).withDensity
      (fun u => (dGrowthDensity D a M u : ENNReal))) σ ≠ ⊤ := by
  unfold laplaceMass
  have hg : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, inter_self,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_dGrowthDensity D a M).coe_nnreal_ennreal hg]
  refine ne_top_of_le_ne_top
    (integrableOn_growth_majorant (C := |M| + D.total) hσ).lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (dGrowthDensity_le D ha hu) (Real.exp_pos _).le

theorem laplaceMass_dGrowth_eq (a M σ : ℝ) :
    laplaceMass (dGrowthMeasure D a M) σ =
      laplaceMass ((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun u => (dGrowthDensity D a M u : ENNReal))) σ + laplaceMass volume (σ - a) := by
  unfold laplaceMass dGrowthMeasure
  rw [Measure.restrict_add, lintegral_add_measure]
  congr 1
  have := laplaceMass_growthShift a σ
  unfold laplaceMass at this
  exact this

/-- The real points of convergence lie in `(a, ∞)`, contain `1`, and form an up-set; their infimum
is the abscissa, which is at least `a`. -/
theorem isAbscissa_dGrowth {a M : ℝ} (ha : a < 1 / 2) :
    IsAbscissa (dGrowthMeasure D a M) (sInf {σ : ℝ | laplaceMass (dGrowthMeasure D a M) σ ≠ ⊤}) ∧
      a ≤ sInf {σ : ℝ | laplaceMass (dGrowthMeasure D a M) σ ≠ ⊤} := by
  set S := {σ : ℝ | laplaceMass (dGrowthMeasure D a M) σ ≠ ⊤} with hS
  have hpos : ∀ σ ∈ S, a < σ := by
    intro σ hσ
    by_contra hle
    apply hσ
    rw [laplaceMass_dGrowth_eq D]
    rcases lt_or_eq_of_le (not_lt.mp hle) with h | h
    · rw [laplaceMass_volume_eq_top (by linarith), add_top]
    · rw [h, sub_self, laplaceMass_volume_zero_eq_top, add_top]
  have hbdd : BddBelow S := ⟨a, fun σ hσ => (hpos σ hσ).le⟩
  have h1S : (1:ℝ) ∈ S := by
    show laplaceMass (dGrowthMeasure D a M) 1 ≠ ⊤
    rw [laplaceMass_dGrowth_eq D]
    exact ENNReal.add_ne_top.mpr ⟨laplaceMass_dGrowth_density_ne_top D ha.le (by norm_num),
      laplaceMass_volume_ne_top (by linarith)⟩
  have hne : S.Nonempty := ⟨1, h1S⟩
  refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, le_csInf hne fun σ hσ => (hpos σ hσ).le⟩
  · obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hne hσ
    exact ne_top_of_le_ne_top hσ'S (laplaceMass_antitone _ hlt.le)
  · by_contra h
    exact absurd (csInf_le hbdd (show σ ∈ S from h)) (not_le.mpr hσ)

/-! ## The complex transform on `Re s > ½` -/

/-- The candidate analytic continuation `H(z) = (M+1)/(z − a) − G(z)`. -/
def dGrowthContinuation (a M : ℝ) (z : ℂ) : ℂ := (M + 1) / (z - a) - dPoleSeries D z

theorem analyticAt_dGrowthContinuation (a M : ℝ) {z : ℂ} (hza : z ≠ a) (hz : xi (z + 1 / 2) ≠ 0) :
    AnalyticAt ℂ (dGrowthContinuation D a M) z := by
  unfold dGrowthContinuation
  exact (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hza)).sub
    (analyticAt_dPoleSeries D hz)

theorem integrable_cexp_dGrowth_density {a M : ℝ} (ha : a ≤ 1 / 2) {s : ℂ} (hs : 1 / 2 < s.re) :
    Integrable (fun u : ℝ => Complex.exp (-s * (u : ℂ)))
      (((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun u => (dGrowthDensity D a M u : ENNReal))).restrict (Ioi 0)) := by
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, inter_self,
    integrable_withDensity_iff_integrable_smul (measurable_dGrowthDensity D a M)]
  refine (integrableOn_growth_majorant (C := |M| + D.total) (by exact hs)).mono' ?_ ?_
  · exact ((measurable_dGrowthDensity D a M).coe_nnreal_real.aestronglyMeasurable.smul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [NNReal.smul_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _),
      norm_cexp_neg_mul]
    exact mul_le_mul_of_nonneg_right (dGrowthDensity_le D ha hu) (Real.exp_pos _).le

/-- On `Re s > ½` the complex Laplace transform of the growth measure is `H(s)`. -/
theorem complexLaplace_dGrowth_eq {a M : ℝ} (ha : a < 1 / 2)
    (hM : ∀ L, 0 ≤ L → dLagReal D L ≤ M * Real.exp (a * L)) {s : ℂ} (hs : 1 / 2 < s.re) :
    complexLaplace (dGrowthMeasure D a M) s = dGrowthContinuation D a M s := by
  have hs0 : 0 < s.re := by linarith
  have hsa : a < s.re := by linarith
  have hsa' : 0 < (s - a).re := by simp; linarith
  have hcexp : Continuous (fun u : ℝ => Complex.exp (-s * (u : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hexpInt : IntegrableOn (fun u : ℝ => Complex.exp (-s * (u : ℂ))) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hs0).mono' hcexp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => le_of_eq (norm_cexp_neg_mul _ u))
  have hexpInt' : IntegrableOn (fun u : ℝ => Complex.exp (-(s - a) * (u : ℂ))) (Ioi 0) := by
    have hc : Continuous (fun u : ℝ => Complex.exp (-(s - a) * (u : ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
    exact (exp_neg_integrableOn_Ioi 0 hsa').mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => le_of_eq (norm_cexp_neg_mul _ u))
  unfold complexLaplace dGrowthMeasure dGrowthContinuation
  rw [Measure.restrict_add, integral_add_measure (integrable_cexp_dGrowth_density D ha.le hs)
    (integrable_cexp_growthShift hsa), complexLaplace_growthShift hsa]
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, inter_self,
    integral_withDensity_eq_integral_smul (measurable_dGrowthDensity D a M)]
  have hpt : ∀ u ∈ Ioi (0:ℝ), dGrowthDensity D a M u • Complex.exp (-s * (u : ℂ)) =
      (M : ℂ) * Complex.exp (-(s - a) * (u : ℂ)) -
        ((dLagReal D u : ℂ) * Complex.exp (-s * (u : ℂ))) := by
    intro u hu
    rw [NNReal.smul_def, Complex.real_smul]
    unfold dGrowthDensity
    rw [Real.coe_toNNReal _ (by linarith [hM u (le_of_lt hu)])]
    push_cast
    rw [show Complex.exp (-(s - a) * (u : ℂ)) = Complex.exp (a * u) * Complex.exp (-s * (u : ℂ)) by
      rw [← Complex.exp_add]; congr 1; ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_sub (hexpInt'.const_mul _) (integrable_dLag_mul_cexp D hs),
    integral_const_mul, integral_cexp_neg_mul_Ioi hsa']
  have hΦ : ∫ u in Ioi (0:ℝ), (dLagReal D u : ℂ) * Complex.exp (-s * (u : ℂ)) =
      dPoleSeries D s := by
    rw [← integral_dLag_mul_cexp D hs]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by
      beta_reduce; rw [dLag_eq_ofReal D])
  rw [hΦ]
  have hne : (s - a) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  field_simp
  ring

/-! ## Landau: the abscissa is `a` -/

theorem abscissa_dGrowth_eq {a M : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2)
    (hM : ∀ L, 0 ≤ L → dLagReal D L ≤ M * Real.exp (a * L)) :
    IsAbscissa (dGrowthMeasure D a M) a := by
  obtain ⟨hc, hac⟩ := isAbscissa_dGrowth D (M := M) ha
  set c : ℝ := sInf {σ : ℝ | laplaceMass (dGrowthMeasure D a M) σ ≠ ⊤} with hcdef
  rcases hac.lt_or_eq with hpos | hzero
  · exfalso
    have hc34 : c ≤ 3 / 4 := by
      refine csInf_le ⟨a, fun σ hσ => ?_⟩ ?_
      · by_contra hlt
        apply hσ
        rw [laplaceMass_dGrowth_eq D, laplaceMass_volume_eq_top (by linarith [not_le.mp hlt]), add_top]
      · show laplaceMass (dGrowthMeasure D a M) (3 / 4) ≠ ⊤
        rw [laplaceMass_dGrowth_eq D]
        exact ENNReal.add_ne_top.mpr ⟨laplaceMass_dGrowth_density_ne_top D ha.le (by norm_num),
          laplaceMass_volume_ne_top (by linarith)⟩
    have hcpos : 0 < c := lt_of_le_of_lt ha0 hpos
    have hne : xi ((c : ℂ) + 1 / 2) ≠ 0 := xi_ofReal_add_half_ne_zero hcpos
    have hopen : IsOpen {z : ℂ | xi z ≠ 0} := isOpen_ne_fun xi_differentiable.continuous continuous_const
    obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hopen _ hne
    set δ : ℝ := min (c - a) d / 2 with hδdef
    have hδ : 0 < δ := by rw [hδdef]; exact half_pos (lt_min (by linarith) hd)
    have hδc : δ ≤ (c - a) / 2 := by rw [hδdef]; linarith [min_le_left (c - a) d]
    have hδd : δ ≤ d / 2 := by rw [hδdef]; linarith [min_le_right (c - a) d]
    refine false_of_analyticAt_abscissa hc hδ (Φ := dGrowthContinuation D a M) ?_ ?_
    · intro z hz
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      have hzre : (c + a) / 2 < z.re := by
        have := Complex.abs_re_le_norm (z - c)
        rw [Complex.sub_re, Complex.ofReal_re] at this
        have := abs_le.mp this
        linarith
      have hza : z ≠ a := fun h => by rw [h] at hzre; simp at hzre; linarith
      have hzxi : xi (z + 1 / 2) ≠ 0 := by
        apply hball
        rw [Metric.mem_ball, Complex.dist_eq]
        calc ‖z + 1 / 2 - ((c : ℂ) + 1 / 2)‖ = ‖z - c‖ := by congr 1; ring
          _ < δ := hz
          _ ≤ d / 2 := hδd
          _ < d := by linarith
      exact analyticAt_dGrowthContinuation D a M hza hzxi
    · intro σ hσc _
      have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hTdiff : DifferentiableOn ℂ (complexLaplace (dGrowthMeasure D a M)) {z : ℂ | c < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hT : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace (dGrowthMeasure D a M) (t : ℂ)) (Ioi c) := by
        intro t ht
        have h1 : AnalyticAt ℂ (complexLaplace (dGrowthMeasure D a M)) (t : ℂ) :=
          hTdiff.analyticAt (hV.mem_nhds (by simpa using ht))
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have hH : AnalyticOnNhd ℝ (fun t : ℝ => dGrowthContinuation D a M (t : ℂ)) (Ioi c) := by
        intro t ht
        have hta : a < t := lt_trans hpos ht
        have ht0 : 0 < t := lt_of_le_of_lt ha0 hta
        have h1 : AnalyticAt ℂ (dGrowthContinuation D a M) (t : ℂ) :=
          analyticAt_dGrowthContinuation D a M (by exact_mod_cast hta.ne')
            (xi_ofReal_add_half_ne_zero ht0)
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have h1mem : (1 : ℝ) ∈ Ioi c := by show c < 1; linarith
      have hfg : (fun t : ℝ => complexLaplace (dGrowthMeasure D a M) (t : ℂ)) =ᶠ[𝓝 (1:ℝ)]
          (fun t : ℝ => dGrowthContinuation D a M (t : ℂ)) := by
        refine Filter.eventuallyEq_of_mem
          (Ioo_mem_nhds (by norm_num : (1/2 : ℝ) < 1) (by norm_num : (1:ℝ) < 3/2)) fun t ht => ?_
        exact complexLaplace_dGrowth_eq D ha hM (by simpa using ht.1)
      have heq := hT.eqOn_of_preconnected_of_eventuallyEq hH isPreconnected_Ioi h1mem hfg
      have hσ : complexLaplace (dGrowthMeasure D a M) (σ : ℂ) = dGrowthContinuation D a M (σ : ℂ) :=
        heq (show σ ∈ Ioi c from hσc)
      rw [← hσ, complexLaplace_ofReal]
  · rw [← hzero] at hc
    exact hc

/-! ## The growth criterion -/

/-- **One-sided exponential growth of the lag function bounds the real parts of the zeros.**
If `Φ(L) ≤ M e^{aL}` for all `L ≥ 0` with `0 ≤ a < ½`, every zero copy has real part at most
`½ + a`. -/
theorem re_le_half_add_of_dLagReal_le_exp {a M : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2)
    (hM : ∀ L, 0 ≤ L → dLagReal D L ≤ M * Real.exp (a * L)) (q : XiZeroCopy) :
    (q.1 : ℂ).re ≤ 1 / 2 + a := by
  have hc := abscissa_dGrowth_eq D ha0 ha hM
  refine re_le_half_add_of_dPoleSeries_extension D ha0
    (F := fun z => ((M : ℂ) + 1) / (z - a) - complexLaplace (dGrowthMeasure D a M) z) ?_ ?_ q
  · intro z hza _
    have hz : z - a ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have h1 : DifferentiableAt ℂ (fun z : ℂ => ((M : ℂ) + 1) / (z - a)) z :=
      (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _)) hz
    have h2 : DifferentiableAt ℂ (complexLaplace (dGrowthMeasure D a M)) z :=
      (hasDerivAt_complexLaplace hc hza).differentiableAt
    exact h1.sub h2
  · intro s hs
    rw [complexLaplace_dGrowth_eq D ha hM hs]
    unfold dGrowthContinuation
    ring


end

end RHTower
