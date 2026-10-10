import GaloisForLFunctions.RHTower.WeilLagFunctionGrowthLower
import GaloisForLFunctions.RHTower.FiniteOffLineVonKoch

/-!
# Landau's theorem with a finite off-line wave subtracted

**Pole extension with finitely many subtracted poles** (`re_le_half_add_of_lagPoleSeries_sub_extension`).
Let `P ⊂ ℂ` be countable, `R` holomorphic off `P`, and `F` holomorphic on `a < Re z < 2`. If
`F + R` equals the lag pole series `G(s) = Σ_ρ (ρ(1−ρ))^{−1}/(s − (ρ − ½))` on `Re s > ½`, then
every zero copy whose pole `ρ − ½` is not in `P` has real part at most `½ + a`.

**Proof.** If `p₀ = ρ₀ − ½ ∉ P` with `Re p₀ > a`, approach `p₀` along a ray `p₀ + t(1 + is)` whose
slope `s ∈ (0,1)` avoids the countably many slopes through other poles and points of `P`. Along the
ray `F + R` and `G` are real-analytic and agree for `Re > ½`, hence everywhere on the ray. `F + R` is
continuous at `p₀`, while `‖G(p₀ + d)‖ ≥ ‖w₀‖/‖d‖ − C` for small `d ≠ 0`
(`norm_lagPoleSeries_ge_disc`): a contradiction.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## The pole blow-up in a punctured disc -/

/-- Near a pole the series is unbounded in every direction: `‖G(p₀ + d)‖ ≥ ‖w₀‖/‖d‖ − C` for
`0 < ‖d‖ < ε`. -/
theorem norm_lagPoleSeries_ge_disc (q₀ : XiZeroCopy) :
    ∃ ε > 0, ∃ C : ℝ, ∀ d : ℂ, 0 < ‖d‖ → ‖d‖ < ε →
      ‖lagWeight q₀‖ / ‖d‖ - C ≤ ‖lagPoleSeries (lagPole q₀ + d)‖ := by
  obtain ⟨ε, hε, hiso⟩ := xi_zero_isolated (xi_xiZeroCopy_eq_zero q₀)
  refine ⟨ε / 2, by positivity, (2 / ε) * ∑' q : XiZeroCopy, ‖lagWeight q‖, fun d hd hdε => ?_⟩
  set S : Set XiZeroCopy := {q | q.1 = q₀.1} with hS
  have hoff : ∀ q : XiZeroCopy, q ∉ S → ε / 2 ≤ ‖lagPole q₀ + d - lagPole q‖ := by
    intro q hq
    have hne : (q.1 : ℂ) ≠ (q₀.1 : ℂ) := fun h => hq (Subtype.ext h)
    have hdist : ε ≤ dist (q.1 : ℂ) (q₀.1 : ℂ) := by
      by_contra hlt
      exact hne (hiso _ (xi_xiZeroCopy_eq_zero q) (not_le.mp hlt))
    rw [Complex.dist_eq] at hdist
    have e : lagPole q₀ + d - lagPole q = -((q.1 : ℂ) - (q₀.1 : ℂ)) + d := by unfold lagPole; ring
    rw [e]
    have h2 := norm_sub_norm_le (-((q.1 : ℂ) - (q₀.1 : ℂ))) (-d)
    rw [norm_neg, norm_neg, sub_neg_eq_add] at h2
    linarith
  have hd0 : d ≠ 0 := norm_pos_iff.mp hd
  have hsumm : Summable (fun q : XiZeroCopy => lagWeight q / (lagPole q₀ + d - lagPole q)) := by
    refine Summable.of_norm_bounded
      (g := fun q => ‖lagWeight q‖ * max (1 / ‖d‖) (2 / ε)) (summable_norm_lagWeight.mul_right _)
      fun q => ?_
    rw [norm_div]
    by_cases hq : q ∈ S
    · have hq' : (q.1 : ℂ) = (q₀.1 : ℂ) := congrArg (fun r : XiDivisorSupport => (r : ℂ)) hq
      have e : lagPole q₀ + d - lagPole q = d := by unfold lagPole; rw [hq']; ring
      rw [e, div_eq_mul_one_div]
      gcongr
      exact le_max_left _ _
    · have := hoff q hq
      have hpos : 0 < ‖lagPole q₀ + d - lagPole q‖ := by linarith
      rw [div_le_iff₀ hpos]
      calc ‖lagWeight q‖ = ‖lagWeight q‖ * (2 / ε) * (ε / 2) := by field_simp
        _ ≤ ‖lagWeight q‖ * max (1 / ‖d‖) (2 / ε) * ‖lagPole q₀ + d - lagPole q‖ := by
            gcongr
            exact le_max_right _ _
  unfold lagPoleSeries
  rw [← hsumm.tsum_subtype_add_tsum_subtype_compl S]
  have hfib : ∀ q : S, lagWeight q.1 / (lagPole q₀ + d - lagPole q.1) = lagWeight q₀ / d := by
    intro q
    have hq' : (q.1.1 : ℂ) = (q₀.1 : ℂ) := congrArg (fun r : XiDivisorSupport => (r : ℂ)) q.2
    unfold lagWeight lagPole
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
  have hcompl : ‖∑' q : ↑Sᶜ, lagWeight q.1 / (lagPole q₀ + d - lagPole q.1)‖ ≤
      (2 / ε) * ∑' q : XiZeroCopy, ‖lagWeight q‖ := by
    have hb : ∀ q : ↑Sᶜ, ‖lagWeight q.1 / (lagPole q₀ + d - lagPole q.1)‖ ≤
        (2 / ε) * ‖lagWeight q.1‖ := by
      intro q
      have := hoff q.1 q.2
      have hpos : 0 < ‖lagPole q₀ + d - lagPole q.1‖ := by linarith
      rw [norm_div, div_le_iff₀ hpos]
      calc ‖lagWeight q.1‖ = (2 / ε) * ‖lagWeight q.1‖ * (ε / 2) := by field_simp
        _ ≤ (2 / ε) * ‖lagWeight q.1‖ * ‖lagPole q₀ + d - lagPole q.1‖ := by gcongr
    have hs1 : Summable (fun q : ↑Sᶜ => ‖lagWeight q.1 / (lagPole q₀ + d - lagPole q.1)‖) :=
      (hsumm.norm.subtype _)
    have hs2 : Summable (fun q : ↑Sᶜ => (2 / ε) * ‖lagWeight q.1‖) :=
      (summable_norm_lagWeight.mul_left _).subtype _
    calc ‖∑' q : ↑Sᶜ, lagWeight q.1 / (lagPole q₀ + d - lagPole q.1)‖
        ≤ ∑' q : ↑Sᶜ, ‖lagWeight q.1 / (lagPole q₀ + d - lagPole q.1)‖ :=
          norm_tsum_le_tsum_norm hs1
      _ ≤ ∑' q : ↑Sᶜ, (2 / ε) * ‖lagWeight q.1‖ := hs1.tsum_le_tsum hb hs2
      _ = (2 / ε) * ∑' q : ↑Sᶜ, ‖lagWeight q.1‖ := tsum_mul_left
      _ ≤ (2 / ε) * ∑' q : XiZeroCopy, ‖lagWeight q‖ := by
          gcongr
          exact Summable.tsum_subtype_le (fun q : XiZeroCopy => ‖lagWeight q‖) Sᶜ
            (fun _ => norm_nonneg _) summable_norm_lagWeight
  have hmain : ‖lagWeight q₀‖ / ‖d‖ ≤ ‖Nat.card S • (lagWeight q₀ / d)‖ := by
    rw [nsmul_eq_mul, norm_mul, Complex.norm_natCast, norm_div]
    have : (1 : ℝ) ≤ Nat.card S := by exact_mod_cast hcard
    calc ‖lagWeight q₀‖ / ‖d‖ = 1 * (‖lagWeight q₀‖ / ‖d‖) := by ring
      _ ≤ (Nat.card S : ℝ) * (‖lagWeight q₀‖ / ‖d‖) := by gcongr
  calc ‖lagWeight q₀‖ / ‖d‖ - (2 / ε) * ∑' q : XiZeroCopy, ‖lagWeight q‖
      ≤ ‖Nat.card S • (lagWeight q₀ / d)‖ -
          ‖∑' q : ↑Sᶜ, lagWeight q.1 / (lagPole q₀ + d - lagPole q.1)‖ := by linarith
    _ ≤ ‖Nat.card S • (lagWeight q₀ / d) +
          ∑' q : ↑Sᶜ, lagWeight q.1 / (lagPole q₀ + d - lagPole q.1)‖ := by
        have := norm_sub_norm_le (Nat.card S • (lagWeight q₀ / d))
          (-(∑' q : ↑Sᶜ, lagWeight q.1 / (lagPole q₀ + d - lagPole q.1)))
        rw [norm_neg, sub_neg_eq_add] at this
        exact this

/-! ## Approach along a tilted ray -/

/-- **Analytic extension of the lag pole series up to finitely many subtracted poles.** Let `P` be
finite, `R` holomorphic off `P` and `F` holomorphic on `a < Re z < 2`. If `F + R = G` on `Re s > ½`
off `P`, then every zero copy whose pole `ρ − ½` lies off `P` has real part at most `½ + a`. -/
theorem re_le_half_add_of_lagPoleSeries_sub_extension {a : ℝ} (ha : 0 ≤ a) {F R : ℂ → ℂ}
    {P : Set ℂ} (hP : P.Finite)
    (hFd : ∀ z : ℂ, a < z.re → z.re < 2 → DifferentiableAt ℂ F z)
    (hRd : ∀ z : ℂ, z ∉ P → DifferentiableAt ℂ R z)
    (hFG : ∀ s : ℂ, 1 / 2 < s.re → s ∉ P → F s + R s = lagPoleSeries s)
    (q₀ : XiZeroCopy) (hq₀ : lagPole q₀ ∉ P) :
    (q₀.1 : ℂ).re ≤ 1 / 2 + a := by
  by_contra hlt
  set p₀ : ℂ := lagPole q₀ with hp₀
  have hp₀re : p₀.re = (q₀.1 : ℂ).re - 1 / 2 := by
    rw [hp₀]; unfold lagPole; simp
  have hp₀a : a < p₀.re := by rw [hp₀re]; linarith [not_le.mp hlt]
  have hp₀half : p₀.re < 1 / 2 := lagPole_re_lt_half q₀
  -- the finitely many obstacles near `p₀`
  set Z : Set ℂ := (fun z : ℂ => z + 1 / 2) ⁻¹'
      (xiZeroSet_weilLagFunctionCriterion ∩ Metric.closedBall (p₀ + 1 / 2) 3) with hZ
  have hZfin : Z.Finite :=
    (finite_xiZeroSet_inter (isCompact_closedBall _ _)).preimage
      (fun x _ y _ h => by simpa using h)
  set B : Set ℂ := Z ∪ P with hB
  have hBfin : B.Finite := hZfin.union hP
  -- a slope avoiding every obstacle
  set Sl : Set ℝ := (fun b : ℂ => (b - p₀).im / (b - p₀).re) '' B with hSl
  have hSlc : Sl.Countable := (hBfin.image _).countable
  obtain ⟨σ, hσSl, hσ0, hσ1⟩ :=
    (hSlc.dense_compl ℝ).exists_between (show (0:ℝ) < 1 by norm_num)
  set v : ℂ := 1 + σ * I with hv
  have hvnorm_pos : 0 < ‖v‖ := by
    refine norm_pos_iff.mpr fun h => ?_
    have := congrArg Complex.re h
    simp [hv] at this
  have hvnorm : ‖v‖ ≤ 2 := by
    calc ‖v‖ ≤ ‖(1:ℂ)‖ + ‖(σ:ℂ) * I‖ := norm_add_le _ _
      _ = 1 + |σ| := by simp
      _ ≤ 2 := by rw [abs_of_pos hσ0]; linarith
  set ℓ : ℝ → ℂ := fun t => p₀ + t * v with hℓ
  have hℓre : ∀ t : ℝ, (ℓ t).re = p₀.re + t := by intro t; simp [hℓ, hv]
  have hℓB : ∀ t : ℝ, 0 < t → ℓ t ∉ B := by
    intro t ht hmem
    apply hσSl
    refine ⟨ℓ t, hmem, ?_⟩
    have e : ℓ t - p₀ = t * v := by simp [hℓ]
    show (ℓ t - p₀).im / (ℓ t - p₀).re = σ
    rw [e]
    simp [hv]
    field_simp
  have hℓball : ∀ t : ℝ, 0 < t → t < 3 / 2 →
      ℓ t + 1 / 2 ∈ Metric.closedBall (p₀ + 1 / 2) 3 := by
    intro t ht ht2
    rw [Metric.mem_closedBall, Complex.dist_eq]
    have e : ℓ t + 1 / 2 - (p₀ + 1 / 2) = t * v := by simp [hℓ]
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    nlinarith
  have hℓP : ∀ t : ℝ, 0 < t → ℓ t ∉ P := fun t ht h => hℓB t ht (Or.inr h)
  have hℓxi : ∀ t : ℝ, 0 < t → t < 3 / 2 → xi (ℓ t + 1 / 2) ≠ 0 := fun t ht ht2 h =>
    hℓB t ht (Or.inl (show ℓ t + 1 / 2 ∈ xiZeroSet_weilLagFunctionCriterion ∩
      Metric.closedBall (p₀ + 1 / 2) 3 from ⟨h, hℓball t ht ht2⟩))
  -- both sides are real-analytic along the ray
  set T : ℝ := 3 / 2 - p₀.re with hT
  have hTpos : 0 < T := by rw [hT]; linarith
  set U : Set ℝ := Ioo (0:ℝ) T with hU
  set V : Set ℂ := {z : ℂ | a < z.re ∧ z.re < 2} with hV
  have hVopen : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hℓV : ∀ t ∈ U, ℓ t ∈ V := by
    intro t ht
    simp only [hV, Set.mem_setOf_eq, hℓre]
    constructor <;> linarith [ht.1, ht.2]
  have hℓan : ∀ t : ℝ, AnalyticAt ℝ ℓ t := fun t =>
    analyticAt_const.add ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const)
  have hFdiff : DifferentiableOn ℂ F V := fun z hz => (hFd z hz.1 hz.2).differentiableWithinAt
  have hRdiff : DifferentiableOn ℂ R Pᶜ := fun z hz => (hRd z hz).differentiableWithinAt
  have hFR : AnalyticOnNhd ℝ (fun t : ℝ => F (ℓ t) + R (ℓ t)) U := by
    intro t ht
    have hFz : AnalyticAt ℂ F (ℓ t) := hFdiff.analyticAt (hVopen.mem_nhds (hℓV t ht))
    have hRz : AnalyticAt ℂ R (ℓ t) :=
      hRdiff.analyticAt (hP.isClosed.isOpen_compl.mem_nhds (hℓP t ht.1))
    exact (hFz.restrictScalars.comp (hℓan t)).add (hRz.restrictScalars.comp (hℓan t))
  have hG : AnalyticOnNhd ℝ (fun t : ℝ => lagPoleSeries (ℓ t)) U := by
    intro t ht
    have ht2 : t < 3 / 2 := by have := ht.2; rw [hT] at this; linarith
    exact (analyticAt_lagPoleSeries (hℓxi t ht.1 ht2)).restrictScalars.comp (hℓan t)
  -- they agree to the right of `Re = ½`, hence on the whole ray
  set t₁ : ℝ := (1 / 2 - p₀.re + T) / 2 with ht₁
  have ht₁U : t₁ ∈ U := ⟨by rw [ht₁, hT]; linarith, by rw [ht₁, hT]; linarith⟩
  have hfg : (fun t : ℝ => F (ℓ t) + R (ℓ t)) =ᶠ[𝓝 t₁] (fun t : ℝ => lagPoleSeries (ℓ t)) := by
    refine Filter.eventuallyEq_of_mem
      (Ioo_mem_nhds (show 1 / 2 - p₀.re < t₁ by rw [ht₁, hT]; linarith)
        (show t₁ < T by rw [ht₁, hT]; linarith)) fun t ht => ?_
    exact hFG _ (by rw [hℓre]; linarith [ht.1]) (hℓP t (by linarith [ht.1]))
  have heq := hFR.eqOn_of_preconnected_of_eventuallyEq hG isPreconnected_Ioo ht₁U hfg
  -- `F + R` stays bounded at `p₀` while `G` blows up
  have hFRcont : ContinuousAt (fun z => F z + R z) p₀ :=
    (hFd p₀ hp₀a (by linarith)).continuousAt.add (hRd p₀ hq₀).continuousAt
  have hℓ0 : Tendsto ℓ (𝓝 0) (𝓝 p₀) := by
    have : Tendsto (fun t : ℝ => p₀ + (t : ℂ) * v) (𝓝 0) (𝓝 (p₀ + ((0:ℝ) : ℂ) * v)) :=
      tendsto_const_nhds.add ((Complex.continuous_ofReal.tendsto 0).mul tendsto_const_nhds)
    simpa using this
  have hcomp : Tendsto (fun t : ℝ => F (ℓ t) + R (ℓ t)) (𝓝 0) (𝓝 (F p₀ + R p₀)) :=
    hFRcont.tendsto.comp hℓ0
  obtain ⟨δ, hδ, hδF⟩ := Metric.eventually_nhds_iff.mp (Metric.tendsto_nhds.mp hcomp 1 one_pos)
  obtain ⟨ε, hε, C, hC⟩ := norm_lagPoleSeries_ge_disc q₀
  set C' : ℝ := max C 0 with hC'
  have hC0 : 0 ≤ C' := le_max_right _ _
  set Bd : ℝ := ‖F p₀ + R p₀‖ + 1 with hBd
  have hw : 0 < ‖lagWeight q₀‖ := by
    rw [norm_pos_iff]
    unfold lagWeight
    exact one_div_ne_zero (mul_ne_zero (xiZeroCopy_ne_zero q₀) (xiZeroCopy_one_sub_ne_zero q₀))
  have hK : 0 < Bd + C' + 1 := by positivity
  set m : ℝ := min (min δ (ε / 2)) (min T (‖lagWeight q₀‖ / (2 * (Bd + C' + 1)))) with hm
  have hmpos : 0 < m := lt_min (lt_min hδ (by positivity)) (lt_min hTpos (by positivity))
  have hmδ : m ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hmε : m ≤ ε / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hmT : m ≤ T := (min_le_right _ _).trans (min_le_left _ _)
  have hmw : m ≤ ‖lagWeight q₀‖ / (2 * (Bd + C' + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  set t₀ : ℝ := m / 2 with ht₀
  have ht₀pos : 0 < t₀ := half_pos hmpos
  have ht₀U : t₀ ∈ U := ⟨ht₀pos, by rw [ht₀]; linarith⟩
  have hFb : ‖F (ℓ t₀) + R (ℓ t₀)‖ ≤ Bd := by
    have hd : dist t₀ 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht₀pos]; rw [ht₀]; linarith
    have := hδF hd
    rw [dist_eq_norm] at this
    calc ‖F (ℓ t₀) + R (ℓ t₀)‖
        = ‖(F (ℓ t₀) + R (ℓ t₀) - (F p₀ + R p₀)) + (F p₀ + R p₀)‖ := by congr 1; ring
      _ ≤ ‖F (ℓ t₀) + R (ℓ t₀) - (F p₀ + R p₀)‖ + ‖F p₀ + R p₀‖ := norm_add_le _ _
      _ ≤ Bd := by rw [hBd]; linarith
  have hdn : ‖(t₀ : ℂ) * v‖ = t₀ * ‖v‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht₀pos]
  have hGb : Bd < ‖lagPoleSeries (ℓ t₀)‖ := by
    have h1 := hC ((t₀ : ℂ) * v) (by rw [hdn]; positivity)
      (by rw [hdn]; rw [ht₀]; nlinarith)
    have h2 : ‖lagWeight q₀‖ / (2 * t₀) ≤ ‖lagWeight q₀‖ / ‖(t₀ : ℂ) * v‖ := by
      rw [hdn]
      exact div_le_div_of_nonneg_left hw.le (by positivity) (by nlinarith)
    have h3 : 2 * (Bd + C' + 1) ≤ ‖lagWeight q₀‖ / (2 * t₀) := by
      rw [le_div_iff₀ (by positivity)]
      have : 2 * t₀ = m := by rw [ht₀]; ring
      rw [this]
      calc 2 * (Bd + C' + 1) * m
          ≤ 2 * (Bd + C' + 1) * (‖lagWeight q₀‖ / (2 * (Bd + C' + 1))) := by gcongr
        _ = ‖lagWeight q₀‖ := by field_simp
    have hℓt : ℓ t₀ = lagPole q₀ + (t₀ : ℂ) * v := rfl
    rw [hℓt]
    linarith [le_max_left C 0]
  have hEq : F (ℓ t₀) + R (ℓ t₀) = lagPoleSeries (ℓ t₀) := heq ht₀U
  rw [hEq] at hFb
  linarith


/-! ## Landau's theorem for a one-sided bounded real function -/

/-- The clipped density `max(M e^{au} − φ(u), 0)`. -/
def landauDensity (φ : ℝ → ℝ) (a M : ℝ) (u : ℝ) : NNReal :=
  Real.toNNReal (M * Real.exp (a * u) - φ u)

theorem measurable_landauDensity {φ : ℝ → ℝ} (hφ : Measurable φ) (a M : ℝ) :
    Measurable (landauDensity φ a M) :=
  ((measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id))).sub
    hφ).real_toNNReal

/-- `(M e^{au} − φ)₊ du + e^{au} du` on `(0,∞)`. -/
def landauMeasure (φ : ℝ → ℝ) (a M : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0:ℝ))).withDensity (fun u => (landauDensity φ a M u : ENNReal))
    + (volume.restrict (Ioi (0:ℝ))).withDensity (fun u => (growthShiftDensity a u : ENNReal))

theorem landauDensity_le {φ : ℝ → ℝ} {K a M : ℝ}
    (hK : ∀ u, 0 < u → |φ u| ≤ K * Real.exp (u / 2)) (ha : a ≤ 1 / 2) {u : ℝ} (hu : 0 < u) :
    ((landauDensity φ a M u : ℝ)) ≤ (|M| + |K|) * Real.exp (u / 2) := by
  unfold landauDensity
  rw [Real.coe_toNNReal']
  have h1 := hK u hu
  have h2 : Real.exp (a * u) ≤ Real.exp (u / 2) := Real.exp_le_exp.mpr (by nlinarith)
  have hE := Real.exp_pos (u / 2)
  have h3 : M * Real.exp (a * u) ≤ |M| * Real.exp (u / 2) := by
    calc M * Real.exp (a * u) ≤ |M| * Real.exp (a * u) :=
          mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le
      _ ≤ |M| * Real.exp (u / 2) := mul_le_mul_of_nonneg_left h2 (abs_nonneg M)
  have h4 := neg_abs_le (φ u)
  have h5 : K * Real.exp (u / 2) ≤ |K| * Real.exp (u / 2) :=
    mul_le_mul_of_nonneg_right (le_abs_self K) hE.le
  rcases le_or_gt (M * Real.exp (a * u) - φ u) 0 with h | h
  · rw [max_eq_right h]; positivity
  · rw [max_eq_left h.le]; nlinarith [abs_nonneg M, abs_nonneg K]

theorem laplaceMass_landauDensity_ne_top {φ : ℝ → ℝ} (hφ : Measurable φ) {K a M σ : ℝ}
    (hK : ∀ u, 0 < u → |φ u| ≤ K * Real.exp (u / 2)) (ha : a ≤ 1 / 2) (hσ : 1 / 2 < σ) :
    laplaceMass ((volume.restrict (Ioi (0:ℝ))).withDensity
      (fun u => (landauDensity φ a M u : ENNReal))) σ ≠ ⊤ := by
  unfold laplaceMass
  have hg : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_landauDensity hφ a M).coe_nnreal_ennreal hg]
  refine ne_top_of_le_ne_top
    (integrableOn_growth_majorant (C := |M| + |K|) hσ).lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (landauDensity_le hK ha hu) (Real.exp_pos _).le

theorem laplaceMass_landau_eq (φ : ℝ → ℝ) (a M σ : ℝ) :
    laplaceMass (landauMeasure φ a M) σ =
      laplaceMass ((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun u => (landauDensity φ a M u : ENNReal))) σ + laplaceMass volume (σ - a) := by
  unfold laplaceMass landauMeasure
  rw [Measure.restrict_add, lintegral_add_measure]
  congr 1
  have := laplaceMass_growthShift a σ
  unfold laplaceMass at this
  exact this

theorem isAbscissa_landau {φ : ℝ → ℝ} (hφ : Measurable φ) {K a M : ℝ}
    (hK : ∀ u, 0 < u → |φ u| ≤ K * Real.exp (u / 2)) (ha : a < 1 / 2) :
    IsAbscissa (landauMeasure φ a M) (sInf {σ : ℝ | laplaceMass (landauMeasure φ a M) σ ≠ ⊤}) ∧
      a ≤ sInf {σ : ℝ | laplaceMass (landauMeasure φ a M) σ ≠ ⊤} := by
  set S := {σ : ℝ | laplaceMass (landauMeasure φ a M) σ ≠ ⊤} with hS
  have hpos : ∀ σ ∈ S, a < σ := by
    intro σ hσ
    by_contra hle
    apply hσ
    rw [laplaceMass_landau_eq]
    rcases lt_or_eq_of_le (not_lt.mp hle) with h | h
    · rw [laplaceMass_volume_eq_top (by linarith), add_top]
    · rw [h, sub_self, laplaceMass_volume_zero_eq_top, add_top]
  have hbdd : BddBelow S := ⟨a, fun σ hσ => (hpos σ hσ).le⟩
  have h1S : (1:ℝ) ∈ S := by
    show laplaceMass (landauMeasure φ a M) 1 ≠ ⊤
    rw [laplaceMass_landau_eq]
    exact ENNReal.add_ne_top.mpr ⟨laplaceMass_landauDensity_ne_top hφ hK ha.le (by norm_num),
      laplaceMass_volume_ne_top (by linarith)⟩
  have hne : S.Nonempty := ⟨1, h1S⟩
  refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, le_csInf hne fun σ hσ => (hpos σ hσ).le⟩
  · obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hne hσ
    exact ne_top_of_le_ne_top hσ'S (laplaceMass_antitone _ hlt.le)
  · by_contra h
    exact absurd (csInf_le hbdd (show σ ∈ S from h)) (not_le.mpr hσ)

theorem integrable_cexp_landauDensity {φ : ℝ → ℝ} (hφ : Measurable φ) {K a M : ℝ}
    (hK : ∀ u, 0 < u → |φ u| ≤ K * Real.exp (u / 2)) (ha : a ≤ 1 / 2) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    Integrable (fun u : ℝ => Complex.exp (-s * (u : ℂ)))
      (((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun u => (landauDensity φ a M u : ENNReal))).restrict (Ioi 0)) := by
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, integrable_withDensity_iff_integrable_smul (measurable_landauDensity hφ a M)]
  refine (integrableOn_growth_majorant (C := |M| + |K|) (by exact hs)).mono' ?_ ?_
  · exact ((measurable_landauDensity hφ a M).coe_nnreal_real.aestronglyMeasurable.smul
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [NNReal.smul_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _),
      norm_cexp_neg_mul]
    exact mul_le_mul_of_nonneg_right (landauDensity_le hK ha hu) (Real.exp_pos _).le

/-- `φ(u) e^{−su}` is integrable on `(0,∞)` for `Re s > ½`. -/
theorem integrable_ofReal_mul_cexp {φ : ℝ → ℝ} (hφ : Measurable φ) {K : ℝ}
    (hK : ∀ u, 0 < u → |φ u| ≤ K * Real.exp (u / 2)) {s : ℂ} (hs : 1 / 2 < s.re) :
    IntegrableOn (fun u : ℝ => (φ u : ℂ) * Complex.exp (-s * (u : ℂ))) (Ioi 0) := by
  refine (integrableOn_growth_majorant (C := K) (σ := s.re) hs).mono' ?_ ?_
  · exact (Complex.measurable_ofReal.comp hφ).aestronglyMeasurable.mul
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_neg_mul]
    exact mul_le_mul_of_nonneg_right (hK u hu) (Real.exp_pos _).le

/-- On `Re s > ½` the complex Laplace transform of the Landau measure is `(M+1)/(s − a) − Λ(s)`,
where `Λ` is the Laplace transform of `φ`. -/
theorem complexLaplace_landau_eq {φ : ℝ → ℝ} (hφ : Measurable φ) {K a M : ℝ}
    (hK : ∀ u, 0 < u → |φ u| ≤ K * Real.exp (u / 2)) (ha : a < 1 / 2)
    (hM : ∀ u, 0 ≤ u → φ u ≤ M * Real.exp (a * u)) {Λ : ℂ → ℂ}
    (hΛφ : ∀ s : ℂ, 1 / 2 < s.re →
      ∫ u in Ioi (0:ℝ), (φ u : ℂ) * Complex.exp (-s * (u : ℂ)) = Λ s)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    complexLaplace (landauMeasure φ a M) s = ((M : ℂ) + 1) / (s - a) - Λ s := by
  have hsa : a < s.re := by linarith
  have hsa' : 0 < (s - a).re := by simp; linarith
  have hexpInt' : IntegrableOn (fun u : ℝ => Complex.exp (-(s - a) * (u : ℂ))) (Ioi 0) := by
    have hc : Continuous (fun u : ℝ => Complex.exp (-(s - a) * (u : ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
    exact (exp_neg_integrableOn_Ioi 0 hsa').mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => le_of_eq (norm_cexp_neg_mul _ u))
  unfold complexLaplace landauMeasure
  rw [Measure.restrict_add, integral_add_measure (integrable_cexp_landauDensity hφ hK ha.le hs)
    (integrable_cexp_growthShift hsa), complexLaplace_growthShift hsa]
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, integral_withDensity_eq_integral_smul (measurable_landauDensity hφ a M)]
  have hpt : ∀ u ∈ Ioi (0:ℝ), landauDensity φ a M u • Complex.exp (-s * (u : ℂ)) =
      (M : ℂ) * Complex.exp (-(s - a) * (u : ℂ)) -
        ((φ u : ℂ) * Complex.exp (-s * (u : ℂ))) := by
    intro u hu
    rw [NNReal.smul_def, Complex.real_smul]
    unfold landauDensity
    rw [Real.coe_toNNReal _ (by linarith [hM u (le_of_lt hu)])]
    push_cast
    rw [show Complex.exp (-(s - a) * (u : ℂ)) = Complex.exp (a * u) * Complex.exp (-s * (u : ℂ))
      by rw [← Complex.exp_add]; congr 1; ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_sub (hexpInt'.const_mul _) (integrable_ofReal_mul_cexp hφ hK hs),
    integral_const_mul, integral_cexp_neg_mul_Ioi hsa', hΛφ s hs]
  have hne : (s - a) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  field_simp
  ring

/-- **Landau: the abscissa of the Landau measure is `a`.** -/
theorem abscissa_landau_eq {φ : ℝ → ℝ} (hφ : Measurable φ) {K a M : ℝ}
    (hK : ∀ u, 0 < u → |φ u| ≤ K * Real.exp (u / 2)) (ha0 : 0 ≤ a) (ha : a < 1 / 2)
    (hM : ∀ u, 0 ≤ u → φ u ≤ M * Real.exp (a * u)) {Λ : ℂ → ℂ}
    (hΛ : ∀ t : ℝ, a < t → AnalyticAt ℂ Λ t)
    (hΛφ : ∀ s : ℂ, 1 / 2 < s.re →
      ∫ u in Ioi (0:ℝ), (φ u : ℂ) * Complex.exp (-s * (u : ℂ)) = Λ s) :
    IsAbscissa (landauMeasure φ a M) a := by
  obtain ⟨hc, hac⟩ := isAbscissa_landau (M := M) hφ hK ha
  set c : ℝ := sInf {σ : ℝ | laplaceMass (landauMeasure φ a M) σ ≠ ⊤} with hcdef
  set H : ℂ → ℂ := fun z => ((M : ℂ) + 1) / (z - a) - Λ z with hH
  have hHan : ∀ z : ℂ, z ≠ a → AnalyticAt ℂ Λ z → AnalyticAt ℂ H z := fun z hza hz =>
    (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hza)).sub hz
  rcases hac.lt_or_eq with hpos | hzero
  · exfalso
    have hc34 : c ≤ 3 / 4 := by
      refine csInf_le ⟨a, fun σ hσ => ?_⟩ ?_
      · by_contra hlt
        apply hσ
        rw [laplaceMass_landau_eq, laplaceMass_volume_eq_top (by linarith [not_le.mp hlt]),
          add_top]
      · show laplaceMass (landauMeasure φ a M) (3 / 4) ≠ ⊤
        rw [laplaceMass_landau_eq]
        exact ENNReal.add_ne_top.mpr ⟨laplaceMass_landauDensity_ne_top hφ hK ha.le (by norm_num),
          laplaceMass_volume_ne_top (by linarith)⟩
    obtain ⟨d, hd, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hΛ c hpos).eventually_analyticAt
    set δ : ℝ := min (c - a) d / 2 with hδdef
    have hδ : 0 < δ := by rw [hδdef]; exact half_pos (lt_min (by linarith) hd)
    have hδc : δ ≤ (c - a) / 2 := by rw [hδdef]; linarith [min_le_left (c - a) d]
    have hδd : δ ≤ d / 2 := by rw [hδdef]; linarith [min_le_right (c - a) d]
    refine false_of_analyticAt_abscissa hc hδ (Φ := H) ?_ ?_
    · intro z hz
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      have hzre : (c + a) / 2 < z.re := by
        have := Complex.abs_re_le_norm (z - c)
        rw [Complex.sub_re, Complex.ofReal_re] at this
        have := abs_le.mp this
        linarith
      have hza : z ≠ a := fun h => by rw [h] at hzre; simp at hzre; linarith
      refine hHan z hza (hball z ?_)
      rw [Metric.mem_ball, Complex.dist_eq]
      linarith
    · intro σ hσc _
      have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hTdiff : DifferentiableOn ℂ (complexLaplace (landauMeasure φ a M)) {z : ℂ | c < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hT : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace (landauMeasure φ a M) (t : ℂ))
          (Ioi c) := by
        intro t ht
        have h1 : AnalyticAt ℂ (complexLaplace (landauMeasure φ a M)) (t : ℂ) :=
          hTdiff.analyticAt (hV.mem_nhds (by simpa using ht))
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have hHt : AnalyticOnNhd ℝ (fun t : ℝ => H (t : ℂ)) (Ioi c) := by
        intro t ht
        have hta : a < t := lt_trans hpos ht
        have h1 : AnalyticAt ℂ H (t : ℂ) :=
          hHan _ (by exact_mod_cast hta.ne') (hΛ t hta)
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have h1mem : (1 : ℝ) ∈ Ioi c := by show c < 1; linarith
      have hfg : (fun t : ℝ => complexLaplace (landauMeasure φ a M) (t : ℂ)) =ᶠ[𝓝 (1:ℝ)]
          (fun t : ℝ => H (t : ℂ)) := by
        refine Filter.eventuallyEq_of_mem
          (Ioo_mem_nhds (by norm_num : (1/2 : ℝ) < 1) (by norm_num : (1:ℝ) < 3/2)) fun t ht => ?_
        exact complexLaplace_landau_eq hφ hK ha hM hΛφ (by simpa using ht.1)
      have heq := hT.eqOn_of_preconnected_of_eventuallyEq hHt isPreconnected_Ioi h1mem hfg
      have hσ : complexLaplace (landauMeasure φ a M) (σ : ℂ) = H (σ : ℂ) :=
        heq (show σ ∈ Ioi c from hσc)
      rw [← hσ, complexLaplace_ofReal]
  · rw [← hzero] at hc
    exact hc

/-- **Landau's theorem.** Let `φ` be real, `|φ(u)| ≤ K e^{u/2}`, and `φ(u) ≤ M e^{au}` for `u ≥ 0`
with `0 ≤ a < ½`. If the Laplace transform `Λ` of `φ` on `Re s > ½` is analytic at every real point
`t > a`, then `Λ` extends holomorphically to `Re s > a`. -/
theorem exists_differentiable_extension_of_le_exp {φ : ℝ → ℝ} (hφ : Measurable φ) {K a M : ℝ}
    (hK : ∀ u, 0 < u → |φ u| ≤ K * Real.exp (u / 2)) (ha0 : 0 ≤ a) (ha : a < 1 / 2)
    (hM : ∀ u, 0 ≤ u → φ u ≤ M * Real.exp (a * u)) {Λ : ℂ → ℂ}
    (hΛ : ∀ t : ℝ, a < t → AnalyticAt ℂ Λ t)
    (hΛφ : ∀ s : ℂ, 1 / 2 < s.re →
      ∫ u in Ioi (0:ℝ), (φ u : ℂ) * Complex.exp (-s * (u : ℂ)) = Λ s) :
    ∃ F : ℂ → ℂ, (∀ z : ℂ, a < z.re → DifferentiableAt ℂ F z) ∧
      ∀ s : ℂ, 1 / 2 < s.re → F s = Λ s := by
  have hc := abscissa_landau_eq hφ hK ha0 ha hM hΛ hΛφ
  refine ⟨fun z => ((M : ℂ) + 1) / (z - a) - complexLaplace (landauMeasure φ a M) z,
    fun z hza => ?_, fun s hs => ?_⟩
  · have hz : z - a ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have h1 : DifferentiableAt ℂ (fun z : ℂ => ((M : ℂ) + 1) / (z - a)) z :=
      (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _)) hz
    exact h1.sub (hasDerivAt_complexLaplace hc hza).differentiableAt
  · simp only
    rw [complexLaplace_landau_eq hφ hK ha hM hΛφ hs]
    ring

end

end RHTower
