import GaloisForLFunctions.RHTower.PrimeLagLandauContinuation
import GaloisForLFunctions.RHTower.WeilLagFunctionPrimeGap
import GaloisForLFunctions.RHTower.LandauSummabilityTransfer

/-!
# The prime-power lag criterion for the Riemann hypothesis

If the lag values `a_n = Φ(log n)` are bounded above at all prime powers, the Riemann hypothesis
holds.  Under `¬RH` let `Θ` be the supremum of the real parts of the zeros; the prime-lag strip
theorem gives `Θ ≤ 3/4`.  The nonnegative Dirichlet series `Σ (M − a_n)Λ(n) n^{−1−s}` converges
for `Re s > Θ − ½` and equals the zero-side continuation `G_M`, which is analytic on a small box
around the real point `Θ − ½ + 2η`; Landau's theorem then forces convergence at a real point to
the left of `Θ − ½`, so the series is analytic on a half-plane containing a pole `ρ₀ − ½` of
`G_M`, which is impossible.
-/

open Complex Filter Topology Set Metric
open ArithmeticFunction (vonMangoldt)

namespace RHTower

noncomputable section

/-! ## The supremum of the real parts -/

/-- The supremum of the real parts of the zero copies. -/
def zeroReSup : ℝ := sSup (Set.range fun q : XiZeroCopy => (q.1 : ℂ).re)

theorem bddAbove_range_re : BddAbove (Set.range fun q : XiZeroCopy => (q.1 : ℂ).re) :=
  ⟨1, by rintro _ ⟨q, rfl⟩; exact (xiZeroCopy_re_lt_one q).le⟩

theorem re_le_zeroReSup (q : XiZeroCopy) : (q.1 : ℂ).re ≤ zeroReSup :=
  le_csSup bddAbove_range_re ⟨q, rfl⟩

theorem zeroReSup_le [Nonempty XiZeroCopy] {θ : ℝ} (h : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) :
    zeroReSup ≤ θ :=
  csSup_le (Set.range_nonempty _) (by rintro _ ⟨q, rfl⟩; exact h q)

theorem exists_re_gt_of_lt_zeroReSup [Nonempty XiZeroCopy] {b : ℝ} (hb : b < zeroReSup) :
    ∃ q : XiZeroCopy, b < (q.1 : ℂ).re := by
  obtain ⟨_, ⟨q, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) hb
  exact ⟨q, hlt⟩

/-- A positive lower bound for `|γ|` over the copies of height at most `6`. -/
theorem exists_pos_le_abs_ordinate :
    ∃ γmin : ℝ, 0 < γmin ∧ ∀ q : XiZeroCopy, |zeroOrdinate q| ≤ 6 → γmin ≤ |zeroOrdinate q| := by
  classical
  set F := (finite_copies_abs_im_le 6).toFinset with hF
  rcases F.eq_empty_or_nonempty with h | hne
  · refine ⟨1, one_pos, fun q hq => ?_⟩
    have : q ∈ F := by rw [hF, Set.Finite.mem_toFinset]; exact hq
    rw [h] at this
    exact absurd this (Finset.notMem_empty q)
  · obtain ⟨q₀, _, hmin⟩ := F.exists_min_image (fun q => |zeroOrdinate q|) hne
    refine ⟨|zeroOrdinate q₀|, abs_pos.mpr (zeroOrdinate_ne_zero' q₀), fun q hq => ?_⟩
    exact hmin q (by rw [hF, Set.Finite.mem_toFinset]; exact hq)

/-- Prime powers include the primes. -/
theorem primeLag_le_of_primePowerLag_le {M : ℝ} (hM : ∀ n : ℕ, vonMangoldt n ≠ 0 → integerLag n ≤ M)
    (p : ℕ) (hp : p.Prime) : integerLag p ≤ M := by
  apply hM
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
  exact (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'

/-! ## The Landau transfer step -/

/-- **Landau transfer.**  Under `¬RH` and bounded prime-power lags, the coefficient series
converges at a real point to the left of `Θ − ½`, with the auxiliary parameter `η`. -/
theorem landau_transfer_step {M : ℝ} (hM : ∀ n : ℕ, vonMangoldt n ≠ 0 → integerLag n ≤ M)
    (hRH : ¬ RiemannHypothesis) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 20 ∧ η < zeroReSup - 1 / 2 ∧
      (∀ q : XiZeroCopy, |zeroOrdinate q| ≤ 6 → 3 * η ≤ |zeroOrdinate q| / 2) ∧
      LSeriesSummable (fun n => (primeLagCoeff M n : ℂ)) ((zeroReSup - 1 / 2 - η / 4 : ℝ) : ℂ) := by
  obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_re_gt_half_of_not_rh hRH
  haveI : Nonempty XiZeroCopy := ⟨q₁⟩
  set Θ := zeroReSup with hΘ
  have hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ Θ := re_le_zeroReSup
  have hΘ12 : 1 / 2 < Θ := lt_of_lt_of_le hq₁ (re_le_zeroReSup q₁)
  have hΘ34 : Θ ≤ 3 / 4 :=
    zeroReSup_le (re_le_three_quarters_of_primeLag_le (primeLag_le_of_primePowerLag_le hM))
  obtain ⟨γmin, hγpos, hγmin⟩ := exists_pos_le_abs_ordinate
  set η : ℝ := min (1 / 20) (min ((Θ - 1 / 2) / 2) (γmin / 6)) with hη
  have hηpos : 0 < η := lt_min (by norm_num) (lt_min (by linarith) (by linarith))
  have hη20 : η ≤ 1 / 20 := min_le_left _ _
  have hηΘ : η ≤ (Θ - 1 / 2) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηγ : η ≤ γmin / 6 := (min_le_right _ _).trans (min_le_right _ _)
  have hηΘ' : η < Θ - 1 / 2 := by linarith
  refine ⟨η, hηpos, hη20, hηΘ', fun q hq => by linarith [hγmin q hq], ?_⟩
  -- the series converges at `σ₁ = Θ − ½ + η`
  have hsum : LSeriesSummable (fun n => (primeLagCoeff M n : ℂ)) ((Θ - 1 / 2 + η : ℝ) : ℂ) :=
    lagCoeff_LSeriesSummable hθ hΘ12.le (by simp; linarith)
  -- the continuation is differentiable on the closed ball of radius `5η/2` around `Θ − ½ + 2η`
  set R : NNReal := ⟨5 * η / 2, by positivity⟩ with hR
  have hRval : (R : ℝ) = 5 * η / 2 := rfl
  have hball : closedBall (((Θ - 1 / 2 + η) + η : ℝ) : ℂ) (R : ℝ) ⊆ landauBox Θ η 0 (3 * η) := by
    intro s hs
    rw [mem_closedBall, Complex.dist_eq] at hs
    have hre := Complex.abs_re_le_norm (s - (((Θ - 1 / 2 + η) + η : ℝ) : ℂ))
    have him := Complex.abs_im_le_norm (s - (((Θ - 1 / 2 + η) + η : ℝ) : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at hre
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at him
    rw [hRval] at hs
    have h1 := (abs_le.mp (hre.trans hs)).1
    have h2 := (abs_le.mp (hre.trans hs)).2
    refine ⟨by linarith, by linarith, ?_⟩
    rw [sub_zero]
    linarith [him.trans hs]
  have hGd : DifferentiableOn ℂ (landauG M)
      (closedBall (((Θ - 1 / 2 + η) + η : ℝ) : ℂ) (R : ℝ)) := by
    refine (differentiableOn_landauG (θ := Θ) (η := η) (t₀ := 0) (r := 3 * η) (M := M) hθ hΘ34 hη20
      (by linarith) (U := landauBox Θ η 0 (3 * η)) le_rfl ?_ ?_).mono hball
    · intro s hs
      have := hs.1
      linarith
    · intro q hq s hs h1
      have hqn : |zeroOrdinate q - 0| < 5 := hq
      rw [sub_zero] at hqn
      have hq6 : |zeroOrdinate q| ≤ 6 := by linarith
      have hγ := hγmin q hq6
      have him : (s + 3 / 2 - (q.1 : ℂ)).im = s.im - zeroOrdinate q := by simp [zeroOrdinate]
      rw [h1, Complex.one_im] at him
      have hs3 := hs.2.2
      rw [sub_zero] at hs3
      have habs : |zeroOrdinate q| = |s.im| := by
        rw [show zeroOrdinate q = s.im by linarith]
      linarith
  have hagree : ∀ s : ℂ, Θ - 1 / 2 + η < s.re →
      landauG M s = LSeries (fun n => (primeLagCoeff M n : ℂ)) s := by
    intro s hs
    rw [LSeries_lagCoeff_eq hθ hΘ12.le (by linarith)]
    rfl
  have hres := landau_local_summability_transfer (a := primeLagCoeff M) (lagCoeff_nonneg hM)
    (σ₁ := Θ - 1 / 2 + η) (h := η) hηpos hsum (R := R) (G := landauG M) hGd hagree
    (σ := Θ - 1 / 2 - η / 4) (by rw [hRval]; linarith)
  exact hres

/-! ## The residue of `−ζ'/ζ` at `1` along the real axis -/

/-- `−ζ'/ζ(1 + t) − 1/t` is bounded on `(0, 1/4]`. -/
theorem exists_bound_neg_logDeriv_zeta_sub_inv :
    ∃ B : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 / 4 →
      ‖-logDeriv riemannZeta (1 + t) - 1 / (t : ℂ)‖ ≤ B := by
  have hlim := tendsto_neg_logDeriv_riemannZeta_sub_one_div_real
  -- eventually within `1` of the limit
  have hev := Metric.tendsto_nhds.mp hlim 1 one_pos
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨δ, hδ, hδev⟩ := Metric.eventually_nhds_iff.mp hev
  set t₁ : ℝ := min (δ / 2) (1 / 4) with ht₁
  have ht₁pos : 0 < t₁ := lt_min (by linarith) (by norm_num)
  have ht₁δ : t₁ ≤ δ / 2 := min_le_left _ _
  have ht₁4 : t₁ ≤ 1 / 4 := min_le_right _ _
  -- the compact part `[t₁, 1/4]`
  have hcont : ContinuousOn (fun t : ℝ => -logDeriv riemannZeta (1 + t) - 1 / (t : ℂ)) (Icc t₁ (1 / 4)) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ht₁pos ht.1
    have h1 : (1 : ℂ) + t ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hζ : riemannZeta (1 + t) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
    have hd : DifferentiableAt ℂ (logDeriv riemannZeta) (1 + t) := differentiableAt_logDeriv_zeta h1 hζ
    have hc1 : ContinuousAt (fun t : ℝ => -logDeriv riemannZeta (1 + t)) t := by
      have := hd.continuousAt.comp (f := fun t : ℝ => (1 : ℂ) + t)
        (continuous_const.add Complex.continuous_ofReal).continuousAt
      exact this.neg
    have hc2 : ContinuousAt (fun t : ℝ => 1 / (t : ℂ)) t := by
      apply ContinuousAt.div continuousAt_const Complex.continuous_ofReal.continuousAt
      exact_mod_cast ht0.ne'
    exact (hc1.sub hc2).continuousWithinAt
  obtain ⟨B₂, hB₂⟩ := (isCompact_Icc (a := t₁) (b := (1 / 4 : ℝ))).exists_bound_of_continuousOn hcont
  refine ⟨max (Real.eulerMascheroniConstant + 1) B₂, fun t ht0 ht4 => ?_⟩
  rcases lt_or_ge t t₁ with hlt | hge
  · have hmem : dist (1 + t) 1 < δ := by
      rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith
    have hin : (1 + t : ℝ) ∈ Ioi (1 : ℝ) := by simp; linarith
    have h := hδev hmem hin
    rw [dist_eq_norm] at h
    have e : (-deriv riemannZeta ((1 + t : ℝ) : ℂ) / riemannZeta ((1 + t : ℝ) : ℂ) - 1 / (((1 + t : ℝ) : ℂ) - 1))
        = -logDeriv riemannZeta (1 + t) - 1 / (t : ℂ) := by
      rw [logDeriv_apply, neg_div]; push_cast; ring_nf
    rw [e] at h
    have hγ : ‖-(Real.eulerMascheroniConstant : ℂ)‖ = Real.eulerMascheroniConstant := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by have := eulerMascheroniConstant_gt; linarith)]
    calc ‖-logDeriv riemannZeta (1 + t) - 1 / (t : ℂ)‖
        = ‖(-logDeriv riemannZeta (1 + t) - 1 / (t : ℂ) - -(Real.eulerMascheroniConstant : ℂ))
            + -(Real.eulerMascheroniConstant : ℂ)‖ := by congr 1; ring
      _ ≤ ‖-logDeriv riemannZeta (1 + t) - 1 / (t : ℂ) - -(Real.eulerMascheroniConstant : ℂ)‖
            + ‖-(Real.eulerMascheroniConstant : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 + Real.eulerMascheroniConstant := by rw [hγ]; linarith
      _ ≤ max (Real.eulerMascheroniConstant + 1) B₂ := by
          have := le_max_left (Real.eulerMascheroniConstant + 1) B₂; linarith
  · exact (hB₂ t ⟨hge, ht4⟩).trans (le_max_right _ _)

/-! ## The pole of the continuation at a maximal zero -/

/-- The aliased weight at `ρ₀`: the sum of the weights of the copies over the same support point. -/
def aliasedWeight (q₀ : XiZeroCopy) : ℂ :=
  ∑ q ∈ (finite_nearSet (zeroOrdinate q₀)).toFinset.filter (fun q => (q.1 : ℂ) = (q₀.1 : ℂ)),
    lagWeight q

theorem aliasedWeight_re_pos (q₀ : XiZeroCopy) : 0 < (aliasedWeight q₀).re := by
  classical
  unfold aliasedWeight
  rw [Complex.re_sum]
  have hmem : q₀ ∈ (finite_nearSet (zeroOrdinate q₀)).toFinset.filter
      (fun q => (q.1 : ℂ) = (q₀.1 : ℂ)) := by
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨by simp [nearSet], rfl⟩
  calc (0 : ℝ) < (lagWeight q₀).re := lagWeight_re_pos q₀
    _ ≤ _ := Finset.single_le_sum (fun q _ => (lagWeight_re_pos q).le) hmem

theorem norm_aliasedWeight_pos (q₀ : XiZeroCopy) : 0 < ‖aliasedWeight q₀‖ :=
  lt_of_lt_of_le (lt_of_lt_of_le (aliasedWeight_re_pos q₀) (le_abs_self _))
    (Complex.abs_re_le_norm _)

/-- Points of the ray `ρ₀ − ½ + t`, `0 < t ≤ 1/4`, lie in the unit box around `γ₀`. -/
theorem ray_mem_landauBox {θ η : ℝ} (q₀ : XiZeroCopy) (hβ₀ : θ - η < (q₀.1 : ℂ).re)
    {t : ℝ} (ht : 0 < t) (ht4 : t ≤ 1 / 4) :
    (q₀.1 : ℂ) - 1 / 2 + t ∈ landauBox θ η (zeroOrdinate q₀) 1 := by
  have h1 := xiZeroCopy_re_lt_one q₀
  refine ⟨?_, ?_, ?_⟩
  · simp; linarith
  · simp; linarith
  · simp [zeroOrdinate]

/-- **The pole of the continuation at a maximal zero.**  If `ρ₀` has the largest real part
among the zeros with its ordinate, then along the ray `ρ₀ − ½ + t` the continuation is bounded
below by `‖W₀‖/t − C`. -/
theorem landauG_ray_lower_bound {θ η M : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hθ34 : θ ≤ 3 / 4) (hη : η ≤ 1 / 20) (hηpos : 0 < η) (q₀ : XiZeroCopy)
    (hβ₀ : θ - η < (q₀.1 : ℂ).re) (hβ₀' : 1 / 2 < (q₀.1 : ℂ).re)
    (hmax : ∀ q : XiZeroCopy, zeroOrdinate q = zeroOrdinate q₀ → (q.1 : ℂ).re ≤ (q₀.1 : ℂ).re) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 / 4 →
      ‖aliasedWeight q₀‖ / t - C ≤ ‖landauG M ((q₀.1 : ℂ) - 1 / 2 + t)‖ := by
  classical
  set ρ₀ : ℂ := (q₀.1 : ℂ) with hρ₀
  set γ₀ : ℝ := zeroOrdinate q₀ with hγ₀
  set N := (finite_nearSet γ₀).toFinset with hN
  set N' := N.filter (fun q => ¬ (q.1 : ℂ) = ρ₀) with hN'
  obtain ⟨B₁, hB₁⟩ := exists_bound_neg_logDeriv_zeta_sub_inv
  -- the `M` term on the closed segment
  have hMc : ContinuousOn (fun t : ℝ => (M : ℂ) * (-logDeriv riemannZeta (1 + (ρ₀ - 1 / 2 + t))))
      (Icc (0 : ℝ) (1 / 4)) := by
    intro t ht
    have hre : (1 + (ρ₀ - 1 / 2 + (t : ℂ))).re = 1 / 2 + ρ₀.re + t := by simp; ring
    have h1 : (1 : ℂ) + (ρ₀ - 1 / 2 + t) ≠ 1 := by
      intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith [ht.1]
    have hζ : riemannZeta (1 + (ρ₀ - 1 / 2 + t)) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by rw [hre]; linarith [ht.1])
    have hd := (differentiableAt_logDeriv_zeta h1 hζ).continuousAt
    have hc : ContinuousAt (fun t : ℝ => (1 : ℂ) + (ρ₀ - 1 / 2 + t)) t :=
      (continuous_const.add (continuous_const.add Complex.continuous_ofReal)).continuousAt
    have hcomp := ContinuousAt.comp (g := logDeriv riemannZeta)
      (f := fun t : ℝ => (1 : ℂ) + (ρ₀ - 1 / 2 + t)) hd hc
    exact (continuousAt_const.mul hcomp.neg).continuousWithinAt
  obtain ⟨B₂, hB₂⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 4)).exists_bound_of_continuousOn hMc
  -- the non-aliased near terms on the closed segment
  have hN'c : ContinuousOn (fun t : ℝ => ∑ q ∈ N', landauTerm_primeLagLandauContinuation q (ρ₀ - 1 / 2 + t))
      (Icc (0 : ℝ) (1 / 4)) := by
    apply continuousOn_finsetSum
    intro q hq t ht
    rw [hN', Finset.mem_filter] at hq
    have hqne : (q.1 : ℂ) ≠ ρ₀ := hq.2
    set w : ℂ := ρ₀ - 1 / 2 + t + 3 / 2 - (q.1 : ℂ) with hw
    have hwre : w.re = ρ₀.re + 1 + t - (q.1 : ℂ).re := by rw [hw]; simp; ring
    have hwim : w.im = γ₀ - zeroOrdinate q := by rw [hw]; simp [zeroOrdinate, hγ₀, hρ₀]
    have hw1 : w ≠ 1 := by
      intro h1
      have him := congrArg Complex.im h1
      rw [hwim, Complex.one_im] at him
      have hord : zeroOrdinate q = γ₀ := by linarith
      have hle := hmax q hord
      have hre := congrArg Complex.re h1
      rw [hwre, Complex.one_re] at hre
      have ht0 : t = 0 := by linarith [ht.1]
      apply hqne
      have : (q.1 : ℂ) = ρ₀ + t := by linear_combination -h1
      rw [this, ht0]; simp
    have hwθ : θ < w.re := by rw [hwre]; linarith [hθ q, ht.1]
    have hζ : riemannZeta w ≠ 0 :=
      riemannZeta_ne_zero_of_re_gt_bound hθ hwθ (by linarith [hθ q₀]) hw1
    have hd := (differentiableAt_logDeriv_zeta hw1 hζ).continuousAt
    rw [hw] at hd
    have hc : ContinuousAt (fun t : ℝ => ρ₀ - 1 / 2 + t + 3 / 2 - (q.1 : ℂ)) t :=
      ((continuous_const.add Complex.continuous_ofReal).add continuous_const |>.sub
        continuous_const).continuousAt
    have hcomp := ContinuousAt.comp (g := logDeriv riemannZeta)
      (f := fun t : ℝ => ρ₀ - 1 / 2 + t + 3 / 2 - (q.1 : ℂ)) hd hc
    exact (continuousAt_const.mul hcomp.neg).continuousWithinAt
  obtain ⟨B₃, hB₃⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 4)).exists_bound_of_continuousOn hN'c
  -- the far tail
  set B₄ : ℝ := ∑' q : XiZeroCopy,
    ‖lagWeight q‖ * (5 * logDerivZetaConstant * Real.log (2 + |zeroOrdinate q - γ₀|)) with hB₄
  refine ⟨‖aliasedWeight q₀‖ * B₁ + B₂ + B₃ + B₄, fun t ht ht4 => ?_⟩
  have hs : ρ₀ - 1 / 2 + t ∈ landauBox θ η γ₀ 1 := ray_mem_landauBox q₀ hβ₀ ht ht4
  rw [landauG_eq, tsum_landauTerm_split hθ hθ34 hη le_rfl hs]
  rw [← Finset.sum_filter_add_sum_filter_not N (fun q => (q.1 : ℂ) = ρ₀)]
  -- the aliased part is the residue term
  have hal : ∑ q ∈ N.filter (fun q => (q.1 : ℂ) = ρ₀), landauTerm_primeLagLandauContinuation q (ρ₀ - 1 / 2 + t)
      = aliasedWeight q₀ * (-logDeriv riemannZeta (1 + t)) := by
    unfold aliasedWeight
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mem_filter] at hq
    unfold landauTerm_primeLagLandauContinuation
    rw [hq.2]
    congr 2
    ring
  rw [hal]
  -- the far part
  have hfar : ‖∑' q : ↑(nearSet γ₀)ᶜ, landauTerm_primeLagLandauContinuation q (ρ₀ - 1 / 2 + t)‖ ≤ B₄ := by
    have hmaj := summable_far_majorant γ₀
    have hmaj0 : ∀ q : XiZeroCopy, 0 ≤ ‖lagWeight q‖
        * (5 * logDerivZetaConstant * Real.log (2 + |zeroOrdinate q - γ₀|)) := by
      intro q
      have : 0 ≤ Real.log (2 + |zeroOrdinate q - γ₀|) :=
        Real.log_nonneg (by linarith [abs_nonneg (zeroOrdinate q - γ₀)])
      have : 0 ≤ logDerivZetaConstant := by unfold logDerivZetaConstant; positivity
      positivity
    have hle : ∀ q : ↑(nearSet γ₀)ᶜ, ‖landauTerm_primeLagLandauContinuation q (ρ₀ - 1 / 2 + t)‖
        ≤ ‖lagWeight q‖ * (5 * logDerivZetaConstant * Real.log (2 + |zeroOrdinate q - γ₀|)) :=
      fun q => norm_landauTerm_le_far hθ hθ34 hη le_rfl hs (five_le_of_mem_compl_nearSet q.2)
    have hsn : Summable fun q : ↑(nearSet γ₀)ᶜ => ‖landauTerm_primeLagLandauContinuation q (ρ₀ - 1 / 2 + t)‖ :=
      Summable.of_nonneg_of_le (fun q => norm_nonneg _) hle (hmaj.subtype _)
    calc ‖∑' q : ↑(nearSet γ₀)ᶜ, landauTerm_primeLagLandauContinuation q (ρ₀ - 1 / 2 + t)‖
        ≤ ∑' q : ↑(nearSet γ₀)ᶜ, ‖landauTerm_primeLagLandauContinuation q (ρ₀ - 1 / 2 + t)‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' q : ↑(nearSet γ₀)ᶜ, ‖lagWeight q‖
            * (5 * logDerivZetaConstant * Real.log (2 + |zeroOrdinate q - γ₀|)) :=
          hsn.tsum_le_tsum hle (hmaj.subtype _)
      _ ≤ B₄ := Summable.tsum_subtype_le _ _ hmaj0 hmaj
  -- the residue term
  have hres : ‖aliasedWeight q₀‖ / t - ‖aliasedWeight q₀‖ * B₁
      ≤ ‖aliasedWeight q₀ * (-logDeriv riemannZeta (1 + t))‖ := by
    rw [norm_mul]
    have h1 := hB₁ t ht ht4
    have h2 := norm_sub_norm_le (1 / (t : ℂ)) (-logDeriv riemannZeta (1 + t))
    have h3 : ‖(1 : ℂ) / (t : ℂ)‖ = 1 / t := by
      rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    rw [norm_sub_rev, h3] at h2
    have hW := norm_nonneg (aliasedWeight q₀)
    have h4 := le_trans h2 h1
    have : 1 / t - B₁ ≤ ‖-logDeriv riemannZeta (1 + t)‖ := by linarith
    calc ‖aliasedWeight q₀‖ / t - ‖aliasedWeight q₀‖ * B₁
        = ‖aliasedWeight q₀‖ * (1 / t - B₁) := by ring
      _ ≤ ‖aliasedWeight q₀‖ * ‖-logDeriv riemannZeta (1 + t)‖ := by gcongr
  -- the bounded parts
  have hMt := hB₂ t ⟨ht.le, ht4⟩
  have hN't := hB₃ t ⟨ht.le, ht4⟩
  -- assemble
  set A := (M : ℂ) * (-logDeriv riemannZeta (1 + (ρ₀ - 1 / 2 + t))) with hA
  set Al := aliasedWeight q₀ * (-logDeriv riemannZeta (1 + t)) with hAl
  set Nt := ∑ q ∈ N.filter (fun q => ¬ (q.1 : ℂ) = ρ₀), landauTerm_primeLagLandauContinuation q (ρ₀ - 1 / 2 + t) with hNt
  set Fa := ∑' q : ↑(nearSet γ₀)ᶜ, landauTerm_primeLagLandauContinuation q (ρ₀ - 1 / 2 + t) with hFa
  have hNt' : ‖Nt‖ ≤ B₃ := hN't
  have key : ‖Al‖ ≤ ‖A‖ + ‖A - (Al + Nt + Fa)‖ + ‖Nt‖ + ‖Fa‖ := by
    have e : Al = A - (A - (Al + Nt + Fa)) - Nt - Fa := by ring
    calc ‖Al‖ = ‖A - (A - (Al + Nt + Fa)) - Nt - Fa‖ := by rw [← e]
      _ ≤ ‖A - (A - (Al + Nt + Fa))‖ + ‖Nt‖ + ‖Fa‖ := by
          have h1 := norm_sub_le (A - (A - (Al + Nt + Fa)) - Nt) Fa
          have h2 := norm_sub_le (A - (A - (Al + Nt + Fa))) Nt
          linarith
      _ ≤ ‖A‖ + ‖A - (Al + Nt + Fa)‖ + ‖Nt‖ + ‖Fa‖ := by
          linarith [norm_sub_le A (A - (Al + Nt + Fa))]
  linarith

/-! ## The ray box -/

/-- A positive lower bound on `|γ_q − γ₀|` over the near copies with `γ_q ≠ γ₀`. -/
theorem exists_pos_le_ordinate_gap (γ₀ : ℝ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ∀ q ∈ nearSet γ₀, zeroOrdinate q ≠ γ₀ → r ≤ |zeroOrdinate q - γ₀| := by
  classical
  set F := (finite_nearSet γ₀).toFinset.filter (fun q => zeroOrdinate q ≠ γ₀) with hF
  rcases F.eq_empty_or_nonempty with h | hne
  · refine ⟨1, one_pos, le_rfl, fun q hq hne => ?_⟩
    have : q ∈ F := by
      rw [hF, Finset.mem_filter, Set.Finite.mem_toFinset]; exact ⟨hq, hne⟩
    rw [h] at this
    exact absurd this (Finset.notMem_empty q)
  · obtain ⟨q₁, hq₁, hmin⟩ := F.exists_min_image (fun q => |zeroOrdinate q - γ₀|) hne
    have hq₁' : zeroOrdinate q₁ ≠ γ₀ := by rw [hF, Finset.mem_filter] at hq₁; exact hq₁.2
    have hpos : 0 < |zeroOrdinate q₁ - γ₀| := abs_pos.mpr (sub_ne_zero.mpr hq₁')
    refine ⟨min 1 |zeroOrdinate q₁ - γ₀|, lt_min one_pos hpos, min_le_left _ _,
      fun q hq hne => ?_⟩
    exact (min_le_right _ _).trans (hmin q (by
      rw [hF, Finset.mem_filter, Set.Finite.mem_toFinset]; exact ⟨hq, hne⟩))

/-! ## The criterion -/

/-- **Bounded prime-power lags force the Riemann hypothesis.**  If `a_n ≤ M` for every prime
power `n`, then every nontrivial zero lies on the critical line. -/
theorem riemannHypothesis_of_primePowerLag_le {M : ℝ}
    (hM : ∀ n : ℕ, vonMangoldt n ≠ 0 → integerLag n ≤ M) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨η, hηpos, hη20, hηΘ, -, hsumσ⟩ := landau_transfer_step hM hRH
  obtain ⟨q₁', hq₁'⟩ := exists_xiZeroCopy_re_gt_half_of_not_rh hRH
  haveI : Nonempty XiZeroCopy := ⟨q₁'⟩
  set Θ := zeroReSup with hΘ
  have hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ Θ := re_le_zeroReSup
  have hΘ12 : 1 / 2 < Θ := lt_of_lt_of_le hq₁' (re_le_zeroReSup q₁')
  have hΘ34 : Θ ≤ 3 / 4 :=
    zeroReSup_le (re_le_three_quarters_of_primeLag_le (primeLag_le_of_primePowerLag_le hM))
  set c : ℕ → ℂ := fun n => (primeLagCoeff M n : ℂ) with hc
  set σ : ℝ := Θ - 1 / 2 - η / 4 with hσ
  -- the Dirichlet series is analytic on `Re s > σ`
  have habs : LSeries.abscissaOfAbsConv c ≤ (σ : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      hsumσ.of_re_le_re (by simp; linarith)
  have hFd : ∀ z : ℂ, σ < z.re → DifferentiableAt ℂ (LSeries c) z := fun z hz =>
    (LSeries_analyticOnNhd c z
      (lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr hz))).differentiableAt
  -- a copy near the top
  obtain ⟨q₁, hq₁⟩ := exists_re_gt_of_lt_zeroReSup (b := Θ - η / 8) (by linarith)
  -- a zero of maximal real part on the horizontal segment through `ρ₁`
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
  have hre₀ : Θ - η / 8 < ρ₀.re := lt_of_lt_of_le hq₁ hρ₀K.1.1
  have hre₀' : ρ₀.re < 1 := by have := xiZeroCopy_re_lt_one q₀; rwa [hq₀] at this
  have him₀ : ρ₀.im = ρ₁.im := le_antisymm hρ₀K.2.2 hρ₀K.2.1
  have hmaxq : ∀ q : XiZeroCopy, zeroOrdinate q = zeroOrdinate q₀ →
      (q.1 : ℂ).re ≤ (q₀.1 : ℂ).re := by
    intro q hq
    rw [hq₀]
    by_contra hlt
    push Not at hlt
    have hmemK : (q.1 : ℂ) ∈ xiZeroSet_weilLagFunctionCriterion ∩ K := by
      refine ⟨xi_xiZeroCopy_eq_zero q, ?_⟩
      rw [hK, Complex.mem_reProdIm]
      refine ⟨⟨by linarith [hρ₀K.1.1], (xiZeroCopy_re_lt_one q).le⟩, ?_⟩
      have : (q.1 : ℂ).im = ρ₁.im := by
        unfold zeroOrdinate at hq; rw [hq, hq₀, him₀]
      rw [this]; exact ⟨le_rfl, le_rfl⟩
    have := hmax _ hmemK hlt.le
    linarith
  -- the pole bound along the ray
  have hβ₀ : Θ - η < (q₀.1 : ℂ).re := by rw [hq₀]; linarith
  have hβ₀' : 1 / 2 < (q₀.1 : ℂ).re := by rw [hq₀]; linarith
  obtain ⟨C, hC⟩ := landauG_ray_lower_bound (M := M) hθ hΘ34 hη20 hηpos q₀ hβ₀ hβ₀' hmaxq
  -- the ray box, avoiding every near pole
  set γ₀ : ℝ := zeroOrdinate q₀ with hγ₀
  have hγ₀im : ρ₀.im = γ₀ := by rw [hγ₀]; unfold zeroOrdinate; rw [hq₀]
  obtain ⟨r, hrpos, hr1, hrgap⟩ := exists_pos_le_ordinate_gap γ₀
  set U₀ : Set ℂ := landauBox ρ₀.re 0 γ₀ r with hU₀
  have hU₀open : IsOpen U₀ := isOpen_landauBox _ _ _ _
  have hGd : DifferentiableOn ℂ (landauG M) U₀ := by
    refine differentiableOn_landauG (θ := Θ) (η := η) (t₀ := γ₀) (r := r) hθ hΘ34 hη20 hr1
      (U := U₀) ?_ ?_ ?_
    · intro s hs
      exact ⟨by linarith [hs.1], hs.2.1, hs.2.2⟩
    · intro s hs
      linarith [hs.1]
    · intro q hq s hs h1
      have him : s.im = zeroOrdinate q := by
        have := congrArg Complex.im h1
        simp at this
        unfold zeroOrdinate
        linarith
      have hre : s.re = (q.1 : ℂ).re - 1 / 2 := by
        have := congrArg Complex.re h1
        simp at this
        linarith
      by_cases hord : zeroOrdinate q = γ₀
      · have := hmaxq q hord
        rw [hq₀] at this
        have hs1 := hs.1
        linarith
      · have hgap := hrgap q hq hord
        have hs3 := hs.2.2
        rw [him] at hs3
        linarith
  -- the ray
  set p₀ : ℂ := ρ₀ - 1 / 2 with hp₀
  set ℓ : ℝ → ℂ := fun t => p₀ + t with hℓ
  have hℓan : ∀ t : ℝ, AnalyticAt ℝ ℓ t := fun t =>
    analyticAt_const.add (Complex.ofRealCLM.analyticAt t)
  have hℓeq : ∀ t : ℝ, ℓ t = (q₀.1 : ℂ) - 1 / 2 + t := fun t => by rw [hℓ, hp₀, hq₀]
  have hℓre : ∀ t : ℝ, (ℓ t).re = ρ₀.re - 1 / 2 + t := fun t => by rw [hℓ, hp₀]; simp
  have hℓim : ∀ t : ℝ, (ℓ t).im = γ₀ := fun t => by rw [hℓ, hp₀]; simp [hγ₀im]
  set U : Set ℝ := Ioo (0 : ℝ) (1 / 4) with hU
  have hℓU₀ : ∀ t ∈ U, ℓ t ∈ U₀ := by
    intro t ht
    refine ⟨?_, ?_, ?_⟩
    · rw [hℓre]; linarith [ht.1]
    · rw [hℓre]; linarith [ht.2]
    · rw [hℓim, sub_self, abs_zero]; exact hrpos
  set V : Set ℂ := {z : ℂ | σ < z.re} with hV
  have hVopen : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hFdiff : DifferentiableOn ℂ (LSeries c) V := fun z hz => (hFd z hz).differentiableWithinAt
  have hℓV : ∀ t ∈ U, ℓ t ∈ V := by
    intro t ht
    show σ < (ℓ t).re
    rw [hℓre]; linarith [ht.1]
  have hF : AnalyticOnNhd ℝ (fun t : ℝ => LSeries c (ℓ t)) U := fun t ht =>
    ((hFdiff.analyticAt (hVopen.mem_nhds (hℓV t ht))).restrictScalars).comp (hℓan t)
  have hG : AnalyticOnNhd ℝ (fun t : ℝ => landauG M (ℓ t)) U := fun t ht =>
    ((hGd.analyticAt (hU₀open.mem_nhds (hℓU₀ t ht))).restrictScalars).comp (hℓan t)
  have hUconn : IsPreconnected U := isPreconnected_Ioo
  have h18U : (1 / 8 : ℝ) ∈ U := ⟨by norm_num, by norm_num⟩
  have hagree : ∀ s : ℂ, Θ - 1 / 2 < s.re → LSeries c s = landauG M s := by
    intro s hs
    rw [hc, LSeries_lagCoeff_eq hθ hΘ12.le hs]
    rfl
  have hfg : (fun t : ℝ => LSeries c (ℓ t)) =ᶠ[𝓝 (1 / 8 : ℝ)]
      (fun t : ℝ => landauG M (ℓ t)) := by
    refine Filter.eventuallyEq_of_mem
      (Ioo_mem_nhds (by linarith : η / 8 < 1 / 8) (by norm_num : (1 / 8 : ℝ) < 1 / 4))
      fun t ht => ?_
    apply hagree
    rw [hℓre]
    linarith [ht.1]
  have heq := hF.eqOn_of_preconnected_of_eventuallyEq hG hUconn h18U hfg
  -- continuity of the series at `p₀`
  have hp₀σ : σ < p₀.re := by rw [hp₀]; simp; linarith
  have hFcont : ContinuousAt (LSeries c) p₀ := (hFd p₀ hp₀σ).continuousAt
  have hℓ0 : Tendsto ℓ (𝓝 0) (𝓝 p₀) := by
    have : Tendsto (fun t : ℝ => p₀ + (t : ℂ)) (𝓝 0) (𝓝 (p₀ + ((0 : ℝ) : ℂ))) :=
      tendsto_const_nhds.add (Complex.continuous_ofReal.tendsto 0)
    simpa using this
  have hcomp : Tendsto (fun t : ℝ => LSeries c (ℓ t)) (𝓝 0) (𝓝 (LSeries c p₀)) :=
    hFcont.tendsto.comp hℓ0
  obtain ⟨δ, hδ, hδF⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp hcomp 1 one_pos)
  set C' : ℝ := max C 0 with hC'
  have hC0 : 0 ≤ C' := le_max_right _ _
  set B : ℝ := ‖LSeries c p₀‖ + 1 with hB
  have hw : 0 < ‖aliasedWeight q₀‖ := norm_aliasedWeight_pos q₀
  have hBpos : 0 < B + C' + 1 := by positivity
  have hw' : 0 < ‖aliasedWeight q₀‖ / (B + C' + 1) := div_pos hw hBpos
  set m : ℝ := min (min δ (1 / 4)) (‖aliasedWeight q₀‖ / (B + C' + 1)) with hm
  have hmpos : 0 < m := lt_min (lt_min hδ (by norm_num)) hw'
  set t₀ : ℝ := m / 2 with ht₀
  have ht₀pos : 0 < t₀ := half_pos hmpos
  have hmδ : m ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hm4 : m ≤ 1 / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hmw : m ≤ ‖aliasedWeight q₀‖ / (B + C' + 1) := min_le_right _ _
  have ht₀δ : t₀ < δ := by rw [ht₀]; linarith
  have ht₀4 : t₀ ≤ 1 / 4 := by rw [ht₀]; linarith
  have ht₀U : t₀ ∈ U := ⟨ht₀pos, by rw [ht₀]; linarith⟩
  have hFb : ‖LSeries c (ℓ t₀)‖ ≤ B := by
    have hd : dist t₀ 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht₀pos]; exact ht₀δ
    have := hδF hd
    rw [dist_eq_norm] at this
    calc ‖LSeries c (ℓ t₀)‖
        = ‖(LSeries c (ℓ t₀) - LSeries c p₀) + LSeries c p₀‖ := by congr 1; ring
      _ ≤ ‖LSeries c (ℓ t₀) - LSeries c p₀‖ + ‖LSeries c p₀‖ := norm_add_le _ _
      _ ≤ 1 + ‖LSeries c p₀‖ := by linarith
      _ = B := by rw [hB]; ring
  have hGb : B < ‖landauG M (ℓ t₀)‖ := by
    have h1 := hC t₀ ht₀pos ht₀4
    rw [← hℓeq] at h1
    have h2 : 2 * (B + C' + 1) ≤ ‖aliasedWeight q₀‖ / t₀ := by
      rw [le_div_iff₀ ht₀pos]
      calc 2 * (B + C' + 1) * t₀
          ≤ 2 * (B + C' + 1) * (‖aliasedWeight q₀‖ / (B + C' + 1) / 2) := by
            gcongr
            rw [ht₀]; linarith
        _ = ‖aliasedWeight q₀‖ := by field_simp
    have h3 : C ≤ C' := le_max_left _ _
    linarith
  have hEq : LSeries c (ℓ t₀) = landauG M (ℓ t₀) := heq ht₀U
  rw [hEq] at hFb
  linarith

/-- **RH ⟺ the lag sequence is bounded above on the prime powers.** -/
theorem riemannHypothesis_iff_primePowerLag_bddAbove :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ n : ℕ, vonMangoldt n ≠ 0 → integerLag n ≤ M := by
  constructor
  · intro h
    exact ⟨poleSharpConstant, fun n _ =>
      (abs_le.mp (abs_integerLag_le_of_riemannHypothesis h n)).2⟩
  · rintro ⟨M, hM⟩
    exact riemannHypothesis_of_primePowerLag_le hM

end

end RHTower
