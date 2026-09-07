import GaloisForLFunctions.RHTower.PowerLagLandauContinuation

/-!
# The `k`-th power lag criterion for the Riemann hypothesis

For every `k ≥ 1`: if the lag values `a_{m^k} = Φ(k log m)` are bounded above, the Riemann
hypothesis holds.  Under `¬RH` let `Θ` be the supremum of the real parts of the zeros.  The
nonnegative Dirichlet series `Σ_m (M − a_{m^k}) m^{−k−u}` converges for `Re u > k(Θ − 3/2) + 1` and
equals `M ζ(k + u) − Σ_ρ w_ρ ζ(u + 3k/2 − kρ)`, which is analytic on a box around the real point
`k(Θ − 3/2) + 1 + 2η` (all poles `kρ − 3k/2 + 1` have imaginary part `kγ ≠ 0`); Landau's theorem
forces convergence to the left of the abscissa, so the series is analytic on a half-plane containing
the pole `kρ₀ − 3k/2 + 1` of a zero of maximal real part on its horizontal line, which is
impossible.  No prime-gap input is needed: the counting function `ζ(kw)` of the `k`-th powers has a
single real pole.
-/

open Complex Filter Topology Set Metric

namespace RHTower

noncomputable section

/-! ## Auxiliary bounds -/

/-- A positive lower bound for `|γ|` over all copies. -/
theorem exists_pos_le_abs_ordinate_all :
    ∃ g : ℝ, 0 < g ∧ ∀ q : XiZeroCopy, g ≤ |zeroOrdinate q| := by
  obtain ⟨γ₁, hγ₁, h⟩ := exists_pos_le_abs_ordinate
  refine ⟨min γ₁ 6, lt_min hγ₁ (by norm_num), fun q => ?_⟩
  rcases le_or_gt |zeroOrdinate q| 6 with h6 | h6
  · exact (min_le_left _ _).trans (h q h6)
  · exact (min_le_right _ _).trans h6.le

/-- The residue of `ζ` at `1`: `‖ζ(1 + t)‖ ≥ 1/(2t)` for small `t > 0`. -/
theorem exists_norm_riemannZeta_ge_inv :
    ∃ t₁ : ℝ, 0 < t₁ ∧ ∀ t : ℝ, 0 < t → t < t₁ → 1 / (2 * t) ≤ ‖riemannZeta (1 + t)‖ := by
  have h := Metric.tendsto_nhdsWithin_nhds.mp riemannZeta_residue_one (1 / 2) (by norm_num)
  obtain ⟨δ, hδ, hδ'⟩ := h
  refine ⟨δ, hδ, fun t ht htδ => ?_⟩
  have hmem : (1 : ℂ) + t ∈ ({1}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h1
    have := congrArg Complex.re h1
    simp at this
    linarith
  have hdist : dist ((1 : ℂ) + t) 1 < δ := by
    rw [Complex.dist_eq, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    exact htδ
  have hlt := hδ' hmem hdist
  rw [Complex.dist_eq, add_sub_cancel_left] at hlt
  -- `‖t ζ(1+t)‖ ≥ 1/2`
  have h1 : (1 : ℝ) - ‖(t : ℂ) * riemannZeta (1 + t)‖ ≤ ‖(t : ℂ) * riemannZeta (1 + t) - 1‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((t : ℂ) * riemannZeta (1 + t))
    rw [norm_one, norm_sub_rev] at this
    exact this
  have h2 : 1 / 2 ≤ ‖(t : ℂ) * riemannZeta (1 + t)‖ := by linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] at h2
  rw [div_le_iff₀ (by positivity)]
  linarith

/-! ## The Landau transfer step -/

/-- **Landau transfer for the `k`-th powers.** -/
theorem powLandau_transfer_step {k : ℕ} (hk : 1 ≤ k) {M : ℝ}
    (hM : ∀ m : ℕ, 1 ≤ m → integerLag (m ^ k) ≤ M) (hRH : ¬ RiemannHypothesis) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ η < k * (zeroReSup - 1 / 2) ∧
      LSeriesSummable (fun m => (powLagCoeff k M m : ℂ))
        ((powAbscissa k zeroReSup - η / 4 : ℝ) : ℂ) := by
  obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_re_gt_half_of_not_rh hRH
  haveI : Nonempty XiZeroCopy := ⟨q₁⟩
  set Θ := zeroReSup with hΘ
  have hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ Θ := re_le_zeroReSup
  have hΘ12 : 1 / 2 < Θ := lt_of_lt_of_le hq₁ (re_le_zeroReSup q₁)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨g, hg, hgall⟩ := exists_pos_le_abs_ordinate_all
  set u₀ : ℝ := powAbscissa k Θ with hu₀
  set η : ℝ := min (1 / 4) (min (k * (Θ - 1 / 2) / 2) (k * g / 6)) with hη
  have hηpos : 0 < η := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hη4 : η ≤ 1 / 4 := min_le_left _ _
  have hηΘ : η ≤ k * (Θ - 1 / 2) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηg : η ≤ k * g / 6 := (min_le_right _ _).trans (min_le_right _ _)
  have hηΘ' : η < k * (Θ - 1 / 2) := by
    have : 0 < k * (Θ - 1 / 2) := by positivity
    linarith
  refine ⟨η, hηpos, hη4, hηΘ', ?_⟩
  -- the series converges at `σ₁ = u₀ + η`
  have hsum : LSeriesSummable (fun m => (powLagCoeff k M m : ℂ)) ((u₀ + η : ℝ) : ℂ) :=
    powLagCoeff_LSeriesSummable hθ hΘ12.le k (by simp; linarith)
  -- the continuation is differentiable on the closed ball of radius `5η/2` around `u₀ + 2η`
  set R : NNReal := ⟨5 * η / 2, by positivity⟩ with hR
  have hRval : (R : ℝ) = 5 * η / 2 := rfl
  set U : Set ℂ := powBox (u₀ - η) (u₀ + 5 * η) 0 (3 * η) with hU
  have hball : closedBall (((u₀ + η) + η : ℝ) : ℂ) (R : ℝ) ⊆ U := by
    intro s hs
    rw [mem_closedBall, Complex.dist_eq] at hs
    have hre := Complex.abs_re_le_norm (s - (((u₀ + η) + η : ℝ) : ℂ))
    have him := Complex.abs_im_le_norm (s - (((u₀ + η) + η : ℝ) : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at hre
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at him
    rw [hRval] at hs
    have h1 := (abs_le.mp (hre.trans hs)).1
    have h2 := (abs_le.mp (hre.trans hs)).2
    refine ⟨by linarith, by linarith, ?_⟩
    rw [sub_zero]
    linarith [him.trans hs]
  have hGd : DifferentiableOn ℂ (powLandauG k M) (closedBall (((u₀ + η) + η : ℝ) : ℂ) (R : ℝ)) := by
    refine (differentiableOn_powLandauG (θ := Θ) (η := η) hθ (by linarith) hk (M := M) (t₀ := 0)
      (g := g) (B := |u₀| + 3) hg (fun q _ => by rw [sub_zero]; exact hgall q)
      (U := U) (isOpen_powBox _ _ _ _) ?_ ?_ ?_ ?_ ?_).mono hball
    · intro u hu; exact hu.1.le
    · intro u hu
      have := hu.2.2
      rw [sub_zero] at this
      rw [mul_zero, sub_zero]
      linarith
    · intro u hu
      have h1 := hu.1
      have h2 := hu.2.1
      have h3 := hu.2.2
      rw [sub_zero] at h3
      have := Complex.norm_le_abs_re_add_abs_im u
      have hre : |u.re| ≤ |u₀| + 2 := by
        rw [abs_le] at *
        constructor <;> linarith [(abs_le.mp (le_refl |u₀|)).1, le_abs_self u₀, neg_abs_le u₀]
      linarith
    · intro u hu h1
      have := congrArg Complex.re h1
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re] at this
      have hu1 := hu.1
      rw [hu₀] at hu1
      unfold powAbscissa at hu1
      nlinarith
    · intro q hq
      exfalso
      exact zeroOrdinate_ne_zero' q hq
  have hagree : ∀ s : ℂ, u₀ + η < s.re →
      powLandauG k M s = LSeries (fun m => (powLagCoeff k M m : ℂ)) s := by
    intro s hs
    exact (LSeries_powLagCoeff_eq_powLandauG hθ hΘ12.le k (by linarith)).symm
  exact landau_local_summability_transfer (a := powLagCoeff k M) (powLagCoeff_nonneg hk hM)
    (σ₁ := u₀ + η) (h := η) hηpos hsum (R := R) (G := powLandauG k M) hGd hagree
    (σ := u₀ - η / 4) (by rw [hRval]; linarith)

/-! ## The pole of the continuation at a maximal zero -/

/-- A positive lower bound on `|γ_q − γ₀|` over all copies with `γ_q ≠ γ₀`. -/
theorem exists_pos_le_ordinate_gap_all (γ₀ : ℝ) :
    ∃ g : ℝ, 0 < g ∧ g ≤ 1 ∧ ∀ q : XiZeroCopy, zeroOrdinate q ≠ γ₀ → g ≤ |zeroOrdinate q - γ₀| := by
  obtain ⟨r, hr, hr1, hgap⟩ := exists_pos_le_ordinate_gap γ₀
  refine ⟨r, hr, hr1, fun q hq => ?_⟩
  by_cases hn : q ∈ nearSet γ₀
  · exact hgap q hn hq
  · have := five_le_of_mem_compl_nearSet hn
    linarith

/-- The pole `k(ρ₀ − 3/2) + 1` of the continuation. -/
def powPole (k : ℕ) (q₀ : XiZeroCopy) : ℂ := (k : ℂ) * ((q₀.1 : ℂ) - 3 / 2) + 1

theorem powPole_re (k : ℕ) (q₀ : XiZeroCopy) :
    (powPole k q₀).re = k * ((q₀.1 : ℂ).re - 3 / 2) + 1 := by
  unfold powPole; simp

theorem powPole_im (k : ℕ) (q₀ : XiZeroCopy) : (powPole k q₀).im = k * zeroOrdinate q₀ := by
  unfold powPole zeroOrdinate; simp

theorem powShift_powPole_add (k : ℕ) (q q₀ : XiZeroCopy) (t : ℂ) :
    powShift k q (powPole k q₀ + t) = 1 + t + k * ((q₀.1 : ℂ) - (q.1 : ℂ)) := by
  unfold powShift powPole; ring

/-- The aliased weight: the sum of the weights of the copies over the support point of `q₀`. -/
def powAliasedWeight (q₀ : XiZeroCopy) : ℂ :=
  ∑ q ∈ (finite_sameOrdinate (zeroOrdinate q₀)).toFinset.filter
    (fun q => (q.1 : ℂ) = (q₀.1 : ℂ)), lagWeight q

theorem powAliasedWeight_re_pos (q₀ : XiZeroCopy) : 0 < (powAliasedWeight q₀).re := by
  classical
  unfold powAliasedWeight
  rw [Complex.re_sum]
  have hmem : q₀ ∈ (finite_sameOrdinate (zeroOrdinate q₀)).toFinset.filter
      (fun q => (q.1 : ℂ) = (q₀.1 : ℂ)) := by
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨rfl, rfl⟩
  calc (0 : ℝ) < (lagWeight q₀).re := lagWeight_re_pos q₀
    _ ≤ _ := Finset.single_le_sum (fun q _ => (lagWeight_re_pos q).le) hmem

theorem norm_powAliasedWeight_pos (q₀ : XiZeroCopy) : 0 < ‖powAliasedWeight q₀‖ :=
  lt_of_lt_of_le (lt_of_lt_of_le (powAliasedWeight_re_pos q₀) (le_abs_self _))
    (Complex.abs_re_le_norm _)

/-- **The pole of the continuation at a maximal zero.**  Along the ray `powPole + t` the
continuation is at least `‖W₀‖/(2t) − C` for small `t > 0`. -/
theorem powLandauG_ray_lower_bound {θ η : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hη : η ≤ 1 / 2) {k : ℕ} (hk : 1 ≤ k) {M : ℝ} (q₀ : XiZeroCopy)
    (hβ₀ : k * (θ - (q₀.1 : ℂ).re) ≤ η) (hβ₀' : 1 / 2 < (q₀.1 : ℂ).re)
    (hmax : ∀ q : XiZeroCopy, zeroOrdinate q = zeroOrdinate q₀ → (q.1 : ℂ).re ≤ (q₀.1 : ℂ).re) :
    ∃ t₁ : ℝ, 0 < t₁ ∧ ∃ C : ℝ, ∀ t : ℝ, 0 < t → t < t₁ →
      ‖powAliasedWeight q₀‖ / (2 * t) - C ≤ ‖powLandauG k M (powPole k q₀ + t)‖ := by
  classical
  set ρ₀ : ℂ := (q₀.1 : ℂ) with hρ₀
  set γ₀ : ℝ := zeroOrdinate q₀ with hγ₀
  set u₁ : ℂ := powPole k q₀ with hu₁
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hu₁re : u₁.re = k * (ρ₀.re - 3 / 2) + 1 := powPole_re k q₀
  have hu₁im : u₁.im = k * γ₀ := powPole_im k q₀
  set N := (finite_sameOrdinate γ₀).toFinset with hN
  set N' := N.filter (fun q => ¬ (q.1 : ℂ) = ρ₀) with hN'
  obtain ⟨t₁, ht₁, hres⟩ := exists_norm_riemannZeta_ge_inv
  obtain ⟨g, hg, hg1, hgap⟩ := exists_pos_le_ordinate_gap_all γ₀
  set B : ℝ := ‖u₁‖ + 1 with hB
  -- the `M` term on the closed segment
  have hMc : ContinuousOn (fun t : ℝ => (M : ℂ) * riemannZeta ((k : ℂ) + (u₁ + t)))
      (Icc (0 : ℝ) (1 / 4)) := by
    intro t ht
    have hre : ((k : ℂ) + (u₁ + (t : ℂ))).re = 1 + k * (ρ₀.re - 1 / 2) + t := by
      simp [hu₁re]; ring
    have h1 : (k : ℂ) + (u₁ + t) ≠ 1 := by
      intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this
      have : 0 < k * (ρ₀.re - 1 / 2) := by positivity
      linarith [ht.1]
    have hd := (differentiableAt_riemannZeta h1).continuousAt
    have hc : ContinuousAt (fun t : ℝ => (k : ℂ) + (u₁ + t)) t :=
      (continuous_const.add (continuous_const.add Complex.continuous_ofReal)).continuousAt
    have hcomp := ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (k : ℂ) + (u₁ + t)) hd hc
    exact (continuousAt_const.mul hcomp).continuousWithinAt
  obtain ⟨B₂, hB₂⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 4)).exists_bound_of_continuousOn hMc
  -- the non-aliased same-ordinate terms on the closed segment
  have hN'c : ContinuousOn (fun t : ℝ => ∑ q ∈ N', powTerm k q (u₁ + t)) (Icc (0 : ℝ) (1 / 4)) := by
    apply continuousOn_finsetSum
    intro q hq t ht
    rw [hN', Finset.mem_filter] at hq
    have hqne : (q.1 : ℂ) ≠ ρ₀ := hq.2
    have hqord : zeroOrdinate q = γ₀ := by
      have := hq.1; rw [hN, Set.Finite.mem_toFinset] at this; exact this
    have hle := hmax q hqord
    have hw1 : powShift k q (u₁ + t) ≠ 1 := by
      rw [hu₁, powShift_powPole_add]
      intro h1
      have hre := congrArg Complex.re h1
      simp at hre
      have ht0 : t = 0 := by nlinarith [ht.1]
      apply hqne
      apply Complex.ext
      · nlinarith
      · unfold zeroOrdinate at hqord; rw [hqord, hγ₀, hρ₀]; rfl
    have hd := (differentiableAt_riemannZeta hw1).continuousAt
    have hc : ContinuousAt (fun t : ℝ => powShift k q (u₁ + t)) t := by
      unfold powShift; fun_prop
    have hcomp := ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => powShift k q (u₁ + t)) hd hc
    exact (continuousAt_const.mul hcomp).continuousWithinAt
  obtain ⟨B₃, hB₃⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 4)).exists_bound_of_continuousOn hN'c
  -- the far tail
  set B₄ : ℝ := ∑' q : XiZeroCopy,
    ‖lagWeight q‖ * (powFarConst k g B * Real.sqrt (2 + |zeroOrdinate q|)) with hB₄
  refine ⟨min t₁ (1 / 4), lt_min ht₁ (by norm_num), B₂ + B₃ + B₄, fun t ht htm => ?_⟩
  have ht1 : t < t₁ := lt_of_lt_of_le htm (min_le_left _ _)
  have ht4 : t < 1 / 4 := lt_of_lt_of_le htm (min_le_right _ _)
  -- the ray point satisfies the far-bound hypotheses
  have hu1 : powAbscissa k θ - η ≤ (u₁ + t).re := by
    simp only [Complex.add_re, Complex.ofReal_re, hu₁re]
    unfold powAbscissa
    nlinarith
  have hu2 : |(u₁ + t).im - k * γ₀| ≤ k * g / 2 := by
    simp only [Complex.add_im, Complex.ofReal_im, add_zero, hu₁im, sub_self, abs_zero]
    positivity
  have hBu : ‖u₁ + t‖ ≤ B := by
    calc ‖u₁ + t‖ ≤ ‖u₁‖ + ‖(t : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖u₁‖ + 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]; linarith
  unfold powLandauG
  rw [tsum_powTerm_split hθ hη hk hg hgap hu1 hu2 hBu]
  rw [← Finset.sum_filter_add_sum_filter_not N (fun q => (q.1 : ℂ) = ρ₀)]
  -- the aliased part is the residue term
  have hal : ∑ q ∈ N.filter (fun q => (q.1 : ℂ) = ρ₀), powTerm k q (u₁ + t)
      = powAliasedWeight q₀ * riemannZeta (1 + t) := by
    unfold powAliasedWeight
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mem_filter] at hq
    unfold powTerm
    rw [hu₁, powShift_powPole_add, hq.2]
    congr 2
    ring
  rw [hal]
  -- the far part
  have hfar : ‖∑' q : ↑(sameOrdinate γ₀)ᶜ, powTerm k q (u₁ + t)‖ ≤ B₄ := by
    have hmaj := summable_powFar_majorant (powFarConst k g B)
    have hB0 : 0 ≤ B := by rw [hB]; positivity
    have hC0 := powFarConst_nonneg hg hk hB0
    have hmaj0 : ∀ q : XiZeroCopy, 0 ≤ ‖lagWeight q‖
        * (powFarConst k g B * Real.sqrt (2 + |zeroOrdinate q|)) := fun q => by positivity
    have hle : ∀ q : ↑(sameOrdinate γ₀)ᶜ, ‖powTerm k q (u₁ + t)‖
        ≤ ‖lagWeight q‖ * (powFarConst k g B * Real.sqrt (2 + |zeroOrdinate q|)) :=
      fun q => norm_powTerm_le_far hθ hη hk hg hu1 hu2 hBu (hgap q.1 q.2)
    have hsn : Summable fun q : ↑(sameOrdinate γ₀)ᶜ => ‖powTerm k q (u₁ + t)‖ :=
      Summable.of_nonneg_of_le (fun q => norm_nonneg _) hle (hmaj.subtype _)
    calc ‖∑' q : ↑(sameOrdinate γ₀)ᶜ, powTerm k q (u₁ + t)‖
        ≤ ∑' q : ↑(sameOrdinate γ₀)ᶜ, ‖powTerm k q (u₁ + t)‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' q : ↑(sameOrdinate γ₀)ᶜ, ‖lagWeight q‖
            * (powFarConst k g B * Real.sqrt (2 + |zeroOrdinate q|)) :=
          hsn.tsum_le_tsum hle (hmaj.subtype _)
      _ ≤ B₄ := Summable.tsum_subtype_le _ _ hmaj0 hmaj
  -- the residue term
  have hresid : ‖powAliasedWeight q₀‖ / (2 * t) ≤ ‖powAliasedWeight q₀ * riemannZeta (1 + t)‖ := by
    rw [norm_mul, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (hres t ht ht1) (norm_nonneg _)
  -- the bounded parts
  have hMt := hB₂ t ⟨ht.le, ht4.le⟩
  have hN't := hB₃ t ⟨ht.le, ht4.le⟩
  -- assemble
  set A := (M : ℂ) * riemannZeta ((k : ℂ) + (u₁ + t)) with hA
  set Al := powAliasedWeight q₀ * riemannZeta (1 + t) with hAl
  set Nt := ∑ q ∈ N.filter (fun q => ¬ (q.1 : ℂ) = ρ₀), powTerm k q (u₁ + t) with hNt
  set Fa := ∑' q : ↑(sameOrdinate γ₀)ᶜ, powTerm k q (u₁ + t) with hFa
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

/-! ## The criterion -/

/-- A ray parameter small enough for the contradiction. -/
theorem exists_small_ray_parameter {δ t₁ W Bd C' : ℝ} (hδ : 0 < δ) (ht₁ : 0 < t₁) (hW : 0 < W)
    (hB : 0 < Bd + C' + 1) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ t₀ < δ ∧ t₀ < t₁ ∧ t₀ < 1 / 4 ∧ 2 * (Bd + C' + 1) ≤ W / (2 * t₀) := by
  have hw' : 0 < W / (4 * (Bd + C' + 1)) := by positivity
  set m : ℝ := min (min δ (min t₁ (1 / 4))) (W / (4 * (Bd + C' + 1))) with hm
  have hmpos : 0 < m := lt_min (lt_min hδ (lt_min ht₁ (by norm_num))) hw'
  have hmδ : m ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hmt₁ : m ≤ t₁ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hm4 : m ≤ 1 / 4 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmw : m ≤ W / (4 * (Bd + C' + 1)) := min_le_right _ _
  have hmw' : m * (4 * (Bd + C' + 1)) ≤ W := (le_div_iff₀ (by positivity)).mp hmw
  clear_value m
  refine ⟨m / 2, half_pos hmpos, by linarith, by linarith, by linarith, ?_⟩
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- **Bounded `k`-th power lags force the Riemann hypothesis.** -/
theorem riemannHypothesis_of_powLag_le {k : ℕ} (hk : 1 ≤ k) {M : ℝ}
    (hM : ∀ m : ℕ, 1 ≤ m → integerLag (m ^ k) ≤ M) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨η, hηpos, hη4, hηΘ, hsumσ⟩ := powLandau_transfer_step hk hM hRH
  obtain ⟨q₁', hq₁'⟩ := exists_xiZeroCopy_re_gt_half_of_not_rh hRH
  haveI : Nonempty XiZeroCopy := ⟨q₁'⟩
  set Θ := zeroReSup with hΘ
  have hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ Θ := re_le_zeroReSup
  have hΘ12 : 1 / 2 < Θ := lt_of_lt_of_le hq₁' (re_le_zeroReSup q₁')
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set c : ℕ → ℂ := fun m => (powLagCoeff k M m : ℂ) with hc
  set u₀ : ℝ := powAbscissa k Θ with hu₀
  set σ : ℝ := u₀ - η / 4 with hσ
  -- the Dirichlet series is analytic on `Re u > σ`
  have habs : LSeries.abscissaOfAbsConv c ≤ (σ : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      hsumσ.of_re_le_re (by simp; linarith)
  have hFd : ∀ z : ℂ, σ < z.re → DifferentiableAt ℂ (LSeries c) z := fun z hz =>
    (LSeries_analyticOnNhd c z
      (lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr hz))).differentiableAt
  -- a copy near the top
  obtain ⟨q₁, hq₁⟩ := exists_re_gt_of_lt_zeroReSup (b := Θ - η / (8 * k)) (by
    have : 0 < η / (8 * k) := by positivity
    linarith)
  -- a zero of maximal real part on the horizontal segment through `ρ₁`
  set ρ₁ : ℂ := (q₁.1 : ℂ) with hρ₁
  set K : Set ℂ := Set.Icc ρ₁.re 1 ×ℂ Set.Icc ρ₁.im ρ₁.im with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hfin : (xiZeroSet ∩ K).Finite := finite_xiZeroSet_inter hKc
  have hmem₁ : ρ₁ ∈ xiZeroSet ∩ K := by
    refine ⟨xi_xiZeroCopy_eq_zero q₁, ?_⟩
    rw [hK, Complex.mem_reProdIm]
    exact ⟨⟨le_rfl, (xiZeroCopy_re_lt_one q₁).le⟩, ⟨le_rfl, le_rfl⟩⟩
  obtain ⟨ρ₀, hρ₀⟩ := hfin.exists_maximalFor Complex.re _ ⟨ρ₁, hmem₁⟩
  have hρ₀mem : ρ₀ ∈ xiZeroSet ∩ K := hρ₀.1
  have hmax : ∀ z ∈ xiZeroSet ∩ K, ρ₀.re ≤ z.re → z.re ≤ ρ₀.re := fun z hz h => hρ₀.2 hz h
  obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ₀mem.1
  have hρ₀K := hρ₀mem.2
  rw [hK, Complex.mem_reProdIm] at hρ₀K
  have hre₀ : Θ - η / (8 * k) < ρ₀.re := lt_of_lt_of_le hq₁ hρ₀K.1.1
  have hre₀' : ρ₀.re < 1 := by have := xiZeroCopy_re_lt_one q₀; rwa [hq₀] at this
  have him₀ : ρ₀.im = ρ₁.im := le_antisymm hρ₀K.2.2 hρ₀K.2.1
  have hmaxq : ∀ q : XiZeroCopy, zeroOrdinate q = zeroOrdinate q₀ →
      (q.1 : ℂ).re ≤ (q₀.1 : ℂ).re := by
    intro q hq
    rw [hq₀]
    by_contra hlt
    push Not at hlt
    have hmemK : (q.1 : ℂ) ∈ xiZeroSet ∩ K := by
      refine ⟨xi_xiZeroCopy_eq_zero q, ?_⟩
      rw [hK, Complex.mem_reProdIm]
      refine ⟨⟨by linarith [hρ₀K.1.1], (xiZeroCopy_re_lt_one q).le⟩, ?_⟩
      have : (q.1 : ℂ).im = ρ₁.im := by
        unfold zeroOrdinate at hq; rw [hq, hq₀, him₀]
      rw [this]; exact ⟨le_rfl, le_rfl⟩
    have := hmax _ hmemK hlt.le
    linarith
  -- `k(Θ − β₀) < η/8`
  have hkβ : k * (Θ - (q₀.1 : ℂ).re) < η / 8 := by
    rw [hq₀]
    have : k * (Θ - ρ₀.re) < k * (η / (8 * k)) := by
      apply mul_lt_mul_of_pos_left _ hk0; linarith
    have e : (k : ℝ) * (η / (8 * k)) = η / 8 := by field_simp
    linarith
  have hρ₀half : 1 / 2 < ρ₀.re := by
    have hkβ' := hkβ
    rw [hq₀] at hkβ'
    have h1 : k * (Θ - ρ₀.re) < k * ((Θ - 1 / 2) / 8) := by linarith
    have h2 : Θ - ρ₀.re < (Θ - 1 / 2) / 8 := lt_of_mul_lt_mul_left h1 hk0.le
    linarith
  have hβ₀' : 1 / 2 < (q₀.1 : ℂ).re := by rw [hq₀]; exact hρ₀half
  -- the pole bound along the ray
  obtain ⟨t₁, ht₁, C, hC⟩ := powLandauG_ray_lower_bound (M := M) hθ (by linarith) hk q₀
    (by linarith) hβ₀' hmaxq
  -- the ray box, avoiding every same-ordinate pole
  set γ₀ : ℝ := zeroOrdinate q₀ with hγ₀
  have hγ₀im : ρ₀.im = γ₀ := by rw [hγ₀]; unfold zeroOrdinate; rw [hq₀]
  obtain ⟨g, hg, hg1, hgap⟩ := exists_pos_le_ordinate_gap_all γ₀
  set u₁ : ℂ := powPole k q₀ with hu₁
  have hu₁re : u₁.re = k * (ρ₀.re - 3 / 2) + 1 := by rw [hu₁, powPole_re, hq₀]
  have hu₁im : u₁.im = k * γ₀ := powPole_im k q₀
  have hu₁u₀ : u₀ - η / 8 < u₁.re := by
    rw [hu₁re, hu₀]; unfold powAbscissa
    rw [hq₀] at hkβ
    linarith
  have hu₁u₀' : u₁.re ≤ u₀ := by
    rw [hu₁re, hu₀]; unfold powAbscissa
    have := hθ q₀; rw [hq₀] at this
    nlinarith
  set r' : ℝ := k * g / 2 with hr'
  have hr'pos : 0 < r' := by positivity
  set U₀ : Set ℂ := powBox u₁.re (u₀ + 1) (k * γ₀) r' with hU₀
  have hU₀open : IsOpen U₀ := isOpen_powBox _ _ _ _
  have hGd : DifferentiableOn ℂ (powLandauG k M) U₀ := by
    refine differentiableOn_powLandauG (θ := Θ) (η := η) hθ (by linarith) hk (M := M) (t₀ := γ₀)
      (g := g) (B := |u₀| + 2 + k * |γ₀| + r') hg hgap (U := U₀) hU₀open ?_ ?_ ?_ ?_ ?_
    · intro u hu; linarith [hu.1]
    · intro u hu; exact hu.2.2.le
    · intro u hu
      have h1 := hu.1
      have h2 := hu.2.1
      have h3 := hu.2.2
      have := Complex.norm_le_abs_re_add_abs_im u
      have hre : |u.re| ≤ |u₀| + 2 := by
        rw [abs_le]; constructor <;> linarith [le_abs_self u₀, neg_abs_le u₀]
      have him : |u.im| ≤ k * |γ₀| + r' := by
        have := abs_sub_abs_le_abs_sub u.im (k * γ₀)
        rw [abs_mul, abs_of_pos hk0] at this
        linarith
      linarith
    · intro u hu h1
      have := congrArg Complex.re h1
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re] at this
      have hu1 := hu.1
      rw [hu₁re] at hu1
      have : 0 < k * (ρ₀.re - 1 / 2) := mul_pos hk0 (by linarith)
      nlinarith
    · intro q hq u hu h1
      have hqord : zeroOrdinate q = γ₀ := hq
      have hle := hmaxq q hqord
      rw [hq₀] at hle
      have hre := congrArg Complex.re h1
      rw [powShift_re, Complex.one_re] at hre
      have hu1 := hu.1
      rw [hu₁re] at hu1
      nlinarith
  -- the ray
  set ℓ : ℝ → ℂ := fun t => u₁ + t with hℓ
  have hℓan : ∀ t : ℝ, AnalyticAt ℝ ℓ t := fun t =>
    analyticAt_const.add (Complex.ofRealCLM.analyticAt t)
  have hℓre : ∀ t : ℝ, (ℓ t).re = u₁.re + t := fun t => by rw [hℓ]; simp
  have hℓim : ∀ t : ℝ, (ℓ t).im = k * γ₀ := fun t => by rw [hℓ]; simp [hu₁im]
  set U : Set ℝ := Ioo (0 : ℝ) (1 / 4) with hU
  have hℓU₀ : ∀ t ∈ U, ℓ t ∈ U₀ := by
    intro t ht
    refine ⟨?_, ?_, ?_⟩
    · rw [hℓre]; linarith [ht.1]
    · rw [hℓre]; linarith [ht.2]
    · rw [hℓim, sub_self, abs_zero]; exact hr'pos
  set V : Set ℂ := {z : ℂ | σ < z.re} with hV
  have hVopen : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hFdiff : DifferentiableOn ℂ (LSeries c) V := fun z hz => (hFd z hz).differentiableWithinAt
  have hℓV : ∀ t ∈ U, ℓ t ∈ V := by
    intro t ht
    show σ < (ℓ t).re
    rw [hℓre]; linarith [ht.1]
  have hF : AnalyticOnNhd ℝ (fun t : ℝ => LSeries c (ℓ t)) U := fun t ht =>
    ((hFdiff.analyticAt (hVopen.mem_nhds (hℓV t ht))).restrictScalars).comp (hℓan t)
  have hG : AnalyticOnNhd ℝ (fun t : ℝ => powLandauG k M (ℓ t)) U := fun t ht =>
    ((hGd.analyticAt (hU₀open.mem_nhds (hℓU₀ t ht))).restrictScalars).comp (hℓan t)
  have hUconn : IsPreconnected U := isPreconnected_Ioo
  have h18U : (1 / 8 : ℝ) ∈ U := ⟨by norm_num, by norm_num⟩
  have hagree : ∀ s : ℂ, u₀ < s.re → LSeries c s = powLandauG k M s := fun s hs =>
    LSeries_powLagCoeff_eq_powLandauG hθ hΘ12.le k hs
  have hfg : (fun t : ℝ => LSeries c (ℓ t)) =ᶠ[𝓝 (1 / 8 : ℝ)]
      (fun t : ℝ => powLandauG k M (ℓ t)) := by
    refine Filter.eventuallyEq_of_mem
      (Ioo_mem_nhds (by linarith : η / 8 < 1 / 8) (by norm_num : (1 / 8 : ℝ) < 1 / 4))
      fun t ht => ?_
    apply hagree
    rw [hℓre]
    linarith [ht.1]
  have heq := hF.eqOn_of_preconnected_of_eventuallyEq hG hUconn h18U hfg
  -- continuity of the series at `u₁`
  have hu₁σ : σ < u₁.re := by rw [hσ]; linarith
  have hFcont : ContinuousAt (LSeries c) u₁ := (hFd u₁ hu₁σ).continuousAt
  have hℓ0 : Tendsto ℓ (𝓝 0) (𝓝 u₁) := by
    have : Tendsto (fun t : ℝ => u₁ + (t : ℂ)) (𝓝 0) (𝓝 (u₁ + ((0 : ℝ) : ℂ))) :=
      tendsto_const_nhds.add (Complex.continuous_ofReal.tendsto 0)
    rwa [Complex.ofReal_zero, add_zero] at this
  have hcomp : Tendsto (fun t : ℝ => LSeries c (ℓ t)) (𝓝 0) (𝓝 (LSeries c u₁)) :=
    hFcont.tendsto.comp hℓ0
  obtain ⟨δ, hδ, hδF⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp hcomp 1 one_pos)
  obtain ⟨C', hC0, h3⟩ : ∃ C' : ℝ, 0 ≤ C' ∧ C ≤ C' := ⟨max C 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨Bd, hBd⟩ : ∃ Bd : ℝ, Bd = ‖LSeries c u₁‖ + 1 := ⟨_, rfl⟩
  have hw : 0 < ‖powAliasedWeight q₀‖ := norm_powAliasedWeight_pos q₀
  have hBpos : 0 < Bd + C' + 1 := by rw [hBd]; positivity
  obtain ⟨t₀, ht₀pos, ht₀δ, ht₀t₁, ht₀4, h2⟩ := exists_small_ray_parameter hδ ht₁ hw hBpos
  have ht₀U : t₀ ∈ U := ⟨ht₀pos, ht₀4⟩
  have hFb : ‖LSeries c (ℓ t₀)‖ ≤ Bd := by
    have hd : dist t₀ 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht₀pos]; exact ht₀δ
    have := hδF hd
    rw [dist_eq_norm] at this
    calc ‖LSeries c (ℓ t₀)‖
        = ‖(LSeries c (ℓ t₀) - LSeries c u₁) + LSeries c u₁‖ := by congr 1; ring
      _ ≤ ‖LSeries c (ℓ t₀) - LSeries c u₁‖ + ‖LSeries c u₁‖ := norm_add_le _ _
      _ ≤ 1 + ‖LSeries c u₁‖ := by linarith
      _ = Bd := by rw [hBd]; ring
  have hGb : Bd < ‖powLandauG k M (ℓ t₀)‖ := by
    have h1 := hC t₀ ht₀pos ht₀t₁
    have hℓt : ℓ t₀ = powPole k q₀ + t₀ := rfl
    rw [hℓt]
    linarith
  have hEq : LSeries c (ℓ t₀) = powLandauG k M (ℓ t₀) := heq ht₀U
  rw [hEq] at hFb
  linarith

/-- **RH ⟺ the lag sequence is bounded above on the `k`-th powers**, for every `k ≥ 1`. -/
theorem riemannHypothesis_iff_powLag_bddAbove {k : ℕ} (hk : 1 ≤ k) :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ m : ℕ, 1 ≤ m → integerLag (m ^ k) ≤ M := by
  constructor
  · intro h
    exact ⟨poleSharpConstant, fun m _ =>
      (abs_le.mp (abs_integerLag_le_of_riemannHypothesis h (m ^ k))).2⟩
  · rintro ⟨M, hM⟩
    exact riemannHypothesis_of_powLag_le hk hM

/-- **The sharp `k`-th power criterion.** RH holds iff `Φ(k log m) ≤ 2 + γ − log 4π` for every
`m ≥ 1`: the lag on the `k`-th powers never exceeds its value at `m = 1`. -/
theorem riemannHypothesis_iff_powLag_le_sharp {k : ℕ} (hk : 1 ≤ k) :
    RiemannHypothesis ↔ ∀ m : ℕ, 1 ≤ m → integerLag (m ^ k) ≤ poleSharpConstant := by
  constructor
  · intro h m _
    exact (abs_le.mp (abs_integerLag_le_of_riemannHypothesis h (m ^ k))).2
  · intro hM
    exact riemannHypothesis_of_powLag_le hk hM

end

end RHTower
