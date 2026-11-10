import GaloisForLFunctions.InfiniteRankPurityTheory.CesaroMeansOnThickSets
import GaloisForLFunctions.InfiniteRankWeilTheory.TheTowersOfZeta
import GaloisForLFunctions.RHTower.VonMangoldtMinusOneAbscissa
import GaloisForLFunctions.RHTower.WeilLagFunctionCriterion
import GaloisForLFunctions.RHTower.FrobeniusTorsionLaw

/-!
# Elimination needs only an attained top

In finite rank a bound `O(1)` on the power sums puts every eigenvalue in the closed unit disc. For
abstract towers of infinite rank the elimination is known when the tower is finite above every radius
(`InfiniteRankWeilTheory`). For the lag function of `ζ` the corpus has the sharper dichotomy: lags
bounded above along a full progression leave RH or an abscissa that no zero attains
(`RHTower.riemannHypothesis_or_not_attained_of_forall_le`,
`RHTower.exists_lag_progression_gt_of_attainedTop`). This module proves the tower theorem behind that
dichotomy at any rank and on thick sets of levels.

* `not_small_on_thick_of_circle_mode`: a summable tower in the closed unit disc whose weights have
  nonnegative real part, with one mode on the unit circle of positive weight, does not have level
  sums tending to zero along a thick set of levels. The modes inside the disc may accumulate at the
  circle and the circle may carry infinitely many modes: window means read the weight at a point of
  the circle.
* `norm_le_one_of_thick_bounded_levelSums`, `curveDatum_unitary_of_thick_bounded_trace`: bounded level
  sums on a thick set and an attained top put the tower in the closed disc; for a curve this is Weil's
  theorem from traces bounded on a thick set of levels, with a decisive step that does not use the
  rank.
* `lag_bound_iff_of_attainedTop`: for `ζ`, if the abscissa `β₀ = sup Re ρ` is attained, the lag
  `Φ(νℓ)` along the tower of any base `ℓ > 0` is `O(e^{aνℓ})` exactly when `β₀ − ½ ≤ a`.
* `riemannHypothesis_iff_attainedTop_and_thick_lag_bounded`: RH holds iff the abscissa is attained and
  the lag is bounded along a thick set of levels of one tower.

The infinite-rank replacement of "finitely many eigenvalues" in the elimination step is therefore not
well-foundedness of the whole tower but closedness of the set of weights at its top. Towers whose
top is not attained can have vanishing level sums (Wolff towers), so the hypothesis cannot be
dropped.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.InfiniteRankPurityTheory

open _root_.RHTower

open GaloisForLFunctions.InfiniteRankWeilTheory renaming lagWeight → lagW,
  summable_norm_lagWeight → summable_norm_lagW, re_lagWeight_pos → re_lagW_pos

open GaloisForLFunctions.InfiniteRankWeilTheory (Thick thick_univ)

variable {ι : Type*}

/-! ### Summable towers -/

/-- Weights of nonnegative real part cannot cancel at a point where one of them is positive. -/
theorem merged_ne_zero_of_re_pos {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (hre : ∀ i, 0 ≤ (c i).re) {i₀ : ι} (hpos : 0 < (c i₀).re) :
    (∑' i, if z i = z i₀ then c i else 0) ≠ 0 := by
  classical
  intro hm
  have hs : Summable fun i => (if z i = z i₀ then c i else 0 : ℂ) :=
    Summable.of_norm_bounded hc fun i => by split_ifs <;> simp
  have hre' := congrArg Complex.re hm
  rw [Complex.re_tsum hs, Complex.zero_re] at hre'
  have hnonneg : ∀ i, 0 ≤ ((if z i = z i₀ then c i else 0 : ℂ)).re := fun i => by
    split_ifs
    · exact hre i
    · simp
  have hsr : Summable fun i => ((if z i = z i₀ then c i else 0 : ℂ)).re :=
    Complex.reCLM.summable hs
  have hposs := hsr.tsum_pos hnonneg i₀ (by simpa using hpos)
  linarith

/-- **A mode of positive weight on the unit circle is seen on every thick set of levels.** -/
theorem not_small_on_thick_of_circle_mode {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (hz : ∀ i, ‖z i‖ ≤ 1) (hre : ∀ i, 0 ≤ (c i).re) {i₀ : ι} (h1 : ‖z i₀‖ = 1)
    (hpos : 0 < (c i₀).re) {G : Set ℕ} (hG : Thick G) :
    ¬ ∀ δ > 0, ∃ ν₀ : ℕ, ∀ ν ∈ G, ν₀ ≤ ν → ‖towerSum c z ν‖ ≤ δ := fun hsmall =>
  merged_ne_zero_of_re_pos hc hre hpos (merged_eq_zero_of_small_on_runs hc hz hG hsmall h1)

/-- The same on all levels. -/
theorem not_tendsto_towerSum_zero_of_circle_mode {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (hz : ∀ i, ‖z i‖ ≤ 1) (hre : ∀ i, 0 ≤ (c i).re) {i₀ : ι} (h1 : ‖z i₀‖ = 1)
    (hpos : 0 < (c i₀).re) : ¬ Tendsto (towerSum c z) atTop (𝓝 0) := fun h0 =>
  merged_ne_zero_of_re_pos hc hre hpos (merged_eq_zero_of_tendsto_zero hc hz h0 h1)

/-- **Elimination with an attained top.** A summable tower whose weights have nonnegative real
part, whose largest modulus is attained at a mode of positive weight, and whose level sums are
bounded along a thick set of levels, lies in the closed unit disc. Neither the rank nor the number
of modes on any circle is restricted. -/
theorem norm_le_one_of_thick_bounded_levelSums {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (hre : ∀ i, 0 ≤ (c i).re) {i₀ : ι} (hmax : ∀ i, ‖z i‖ ≤ ‖z i₀‖) (hpos : 0 < (c i₀).re)
    {G : Set ℕ} (hG : Thick G) {C : ℝ} (hb : ∀ ν ∈ G, ‖∑' i, c i * z i ^ ν‖ ≤ C) :
    ‖z i₀‖ ≤ 1 := by
  by_contra hlt
  have hR : 1 < ‖z i₀‖ := not_le.mp hlt
  set R : ℝ := ‖z i₀‖ with hRdef
  have hR0 : 0 < R := by linarith
  set y : ι → ℂ := fun i => z i / R with hy
  have hy1 : ∀ i, ‖y i‖ ≤ 1 := by
    intro i
    rw [hy]
    simp only
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
    exact (div_le_one hR0).mpr (hmax i)
  have hyi₀ : ‖y i₀‖ = 1 := by
    rw [hy]
    simp only
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0, div_self hR0.ne']
  have hrel : ∀ ν : ℕ, towerSum c y ν = (∑' i, c i * z i ^ ν) / (R : ℂ) ^ ν := by
    intro ν
    rw [towerSum, ← tsum_div_const]
    refine tsum_congr fun i => ?_
    rw [hy]
    simp only
    rw [div_pow, mul_div_assoc]
  have hinv0 : (0 : ℝ) ≤ R⁻¹ := inv_nonneg.mpr hR0.le
  have hinv1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hgeom : Tendsto (fun ν : ℕ => |C| * R⁻¹ ^ ν) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hinv0 hinv1).const_mul |C|
  refine not_small_on_thick_of_circle_mode hc hy1 hre hyi₀ hpos hG fun δ hδ => ?_
  obtain ⟨ν₀, hν₀⟩ := eventually_atTop.mp (hgeom.eventually (ge_mem_nhds hδ))
  refine ⟨ν₀, fun ν hν hge => ?_⟩
  rw [hrel ν, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0,
    div_eq_mul_inv, ← inv_pow]
  exact (mul_le_mul_of_nonneg_right ((hb ν hν).trans (le_abs_self C))
    (pow_nonneg hinv0 ν)).trans (hν₀ ν hge)

/-- **Weil's theorem for a curve from traces bounded on a thick set of levels.** The decisive
step is `norm_le_one_of_thick_bounded_levelSums`, which does not use the rank. -/
theorem curveDatum_unitary_of_thick_bounded_trace {κ : Type*} [Fintype κ]
    (D : ArithmeticCastelnuovoSeveri.CurveDatum κ) {G : Set ℕ} (hG : Thick G) {C : ℝ}
    (hb : ∀ ν ∈ G, |D.trace ν| ≤ C) : ∀ i, ‖D.β i‖ = 1 := by
  classical
  have hle : ∀ i, ‖D.β i‖ ≤ 1 := by
    intro i
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun j => ‖D.β j‖)
      ⟨i, Finset.mem_univ i⟩
    have hsum : Summable fun _ : κ => ‖(1 : ℂ)‖ := (hasSum_fintype _).summable
    have hb' : ∀ ν ∈ G, ‖∑' j : κ, (1 : ℂ) * D.β j ^ ν‖ ≤ C := by
      intro ν hν
      have hps : (∑' j : κ, (1 : ℂ) * D.β j ^ ν) = D.powerSum ν := by
        rw [tsum_fintype]
        simp [ArithmeticCastelnuovoSeveri.CurveDatum.powerSum]
      have hreal : D.powerSum ν = ((D.trace ν : ℝ) : ℂ) := by
        have him : (D.powerSum ν).im = 0 := Complex.conj_eq_iff_im.mp (D.conj_powerSum ν)
        exact Complex.ext (by simp [ArithmeticCastelnuovoSeveri.CurveDatum.trace])
          (by simp [him])
      rw [hps, hreal, Complex.norm_real, Real.norm_eq_abs]
      exact hb ν hν
    have h1 := norm_le_one_of_thick_bounded_levelSums (c := fun _ : κ => (1 : ℂ)) (z := D.β) hsum
      (fun _ => by simp) (fun j => hi₀ j (Finset.mem_univ j)) (by simp) hG hb'
    exact (hi₀ i (Finset.mem_univ i)).trans h1
  intro i
  have hfe := D.β_fePerm i
  have hprod : ‖D.β (D.fePerm i)‖ * ‖D.β i‖ = 1 := by rw [← norm_mul, hfe, norm_one]
  have h1 := hle i
  have h2 := hle (D.fePerm i)
  have h3 : 0 ≤ ‖D.β i‖ := norm_nonneg _
  have h4 : 0 ≤ ‖D.β (D.fePerm i)‖ := norm_nonneg _
  nlinarith

/-! ### The towers of `ζ`, normalized at the abscissa -/

/-- The mode `e^{ℓ(q − Θ)}` of the zero `q` at base `ℓ`, normalized at the weight `Θ`. -/
noncomputable def abscissaMode (ℓ Θ : ℝ) (q : XiZeroCopy) : ℂ :=
  Complex.exp ((ℓ : ℂ) * ((q.1 : ℂ) - Θ))

theorem norm_abscissaMode (ℓ Θ : ℝ) (q : XiZeroCopy) :
    ‖abscissaMode ℓ Θ q‖ = Real.exp (ℓ * ((q.1 : ℂ).re - Θ)) := by
  rw [abscissaMode, Complex.norm_exp]
  congr 1
  simp

theorem norm_abscissaMode_le_one {ℓ Θ : ℝ} (hℓ : 0 < ℓ)
    (hmax : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ Θ) (q : XiZeroCopy) : ‖abscissaMode ℓ Θ q‖ ≤ 1 := by
  rw [norm_abscissaMode, Real.exp_le_one_iff]
  exact mul_nonpos_of_nonneg_of_nonpos hℓ.le (by linarith [hmax q])

/-- `Φ(νℓ) = e^{νℓ(Θ − ½)} Σ_q w_q (e^{ℓ(q − Θ)})^ν`. -/
theorem weilLagFunction_eq_towerSum (ℓ Θ : ℝ) (ν : ℕ) :
    weilLagFunction (ν * ℓ) =
      Complex.exp ((ν : ℂ) * ((ℓ : ℂ) * ((Θ : ℂ) - 1 / 2))) *
        towerSum lagW (abscissaMode ℓ Θ) ν := by
  rw [weilLagFunction, towerSum, ← tsum_mul_left]
  refine tsum_congr fun q => ?_
  rw [abscissaMode, lagW, ← Complex.exp_nat_mul, div_eq_mul_one_div, mul_comm,
    ← mul_assoc, mul_comm _ (1 / _), mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem norm_abscissa_towerSum (ℓ Θ : ℝ) (ν : ℕ) :
    ‖towerSum lagW (abscissaMode ℓ Θ) ν‖ =
      Real.exp (-(ν * (ℓ * (Θ - 1 / 2)))) * ‖weilLagFunction (ν * ℓ)‖ := by
  rw [weilLagFunction_eq_towerSum ℓ Θ ν, norm_mul, Complex.norm_exp, ← mul_assoc,
    ← Real.exp_add]
  have : -(ν * (ℓ * (Θ - 1 / 2))) + ((ν : ℂ) * ((ℓ : ℂ) * ((Θ : ℂ) - 1 / 2))).re = 0 := by
    simp
  rw [this, Real.exp_zero, one_mul]

/-- **The lag along one tower is not smaller than the attained abscissa allows.** If the largest
real part `β₀` of a zero is attained and `a < β₀ − ½`, the lag along the tower at base `ℓ > 0` is not
`O(e^{aνℓ})` on any thick set of levels. -/
theorem lag_not_small_of_attainedTop {ℓ : ℝ} (hℓ : 0 < ℓ) {β₀ : ℝ} (h : AttainedTop β₀) {a : ℝ}
    (ha : a < β₀ - 1 / 2) {G : Set ℕ} (hG : Thick G) (C : ℝ) :
    ¬ ∀ ν ∈ G, ‖weilLagFunction (ν * ℓ)‖ ≤ C * Real.exp (a * ν * ℓ) := by
  intro hbound
  obtain ⟨⟨q₀, hq₀⟩, hmax⟩ := h
  have h1 : ‖abscissaMode ℓ β₀ q₀‖ = 1 := by
    rw [norm_abscissaMode, hq₀, sub_self, mul_zero, Real.exp_zero]
  -- the normalized tower is small along `G`
  set κ : ℝ := Real.exp (ℓ * (a - (β₀ - 1 / 2))) with hκ
  have hκ0 : 0 ≤ κ := (Real.exp_pos _).le
  have hκ1 : κ < 1 := by
    rw [hκ, Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg hℓ (by linarith)
  have hgeom : Tendsto (fun ν : ℕ => |C| * κ ^ ν) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1).const_mul |C|
  refine not_small_on_thick_of_circle_mode summable_norm_lagW (norm_abscissaMode_le_one hℓ hmax)
    (fun q => (re_lagW_pos q).le) h1 (re_lagW_pos q₀) hG fun δ hδ => ?_
  obtain ⟨ν₀, hν₀⟩ := eventually_atTop.mp (hgeom.eventually (ge_mem_nhds hδ))
  refine ⟨ν₀, fun ν hν hge => ?_⟩
  rw [norm_abscissa_towerSum]
  have hpos : 0 < Real.exp (-(ν * (ℓ * (β₀ - 1 / 2)))) := Real.exp_pos _
  calc Real.exp (-(ν * (ℓ * (β₀ - 1 / 2)))) * ‖weilLagFunction (ν * ℓ)‖
      ≤ Real.exp (-(ν * (ℓ * (β₀ - 1 / 2)))) * (C * Real.exp (a * ν * ℓ)) :=
        mul_le_mul_of_nonneg_left (hbound ν hν) hpos.le
    _ = C * κ ^ ν := by
        rw [hκ, ← Real.exp_nat_mul, mul_left_comm, ← Real.exp_add]
        congr 2
        ring
    _ ≤ |C| * κ ^ ν := mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hκ0 ν)
    _ ≤ δ := hν₀ ν hge

/-- The trivial bound: the lag along a tower grows at most at the rate of the abscissa. -/
theorem norm_weilLagFunction_le_of_re_le {ℓ Θ : ℝ} (hℓ : 0 < ℓ)
    (hmax : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ Θ) (ν : ℕ) :
    ‖weilLagFunction (ν * ℓ)‖ ≤ (∑' q, ‖lagW q‖) * Real.exp ((Θ - 1 / 2) * ν * ℓ) := by
  rw [weilLagFunction_eq_towerSum ℓ Θ ν, norm_mul, Complex.norm_exp, mul_comm]
  have hexp : ((ν : ℂ) * ((ℓ : ℂ) * ((Θ : ℂ) - 1 / 2))).re = (Θ - 1 / 2) * ν * ℓ := by
    simp
    ring
  rw [hexp]
  exact mul_le_mul_of_nonneg_right
    (norm_towerSum_le summable_norm_lagW (norm_abscissaMode_le_one hℓ hmax) ν)
    (Real.exp_pos _).le

/-- **The tower reads the attained abscissa.** If the largest real part `β₀` of a zero is attained,
the lag along the tower at base `ℓ > 0` is `O(e^{aνℓ})` exactly when `β₀ − ½ ≤ a`. -/
theorem lag_bound_iff_of_attainedTop {ℓ : ℝ} (hℓ : 0 < ℓ) {β₀ : ℝ} (h : AttainedTop β₀) (a : ℝ) :
    (∃ C : ℝ, ∀ ν : ℕ, ‖weilLagFunction (ν * ℓ)‖ ≤ C * Real.exp (a * ν * ℓ)) ↔
      β₀ - 1 / 2 ≤ a := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hlt
    exact lag_not_small_of_attainedTop hℓ h (not_le.mp hlt) thick_univ C fun ν _ => hC ν
  · intro hle
    refine ⟨∑' q, ‖lagW q‖, fun ν => ?_⟩
    refine (norm_weilLagFunction_le_of_re_le hℓ h.2 ν).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
      (tsum_nonneg fun _ => norm_nonneg _)
    have hν : (0 : ℝ) ≤ ν := Nat.cast_nonneg ν
    nlinarith [mul_nonneg hν hℓ.le]

/-- Under RH the abscissa `½` is attained. -/
theorem attainedTop_half_of_riemannHypothesis (hRH : RiemannHypothesis) : AttainedTop (1 / 2) := by
  have hhalf := riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH
  obtain ⟨ρ, hρ⟩ := xiZeros_infinite.nonempty
  obtain ⟨q₀, -⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  exact ⟨⟨q₀, hhalf _ (xi_xiZeroCopy_eq_zero q₀)⟩, fun q => (hhalf _ (xi_xiZeroCopy_eq_zero q)).le⟩

/-- **RH is an attained abscissa plus one thick bounded lag.** The Riemann hypothesis holds iff the
largest real part of a zero is attained and the lag is bounded along a thick set of levels of one
tower. -/
theorem riemannHypothesis_iff_attainedTop_and_thick_lag_bounded :
    RiemannHypothesis ↔ (∃ β₀ : ℝ, AttainedTop β₀) ∧
      ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ G : Set ℕ, Thick G ∧ ∃ C : ℝ,
        ∀ ν ∈ G, ‖weilLagFunction (ν * ℓ)‖ ≤ C := by
  constructor
  · intro hRH
    exact ⟨⟨1 / 2, attainedTop_half_of_riemannHypothesis hRH⟩, 1, one_pos, Set.univ, thick_univ,
      RHTower.poleSharpConstant,
      fun ν _ => RHTower.norm_weilLagFunction_le_of_riemannHypothesis hRH _⟩
  · rintro ⟨⟨β₀, h⟩, ℓ, hℓ, G, hG, C, hC⟩
    have htop : β₀ - 1 / 2 ≤ 0 := by
      by_contra hlt
      exact lag_not_small_of_attainedTop hℓ h (not_le.mp hlt) hG C
        fun ν hν => by simpa using hC ν hν
    rw [riemannHypothesis_iff_xiZeroHalfPlaneBound_zero]
    intro ρ hρ
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have := h.2 q
    rw [hq] at this
    linarith

/-- A lag bounded on a thick set of levels of one tower leaves two worlds: RH, or an abscissa that no
zero attains. -/
theorem riemannHypothesis_or_not_attainedTop {ℓ C : ℝ} (hℓ : 0 < ℓ) {G : Set ℕ}
    (hG : Thick G) (hC : ∀ ν ∈ G, ‖weilLagFunction (ν * ℓ)‖ ≤ C) :
    RiemannHypothesis ∨ ¬ ∃ β₀ : ℝ, AttainedTop β₀ := by
  by_cases h : ∃ β₀ : ℝ, AttainedTop β₀
  · exact Or.inl (riemannHypothesis_iff_attainedTop_and_thick_lag_bounded.mpr
      ⟨h, ℓ, hℓ, G, hG, C, hC⟩)
  · exact Or.inr h

/-- **The same in primes.** RH holds iff the abscissa is attained and, for one base `ℓ`, the prime
deviation `(X − ψ(X)) + X(Σ_{n≤X} Λ(n)/n − log X + γ) − log 2π + …` is `O(X^{1/2})` along
`X = e^{νℓ}`, `ν` in a thick set. -/
theorem riemannHypothesis_iff_attainedTop_and_thick_primeDeviation :
    RiemannHypothesis ↔ (∃ β₀ : ℝ, AttainedTop β₀) ∧
      ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ G : Set ℕ, Thick G ∧ ∃ C : ℝ, ∀ ν ∈ G, 1 ≤ ν →
        ‖InfiniteRankWeilTheory.primeDeviation (Real.exp (ν * ℓ))‖ ≤
          C * Real.exp ((ν * ℓ) / 2) := by
  rw [riemannHypothesis_iff_attainedTop_and_thick_lag_bounded]
  have he : ∀ x : ℝ, Real.exp (x / 2) * Real.exp (-x / 2) = 1 := fun x => by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  constructor
  · rintro ⟨hA, ℓ, hℓ, G, hG, C, hC⟩
    refine ⟨hA, ℓ, hℓ, G, hG, C, fun ν hν hν1 => ?_⟩
    have hL : 0 < (ν : ℝ) * ℓ := mul_pos (by exact_mod_cast hν1) hℓ
    have h := hC ν hν
    rw [InfiniteRankWeilTheory.norm_weilLagFunction_eq hL] at h
    calc ‖InfiniteRankWeilTheory.primeDeviation (Real.exp (ν * ℓ))‖
        = Real.exp ((ν * ℓ) / 2) * (Real.exp (-(ν * ℓ) / 2) *
            ‖InfiniteRankWeilTheory.primeDeviation (Real.exp (ν * ℓ))‖) := by
          rw [← mul_assoc, he, one_mul]
      _ ≤ Real.exp ((ν * ℓ) / 2) * C := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = C * Real.exp ((ν * ℓ) / 2) := mul_comm _ _
  · rintro ⟨hA, ℓ, hℓ, G, hG, C, hC⟩
    refine ⟨hA, ℓ, hℓ, G ∩ Set.Ici 1, InfiniteRankWeilTheory.thick_inter_Ici hG 1, C,
      fun ν hν => ?_⟩
    have hν1 : 1 ≤ ν := hν.2
    have hL : 0 < (ν : ℝ) * ℓ := mul_pos (by exact_mod_cast hν1) hℓ
    rw [InfiniteRankWeilTheory.norm_weilLagFunction_eq hL]
    have hb := hC ν hν.1 hν1
    calc Real.exp (-(ν * ℓ) / 2) * ‖InfiniteRankWeilTheory.primeDeviation (Real.exp (ν * ℓ))‖
        ≤ Real.exp (-(ν * ℓ) / 2) * (C * Real.exp ((ν * ℓ) / 2)) :=
          mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = C := by rw [mul_left_comm, mul_comm (Real.exp _), he, mul_one]

end GaloisForLFunctions.InfiniteRankPurityTheory
