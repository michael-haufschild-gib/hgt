import GaloisForLFunctions.InfiniteRankWeilTheory.TheExceptionalCoordinate
import GaloisForLFunctions.RHTower.ZetaWeakRecurrenceLadderCollapse
import GaloisForLFunctions.RHTower.WeilLagFunction
import GaloisForLFunctions.RHTower.XiTaylorCoefficientsLogConcave

/-!
# The towers of ζ

At base `ℓ > 0` the zeros of `ξ` (with multiplicity) form the Weil tower `z_q = e^{ℓ(q−½)}`
(`zetaTower`), closed under conjugation and the functional equation. Sampling the Weil lag function
`Φ(L) = Σ_q e^{L(q−½)}/(q(1−q))` at the levels `L = νℓ` is the level sum of this tower with the lag
weights `1/(q(1−q))` (`weilLagFunction_mul_eq_levelSum`). These weights have positive real part, so
every point of every tower is visible (`mergedLagWeight_ne_zero`).

The window theorem then reads, for `ζ`:

* `exists_syndetic_lag_excursions_of_not_asymptoticAbscissaLaw`: if AAL fails, there are a rank `k`
  (the number of top zeros) and an exponent `a > 0` such that at **every** base `ℓ > 0` and for every
  constant `C`, beyond some level every window of `k` consecutive levels contains a level with
  `|Φ(νℓ)| > C e^{aνℓ}`. The rank of the window is the exceptional rank and does not depend on the
  base.
* `asymptoticAbscissaLaw_of_thick_lag_bound`: conversely, AAL follows if at one base the lag has
  growth exponent `0` along a thick set of levels.
* `riemannHypothesis_iff_zerosApproachLine_and_thick_lag_bounded`: RH is ZAL plus one bounded lag
  along a thick set of levels of one tower. By `TheRankBarrier`, no density statement in the levels
  can replace "thick" in an argument that applies to all towers of finite exceptional rank.
-/

open Complex
open RHTower (XiZeroCopy weilLagFunction xiZeroCopyConjEquiv xiZeroCopyReflectEquiv)

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- The zero configuration of `ξ`. -/
def zetaConfig : XiZeroCopy → ℂ := fun q => (q.1 : ℂ)

/-- The corpus AAL is AAL of the zero configuration. -/
theorem asymptoticAbscissaLaw_zetaConfig_iff :
    RHTower.AsymptoticAbscissaLaw ↔ AsymptoticAbscissaLaw zetaConfig := Iff.rfl

/-- The tower of `ζ` at base `ℓ`. -/
def zetaTower (ℓ : ℝ) : WeilTower XiZeroCopy where
  z := frobTower ℓ zetaConfig
  conjPerm := xiZeroCopyConjEquiv
  z_conjPerm q := by
    simp only [frobTower, zetaConfig, RHTower.xiZeroCopyConjEquiv_coe, ← Complex.exp_conj, map_mul,
      map_sub, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]
  invPerm := xiZeroCopyReflectEquiv
  z_invPerm q := by
    simp only [frobTower, zetaConfig, RHTower.xiZeroCopy_reflect_val, ← Complex.exp_add]
    rw [show (ℓ : ℂ) * (1 - (q.1 : ℂ) - 1 / 2) + ℓ * ((q.1 : ℂ) - 1 / 2) = 0 by ring,
      Complex.exp_zero]

/-- The lag weight `1/(q(1−q))`. -/
def lagWeight (q : XiZeroCopy) : ℂ := 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))

/-- **The lag along a tower is a level sum.** `Φ(νℓ) = Σ_q (1/(q(1−q))) z_qᵛ`. -/
theorem weilLagFunction_mul_eq_levelSum (ℓ : ℝ) (ν : ℕ) :
    weilLagFunction (ν * ℓ) = levelSum (frobTower ℓ zetaConfig) lagWeight ν := by
  unfold weilLagFunction levelSum
  refine tsum_congr fun q => ?_
  rw [zpow_natCast, frobTower_pow, lagWeight, zetaConfig]
  ring

/-- The lag weights have positive real part. -/
theorem re_lagWeight_pos (q : XiZeroCopy) : 0 < (lagWeight q).re := by
  have h0 := RHTower.xiZeroCopy_re_pos q
  have h1 := RHTower.xiZeroCopy_re_lt_one q
  set w : ℂ := (q.1 : ℂ) * (1 - (q.1 : ℂ)) with hw
  have hwre : 0 < w.re := by
    have : w.re = (q.1 : ℂ).re * (1 - (q.1 : ℂ).re) + (q.1 : ℂ).im ^ 2 := by
      simp only [hw, Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im,
        Complex.one_im]
      ring
    rw [this]
    nlinarith [sq_nonneg (q.1 : ℂ).im]
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at hwre; exact lt_irrefl _ hwre
  rw [lagWeight, ← hw, one_div, Complex.inv_re]
  exact div_pos hwre (Complex.normSq_pos.mpr hw0)

/-- **Every point of a tower of `ζ` is visible**: merged lag weights are nonzero. -/
theorem mergedLagWeight_ne_zero (ℓ : ℝ) (F : Finset XiZeroCopy) {q : XiZeroCopy} (hq : q ∈ F) :
    (∑ j ∈ F with frobTower ℓ zetaConfig j = frobTower ℓ zetaConfig q, lagWeight j) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  rw [Complex.re_sum, Complex.zero_re] at hre
  have hpos : 0 < ∑ j ∈ F with frobTower ℓ zetaConfig j = frobTower ℓ zetaConfig q,
      (lagWeight j).re :=
    Finset.sum_pos (fun j _ => re_lagWeight_pos j) ⟨q, Finset.mem_filter.2 ⟨hq, rfl⟩⟩
  linarith

theorem summable_norm_lagWeight : Summable fun q => ‖lagWeight q‖ :=
  RHTower.summable_norm_inv_mul_one_sub

/-- The window data of an isolated top of `ζ` at base `ℓ`. -/
theorem zeta_window_data {ℓ : ℝ} (hℓ : 0 < ℓ) {F : Finset XiZeroCopy} {Θ Θ₂ : ℝ}
    (hFne : F.Nonempty) (hΘ₂ : Θ₂ < Θ) (hF : ∀ q ∈ F, (zetaConfig q).re = Θ)
    (hrest : ∀ q ∉ F, (zetaConfig q).re ≤ Θ₂) :
    (∀ q ∉ F, ‖frobTower ℓ zetaConfig q‖ ≤ Real.exp (ℓ * (Θ₂ - 1 / 2))) ∧
      (∀ q ∈ F, (∑ j ∈ F with frobTower ℓ zetaConfig j = frobTower ℓ zetaConfig q, lagWeight j)
        ≠ 0 → ‖frobTower ℓ zetaConfig q‖ = Real.exp (ℓ * (Θ - 1 / 2))) ∧
      (∃ q ∈ F, (∑ j ∈ F with frobTower ℓ zetaConfig j = frobTower ℓ zetaConfig q, lagWeight j)
        ≠ 0) ∧
      Real.exp (ℓ * (Θ₂ - 1 / 2)) < Real.exp (ℓ * (Θ - 1 / 2)) := by
  obtain ⟨htop, hlow, hlt⟩ := frobTower_isolatedTop hℓ hΘ₂ hF hrest
  obtain ⟨q₀, hq₀⟩ := hFne
  exact ⟨hlow, fun q hq _ => htop q hq, ⟨q₀, hq₀, mergedLagWeight_ne_zero ℓ F hq₀⟩, hlt⟩

/-- **Syndetic lag excursions.** If AAL fails, there are `k` (the exceptional rank) and `a > 0` such
that at every base `ℓ > 0` and for every `C`, beyond some level every window of `k` consecutive
levels contains `ν` with `|Φ(νℓ)| > C e^{aνℓ}`. -/
theorem exists_syndetic_lag_excursions_of_not_asymptoticAbscissaLaw
    (hnot : ¬ RHTower.AsymptoticAbscissaLaw) :
    ∃ k : ℕ, 0 < k ∧ ∃ a : ℝ, 0 < a ∧ ∀ ℓ : ℝ, 0 < ℓ → ∀ C : ℝ, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M →
      ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + k ∧
        C * Real.exp (a * ν * ℓ) < ‖weilLagFunction (ν * ℓ)‖ := by
  rw [asymptoticAbscissaLaw_zetaConfig_iff, not_asymptoticAbscissaLaw_iff_hasIsolatedTop] at hnot
  obtain ⟨F, Θ, Θ₂, hFne, hΘ, hΘ₂, hF, hrest⟩ := hnot
  refine ⟨F.card, hFne.card_pos, (Θ - 1 / 2) / 2, by linarith, fun ℓ hℓ C => ?_⟩
  obtain ⟨hlow, htop, hvis, hlt⟩ := zeta_window_data hℓ hFne hΘ₂ hF hrest
  have hρR : Real.exp ((Θ - 1 / 2) / 2 * ℓ) < Real.exp (ℓ * (Θ - 1 / 2)) :=
    Real.exp_lt_exp.mpr (by nlinarith)
  obtain ⟨M₀, hM₀⟩ := eventually_forall_window_exists_lt_norm_levelSum (frobTower ℓ zetaConfig)
    lagWeight summable_norm_lagWeight F (Real.exp_pos _) (Real.exp_pos _).le hlt hlow htop hvis
    (C := C) (Real.exp_pos _).le hρR
  refine ⟨M₀, fun M hM => ?_⟩
  obtain ⟨ν, h1, h2, h3⟩ := hM₀ M hM
  refine ⟨ν, h1, h2, ?_⟩
  rw [weilLagFunction_mul_eq_levelSum, show (Θ - 1 / 2) / 2 * (ν : ℝ) * ℓ =
    ν * ((Θ - 1 / 2) / 2 * ℓ) by ring, Real.exp_nat_mul]
  exact h3

/-- **AAL from a thick lag bound.** If at one base `ℓ > 0` the lag along a thick set of levels grows
slower than every exponential, AAL holds. -/
theorem asymptoticAbscissaLaw_of_thick_lag_bound {ℓ : ℝ} (hℓ : 0 < ℓ)
    (h : ∀ a : ℝ, 0 < a → ∃ G : Set ℕ, Thick G ∧ ∃ C : ℝ,
      ∀ ν ∈ G, ‖weilLagFunction (ν * ℓ)‖ ≤ C * Real.exp (a * ν * ℓ)) :
    RHTower.AsymptoticAbscissaLaw := by
  by_contra hnot
  rw [asymptoticAbscissaLaw_zetaConfig_iff, not_asymptoticAbscissaLaw_iff_hasIsolatedTop] at hnot
  obtain ⟨F, Θ, Θ₂, hFne, hΘ, hΘ₂, hF, hrest⟩ := hnot
  obtain ⟨hlow, htop, hvis, hlt⟩ := zeta_window_data hℓ hFne hΘ₂ hF hrest
  obtain ⟨G, hG, C, hC⟩ := h ((Θ - 1 / 2) / 2) (by linarith)
  have hρR : Real.exp ((Θ - 1 / 2) / 2 * ℓ) < Real.exp (ℓ * (Θ - 1 / 2)) :=
    Real.exp_lt_exp.mpr (by nlinarith)
  refine not_forall_mem_thick_norm_levelSum_le (frobTower ℓ zetaConfig) lagWeight
    summable_norm_lagWeight F (Real.exp_pos _) (Real.exp_pos _).le hlt hlow htop hvis
    (Real.exp_pos _).le hρR hG (fun ν hν => ?_)
  have := hC ν hν
  rwa [weilLagFunction_mul_eq_levelSum, show (Θ - 1 / 2) / 2 * (ν : ℝ) * ℓ =
    ν * ((Θ - 1 / 2) / 2 * ℓ) by ring, Real.exp_nat_mul] at this

/-- **RH is ZAL plus one thick bounded lag.** `RH ⇔ ZAL ∧` the lag is bounded along a thick set of
levels of one tower. -/
theorem riemannHypothesis_iff_zerosApproachLine_and_thick_lag_bounded :
    RiemannHypothesis ↔ RHTower.ZerosApproachLine ∧
      ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ G : Set ℕ, Thick G ∧ ∃ C : ℝ,
        ∀ ν ∈ G, ‖weilLagFunction (ν * ℓ)‖ ≤ C := by
  constructor
  · intro hRH
    refine ⟨(RHTower.riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.1 hRH).1,
      1, one_pos, Set.univ, thick_univ, RHTower.poleSharpConstant, fun ν _ => ?_⟩
    exact RHTower.norm_weilLagFunction_le_of_riemannHypothesis hRH _
  · rintro ⟨hZ, ℓ, hℓ, G, hG, C, hC⟩
    refine RHTower.riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.2
      ⟨hZ, asymptoticAbscissaLaw_of_thick_lag_bound hℓ fun a ha =>
        ⟨G, hG, max C 0, fun ν hν => ?_⟩⟩
    calc ‖weilLagFunction (ν * ℓ)‖ ≤ C := hC ν hν
      _ ≤ max C 0 := le_max_left _ _
      _ ≤ max C 0 * Real.exp (a * ν * ℓ) :=
          le_mul_of_one_le_right (le_max_right _ _) (Real.one_le_exp (by positivity))

end GaloisForLFunctions.InfiniteRankWeilTheory
