import GaloisForLFunctions.RHTower.PaperWoldDirectedCovarianceRH
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualNaturalWidthSpectrum
import GaloisForLFunctions.RHTower.CCM.CCMGeneralizedVonKoch
import GaloisForLFunctions.RHTower.ZetaRealStrip

/-!
# The Wold energy abscissa is the zero abscissa

For `0 ≤ α < 1/2` the following are equivalent:

* `XiZeroHalfPlaneBound α`: every zero of `ξ` has `Re ρ ≤ 1/2 + α`;
* the natural Wold square energy `E(t) = Σ_N N^(2t-1) R_N²` is finite for every `0 < t < 1/2 - α`
  (`xiZeroHalfPlaneBound_iff_forall_woldNatResidualSquareEnergy`);
* the signed directed covariance `D_t(N) + Q_t(N)/2` of the literal Wold increments is bounded in
  `N` for every `0 < t < 1/2 - α` (`xiZeroHalfPlaneBound_iff_forall_directedCovariance_bdd`).

The raw covariance `D_t(N)` alone is bounded below unconditionally for `0 ≤ t < 1/2`
(`exists_le_directedCovariance`, the diagonal is summable), so the whole content is one-sided:
`XiZeroHalfPlaneBound α` iff `D_t` is bounded above for every `0 < t < 1/2 - α`
(`xiZeroHalfPlaneBound_iff_forall_directedCovariance_bddAbove`).

Hence the energy abscissa `sup {t : E(t) < ∞}` equals `1 - sup Re ρ` at every width, and route TT's
covariance sees exactly the zero-free half-plane of matching width.  At `α = 0` these are
`riemannHypothesis_iff_forall_woldNatResidualSquareEnergy_lt_half` and
`riemannHypothesis_iff_forall_directedCovariance_bdd`.

**Forward.**  Generalized von Koch gives the Chebyshev power spectrum at width `α`, which transports
to the Wold power spectrum: `|R_N| ≤ B N^(-c)` for every `c < 1/2 - α`.  With `t < c` the energy is
dominated by `B² Σ N^(2t-1-2c)`; with `c = t` the boundary term of the covariance is bounded.

**Reverse.**  Finite energy at `t ≤ 1/2` makes the Abel current regular on `Re s > 1 - t`
(`riemannZeta_ne_zero_of_squareEnergy_subhalf`).  A zero with `Re ρ > 1/2 + α` lies right of
`1 - t` for `t = (1 - Re ρ + 1/2 - α)/2`; real zeros in the strip are excluded separately.
-/

namespace RHTower
noncomputable section
open Filter

local notation "R" => xiHeatCassiniWoldNatResidualLogDiscrepancy

/-- A Wold power rate strictly beyond the radius makes the square energy finite. -/
theorem woldNatResidualSquareEnergy_of_powerSpectrum {α t : ℝ} (ht0 : 0 < t)
    (ht : t < 1 / 2 - α) (h : WoldNatResidualPowerSpectrum α) : WoldNatResidualSquareEnergy t := by
  let c : ℝ := (t + (1 / 2 - α)) / 2
  obtain ⟨B, -, hrate⟩ := h c (by dsimp only [c]; linarith) (by dsimp only [c]; linarith)
  have hmaj : Summable (fun N : ℕ => B ^ 2 * (N : ℝ) ^ (2 * t - 1 - 2 * c)) :=
    (Real.summable_nat_rpow.mpr (by dsimp only [c]; linarith)).mul_left _
  refine Summable.of_norm_bounded_eventually hmaj ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hrate, eventually_ge_atTop 1] with N hN hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hR2 : |R N| ^ 2 ≤ (B * (N : ℝ) ^ (-c)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hN 2
  calc (N : ℝ) ^ (2 * t - 1) * |R N| ^ 2
      ≤ (N : ℝ) ^ (2 * t - 1) * (B * (N : ℝ) ^ (-c)) ^ 2 :=
        mul_le_mul_of_nonneg_left hR2 (by positivity)
    _ = B ^ 2 * (N : ℝ) ^ (2 * t - 1 - 2 * c) := by
        rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ _), ← Real.rpow_mul hNpos.le]
        rw [mul_comm, mul_assoc, ← Real.rpow_add hNpos]
        congr 2
        push_cast
        ring

/-- Finite square energy below the complementary radius bounds every zero of `ξ`. -/
theorem xiZeroHalfPlaneBound_of_forall_woldNatResidualSquareEnergy {α : ℝ} (hα0 : 0 ≤ α)
    (h : ∀ t : ℝ, 0 < t → t < 1 / 2 - α → WoldNatResidualSquareEnergy t) :
    XiZeroHalfPlaneBound α := by
  intro ρ hρ
  by_contra hlt0
  have hlt := not_le.mp hlt0
  obtain ⟨hz, -⟩ := xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hρ
  have h1 : ρ.re < 1 := by
    by_contra hc
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hc) hz
  let t : ℝ := (1 - ρ.re + (1 / 2 - α)) / 2
  have ht0 : 0 < t := by dsimp only [t]; linarith
  have htlt : t < 1 / 2 - α := by dsimp only [t]; linarith
  have hthalf : t ≤ 1 / 2 := by dsimp only [t]; linarith
  have hre : 1 - t < ρ.re := by dsimp only [t]; linarith
  have hE := h t ht0 htlt
  rcases lt_trichotomy ρ.im 0 with him | him | him
  · have hc : riemannZeta (starRingEnd ℂ ρ) = 0 := by rw [riemannZeta_conj, hz, map_zero]
    exact riemannZeta_ne_zero_of_squareEnergy_subhalf ht0 hthalf hE (by simpa using hre)
      (by simpa using him) hc
  · have hρeq : ρ = ((ρ.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
    rw [hρeq] at hz
    exact riemannZeta_real_strip_ne_zero (by linarith) h1 hz
  · exact riemannZeta_ne_zero_of_squareEnergy_subhalf ht0 hthalf hE hre him hz

/-- **The Wold energy abscissa is the zero abscissa.**  For `0 ≤ α < 1/2`, every zero of `ξ` has
`Re ρ ≤ 1/2 + α` iff the natural Wold square energy is finite at every radius `0 < t < 1/2 - α`. -/
theorem xiZeroHalfPlaneBound_iff_forall_woldNatResidualSquareEnergy {α : ℝ} (hα0 : 0 ≤ α)
    (hα : α < 1 / 2) :
    XiZeroHalfPlaneBound α ↔ ∀ t : ℝ, 0 < t → t < 1 / 2 - α → WoldNatResidualSquareEnergy t :=
  ⟨fun hXi _ ht0 ht => woldNatResidualSquareEnergy_of_powerSpectrum ht0 ht
      (woldNatResidualPowerSpectrum_of_chebyshevErrorPowerSpectrum hα0
        (chebyshevErrorPowerSpectrum_of_xiZeroHalfPlaneBound_lt_half hα0 hα hXi)),
    xiZeroHalfPlaneBound_of_forall_woldNatResidualSquareEnergy hα0⟩

/-- **Route TT's signed covariance sees exactly the zero-free half-plane of matching width.** -/
theorem xiZeroHalfPlaneBound_iff_forall_directedCovariance_bdd {α : ℝ} (hα0 : 0 ≤ α)
    (hα : α < 1 / 2) :
    XiZeroHalfPlaneBound α ↔ ∀ t : ℝ, 0 < t → t < 1 / 2 - α → ∃ C : ℝ, ∀ N : ℕ,
      directedCovariance (woldPowerWeight t) woldShiftedResidual N +
        incrementDiagonal (woldPowerWeight t) woldShiftedResidual N / 2 ≤ C := by
  rw [xiZeroHalfPlaneBound_iff_forall_woldNatResidualSquareEnergy hα0 hα]
  constructor
  · intro hE t ht0 ht
    have hspec : WoldNatResidualPowerSpectrum α :=
      woldNatResidualPowerSpectrum_of_chebyshevErrorPowerSpectrum hα0
        (chebyshevErrorPowerSpectrum_of_xiZeroHalfPlaneBound_lt_half hα0 hα
          (xiZeroHalfPlaneBound_of_forall_woldNatResidualSquareEnergy hα0 hE))
    obtain ⟨B, -, hrate⟩ := hspec t ht0 ht
    exact exists_directedCovariance_bdd_of_squareEnergy (c := t) ht0 (by linarith) le_rfl
      (hE t ht0 ht) ⟨B, hrate⟩
  · intro hC t ht0 ht
    exact woldNatResidualSquareEnergy_of_directedCovariance_bdd ht0 (by linarith) (hC t ht0 ht)

/-! ### The raw signed covariance -/

/-- Below one half the weighted increment diagonal is summable, unconditionally. -/
theorem summable_woldIncrementDiagonal {t : ℝ} (ht : t < 1 / 2) :
    Summable (fun n : ℕ => woldPowerWeight t n * seqIncrement woldShiftedResidual n ^ 2) := by
  set ε : ℝ := (1 / 2 - t) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hsum : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (2 * t - 2 + 2 * ε)) := by
    have h := (summable_nat_add_iff 1).mpr
      ((Real.summable_nat_rpow (p := 2 * t - 2 + 2 * ε)).mpr (by rw [hε]; linarith))
    simpa [Nat.cast_add, Nat.cast_one] using h
  refine Summable.of_nonneg_of_le (fun n => by unfold woldPowerWeight; positivity) (fun n => ?_)
    (hsum.mul_left ((2 + 1 / ε) ^ 2))
  have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hx1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hd : |seqIncrement woldShiftedResidual n| ≤ (Real.log ((n : ℝ) + 1) + 2) / ((n : ℝ) + 1) := by
    rw [seqIncrement_woldShiftedResidual]; exact xiHeatCassiniWoldNatIncrement_abs_le n
  have hpow1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ ε := Real.one_le_rpow hx1 hε0.le
  have hlog : Real.log ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ ε / ε := Real.log_le_rpow_div hx.le hε0
  have hnum : Real.log ((n : ℝ) + 1) + 2 ≤ (2 + 1 / ε) * ((n : ℝ) + 1) ^ ε := by
    have hrw : ((n : ℝ) + 1) ^ ε / ε = 1 / ε * ((n : ℝ) + 1) ^ ε := by ring
    rw [hrw] at hlog
    nlinarith
  have hd' : seqIncrement woldShiftedResidual n ^ 2 ≤
      ((2 + 1 / ε) * ((n : ℝ) + 1) ^ ε / ((n : ℝ) + 1)) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (hd.trans (div_le_div_of_nonneg_right hnum hx.le)) 2
  have heq : woldPowerWeight t n * ((2 + 1 / ε) * ((n : ℝ) + 1) ^ ε / ((n : ℝ) + 1)) ^ 2 =
      (2 + 1 / ε) ^ 2 * ((n : ℝ) + 1) ^ (2 * t - 2 + 2 * ε) := by
    unfold woldPowerWeight
    rw [show 2 * t - 2 + 2 * ε = 2 * t + ε + ε + (-1) + (-1) by ring, Real.rpow_add hx,
      Real.rpow_add hx, Real.rpow_add hx, Real.rpow_add hx, Real.rpow_neg_one]
    field_simp
  calc woldPowerWeight t n * seqIncrement woldShiftedResidual n ^ 2
      ≤ woldPowerWeight t n * ((2 + 1 / ε) * ((n : ℝ) + 1) ^ ε / ((n : ℝ) + 1)) ^ 2 :=
        mul_le_mul_of_nonneg_left hd' (by unfold woldPowerWeight; positivity)
    _ = (2 + 1 / ε) ^ 2 * ((n : ℝ) + 1) ^ (2 * t - 2 + 2 * ε) := heq

private theorem incrementDiagonal_nonneg_le {t : ℝ} (ht : t < 1 / 2) (N : ℕ) :
    0 ≤ incrementDiagonal (woldPowerWeight t) woldShiftedResidual N ∧
      incrementDiagonal (woldPowerWeight t) woldShiftedResidual N ≤
        ∑' n, woldPowerWeight t n * seqIncrement woldShiftedResidual n ^ 2 := by
  have hnn : ∀ n, 0 ≤ woldPowerWeight t n * seqIncrement woldShiftedResidual n ^ 2 :=
    fun n => by unfold woldPowerWeight; positivity
  exact ⟨Finset.sum_nonneg fun n _ => hnn n,
    (summable_woldIncrementDiagonal ht).sum_le_tsum _ fun n _ => hnn n⟩

/-- **The raw signed covariance is bounded below, unconditionally**, at every radius
`0 ≤ t < 1/2`. -/
theorem exists_le_directedCovariance {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1 / 2) :
    ∃ C : ℝ, ∀ N : ℕ, C ≤ directedCovariance (woldPowerWeight t) woldShiftedResidual N := by
  refine ⟨-(∑' n, woldPowerWeight t n * seqIncrement woldShiftedResidual n ^ 2) / 2, fun N => ?_⟩
  have hid := directedCovariance_add_half_diagonal (woldPowerWeight t) woldShiftedResidual N
  have hE := endpointEnergy_nonneg (r := woldShiftedResidual)
    (by unfold woldPowerWeight; positivity) (monotone_woldPowerWeight ht0) N
  have hQ := (incrementDiagonal_nonneg_le ht N).2
  linarith

/-- Below one half, the corrected and the raw covariance are bounded above together. -/
theorem directedCovariance_add_half_bdd_iff {t : ℝ} (ht : t < 1 / 2) :
    (∃ C : ℝ, ∀ N : ℕ, directedCovariance (woldPowerWeight t) woldShiftedResidual N +
      incrementDiagonal (woldPowerWeight t) woldShiftedResidual N / 2 ≤ C) ↔
    ∃ C : ℝ, ∀ N : ℕ, directedCovariance (woldPowerWeight t) woldShiftedResidual N ≤ C := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun N => by linarith [hC N, (incrementDiagonal_nonneg_le ht N).1]⟩
  · rintro ⟨C, hC⟩
    refine ⟨C + (∑' n, woldPowerWeight t n * seqIncrement woldShiftedResidual n ^ 2) / 2,
      fun N => ?_⟩
    linarith [hC N, (incrementDiagonal_nonneg_le ht N).2]

/-- **Route TT's raw signed covariance: its upper bound is exactly the zero-free half-plane of
matching width**; its lower bound is free (`exists_le_directedCovariance`). -/
theorem xiZeroHalfPlaneBound_iff_forall_directedCovariance_bddAbove {α : ℝ} (hα0 : 0 ≤ α)
    (hα : α < 1 / 2) :
    XiZeroHalfPlaneBound α ↔ ∀ t : ℝ, 0 < t → t < 1 / 2 - α → ∃ C : ℝ, ∀ N : ℕ,
      directedCovariance (woldPowerWeight t) woldShiftedResidual N ≤ C := by
  rw [xiZeroHalfPlaneBound_iff_forall_directedCovariance_bdd hα0 hα]
  exact forall_congr' fun t => forall_congr' fun _ => forall_congr' fun ht =>
    directedCovariance_add_half_bdd_iff (by linarith)

/-- **RH is exactly upper boundedness of TT's raw signed covariance below one half.** -/
theorem riemannHypothesis_iff_forall_directedCovariance_bddAbove :
    RiemannHypothesis ↔ ∀ t : ℝ, 0 < t → t < 1 / 2 → ∃ C : ℝ, ∀ N : ℕ,
      directedCovariance (woldPowerWeight t) woldShiftedResidual N ≤ C := by
  rw [riemannHypothesis_iff_forall_directedCovariance_bdd]
  exact forall_congr' fun t => forall_congr' fun _ => forall_congr' fun ht =>
    directedCovariance_add_half_bdd_iff ht

end
end RHTower
