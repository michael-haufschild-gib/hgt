import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheWeightedAffineShellErrorsVanishInHarmonicNorm
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheUpwardPrimeRowsHaveUniformKernelBounds

/-!
# Weighted prime shells are uniform on bounded overlap

The finite-part Abel identity has one source horizon for every smooth weight with common
flatness, height and derivative bounds. Reciprocal autocorrelation weights on a positive compact
parameter interval satisfy these bounds. Consequently the literal affine Mangoldt shells and
their full signed correction converge uniformly over bounded overlap, all affine parameters and
all shell shifts. Every prime power is retained.
-/

noncomputable section
open MeasureTheory Filter Topology Finset
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  BezoutValuationIncidence

private theorem deriv_zero_on_flat_interval {W : ℝ → ℝ} {a : ℝ}
    (hflat : ∀ u, |u| < a → W u = 0) {u : ℝ} (hu : |u| < a) : deriv W u = 0 := by
  have hlocal : W =ᶠ[𝓝 u] fun _ => 0 := by
    filter_upwards [continuous_abs.continuousAt.eventually (gt_mem_nhds hu)] with v hv
    exact hflat v hv
  exact ((hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq hlocal).deriv

/-- One source horizon controls all smooth weights with common flatness and derivative bounds,
in the full signed residue norm. -/
theorem eventually_weightedResiduePrimeReading_uniform_weights {q : ℕ} [NeZero q]
    {a B D : ℝ} (ha : 0 < a) (hB : 0 ≤ B) (hD : 0 ≤ D)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ W : ℝ → ℝ, ContDiff ℝ 1 W →
      (∀ u, |u| < a → W u = 0) → |W 1| ≤ B →
      (∀ u ∈ Set.Icc (0 : ℝ) 1, |deriv W u| ≤ D) →
      ∀ F : ZMod q → ℝ,
      |weightedResiduePrimeReading q F W X -
          primeClassKappa q F * ∫ u in (0 : ℝ)..1, W u / u| ≤
        ε * ∑ r : ZMod q, |F r| := by
  let α := min (a / 2) (1 / 2)
  have hα : 0 < α := lt_min (by positivity) (by norm_num)
  have hαa : α < a := (min_le_left _ _).trans_lt (half_lt_self ha)
  let δ := ε / (2 * (B + D + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : δ * (2 * (B + D + 1)) = ε := div_mul_cancel₀ ε (by positivity)
  have hE : ∀ᶠ Y : ℝ in atTop, ∀ r : ZMod q,
      |residuePrimeRealError q (primeResidueIndicator r) Y| < δ := by
    apply Filter.eventually_all.mpr
    intro r
    have h := (tendsto_residuePrimeRealError (primeResidueIndicator r)).abs
    simp only [abs_zero] at h
    exact h.eventually (gt_mem_nhds hδ)
  obtain ⟨Y, hY⟩ := eventually_atTop.mp hE
  let A := max 1 Y
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  filter_upwards [eventually_ge_atTop (max A (A / α))] with X hX
  intro W hW hflat hW1 hWD F
  have hXA : A ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := hA.trans_le hXA
  have hXα : A ≤ X * α := (div_le_iff₀ hα).mp ((le_max_right _ _).trans hX)
  have hsingle (r : ZMod q) :
      |weightedResiduePrimeReading q (primeResidueIndicator r) W X -
        primeClassKappa q (primeResidueIndicator r) * ∫ u in (0 : ℝ)..1, W u / u| ≤ ε := by
    have hEX : |residuePrimeRealError q (primeResidueIndicator r) X| ≤ δ :=
      (hY X ((le_max_right _ _).trans hXA) r).le
    have hpoint : ∀ u ∈ Set.uIoc (0 : ℝ) 1,
        ‖deriv W u * residuePrimeRealError q (primeResidueIndicator r) (X * u)‖ ≤ D * δ := by
      intro u hu
      rw [Set.uIoc_of_le zero_le_one] at hu
      by_cases hsmall : u < α
      · have hd0 : deriv W u = 0 := deriv_zero_on_flat_interval hflat (by
          rw [abs_of_pos hu.1]
          exact hsmall.trans hαa)
        rw [hd0, zero_mul, norm_zero]
        exact mul_nonneg hD hδ.le
      · have hXu : Y ≤ X * u := (le_max_right 1 Y).trans
          (hXα.trans (mul_le_mul_of_nonneg_left (le_of_not_gt hsmall) hX0.le))
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hWD u ⟨hu.1.le, hu.2⟩) (hY (X * u) hXu r).le (abs_nonneg _) hD
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    simp only [sub_zero, abs_one, mul_one, Real.norm_eq_abs] at hI
    rw [weightedResiduePrimeReading_sub_mean_eq (primeResidueIndicator r) hW ha hflat hX0]
    calc
      _ ≤ |W 1| * |residuePrimeRealError q (primeResidueIndicator r) X| +
          |∫ u in (0 : ℝ)..1, deriv W u * residuePrimeRealError q (primeResidueIndicator r) (X * u)| := by
        simpa only [abs_mul] using abs_sub (W 1 * residuePrimeRealError q (primeResidueIndicator r) X)
          (∫ u in (0 : ℝ)..1, deriv W u * residuePrimeRealError q (primeResidueIndicator r) (X * u))
      _ ≤ B * δ + D * δ := add_le_add (mul_le_mul hW1 hEX (abs_nonneg _) hB) hI
      _ ≤ ε := by nlinarith only [hδeq, hδ, hB, hD, hε]
  have heq : weightedResiduePrimeReading q F W X -
      primeClassKappa q F * ∫ u in (0 : ℝ)..1, W u / u =
      ∑ r : ZMod q, F r * (weightedResiduePrimeReading q (primeResidueIndicator r) W X -
        primeClassKappa q (primeResidueIndicator r) * ∫ u in (0 : ℝ)..1, W u / u) := by
    rw [weightedResiduePrimeReading_eq_indicator_sum, primeClassKappa_eq_indicator_sum,
      sum_mul, ← sum_sub_distrib]
    exact sum_congr rfl fun r _ => by ring
  rw [heq, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r _ => ?_)
  rw [abs_mul, mul_comm ε]
  exact mul_le_mul_of_nonneg_left (hsingle r) (abs_nonneg _)

/-- The derivative of a reciprocal shell weight away from its zero extension. -/
theorem deriv_reciprocalShellWeight_of_ne_zero {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (a : ℝ) {t : ℝ} (ht : t ≠ 0) :
    deriv (reciprocalShellWeight φ a) t = deriv (shellAutocorr φ) (a / t) * (-a / t ^ 2) := by
  have hi : HasDerivAt (fun u : ℝ => a / u) (-a / t ^ 2) t := by
    have h := (hasDerivAt_const t a).div (hasDerivAt_id t) ht
    change HasDerivAt (fun u : ℝ => a / u) ((0 * t - a * 1) / t ^ 2) t at h
    simpa only [zero_mul, mul_one, zero_sub] using h
  have hG := ((contDiff_shellAutocorr hφ hsupp).differentiable (by norm_num)) (a / t)
  have hcomp := hG.hasDerivAt.comp t hi
  have hlocal : reciprocalShellWeight φ a =ᶠ[𝓝 t] fun u => shellAutocorr φ (a / u) := by
    filter_upwards [eventually_ne_nhds ht] with u hu
    exact if_neg hu
  exact (hcomp.congr_of_eventuallyEq hlocal).deriv

/-- Reciprocal shell weights with parameters in a positive compact interval have common height
and derivative bounds; their zero extension supplies the same flat neighborhood. -/
theorem exists_reciprocalShellWeight_uniform_bounds {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {a₀ A : ℝ} (ha₀ : 0 < a₀) (hA : 0 ≤ A) :
    ∃ B D : ℝ, 0 ≤ B ∧ 0 ≤ D ∧ ∀ a : ℝ, a₀ ≤ a → a ≤ A →
      |reciprocalShellWeight φ a 1| ≤ B ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, |deriv (reciprocalShellWeight φ a) u| ≤ D := by
  obtain ⟨L, hLip⟩ := exists_lipschitz_shellAutocorr hφ hsupp
  let τ := a₀ / 2
  let B := (L : ℝ) * A + |shellAutocorr φ 0|
  let D := (L : ℝ) * (A / τ ^ 2)
  have hτ : 0 < τ := half_pos ha₀
  refine ⟨B, D, by dsimp only [B]; positivity, by dsimp only [D]; positivity, ?_⟩
  intro a halow haA
  have ha : 0 < a := ha₀.trans_le halow
  constructor
  · rw [reciprocalShellWeight, if_neg one_ne_zero, div_one]
    have h := hLip.dist_le_mul a 0
    simp only [Real.dist_eq, sub_zero, abs_of_pos ha] at h
    calc |shellAutocorr φ a| = |shellAutocorr φ a - shellAutocorr φ 0 + shellAutocorr φ 0| := by
          congr 1
          ring
      _ ≤ |shellAutocorr φ a - shellAutocorr φ 0| + |shellAutocorr φ 0| := abs_add_le _ _
      _ ≤ (L : ℝ) * a + |shellAutocorr φ 0| := by linarith only [h]
      _ ≤ B := by
        have hbound := mul_le_mul_of_nonneg_left haA L.coe_nonneg
        dsimp only [B]
        linarith only [hbound]
  · intro u hu
    by_cases hsmall : u < τ
    · have hd0 : deriv (reciprocalShellWeight φ a) u = 0 := deriv_zero_on_flat_interval
        (fun v hv => reciprocalShellWeight_zero_near hφ hsupp ha hv) (by
          rw [abs_of_nonneg hu.1]
          exact hsmall.trans ((half_lt_self ha₀).trans_le halow))
      rw [hd0, abs_zero]
      dsimp only [D]
      positivity
    · have hτu : τ ≤ u := le_of_not_gt hsmall
      have hu0 : 0 < u := hτ.trans_le hτu
      have hsq : τ ^ 2 ≤ u ^ 2 := by
        simpa only [pow_two] using mul_self_le_mul_self hτ.le hτu
      have hG : |deriv (shellAutocorr φ) (a / u)| ≤ (L : ℝ) := by
        simpa only [Real.norm_eq_abs] using
          (norm_deriv_le_of_lipschitz (x₀ := a / u) hLip)
      have hquot : a / u ^ 2 ≤ A / τ ^ 2 :=
        (div_le_div_of_nonneg_right haA (sq_nonneg u)).trans
          (div_le_div_of_nonneg_left hA (sq_pos_of_pos hτ) hsq)
      rw [deriv_reciprocalShellWeight_of_ne_zero hφ hsupp a hu0.ne', abs_mul, abs_div,
        abs_neg, abs_of_pos ha, abs_of_nonneg (sq_nonneg u)]
      exact mul_le_mul hG hquot (div_nonneg ha.le (sq_nonneg u)) L.coe_nonneg

/-- The actual affine prime source is uniform over the whole reciprocal-weight interval,
including arbitrary moving multipliers and shifts. -/
theorem eventually_weightedAffinePrimeReading_uniform_reciprocal {q : ℕ} (hq : 0 < q)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {a₀ A : ℝ} (ha₀ : 0 < a₀) (hA : 0 ≤ A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ a : ℝ, a₀ ≤ a → a ≤ A → ∀ n b : ℕ,
      |weightedAffineRamanujanPrimeReading q n b (reciprocalShellWeight φ a) X -
        (ramanujanLagCoefficient q n * ramanujanLagCoefficient q b / (q.totient : ℝ)) *
          ∫ u in a..1, shellAutocorr φ u / u| ≤ ε := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have htot : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  obtain ⟨B, D, hB, hD, hbounds⟩ := exists_reciprocalShellWeight_uniform_bounds hφ hsupp ha₀ hA
  have hlim := eventually_weightedResiduePrimeReading_uniform_weights (q := q)
    ha₀ hB hD (div_pos hε (mul_pos hqR htot))
  filter_upwards [hlim] with X hX
  intro a halow haA n b
  have ha : 0 < a := ha₀.trans_le halow
  have hw := (contDiff_reciprocalShellWeight hφ hsupp ha).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hb := hX (reciprocalShellWeight φ a) hw
    (fun u hu => reciprocalShellWeight_zero_near hφ hsupp ha (hu.trans_le halow))
    (hbounds a halow haA).1 (hbounds a halow haA).2 (affineRamanujanResidue q n b)
  rw [← weightedAffineRamanujanPrimeReading_eq_residue,
    primeClassKappa_affineRamanujanResidue, integral_reciprocalShellWeight hφ hsupp ha] at hb
  have hresidue : (∑ r : ZMod q, |affineRamanujanResidue q n b r|) ≤ (q : ℝ) * q.totient := by
    have h := sum_le_sum (s := (univ : Finset (ZMod q))) fun r _ =>
      BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient q (r.val * n + b)
    simpa only [affineRamanujanResidue, sum_const, card_univ, ZMod.card, nsmul_eq_mul] using h
  refine hb.trans ?_
  calc (ε / ((q : ℝ) * q.totient)) * ∑ r : ZMod q, |affineRamanujanResidue q n b r|
      ≤ (ε / ((q : ℝ) * q.totient)) * ((q : ℝ) * q.totient) :=
        mul_le_mul_of_nonneg_left hresidue (div_nonneg hε.le (mul_nonneg hqR.le htot.le))
    _ = ε := div_mul_cancel₀ ε (mul_pos hqR htot).ne'

/-- One real horizon controls every bounded-overlap shell and both affine parameters. -/
theorem eventually_affineRamanujanPrimeShell_uniform_overlap {q : ℕ} (hq : 0 < q)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {K : ℝ} (hK : 0 < K) (H : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K → ∀ h : ℕ, 1 ≤ h → h ≤ H → ∀ n b : ℕ,
      |affineRamanujanPrimeShell q n b φ c h X -
        (ramanujanLagCoefficient q n * ramanujanLagCoefficient q b / (q.totient : ℝ)) *
          ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u| ≤ ε := by
  have hlim := eventually_weightedAffinePrimeReading_uniform_reciprocal hq hφ hsupp
    (one_div_pos.mpr hK) (Nat.cast_nonneg H) hε
  filter_upwards [hlim, eventually_gt_atTop (0 : ℝ)] with X hX hX0
  intro c hc1 hcK h hh hH n b
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hlow : 1 / K ≤ (h : ℝ) / c := by
    calc 1 / K ≤ 1 / c := one_div_le_one_div_of_le hc hcK
      _ ≤ (h : ℝ) / c := div_le_div_of_nonneg_right hhR hc.le
  have hhigh : (h : ℝ) / c ≤ H := by
    exact (div_le_self (Nat.cast_nonneg h) hc1).trans (by exact_mod_cast hH)
  rw [affineRamanujanPrimeShell_eq_weighted q n b φ hc h hX0]
  exact hX (h / c) hlow hhigh n b

/-- The full signed shell correction has one horizon on every bounded overlap interval,
uniformly over all mode indices and every choice of shell shifts. -/
theorem eventually_affinePrimeShellCorrectionOfShift_uniform_overlap {q : ℕ} (hq : 0 < q)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {K : ℝ} (hK : 0 < K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K → ∀ shift : ℕ → ℕ, ∀ n : ℕ,
      |affinePrimeShellCorrectionOfShift q n shift φ c X -
        ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift| ≤ ε := by
  let H : ℕ := ⌈K⌉₊
  let A := 2 / (∫ u, φ u ^ 2)
  let δ := ε / (|A| * H + 1)
  have hden : 0 < |A| * (H : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hδeq : δ * (|A| * H + 1) = ε := div_mul_cancel₀ ε hden.ne'
  filter_upwards [eventually_affineRamanujanPrimeShell_uniform_overlap hq hφ hsupp hK H hδ]
    with X hX
  intro c hc1 hcK shift n
  let S := Ico 1 ⌈c⌉₊
  have hceil : ⌈c⌉₊ ≤ H := Nat.ceil_mono hcK
  have hmem : ∀ h ∈ S, 1 ≤ h ∧ h ≤ H := by
    intro h hh
    have hh' := mem_Ico.mp hh
    exact ⟨hh'.1, hh'.2.le.trans hceil⟩
  have hcard : (S.card : ℝ) ≤ H := by
    have hnat : S.card ≤ H := by
      dsimp only [S]
      rw [Nat.card_Ico]
      omega
    exact_mod_cast hnat
  have heq : affinePrimeShellCorrectionOfShift q n shift φ c X -
      ramanujanLagCoefficient q n * shellCorrectionOfShift φ c q shift =
      A * ∑ h ∈ S, (affineRamanujanPrimeShell q n (shift h) φ c h X -
        (ramanujanLagCoefficient q n * ramanujanLagCoefficient q (shift h) / (q.totient : ℝ)) *
          ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u) := by
    simp only [affinePrimeShellCorrectionOfShift, shellCorrectionOfShift, S, A, sum_sub_distrib,
      mul_sub, mul_sum, div_eq_mul_inv, mul_inv_rev]
    congr 1
    exact sum_congr rfl fun h _ => by ring
  rw [heq, abs_mul]
  calc
    _ ≤ |A| * ∑ h ∈ S, |affineRamanujanPrimeShell q n (shift h) φ c h X -
        (ramanujanLagCoefficient q n * ramanujanLagCoefficient q (shift h) / (q.totient : ℝ)) *
          ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u| :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (abs_nonneg _)
    _ ≤ |A| * ∑ _h ∈ S, δ := mul_le_mul_of_nonneg_left
      (sum_le_sum fun h hh => hX c hc1 hcK h (hmem h hh).1 (hmem h hh).2 n (shift h))
      (abs_nonneg _)
    _ ≤ |A| * ((H : ℝ) * δ) := by
      rw [sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hδ.le) (abs_nonneg _)
    _ ≤ ε := by nlinarith only [hδeq, hδ]

open SpacingScaleHarmonicAnalysis in
/-- The explicit spline's actual shell source has one horizon for every bounded overlap,
all mode indices and all reflected or positive shell shifts. -/
theorem eventually_tiltedUnitSpline_affineShellCorrection_uniform_overlap {q : ℕ} (hq : 0 < q)
    {K : ℝ} (hK : 0 < K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K → ∀ shift : ℕ → ℕ, ∀ n : ℕ,
      |affinePrimeShellCorrectionOfShift q n shift tiltedUnitSpline c X -
        ramanujanLagCoefficient q n * shellCorrectionOfShift tiltedUnitSpline c q shift| ≤ ε :=
  eventually_affinePrimeShellCorrectionOfShift_uniform_overlap hq contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero hK hε

#print axioms eventually_weightedResiduePrimeReading_uniform_weights
#print axioms eventually_affineRamanujanPrimeShell_uniform_overlap
#print axioms eventually_affinePrimeShellCorrectionOfShift_uniform_overlap
#print axioms eventually_tiltedUnitSpline_affineShellCorrection_uniform_overlap

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
