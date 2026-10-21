import GaloisForLFunctions.ArithmeticIncidencePositivity.OddFoldCrossingPotentialAtEveryAperture
import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeAtomEvenPartPotential
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShortProfilePoleFreeVariationInequality

/-!
# The global incidence allocation condition

For an odd test `F ∈ C²_c` supported in `[−r, r]` and a plateau radius `R > r`, with the plateau
`P = aperturePlateau r R` (`1` on `[−r, r]`, `0` outside `(−R, R)`), the full zero form of `F` is
exactly the **incidence ledger** (`fullZeroForm_eq_incidenceLedger`):

    Ẑ(F) = surplusPool + crossingPotentialTerm + Σ_n evenStripGain_n − Σ_n oddStripCost_n
           + gaugeRemainder − poleCharge,

with the sum over the **relevant shifts** `n ≥ 2`, `log n < 2r` (`relevantShifts r`), the only
prime-power shifts at which the test meets its own translate. The six components are:

* `surplusPool P F = 2 S_P(F)`: the archimedean surplus of all same-side pairs, the only pool a
  strip allocation can draw on (`stripBoxEnergy`, `sum_primeStripCharge_le_union`);
* `crossingPotentialTerm P F = 4 ∫_{x>0} F(x)² Π_P(x)`: the crossing pairs folded onto the point `x`,
  the killing `Ω(x) − Ω(x + r)` of the plateau plus the axial collar potential of the gauge beyond
  `r` (`crossingPotential_eq_killing_add_collar`);
* `evenStripGain F r n = 2 Λ(n)/√n ∫_{S_n} F²`: the favorable component of the atom of `n`, carried
  by the part of `F` even about `½ log n` on the strip `S_n = [log n − r, r]`;
* `oddStripCost F r n = 4 Λ(n)/√n ∫_{S_n} α_n²`: the charge of the atom of `n`, carried by the odd
  part `α_n` of `F` about `½ log n`;
* `gaugeRemainder P F = ∫ F² P (−𝒲P + prime part)`: the plateau potential with the prime part
  returned, bounded below pointwise by `Ω(R − x) + Ω(R + x) − 2E(0) − (γ + log π)`
  (`neg_poleFreeWeilOperator_add_primeSum_ge`);
* `poleCharge F = 2 (∫ F sinh(x/2))²`: the odd pole moment.

The pool, the crossing potential, the favorable components, the costs and the pole are
nonnegative; the gauge remainder is the only signed piece. The **global incidence allocation
condition** `GlobalIncidenceAllocation r R F` says that the costs and the pole are paid by the pool,
the crossing potential, the favorable components and the remainder. By the ledger it is equivalent,
test by test, to `Ẑ(F) ≥ 0` (`globalIncidenceAllocation_iff_fullZeroForm_nonneg`), so

    RH ⟺ every odd compact test satisfies the condition at every aperture and plateau

(`riemannHypothesis_iff_globalIncidenceAllocation`), through the odd Weil positivity
`RH ⟺ Ẑ ≥ 0 on odd tests` (`riemannHypothesis_iff_forall_odd_fullZeroForm_nonneg`). The plateau
radius is free: one plateau per test suffices
(`riemannHypothesis_iff_exists_plateau_globalIncidenceAllocation`).

Every window theorem of the programme is an instance of the condition at its aperture: the sharp
micro-fold pays `oddStripCost` from a share of the pool, the even part is `evenStripGain`, and the
certificates bound the gauge remainder with the crossing potential and the pole.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### The relevant prime-power shifts of an aperture -/

/-- The relevant shifts of the aperture `r`: the integers `n ≥ 2` with `log n < 2r`, the only
shifts at which a test supported in `[−r, r]` meets its own translate. -/
def relevantShifts (r : ℝ) : Finset ℕ :=
  (Finset.range ⌈Real.exp (2 * r)⌉₊).filter fun n => 2 ≤ n ∧ Real.log n < 2 * r

theorem mem_relevantShifts {r : ℝ} {n : ℕ} :
    n ∈ relevantShifts r ↔ 2 ≤ n ∧ Real.log n < 2 * r := by
  simp only [relevantShifts, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [Nat.lt_ceil]
    have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact (Real.log_lt_iff_lt_exp hn).mp h.2

theorem relevantShifts_mono {r R : ℝ} (h : r ≤ R) : relevantShifts r ⊆ relevantShifts R :=
  fun n hn => by
    rw [mem_relevantShifts] at hn ⊢
    exact ⟨hn.1, by linarith [hn.2]⟩

/-! ### The components of the ledger -/

/-- The odd strip cost of the shift `n`: `4 Λ(n)/√n ∫_{S_n} α_n²` on the strip
`S_n = [log n − r, r]`, `α_n` the part of `F` odd about `½ log n`. -/
def oddStripCost (F : ℝ → ℝ) (r : ℝ) (n : ℕ) : ℝ :=
  4 * vonMangoldtAtom n * ∫ a in (Real.log n - r)..r, reflectedOddPart F (Real.log n) a ^ 2

/-- The favorable even component of the shift `n`: `2 Λ(n)/√n ∫_{S_n} F²`. -/
def evenStripGain (F : ℝ → ℝ) (r : ℝ) (n : ℕ) : ℝ :=
  2 * vonMangoldtAtom n * ∫ a in (Real.log n - r)..r, F a ^ 2

/-- The surplus pool `2 S_P(F)` of all same-side pairs. -/
def surplusPool (P F : ℝ → ℝ) : ℝ := 2 * surplusEnergy P F

/-- The crossing potential term `4 ∫_{x>0} F(x)² Π_P(x) dx`: killing plus axial collars. -/
def crossingPotentialTerm (P F : ℝ → ℝ) : ℝ :=
  4 * ∫ x in Ioi (0 : ℝ), F x ^ 2 * crossingPotential P x

/-- The gauge remainder `∫ F² P (−𝒲P + prime part)`: the plateau potential with the prime part
returned. -/
def gaugeRemainder (P F : ℝ → ℝ) : ℝ :=
  ∫ x, F x ^ 2 * P x * (-poleFreeWeilOperator P x + profilePrimeSum P x)

/-- The pole charge `2 (∫ F sinh(x/2))²` of an odd test. -/
def poleCharge (F : ℝ → ℝ) : ℝ := 2 * oddPoleMoment F ^ 2

/-- The plateau of the aperture `r` with radius `R`: `1` on `[−r, r]`, `0` outside `(−R, R)`. -/
def aperturePlateau (r R : ℝ) : ℝ → ℝ := plateauGauge R (R - r)

/-- **The global incidence allocation condition** at aperture `r` and plateau radius `R`: the odd
strip costs of every relevant shift and the pole are paid by the surplus pool, the crossing
potential, the favorable components and the gauge remainder. -/
def GlobalIncidenceAllocation (r R : ℝ) (F : ℝ → ℝ) : Prop :=
  (∑ n ∈ relevantShifts r, oddStripCost F r n) + poleCharge F ≤
    surplusPool (aperturePlateau r R) F + crossingPotentialTerm (aperturePlateau r R) F +
      (∑ n ∈ relevantShifts r, evenStripGain F r n) + gaugeRemainder (aperturePlateau r R) F

/-! ### Signs of the components -/

theorem surplusEnergy_nonneg {P F : ℝ → ℝ} (hP0 : ∀ x, 0 ≤ P x) : 0 ≤ surplusEnergy P F := by
  unfold surplusEnergy
  refine setIntegral_nonneg measurableSet_Ioi fun x hx => ?_
  refine setIntegral_nonneg measurableSet_Ioi fun s hs => ?_
  have hx0 : 0 < x := hx
  have hs0 : 0 < s := hs
  refine mul_nonneg ?_ (signedShiftJump_nonneg' hP0 s x)
  linarith [strictAntiOn_archLevyDensity.antitoneOn hs0 (show (0 : ℝ) < s + 2 * x by linarith)
    (by linarith)]

theorem surplusPool_nonneg {P F : ℝ → ℝ} (hP0 : ∀ x, 0 ≤ P x) : 0 ≤ surplusPool P F := by
  unfold surplusPool; linarith [surplusEnergy_nonneg (F := F) hP0]

theorem crossingPotential_nonneg {P : ℝ → ℝ} (hP0 : ∀ x, 0 ≤ P x) {x : ℝ} (hx : 0 < x) :
    0 ≤ crossingPotential P x :=
  setIntegral_nonneg measurableSet_Ioi fun t ht =>
    mul_nonneg (archLevyDensity_pos (lt_trans hx ht)).le (hP0 (t - x))

theorem crossingPotentialTerm_nonneg {P F : ℝ → ℝ} (hP0 : ∀ x, 0 ≤ P x) :
    0 ≤ crossingPotentialTerm P F := by
  unfold crossingPotentialTerm
  refine mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioi fun x hx => ?_)
  exact mul_nonneg (sq_nonneg _) (crossingPotential_nonneg hP0 hx)

theorem oddStripCost_nonneg (F : ℝ → ℝ) {r : ℝ} {n : ℕ} (h : Real.log n - r ≤ r) :
    0 ≤ oddStripCost F r n := by
  unfold oddStripCost
  exact mul_nonneg (mul_nonneg (by norm_num) (vonMangoldtAtom_nonneg n))
    (intervalIntegral.integral_nonneg h fun _ _ => sq_nonneg _)

theorem evenStripGain_nonneg (F : ℝ → ℝ) {r : ℝ} {n : ℕ} (h : Real.log n - r ≤ r) :
    0 ≤ evenStripGain F r n := by
  unfold evenStripGain
  exact mul_nonneg (mul_nonneg (by norm_num) (vonMangoldtAtom_nonneg n))
    (intervalIntegral.integral_nonneg h fun _ _ => sq_nonneg _)

theorem poleCharge_nonneg (F : ℝ → ℝ) : 0 ≤ poleCharge F := by
  unfold poleCharge; positivity

/-- On the relevant shifts every strip has positive length, so costs and gains are nonnegative. -/
theorem sum_oddStripCost_nonneg (F : ℝ → ℝ) (r : ℝ) :
    0 ≤ ∑ n ∈ relevantShifts r, oddStripCost F r n :=
  Finset.sum_nonneg fun n hn => oddStripCost_nonneg F (by linarith [(mem_relevantShifts.mp hn).2])

theorem sum_evenStripGain_nonneg (F : ℝ → ℝ) (r : ℝ) :
    0 ≤ ∑ n ∈ relevantShifts r, evenStripGain F r n :=
  Finset.sum_nonneg fun n hn => evenStripGain_nonneg F (by linarith [(mem_relevantShifts.mp hn).2])

/-! ### The ledger identity -/

/-- A continuous function vanishing for `r < |x|` vanishes at `r`. -/
theorem eq_zero_at_support_radius {F : ℝ → ℝ} {r : ℝ} (hF : Continuous F) (hr : 0 < r)
    (hsupp : ∀ x, r < |x| → F x = 0) : F r = 0 := by
  have h1 : Tendsto F (𝓝[>] r) (𝓝 (F r)) := hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto F (𝓝[>] r) (𝓝 0) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun x hx =>
      (hsupp x (by rw [abs_of_pos (by linarith [mem_Ioi.mp hx])]; exact hx)).symm)
  exact tendsto_nhds_unique h1 h2

/-- A shift `log n ≥ 2r` meets no translate of a test supported in `[−r, r]`. -/
theorem integral_mul_shift_eq_zero_of_two_mul_le {F : ℝ → ℝ} {r L : ℝ} (hF : Continuous F)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) (hL : 2 * r ≤ L) :
    (∫ x, F x * F (x + L)) = 0 := by
  have hFr0 := eq_zero_at_support_radius hF hr hsupp
  refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
  simp only [Pi.zero_apply]
  by_cases hx : F x = 0
  · rw [hx, zero_mul]
  · have hxr : |x| ≤ r := by
      by_contra h
      exact hx (hsupp x (not_le.mp h))
    have hx1 := neg_abs_le x
    rcases lt_or_eq_of_le (show r ≤ x + L by linarith) with h | h
    · rw [hsupp (x + L) (by rw [abs_of_pos (by linarith)]; exact h), mul_zero]
    · rw [← h, hFr0, mul_zero]

/-- **The incidence ledger of the odd zero form at every aperture.** For an odd `F ∈ C²_c`
supported in `[−r, r]`, `r > 0`, and every plateau radius `R > r`:
`Ẑ(F) = surplusPool + crossingPotentialTerm + Σ evenStripGain − Σ oddStripCost + gaugeRemainder
− poleCharge`, the sums over the relevant shifts of `r`. -/
theorem fullZeroForm_eq_incidenceLedger {F : ℝ → ℝ} {r R : ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x) (hr : 0 < r)
    (hsupp : ∀ x, r < |x| → F x = 0) (hrR : r < R) :
    fullZeroForm F =
      surplusPool (aperturePlateau r R) F + crossingPotentialTerm (aperturePlateau r R) F +
        (∑ n ∈ relevantShifts r, evenStripGain F r n) -
        (∑ n ∈ relevantShifts r, oddStripCost F r n) +
        gaugeRemainder (aperturePlateau r R) F - poleCharge F := by
  set P := aperturePlateau r R with hPdef
  have hδ : 0 < R - r := by linarith
  have hPd : ContDiff ℝ 2 P := by rw [hPdef]; exact contDiff_plateauGauge R (R - r)
  have hPcs : HasCompactSupport P := by rw [hPdef]; exact hasCompactSupport_plateauGauge hδ
  have hP0 : ∀ y, 0 ≤ P y := fun y => by rw [hPdef]; exact plateauGauge_nonneg R (R - r) y
  have hP1 : ∀ y, P y ≤ 1 := fun y => by rw [hPdef]; exact plateauGauge_le_one R (R - r) y
  have hPB : ∀ y, R ≤ |y| → P y = 0 := fun y hy => by
    rw [hPdef]; exact plateauGauge_eq_zero hδ hy
  have hPr : ∀ y, |y| ≤ r → P y = 1 := fun y hy => by
    rw [hPdef]; exact plateauGauge_eq_one hδ (by linarith)
  have hPe : ∀ y, P (-y) = P y := fun y => by
    simp only [hPdef, aperturePlateau, plateauGauge, sub_neg_eq_add, ← sub_eq_add_neg]
    ring
  have hFr : ∀ x, F x ≠ 0 → |x| ≤ r := fun x hx => by
    by_contra h
    exact hx (hsupp x (not_le.mp h))
  have hFM : ∀ x, F x ≠ 0 → P x = 1 := fun x hx => hPr x (hFr x hx)
  have hFB : ∀ x, R ≤ |x| → F x = 0 := fun x hx => hsupp x (by linarith)
  obtain ⟨KF, -, hKF⟩ := exists_lipschitz_bound_of_compactSupport (hF.of_le (by norm_num)) hFc
  have hFL : ∀ a b, |F a - F b| ≤ KF * |a - b| := fun a b => hKF b a
  obtain ⟨KM, -, hKM⟩ := exists_lipschitz_bound_of_compactSupport (hPd.of_le (by norm_num)) hPcs
  have hPL : ∀ a b, |P a - P b| ≤ KM * |a - b| := fun a b => hKM b a
  have hR0 : 0 < R := by linarith
  -- the Markov energy in the plateau gauge
  have hZ : fullZeroForm F = markovEnergy (fun x => (F x : ℂ)) - 2 * oddPoleMoment F ^ 2 := by
    unfold fullZeroForm
    rw [evenPoleMoment_eq_zero_of_odd hodd]
    ring
  have hQ := markovEnergy_eq_gauge_window hF hFc hPd hPcs hP1 hP0 hPB hFM
  -- the prime jumps reduce to the shifts below `2R`
  have hJ : signedJumpEnergy P F =
      (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P F t) +
        ∑ n ∈ relevantShifts R, vonMangoldtAtom n * gaugeJumpProfile P F (Real.log n) := by
    unfold signedJumpEnergy
    congr 1
    refine tsum_eq_sum fun n hn => ?_
    rw [mem_relevantShifts, not_and_or, not_le, not_lt] at hn
    rcases hn with h2 | h2
    · unfold vonMangoldtAtom; rw [if_neg (by omega), zero_mul]
    · rw [show (∫ x, signedShiftJump P F (Real.log n) x) = gaugeJumpProfile P F (Real.log n) from rfl,
        gaugeJumpProfile_eq_zero_of_ge hPB h2, mul_zero]
  -- the prime part of the potential on the support
  have hprimeSum : ∀ x, |x| ≤ r → profilePrimeSum P x =
      ∑ n ∈ relevantShifts R, vonMangoldtAtom n * (P (x + Real.log n) + P (x - Real.log n)) := by
    intro x hx
    unfold profilePrimeSum
    refine tsum_eq_sum fun n hn => ?_
    rw [mem_relevantShifts, not_and_or, not_le, not_lt] at hn
    rcases hn with h2 | h2
    · unfold vonMangoldtAtom; rw [if_neg (by omega), zero_mul]
    · have hx1 := le_abs_self x
      have hx2 := neg_abs_le x
      rw [hPB (x + Real.log n) ?_, hPB (x - Real.log n) ?_, add_zero, mul_zero]
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
  -- the gauge remainder split into its archimedean and prime parts
  have hdec8 : ∀ y, |P y| ≤ Real.exp (8 * R) * Real.exp (-(8 * |y|)) := by
    intro y
    by_cases hy : |y| < R
    · rw [abs_of_nonneg (hP0 y), ← Real.exp_add]
      exact (hP1 y).trans (Real.one_le_exp (by nlinarith))
    · rw [hPB y (not_lt.mp hy), abs_zero]
      positivity
  have hW : Continuous fun x => -poleFreeWeilOperator P x :=
    (continuous_poleFreeWeilOperator hPd.continuous hPL hdec8).neg
  have hGi : Integrable fun x => F x ^ 2 * P x * -poleFreeWeilOperator P x :=
    (((hF.continuous.pow 2).mul hPd.continuous).mul hW).integrable_of_hasCompactSupport
      ((hasCompactSupport_sq hFc).mul_right.mul_right)
  have hPri : ∀ n : ℕ, Integrable fun x =>
      F x ^ 2 * P x * (P (x + Real.log n) + P (x - Real.log n)) := fun n =>
    ((((hF.continuous.pow 2).mul hPd.continuous).mul
      ((hPd.continuous.comp (continuous_id.add continuous_const)).add
        (hPd.continuous.comp (continuous_id.sub continuous_const))))).integrable_of_hasCompactSupport
      ((hasCompactSupport_sq hFc).mul_right.mul_right)
  have hSumi : Integrable fun x => ∑ n ∈ relevantShifts R,
      vonMangoldtAtom n * (F x ^ 2 * P x * (P (x + Real.log n) + P (x - Real.log n))) :=
    integrable_finset_sum _ fun n _ => (hPri n).const_mul _
  have hGR : gaugeRemainder P F =
      (∫ x, F x ^ 2 * P x * -poleFreeWeilOperator P x) +
        ∑ n ∈ relevantShifts R, vonMangoldtAtom n *
          ∫ x, F x ^ 2 * P x * (P (x + Real.log n) + P (x - Real.log n)) := by
    unfold gaugeRemainder
    have hpt : ∀ x, F x ^ 2 * P x * (-poleFreeWeilOperator P x + profilePrimeSum P x) =
        F x ^ 2 * P x * -poleFreeWeilOperator P x + ∑ n ∈ relevantShifts R,
          vonMangoldtAtom n * (F x ^ 2 * P x * (P (x + Real.log n) + P (x - Real.log n))) := by
      intro x
      by_cases h : F x = 0
      · simp [h]
      · rw [hprimeSum x (hFr x h), mul_add, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun n _ => by ring
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_add hGi hSumi, integral_finsetSum _
      fun n _ => (hPri n).const_mul _]
    congr 1
    exact Finset.sum_congr rfl fun n _ => integral_const_mul _ _
  -- each prime jump minus its potential is the autocorrelation at the shift
  have hprime : ∀ n : ℕ, vonMangoldtAtom n * gaugeJumpProfile P F (Real.log n) -
      vonMangoldtAtom n * ∫ x, F x ^ 2 * P x * (P (x + Real.log n) + P (x - Real.log n)) =
      -2 * (vonMangoldtAtom n * ∫ x, F x * F (x + Real.log n)) := fun n => by
    rw [← mul_sub, gaugeJumpProfile_sub_primePotential_eq hPd.continuous hF.continuous hFc hFM
      (Real.log n)]
    ring
  -- the shifts between `2r` and `2R` contribute nothing; those below `2r` split even/odd
  have hsum : ∑ n ∈ relevantShifts R, (vonMangoldtAtom n * gaugeJumpProfile P F (Real.log n) -
      vonMangoldtAtom n * ∫ x, F x ^ 2 * P x * (P (x + Real.log n) + P (x - Real.log n))) =
      (∑ n ∈ relevantShifts r, evenStripGain F r n) - ∑ n ∈ relevantShifts r, oddStripCost F r n := by
    have h1 : ∑ n ∈ relevantShifts r, (vonMangoldtAtom n * gaugeJumpProfile P F (Real.log n) -
        vonMangoldtAtom n * ∫ x, F x ^ 2 * P x * (P (x + Real.log n) + P (x - Real.log n))) =
        ∑ n ∈ relevantShifts R, (vonMangoldtAtom n * gaugeJumpProfile P F (Real.log n) -
        vonMangoldtAtom n * ∫ x, F x ^ 2 * P x * (P (x + Real.log n) + P (x - Real.log n))) := by
      refine Finset.sum_subset (relevantShifts_mono hrR.le) fun n hnR hnr => ?_
      rw [mem_relevantShifts] at hnR
      rw [mem_relevantShifts, not_and_or, not_lt] at hnr
      have hL : 2 * r ≤ Real.log n := by
        rcases hnr with h | h
        · exact absurd hnR.1 h
        · exact h
      rw [hprime n, integral_mul_shift_eq_zero_of_two_mul_le hF.continuous hr hsupp hL]
      ring
    rw [← h1, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [mem_relevantShifts] at hn
    rw [hprime n, integral_mul_shift_eq_two_reflectedOdd_sub hF.continuous hodd hr.le
      (by linarith [hn.2]) hsupp]
    unfold evenStripGain oddStripCost
    ring
  -- the archimedean fold at this aperture
  have hfold := archJump_eq_two_mul_surplus_add_crossingPotential hPd.continuous hF.continuous hPe
    hodd hP0 hP1 hPB hFB hFL hR0 hFM
  have hsum' := hsum
  rw [Finset.sum_sub_distrib] at hsum'
  unfold surplusPool crossingPotentialTerm poleCharge
  rw [hZ, hQ, hJ, hGR, hfold.2]
  linarith

/-! ### The condition is the sign of the form, test by test -/

/-- **The allocation condition is the positivity of the form.** For an odd `F ∈ C²_c` supported in
`[−r, r]`, `r > 0`, and every plateau radius `R > r`:
`GlobalIncidenceAllocation r R F ↔ 0 ≤ Ẑ(F)`. -/
theorem globalIncidenceAllocation_iff_fullZeroForm_nonneg {F : ℝ → ℝ} {r R : ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x) (hr : 0 < r)
    (hsupp : ∀ x, r < |x| → F x = 0) (hrR : r < R) :
    GlobalIncidenceAllocation r R F ↔ 0 ≤ fullZeroForm F := by
  rw [fullZeroForm_eq_incidenceLedger hF hFc hodd hr hsupp hrR]
  unfold GlobalIncidenceAllocation
  constructor <;> intro h <;> linarith

/-! ### Transfer to odd Weil positivity and to RH -/

/-- **RH is the positivity of the full zero form on odd compact tests.** -/
theorem riemannHypothesis_iff_forall_odd_fullZeroForm_nonneg :
    RiemannHypothesis ↔ ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → 0 ≤ fullZeroForm F := by
  constructor
  · intro hRH F hF hFc _
    have h := riemannHypothesis_iff_forall_fullZeroForm_nonneg.mp hRH (phiDoobInv F)
      (contDiff_phiDoobInv hF) (hasCompactSupport_phiDoobInv hFc)
    rwa [show phiDoobTest (phiDoobInv F) = F from funext (phiDoobTest_phiDoobInv F)] at h
  · intro h
    refine riemannHypothesis_iff_forall_odd_zeroForm_nonneg.mpr fun v hv hvc hodd => ?_
    rw [zeroForm_eq_fullZeroForm_of_odd (phiDoobTest_odd hodd)]
    exact h _ (contDiff_phiDoobTest hv) (hasCompactSupport_phiDoobTest hvc) (phiDoobTest_odd hodd)

/-- **Transfer.** Odd Weil positivity on all compact tests is the global incidence allocation
condition at every aperture `r > 0`, every plateau radius `R > r` and every odd test supported in
`[−r, r]`. -/
theorem forall_odd_fullZeroForm_nonneg_iff_globalIncidenceAllocation :
    (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, F (-x) = -F x) →
        0 ≤ fullZeroForm F) ↔
      ∀ (r R : ℝ) (F : ℝ → ℝ), 0 < r → r < R → ContDiff ℝ 2 F → HasCompactSupport F →
        (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) → GlobalIncidenceAllocation r R F := by
  constructor
  · intro h r R F hr hrR hF hFc hodd hsupp
    exact (globalIncidenceAllocation_iff_fullZeroForm_nonneg hF hFc hodd hr hsupp hrR).mpr
      (h F hF hFc hodd)
  · intro h F hF hFc hodd
    obtain ⟨r, hr1, hsupp⟩ :=
      GaloisForLFunctions.ArithmeticCriticalityTheory.exists_support_radius hFc
    exact (globalIncidenceAllocation_iff_fullZeroForm_nonneg hF hFc hodd (by linarith) hsupp
      (by linarith : r < r + 1)).mp (h r (r + 1) F (by linarith) (by linarith) hF hFc hodd hsupp)

/-- **RH is the global incidence allocation condition** at every aperture and plateau radius, for
every odd compact test. -/
theorem riemannHypothesis_iff_globalIncidenceAllocation :
    RiemannHypothesis ↔
      ∀ (r R : ℝ) (F : ℝ → ℝ), 0 < r → r < R → ContDiff ℝ 2 F → HasCompactSupport F →
        (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) → GlobalIncidenceAllocation r R F :=
  riemannHypothesis_iff_forall_odd_fullZeroForm_nonneg.trans
    forall_odd_fullZeroForm_nonneg_iff_globalIncidenceAllocation

/-- The plateau radius is free: RH holds iff every odd test at every aperture satisfies the
condition for some plateau radius. -/
theorem riemannHypothesis_iff_exists_plateau_globalIncidenceAllocation :
    RiemannHypothesis ↔
      ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r → ContDiff ℝ 2 F → HasCompactSupport F →
        (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
          ∃ R, r < R ∧ GlobalIncidenceAllocation r R F := by
  rw [riemannHypothesis_iff_globalIncidenceAllocation]
  constructor
  · intro h r F hr hF hFc hodd hsupp
    exact ⟨r + 1, by linarith, h r (r + 1) F hr (by linarith) hF hFc hodd hsupp⟩
  · intro h r R F hr hrR hF hFc hodd hsupp
    obtain ⟨R', hR', hGIA⟩ := h r F hr hF hFc hodd hsupp
    rw [globalIncidenceAllocation_iff_fullZeroForm_nonneg hF hFc hodd hr hsupp hR'] at hGIA
    exact (globalIncidenceAllocation_iff_fullZeroForm_nonneg hF hFc hodd hr hsupp hrR).mpr hGIA

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
