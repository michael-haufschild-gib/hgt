import GaloisForLFunctions.RHTower.CCM.CCMCompletedPrimeGammaAccretivityCriterion
import GaloisForLFunctions.RHTower.PrimeArchSourceUpperBoundGate

/-!
# A local lower-bound gate for the completed prime--Gamma source

The global finite-bound source criterion can be weakened to a purely local condition.  Around
every point of the open left half of the critical strip, require only some finite lower bound for
the real completed prime--Gamma flux on nearby regular points.  There is no common bound, growth
rate, tail, or sign requirement.

A reflected off-line Xi zero violates this condition in its own neighborhood: along a rightward
approach the negative Xi logarithmic derivative tends to negative infinity with its full positive
multiplicity.  Conversely RH supplies the sharper global lower bound zero by completed
prime--Gamma accretivity.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- Pointwise local lower boundedness of the real completed prime--Gamma flux throughout the open
left half of the critical strip.  The radius and lower bound may depend on the center. -/
def CompletedPrimeGammaLeftHalfLocallyBoundedBelow : Prop :=
  ∀ sigma : ℂ, 0 < sigma.re → sigma.re < 1 / 2 →
    ∃ r : ℝ, 0 < r ∧ ∃ L : ℝ, ∀ s : ℂ,
      dist s sigma < r → 0 < s.re → s.re < 1 / 2 →
        riemannZeta s ≠ 0 → L ≤ (completedPrimeGammaFlux s).re

/-- Local lower boundedness excludes every off-line zero and proves RH.  Only the neighborhood of
the reflected hypothetical zero is used. -/
theorem riemannHypothesis_of_completedPrimeGammaLeftHalfLocallyBoundedBelow
    (hlocal : CompletedPrimeGammaLeftHalfLocallyBoundedBelow) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  have hrhoGt : 1 / 2 < rho.re := mem_rightHalf.mp hrho
  have hrhoPos : 0 < rho.re := lt_trans (by norm_num) hrhoGt
  have hrhoLt : rho.re < 1 := xi_zero_re_lt_one hzero
  let sigma : ℂ := 1 - rho
  have hsigmaZero : xi sigma = 0 := by
    dsimp only [sigma]
    rw [xi_one_sub, hzero]
  have hsigmaPos : 0 < sigma.re := by
    dsimp only [sigma]
    simp only [sub_re, one_re]
    linarith
  have hsigmaHalf : sigma.re < 1 / 2 := by
    dsimp only [sigma]
    simp only [sub_re, one_re]
    linarith
  obtain ⟨r, hr, L, hL⟩ := hlocal sigma hsigmaPos hsigmaHalf
  let epsilon : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ)⁻¹)
  have hepsilonPos (n : ℕ) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
    dsimp only [epsilon]
    exact tendsto_natCast_atTop_atTop.inv_tendsto_atTop.comp
      (Filter.tendsto_add_atTop_nat 1)
  have hshift : Tendsto (fun n : ℕ => sigma + (epsilon n : ℂ)) atTop (nhds sigma) := by
    have hcast : Tendsto (fun n : ℕ => (epsilon n : ℂ)) atTop (nhds 0) :=
      (Complex.continuous_ofReal.tendsto 0).comp hepsilonZero
    simpa using tendsto_const_nhds.add hcast
  have hshiftWithin : Tendsto (fun n : ℕ => sigma + (epsilon n : ℂ)) atTop
      (nhdsWithin sigma ({sigma}ᶜ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hshift, Eventually.of_forall (fun n => ?_)⟩
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have : (epsilon n : ℂ) = 0 := by linear_combination h
    exact (ofReal_ne_zero.mpr (hepsilonPos n).ne') this
  let m : ℕ := (analyticOrderAt xi sigma).toNat
  have hmPos : 0 < m := Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hsigmaZero)
  have hnormalized := (xi_normalizedLogDeriv_tendsto_order sigma).comp hshiftWithin
  have hnormalized' : Tendsto
      (fun n : ℕ => (epsilon n : ℂ) * logDeriv xi (sigma + (epsilon n : ℂ)))
      atTop (nhds (m : ℂ)) := by
    simpa [m, Function.comp_def] using hnormalized
  have hnormalizedRe : Tendsto
      (fun n : ℕ => epsilon n * (logDeriv xi (sigma + (epsilon n : ℂ))).re)
      atTop (nhds (m : ℝ)) := by
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hnormalized'
    simpa [mul_re, Function.comp_def] using hre
  let B : ℝ := max (-L) 0 + 1
  have hBPos : 0 < B := by
    dsimp [B]
    linarith [le_max_right (-L) 0]
  have hNegLtB : -L < B := by
    dsimp [B]
    linarith [le_max_left (-L) 0]
  have hmRealPos : 0 < (m : ℝ) := by exact_mod_cast hmPos
  have hevLower : ∀ᶠ n in atTop,
      (m : ℝ) / 2 < epsilon n * (logDeriv xi (sigma + (epsilon n : ℂ))).re :=
    hnormalizedRe.eventually (eventually_gt_nhds (by linarith))
  have hsmallPos : 0 < (m : ℝ) / (2 * B) := by positivity
  have hevSmall : ∀ᶠ n in atTop, epsilon n < (m : ℝ) / (2 * B) :=
    hepsilonZero.eventually (eventually_lt_nhds hsmallPos)
  have hevRadius : ∀ᶠ n in atTop, epsilon n < r :=
    hepsilonZero.eventually (eventually_lt_nhds hr)
  have hgapPos : 0 < 1 / 2 - sigma.re := by linarith
  have hevGap : ∀ᶠ n in atTop, epsilon n < 1 / 2 - sigma.re :=
    hepsilonZero.eventually (eventually_lt_nhds hgapPos)
  obtain ⟨n, hnLower, hnSmall, hnRadius, hnGap⟩ :=
    (hevLower.and (hevSmall.and (hevRadius.and hevGap))).exists
  let s : ℂ := sigma + (epsilon n : ℂ)
  have hsre : s.re = sigma.re + epsilon n := by simp [s]
  have hspos : 0 < s.re := by rw [hsre]; linarith [hepsilonPos n]
  have hshalf : s.re < 1 / 2 := by rw [hsre]; linarith
  have hdist : dist s sigma = epsilon n := by
    simp [s, dist_eq_norm, Complex.norm_real, abs_of_pos (hepsilonPos n)]
  have hlogB : B < (logDeriv xi s).re := by
    have hepsilonB : epsilon n * B < (m : ℝ) / 2 := by
      have h := mul_lt_mul_of_pos_right hnSmall hBPos
      field_simp [ne_of_gt hBPos] at h
      nlinarith
    dsimp only [s]
    nlinarith [hepsilonPos n]
  have hxiS : xi s ≠ 0 := by
    intro hs0
    have hld0 : logDeriv xi s = 0 := by simp [logDeriv_apply, hs0]
    rw [hld0, zero_re] at hlogB
    linarith
  have hs1 : s ≠ 1 := by
    intro hsone
    have hre := congrArg Complex.re hsone
    rw [one_re] at hre
    linarith
  have hzetaS : riemannZeta s ≠ 0 :=
    (xi_eq_zero_iff hspos hs1).not.mp hxiS
  let z : ℂ := (s - 1 / 2) * (-I)
  have hcoord : 1 / 2 + z * I = s := by
    dsimp only [z]
    rw [mul_assoc]
    have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
    rw [hI, mul_one]
    ring
  have hXiZ : XiC z ≠ 0 := by
    rw [XiC, hcoord]
    exact hxiS
  have hsourceFlux :
      -I * completedPrimeGammaFlux s = I * logDeriv xi s := by
    calc
      -I * completedPrimeGammaFlux s = continuedPrimeArchSourceRelativeTrace z := by
        rw [continuedPrimeArchSourceRelativeTrace, hcoord]
        rfl
      _ = xiRelativeResolventTrace z :=
        continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
          (by rw [hcoord]; exact hspos) (by rw [hcoord]; exact hs1)
          (by rw [hcoord]; exact hzetaS)
      _ = logDeriv XiC z := (logDeriv_XiC_eq_relativeResolventTrace hXiZ).symm
      _ = I * logDeriv xi s := by
        rw [logDeriv_XiC_eq_mul_I_logDeriv_xi, hcoord]
  have hflux : completedPrimeGammaFlux s = -logDeriv xi s := by
    calc
      completedPrimeGammaFlux s = I * (-I * completedPrimeGammaFlux s) := by
        rw [← mul_assoc, mul_neg, I_mul_I]
        ring
      _ = I * (I * logDeriv xi s) := by rw [hsourceFlux]
      _ = -logDeriv xi s := by
        rw [← mul_assoc, I_mul_I]
        ring
  have hlocalBound := hL s (by rw [hdist]; exact hnRadius) hspos hshalf hzetaS
  have : (completedPrimeGammaFlux s).re < L := by
    rw [hflux]
    simp only [neg_re]
    linarith
  exact (not_lt_of_ge hlocalBound) this

/-- RH gives local lower boundedness; in fact the common lower bound zero works throughout the
whole left half-strip. -/
theorem completedPrimeGammaLeftHalfLocallyBoundedBelow_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    CompletedPrimeGammaLeftHalfLocallyBoundedBelow := by
  have hacc := completedPrimeGammaLeftHalfAccretive_iff_riemannHypothesis.mpr hRH
  intro sigma _hsigmaPos _hsigmaHalf
  refine ⟨1, zero_lt_one, 0, ?_⟩
  intro s _hdist hspos hshalf hzeta
  exact hacc s hspos hshalf hzeta

/-- Exact local lower-bound criterion for RH. -/
theorem completedPrimeGammaLeftHalfLocallyBoundedBelow_iff_riemannHypothesis :
    CompletedPrimeGammaLeftHalfLocallyBoundedBelow ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_completedPrimeGammaLeftHalfLocallyBoundedBelow,
    completedPrimeGammaLeftHalfLocallyBoundedBelow_of_riemannHypothesis⟩

/-- Interface-free capstone: RH is equivalent to the fully expanded pointwise local source
condition, with no global constant or asymptotic rate. -/
theorem riemannHypothesis_iff_forall_exists_completedPrimeGamma_local_lowerBound :
    RiemannHypothesis ↔
      ∀ sigma : ℂ, 0 < sigma.re → sigma.re < 1 / 2 →
        ∃ r : ℝ, 0 < r ∧ ∃ L : ℝ, ∀ s : ℂ,
          dist s sigma < r → 0 < s.re → s.re < 1 / 2 →
            riemannZeta s ≠ 0 → L ≤ (completedPrimeGammaFlux s).re := by
  change RiemannHypothesis ↔ CompletedPrimeGammaLeftHalfLocallyBoundedBelow
  exact completedPrimeGammaLeftHalfLocallyBoundedBelow_iff_riemannHypothesis.symm

end

end RHTower
