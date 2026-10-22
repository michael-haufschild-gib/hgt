import GaloisForLFunctions.RHTower.CCM.CCMAnalyticShiftSpectrumRigidity
import GaloisForLFunctions.HTGeometry.BoundaryTraceRamification

/-!
# Finite-ramified CCM boundary monodromy selection

This file classifies every finite-sheeted norm-holomorphic realization of a
positive first-order thermal boundary density.  The density fixes the analytic
order to exactly half the ramification degree and therefore selects the sign
character of the deck generator.  Consequently, a branch that descends through
the full deck group cannot realize any positive finite density, including the
CCM four-unit normalization.

The target is an arbitrary complex normed space; no rank, dimension, or
scalarization assumption occurs.
-/

open Filter
open scoped Topology

noncomputable section

namespace RHTower

/-- A nonzero finite limit of an exponential rate times a positive-limit factor
forces the exponential rate to vanish. -/
theorem exp_rate_eq_zero_of_tendsto_mul_pos
    {k c ell : ℝ} {U : ℝ → ℝ}
    (hc : 0 < c) (hell : 0 < ell)
    (hU : Tendsto U atTop (nhds c))
    (hprod : Tendsto (fun h : ℝ => Real.exp (k * h) * U h) atTop (nhds ell)) :
    k = 0 := by
  by_contra hk
  rcases lt_or_gt_of_ne hk with hkneg | hkpos
  · have hlin : Tendsto (fun h : ℝ => k * h) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg hkneg
    have hexp : Tendsto (fun h : ℝ => Real.exp (k * h)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp hlin
    have hzero : Tendsto (fun h : ℝ => Real.exp (k * h) * U h) atTop (nhds 0) := by
      simpa using hexp.mul hU
    have : (0 : ℝ) = ell := tendsto_nhds_unique hzero hprod
    linarith
  · have hlin : Tendsto (fun h : ℝ => -k * h) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by linarith)
    have hexp : Tendsto (fun h : ℝ => Real.exp (-k * h)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp hlin
    have hinvU : Tendsto (fun h => (U h)⁻¹) atTop (nhds c⁻¹) := hU.inv₀ hc.ne'
    have hzero : Tendsto (fun h : ℝ => Real.exp (-k * h) * (U h)⁻¹)
        atTop (nhds 0) := by
      simpa using hexp.mul hinvU
    have hinvprod : Tendsto
        (fun h : ℝ => (Real.exp (k * h) * U h)⁻¹) atTop (nhds ell⁻¹) :=
      hprod.inv₀ hell.ne'
    have hcongr : (fun h : ℝ => (Real.exp (k * h) * U h)⁻¹) =
        fun h : ℝ => Real.exp (-k * h) * (U h)⁻¹ := by
      funext h
      rw [mul_inv_rev, ← Real.exp_neg]
      ring_nf
    rw [hcongr] at hinvprod
    have : (0 : ℝ) = ell⁻¹ := tendsto_nhds_unique hzero hinvprod
    exact (inv_ne_zero hell.ne').symm this

/-- Thermal boundary density of an analytic germ along the exponential arc
`z = exp (-q h)`, with physical boundary coordinate `u = exp (-h)`. -/
def analyticRamifiedBoundaryDensity
    {E : Type*} [NormedAddCommGroup E] (q : ℝ) (F : ℂ → E) (h : ℝ) : ℝ :=
  normedAnalyticShiftMultiplier q F h ^ 2 /
    (1 - Real.exp (-Real.exp (-h)))

/-- Boundary density on an `r`-sheeted analytic branch, obtained from the
universal exponential rate by `q = 1/r`. -/
def finiteRamifiedAnalyticBoundaryDensity
    {E : Type*} [NormedAddCommGroup E] (r : ℕ) (F : ℂ → E) (h : ℝ) : ℝ :=
  analyticRamifiedBoundaryDensity (r : ℝ)⁻¹ F h

/-- The thermal denominator is asymptotic to the physical boundary coordinate. -/
theorem tendsto_exp_neg_div_one_sub_exp_neg_exp_neg :
    Tendsto (fun h : ℝ => Real.exp (-h) /
      (1 - Real.exp (-Real.exp (-h)))) atTop (nhds 1) := by
  have hexp : Tendsto (fun h : ℝ => Real.exp (-h)) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨Real.tendsto_exp_neg_atTop_nhds_zero, ?_⟩
    exact Eventually.of_forall fun h => Real.exp_pos (-h)
  exact HTGeometry.tendsto_id_div_one_sub_exp_neg_nhdsGT_zero.comp hexp

/-- Positive boundary density itself excludes the locally-zero analytic branch;
finiteness of analytic order is a conclusion, not an extra premise. -/
theorem analyticOrderAt_ne_top_of_analyticRamifiedBoundaryDensity_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {q : ℝ} (hq : 0 < q) {F : ℂ → E} {ell : ℝ} (hell : 0 < ell)
    (hdensity : Tendsto (analyticRamifiedBoundaryDensity q F) atTop (nhds ell)) :
    analyticOrderAt F 0 ≠ ⊤ := by
  intro htop
  have hzeroMultiplier :
      normedAnalyticShiftMultiplier q F =ᶠ[atTop] 0 :=
    normedAnalyticShiftMultiplier_eventually_eq_zero_of_order_eq_top
      hq htop
  have hzeroDensity : analyticRamifiedBoundaryDensity q F =ᶠ[atTop] 0 := by
    filter_upwards [hzeroMultiplier] with h hh
    rw [analyticRamifiedBoundaryDensity, hh]
    simp
  have hzeroAtEll : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds ell) :=
    hdensity.congr' hzeroDensity
  have : (0 : ℝ) = ell := tendsto_nhds_unique tendsto_const_nhds hzeroAtEll
  linarith

/-- **Universal charge-rate law.** A positive finite first-order boundary
density forces twice the ramification rate times the integral analytic charge
to equal one. -/
theorem two_mul_rate_mul_analyticOrderNatAt_eq_one_of_boundaryDensity_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {q : ℝ} (hq : 0 < q) {F : ℂ → E} (hF : AnalyticAt ℂ F 0)
    {ell : ℝ} (hell : 0 < ell)
    (hdensity : Tendsto (analyticRamifiedBoundaryDensity q F) atTop (nhds ell)) :
    2 * q * (analyticOrderNatAt F 0 : ℝ) = 1 := by
  have hFfinite : analyticOrderAt F 0 ≠ ⊤ :=
    analyticOrderAt_ne_top_of_analyticRamifiedBoundaryDensity_pos hq hell hdensity
  obtain ⟨G, _, hG0, hGlim, hfactor⟩ :=
    normedAnalyticShiftMultiplier_eventually_factor hq hF hFfinite
  let m : ℕ := analyticOrderNatAt F 0
  let U : ℝ → ℝ := fun h =>
    normedAnalyticShiftMultiplier q G h ^ 2 *
      (Real.exp (-h) / (1 - Real.exp (-Real.exp (-h))))
  have hU : Tendsto U atTop (nhds (‖G 0‖ ^ 2)) := by
    have hGsq : Tendsto
        (fun h => normedAnalyticShiftMultiplier q G h ^ 2)
        atTop (nhds (‖G 0‖ ^ 2)) := hGlim.pow 2
    simpa only [U, mul_one] using
      hGsq.mul tendsto_exp_neg_div_one_sub_exp_neg_exp_neg
  have hUpos : 0 < ‖G 0‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hG0)
  have hcongr : analyticRamifiedBoundaryDensity q F =ᶠ[atTop]
      fun h => Real.exp ((1 - 2 * q * (m : ℝ)) * h) * U h := by
    filter_upwards [hfactor] with h hh
    rw [analyticRamifiedBoundaryDensity, hh]
    dsimp only [U, m]
    have hden : 1 - Real.exp (-Real.exp (-h)) ≠ 0 := by
      have hlt : Real.exp (-Real.exp (-h)) < 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (neg_neg_of_pos (Real.exp_pos (-h)))
      linarith
    rw [mul_pow]
    field_simp [hden]
    have hexpeq :
        Real.exp (-(q * (analyticOrderNatAt F 0 : ℝ) * h)) ^ 2 =
          Real.exp (-h) * Real.exp
            ((1 - 2 * q * (analyticOrderNatAt F 0 : ℝ)) * h) := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring_nf
    rw [hexpeq]
    ring_nf
  have hproduct : Tendsto
      (fun h => Real.exp ((1 - 2 * q * (m : ℝ)) * h) * U h)
      atTop (nhds ell) := hdensity.congr' hcongr
  have hk : 1 - 2 * q * (m : ℝ) = 0 :=
    exp_rate_eq_zero_of_tendsto_mul_pos hUpos hell hU hproduct
  exact by nlinarith

/-- Positive density on a finite `r`-sheeted branch automatically has finite
analytic order. -/
theorem analyticOrderAt_ne_top_of_finiteRamified_boundaryDensity_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {r : ℕ} (hr : 0 < r) {F : ℂ → E} {ell : ℝ} (hell : 0 < ell)
    (hdensity : Tendsto (finiteRamifiedAnalyticBoundaryDensity r F) atTop (nhds ell)) :
    analyticOrderAt F 0 ≠ ⊤ := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  exact analyticOrderAt_ne_top_of_analyticRamifiedBoundaryDensity_pos
    (inv_pos.mpr hrR) hell hdensity

/-- **Finite half-order law.** On an `r`-sheeted analytic branch, positive
first-order density forces twice the vanishing order to equal the sheet number. -/
theorem two_mul_analyticOrderNatAt_eq_ramification_of_boundaryDensity_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {r : ℕ} (hr : 0 < r) {F : ℂ → E} (hF : AnalyticAt ℂ F 0)
    {ell : ℝ} (hell : 0 < ell)
    (hdensity : Tendsto (finiteRamifiedAnalyticBoundaryDensity r F) atTop (nhds ell)) :
    2 * analyticOrderNatAt F 0 = r := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrate :=
    two_mul_rate_mul_analyticOrderNatAt_eq_one_of_boundaryDensity_pos
      (inv_pos.mpr hrR) hF hell hdensity
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hrR
  exact_mod_cast (by
    field_simp [hrne] at hrate
    nlinarith : (2 * (analyticOrderNatAt F 0 : ℝ) : ℝ) = r)

/-- Deck invariance under any scalar generator forces the leading analytic
charge to lie in that generator's trivial character. -/
theorem analyticOrderNatAt_deckCharacter_eq_one_of_deck_invariant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ζ : ℂ} {F : ℂ → E} (hF : AnalyticAt ℂ F 0)
    (hsym : ∀ᶠ z : ℂ in 𝓝 0, F (ζ * z) = F z)
    (hFfinite : analyticOrderAt F 0 ≠ ⊤) :
    ζ ^ analyticOrderNatAt F 0 = 1 := by
  let m : ℕ := analyticOrderNatAt F 0
  have horder : (m : ℕ∞) = analyticOrderAt F 0 := ENat.coe_toNat hFfinite
  obtain ⟨G, hGan, hG0, hfactor⟩ :=
    (hF.analyticOrderAt_eq_natCast).mp horder.symm
  have hrot : Tendsto (fun z : ℂ => ζ * z) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun z : ℂ => ζ * z) 0 :=
      continuousAt_const.mul continuousAt_id
    simpa using hc.tendsto
  have hfactorSelf : ∀ᶠ z : ℂ in 𝓝[≠] 0, F z = z ^ m • G z := by
    simpa only [sub_zero] using hfactor.filter_mono nhdsWithin_le_nhds
  have hfactorRot : ∀ᶠ z : ℂ in 𝓝[≠] 0,
      F (ζ * z) = (ζ * z) ^ m • G (ζ * z) := by
    simpa only [sub_zero] using
      (hrot.mono_left nhdsWithin_le_nhds).eventually hfactor
  have hsymWithin : ∀ᶠ z : ℂ in 𝓝[≠] 0, F (ζ * z) = F z :=
    hsym.filter_mono nhdsWithin_le_nhds
  have key : ∀ᶠ z : ℂ in 𝓝[≠] 0, G z = ζ ^ m • G (ζ * z) := by
    filter_upwards [self_mem_nhdsWithin, hfactorSelf, hfactorRot, hsymWithin]
      with z hz hself hrotFact hsymz
    have hzpow : z ^ m ≠ 0 := pow_ne_zero m hz
    have heq : z ^ m • G z = z ^ m • (ζ ^ m • G (ζ * z)) := by
      rw [← hself, ← hsymz, hrotFact, mul_pow, mul_smul]
      simp only [smul_smul]
      rw [mul_comm (ζ ^ m) (z ^ m)]
    have hcancel := congrArg (fun v : E => (z ^ m)⁻¹ • v) heq
    simpa [smul_smul, hzpow] using hcancel
  have hlimSelf : Tendsto G (𝓝[≠] 0) (𝓝 (G 0)) :=
    hGan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlimRot : Tendsto (fun z : ℂ => ζ ^ m • G (ζ * z)) (𝓝[≠] 0)
      (𝓝 (ζ ^ m • G 0)) := by
    have hcomp : Tendsto (fun z : ℂ => G (ζ * z)) (𝓝 0) (𝓝 (G 0)) :=
      hGan.continuousAt.tendsto.comp hrot
    exact (hcomp.const_smul (ζ ^ m)).mono_left nhdsWithin_le_nhds
  have heq : G 0 = ζ ^ m • G 0 :=
    tendsto_nhds_unique (hlimSelf.congr' key) hlimRot
  have hpow : ζ ^ m = 1 := by
    have hzero : (ζ ^ m - 1) • G 0 = 0 := by
      rw [sub_smul, one_smul, ← heq, sub_self]
    rcases smul_eq_zero.mp hzero with hs | hv
    · exact sub_eq_zero.mp hs
    · exact False.elim (hG0 hv)
  simpa only [m] using hpow

/-- For a primitive finite deck generator, trivial leading character is
equivalent to divisibility of analytic charge by sheet number. -/
theorem ramification_dvd_analyticOrderNatAt_of_deck_invariant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {r : ℕ} {ζ : ℂ} {F : ℂ → E} (hF : AnalyticAt ℂ F 0)
    (hroot : IsPrimitiveRoot ζ r)
    (hsym : ∀ᶠ z : ℂ in 𝓝 0, F (ζ * z) = F z)
    (hFfinite : analyticOrderAt F 0 ≠ ⊤) :
    r ∣ analyticOrderNatAt F 0 := by
  exact (hroot.pow_eq_one_iff_dvd (analyticOrderNatAt F 0)).mp
    (analyticOrderNatAt_deckCharacter_eq_one_of_deck_invariant hF hsym hFfinite)

private theorem not_dvd_of_two_mul_eq
    {r m : ℕ} (hr : 0 < r) (hhalf : 2 * m = r) : ¬ r ∣ m := by
  intro hdvd
  have hmpos : 0 < m := by omega
  have hrle : r ≤ m := Nat.le_of_dvd hmpos hdvd
  omega

/-- **Universal density--monodromy charge law.** At every positive
ramification rate, a positive finite thermal density and deck descent force a
strictly positive integral charge `m`, the exact relation `2 q m = 1`, and
trivial deck character `ζ^m = 1`. -/
theorem analyticRamified_boundaryDensity_deckInvariant_chargeLaw
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {q : ℝ} (hq : 0 < q) {ζ : ℂ} {F : ℂ → E}
    (hF : AnalyticAt ℂ F 0)
    (hsym : ∀ᶠ z : ℂ in 𝓝 0, F (ζ * z) = F z)
    {ell : ℝ} (hell : 0 < ell)
    (hdensity : Tendsto (analyticRamifiedBoundaryDensity q F) atTop (nhds ell)) :
    0 < analyticOrderNatAt F 0 ∧
      2 * q * (analyticOrderNatAt F 0 : ℝ) = 1 ∧
      ζ ^ analyticOrderNatAt F 0 = 1 := by
  have hfinite : analyticOrderAt F 0 ≠ ⊤ :=
    analyticOrderAt_ne_top_of_analyticRamifiedBoundaryDensity_pos hq hell hdensity
  have hrate := two_mul_rate_mul_analyticOrderNatAt_eq_one_of_boundaryDensity_pos
    hq hF hell hdensity
  have hmpos : 0 < analyticOrderNatAt F 0 := by
    by_contra hnot
    have hmzero : analyticOrderNatAt F 0 = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hmzero] at hrate
    norm_num at hrate
  exact ⟨hmpos, hrate,
    analyticOrderNatAt_deckCharacter_eq_one_of_deck_invariant hF hsym hfinite⟩

/-- **Infinite-sheet exclusion.** A nontorsion scalar deck generator cannot
descend any norm-holomorphic branch carrying positive finite thermal density. -/
theorem not_exists_analyticRamified_infiniteDeckInvariant_positiveBoundaryDensity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {q : ℝ} (hq : 0 < q) {ζ : ℂ} {F : ℂ → E}
    (hF : AnalyticAt ℂ F 0)
    (hinfinite : ∀ n : ℕ, 0 < n → ζ ^ n ≠ 1)
    (hsym : ∀ᶠ z : ℂ in 𝓝 0, F (ζ * z) = F z) :
    ¬ ∃ ell : ℝ, 0 < ell ∧
      Tendsto (analyticRamifiedBoundaryDensity q F) atTop (nhds ell) := by
  rintro ⟨ell, hell, hdensity⟩
  obtain ⟨hmpos, _, hcharacter⟩ :=
    analyticRamified_boundaryDensity_deckInvariant_chargeLaw
      hq hF hsym hell hdensity
  exact hinfinite _ hmpos hcharacter

/-- **Monodromy selection law.** Positive first-order boundary density selects
the sign character of every finite ramified analytic branch: sheet number is
even and deck generator acts by `-1` on the leading coefficient. -/
theorem finiteRamified_boundaryDensity_forces_even_and_deckCharacter_neg_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {r : ℕ} (hr : 0 < r) {ζ : ℂ} {F : ℂ → E}
    (hF : AnalyticAt ℂ F 0) (hroot : IsPrimitiveRoot ζ r)
    {ell : ℝ} (hell : 0 < ell)
    (hdensity : Tendsto (finiteRamifiedAnalyticBoundaryDensity r F) atTop (nhds ell)) :
    Even r ∧ ζ ^ analyticOrderNatAt F 0 = -1 := by
  let m : ℕ := analyticOrderNatAt F 0
  have hhalf : 2 * m = r :=
    two_mul_analyticOrderNatAt_eq_ramification_of_boundaryDensity_pos
      hr hF hell hdensity
  have heven : Even r := ⟨m, by omega⟩
  have hsq : (ζ ^ m) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm m 2, hhalf]
    exact hroot.pow_eq_one
  have hne : ζ ^ m ≠ 1 := by
    intro hone
    have hdvd : r ∣ m := (hroot.pow_eq_one_iff_dvd m).mp hone
    exact not_dvd_of_two_mul_eq hr hhalf hdvd
  refine ⟨heven, ?_⟩
  exact (sq_eq_one_iff.mp hsq).resolve_left hne

/-- **Finite ramification exclusion.** No finite-sheeted norm-holomorphic
boundary germ can both descend through its full deck group and carry a positive
finite first-order thermal density. -/
theorem not_exists_finiteRamified_deckInvariant_positiveBoundaryDensity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {r : ℕ} (hr : 0 < r) {ζ : ℂ} {F : ℂ → E}
    (hF : AnalyticAt ℂ F 0) (hroot : IsPrimitiveRoot ζ r)
    (hsym : ∀ᶠ z : ℂ in 𝓝 0, F (ζ * z) = F z) :
    ¬ ∃ ell : ℝ, 0 < ell ∧
      Tendsto (finiteRamifiedAnalyticBoundaryDensity r F) atTop (nhds ell) := by
  rintro ⟨ell, hell, hdensity⟩
  have hfinite : analyticOrderAt F 0 ≠ ⊤ :=
    analyticOrderAt_ne_top_of_finiteRamified_boundaryDensity_pos hr hell hdensity
  have hhalf := two_mul_analyticOrderNatAt_eq_ramification_of_boundaryDensity_pos
    hr hF hell hdensity
  have hdvd := ramification_dvd_analyticOrderNatAt_of_deck_invariant
    hF hroot hsym hfinite
  exact not_dvd_of_two_mul_eq hr hhalf hdvd

/-- Direct CCM connector: four-unit boundary density forces even ramification
and sign monodromy on every finite analytic branch. -/
theorem ccmFourUnit_finiteRamifiedBoundary_forces_deckCharacter_neg_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {r : ℕ} (hr : 0 < r) {ζ : ℂ} {F : ℂ → E}
    (hF : AnalyticAt ℂ F 0) (hroot : IsPrimitiveRoot ζ r)
    (hfour : Tendsto (finiteRamifiedAnalyticBoundaryDensity r F) atTop (nhds 4)) :
    Even r ∧ ζ ^ analyticOrderNatAt F 0 = -1 := by
  exact finiteRamified_boundaryDensity_forces_even_and_deckCharacter_neg_one
    hr hF hroot (by norm_num) hfour

/-- Direct infinite-sheet CCM no-go: a nontorsion scalar deck generator cannot
descend a norm-holomorphic branch carrying the four-unit normalization. -/
theorem ccmFourUnit_not_analyticRamified_infiniteDeckInvariant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {q : ℝ} (hq : 0 < q) {ζ : ℂ} {F : ℂ → E}
    (hF : AnalyticAt ℂ F 0)
    (hinfinite : ∀ n : ℕ, 0 < n → ζ ^ n ≠ 1)
    (hsym : ∀ᶠ z : ℂ in 𝓝 0, F (ζ * z) = F z) :
    ¬ Tendsto (analyticRamifiedBoundaryDensity q F) atTop (nhds 4) := by
  intro hfour
  exact not_exists_analyticRamified_infiniteDeckInvariant_positiveBoundaryDensity
    hq hF hinfinite hsym ⟨4, by norm_num, hfour⟩

/-- Direct CCM no-go: no finite-sheeted, deck-invariant norm-holomorphic germ
can realize the four-unit boundary normalization. -/
theorem ccmFourUnit_not_finiteRamified_deckInvariant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {r : ℕ} (hr : 0 < r) {ζ : ℂ} {F : ℂ → E}
    (hF : AnalyticAt ℂ F 0) (hroot : IsPrimitiveRoot ζ r)
    (hsym : ∀ᶠ z : ℂ in 𝓝 0, F (ζ * z) = F z) :
    ¬ Tendsto (finiteRamifiedAnalyticBoundaryDensity r F) atTop (nhds 4) := by
  intro hfour
  exact not_exists_finiteRamified_deckInvariant_positiveBoundaryDensity
    hr hF hroot hsym ⟨4, by norm_num, hfour⟩

end RHTower
