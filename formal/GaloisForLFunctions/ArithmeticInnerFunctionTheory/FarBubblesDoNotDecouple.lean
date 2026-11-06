import GaloisForLFunctions.ArithmeticOrientationGeometry.TheOrientationRateIsTheDepthOfTheDeepestSeenZero
import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheLatticeHasNoSlackUnderRH
import GaloisForLFunctions.GrowingWindowsOfSpecZ.ForbiddingLatticeZeroModesIsRH
import GaloisForLFunctions.GrowingWindowsOfSpecZ.RHIsDecidedOnTwoSites
import GaloisForLFunctions.RHTower.CompactTestXiDivisibilityObstruction
import GaloisForLFunctions.RHTower.CrossRouteReceiverBridges

/-!
# Far bubbles do not decouple

Concentration-compactness (Lions) runs on one principle: a sequence that loses compactness splits into far-apart bubbles, and the energy
of far-apart bubbles adds. For Weil's form the failure of compactness is translation, and the defect of additivity is the orbit correlation:
`Q(φ − φ(· + t)) = 2Q(φ) − 2c_φ(t)`.

**Theorem** (`not_tendsto_weilOrbitCorr`, unconditional). For every nonzero test, `c_φ(t)` does not tend to `0` as `t → ∞`. So no nonzero
bubble decouples from its far translate (`not_tendsto_dipole`), and Lions' dichotomy fails on every bubble.

The proof has three parts. If `c_φ → 0` it is bounded, so `φ` is blind to every off-line zero (the orientation rate theorem). What remains is a cosine
series with nonnegative weights on the line, and such a series recurs (`eq_zero_of_tendsto_cos_sum`, by simultaneous Dirichlet
approximation), so all on-line weights vanish. Then `φ̂` vanishes at all real zeros of `Ξ`, which forces `φ = 0`.

**No energy is lost at spectral infinity** (`tendsto_weilQuad_of_dominated`, unconditional). The form sees only the zeros, through an absolutely convergent sum. A sequence
of tests whose zero summands are dominated by one summable sequence and converge at each zero has converging energy. So translation is the only loss of compactness,
and it acts on the zero side by phases.

**What replaces decoupling: recurrence** (`riemannHypothesis_iff_orbit_recurs`). RH is the strict orbit Cauchy–Schwarz inequality together with this: dipoles of mass `2‖φ‖²` have
arbitrarily small energy at arbitrarily large separation. The bottom of the form is reached at translation infinity, by bubbles that interfere destructively and never
separate. The space at infinity of a compactness theorem for arithmetic forms is the Bohr compactification of the translation group, in place of a sum of decoupled profiles.
-/

open Filter Topology MeasureTheory Set Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open GrowingWindowsOfSpecZ ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry Zeta23
  SpacingScaleHarmonicAnalysis
open GaloisForLFunctions.SquareRootThreshold (temperedConfig_zetaZeroConfig)

noncomputable section

/-! ### Cosine series with nonnegative weights recur -/

/-- **Simultaneous recurrence**: finitely many cosines are at least `½` at arbitrarily large times. -/
theorem exists_cos_ge_half {ι : Type*} (F : Finset ι) (g : ι → ℝ) (T : ℝ) :
    ∃ t, T ≤ t ∧ ∀ i ∈ F, 1 / 2 ≤ Real.cos (g i * t) := by
  classical
  set h : ℝ := max T 1 with hh
  have hh1 : 1 ≤ h := le_max_right _ _
  have hπ : 0 < Real.pi := Real.pi_pos
  let e := F.equivFin
  let β : Fin F.card → ℝ := fun j => g (e.symm j).1 * h / (2 * Real.pi)
  obtain ⟨p, hp1, -, hclose⟩ := HTGeometry.exists_simultaneous_dirichlet β (Q := 10) (by norm_num)
  refine ⟨p * h, ?_, fun i hi => ?_⟩
  · have hp : (1 : ℝ) ≤ p := by exact_mod_cast hp1
    calc T ≤ h := le_max_left _ _
      _ = 1 * h := (one_mul h).symm
      _ ≤ p * h := mul_le_mul_of_nonneg_right hp (by linarith)
  · obtain ⟨k, hk⟩ := hclose (e ⟨i, hi⟩)
    have hβ : β (e ⟨i, hi⟩) = g i * h / (2 * Real.pi) := by
      simp only [β, Equiv.symm_apply_apply]
    rw [hβ] at hk
    have hx : g i * ((p : ℝ) * h) =
        2 * Real.pi * ((p : ℝ) * (g i * h / (2 * Real.pi)) - k) + k * (2 * Real.pi) := by
      field_simp
      ring
    rw [hx, Real.cos_add_int_mul_two_pi]
    set y : ℝ := (p : ℝ) * (g i * h / (2 * Real.pi)) - k with hy
    have hyb : |y| < 1 / ((10 : ℕ) : ℝ) := hk
    have hy2 : y ^ 2 ≤ (1 / 10) ^ 2 := by
      rw [← sq_abs y]
      have h0 := abs_nonneg y
      have h1 : |y| ≤ 1 / 10 := by
        have : (1 : ℝ) / ((10 : ℕ) : ℝ) = 1 / 10 := by norm_num
        rw [this] at hyb
        exact hyb.le
      exact pow_le_pow_left₀ h0 h1 2
    have hc := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * y)
    have hπ2 : Real.pi ^ 2 ≤ 10 := by
      have := Real.pi_lt_d2
      nlinarith
    have hbound : (2 * Real.pi * y) ^ 2 ≤ 1 := by
      have e2 : (2 * Real.pi * y) ^ 2 = 4 * Real.pi ^ 2 * y ^ 2 := by ring
      rw [e2]
      have h2 : 0 ≤ y ^ 2 := sq_nonneg y
      nlinarith
    linarith

/-- **A cosine series with nonnegative weights tending to `0` is zero.** -/
theorem eq_zero_of_tendsto_cos_sum {ι : Type*} {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw : Summable w)
    {g : ι → ℝ} (h : Tendsto (fun t : ℝ => ∑' i, w i * Real.cos (g i * t)) atTop (𝓝 0)) (i : ι) :
    w i = 0 := by
  classical
  by_contra hne
  have hi : 0 < w i := lt_of_le_of_ne (hw0 i) (Ne.symm hne)
  set W := ∑' j, w j with hW
  have hWpos : 0 < W := lt_of_lt_of_le hi (hw.le_tsum i fun j _ => hw0 j)
  have htail := tendsto_tsum_compl_atTop_zero w
  obtain ⟨F, hF⟩ := eventually_atTop.mp (htail.eventually_lt_const (by linarith : (0 : ℝ) < W / 8))
  have hτ : ∑' q : {x // x ∉ F}, w q < W / 8 := hF F le_rfl
  obtain ⟨T, hT⟩ := eventually_atTop.mp (h.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < 5 * W / 16)))
  obtain ⟨t, ht, hcos⟩ := exists_cos_ge_half F g T
  have hsum : Summable fun j => w j * Real.cos (g j * t) := hw.of_norm_bounded fun j => by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hw0 j)]
    exact mul_le_of_le_one_right (hw0 j) (Real.abs_cos_le_one _)
  have hsplit : ∑ j ∈ F, w j * Real.cos (g j * t) +
      ∑' q : {x // x ∉ F}, w q * Real.cos (g q * t) = ∑' j, w j * Real.cos (g j * t) :=
    hsum.sum_add_tsum_compl (s := F)
  have hsplitw : ∑ j ∈ F, w j + ∑' q : {x // x ∉ F}, w q = W := hw.sum_add_tsum_compl (s := F)
  have h1 : (1 / 2) * ∑ j ∈ F, w j ≤ ∑ j ∈ F, w j * Real.cos (g j * t) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have := mul_le_mul_of_nonneg_left (hcos j hj) (hw0 j)
    linarith
  have hsc : Summable fun q : {x // x ∉ F} => w q * Real.cos (g q * t) :=
    hsum.subtype _
  have hsw : Summable fun q : {x // x ∉ F} => w q := hw.subtype _
  have h2 : -∑' q : {x // x ∉ F}, w q ≤ ∑' q : {x // x ∉ F}, w q * Real.cos (g q * t) := by
    rw [← tsum_neg]
    refine hsw.neg.tsum_le_tsum (fun q => ?_) hsc
    have := Real.neg_one_le_cos (g q * t)
    have h3 := hw0 q
    nlinarith
  have h3 := hT t ht
  have hg : ∑ j ∈ F, w j = W - ∑' q : {x // x ∉ F}, w q := by linarith
  have hge : 5 * W / 16 ≤ ∑' j, w j * Real.cos (g j * t) := by
    have e1 : ∑' j, w j * Real.cos (g j * t) = ∑ j ∈ F, w j * Real.cos (g j * t) +
        ∑' q : {x // x ∉ F}, w q * Real.cos (g q * t) := hsplit.symm
    rw [e1]
    rw [hg] at h1
    linarith
  linarith

/-! ### No nonzero bubble decouples -/

/-- The value of `gammaOf` on the line. -/
theorem gammaOf_of_re_eq_half {ρ : ℂ} (hρ : ρ.re = 1 / 2) : gammaOf ρ = (ρ.im : ℂ) := by
  have e : ρ - 1 / 2 = (ρ.im : ℂ) * I := by
    apply Complex.ext <;> simp [hρ]
  rw [gammaOf, e]
  field_simp

/-- **Unconditional.** The orbit correlation of a nonzero test does not tend to `0`. -/
theorem not_tendsto_weilOrbitCorr {φ : ℝ → ℝ} (hφ : φ ∈ realTests) (hφ0 : φ ≠ 0) :
    ¬Tendsto (weilOrbitCorr φ) atTop (𝓝 0) := by
  intro hlim
  classical
  let x : ScalingCycle := (0, 0, ⟨φ, hφ⟩)
  have hcfg : ∀ t, (configScalingDatum zetaZeroConfig temperedConfig_zetaZeroConfig).orbitCorr x t =
      weilOrbitCorr φ t := fun t => by
    rw [configScalingDatum_zeta_orbitCorr, zeta_orbitCorr_eq]
  -- the correlation is bounded on the half-line
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hlim.eventually (Metric.ball_mem_nhds (0 : ℝ) one_pos))
  obtain ⟨K₁, hK₁⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := max T 0)).exists_bound_of_continuousOn
    (continuous_weilOrbitCorr hφ).continuousOn
  have hbd : ∀ t, 0 ≤ t → |weilOrbitCorr φ t| ≤ max K₁ 1 := fun t ht => by
    by_cases htT : t ≤ max T 0
    · exact (hK₁ t ⟨ht, htT⟩).trans (le_max_left _ _)
    · push Not at htT
      have h1 := hT t ((le_max_left _ _).trans htT.le)
      rw [Real.dist_eq, sub_zero] at h1
      exact h1.le.trans (le_max_right _ _)
  have hblind : BlindAbove zetaZeroConfig 0 φ :=
    blindAbove_of_orbitCorr_le zetaZeroConfig temperedConfig_zetaZeroConfig
      fesSymmetric_zetaZeroConfig le_rfl x (K := max K₁ 1) fun t ht => by
        rw [hcfg, zero_mul, Real.exp_zero, mul_one]
        exact hbd t ht
  set S : zetaZeroConfig.carrier → ℂ := fun ρ => zetaZeroConfig.Wsummand (cx φ) (cx φ) ρ with hS
  have hSsum : Summable S := summable_Wsummand zetaZeroConfig temperedConfig_zetaZeroConfig
    (cx_contDiff hφ.1) (cx_hasCompactSupport hφ.2) (cx_contDiff hφ.1) (cx_hasCompactSupport hφ.2)
  have hSoff : ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re ≠ 1 / 2 → S ρ = 0 := fun ρ hρ =>
    Wsummand_eq_zero_of_blindAbove hblind ρ.2 (abs_pos.mpr (sub_ne_zero.mpr hρ))
  have hSon : ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re = 1 / 2 →
      S ρ = (((zetaZeroConfig.mult ρ : ℝ) * ‖paperFT (cx φ) (((ρ : ℂ).im : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    intro ρ hρ
    simp only [hS, ZeroConfig.Wsummand]
    rw [gammaOf_of_re_eq_half hρ, Complex.conj_ofReal, mul_assoc, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    ring
  -- the weights
  set a : zetaZeroConfig.carrier → ℝ := fun ρ => (S ρ).re with ha
  have hSa : ∀ ρ, S ρ = (a ρ : ℂ) := fun ρ => by
    by_cases hρ : (ρ : ℂ).re = 1 / 2
    · simp only [ha, hSon ρ hρ, Complex.ofReal_re]
    · simp [ha, hSoff ρ hρ]
  have ha0 : ∀ ρ, 0 ≤ a ρ := fun ρ => by
    by_cases hρ : (ρ : ℂ).re = 1 / 2
    · simp only [ha, hSon ρ hρ, Complex.ofReal_re]
      positivity
    · simp [ha, hSoff ρ hρ]
  have hasum : Summable a := hSsum.mapL Complex.reCLM
  -- the correlation is the cosine series
  have hre : ∀ (t : ℝ) (ρ : zetaZeroConfig.carrier),
      (cexp (t * ((ρ : ℂ) - 1 / 2)) * S ρ).re = a ρ * Real.cos ((ρ : ℂ).im * t) := by
    intro t ρ
    by_cases hρ : (ρ : ℂ).re = 1 / 2
    · have e : (t : ℂ) * ((ρ : ℂ) - 1 / 2) = (((ρ : ℂ).im * t : ℝ) : ℂ) * I := by
        apply Complex.ext <;> simp [hρ]
        ring
      rw [e, hSa ρ, Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re]
      ring
    · have h0 : a ρ = 0 := by simp [ha, hSoff ρ hρ]
      rw [hSoff ρ hρ, h0]
      simp
  have hsumc : ∀ t : ℝ, Summable fun ρ : zetaZeroConfig.carrier => cexp (t * ((ρ : ℂ) - 1 / 2)) * S ρ := by
    intro t
    refine Summable.of_norm_bounded hSsum.norm fun ρ => ?_
    by_cases hρ : (ρ : ℂ).re = 1 / 2
    · rw [norm_mul, Complex.norm_exp]
      have e : ((t : ℂ) * ((ρ : ℂ) - 1 / 2)).re = 0 := by simp [hρ]
      rw [e, Real.exp_zero, one_mul]
    · rw [hSoff ρ hρ]
      simp
  have hcos : ∀ t : ℝ, weilOrbitCorr φ t = ∑' ρ : zetaZeroConfig.carrier, a ρ * Real.cos ((ρ : ℂ).im * t) := by
    intro t
    rw [← hcfg, configScalingDatum_orbitCorr_eq, Complex.re_tsum (hsumc t)]
    exact tsum_congr fun ρ => hre t ρ
  have hazero := eq_zero_of_tendsto_cos_sum ha0 hasum (g := fun ρ : zetaZeroConfig.carrier => (ρ : ℂ).im)
    (by simpa only [hcos] using (hlim.congr hcos))
  -- the transform vanishes at the real zeros of `Ξ`
  have hvan : ∀ t : ℝ, RHTower.XiC (t : ℂ) = 0 → paperFT (cx φ) t = 0 := by
    intro t ht
    rw [RHTower.CompactTestXiDivisibility.XiC_ofReal_eq_xi_linePt] at ht
    have hmem := RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_of_xi_eq_zero ht
    have hre2 : (RHTower.linePt t).re = 1 / 2 := by simp [RHTower.linePt]
    have him2 : (RHTower.linePt t).im = t := by simp [RHTower.linePt]
    have h0 := hazero ⟨_, hmem⟩
    simp only [ha] at h0
    rw [hSon ⟨_, hmem⟩ hre2, Complex.ofReal_re] at h0
    simp only [him2] at h0
    have hm : 0 < (zetaZeroConfig.mult (RHTower.linePt t) : ℝ) := by
      exact_mod_cast zetaZeroConfig.one_le_mult _ hmem
    have h1 : ‖paperFT (cx φ) (t : ℂ)‖ ^ 2 = 0 :=
      (mul_eq_zero.mp h0).resolve_left hm.ne'
    exact norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero)|>.mp h1)
  have hz := RHTower.CompactTestXiDivisibility.eq_zero_of_paperFT_eq_zero_of_XiC_eq_zero (cx_contDiff hφ.1).continuous
    (cx_hasCompactSupport hφ.2) hvan
  apply hφ0
  funext u
  have := congrFun hz u
  simpa [cx] using this

/-- **Lions' dichotomy fails on every bubble.** The energy of a dipole does not tend to the sum `2Q(φ)` of the
energies of its two bubbles. -/
theorem not_tendsto_dipole {φ : ℝ → ℝ} (hφ : φ ∈ realTests) (hφ0 : φ ≠ 0) :
    ¬Tendsto (fun t : ℝ => weilQuad (fun u => 1 * φ u + -1 * latticeTranslate φ t 1 u)) atTop
      (𝓝 (2 * weilQuad φ)) := by
  intro hlim
  have he : ∀ t : ℝ, weilQuad (fun u => 1 * φ u + -1 * latticeTranslate φ t 1 u) =
      2 * weilQuad φ - 2 * weilOrbitCorr φ t := fun t => by
    have h2 := two_mul_weilSeq_sub hφ t 1
    have h0 : weilSeq φ t 0 = weilQuad φ := by rw [weilSeq, latticeTranslate_zero]; rfl
    rw [h0, weilSeq_one] at h2
    linarith
  simp only [he] at hlim
  have h3 : Tendsto (weilOrbitCorr φ) atTop (𝓝 0) := by
    have h4 := (hlim.const_sub (2 * weilQuad φ)).div_const 2
    simpa using h4.congr fun t => by ring
  exact not_tendsto_weilOrbitCorr hφ hφ0 h3

/-- **No energy is lost at spectral infinity.** Weil's form is continuous along sequences whose zero summands are dominated and converge at each zero. -/
theorem tendsto_weilQuad_of_dominated {g : ℕ → ℝ → ℝ} {G : ℝ → ℝ} (hg : ∀ k, g k ∈ realTests)
    (hG : G ∈ realTests) {B : zetaZeroConfig.carrier → ℝ} (hB : Summable B)
    (hdom : ∀ (k : ℕ) (ρ : zetaZeroConfig.carrier),
      ‖zetaZeroConfig.Wsummand (fun u => (g k u : ℂ)) (fun u => (g k u : ℂ)) ρ‖ ≤ B ρ)
    (hpt : ∀ ρ : zetaZeroConfig.carrier,
      Tendsto (fun k => zetaZeroConfig.Wsummand (fun u => (g k u : ℂ)) (fun u => (g k u : ℂ)) ρ) atTop
        (𝓝 (zetaZeroConfig.Wsummand (fun u => (G u : ℂ)) (fun u => (G u : ℂ)) ρ))) :
    Tendsto (fun k => weilQuad (g k)) atTop (𝓝 (weilQuad G)) := by
  have h := tendsto_tsum_of_dominated_convergence hB hpt (Eventually.of_forall fun k ρ => hdom k ρ)
  have hre := Complex.continuous_re.continuousAt.tendsto.comp h
  have e : ∀ f : ℝ → ℝ, f ∈ realTests → weilQuad f =
      (∑' ρ : zetaZeroConfig.carrier, zetaZeroConfig.Wsummand (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) ρ).re :=
    fun f hf => LogCells.weilQuad_eq_zetaW hf.1 hf.2
  rw [e G hG]
  exact hre.congr fun k => (e (g k) (hg k)).symm

/-- **Recurrence replaces decoupling.** RH is the strict orbit Cauchy–Schwarz inequality together with recurrence: dipoles of mass `2‖φ‖²` have
arbitrarily small energy at arbitrarily large separation. -/
theorem riemannHypothesis_iff_orbit_recurs :
    RiemannHypothesis ↔ ∀ φ ∈ realTests, φ ≠ 0 →
      (∀ t : ℝ, t ≠ 0 → |weilOrbitCorr φ t| < weilQuad φ) ∧
      ∀ ε : ℝ, 0 < ε → ∀ T : ℝ, ∃ t, T ≤ t ∧ weilQuad (fun u => φ u - φ (u + t)) < ε ∧
        ∫ u, (φ u - φ (u + t)) ^ 2 = 2 * ∫ u, φ u ^ 2 := by
  refine ⟨fun hRH φ hφ hφ0 => ⟨fun t ht => abs_weilOrbitCorr_lt hRH hφ hφ0 ht, fun ε hε T => ?_⟩,
    fun h => riemannHypothesis_iff_abs_weilOrbitCorr_lt.mpr fun φ hφ hφ0 t ht =>
      (h φ hφ hφ0).1 t ht⟩
  obtain ⟨R, hR⟩ := hφ.2.isCompact.isBounded.subset_closedBall 0
  have hsupp : ∀ u, R < |u| → φ u = 0 := fun u hu => by
    by_contra hne
    have := hR (subset_tsupport _ hne)
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    linarith
  set h : ℝ := max T (max (2 * |R| + 1) 1) with hh
  have hh1 : 2 * |R| + 1 ≤ h := (le_max_left _ _).trans (le_max_right _ _)
  have hh2 : 1 ≤ h := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨p, hp1, hp⟩ := exists_frobeniusDiff_lt hRH hφ h hε
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp1
  have ht : h ≤ (p : ℝ) * h := by nlinarith
  refine ⟨(p : ℝ) * h, (le_max_left _ _).trans ht, ?_, ?_⟩
  · have e : (fun u => φ u - φ (u + (p : ℝ) * h)) =
        fun u => 1 * φ u + -1 * latticeTranslate φ h p u := by
      funext u
      simp only [latticeTranslate, Int.cast_natCast]
      ring
    rw [e]
    exact hp
  · set t : ℝ := (p : ℝ) * h with htd
    have htR : 2 * |R| + 1 ≤ t := hh1.trans ht
    have hcross : ∀ u, φ u * φ (u + t) = 0 := fun u => by
      by_cases hu : R < |u|
      · rw [hsupp u hu, zero_mul]
      · push Not at hu
        have hle := le_abs_self R
        have h1 : R < |u + t| := by
          have h2 := neg_abs_le u
          have h3 := abs_le.mp hu
          have h4 : u + t ≤ |u + t| := le_abs_self _
          have h5 : R ≤ |R| := le_abs_self R
          have h6 := abs_nonneg R
          linarith [h3.1, h3.2, abs_nonneg u]
        rw [hsupp _ h1, mul_zero]
    have hc : Continuous φ := ContDiff.continuous hφ.1
    have hcs : HasCompactSupport φ := hφ.2
    have hcs2 : HasCompactSupport fun u => φ u ^ 2 :=
      hcs.mono fun u hu h0 => hu (by simp [h0])
    have hint : Integrable fun u => φ u ^ 2 :=
      (hc.pow 2).integrable_of_hasCompactSupport hcs2
    have hint2 : Integrable fun u => φ (u + t) ^ 2 := hint.comp_add_right t
    have e : (fun u => (φ u - φ (u + t)) ^ 2) = fun u => φ u ^ 2 + φ (u + t) ^ 2 := by
      funext u
      have := hcross u
      nlinarith
    rw [e, integral_add hint hint2, integral_add_right_eq_self (fun u => φ u ^ 2) t]
    ring

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
