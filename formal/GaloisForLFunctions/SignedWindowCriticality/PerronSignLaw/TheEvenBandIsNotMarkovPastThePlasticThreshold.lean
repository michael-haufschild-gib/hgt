import GaloisForLFunctions.SignedWindowCriticality.PerronSignLaw.ThePerronMarginIsBoundedByThePoleSaturationGap

/-!
# The even band is not Markov past the plastic threshold

`evenKernel_neg_of_threshold_lt` makes the even kernel `ω(|u − v|) + ω(−u − v) − 4cosh(u/2)cosh(v/2)`
negative at the pair (window edge, centre) once `c > t_* = log ρ`. Here the pointwise sign becomes a
failure of the Beurling–Deny property of the band form itself, uniformly in the pole strength and
in the prime weights.

* `evenPoleBand_lt_of_bumps` — let `a ≥ 0` live in `(−c, −c + r)` (edge) and `b ≥ 0` in `(−r, 0)`
  (centre), `4r ≤ c`, `2r ≤ log 2 − c`. In kernel form
  `E_s(a + b) − E_s(a − b) ≥ 4(∫a)(∫b)[4s·cosh((c − r)/2) − ω(c − 2r) − ω(c − r)]`: the pole pays
  at least `4s·cosh((c − r)/2)` on the pair, the Lévy jumps return at most `ω(c − 2r)` (no lag
  below `c − 2r` joins opposite signs), the trivial-zero squares at most `ω(c − r)`, and no prime
  reflection `u ↦ −log n − u` joins the two bumps.
* `exists_evenPoleBand_lt_abs` — for `t_* < c < log 2`, all weights `w₂, w₃` and every pole strength
  `s ≥ 1` (pole `κ ≥ 4`) there is a smooth test `f` vanishing off `[−c, 0]`, positive at the edge and
  negative at the centre, with `E_s(f) < E_s(|f|)`.
* `evenBand_markov_iff` — **sharp Markov range**: for `0 ≤ c < log 2` and nonnegative weights the
  arithmetic even band satisfies `E(|f|) ≤ E(f)` on every `C²` half-window test iff `c ≤ t_*`.

So Beurling–Deny comparison and kernel domination give Perron in the even sector exactly up to
`t_*`, at every pole strength `≥ 4` and for every choice of prime weights.
-/

open Real MeasureTheory Set Filter Topology
open scoped ContDiff
open _root_.RHTower

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality.PerronSignLaw

open GaloisForLFunctions.SignedWindowCriticality
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.RHTower (screwSignThreshold)
open SpacingScaleHarmonicAnalysis

/-! ### 1. A radius for the frustrated pair -/

lemma levyDensity_continuousAt {x : ℝ} (hx : 0 < x) : ContinuousAt archLevyDensity x := by
  have h2 : 1 - Real.exp (-2 * x) ≠ 0 := by
    have : Real.exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  show ContinuousAt (fun y => Real.exp (-y / 2) / (1 - Real.exp (-2 * y))) x
  exact ((by fun_prop : Continuous fun y : ℝ => Real.exp (-y / 2)).continuousAt).div
    ((by fun_prop : Continuous fun y : ℝ => 1 - Real.exp (-2 * y)).continuousAt) h2

/-- A radius `r` for the two bumps: they fit in the window apart from each other, no prime
reflection joins them, and the kernel stays negative across them. -/
lemma exists_bumpRadius {c : ℝ} (hc0 : 0 < c) (hc : c < Real.log 2)
    (hk : archLevyDensity c + archLevyDensity c < 4 * Real.cosh (c / 2)) :
    ∃ r, 0 < r ∧ 4 * r ≤ c ∧ 2 * r ≤ Real.log 2 - c ∧
      archLevyDensity (c - 2 * r) + archLevyDensity (c - r) < 4 * Real.cosh ((c - r) / 2) := by
  set φ : ℝ → ℝ := fun r =>
    4 * Real.cosh ((c - r) / 2) - archLevyDensity (c - 2 * r) - archLevyDensity (c - r) with hφ
  have hcont : ContinuousAt φ 0 := by
    have h1 : ContinuousAt (fun r : ℝ => archLevyDensity (c - 2 * r)) 0 :=
      (levyDensity_continuousAt hc0).comp_of_eq (f := fun r : ℝ => c - 2 * r) (by fun_prop)
        (by norm_num)
    have h2 : ContinuousAt (fun r : ℝ => archLevyDensity (c - r)) 0 :=
      (levyDensity_continuousAt hc0).comp_of_eq (f := fun r : ℝ => c - r) (by fun_prop)
        (by norm_num)
    exact ((by fun_prop : Continuous fun r : ℝ => 4 * Real.cosh ((c - r) / 2)).continuousAt.sub
      h1).sub h2
  have h0 : 0 < φ 0 := by
    simp only [hφ, mul_zero, sub_zero]
    linarith
  obtain ⟨ε, hε, hball⟩ :=
    Metric.eventually_nhds_iff.mp (Filter.Tendsto.eventually hcont (lt_mem_nhds h0))
  have hlog : 0 < Real.log 2 - c := by linarith
  set r := min (ε / 2) (min (c / 4) ((Real.log 2 - c) / 2)) with hr
  have hr1 : r ≤ ε / 2 := min_le_left _ _
  have hr2 : r ≤ c / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hr3 : r ≤ (Real.log 2 - c) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hr0 : 0 < r := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  refine ⟨r, hr0, by linarith, by linarith, ?_⟩
  have hφr : 0 < φ r := hball (by rw [Real.dist_eq, sub_zero, abs_of_pos hr0]; linarith)
  simp only [hφ] at hφr
  linarith

/-! ### 2. Bumps -/

/-- A smooth bump `φ ≥ 0` with `∫ φ > 0` vanishing off `(x₀ − R, x₀ + R)`. -/
lemma exists_bump (x₀ : ℝ) {R : ℝ} (hR : 0 < R) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧ (∀ u, 0 ≤ φ u) ∧
      0 < ∫ u, φ u ∧ ∀ u, φ u ≠ 0 → x₀ - R < u ∧ u < x₀ + R := by
  let φ : ContDiffBump x₀ := ⟨R / 2, R, by positivity, by linarith⟩
  refine ⟨φ, φ.contDiff, φ.contDiff, φ.hasCompactSupport, φ.nonneg', φ.integral_pos,
    fun u hu => ?_⟩
  have h : u ∈ Function.support φ := hu
  rw [φ.support_eq, Metric.mem_ball, Real.dist_eq, abs_lt] at h
  have hR' : φ.rOut = R := rfl
  rw [hR'] at h
  constructor <;> linarith [h.1, h.2]

/-! ### 3. The two-bump comparison -/

/-- **The frustrated pair breaks the contraction.** For bumps `a ≥ 0` in `(−c, −c + r)` and
`b ≥ 0` in `(−r, 0)` with `4r ≤ c`, `2r ≤ log 2 − c`, `ω(c − 2r) + ω(c − r) < 4cosh((c − r)/2)`
and pole strength `s ≥ 1`: `E_s(a − b) < E_s(a + b)` for all weights. -/
theorem evenPoleBand_lt_of_bumps {c r : ℝ} (hc0 : 0 < c) (hc : c < Real.log 2) (hr0 : 0 < r)
    (hr4 : 4 * r ≤ c) (hrl : 2 * r ≤ Real.log 2 - c)
    (hkr : archLevyDensity (c - 2 * r) + archLevyDensity (c - r) < 4 * Real.cosh ((c - r) / 2))
    {a b : ℝ → ℝ} (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b) (hac : HasCompactSupport a)
    (hbc : HasCompactSupport b) (ha0 : ∀ u, 0 ≤ a u) (hb0 : ∀ u, 0 ≤ b u)
    (hapos : 0 < ∫ u, a u) (hbpos : 0 < ∫ u, b u)
    (has : ∀ u, a u ≠ 0 → -c < u ∧ u < -c + r) (hbs : ∀ u, b u ≠ 0 → -r < u ∧ u < 0)
    (w₂ w₃ : ℝ) {s : ℝ} (hs : 1 ≤ s) :
    evenPoleBand w₂ w₃ s (fun u => a u - b u) < evenPoleBand w₂ w₃ s (fun u => a u + b u) := by
  set f : ℝ → ℝ := fun u => a u - b u with hf_def
  set G : ℝ → ℝ := fun u => a u + b u with hG_def
  set α := ∫ u, a u with hα
  set β := ∫ u, b u with hβ
  have hca : Continuous a := ha.continuous
  have hcb : Continuous b := hb.continuous
  -- supports
  have haz : ∀ u, (u ≤ -c ∨ -c + r ≤ u) → a u = 0 := fun u hu => by
    by_contra h
    have := has u h
    rcases hu with hu | hu <;> linarith [this.1, this.2]
  have hbz : ∀ u, (u ≤ -r ∨ 0 ≤ u) → b u = 0 := fun u hu => by
    by_contra h
    have := hbs u h
    rcases hu with hu | hu <;> linarith [this.1, this.2]
  have hdisj : ∀ u, a u = 0 ∨ b u = 0 := fun u => by
    by_cases h : a u = 0
    · exact Or.inl h
    · exact Or.inr (hbz u (Or.inl (by linarith [(has u h).2])))
  have habs : (fun u => |f u|) = G := by
    funext u
    simp only [hf_def, hG_def]
    rcases hdisj u with h | h
    · rw [h, zero_sub, zero_add, abs_neg, abs_of_nonneg (hb0 u)]
    · rw [h, sub_zero, add_zero, abs_of_nonneg (ha0 u)]
  have hf2 : ContDiff ℝ 2 f := ha.sub hb
  have hG2 : ContDiff ℝ 2 G := ha.add hb
  have hfc : HasCompactSupport f := hac.sub hbc
  have hGc : HasCompactSupport G := hac.add hbc
  have hf0 : ∀ u, 0 < u → f u = 0 := fun u hu => by
    simp only [hf_def, haz u (Or.inr (by linarith)), hbz u (Or.inr hu.le), sub_zero]
  have hfl : ∀ u, u < -c → f u = 0 := fun u hu => by
    simp only [hf_def, haz u (Or.inl hu.le), hbz u (Or.inl (by linarith)), sub_zero]
  have hG0 : ∀ u, 0 < u → G u = 0 := fun u hu => by
    simp only [hG_def, haz u (Or.inr (by linarith)), hbz u (Or.inr hu.le), add_zero]
  have hGl : ∀ u, u < -c → G u = 0 := fun u hu => by
    simp only [hG_def, haz u (Or.inl hu.le), hbz u (Or.inl (by linarith)), add_zero]
  have hfs : ∀ x, c < |x| → f x = 0 := fun x hx => by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h] at hx; exact hf0 x (by linarith)
    · rw [abs_of_neg h] at hx; exact hfl x (by linarith)
  have hIa : Integrable a := hca.integrable_of_hasCompactSupport hac
  have hIb : Integrable b := hcb.integrable_of_hasCompactSupport hbc
  -- signs of `f`: positive only at the edge, negative only at the centre
  have hfpos : ∀ u, 0 < f u → u < -c + r := fun u hu => by
    have : a u ≠ 0 := fun h => by
      simp only [hf_def, h, zero_sub] at hu; linarith [hb0 u]
    exact (has u this).2
  have hfneg : ∀ u, f u < 0 → -r < u := fun u hu => by
    have : b u ≠ 0 := fun h => by
      simp only [hf_def, h, sub_zero] at hu; linarith [ha0 u]
    exact (hbs u this).1
  /- The pole: `P(a + b) − P(a − b) = 4(∫ah)(∫bh) ≥ 16cosh((c − r)/2) αβ`. -/
  have hcw : Continuous coshWeight := by unfold coshWeight; fun_prop
  have hIah : Integrable fun u => a u * coshWeight u :=
    (hca.mul hcw).integrable_of_hasCompactSupport (hac.mono fun u hu h0 => hu (by simp [h0]))
  have hIbh : Integrable fun u => b u * coshWeight u :=
    (hcb.mul hcw).integrable_of_hasCompactSupport (hbc.mono fun u hu h0 => hu (by simp [h0]))
  set κ := Real.cosh ((c - r) / 2) with hκ
  have hκ0 : 0 < κ := Real.cosh_pos _
  have hAh : 2 * κ * α ≤ ∫ u, a u * coshWeight u := by
    rw [hα, ← integral_const_mul]
    refine integral_mono (hIa.const_mul _) hIah fun u => ?_
    show 2 * κ * a u ≤ a u * coshWeight u
    by_cases h : a u = 0
    · rw [h]; simp
    have hu := has u h
    have hcosh : κ ≤ Real.cosh (u / 2) := by
      rw [hκ, Real.cosh_le_cosh, abs_of_pos (by linarith), abs_of_neg (by linarith)]
      linarith [hu.2]
    unfold coshWeight
    nlinarith [ha0 u]
  have hBh : 2 * β ≤ ∫ u, b u * coshWeight u := by
    rw [hβ, ← integral_const_mul]
    refine integral_mono (hIb.const_mul _) hIbh fun u => ?_
    show 2 * b u ≤ b u * coshWeight u
    have : 2 ≤ coshWeight u := by unfold coshWeight; linarith [Real.one_le_cosh (u / 2)]
    nlinarith [hb0 u]
  have hPG : (∫ u, G u * coshWeight u) =
      (∫ u, a u * coshWeight u) + ∫ u, b u * coshWeight u := by
    rw [← integral_add hIah hIbh]
    exact integral_congr_ae (Eventually.of_forall fun u => by simp only [hG_def]; ring)
  have hPf : (∫ u, f u * coshWeight u) =
      (∫ u, a u * coshWeight u) - ∫ u, b u * coshWeight u := by
    rw [← integral_sub hIah hIbh]
    exact integral_congr_ae (Eventually.of_forall fun u => by simp only [hf_def]; ring)
  have hpole : 16 * κ * (α * β) ≤ poleSquare G - poleSquare f := by
    unfold poleSquare
    rw [hPG, hPf]
    have h1 : 0 ≤ 2 * κ * α := by positivity
    have h2 := mul_le_mul hAh hBh (by positivity) (h1.trans hAh)
    nlinarith [h2]
  have hpole0 : 0 ≤ poleSquare G - poleSquare f := le_trans (by positivity) hpole
  /- The trivial-zero squares: `Σ_j (ν_j(a + b)² − ν_j(a − b)²) ≤ 4 ω(c − r) αβ`. -/
  have hew (j : ℕ) : Continuous (expWeight j) := by unfold expWeight; fun_prop
  have hIae (j : ℕ) : Integrable fun u => a u * expWeight j u :=
    (hca.mul (hew j)).integrable_of_hasCompactSupport (hac.mono fun u hu h0 => hu (by simp [h0]))
  have hIbe (j : ℕ) : Integrable fun u => b u * expWeight j u :=
    (hcb.mul (hew j)).integrable_of_hasCompactSupport (hbc.mono fun u hu h0 => hu (by simp [h0]))
  have hνG (j : ℕ) : expMoment G j = expMoment a j + expMoment b j := by
    unfold expMoment
    rw [← integral_add (hIae j) (hIbe j)]
    exact integral_congr_ae (Eventually.of_forall fun u => by simp only [hG_def]; ring)
  have hνf (j : ℕ) : expMoment f j = expMoment a j - expMoment b j := by
    unfold expMoment
    rw [← integral_sub (hIae j) (hIbe j)]
    exact integral_congr_ae (Eventually.of_forall fun u => by simp only [hf_def]; ring)
  have hνa0 (j : ℕ) : 0 ≤ expMoment a j :=
    integral_nonneg fun u => mul_nonneg (ha0 u) (by unfold expWeight; positivity)
  have hνb0 (j : ℕ) : 0 ≤ expMoment b j :=
    integral_nonneg fun u => mul_nonneg (hb0 u) (by unfold expWeight; positivity)
  have hνa (j : ℕ) : expMoment a j ≤
      α * Real.exp (-((2 * (j : ℝ) + 1 / 2) * (c - r))) := by
    rw [hα, ← integral_mul_const]
    refine integral_mono (hIae j) (hIa.mul_const _) fun u => ?_
    show a u * expWeight j u ≤ a u * Real.exp (-((2 * (j : ℝ) + 1 / 2) * (c - r)))
    by_cases h : a u = 0
    · rw [h]; simp
    have hu := has u h
    have hj : (0 : ℝ) ≤ 2 * (j : ℝ) + 1 / 2 := by positivity
    refine mul_le_mul_of_nonneg_left ?_ (ha0 u)
    unfold expWeight
    exact Real.exp_le_exp.mpr (by nlinarith [hu.2])
  have hνb (j : ℕ) : expMoment b j ≤ β := by
    rw [hβ]
    refine integral_mono (hIbe j) hIb fun u => ?_
    show b u * expWeight j u ≤ b u
    by_cases h : b u = 0
    · rw [h]; simp
    have hu := hbs u h
    have hj : (0 : ℝ) ≤ 2 * (j : ℝ) + 1 / 2 := by positivity
    have he : expWeight j u ≤ 1 := by
      unfold expWeight
      exact Real.exp_le_one_iff.mpr (by nlinarith [hu.2])
    nlinarith [hb0 u]
  obtain ⟨Bf, hBf⟩ : ∃ B, ∀ u, |f u| ≤ B := by
    obtain ⟨B, hB⟩ := hfc.exists_bound_of_continuous hf2.continuous
    exact ⟨B, fun u => by simpa [Real.norm_eq_abs] using hB u⟩
  obtain ⟨BG, hBG⟩ : ∃ B, ∀ u, |G u| ≤ B := by
    obtain ⟨B, hB⟩ := hGc.exists_bound_of_continuous hG2.continuous
    exact ⟨B, fun u => by simpa [Real.norm_eq_abs] using hB u⟩
  have hSf := summable_expMoment_sq hc0.le hBf hf0 hfl
  have hSG := summable_expMoment_sq hc0.le hBG hG0 hGl
  have hcr : 0 < c - r := by linarith
  have hmom : (∑' j, expMoment G j ^ 2) - (∑' j, expMoment f j ^ 2) ≤
      4 * (α * β) * archLevyDensity (c - r) := by
    rw [← hSG.tsum_sub hSf, archLevyDensity_eq_tsum hcr, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun j => ?_) (hSG.sub hSf)
      ((summable_levyModes hcr).mul_left _)
    rw [hνG, hνf]
    have h := mul_le_mul (hνa j) (hνb j) (hνb0 j) (by positivity)
    nlinarith [h]
  /- The Lévy jumps: `𝒥(a − b) − 𝒥(a + b) ≤ 4 ω(c − 2r) αβ`. -/
  have hJf := integrableOn_biScaleLevyIntegrand hf2 hfc
  have hJg := integrableOn_levy_abs hf2.continuous hfc hJf
  have hlevy := levy_sub_eq hJf hJg
  have h00 : autocorr (fun u => |f u|) 0 = autocorr f 0 := by
    unfold autocorr; simp only [add_zero, abs_mul_abs_self]
  have hgs : ∀ x, c < |x| → |f x| = 0 := fun x hx => by rw [hfs x hx, abs_zero]
  have hIAg := integrable_autocorr' (G := fun u => |f u|) hf2.continuous.abs hgs
  have hIAf := integrable_autocorr' hf2.continuous hfs
  have hD0 : ∀ x, 0 < x → x ≤ c - 2 * r →
      autocorr (fun u => |f u|) x - autocorr f x = 0 := fun x hx hxr => by
    rw [← integral_pairDefect_shift' hf2.continuous hfc x]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun u => ?_)
    show pairDefect f u (u + x) = 0
    by_contra h
    rcases mul_neg_iff.mp (mul_neg_of_pairDefect_ne_zero h) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith [hfpos u h1, hfneg (u + x) h2]
    · linarith [hfneg u h2, hfpos (u + x) h1]
  have hDnn : ∀ x, 0 ≤ autocorr (fun u => |f u|) x - autocorr f x := fun x => by
    rw [← integral_pairDefect_shift' hf2.continuous hfc x]
    exact integral_nonneg fun u => pairDefect_nonneg f u (u + x)
  have hI1 : IntegrableOn (fun x => archLevyDensity x *
      (autocorr (fun u => |f u|) x - autocorr f x)) (Ioi 0) := by
    have h := (hJf.sub hJg).const_mul (1 / 2 : ℝ)
    refine IntegrableOn.congr_fun h (fun x hx => ?_) measurableSet_Ioi
    show (1 / 2 : ℝ) * ((autocorr f 0 - autocorr f x) * archLevySinhWeight x -
        (autocorr (fun u => |f u|) 0 - autocorr (fun u => |f u|) x) * archLevySinhWeight x) =
      archLevyDensity x * (autocorr (fun u => |f u|) x - autocorr f x)
    rw [archLevySinhWeight, exp_half_div_sinh_eq hx, h00]
    ring
  have hI2 : IntegrableOn (fun x => archLevyDensity (c - 2 * r) *
      (autocorr (fun u => |f u|) x - autocorr f x)) (Ioi 0) :=
    ((hIAg.sub hIAf).const_mul _).integrableOn
  have hc2r : 0 < c - 2 * r := by linarith
  have hJbound : (∫ x in Ioi (0 : ℝ), archLevyDensity x *
      (autocorr (fun u => |f u|) x - autocorr f x)) ≤
      archLevyDensity (c - 2 * r) *
        ∫ x in Ioi (0 : ℝ), (autocorr (fun u => |f u|) x - autocorr f x) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on hI1 hI2 measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := hx
    rcases le_or_gt x (c - 2 * r) with hxr | hxr
    · rw [hD0 x hx0 hxr, mul_zero, mul_zero]
    · exact mul_le_mul_of_nonneg_right
        (strictAntiOn_archLevyDensity_Ioi.antitoneOn hc2r hx0 hxr.le) (hDnn x)
  have hmass : (∫ x in Ioi (0 : ℝ), (autocorr (fun u => |f u|) x - autocorr f x)) =
      2 * (α * β) := by
    rw [integral_sub hIAg.integrableOn hIAf.integrableOn]
    have e1 := sq_integral_eq_two_mul_integral_autocorr (G := fun u => |f u|)
      hf2.continuous.abs hfc.abs
    have e2 := sq_integral_eq_two_mul_integral_autocorr hf2.continuous hfc
    have i1 : (∫ u, |f u|) = α + β := by
      rw [habs, hα, hβ, ← integral_add hIa hIb]
    have i2 : (∫ u, f u) = α - β := by
      rw [hα, hβ, ← integral_sub hIa hIb]
    rw [i1] at e1
    rw [i2] at e2
    nlinarith [e1, e2]
  have hlev : biScaleLevyEnergy f - biScaleLevyEnergy G ≤
      4 * (α * β) * archLevyDensity (c - 2 * r) := by
    rw [← habs, hlevy]
    rw [hmass] at hJbound
    nlinarith [hJbound]
  /- No prime reflection joins the two bumps. -/
  have hab : ∀ u v, u + v ≤ -(c + r) → a u * b v = 0 := fun u v huv => by
    by_contra h
    have h1 := has u (left_ne_zero_of_mul h)
    have h2 := hbs v (right_ne_zero_of_mul h)
    linarith [h1.1, h2.1]
  have hprime : ∀ t, t ≤ -(c + r) → selfConv G t = selfConv f t := fun t ht => by
    unfold selfConv
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    have h1 := hab u (t - u) (by linarith)
    have h2 := hab (t - u) u (by linarith)
    simp only [hf_def, hG_def]
    linear_combination 2 * h1 + 2 * h2
  have hlog3 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  have hp2 := hprime (-Real.log 2) (by linarith)
  have hp3 := hprime (-Real.log 3) (by linarith)
  have hA0 : autocorr G 0 = autocorr f 0 := by rw [← habs]; exact h00
  /- Assemble in kernel form. -/
  have hJG := integrableOn_biScaleLevyIntegrand hG2 hGc
  have eG := evenSector_eq hG2.continuous hc0.le hc hG0 hGl hJG
  have ef := evenSector_eq hf2.continuous hc0.le hc hf0 hfl hJf
  have hαβ : 0 < α * β := mul_pos hapos hbpos
  have hker : 4 * (α * β) * (archLevyDensity (c - 2 * r) + archLevyDensity (c - r)) <
      16 * κ * (α * β) := by
    nlinarith [mul_lt_mul_of_pos_left hkr hαβ]
  have hspole : poleSquare G - poleSquare f ≤ s * (poleSquare G - poleSquare f) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) hpole0]
  show evenPoleBand w₂ w₃ s f < evenPoleBand w₂ w₃ s G
  unfold evenPoleBand
  rw [hp2, hp3]
  unfold poleSquare at hpole hspole
  linarith

/-! ### 4. The even band is not Markov past `t_*` -/

/-- **The even band is not Markov past the plastic threshold.** For `t_* < c < log 2`, all weights
and every pole strength `s ≥ 1` there is a smooth test `f` vanishing off `[−c, 0]` — positive at the
window edge, negative at the centre — with `E_s(f) < E_s(|f|)`; `|f|` is smooth as well. -/
theorem exists_evenPoleBand_lt_abs {c : ℝ} (hct : screwSignThreshold < c) (hc : c < Real.log 2)
    (w₂ w₃ : ℝ) {s : ℝ} (hs : 1 ≤ s) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ (fun u => |f u|) ∧ ContDiff ℝ 2 f ∧
      (∀ u, 0 < u → f u = 0) ∧ (∀ u, u < -c → f u = 0) ∧
      evenPoleBand w₂ w₃ s f < evenPoleBand w₂ w₃ s (fun u => |f u|) := by
  have ht0 : 0 < screwSignThreshold := lt_trans (by norm_num) screwSignThreshold_gt
  have hc0 : 0 < c := lt_trans ht0 hct
  have hk : archLevyDensity c + archLevyDensity c < 4 * Real.cosh (c / 2) := by
    have h := evenKernel_neg_of_threshold_lt hct
    rwa [sub_zero, add_zero, abs_of_pos hc0, zero_div, Real.cosh_zero, mul_one] at h
  obtain ⟨r, hr0, hr4, hrl, hkr⟩ := exists_bumpRadius hc0 hc hk
  obtain ⟨a, ha, ha2, hac, ha0, hapos, has⟩ := exists_bump (-c + r / 2) (R := r / 2) (by positivity)
  obtain ⟨b, hb, hb2, hbc, hb0, hbpos, hbs⟩ := exists_bump (-(r / 2)) (R := r / 2) (by positivity)
  have has' : ∀ u, a u ≠ 0 → -c < u ∧ u < -c + r := fun u h => by
    have := has u h; constructor <;> linarith [this.1, this.2]
  have hbs' : ∀ u, b u ≠ 0 → -r < u ∧ u < 0 := fun u h => by
    have := hbs u h; constructor <;> linarith [this.1, this.2]
  have hdisj : ∀ u, a u = 0 ∨ b u = 0 := fun u => by
    by_cases h : a u = 0
    · exact Or.inl h
    · by_contra hb'
      push_neg at hb'
      linarith [(has' u h).2, (hbs' u hb'.2).1]
  have habs : (fun u => |a u - b u|) = fun u => a u + b u := by
    funext u
    rcases hdisj u with h | h
    · rw [h, zero_sub, zero_add, abs_neg, abs_of_nonneg (hb0 u)]
    · rw [h, sub_zero, add_zero, abs_of_nonneg (ha0 u)]
  have hlt := evenPoleBand_lt_of_bumps hc0 hc hr0 hr4 hrl hkr ha2 hb2 hac hbc ha0 hb0 hapos hbpos
    has' hbs' w₂ w₃ hs
  refine ⟨fun u => a u - b u, ha.sub hb, ?_, ha2.sub hb2, fun u hu => ?_, fun u hu => ?_, ?_⟩
  · rw [habs]; exact ha.add hb
  · have h1 : a u = 0 := by
      by_contra h; linarith [(has' u h).2]
    have h2 : b u = 0 := by
      by_contra h; linarith [(hbs' u h).2]
    simp [h1, h2]
  · have h1 : a u = 0 := by
      by_contra h; linarith [(has' u h).1]
    have h2 : b u = 0 := by
      by_contra h; linarith [(hbs' u h).1]
    simp [h1, h2]
  · rw [habs]; exact hlt

/-- **Sharp Markov range of the even band.** For `0 ≤ c < log 2` and nonnegative weights the
arithmetic even band `E = W + 𝓗₀ − w₂(f⋆f)(−log 2) − w₃(f⋆f)(−log 3)` satisfies `E(|f|) ≤ E(f)` for
every `C²` test vanishing off `[−c, 0]` iff `c ≤ t_*`. -/
theorem evenBand_markov_iff {c : ℝ} (hc0 : 0 ≤ c) (hc : c < Real.log 2) {w₂ w₃ : ℝ}
    (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃) :
    (∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -c → f u = 0) →
      evenPoleBand w₂ w₃ 1 (fun u => |f u|) ≤ evenPoleBand w₂ w₃ 1 f) ↔
      c ≤ screwSignThreshold := by
  constructor
  · intro h
    by_contra hct
    push_neg at hct
    obtain ⟨f, -, -, hf2, hf0, hfl, hlt⟩ := exists_evenPoleBand_lt_abs hct hc w₂ w₃ le_rfl
    exact absurd (h f hf2 hf0 hfl) (not_le.mpr hlt)
  · intro hct f hf h0 hl
    rw [evenPoleBand_one, evenPoleBand_one]
    exact evenBand_abs_le_of_frustrationFree hc0 hc hf h0 hl
      (evenFrustrationFree_of_le_threshold hct h0 hl) hw₂ hw₃

end GaloisForLFunctions.SignedWindowCriticality.PerronSignLaw

end
