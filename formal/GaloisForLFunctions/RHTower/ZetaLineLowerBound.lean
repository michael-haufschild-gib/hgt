import GaloisForLFunctions.RHTower.ZetaLittlewoodDeficit

/-!
# An absolute lower bound for zeta near the real axis

The pole-removed function `(s-1)ζ(s)` extends continuously through `s = 1` with value one, and it
never vanishes on the closed half plane `Re s ≥ 1`.  On the compact rectangle
`1 ≤ Re s ≤ 2`, `|Im s| ≤ 1` it therefore has a positive minimum, so

```text
|ζ(1 + δ + it)| ≥ c > 0        (0 < δ ≤ 1, |t| ≤ 1),
```

with an absolute constant.  This is the low-frequency half of the polynomial-horizon antiscale
frame.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-- The pole-removed zeta factor `(s-1)ζ(s)`, with its removable value at `s = 1`. -/
def zetaPoleFactor (s : ℂ) : ℂ := if s = 1 then 1 else (s - 1) * riemannZeta s

theorem zetaPoleFactor_ne_zero {s : ℂ} (hs : 1 ≤ s.re) : zetaPoleFactor s ≠ 0 := by
  rw [zetaPoleFactor]
  split
  · exact one_ne_zero
  · rename_i hne
    exact mul_ne_zero (sub_ne_zero.mpr hne) (riemannZeta_ne_zero_of_one_le_re hs)

theorem continuousAt_zetaPoleFactor_of_ne {s : ℂ} (hs : s ≠ 1) : ContinuousAt zetaPoleFactor s := by
  have hcont : ContinuousAt (fun z : ℂ => (z - 1) * riemannZeta z) s := by
    have h1 : ContinuousAt (fun z : ℂ => z - 1) s :=
      (continuous_id.sub continuous_const).continuousAt
    have h2 : ContinuousAt riemannZeta s := (differentiableAt_riemannZeta hs).continuousAt
    exact h1.mul h2
  refine hcont.congr ?_
  filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hs)] with z hz
  rw [zetaPoleFactor, if_neg (by simpa using hz)]

theorem continuousAt_zetaPoleFactor_one : ContinuousAt zetaPoleFactor 1 := by
  have hval : zetaPoleFactor 1 = 1 := by
    rw [zetaPoleFactor, if_pos rfl]
  have hres := riemannZeta_residue_one
  have hcongr : Tendsto zetaPoleFactor (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
    refine hres.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [zetaPoleFactor, if_neg (by simpa using hs)]
  rw [ContinuousAt, hval]
  refine Filter.Tendsto.mono_left ?_ (le_of_eq (nhdsNE_sup_pure (1 : ℂ)).symm)
  rw [Filter.tendsto_sup]
  refine ⟨hcongr, ?_⟩
  rw [Filter.tendsto_pure_left]
  intro U hU
  rw [hval]
  exact mem_of_mem_nhds hU

theorem continuous_zetaPoleFactor : Continuous zetaPoleFactor := by
  rw [continuous_iff_continuousAt]
  intro s
  rcases eq_or_ne s 1 with rfl | hs
  · exact continuousAt_zetaPoleFactor_one
  · exact continuousAt_zetaPoleFactor_of_ne hs

/-- The compact rectangle carrying the low-frequency bound. -/
def zetaLowRectangle : Set ℂ := {s : ℂ | 1 ≤ s.re ∧ s.re ≤ 2 ∧ |s.im| ≤ 1}

theorem isCompact_zetaLowRectangle : IsCompact zetaLowRectangle := by
  have hclosed : IsClosed zetaLowRectangle := by
    have h1 : IsClosed {s : ℂ | 1 ≤ s.re} := isClosed_le continuous_const Complex.continuous_re
    have h2 : IsClosed {s : ℂ | s.re ≤ 2} := isClosed_le Complex.continuous_re continuous_const
    have h3 : IsClosed {s : ℂ | |s.im| ≤ 1} :=
      isClosed_le (Complex.continuous_im.abs) continuous_const
    have hset : zetaLowRectangle
        = {s : ℂ | 1 ≤ s.re} ∩ ({s : ℂ | s.re ≤ 2} ∩ {s : ℂ | |s.im| ≤ 1}) := by
      ext s
      simp only [zetaLowRectangle, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [hset]
    exact h1.inter (h2.inter h3)
  have hbounded : Bornology.IsBounded zetaLowRectangle := by
    refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 3)) ?_
    intro s hs
    obtain ⟨h1, h2, h3⟩ := hs
    have hre : |s.re| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith
    have hnorm : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbounded

theorem zetaLowRectangle_nonempty : zetaLowRectangle.Nonempty := by
  refine ⟨1, ?_⟩
  refine ⟨by simp, by simp, by simp⟩

/-- **The pole-removed factor has a positive minimum on the rectangle.** -/
theorem exists_pos_le_norm_zetaPoleFactor :
    ∃ c : ℝ, 0 < c ∧ ∀ s ∈ zetaLowRectangle, c ≤ ‖zetaPoleFactor s‖ := by
  obtain ⟨s₀, hs₀mem, hs₀min⟩ := isCompact_zetaLowRectangle.exists_isMinOn
    zetaLowRectangle_nonempty (continuous_zetaPoleFactor.norm.continuousOn)
  refine ⟨‖zetaPoleFactor s₀‖, ?_, fun s hs => hs₀min hs⟩
  have hne := zetaPoleFactor_ne_zero (s := s₀) hs₀mem.1
  exact norm_pos_iff.mpr hne

/-- **An absolute lower bound for `ζ` on the shifted line at low frequency.** -/
theorem exists_pos_le_norm_riemannZeta_low_freq :
    ∃ c : ℝ, 0 < c ∧ ∀ δ t : ℝ, 0 < δ → δ ≤ 1 → |t| ≤ 1 →
      c ≤ ‖riemannZeta (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ))‖ := by
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_norm_zetaPoleFactor
  refine ⟨c / 2, by positivity, fun δ t hδ0 hδ1 ht => ?_⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℂ, s = ((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ) := ⟨_, rfl⟩
  have hre : s.re = 1 + δ := by
    rw [hsdef]; simp
  have him : s.im = t := by
    rw [hsdef]; simp
  have hmem : s ∈ zetaLowRectangle := by
    refine ⟨by rw [hre]; linarith, by rw [hre]; linarith, by rw [him]; exact ht⟩
  have hne : s ≠ 1 := by
    intro hcon
    rw [hcon] at hre
    simp at hre
    linarith
  have hfactor : zetaPoleFactor s = (s - 1) * riemannZeta s := by
    rw [zetaPoleFactor, if_neg hne]
  have hnorm : ‖zetaPoleFactor s‖ = ‖s - 1‖ * ‖riemannZeta s‖ := by
    rw [hfactor, norm_mul]
  have hsub : ‖s - 1‖ ≤ 2 := by
    have hre' : (s - 1).re = δ := by
      rw [Complex.sub_re, hre]
      simp
    have him' : (s - 1).im = t := by
      rw [Complex.sub_im, him]
      simp
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    rw [hre', him'] at h
    have habs : |δ| = δ := abs_of_pos hδ0
    linarith [h, habs.le, habs.ge, ht]
  have hcs := hc s hmem
  rw [hnorm] at hcs
  have hzeta : 0 ≤ ‖riemannZeta s‖ := norm_nonneg _
  rw [← hsdef]
  nlinarith [hcs, hsub, hzeta, hc0]

/-! ## The polynomial-horizon antiscale frame -/

/-- The positive prime cosine sum `∑_{p ≤ x} (1 + cos(t log p))/p`. -/
def primeCosPlusSum (t x : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 + Real.cos (t * Real.log p)) / p

/-- **(Z18c) The positive sum is the pretentious distance to the Liouville character.** -/
theorem pretentiousDistSq_neg_one_eq (t x : ℝ) :
    pretentiousDistSq (fun _ => (-1 : ℂ)) (primeChar t) x = primeCosPlusSum t x := by
  rw [pretentiousDistSq, Sieve.mulDistSqPair, primeCosPlusSum]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 2
  rw [primeChar, Sieve.conj_charFn]
  have hre : ((-1 : ℂ) * Complex.exp (((-(t * Real.log p) : ℝ) : ℂ) * Complex.I)).re
      = -Real.cos (t * Real.log p) := by
    simp only [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im]
    rw [Real.cos_neg]
    ring
  rw [hre]
  ring

/-- The physical form: the squared modulus of `1 + p^{it}` is twice the local distance. -/
theorem sum_norm_one_add_primeChar_sq (t x : ℝ) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, ‖1 + primeChar t p‖ ^ 2 / p = 2 * primeCosPlusSum t x := by
  rw [primeCosPlusSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hnorm : ‖(1 : ℂ) + primeChar t p‖ ^ 2 = 2 + 2 * Real.cos (t * Real.log p) := by
    have hsq : ‖(1 : ℂ) + primeChar t p‖ ^ 2 = Complex.normSq (1 + primeChar t p) :=
      Complex.sq_norm _
    rw [hsq, Complex.normSq_apply, primeChar, Sieve.charFn]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    nlinarith [Real.sin_sq_add_cos_sq (t * Real.log p)]
  rw [hnorm]
  ring

theorem primeCosPlusSum_eq (t x : ℝ) :
    primeCosPlusSum t x = 2 * Sieve.mertensS ⌊x⌋₊ - primeClockEnergy t x := by
  rw [primeCosPlusSum, primeClockEnergy, Sieve.mertensS, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  field_simp
  ring

/-- **(Z18d) At low frequency the positive sum keeps its full harmonic size.** -/
theorem primeCosPlusSum_ge_low_freq {c : ℝ} (hc0 : 0 < c)
    (hc : ∀ δ t : ℝ, 0 < δ → δ ≤ 1 → |t| ≤ 1 →
      c ≤ ‖riemannZeta (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ))‖)
    {x t : ℝ} (hx : Real.exp 2 ≤ x) (ht : |t| ≤ 1) :
    Real.log (Real.log x) + Real.log c + 2 * Sieve.meisselMertensConst
        - (2 * ((2 * Sieve.mertensFirstConst + 1 / 2) + 1) + zetaDeficitConst)
      ≤ primeCosPlusSum t x := by
  have hexp2 : (7 : ℝ) < Real.exp 2 := by
    have h := Real.exp_one_gt_d9
    have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [h, Real.exp_pos 1, hsq]
  have hx7 : (7 : ℝ) < x := lt_of_lt_of_le hexp2 hx
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hlogx : (2 : ℝ) ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 2) hx
    rwa [Real.log_exp] at h
  have hlogx0 : (0 : ℝ) < Real.log x := by linarith
  have hδ0 : (0 : ℝ) < 1 / Real.log x := by positivity
  have hδ1 : 1 / Real.log x ≤ 1 := by
    rw [div_le_one hlogx0]
    linarith
  -- the deficit identity
  have hdef := abs_le.mp (abs_zeta_deficit_sub_primeClockEnergy_le (τ := t) (x := x) hx)
  -- Mertens' second theorem
  have hfloor2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx2)
  have hfloor6 : (6 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by
    have h : (6 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (6 : ℝ) ≤ x))
    exact_mod_cast h
  have hexp1 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hlogfloor : (1 : ℝ) ≤ Real.log ((⌊x⌋₊ : ℕ) : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ ((⌊x⌋₊ : ℕ) : ℝ) by linarith)
    rwa [Real.log_exp] at h
  have hmertens := abs_le.mp (Sieve.abs_mertensS_sub_logLog_sub_const_le hfloor2)
  have hfloorlog := abs_le.mp (abs_logLog_floor_sub_le hx)
  have hC1 : 0 ≤ 2 * Sieve.mertensFirstConst + 1 / 2 := by
    have := Sieve.mertensFirstConst_nonneg
    linarith
  have hdiv : (2 * Sieve.mertensFirstConst + 1 / 2) / Real.log ((⌊x⌋₊ : ℕ) : ℝ)
      ≤ 2 * Sieve.mertensFirstConst + 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hC1, hlogfloor]
  -- the zeta lower bound at low frequency
  have hpoint : zetaLinePoint (1 + 1 / Real.log x) t
      = ((1 + 1 / Real.log x : ℝ) : ℂ) + Complex.I * (t : ℂ) := by
    rw [zetaLinePoint]
    push_cast
    ring
  have hzeta := hc (1 / Real.log x) t hδ0 hδ1 ht
  have hlogzeta : Real.log c
      ≤ Real.log ‖riemannZeta (zetaLinePoint (1 + 1 / Real.log x) t)‖ := by
    rw [hpoint]
    exact Real.log_le_log hc0 hzeta
  rw [primeCosPlusSum_eq]
  linarith [hdef.1, hdef.2, hmertens.1, hmertens.2, hfloorlog.1, hfloorlog.2, hdiv, hlogzeta]

/-- **(Z18b) The polynomial-horizon antiscale frame.**  Uniformly over every frequency of the
horizon `|t| ≤ x^B`, the positive prime cosine sum is at least `(1/4) log log log x` up to an
absolute constant; equivalently `∑_{p ≤ x} |1 + p^{it}|²/p ≥ (1/2) log log log x - O_B(1)`. -/
theorem exists_antiscale_frame (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, ∀ x t : ℝ, zetaHorizonLogThreshold ≤ Real.log x → 0 < x → |t| ≤ x ^ B →
      (Real.log (Real.log (Real.log x)) - C) / 4 ≤ primeCosPlusSum t x := by
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_norm_riemannZeta_low_freq
  obtain ⟨Chigh, hChighdef⟩ : ∃ C : ℝ, C = Real.log (37 + littlewoodFreqThreshold
      + 24 * (B + 1) * Real.log 2) + zetaDeficitConst := ⟨_, rfl⟩
  obtain ⟨Clow, hClowdef⟩ : ∃ C : ℝ, C = 4 * ((2 * ((2 * Sieve.mertensFirstConst + 1 / 2) + 1)
      + zetaDeficitConst) - Real.log c - 2 * Sieve.meisselMertensConst) := ⟨_, rfl⟩
  refine ⟨max 0 (max Chigh Clow), fun x t hx hx0 ht => ?_⟩
  have hexp4 : (4 : ℝ) < Real.exp 4 := by
    have h := Real.add_one_le_exp (4 : ℝ)
    linarith
  have hmax4 : (4 : ℝ) ≤ max 4 (4 * Real.log 69122 + 16 * Real.log 2) := le_max_left _ _
  have hle : Real.exp (max 4 (4 * Real.log 69122 + 16 * Real.log 2)) ≤ Real.log x := by
    rw [zetaHorizonLogThreshold] at hx
    exact hx
  have hexpmono := Real.exp_le_exp.mpr hmax4
  have h4 : (4 : ℝ) ≤ Real.log x := by linarith
  have hxexp : Real.exp 2 ≤ x := by
    have hlog : Real.log (Real.exp 2) ≤ Real.log x := by
      rw [Real.log_exp]
      linarith
    have h := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log (Real.exp_pos 2), Real.exp_log hx0] at h
  have hexp2 : (7 : ℝ) < Real.exp 2 := by
    have h := Real.exp_one_gt_d9
    have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [h, Real.exp_pos 1, hsq]
  have hx7 : (7 : ℝ) < x := lt_of_lt_of_le hexp2 hxexp
  have hloglog0 : (0 : ℝ) ≤ Real.log (Real.log x) := Real.log_nonneg (by linarith)
  have hloglogpos : (0 : ℝ) < Real.log (Real.log x) := Real.log_pos (by linarith)
  have hlogloglog : Real.log (Real.log (Real.log x)) ≤ Real.log (Real.log x) := by
    have h := Real.log_le_sub_one_of_pos hloglogpos
    linarith
  rcases le_or_gt (|t|) 1 with hlow | hhigh
  · -- low frequency
    have hbound := primeCosPlusSum_ge_low_freq hc0 hc (x := x) (t := t) hxexp hlow
    have hCle : Clow ≤ max 0 (max Chigh Clow) :=
      le_trans (le_max_right Chigh Clow) (le_max_right 0 (max Chigh Clow))
    have hC0 : (0 : ℝ) ≤ max 0 (max Chigh Clow) := le_max_left _ _
    linarith [hbound, hlogloglog, hloglog0, hCle, hC0, hClowdef.le, hClowdef.ge]
  · -- Littlewood frequency
    have ht1 : (1 : ℝ) ≤ |2 * t| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
      linarith
    have htB : |2 * t| ≤ x ^ (B + 1) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
      have hx1 : (2 : ℝ) ≤ x := by linarith
      have hpow : x ^ (B + 1) = x ^ B * x := by
        rw [Real.rpow_add hx0, Real.rpow_one]
      have hxpow : (0 : ℝ) < x ^ B := Real.rpow_pos_of_pos hx0 _
      rw [hpow]
      nlinarith [ht, hxpow, hx1]
    have hr : ∀ n : ℕ, |(-1 : ℝ)| ≤ 1 := by
      intro n
      rw [abs_neg, abs_one]
    have htransfer := quarter_littlewoodDeficit_le_pretentiousDistSq (r := fun _ => (-1 : ℝ))
      hr (B := B + 1) (x := x) (α := t) (by linarith) hx hx0 ht1 htB
    have hfun : (fun n : ℕ => (((-1 : ℝ) : ℂ))) = (fun _ : ℕ => (-1 : ℂ)) := by
      funext n
      push_cast
      ring
    rw [hfun, pretentiousDistSq_neg_one_eq] at htransfer
    have hCle : Chigh ≤ max 0 (max Chigh Clow) :=
      le_trans (le_max_left Chigh Clow) (le_max_right 0 (max Chigh Clow))
    have hstep : (Real.log (Real.log (Real.log x)) - max 0 (max Chigh Clow)) / 4
        ≤ (Real.log (Real.log (Real.log x))
            - Real.log (37 + littlewoodFreqThreshold + 24 * (B + 1) * Real.log 2)
            - zetaDeficitConst) / 4 := by
      have hnum : Real.log (Real.log (Real.log x)) - max 0 (max Chigh Clow)
          ≤ Real.log (Real.log (Real.log x))
            - Real.log (37 + littlewoodFreqThreshold + 24 * (B + 1) * Real.log 2)
            - zetaDeficitConst := by
        linarith [hCle, hChighdef.le, hChighdef.ge]
      exact div_le_div_of_nonneg_right hnum (by norm_num : (0:ℝ) ≤ 4)
    linarith [hstep, htransfer]

end

end RHTower
