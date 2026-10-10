import GaloisForLFunctions.RHTower.RayPolylogMultiplicity
import GaloisForLFunctions.RHTower.RieszFunctionExponentLaw

/-!
# Strict polylogarithmic multiplicity for Riesz's criterion

Riesz's function `F(x) = x R(x)`, `R(x) = Σ μ(n) n^{-2} e^{-x/n²}`, satisfies
`F(x) = O(x^{¼+ε})` for every `ε > 0` iff RH (`riemannHypothesis_iff_rieszFunction_le`). It is a
`1/ζ`-type receiver: `∫_0^∞ R(t) t^{s-1} dt · (w - 1)ζ(w) = Γ(s)(1 - 2s)` with `w = 2 - 2s`, so a
zero of order `m` at `ρ` is a pole of order `m` of the transform at `s = 1 - ρ/2`. Hence the
logarithmic forms grade multiplicity strictly:

* if `|F(x)| ≤ ε x^{¼} (1 + log x)^a` for `x ≥ T_ε`, for every `ε > 0`, then RH holds and every
  critical zero has order `< a + 1` (`riemannHypothesis_and_order_lt_of_rieszLittleO`);
* for `a ≤ 1` this is RH ∧ all critical zeros simple;
* `F(x) ≠ o(x^{¼})`, unconditionally (`not_rieszLittleO_zero`), since Hardy's theorem supplies a
  critical zero.

**Proof.** The transform continues to `0 < Re s < ¾`, where the identity holds by the identity
theorem. Along `s = 1 - ρ/2 - r`, the part over `(0, 1)` stays bounded, and the part over `(1, ∞)`
is `∫_1^∞ t^{-(1-s)-1} F(t) dt`, bounded by `η r^{-(a+1)} + C_η`
(`norm_integral_Ioi_one_cpow_mul_le`). The ray lemma `natCast_lt_of_ray_littleO` then caps the order.
-/

open Complex Filter Topology MeasureTheory Set

namespace RHTower

noncomputable section

/-- `F(x) = o(x^{¼}(1 + log x)^a)`, in explicit form. -/
def RieszLittleO (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 1 ≤ T ∧ ∀ x : ℝ, T ≤ x →
    |rieszFunction x| ≤ ε * x ^ (1 / 4 : ℝ) * (1 + Real.log x) ^ a

/-- `S = Σ 1/n²` bounds `R` on `[0, ∞)`. -/
def rieszBound : ℝ := ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹

theorem rieszBound_nonneg : 0 ≤ rieszBound :=
  tsum_nonneg fun _ => inv_nonneg.mpr (sq_nonneg _)

theorem abs_rieszFunction_le_mul {x : ℝ} (hx : 0 ≤ x) : |rieszFunction x| ≤ x * rieszBound := by
  rw [rieszFunction, abs_mul, abs_of_nonneg hx]
  exact mul_le_mul_of_nonneg_left (abs_rieszSeries_le hx) hx

/-- A global polylog bound from the eventual one. -/
theorem exists_abs_rieszFunction_le_global {a : ℝ} (ha : 0 ≤ a) (h : RieszLittleO a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x →
      |rieszFunction x| ≤ B * x ^ (1 / 4 : ℝ) * (1 + Real.log x) ^ a := by
  obtain ⟨T, hT1, hT⟩ := h 1 one_pos
  refine ⟨max 1 (T * rieszBound), le_max_of_le_left zero_le_one, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hw : 1 ≤ x ^ (1 / 4 : ℝ) * (1 + Real.log x) ^ a :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hx (by norm_num))
      (Real.one_le_rpow (by linarith [Real.log_nonneg hx]) ha)
  rcases le_or_gt T x with hTx | hxT
  · calc |rieszFunction x| ≤ 1 * x ^ (1 / 4 : ℝ) * (1 + Real.log x) ^ a := hT x hTx
      _ ≤ max 1 (T * rieszBound) * x ^ (1 / 4 : ℝ) * (1 + Real.log x) ^ a := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · calc |rieszFunction x| ≤ x * rieszBound := abs_rieszFunction_le_mul hx0
      _ ≤ T * rieszBound := mul_le_mul_of_nonneg_right hxT.le rieszBound_nonneg
      _ ≤ max 1 (T * rieszBound) := le_max_right _ _
      _ = max 1 (T * rieszBound) * 1 := (mul_one _).symm
      _ ≤ max 1 (T * rieszBound) * (x ^ (1 / 4 : ℝ) * (1 + Real.log x) ^ a) :=
          mul_le_mul_of_nonneg_left hw (le_max_of_le_left zero_le_one)
      _ = _ := by ring

theorem riemannHypothesis_of_rieszLittleO {a : ℝ} (ha : 0 ≤ a) (h : RieszLittleO a) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_rieszFunction_le]
  intro ε hε
  obtain ⟨B, hB0, hB⟩ := exists_abs_rieszFunction_le_global ha h
  set r : ℝ := min (2 * ε) 1 with hr
  have hr0 : 0 < r := lt_min (by linarith) one_pos
  have hr1 : r ≤ 1 := min_le_right _ _
  have hr2 : r / 2 ≤ ε := by have := min_le_left (2 * ε) 1; linarith
  refine ⟨B * ((2 / r) ^ a * polylogConst a), fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hl := one_add_log_rpow_le ha hr0 hr1 hx
  have hxr : x ^ (r / 2) ≤ x ^ ε := Real.rpow_le_rpow_of_exponent_le hx hr2
  have hK0 : 0 ≤ (2 / r) ^ a * polylogConst a :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (polylogConst_pos a).le
  calc |rieszFunction x| ≤ B * x ^ (1 / 4 : ℝ) * (1 + Real.log x) ^ a := hB x hx
    _ ≤ B * x ^ (1 / 4 : ℝ) * ((2 / r) ^ a * polylogConst a * x ^ ε) := by
        gcongr
        exact hl.trans (mul_le_mul_of_nonneg_left hxr hK0)
    _ = B * ((2 / r) ^ a * polylogConst a) * (x ^ (1 / 4 : ℝ) * x ^ ε) := by ring
    _ = B * ((2 / r) ^ a * polylogConst a) * x ^ (1 / 4 + ε) := by
        rw [← Real.rpow_add hx0]

/-- The transform of `R` continues to `0 < Re s < ¾`. -/
theorem differentiableOn_mellin_rieszSeries_of_littleO {a : ℝ} (ha : 0 ≤ a)
    (h : RieszLittleO a) :
    DifferentiableOn ℂ (mellin fun t => ((rieszSeries t : ℝ) : ℂ)) (rieszStrip (3 / 4)) := by
  intro s hs
  obtain ⟨T, hT1, hT⟩ := h 1 one_pos
  set β : ℝ := (s.re + 3 / 4) / 2 with hβ
  have hsβ : s.re < β := by rw [hβ]; linarith [hs.2]
  set r : ℝ := min (3 / 4 - β) 1 with hr
  have hr0 : 0 < r := lt_min (by rw [hβ]; linarith [hs.2]) one_pos
  have hr1 : r ≤ 1 := min_le_right _ _
  have hr2 : r / 2 ≤ 3 / 4 - β := by have := min_le_left (3 / 4 - β) 1; linarith
  have hbound : ∀ x : ℝ, T ≤ x → |rieszSeries x| ≤ ((2 / r) ^ a * polylogConst a) * x ^ (-β) := by
    intro x hx
    have hx1 : 1 ≤ x := hT1.trans hx
    have hx0 : 0 < x := by linarith
    have hF := hT x hx
    rw [rieszFunction, abs_mul, abs_of_pos hx0] at hF
    have hl := one_add_log_rpow_le ha hr0 hr1 hx1
    have hxr : x ^ (r / 2) ≤ x ^ (3 / 4 - β) := Real.rpow_le_rpow_of_exponent_le hx1 hr2
    have hK0 : 0 ≤ (2 / r) ^ a * polylogConst a :=
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (polylogConst_pos a).le
    have hstep : x * |rieszSeries x| ≤ x * (((2 / r) ^ a * polylogConst a) * x ^ (-β)) := by
      calc x * |rieszSeries x| ≤ 1 * x ^ (1 / 4 : ℝ) * (1 + Real.log x) ^ a := hF
        _ ≤ x ^ (1 / 4 : ℝ) * ((2 / r) ^ a * polylogConst a * x ^ (3 / 4 - β)) := by
            rw [one_mul]
            exact mul_le_mul_of_nonneg_left (hl.trans (mul_le_mul_of_nonneg_left hxr hK0))
              (Real.rpow_nonneg hx0.le _)
        _ = ((2 / r) ^ a * polylogConst a) * (x ^ (1 / 4 : ℝ) * x ^ (3 / 4 - β)) := by ring
        _ = ((2 / r) ^ a * polylogConst a) * (x * x ^ (-β)) := by
            rw [← Real.rpow_add hx0, ← Real.rpow_one_add' hx0.le (by linarith)]
            congr 2
            ring
        _ = x * (((2 / r) ^ a * polylogConst a) * x ^ (-β)) := by ring
    exact le_of_mul_le_mul_left hstep hx0
  have hd := differentiableOn_mellin_rieszSeries hbound
  have hsU : s ∈ rieszStrip β := ⟨hs.1, hsβ⟩
  exact (hd.differentiableAt ((isOpen_rieszStrip β).mem_nhds hsU)).differentiableWithinAt

/-- The zeta identity on `0 < Re s < ¾`. -/
theorem mellin_rieszSeries_mul_eq_of_littleO {a : ℝ} (ha : 0 ≤ a) (h : RieszLittleO a)
    {s : ℂ} (hs : s ∈ rieszStrip (3 / 4)) :
    mellin (fun t => ((rieszSeries t : ℝ) : ℂ)) s * zetaResidueUnit (2 - 2 * s) =
      Complex.Gamma s * (1 - 2 * s) := by
  set U := rieszStrip (3 / 4)
  set f : ℂ → ℂ := fun s =>
    mellin (fun t => ((rieszSeries t : ℝ) : ℂ)) s * zetaResidueUnit (2 - 2 * s)
  set g : ℂ → ℂ := fun s => Complex.Gamma s * (1 - 2 * s)
  have hf : AnalyticOnNhd ℂ f U := by
    refine DifferentiableOn.analyticOnNhd ?_ (isOpen_rieszStrip _)
    refine (differentiableOn_mellin_rieszSeries_of_littleO ha h).mul ?_
    intro s _
    exact ((analyticAt_zetaResidueUnit _).differentiableAt.comp s
      ((differentiableAt_const _).sub ((differentiableAt_const _).mul
        differentiableAt_id))).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ g U := by
    refine DifferentiableOn.analyticOnNhd ?_ (isOpen_rieszStrip _)
    intro s hs
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (Complex.differentiableAt_Gamma s fun m hm => ?_).mul
      ((differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id))
    have : s.re = -(m : ℝ) := by rw [hm]; simp
    have := hs.1
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hs₀ : ((1 / 4 : ℝ) : ℂ) ∈ U := ⟨by norm_num, by norm_num⟩
  have hfg : f =ᶠ[𝓝 ((1 / 4 : ℝ) : ℂ)] g := by
    have hopen : IsOpen (rieszStrip (1 / 2)) := isOpen_rieszStrip _
    have hmem : ((1 / 4 : ℝ) : ℂ) ∈ rieszStrip (1 / 2) := ⟨by norm_num, by norm_num⟩
    filter_upwards [hopen.mem_nhds hmem] with s hs
    exact mellin_rieszSeries_mul_zetaResidueUnit hs.1 hs.2
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg (isPreconnected_rieszStrip _) hs₀ hfg hs

/-- The transform near the abscissa: `‖∫_0^∞ R t^{s-1}‖ ≤ η (¾ - Re s)^{-(a+1)} + C_η`. -/
theorem exists_norm_mellin_rieszSeries_le {a : ℝ} (ha : 0 ≤ a) (h : RieszLittleO a) :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re < 3 / 4 →
      ‖mellin (fun t => ((rieszSeries t : ℝ) : ℂ)) s‖ ≤
        η * (3 / 4 - s.re) ^ (-(a + 1)) + C := by
  intro η hη
  obtain ⟨B, hB0, hB⟩ := exists_abs_rieszFunction_le_global ha h
  have htail := norm_integral_Ioi_one_cpow_mul_le (f := fun t => ((rieszFunction t : ℝ) : ℂ))
    (c := 1 / 4) (a := a) (B := B) ha
    (fun t ht => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hB t ht.le)
    (fun ε hε => by
      obtain ⟨T, hT1, hT⟩ := h ε hε
      exact ⟨T, hT1, fun t ht => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hT t ht⟩)
    η hη
  obtain ⟨C, hC⟩ := htail
  refine ⟨2 * rieszBound + C, fun s hs1 hs2 => ?_⟩
  set g : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) • ((rieszSeries t : ℝ) : ℂ) with hg
  have hS := rieszBound_nonneg
  -- the head over `(0, 1]`
  have hheadI : IntegrableOn (fun t : ℝ => rieszBound * t ^ (-(1 / 2 : ℝ))) (Ioc 0 1) := by
    have hI : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    exact (hI.1 : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (Ioc 0 1)).const_mul _
  have hheadB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖g t‖ ≤ rieszBound * t ^ (-(1 / 2 : ℝ)) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    show ‖(t : ℂ) ^ (s - 1) • ((rieszSeries t : ℝ) : ℂ)‖ ≤ _
    rw [smul_eq_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real,
      Real.norm_eq_abs, Complex.sub_re, Complex.one_re, mul_comm]
    refine mul_le_mul (abs_rieszSeries_le ht0.le)
      (Real.rpow_le_rpow_of_exponent_ge ht0 ht.2 (by linarith)) (Real.rpow_nonneg ht0.le _) hS
  have hgm : AEStronglyMeasurable g (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have h1 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1)) (Ioi 0) := fun t ht =>
      (Complex.continuousAt_ofReal_cpow_const t (s - 1)
        (Or.inr (ne_of_gt (show (0 : ℝ) < t from ht)))).continuousWithinAt
    have h2 : ContinuousOn (fun t : ℝ => ((rieszSeries t : ℝ) : ℂ)) (Ioi 0) :=
      Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_rieszSeries.mono Ioi_subset_Ici_self)
    exact h1.smul h2
  have hheadInt : IntegrableOn g (Ioc 0 1) :=
    hheadI.mono' (hgm.mono_set Ioc_subset_Ioi_self)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hheadB))
  have hhead : ‖∫ t in Ioc (0 : ℝ) 1, g t‖ ≤ 2 * rieszBound := by
    refine (norm_integral_le_of_norm_le hheadI
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hheadB))).trans
      (le_of_eq ?_)
    rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by norm_num))]
    norm_num
    ring
  -- the tail over `(1, ∞)`
  have htailEq : ∀ t ∈ Ioi (1 : ℝ),
      g t = (t : ℂ) ^ (-(1 - s) - 1) * ((rieszFunction t : ℝ) : ℂ) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by
      have : (0 : ℝ) < t := lt_trans one_pos ht
      exact_mod_cast this.ne'
    show (t : ℂ) ^ (s - 1) • ((rieszSeries t : ℝ) : ℂ) = _
    rw [smul_eq_mul, rieszFunction, Complex.ofReal_mul, show -(1 - s) - 1 = (s - 1) - 1 by ring,
      show (t : ℂ) ^ (s - 1 - 1) * ((t : ℂ) * ((rieszSeries t : ℝ) : ℂ)) =
        ((t : ℂ) ^ (s - 1 - 1) * (t : ℂ) ^ (1 : ℂ)) * ((rieszSeries t : ℝ) : ℂ) by
          rw [Complex.cpow_one]; ring,
      ← Complex.cpow_add _ _ ht0, sub_add_cancel]
  have hre' : (1 - s).re = 1 / 4 + (3 / 4 - s.re) := by simp; ring
  have htailB := hC (1 - s) (by rw [hre']; linarith) (by rw [hre']; linarith)
  rw [hre', show (1 / 4 + (3 / 4 - s.re) - 1 / 4 : ℝ) = 3 / 4 - s.re by ring] at htailB
  have htailInt : IntegrableOn g (Ioi 1) := by
    set r : ℝ := 3 / 4 - s.re with hr
    have hr0 : 0 < r := by rw [hr]; linarith
    have hr1 : r ≤ 1 := by rw [hr]; linarith
    have hi1 : IntegrableOn (fun t : ℝ => t ^ (-1 - r / 2)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine (hi1.const_mul (B * ((2 / r) ^ a * polylogConst a))).mono'
      (hgm.mono_set (Ioi_subset_Ioi zero_le_one))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := by linarith
    rw [htailEq t ht, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real,
      Real.norm_eq_abs]
    have hre2 : (-(1 - s) - 1).re = -(1 / 4 + r) - 1 := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, hr]; ring
    rw [hre2]
    have hl := one_add_log_rpow_le ha hr0 hr1 ht1.le
    have hK0 : 0 ≤ (2 / r) ^ a * polylogConst a :=
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (polylogConst_pos a).le
    have e1 : t ^ (-(1 / 4 + r) - 1) * t ^ (1 / 4 : ℝ) = t ^ (-1 - r) := by
      rw [← Real.rpow_add ht0]; ring_nf
    have e2 : t ^ (-1 - r) * t ^ (r / 2) = t ^ (-1 - r / 2) := by
      rw [← Real.rpow_add ht0]; ring_nf
    calc t ^ (-(1 / 4 + r) - 1) * |rieszFunction t|
        ≤ t ^ (-(1 / 4 + r) - 1) * (B * t ^ (1 / 4 : ℝ) * (1 + Real.log t) ^ a) :=
          mul_le_mul_of_nonneg_left (hB t ht1.le) (Real.rpow_nonneg ht0.le _)
      _ = B * (t ^ (-(1 / 4 + r) - 1) * t ^ (1 / 4 : ℝ)) * (1 + Real.log t) ^ a := by ring
      _ = B * t ^ (-1 - r) * (1 + Real.log t) ^ a := by rw [e1]
      _ ≤ B * t ^ (-1 - r) * ((2 / r) ^ a * polylogConst a * t ^ (r / 2)) := by gcongr
      _ = B * ((2 / r) ^ a * polylogConst a) * (t ^ (-1 - r) * t ^ (r / 2)) := by ring
      _ = B * ((2 / r) ^ a * polylogConst a) * t ^ (-1 - r / 2) := by rw [e2]
  have hsplit : mellin (fun t => ((rieszSeries t : ℝ) : ℂ)) s =
      (∫ t in Ioc (0 : ℝ) 1, g t) + ∫ t in Ioi (1 : ℝ), g t := by
    rw [mellin, ← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hheadInt htailInt]
  rw [hsplit, setIntegral_congr_fun measurableSet_Ioi htailEq]
  calc _ ≤ ‖∫ t in Ioc (0 : ℝ) 1, g t‖ +
        ‖∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-(1 - s) - 1) * ((rieszFunction t : ℝ) : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ 2 * rieszBound + (η * (3 / 4 - s.re) ^ (-(a + 1)) + C) := add_le_add hhead htailB
    _ = _ := by ring

/-- **Strict multiplicity from Riesz's function.** -/
theorem analyticOrderAt_riemannZeta_toNat_lt_of_rieszLittleO {a : ℝ} (ha : 0 ≤ a)
    (h : RieszLittleO a) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    ((analyticOrderAt riemannZeta ρ).toNat : ℝ) < a + 1 := by
  have hρpos : 0 < ρ.re := by rw [hρ]; norm_num
  have hρ1 : ρ ≠ 1 := by intro h; rw [h, Complex.one_re] at hρ; norm_num at hρ
  have horderFinite : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    rw [← xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hρpos, by rw [hρ]; norm_num⟩]
    exact xi_orderAt_ne_top ρ
  set n : ℕ := (analyticOrderAt riemannZeta ρ).toNat with hn
  have hncoe : (n : ℕ∞) = analyticOrderAt riemannZeta ρ := ENat.coe_toNat horderFinite
  obtain ⟨p, hp, _, hfactor⟩ :=
    ((analyticOn_riemannZeta ρ hρ1).analyticOrderAt_eq_natCast).mp hncoe.symm
  set s₀ : ℂ := 1 - ρ / 2 with hs₀
  have hs₀re : s₀.re = 3 / 4 := by simp [hs₀, hρ]; norm_num
  have hw : ∀ s : ℂ, 2 - 2 * s - ρ = -2 * (s - s₀) := fun s => by rw [hs₀]; ring
  have hmap : Tendsto (fun s : ℂ => 2 - 2 * s) (𝓝 s₀) (𝓝 ρ) :=
    (by fun_prop : Continuous fun s : ℂ => 2 - 2 * s).tendsto' s₀ ρ (by rw [hs₀]; ring)
  set P : ℂ → ℂ := fun s => (-2) ^ n * ((1 - 2 * s) * p (2 - 2 * s)) with hP
  have hPc : ContinuousAt P s₀ :=
    continuousAt_const.mul ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).mul
      (hp.continuousAt.comp_of_eq (continuous_const.sub (continuous_const.mul
        continuous_id)).continuousAt (by rw [hs₀]; ring)))
  have hfac : ∀ᶠ s in 𝓝 s₀, zetaResidueUnit (2 - 2 * s) = (s - s₀) ^ n * P s := by
    filter_upwards [hmap.eventually hfactor, hmap.eventually (isOpen_compl_singleton.mem_nhds hρ1)]
      with s hs hne
    rw [zetaResidueUnit, Function.update_of_ne hne, hs, smul_eq_mul, hw, hP]
    rw [mul_pow]
    ring
  set H : ℂ → ℂ := fun s => Complex.Gamma s * (1 - 2 * s) with hH
  have hHc : ContinuousAt H s₀ := by
    refine ((Complex.differentiableAt_Gamma s₀ fun m hm => ?_).continuousAt).mul
      (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
    have : s₀.re = -(m : ℝ) := by rw [hm]; simp
    rw [hs₀re] at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hHρ : H s₀ ≠ 0 := by
    refine mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by rw [hs₀re]; norm_num)) ?_
    rw [show 1 - 2 * s₀ = ρ - 1 by rw [hs₀]; ring]
    exact sub_ne_zero.mpr hρ1
  have hray_re : ∀ r : ℝ, (s₀ + (r : ℂ) * (-1)).re = 3 / 4 - r := fun r => by
    simp [hs₀re]; ring
  have hFE : ∀ᶠ r : ℝ in 𝓝[>] 0,
      mellin (fun t => ((rieszSeries t : ℝ) : ℂ)) (s₀ + r * (-1)) *
        zetaResidueUnit (2 - 2 * (s₀ + r * (-1))) = H (s₀ + r * (-1)) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 3 / 4)] with r hr
    exact mellin_rieszSeries_mul_eq_of_littleO ha h
      ⟨by rw [hray_re]; linarith [hr.2], by rw [hray_re]; linarith [hr.1]⟩
  have hF : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ᶠ r : ℝ in 𝓝[>] 0,
      ‖mellin (fun t => ((rieszSeries t : ℝ) : ℂ)) (s₀ + r * (-1))‖ ≤
        η * r ^ (-(a + 1)) + C := by
    intro η hη
    obtain ⟨C, hC⟩ := exists_norm_mellin_rieszSeries_le ha h η hη
    refine ⟨C, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with r hr
    have := hC (s₀ + r * (-1)) (by rw [hray_re]; linarith [hr.2])
      (by rw [hray_re]; linarith [hr.1])
    rwa [hray_re, show (3 / 4 - (3 / 4 - r) : ℝ) = r by ring] at this
  exact natCast_lt_of_ray_littleO (E := fun s => zetaResidueUnit (2 - 2 * s)) ha hPc hfac hHc
    hHρ hFE hF

/-- **RH with a strict multiplicity cap from a little-`o` polylog Riesz bound.** -/
theorem riemannHypothesis_and_order_lt_of_rieszLittleO {a : ℝ} (ha : 0 ≤ a)
    (h : RieszLittleO a) :
    RiemannHypothesis ∧ ∀ ρ : ℂ, ρ.re = 1 / 2 →
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) < a + 1 :=
  ⟨riemannHypothesis_of_rieszLittleO ha h,
    fun _ hρ => analyticOrderAt_riemannZeta_toNat_lt_of_rieszLittleO ha h hρ⟩

/-- **Riesz's function is not `o(x^{¼})`.** -/
theorem not_rieszLittleO_zero : ¬ RieszLittleO 0 := by
  intro h
  obtain ⟨t, -, ht0⟩ := exists_Xi_zero_gt 1
  set ρ : ℂ := 1 / 2 + (t : ℂ) * I with hρdef
  have hxi : xi ρ = 0 := by
    rw [xi_eq_XiC_comp]
    have e : ((1 / 2 + (t : ℂ) * I - 1 / 2) * -I) = (t : ℂ) := by
      ring_nf
      simp [Complex.I_sq]
    rw [e, XiC_ofReal, ht0]
    simp
  have hρre : ρ.re = 1 / 2 := by simp [hρdef]
  have hz : riemannZeta ρ = 0 := riemannZeta_eq_zero_iff_xi_or_trivial.mpr (Or.inl hxi)
  have h1 := one_le_analyticOrderAt_riemannZeta_toNat_of_critical hρre hz
  have h2 := analyticOrderAt_riemannZeta_toNat_lt_of_rieszLittleO le_rfl h hρre
  have : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by exact_mod_cast h1
  linarith

end

end RHTower
