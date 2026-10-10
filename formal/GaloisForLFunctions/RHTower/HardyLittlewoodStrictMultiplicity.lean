import GaloisForLFunctions.RHTower.RieszFunctionStrictMultiplicity
import GaloisForLFunctions.RHTower.HardyLittlewoodExponentLaw

/-!
# Strict polylogarithmic multiplicity for the Hardy–Littlewood criterion

The Hardy–Littlewood function `H(x) = Σ μ(n) n^{-1}(e^{-x/n²} - 1)` satisfies
`H(x) = O(x^{-¼+ε})` for every `ε > 0` iff RH (`riemannHypothesis_iff_hardyLittlewoodFunction_le`),
and `∫_0^∞ H(t) t^{s-1} dt · (w - 1)ζ(w) = -2Γ(s + 1)` with `w = 1 - 2s`. It is a `1/ζ`-type
receiver, so its logarithmic forms grade multiplicity strictly:

* if `|H(x)| ≤ ε x^{-¼} (1 + log x)^a` for `x ≥ T_ε`, for every `ε > 0`, then RH holds and every
  critical zero has order `< a + 1` (`riemannHypothesis_and_order_lt_of_hardyLittlewoodLittleO`);
* `H(x) ≠ o(x^{-¼})`, unconditionally (`not_hardyLittlewoodLittleO_zero`).

The proof is the Riesz proof with the ray `s = (1 - ρ)/2 - r` into the abscissa `Re s = ¼`: the
part of the transform over `(0, 1)` is bounded by `Σ 1/n³`, and the part over `(1, ∞)` is the
Mellin tail `∫ t^{-(-s)-1} H(t) dt` at the exponent `c = -¼` (`norm_integral_Ioi_one_cpow_mul_le`).
-/

open Complex Filter Topology MeasureTheory Set

namespace RHTower

noncomputable section

/-- `H(x) = o(x^{-¼}(1 + log x)^a)`, in explicit form. -/
def HardyLittlewoodLittleO (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 1 ≤ T ∧ ∀ x : ℝ, T ≤ x →
    |hardyLittlewoodFunction x| ≤ ε * x ^ (-(1 / 4) : ℝ) * (1 + Real.log x) ^ a

/-- `Σ 1/n³`. -/
def cubeBound : ℝ := ∑' n : ℕ, ((n : ℝ) ^ 3)⁻¹

theorem cubeBound_nonneg : 0 ≤ cubeBound :=
  tsum_nonneg fun _ => inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) 3)

theorem exists_abs_hardyLittlewoodFunction_le_global {a : ℝ} (ha : 0 ≤ a)
    (h : HardyLittlewoodLittleO a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x →
      |hardyLittlewoodFunction x| ≤ B * x ^ (-(1 / 4) : ℝ) * (1 + Real.log x) ^ a := by
  obtain ⟨T, hT1, hT⟩ := h 1 one_pos
  have hT0 : 0 < T := by linarith
  set B : ℝ := max 1 (T ^ (5 / 4 : ℝ) * cubeBound) with hB
  refine ⟨B, le_max_of_le_left zero_le_one, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hlog1 : 1 ≤ (1 + Real.log x) ^ a := Real.one_le_rpow (by linarith [Real.log_nonneg hx]) ha
  have hxq : 0 < x ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos hx0 _
  rcases le_or_gt T x with hTx | hxT
  · calc |hardyLittlewoodFunction x| ≤ 1 * x ^ (-(1 / 4) : ℝ) * (1 + Real.log x) ^ a := hT x hTx
      _ ≤ B * x ^ (-(1 / 4) : ℝ) * (1 + Real.log x) ^ a := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hxT' : x ^ (-(1 / 4) : ℝ) ≥ T ^ (-(1 / 4) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hx0 hxT.le (by norm_num)
    have hTpow : T ^ (5 / 4 : ℝ) * T ^ (-(1 / 4) : ℝ) = T := by
      rw [← Real.rpow_add hT0]; norm_num
    calc |hardyLittlewoodFunction x| ≤ x * cubeBound := by
          rw [mul_comm]; exact (abs_hardyLittlewoodFunction_le hx0.le).trans (by
            rw [mul_comm]; rfl)
      _ ≤ T * cubeBound := mul_le_mul_of_nonneg_right hxT.le cubeBound_nonneg
      _ = (T ^ (5 / 4 : ℝ) * cubeBound) * T ^ (-(1 / 4) : ℝ) := by rw [mul_right_comm, hTpow]
      _ ≤ B * x ^ (-(1 / 4) : ℝ) :=
          mul_le_mul (le_max_right _ _) hxT' (Real.rpow_nonneg hT0.le _)
            (le_max_of_le_left zero_le_one)
      _ ≤ B * x ^ (-(1 / 4) : ℝ) * (1 + Real.log x) ^ a :=
          le_mul_of_one_le_right (mul_nonneg (le_max_of_le_left zero_le_one) hxq.le) hlog1

theorem riemannHypothesis_of_hardyLittlewoodLittleO {a : ℝ} (ha : 0 ≤ a)
    (h : HardyLittlewoodLittleO a) : RiemannHypothesis := by
  rw [riemannHypothesis_iff_hardyLittlewoodFunction_le]
  intro ε hε
  obtain ⟨B, hB0, hB⟩ := exists_abs_hardyLittlewoodFunction_le_global ha h
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
  calc |hardyLittlewoodFunction x| ≤ B * x ^ (-(1 / 4) : ℝ) * (1 + Real.log x) ^ a := hB x hx
    _ ≤ B * x ^ (-(1 / 4) : ℝ) * ((2 / r) ^ a * polylogConst a * x ^ ε) := by
        gcongr
        exact hl.trans (mul_le_mul_of_nonneg_left hxr hK0)
    _ = B * ((2 / r) ^ a * polylogConst a) * (x ^ (-(1 / 4) : ℝ) * x ^ ε) := by ring
    _ = B * ((2 / r) ^ a * polylogConst a) * x ^ (-(1 / 4) + ε) := by
        rw [← Real.rpow_add hx0]

/-- The transform of `H` continues to `-1 < Re s < ¼`. -/
theorem differentiableOn_mellin_hardyLittlewoodFunction_of_littleO {a : ℝ} (ha : 0 ≤ a)
    (h : HardyLittlewoodLittleO a) :
    DifferentiableOn ℂ (mellin fun t => ((hardyLittlewoodFunction t : ℝ) : ℂ))
      (hardyLittlewoodStrip (1 / 4)) := by
  intro s hs
  obtain ⟨T, hT1, hT⟩ := h 1 one_pos
  set b : ℝ := (s.re + 1 / 4) / 2 with hb
  have hsb : s.re < b := by rw [hb]; linarith [hs.2]
  set r : ℝ := min (1 / 4 - b) 1 with hr
  have hr0 : 0 < r := lt_min (by rw [hb]; linarith [hs.2]) one_pos
  have hr1 : r ≤ 1 := min_le_right _ _
  have hr2 : r / 2 ≤ 1 / 4 - b := by have := min_le_left (1 / 4 - b) 1; linarith
  have hbound : ∀ x : ℝ, T ≤ x →
      |hardyLittlewoodFunction x| ≤ ((2 / r) ^ a * polylogConst a) * x ^ (-b) := by
    intro x hx
    have hx1 : 1 ≤ x := hT1.trans hx
    have hx0 : 0 < x := by linarith
    have hl := one_add_log_rpow_le ha hr0 hr1 hx1
    have hxr : x ^ (r / 2) ≤ x ^ (1 / 4 - b) := Real.rpow_le_rpow_of_exponent_le hx1 hr2
    have hK0 : 0 ≤ (2 / r) ^ a * polylogConst a :=
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (polylogConst_pos a).le
    calc |hardyLittlewoodFunction x| ≤ 1 * x ^ (-(1 / 4) : ℝ) * (1 + Real.log x) ^ a := hT x hx
      _ ≤ x ^ (-(1 / 4) : ℝ) * ((2 / r) ^ a * polylogConst a * x ^ (1 / 4 - b)) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left (hl.trans (mul_le_mul_of_nonneg_left hxr hK0))
            (Real.rpow_nonneg hx0.le _)
      _ = ((2 / r) ^ a * polylogConst a) * (x ^ (-(1 / 4) : ℝ) * x ^ (1 / 4 - b)) := by ring
      _ = ((2 / r) ^ a * polylogConst a) * x ^ (-b) := by
          rw [← Real.rpow_add hx0]; congr 2; ring
  have hd := differentiableOn_mellin_hardyLittlewoodFunction hbound
  have hsU : s ∈ hardyLittlewoodStrip b := ⟨hs.1, hsb⟩
  exact (hd.differentiableAt ((isOpen_hardyLittlewoodStrip b).mem_nhds hsU)).differentiableWithinAt

theorem mellin_hardyLittlewoodFunction_mul_eq_of_littleO {a : ℝ} (ha : 0 ≤ a)
    (h : HardyLittlewoodLittleO a) {s : ℂ} (hs : s ∈ hardyLittlewoodStrip (1 / 4)) :
    mellin (fun t => ((hardyLittlewoodFunction t : ℝ) : ℂ)) s * zetaResidueUnit (1 - 2 * s) =
      -2 * Complex.Gamma (s + 1) := by
  set U := hardyLittlewoodStrip (1 / 4)
  set f : ℂ → ℂ := fun s =>
    mellin (fun t => ((hardyLittlewoodFunction t : ℝ) : ℂ)) s * zetaResidueUnit (1 - 2 * s)
  set g : ℂ → ℂ := fun s => -2 * Complex.Gamma (s + 1)
  have hf : AnalyticOnNhd ℂ f U := by
    refine DifferentiableOn.analyticOnNhd ?_ (isOpen_hardyLittlewoodStrip _)
    refine (differentiableOn_mellin_hardyLittlewoodFunction_of_littleO ha h).mul ?_
    intro s _
    exact ((analyticAt_zetaResidueUnit _).differentiableAt.comp s
      ((differentiableAt_const _).sub ((differentiableAt_const _).mul
        differentiableAt_id))).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ g U := by
    refine DifferentiableOn.analyticOnNhd ?_ (isOpen_hardyLittlewoodStrip _)
    intro s hs
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (differentiableAt_const _).mul ?_
    refine (Complex.differentiableAt_Gamma (s + 1) fun m hm => ?_).comp s
      (differentiableAt_id.add (differentiableAt_const _))
    have : s.re + 1 = -(m : ℝ) := by
      have := congrArg Complex.re hm; simpa using this
    have := hs.1
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hs₀ : ((-1 / 2 : ℝ) : ℂ) ∈ U := ⟨by norm_num, by norm_num⟩
  have hfg : f =ᶠ[𝓝 ((-1 / 2 : ℝ) : ℂ)] g := by
    have hopen : IsOpen (hardyLittlewoodStrip 0) := isOpen_hardyLittlewoodStrip _
    have hmem : ((-1 / 2 : ℝ) : ℂ) ∈ hardyLittlewoodStrip 0 := ⟨by norm_num, by norm_num⟩
    filter_upwards [hopen.mem_nhds hmem] with s hs
    exact mellin_hardyLittlewoodFunction_mul_zetaResidueUnit hs.1 hs.2
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg
    ((convex_halfSpace_re_gt (-1) |>.inter (convex_halfSpace_re_lt (1 / 4))).isPreconnected)
    hs₀ hfg hs

/-- The transform near the abscissa `Re s = ¼`. -/
theorem exists_norm_mellin_hardyLittlewoodFunction_le {a : ℝ} (ha : 0 ≤ a)
    (h : HardyLittlewoodLittleO a) :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ s : ℂ, 0 ≤ s.re → s.re < 1 / 4 →
      ‖mellin (fun t => ((hardyLittlewoodFunction t : ℝ) : ℂ)) s‖ ≤
        η * (1 / 4 - s.re) ^ (-(a + 1)) + C := by
  intro η hη
  obtain ⟨B, hB0, hB⟩ := exists_abs_hardyLittlewoodFunction_le_global ha h
  obtain ⟨C, hC⟩ := norm_integral_Ioi_one_cpow_mul_le
    (f := fun t => ((hardyLittlewoodFunction t : ℝ) : ℂ)) (c := -(1 / 4)) (a := a) (B := B) ha
    (fun t ht => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hB t ht.le)
    (fun ε hε => by
      obtain ⟨T, hT1, hT⟩ := h ε hε
      exact ⟨T, hT1, fun t ht => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hT t ht⟩)
    η hη
  refine ⟨cubeBound + C, fun s hs0 hs1 => ?_⟩
  set g : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) • ((hardyLittlewoodFunction t : ℝ) : ℂ) with hg
  have hS := cubeBound_nonneg
  have hheadB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖g t‖ ≤ cubeBound := by
    intro t ht
    have ht0 : 0 < t := ht.1
    show ‖(t : ℂ) ^ (s - 1) • ((hardyLittlewoodFunction t : ℝ) : ℂ)‖ ≤ _
    rw [smul_eq_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real,
      Real.norm_eq_abs, Complex.sub_re, Complex.one_re]
    have hH := abs_hardyLittlewoodFunction_le ht0.le
    have e : t ^ (s.re - 1) * t = t ^ s.re := by
      rw [← Real.rpow_add_one ht0.ne']; ring_nf
    have hle1 : t ^ s.re ≤ 1 := Real.rpow_le_one ht0.le ht.2 hs0
    calc t ^ (s.re - 1) * |hardyLittlewoodFunction t| ≤ t ^ (s.re - 1) * (t * cubeBound) :=
          mul_le_mul_of_nonneg_left hH (Real.rpow_nonneg ht0.le _)
      _ = t ^ s.re * cubeBound := by rw [← mul_assoc, e]
      _ ≤ 1 * cubeBound := mul_le_mul_of_nonneg_right hle1 hS
      _ = cubeBound := one_mul _
  have hgm : AEStronglyMeasurable g (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have h1 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1)) (Ioi 0) := fun t ht =>
      (Complex.continuousAt_ofReal_cpow_const t (s - 1)
        (Or.inr (ne_of_gt (show (0 : ℝ) < t from ht)))).continuousWithinAt
    have h2 : ContinuousOn (fun t : ℝ => ((hardyLittlewoodFunction t : ℝ) : ℂ)) (Ioi 0) :=
      Complex.continuous_ofReal.comp_continuousOn continuousOn_hardyLittlewoodFunction
    exact h1.smul h2
  have hheadI : IntegrableOn (fun _ : ℝ => cubeBound) (Ioc 0 1) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hheadInt : IntegrableOn g (Ioc 0 1) :=
    hheadI.mono' (hgm.mono_set Ioc_subset_Ioi_self)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hheadB))
  have hhead : ‖∫ t in Ioc (0 : ℝ) 1, g t‖ ≤ cubeBound := by
    refine (norm_integral_le_of_norm_le hheadI
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hheadB))).trans
      (le_of_eq ?_)
    rw [setIntegral_const, Real.volume_real_Ioc_of_le zero_le_one, smul_eq_mul]
    ring
  have htailEq : ∀ t ∈ Ioi (1 : ℝ),
      g t = (t : ℂ) ^ (-(-s) - 1) * ((hardyLittlewoodFunction t : ℝ) : ℂ) := by
    intro t _
    show (t : ℂ) ^ (s - 1) • ((hardyLittlewoodFunction t : ℝ) : ℂ) = _
    rw [smul_eq_mul, neg_neg]
  have hre' : (-s).re = -(1 / 4) + (1 / 4 - s.re) := by simp; ring
  have htailB := hC (-s) (by rw [hre']; linarith) (by rw [hre']; linarith)
  rw [hre', show (-(1 / 4) + (1 / 4 - s.re) - -(1 / 4) : ℝ) = 1 / 4 - s.re by ring] at htailB
  have htailInt : IntegrableOn g (Ioi 1) := by
    set r : ℝ := 1 / 4 - s.re with hr
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
    have hre2 : (-(-s) - 1).re = -(-(1 / 4) + r) - 1 := by
      simp only [Complex.sub_re, Complex.one_re, neg_neg, hr]; ring
    rw [hre2]
    have hl := one_add_log_rpow_le ha hr0 hr1 ht1.le
    have hK0 : 0 ≤ (2 / r) ^ a * polylogConst a :=
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (polylogConst_pos a).le
    have e1 : t ^ (-(-(1 / 4) + r) - 1) * t ^ (-(1 / 4) : ℝ) = t ^ (-1 - r) := by
      rw [← Real.rpow_add ht0]; ring_nf
    have e2 : t ^ (-1 - r) * t ^ (r / 2) = t ^ (-1 - r / 2) := by
      rw [← Real.rpow_add ht0]; ring_nf
    calc t ^ (-(-(1 / 4) + r) - 1) * |hardyLittlewoodFunction t|
        ≤ t ^ (-(-(1 / 4) + r) - 1) * (B * t ^ (-(1 / 4) : ℝ) * (1 + Real.log t) ^ a) :=
          mul_le_mul_of_nonneg_left (hB t ht1.le) (Real.rpow_nonneg ht0.le _)
      _ = B * (t ^ (-(-(1 / 4) + r) - 1) * t ^ (-(1 / 4) : ℝ)) * (1 + Real.log t) ^ a := by ring
      _ = B * t ^ (-1 - r) * (1 + Real.log t) ^ a := by rw [e1]
      _ ≤ B * t ^ (-1 - r) * ((2 / r) ^ a * polylogConst a * t ^ (r / 2)) := by gcongr
      _ = B * ((2 / r) ^ a * polylogConst a) * (t ^ (-1 - r) * t ^ (r / 2)) := by ring
      _ = B * ((2 / r) ^ a * polylogConst a) * t ^ (-1 - r / 2) := by rw [e2]
  have hsplit : mellin (fun t => ((hardyLittlewoodFunction t : ℝ) : ℂ)) s =
      (∫ t in Ioc (0 : ℝ) 1, g t) + ∫ t in Ioi (1 : ℝ), g t := by
    rw [mellin, ← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hheadInt htailInt]
  rw [hsplit, setIntegral_congr_fun measurableSet_Ioi htailEq]
  calc _ ≤ ‖∫ t in Ioc (0 : ℝ) 1, g t‖ +
        ‖∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-(-s) - 1) * ((hardyLittlewoodFunction t : ℝ) : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ cubeBound + (η * (1 / 4 - s.re) ^ (-(a + 1)) + C) := add_le_add hhead htailB
    _ = _ := by ring

/-- **Strict multiplicity from the Hardy–Littlewood function.** -/
theorem analyticOrderAt_riemannZeta_toNat_lt_of_hardyLittlewoodLittleO {a : ℝ} (ha : 0 ≤ a)
    (h : HardyLittlewoodLittleO a) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
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
  set s₀ : ℂ := (1 - ρ) / 2 with hs₀
  have hs₀re : s₀.re = 1 / 4 := by simp [hs₀, hρ]; norm_num
  have hw : ∀ s : ℂ, 1 - 2 * s - ρ = -2 * (s - s₀) := fun s => by rw [hs₀]; ring
  have hmap : Tendsto (fun s : ℂ => 1 - 2 * s) (𝓝 s₀) (𝓝 ρ) :=
    (by fun_prop : Continuous fun s : ℂ => 1 - 2 * s).tendsto' s₀ ρ (by rw [hs₀]; ring)
  set P : ℂ → ℂ := fun s => (-2) ^ n * ((-2 * s) * p (1 - 2 * s)) with hP
  have hPc : ContinuousAt P s₀ :=
    continuousAt_const.mul ((continuousAt_const.mul continuousAt_id).mul
      (hp.continuousAt.comp_of_eq (continuous_const.sub (continuous_const.mul
        continuous_id)).continuousAt (by rw [hs₀]; ring)))
  have hfac : ∀ᶠ s in 𝓝 s₀, zetaResidueUnit (1 - 2 * s) = (s - s₀) ^ n * P s := by
    filter_upwards [hmap.eventually hfactor, hmap.eventually (isOpen_compl_singleton.mem_nhds hρ1)]
      with s hs hne
    rw [zetaResidueUnit, Function.update_of_ne hne, hs, smul_eq_mul, hw, hP, mul_pow]
    ring
  set H : ℂ → ℂ := fun s => -2 * Complex.Gamma (s + 1) with hH
  have hHc : ContinuousAt H s₀ := by
    have h1 : ContinuousAt Complex.Gamma (s₀ + 1) := by
      refine (Complex.differentiableAt_Gamma (s₀ + 1) fun m hm => ?_).continuousAt
      have : s₀.re + 1 = -(m : ℝ) := by
        have := congrArg Complex.re hm; simpa using this
      rw [hs₀re] at this
      linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have h2 : ContinuousAt (fun s : ℂ => Complex.Gamma (s + 1)) s₀ :=
      h1.comp (f := fun s : ℂ => s + 1) (continuous_add_const (1 : ℂ)).continuousAt
    exact continuousAt_const.mul h2
  have hHρ : H s₀ ≠ 0 := by
    refine mul_ne_zero (by norm_num) (Complex.Gamma_ne_zero_of_re_pos ?_)
    simp only [Complex.add_re, Complex.one_re, hs₀re]; norm_num
  have hray_re : ∀ r : ℝ, (s₀ + (r : ℂ) * (-1)).re = 1 / 4 - r := fun r => by
    simp [hs₀re]; ring
  have hFE : ∀ᶠ r : ℝ in 𝓝[>] 0,
      mellin (fun t => ((hardyLittlewoodFunction t : ℝ) : ℂ)) (s₀ + r * (-1)) *
        zetaResidueUnit (1 - 2 * (s₀ + r * (-1))) = H (s₀ + r * (-1)) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with r hr
    exact mellin_hardyLittlewoodFunction_mul_eq_of_littleO ha h
      ⟨by rw [hray_re]; linarith [hr.2], by rw [hray_re]; linarith [hr.1]⟩
  have hF : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ᶠ r : ℝ in 𝓝[>] 0,
      ‖mellin (fun t => ((hardyLittlewoodFunction t : ℝ) : ℂ)) (s₀ + r * (-1))‖ ≤
        η * r ^ (-(a + 1)) + C := by
    intro η hη
    obtain ⟨C, hC⟩ := exists_norm_mellin_hardyLittlewoodFunction_le ha h η hη
    refine ⟨C, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with r hr
    have := hC (s₀ + r * (-1)) (by rw [hray_re]; linarith [hr.2])
      (by rw [hray_re]; linarith [hr.1])
    rwa [hray_re, show (1 / 4 - (1 / 4 - r) : ℝ) = r by ring] at this
  exact natCast_lt_of_ray_littleO (E := fun s => zetaResidueUnit (1 - 2 * s)) ha hPc hfac hHc
    hHρ hFE hF

theorem riemannHypothesis_and_order_lt_of_hardyLittlewoodLittleO {a : ℝ} (ha : 0 ≤ a)
    (h : HardyLittlewoodLittleO a) :
    RiemannHypothesis ∧ ∀ ρ : ℂ, ρ.re = 1 / 2 →
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) < a + 1 :=
  ⟨riemannHypothesis_of_hardyLittlewoodLittleO ha h,
    fun _ hρ => analyticOrderAt_riemannZeta_toNat_lt_of_hardyLittlewoodLittleO ha h hρ⟩

/-- **The Hardy–Littlewood function is not `o(x^{-¼})`.** -/
theorem not_hardyLittlewoodLittleO_zero : ¬ HardyLittlewoodLittleO 0 := by
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
  have h2 := analyticOrderAt_riemannZeta_toNat_lt_of_hardyLittlewoodLittleO le_rfl h hρre
  have : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by exact_mod_cast h1
  linarith

end

end RHTower
