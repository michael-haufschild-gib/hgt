import GaloisForLFunctions.RHTower.MertensSquareRootOmega
import GaloisForLFunctions.RHTower.MobiusLaplacePolylogBoundaryMultiplicity
import GaloisForLFunctions.RHTower.SignedArithmeticAbscissaRH

/-!
# Strict polylogarithmic Mertens bounds and the multiplicity of critical zeros

Let `M(x) = Σ_{k ≤ x} μ(k)` and `a ≥ 0`.  If `M(x) = o(√x (1 + log x)^a)`, in the form
`|M(x)| ≤ ε√x(1 + log x)^a + C_ε` for every `ε > 0`, then RH holds and every zero `ρ` of `ζ` on the
critical line has order `< a + 1` (`riemannHypothesis_and_order_lt_of_mertens_littleO`).

**Proof.**  The Mellin transform `G(s) = ∫_1^∞ M(x) x^{-s-1} dx` equals `1/(sζ(s))` on `Re s > 1` and
is holomorphic on `Re s > ½`, so `G(s)·s·(s − 1)ζ(s) = s − 1` there; this gives RH.  On the ray
`s = ρ + r`, the pointwise bound `(1 + log x)^a ≤ (2/r)^a K_a x^{r/2}` gives
`‖G(ρ + r)‖ ≤ εK_a 2^{a+1} r^{-(a+1)} + 2C_ε`.  If `ρ` had order `n ≥ a + 1`, then
`G(ρ + r)·(ρ + r − 1)ζ(ρ + r) → 0`, while the identity makes it tend to `(ρ − 1)/ρ ≠ 0`.

**The single point `s = ½`.**  Kronecker's lemma turns convergence of
`Σ_{n ≥ 1} μ(n) n^{-1/2} (1 + log n)^{-a}` into the little-`o` bound
(`mertens_littleO_of_weighted_converges`).  Convergence of this one series, at the one point
`s = ½`, therefore forces RH together with order `< a + 1`
(`riemannHypothesis_and_order_lt_of_weighted_moebius_converges`).  For `0 ≤ a ≤ 1` this means all
critical zeros are simple (`riemannHypothesis_and_simple_of_weighted_moebius_converges`).  At `a = 0`,
Hardy's critical zeros make `Σ μ(n)/√n` divergent, unconditionally
(`not_moebius_div_sqrt_converges`).
-/

open Complex Filter Topology MeasureTheory Set Asymptotics
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## The Mellin transform of `M` -/

/-- `M(x)` as a complex function. -/
def mertensC (x : ℝ) : ℂ := (mertensFunctionReal x : ℂ)

/-- `G(s) = ∫_1^∞ M(x) x^{-s-1} dx`, the Mellin transform of `M` at `-s`. -/
def mertensMellin (s : ℂ) : ℂ := mellin mertensC (-s)

theorem mertensFunctionReal_eq_zero_of_lt_one {x : ℝ} (hx : x < 1) :
    mertensFunctionReal x = 0 := by
  unfold mertensFunctionReal
  rw [Nat.floor_eq_zero.mpr hx]
  simp

theorem abs_mertensFunctionReal_le_abs (x : ℝ) : |mertensFunctionReal x| ≤ |x| := by
  refine (abs_mertensFunctionReal_le x).trans ?_
  rcases le_or_gt 0 x with hx | hx
  · exact (Nat.floor_le hx).trans (le_abs_self x)
  · rw [Nat.floor_of_nonpos hx.le, Nat.cast_zero]; exact abs_nonneg x

theorem mertensMellin_eq_integral_Ici (s : ℂ) :
    mertensMellin s = ∫ x in Ici (1 : ℝ), (x : ℂ) ^ (-s - 1) * mertensC x := by
  unfold mertensMellin mellin
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ici_subset_Ioi.mpr one_pos) fun x hx => ?_]
  · simp only [smul_eq_mul]
  · have hx1 : x < 1 := by simpa using hx.2
    rw [mertensC, mertensFunctionReal_eq_zero_of_lt_one hx1, Complex.ofReal_zero, smul_zero]

theorem mertensMellin_eq_inv {s : ℂ} (hs : 1 < s.re) :
    mertensMellin s = 1 / (s * riemannZeta s) := by
  have hs0 : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hs; linarith
  have h := Sieve.inv_riemannZeta_eq_mul_integral_mertens hs
  have hcongr : ∫ x in Ici (1 : ℝ), (x : ℂ) ^ (-s - 1) * mertensC x =
      ∫ t in Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.moebius k : ℤ) : ℂ)) *
        ((t : ℝ) : ℂ) ^ (-(s + 1)) := by
    rw [integral_Ici_eq_integral_Ioi]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [mertensC, mertensFunctionReal, show -s - 1 = -(s + 1) by ring, mul_comm]
    push_cast
    rfl
  rw [mertensMellin_eq_integral_Ici, hcongr, one_div, mul_inv, h, ← mul_assoc,
    inv_mul_cancel₀ hs0, one_mul]

/-! ## The polylogarithmic weight -/

/-- `K_a = 1 + ⌈a⌉! e^{1/2}`. -/
def polylogConst (a : ℝ) : ℝ := 1 + ((⌈a⌉₊).factorial : ℝ) * Real.exp (1 / 2)

theorem polylogConst_pos (a : ℝ) : 0 < polylogConst a := by
  unfold polylogConst; positivity

/-- `(1 + log x)^a ≤ (2/r)^a K_a x^{r/2}` for `x ≥ 1`, `0 < r ≤ 1`. -/
theorem one_add_log_rpow_le {a r x : ℝ} (ha : 0 ≤ a) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hx : 1 ≤ x) : (1 + Real.log x) ^ a ≤ (2 / r) ^ a * polylogConst a * x ^ (r / 2) := by
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  set y : ℝ := r * (1 + Real.log x) / 2 with hy
  have hy0 : 0 ≤ y := by positivity
  have hL : 1 + Real.log x = 2 / r * y := by rw [hy]; field_simp
  set n : ℕ := ⌈a⌉₊ with hn
  have hya : y ^ a ≤ 1 + y ^ n := by
    rcases le_or_gt y 1 with hy1 | hy1
    · have := Real.rpow_le_one hy0 hy1 ha
      have : 0 ≤ y ^ n := pow_nonneg hy0 n
      linarith
    · have h1 : y ^ a ≤ y ^ (n : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hy1.le (Nat.le_ceil a)
      rw [Real.rpow_natCast] at h1
      linarith
  have hfac : y ^ n ≤ (n.factorial : ℝ) * Real.exp y := by
    have h := Real.pow_div_factorial_le_exp y hy0 n
    rwa [div_le_iff₀ (by exact_mod_cast n.factorial_pos), mul_comm] at h
  have hexp : Real.exp y ≤ Real.exp (1 / 2) * x ^ (r / 2) := by
    rw [Real.rpow_def_of_pos (by linarith), ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by rw [hy]; nlinarith)
  have hxr : 1 ≤ x ^ (r / 2) := Real.one_le_rpow hx (by positivity)
  have hfac0 : (0 : ℝ) ≤ n.factorial := by positivity
  have hyb : y ^ a ≤ polylogConst a * x ^ (r / 2) := by
    unfold polylogConst
    rw [← hn]
    have := mul_le_mul_of_nonneg_left hexp hfac0
    nlinarith
  rw [hL, Real.mul_rpow (by positivity) hy0, mul_assoc]
  exact mul_le_mul_of_nonneg_left hyb (by positivity)

/-! ## Holomorphy and the zeta identity on `Re s > ½` -/

theorem locallyIntegrable_mertensC : LocallyIntegrable mertensC := by
  refine (Complex.continuous_ofReal.locallyIntegrable (μ := volume)).mono
    (Complex.measurable_ofReal.comp measurable_mertensFunctionReal).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [mertensC, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  exact abs_mertensFunctionReal_le_abs x

theorem mertensC_isBigO_rpow {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hM : ∀ x : ℝ, 1 ≤ x → |mertensFunctionReal x| ≤ Real.sqrt x * (1 + Real.log x) ^ a + C)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    mertensC =O[atTop] fun x : ℝ => x ^ (-(-(1 / 2 + δ))) := by
  refine IsBigO.of_bound ((1 / δ) ^ a * polylogConst a + C) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  rw [neg_neg, mertensC, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
  have hl := one_add_log_rpow_le ha (by linarith : 0 < 2 * δ) (by linarith) hx
  rw [show 2 / (2 * δ) = 1 / δ by field_simp, show 2 * δ / 2 = δ by ring] at hl
  have hsq : Real.sqrt x * x ^ δ = x ^ (1 / 2 + δ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
  have hx1 : 1 ≤ x ^ (1 / 2 + δ) := Real.one_le_rpow hx (by linarith)
  have hsqrt0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  calc |mertensFunctionReal x| ≤ Real.sqrt x * (1 + Real.log x) ^ a + C := hM x hx
    _ ≤ Real.sqrt x * ((1 / δ) ^ a * polylogConst a * x ^ δ) + C * x ^ (1 / 2 + δ) := by
        gcongr
        exact le_mul_of_one_le_right hC hx1
    _ = ((1 / δ) ^ a * polylogConst a + C) * x ^ (1 / 2 + δ) := by
        rw [← hsq]; ring

theorem differentiableOn_mertensMellin {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hM : ∀ x : ℝ, 1 ≤ x → |mertensFunctionReal x| ≤ Real.sqrt x * (1 + Real.log x) ^ a + C) :
    DifferentiableOn ℂ mertensMellin {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  have hs' : 1 / 2 < s.re := hs
  set δ : ℝ := min ((s.re - 1 / 2) / 2) (1 / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have hδs : δ ≤ (s.re - 1 / 2) / 2 := min_le_left _ _
  have hbot : mertensC =O[𝓝[>] 0] fun x : ℝ => x ^ (-(-s.re - 1)) := by
    refine IsBigO.of_bound 0 ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx
    rw [mertensC, mertensFunctionReal_eq_zero_of_lt_one hx.2]
    simp
  have hd : DifferentiableAt ℂ (mellin mertensC) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow (locallyIntegrable_mertensC.locallyIntegrableOn _)
      (mertensC_isBigO_rpow ha hC hM hδ0 hδ1) (by rw [Complex.neg_re]; linarith) hbot
      (by rw [Complex.neg_re]; linarith)
  exact (hd.comp s differentiableAt_id.neg).differentiableWithinAt

/-- **The zeta identity on `Re s > ½`.** -/
theorem mertensMellin_mul_eq {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hM : ∀ x : ℝ, 1 ≤ x → |mertensFunctionReal x| ≤ Real.sqrt x * (1 + Real.log x) ^ a + C)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    mertensMellin s * (s * zetaResidueUnit s) = s - 1 := by
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hFa : AnalyticOnNhd ℂ (fun s => mertensMellin s * (s * zetaResidueUnit s)) U :=
    ((differentiableOn_mertensMellin ha hC hM).mul (differentiableOn_id.mul
      (fun z _ => (analyticAt_zetaResidueUnit z).differentiableAt.differentiableWithinAt))).analyticOnNhd
      hUo
  have hGa : AnalyticOnNhd ℂ (fun s : ℂ => s - 1) U := fun z _ => analyticAt_id.sub analyticAt_const
  have h2U : (2 : ℂ) ∈ U := by simp [hU]; norm_num
  have hev : (fun s => mertensMellin s * (s * zetaResidueUnit s)) =ᶠ[𝓝 (2 : ℂ)]
      fun s : ℂ => s - 1 := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with w hw
    have hw1 : 1 < w.re := hw
    have hw0 : w ≠ 0 := by intro h; rw [h, Complex.zero_re] at hw1; linarith
    have hwne : w ≠ 1 := by intro h; rw [h, Complex.one_re] at hw1; linarith
    have hz : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hw1
    rw [mertensMellin_eq_inv hw1, zetaResidueUnit, Function.update_of_ne hwne]
    field_simp
  exact hFa.eqOn_of_preconnected_of_eventuallyEq hGa (convex_halfSpace_re_gt _).isPreconnected
    h2U hev hs

theorem riemannHypothesis_of_mertens_bound {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hM : ∀ x : ℝ, 1 ≤ x → |mertensFunctionReal x| ≤ Real.sqrt x * (1 + Real.log x) ^ a + C) :
    RiemannHypothesis := by
  rw [Sieve.riemannHypothesis_iff_zetaResidueUnit_ne_zero]
  intro s hs hzero
  have h := mertensMellin_mul_eq ha hC hM hs
  rw [hzero, mul_zero, mul_zero] at h
  have hs1 : s = 1 := (sub_eq_zero.mp h.symm)
  rw [hs1, zetaResidueUnit_one] at hzero
  exact one_ne_zero hzero

/-! ## The ray bound -/

theorem norm_mertensMellin_ray_le {a ε C : ℝ} (ha : 0 ≤ a) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hM : ∀ x : ℝ, 1 ≤ x →
      |mertensFunctionReal x| ≤ ε * Real.sqrt x * (1 + Real.log x) ^ a + C)
    {ρ : ℂ} (hρ : ρ.re = 1 / 2) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ‖mertensMellin (ρ + r)‖ ≤ ε * (polylogConst a * 2 ^ (a + 1)) * r ^ (-(a + 1)) + 2 * C := by
  set K : ℝ := polylogConst a with hK
  have hK0 : 0 < K := polylogConst_pos a
  set g : ℝ → ℝ := fun x => ε * ((2 / r) ^ a * K) * x ^ (-1 - r / 2) + C * x ^ (-3 / 2 - r)
    with hg
  have hi1 : IntegrableOn (fun x : ℝ => x ^ (-1 - r / 2)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hi2 : IntegrableOn (fun x : ℝ => x ^ (-3 / 2 - r)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hgi : IntegrableOn g (Ici 1) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact (hi1.const_mul _).add (hi2.const_mul _)
  have hbound : ∀ x ∈ Ici (1 : ℝ), ‖(x : ℂ) ^ (-(ρ + r) - 1) * mertensC x‖ ≤ g x := by
    intro x hx
    have hx1 : 1 ≤ x := hx
    have hx0 : 0 < x := by linarith
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, mertensC, Complex.norm_real,
      Real.norm_eq_abs]
    have hre : (-(ρ + (r : ℂ)) - 1).re = -3 / 2 - r := by
      simp [hρ]; ring
    rw [hre]
    have hl := one_add_log_rpow_le ha hr0 hr1 hx1
    have hxp : 0 < x ^ (-3 / 2 - r) := Real.rpow_pos_of_pos hx0 _
    have e1 : x ^ (-3 / 2 - r) * Real.sqrt x = x ^ (-1 - r) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]; ring_nf
    have e2 : x ^ (-1 - r) * x ^ (r / 2) = x ^ (-1 - r / 2) := by
      rw [← Real.rpow_add hx0]; ring_nf
    have hlogn : 0 ≤ (1 + Real.log x) ^ a := Real.rpow_nonneg (by linarith [Real.log_nonneg hx1]) a
    calc x ^ (-3 / 2 - r) * |mertensFunctionReal x|
        ≤ x ^ (-3 / 2 - r) * (ε * Real.sqrt x * (1 + Real.log x) ^ a + C) :=
          mul_le_mul_of_nonneg_left (hM x hx1) hxp.le
      _ = ε * (x ^ (-3 / 2 - r) * Real.sqrt x) * (1 + Real.log x) ^ a + C * x ^ (-3 / 2 - r) := by
          ring
      _ = ε * x ^ (-1 - r) * (1 + Real.log x) ^ a + C * x ^ (-3 / 2 - r) := by rw [e1]
      _ ≤ ε * x ^ (-1 - r) * ((2 / r) ^ a * K * x ^ (r / 2)) + C * x ^ (-3 / 2 - r) := by
          gcongr
      _ = g x := by
          rw [hg]
          simp only
          rw [← e2]
          ring
  have hle := norm_integral_le_of_norm_le hgi
    ((ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall hbound))
  rw [mertensMellin_eq_integral_Ici]
  refine hle.trans ?_
  have hint : ∫ x in Ici (1 : ℝ), g x =
      ε * ((2 / r) ^ a * K) * (2 / r) + C * (1 / (1 / 2 + r)) := by
    rw [integral_Ici_eq_integral_Ioi, hg, integral_add (hi1.const_mul _) (hi2.const_mul _),
      integral_const_mul, integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos,
      integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow, Real.one_rpow]
    rw [show (-1 - r / 2 + 1 : ℝ) = -(r / 2) by ring, show (-3 / 2 - r + 1 : ℝ) = -(1 / 2 + r) by ring,
      neg_div_neg_eq, neg_div_neg_eq, one_div_div]
  rw [hint]
  · have h2 : (2 / r) ^ a * (2 / r) = 2 ^ (a + 1) * r ^ (-(a + 1)) := by
      rw [Real.div_rpow (by norm_num) hr0.le, Real.rpow_add_one (by norm_num),
        Real.rpow_neg hr0.le, Real.rpow_add_one hr0.ne']
      field_simp
    have h3 : 1 / (1 / 2 + r) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    calc ε * ((2 / r) ^ a * K) * (2 / r) + C * (1 / (1 / 2 + r))
        = ε * K * ((2 / r) ^ a * (2 / r)) + C * (1 / (1 / 2 + r)) := by ring
      _ ≤ ε * K * (2 ^ (a + 1) * r ^ (-(a + 1))) + C * 2 := by
          rw [h2]; gcongr
      _ = ε * (K * 2 ^ (a + 1)) * r ^ (-(a + 1)) + 2 * C := by ring

/-! ## Strict multiplicity -/

/-- **Strict polylog multiplicity law.**  If `|M(x)| ≤ ε√x(1 + log x)^a + C_ε` for every `ε > 0`,
then `ζ` has order `< a + 1` at every point of the critical line. -/
theorem analyticOrderAt_riemannZeta_toNat_lt_of_mertens_littleO {a : ℝ} (ha : 0 ≤ a)
    (hM : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |mertensFunctionReal x| ≤ ε * Real.sqrt x * (1 + Real.log x) ^ a + C)
    {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    ((analyticOrderAt riemannZeta ρ).toNat : ℝ) < a + 1 := by
  obtain ⟨C₁, hC₁, hM₁⟩ := hM 1 one_pos
  have hM₁' : ∀ x : ℝ, 1 ≤ x →
      |mertensFunctionReal x| ≤ Real.sqrt x * (1 + Real.log x) ^ a + C₁ := fun x hx => by
    simpa using hM₁ x hx
  have hρpos : 0 < ρ.re := by rw [hρ]; norm_num
  have hρ1 : ρ ≠ 1 := by intro h; rw [h, Complex.one_re] at hρ; norm_num at hρ
  have hρ0 : ρ ≠ 0 := by intro h; rw [h, Complex.zero_re] at hρ; norm_num at hρ
  have horderFinite : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    rw [← xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hρpos, by rw [hρ]; norm_num⟩]
    exact xi_orderAt_ne_top ρ
  set n : ℕ := (analyticOrderAt riemannZeta ρ).toNat with hn
  have hncoe : (n : ℕ∞) = analyticOrderAt riemannZeta ρ := ENat.coe_toNat horderFinite
  have hzA : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ1
  obtain ⟨p, hp, _, hfactor⟩ := (hzA.analyticOrderAt_eq_natCast).mp hncoe.symm
  by_contra hlt
  have hn_ge : a + 1 ≤ (n : ℝ) := not_lt.mp hlt
  have hn1 : 1 ≤ n := by exact_mod_cast (show (1 : ℝ) ≤ n by linarith)
  have hray : Tendsto (fun r : ℝ => ρ + (r : ℂ)) (𝓝[>] 0) (𝓝 ρ) := by
    have h : Tendsto (fun r : ℝ => ρ + (r : ℂ)) (𝓝 0) (𝓝 (ρ + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    rw [Complex.ofReal_zero, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  -- the vanishing factor `r^n G(ρ + r)`
  set K' : ℝ := polylogConst a * 2 ^ (a + 1) with hK'
  have hK'0 : 0 < K' := mul_pos (polylogConst_pos a) (by positivity)
  have hsmall : Tendsto (fun r : ℝ => (r : ℂ) ^ n * mertensMellin (ρ + r)) (𝓝[>] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    obtain ⟨C, hC, hMC⟩ := hM (η / (4 * K')) (by positivity)
    set m : ℝ := min 1 (η / (4 * C + 1)) with hm
    have hm0 : 0 < m := lt_min one_pos (by positivity)
    filter_upwards [Ioo_mem_nhdsGT hm0] with r hr
    have hr0 : 0 < r := hr.1
    have hr1 : r ≤ 1 := hr.2.le.trans (min_le_left _ _)
    have hrC : r < η / (4 * C + 1) := hr.2.trans_le (min_le_right _ _)
    have hb := norm_mertensMellin_ray_le ha (by positivity) hC hMC hρ hr0 hr1
    rw [dist_zero_right, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    have hpow : r ^ n * r ^ (-(a + 1)) ≤ 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hr0]
      exact Real.rpow_le_one hr0.le hr1 (by linarith)
    have hrn : r ^ n ≤ r := by
      calc r ^ n ≤ r ^ 1 := pow_le_pow_of_le_one hr0.le hr1 hn1
        _ = r := pow_one r
    have hrn0 : 0 ≤ r ^ n := pow_nonneg hr0.le n
    have hrpow0 : 0 ≤ r ^ (-(a + 1)) := Real.rpow_nonneg hr0.le _
    have hCr : 2 * C * r ≤ η / 2 := by
      have h4 : (4 * C + 1) * r < η := by
        rwa [lt_div_iff₀ (by positivity), mul_comm] at hrC
      nlinarith
    calc r ^ n * ‖mertensMellin (ρ + r)‖
        ≤ r ^ n * (η / (4 * K') * K' * r ^ (-(a + 1)) + 2 * C) :=
          mul_le_mul_of_nonneg_left hb hrn0
      _ = η / 4 * (r ^ n * r ^ (-(a + 1))) + 2 * C * r ^ n := by
          field_simp
      _ ≤ η / 4 * 1 + 2 * C * r := by
          gcongr
      _ < η := by linarith
  -- the product with the zeta unit
  have hfactorRay : ∀ᶠ r : ℝ in 𝓝[>] 0,
      riemannZeta (ρ + (r : ℂ)) = (r : ℂ) ^ n * p (ρ + (r : ℂ)) := by
    filter_upwards [hray.eventually hfactor] with r hr
    simpa [smul_eq_mul] using hr
  have hnotOne : ∀ᶠ r : ℝ in 𝓝[>] 0, ρ + (r : ℂ) ≠ 1 :=
    hray.eventually (isOpen_compl_singleton.mem_nhds hρ1)
  have hother : Tendsto (fun r : ℝ => (ρ + (r : ℂ) - 1) * p (ρ + (r : ℂ))) (𝓝[>] 0)
      (𝓝 ((ρ - 1) * p ρ)) :=
    (((continuous_id.sub continuous_const).tendsto ρ).comp hray).mul
      (hp.continuousAt.tendsto.comp hray)
  have hzeroProd : Tendsto (fun r : ℝ => mertensMellin (ρ + r) * zetaResidueUnit (ρ + r))
      (𝓝[>] 0) (𝓝 0) := by
    have := hsmall.mul hother
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [hfactorRay, hnotOne] with r hfac hr1
    rw [zetaResidueUnit, Function.update_of_ne hr1, hfac]
    ring
  have hval : Tendsto (fun r : ℝ => mertensMellin (ρ + r) * zetaResidueUnit (ρ + r))
      (𝓝[>] 0) (𝓝 ((ρ - 1) / ρ)) := by
    have hlim : Tendsto (fun r : ℝ => (ρ + (r : ℂ) - 1) / (ρ + (r : ℂ))) (𝓝[>] 0)
        (𝓝 ((ρ - 1) / ρ)) :=
      (((continuous_id.sub continuous_const).tendsto ρ).comp hray).div hray hρ0
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : (0 : ℝ) < r := hr
    have hre : 1 / 2 < (ρ + (r : ℂ)).re := by simp [hρ]; linarith
    have hne : ρ + (r : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp [hρ] at this; linarith
    have hid := mertensMellin_mul_eq ha hC₁ hM₁' hre
    field_simp
    rw [← hid]
    ring
  have heq := tendsto_nhds_unique hval hzeroProd
  exact div_ne_zero (sub_ne_zero.mpr hρ1) hρ0 heq

/-- **RH with a strict multiplicity cap from a little-`o` polylog Mertens bound.** -/
theorem riemannHypothesis_and_order_lt_of_mertens_littleO {a : ℝ} (ha : 0 ≤ a)
    (hM : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |mertensFunctionReal x| ≤ ε * Real.sqrt x * (1 + Real.log x) ^ a + C) :
    RiemannHypothesis ∧ ∀ ρ : ℂ, ρ.re = 1 / 2 → riemannZeta ρ = 0 →
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) < a + 1 := by
  obtain ⟨C₁, hC₁, hM₁⟩ := hM 1 one_pos
  refine ⟨riemannHypothesis_of_mertens_bound ha hC₁ fun x hx => by simpa using hM₁ x hx,
    fun ρ hρ _ => analyticOrderAt_riemannZeta_toNat_lt_of_mertens_littleO ha hM hρ⟩

/-! ## Kronecker's lemma at `s = ½` -/

/-- The weight `√(n+1) (1 + log(n+1))^a`. -/
def mertensSqrtLogWeight (a : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) + 1) * (1 + Real.log ((n : ℝ) + 1)) ^ a

theorem mertensSqrtLogWeight_pos (a : ℝ) (n : ℕ) : 0 < mertensSqrtLogWeight a n := by
  unfold mertensSqrtLogWeight
  have h1 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith [n.cast_nonneg (α := ℝ)])
  exact mul_pos (Real.sqrt_pos.mpr (by positivity)) (Real.rpow_pos_of_pos (by linarith) a)

theorem mertensSqrtLogWeight_mono {a : ℝ} (ha : 0 ≤ a) {m n : ℕ} (h : m ≤ n) :
    mertensSqrtLogWeight a m ≤ mertensSqrtLogWeight a n := by
  unfold mertensSqrtLogWeight
  have hmn : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right h 1
  have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hl0 : 0 ≤ 1 + Real.log ((m : ℝ) + 1) := by
    linarith [Real.log_nonneg (by linarith [m.cast_nonneg (α := ℝ)] : (1 : ℝ) ≤ (m : ℝ) + 1)]
  exact mul_le_mul (Real.sqrt_le_sqrt hmn)
    (Real.rpow_le_rpow hl0 (by linarith [Real.log_le_log hm0 hmn]) ha)
    (Real.rpow_nonneg hl0 a) (Real.sqrt_nonneg _)

/-- **Kronecker's lemma for the weighted Möbius series.**  Convergence of
`Σ_{n ≥ 1} μ(n) n^{-1/2} (1 + log n)^{-a}` gives `|M(x)| ≤ ε√x(1 + log x)^a + C_ε`. -/
theorem mertens_littleO_of_weighted_converges {a : ℝ} (ha : 0 ≤ a)
    (hconv : ∃ L : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N,
      ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ) / mertensSqrtLogWeight a n) atTop (𝓝 L)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |mertensFunctionReal x| ≤ ε * Real.sqrt x * (1 + Real.log x) ^ a + C := by
  obtain ⟨L, hL⟩ := hconv
  intro ε hε
  set c : ℕ → ℝ := fun n => ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ) / mertensSqrtLogWeight a n
    with hc
  set S : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N, c n with hS
  obtain ⟨n₀, hn₀⟩ := (Metric.tendsto_atTop.mp hL) (ε / 4) (by positivity)
  have hμ : ∀ k : ℕ, |((ArithmeticFunction.moebius k : ℤ) : ℝ)| ≤ 1 := fun k => by
    rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  -- the partial sums of `μ(n+1)`
  have hpart : ∀ N : ℕ, |∑ n ∈ Finset.range N, ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ)|
      ≤ ε * mertensSqrtLogWeight a (N - 1) + n₀ := by
    intro N
    have hw0 : 0 ≤ ε * mertensSqrtLogWeight a (N - 1) := mul_nonneg hε.le (mertensSqrtLogWeight_pos a _).le
    rcases le_or_gt N n₀ with hN | hN
    · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun n _ => hμ (n + 1)).trans ?_
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      have : (N : ℝ) ≤ n₀ := by exact_mod_cast hN
      linarith
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hN.le
      have hterm : ∀ n, ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ) =
          mertensSqrtLogWeight a n * c n := fun n => by
        rw [hc]; field_simp [(mertensSqrtLogWeight_pos a n).ne']
      simp_rw [hterm]
      rw [Finset.sum_range_add]
      have hhead : |∑ n ∈ Finset.range n₀, mertensSqrtLogWeight a n * c n| ≤ n₀ := by
        simp_rw [← hterm]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun n _ => hμ (n + 1)).trans ?_
        simp
      have hB : ∀ k, |∑ j ∈ Finset.range k, c (n₀ + j)| ≤ ε / 2 := by
        intro k
        have e : ∑ j ∈ Finset.range k, c (n₀ + j) = S (n₀ + k) - S n₀ := by
          simp only [hS, Finset.sum_range_add, add_sub_cancel_left]
        rw [e]
        have h1 := hn₀ (n₀ + k) (Nat.le_add_right _ _)
        have h2 := hn₀ n₀ le_rfl
        rw [Real.dist_eq] at h1 h2
        calc |S (n₀ + k) - S n₀| = |(S (n₀ + k) - L) - (S n₀ - L)| := by ring_nf
          _ ≤ |S (n₀ + k) - L| + |S n₀ - L| := abs_sub _ _
          _ ≤ ε / 2 := by linarith
      have htail := abs_sum_mul_le_of_bounded_partial_mono (g := fun j => c (n₀ + j))
        (w := fun j => mertensSqrtLogWeight a (n₀ + j)) m hB
        (fun i => (mertensSqrtLogWeight_pos a _).le)
        (fun i => mertensSqrtLogWeight_mono ha (by omega))
      have hidx : n₀ + (m - 1) ≤ n₀ + m - 1 := by omega
      have hwle : mertensSqrtLogWeight a (n₀ + (m - 1)) ≤ mertensSqrtLogWeight a (n₀ + m - 1) :=
        mertensSqrtLogWeight_mono ha hidx
      calc |∑ n ∈ Finset.range n₀, mertensSqrtLogWeight a n * c n +
            ∑ j ∈ Finset.range m, mertensSqrtLogWeight a (n₀ + j) * c (n₀ + j)|
          ≤ |∑ n ∈ Finset.range n₀, mertensSqrtLogWeight a n * c n| +
            |∑ j ∈ Finset.range m, mertensSqrtLogWeight a (n₀ + j) * c (n₀ + j)| := abs_add_le _ _
        _ ≤ n₀ + 2 * (ε / 2) * mertensSqrtLogWeight a (n₀ + (m - 1)) := add_le_add hhead htail
        _ ≤ ε * mertensSqrtLogWeight a (n₀ + m - 1) + n₀ := by
            have := mul_le_mul_of_nonneg_left hwle hε.le
            linarith
  refine ⟨n₀, by positivity, fun x hx => ?_⟩
  set N : ℕ := ⌊x⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hMeq : mertensFunctionReal x =
      ∑ n ∈ Finset.range N, ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ) := by
    rw [sum_range_succ_eq_sourcePartialSum (fun k => ((ArithmeticFunction.moebius k : ℤ) : ℝ)) N]
    rfl
  have hw : mertensSqrtLogWeight a (N - 1) ≤ Real.sqrt x * (1 + Real.log x) ^ a := by
    unfold mertensSqrtLogWeight
    have hc : ((N - 1 : ℕ) : ℝ) + 1 = N := by
      rw [Nat.cast_sub hN1, Nat.cast_one, sub_add_cancel]
    rw [hc]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hl0 : 0 ≤ 1 + Real.log (N : ℝ) := by
      linarith [Real.log_nonneg (by exact_mod_cast hN1 : (1 : ℝ) ≤ N)]
    exact mul_le_mul (Real.sqrt_le_sqrt hNx)
      (Real.rpow_le_rpow hl0 (by linarith [Real.log_le_log hN0 hNx]) ha)
      (Real.rpow_nonneg hl0 a) (Real.sqrt_nonneg _)
  rw [hMeq]
  calc _ ≤ ε * mertensSqrtLogWeight a (N - 1) + n₀ := hpart N
    _ ≤ ε * (Real.sqrt x * (1 + Real.log x) ^ a) + n₀ := by gcongr
    _ = ε * Real.sqrt x * (1 + Real.log x) ^ a + n₀ := by ring

/-- **A single-point receiver at `s = ½`.**  If `Σ_{n ≥ 1} μ(n) n^{-1/2} (1 + log n)^{-a}`
converges, then RH holds and every critical zero has order `< a + 1`. -/
theorem riemannHypothesis_and_order_lt_of_weighted_moebius_converges {a : ℝ} (ha : 0 ≤ a)
    (hconv : ∃ L : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N,
      ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ) / mertensSqrtLogWeight a n) atTop (𝓝 L)) :
    RiemannHypothesis ∧ ∀ ρ : ℂ, ρ.re = 1 / 2 → riemannZeta ρ = 0 →
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) < a + 1 :=
  riemannHypothesis_and_order_lt_of_mertens_littleO ha
    (mertens_littleO_of_weighted_converges ha hconv)

theorem one_le_analyticOrderAt_riemannZeta_toNat_of_critical {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hzero : riemannZeta ρ = 0) : 1 ≤ (analyticOrderAt riemannZeta ρ).toNat := by
  have hρpos : 0 < ρ.re := by rw [hρ]; norm_num
  have hρ1 : ρ ≠ 1 := by intro h; rw [h, Complex.one_re] at hρ; norm_num at hρ
  have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    rw [← xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hρpos, by rw [hρ]; norm_num⟩]
    exact xi_orderAt_ne_top ρ
  have hne : analyticOrderAt riemannZeta ρ ≠ 0 := by
    rw [Ne, analyticOrderAt_eq_zero]
    rintro (h | h)
    exacts [h (analyticOn_riemannZeta ρ hρ1), h hzero]
  rw [Nat.one_le_iff_ne_zero]
  intro h
  exact hne ((ENat.toNat_eq_zero.mp h).resolve_right hfin)

/-- **Simplicity from convergence at `½`.**  For `0 ≤ a ≤ 1`, convergence of
`Σ μ(n) n^{-1/2} (1 + log n)^{-a}` forces RH and every critical zero to be simple. -/
theorem riemannHypothesis_and_simple_of_weighted_moebius_converges {a : ℝ} (ha : 0 ≤ a)
    (ha1 : a ≤ 1)
    (hconv : ∃ L : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N,
      ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ) / mertensSqrtLogWeight a n) atTop (𝓝 L)) :
    RiemannHypothesis ∧ ∀ ρ : ℂ, ρ.re = 1 / 2 → riemannZeta ρ = 0 →
      analyticOrderAt riemannZeta ρ = 1 := by
  obtain ⟨hRH, hord⟩ := riemannHypothesis_and_order_lt_of_weighted_moebius_converges ha hconv
  refine ⟨hRH, fun ρ hρ hzero => ?_⟩
  have h1 := one_le_analyticOrderAt_riemannZeta_toNat_of_critical hρ hzero
  have h2 : (analyticOrderAt riemannZeta ρ).toNat < 2 := by
    have := hord ρ hρ hzero
    exact_mod_cast (show ((analyticOrderAt riemannZeta ρ).toNat : ℝ) < 2 by linarith)
  have hρpos : 0 < ρ.re := by rw [hρ]; norm_num
  have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    rw [← xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hρpos, by rw [hρ]; norm_num⟩]
    exact xi_orderAt_ne_top ρ
  rw [← ENat.coe_toNat hfin]
  exact_mod_cast (show (analyticOrderAt riemannZeta ρ).toNat = 1 by omega)

/-- **`Σ μ(n)/√n` diverges.**  Unconditionally, the partial sums of `Σ_{n ≥ 1} μ(n) n^{-1/2}` do
not converge. -/
theorem not_moebius_div_sqrt_converges :
    ¬ ∃ L : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N,
      ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ) / Real.sqrt ((n : ℝ) + 1)) atTop (𝓝 L) := by
  intro hconv
  have hw : ∀ n : ℕ, mertensSqrtLogWeight 0 n = Real.sqrt ((n : ℝ) + 1) := fun n => by
    simp [mertensSqrtLogWeight]
  obtain ⟨-, hord⟩ := riemannHypothesis_and_order_lt_of_weighted_moebius_converges le_rfl
    (by simpa only [hw] using hconv)
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
  have h2 := hord ρ hρre hz
  have : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by exact_mod_cast h1
  linarith

end

end RHTower
