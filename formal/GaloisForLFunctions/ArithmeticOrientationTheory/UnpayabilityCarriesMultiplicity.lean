import GaloisForLFunctions.ArithmeticOrientationTheory.ATowerPoleObstructsAVerticalProgression
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DoubleZeroKernelsAndLogarithmicSmoothPowerAtThePole

/-!
# Unpayability carries multiplicity

The obstruction hull records where payment fails, not how badly.  The logarithmic smooth power
`ℓ_ε(d) = (log d) d^{−ε}` has Dirichlet series `−ζ'(s + ε)`, a double pole at `1 − ε`.  For
`0 < ε < ½`:

* **Same hull as the smooth power** (`mem_obstructionHull_logPower_iff`): the hull of `ℓ_ε` is the
  single pole point, exactly as for `d^{−ε}`.  Every repairing kernel vanishes there, by the
  continuation of a paid receiver across the strip (`lSeries_eq_zero_of_repairs_logPower`); any other
  point is avoided by the square of a local factor.
* **A smaller, non-radical ideal** (`not_isRadical_paidIdeal_logPower`): the local factor
  `δ₁ − 2^{1−ε} δ₂` vanishes simply at the pole and does not repair `ℓ_ε`, while its square does.  So
  `P(ℓ_ε) ⊊ P(d^{−ε})` (`paidIdeal_logPower_lt_smoothPower`) although the hulls coincide.
* **The index reads the order** (`two_le_rank_quotient_paidIdeal_logPower`): `𝒲_{1/2}/P(ℓ_ε)` has
  rank at least `2`, against `1` for the smooth power.

The repairing ideal is a scheme, not a set: its length counts the order of the pole.
-/

open Finset ArithmeticFunction LSeries Complex Filter Topology
open scoped LSeries.notation ArithmeticFunction.zeta

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open TransHorizonIncidenceMechanics WienerAlgebraAt

noncomputable section
set_option autoImplicit false

/-- The logarithmic smooth power `(log d) d^{−ε}`. -/
abbrev logPower (ε : ℝ) : ℕ → ℝ := logWeight (dampedSignWeight unitSign ε)

theorem logPower_apply (ε : ℝ) (d : ℕ) : logPower ε d = (d : ℝ) ^ (-ε) * Real.log d := by
  simp [logWeight, dampedSignWeight, unitSign]

theorem summable_logPower_rpow {ε θ : ℝ} (h : 1 < θ + ε) :
    Summable fun n : ℕ => |logPower ε n| * (n : ℝ) ^ (-θ) := by
  set η := (θ + ε - 1) / 2
  have hη : 0 < η := by simp only [η]; linarith
  refine ((Real.summable_nat_rpow.mpr (by simp only [η]; linarith : -(θ + ε - η) < -1)).mul_left
    η⁻¹).of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [logPower_apply, Nat.cast_zero, Real.log_zero, mul_zero, abs_zero, zero_mul]
    positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  rw [logPower_apply, abs_mul, abs_of_nonneg (Real.rpow_nonneg hn0.le _), abs_of_nonneg hlog]
  have hle := Real.log_le_rpow_div hn0.le hη
  calc (n : ℝ) ^ (-ε) * Real.log n * (n : ℝ) ^ (-θ)
      ≤ (n : ℝ) ^ (-ε) * ((n : ℝ) ^ η / η) * (n : ℝ) ^ (-θ) := by gcongr
    _ = η⁻¹ * (n : ℝ) ^ (-(θ + ε - η)) := by
        rw [div_eq_mul_inv]
        have : (n : ℝ) ^ (-ε) * (n : ℝ) ^ η * (n : ℝ) ^ (-θ) = (n : ℝ) ^ (-(θ + ε - η)) := by
          rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]; ring_nf
        rw [← this]; ring

theorem summable_abs_logPower_div {ε : ℝ} (hε : 0 < ε) :
    Summable fun d : ℕ => |logPower ε d / d| :=
  (summable_logPower_rpow (by linarith : 1 < 1 + ε)).congr fun d => by
    rw [abs_div, Nat.abs_cast, Real.rpow_neg_one, div_eq_mul_inv]

/-! ### The Dirichlet series `−ζ'(s + ε)` -/

theorem lSeries_logPower {ε : ℝ} {w : ℂ} (hw : 1 < w.re + ε) :
    LSeries (cplx (logPower ε)) w = -deriv riemannZeta (w + ε) := by
  have hre : 1 < (w + ε).re := by simpa using hw
  have h1 : LSeries (cplx (logPower ε)) w = LSeries (logMul ↗ζ) (w + ε) := by
    unfold LSeries
    refine tsum_congr fun d => ?_
    rcases eq_or_ne d 0 with rfl | hd
    · simp
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
    rw [term_of_ne_zero hd, term_of_ne_zero hd, cplx, logPower_apply]
    simp only [logMul, ArithmeticFunction.zeta_apply, hd, if_false, Nat.cast_one, mul_one]
    rw [Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg d), Complex.ofReal_natCast,
      ← Complex.natCast_log, Complex.cpow_add _ _ hd', Complex.ofReal_neg, Complex.cpow_neg]
    have h2 : (d : ℂ) ^ w ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hd' h.1
    have h3 : (d : ℂ) ^ ((ε : ℝ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hd' h.1
    field_simp
  have hab : abscissaOfAbsConv (↗ζ : ℕ → ℂ) < (w + ε).re := by
    refine lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (x := 1) fun y hy => ?_) (by exact_mod_cast hre)
    exact ArithmeticFunction.LSeriesSummable_zeta_iff.2 (by simpa using hy)
  have h2 : deriv riemannZeta (w + ε) = -LSeries (logMul ↗ζ) (w + ε) := by
    rw [← LSeries_deriv hab]
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre] with z hz
    exact (LSeries_zeta_eq_riemannZeta hz).symm
  rw [h1, h2, neg_neg]

/-- Near a regular point, `(w − 1)² ζ'(w) = (w − 1) Z'(w) − Z(w)` with `Z(w) = (w − 1) ζ(w)`. -/
theorem sq_mul_deriv_riemannZeta {w : ℂ} (hw : w ≠ 1) :
    (w - 1) ^ 2 * deriv riemannZeta w =
      (w - 1) * deriv RHTower.zetaResidueUnit w - RHTower.zetaResidueUnit w := by
  have hd : deriv RHTower.zetaResidueUnit w = riemannZeta w + (w - 1) * deriv riemannZeta w := by
    rw [(RHTower.zetaResidueUnit_eventuallyEq hw).deriv_eq]
    have h2 : HasDerivAt (fun s => (s - 1) * riemannZeta s)
        (1 * riemannZeta w + (w - 1) * deriv riemannZeta w) w :=
      ((hasDerivAt_id' w).sub_const 1).mul (differentiableAt_riemannZeta hw).hasDerivAt
    rw [h2.deriv]; ring
  rw [hd, RHTower.zetaResidueUnit, Function.update_of_ne hw]
  ring

/-! ### Repairing kernels vanish at the pole -/

/-- **A repairing kernel vanishes at the pole**: if `k ⋆ ℓ_ε` is paid then `K(1 − ε) = 0`. -/
theorem lSeries_eq_zero_of_repairs_logPower {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {k : ℕ → ℝ}
    (hk : CriticalWiener k) (hB : ReceiverBounded (RHTower.dirichletConv k (logPower ε))) :
    LSeries (cplx k) ((1 - ε : ℝ) : ℂ) = 0 := by
  set c := RHTower.dirichletConv k (logPower ε)
  obtain ⟨E, hE⟩ := hB
  have hcθ : ∀ θ : ℝ, 1 - ε < θ → Summable fun d : ℕ => |c d| * (d : ℝ) ^ (-θ) := fun θ hθ =>
    summable_abs_dirichletConv_rpow (by linarith) (summable_kernel_rpow hε hε2 hk (by linarith))
      (summable_logPower_rpow (ε := ε) (θ := θ) (by linarith))
  obtain ⟨Φ, hΦ, hΦσ⟩ := exists_holomorphic_continuation (a := 1 - ε) (by linarith) hcθ hE
  set m : ℂ := ((∑' d : ℕ, c d / d : ℝ) : ℂ)
  set U : Set ℂ := {z | 1 / 2 < z.re ∧ z.re < 1}
  set Z := RHTower.zetaResidueUnit
  have hUopen : IsOpen {z : ℂ | 1 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hΦa : AnalyticOnNhd ℂ Φ {z : ℂ | 1 / 2 < z.re} := hΦ.analyticOnNhd hUopen
  have hZa : ∀ z : ℂ, AnalyticAt ℂ (fun w : ℂ => Z (w + ε)) z := fun z =>
    (RHTower.analyticAt_zetaResidueUnit (z + ε)).comp (f := fun w : ℂ => w + (ε : ℂ))
      (analyticAt_id.add analyticAt_const)
  have hZ'a : ∀ z : ℂ, AnalyticAt ℂ (fun w : ℂ => deriv Z (w + ε)) z := fun z =>
    (RHTower.analyticAt_zetaResidueUnit (z + ε)).deriv.comp (f := fun w : ℂ => w + (ε : ℂ))
      (analyticAt_id.add analyticAt_const)
  have hζ : ∀ z ∈ U, AnalyticAt ℂ riemannZeta z := fun z hz' =>
    RHTower.Sieve.analyticAt_riemannZeta_of_ne_one fun h => by
      have := congrArg Complex.re h; simp at this; linarith [hz'.2]
  set G : ℂ → ℂ := fun z => Z (z + ε) - (z + ε - 1) * deriv Z (z + ε)
  have hGa : ∀ z : ℂ, AnalyticAt ℂ G z := fun z =>
    (hZa z).sub (((analyticAt_id.add analyticAt_const).sub analyticAt_const).mul (hZ'a z))
  have hL : AnalyticOnNhd ℂ (fun z => (z + ε - 1) ^ 2 * Φ z) U := fun z hz' =>
    (((analyticAt_id.add analyticAt_const).sub analyticAt_const).pow 2).mul (hΦa z hz'.1)
  have hR : AnalyticOnNhd ℂ (fun z => riemannZeta z *
      (LSeries (cplx k) z * G z - m * (z + ε - 1) ^ 2)) U := fun z hz' =>
    (hζ z hz').mul (((analyticOnNhd_lSeries_kernel hk z hz'.1).mul (hGa z)).sub
      (analyticAt_const.mul (((analyticAt_id.add analyticAt_const).sub analyticAt_const).pow 2)))
  have hreal : ∀ σ : ℝ, 1 - ε < σ → σ < 1 →
      ((σ : ℂ) + ε - 1) ^ 2 * Φ σ =
        riemannZeta σ * (LSeries (cplx k) σ * G σ - m * ((σ : ℂ) + ε - 1) ^ 2) := by
    intro σ hσ hσ1
    have hσ0 : 0 < σ := by linarith
    have hne : (σ : ℂ) + ε ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hkσ := (lSeriesSummable_cplx_iff hσ0).2 (summable_kernel_rpow hε hε2 hk (by linarith))
    have hlσ := (lSeriesSummable_cplx_iff hσ0).2
      (summable_logPower_rpow (ε := ε) (θ := σ) (by linarith))
    have hC : LSeries (cplx c) σ = LSeries (cplx k) σ * -deriv riemannZeta ((σ : ℂ) + ε) := by
      rw [cplx_dirichletConv, LSeries_convolution' hkσ hlσ, lSeries_logPower (by simp; linarith)]
    have hsq := sq_mul_deriv_riemannZeta hne
    rw [hΦσ σ hσ hσ1, Complex.ofReal_sub, ofReal_tsum_rpow _ hσ0, hC]
    simp only [G, Z]
    rw [show ((σ : ℂ) + ε - 1) ^ 2 * (riemannZeta σ * (LSeries (cplx k) σ *
        -deriv riemannZeta ((σ : ℂ) + ε) - m)) = riemannZeta σ * (LSeries (cplx k) σ *
        -(((σ : ℂ) + ε - 1) ^ 2 * deriv riemannZeta ((σ : ℂ) + ε)) - m * ((σ : ℂ) + ε - 1) ^ 2)
        by ring, hsq]
    ring
  set r : ℂ := ((1 - ε / 2 : ℝ) : ℂ)
  have hrU : r ∈ U := by
    simp only [U, Set.mem_setOf_eq, r, Complex.ofReal_re]; constructor <;> linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] r, (z + ε - 1) ^ 2 * Φ z =
      riemannZeta z * (LSeries (cplx k) z * G z - m * (z + ε - 1) ^ 2) := by
    rw [Filter.frequently_iff]
    intro V hV
    obtain ⟨r0, hr0, hball⟩ := Metric.mem_nhdsWithin_iff.1 hV
    set η := min (r0 / 2) (ε / 4)
    have hη : 0 < η := lt_min (by linarith) (by linarith)
    refine ⟨((1 - ε / 2 + η : ℝ) : ℂ), hball ⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        show 1 - ε / 2 + η - (1 - ε / 2) = η by ring, abs_of_pos hη]
      exact (min_le_left _ _).trans_lt (by linarith)
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, r]
      intro h
      have := Complex.ofReal_injective h
      linarith
    · exact hreal _ (by linarith) (by linarith [min_le_right (r0 / 2) (ε / 4)])
  have heq := hL.eqOn_of_preconnected_of_frequently_eq hR
    ((convex_halfSpace_re_gt (1 / 2)).inter (convex_halfSpace_re_lt 1)).isPreconnected hrU hfreq
  have hs0 : ((1 - ε : ℝ) : ℂ) ∈ U := by
    simp only [U, Set.mem_setOf_eq, Complex.ofReal_re]; constructor <;> linarith
  have h := heq hs0
  have hzero : ((1 - ε : ℝ) : ℂ) + ε - 1 = 0 := by push_cast; ring
  have hG1 : G ((1 - ε : ℝ) : ℂ) = 1 := by
    simp only [G, hzero, zero_mul, sub_zero]
    rw [show ((1 - ε : ℝ) : ℂ) + ε = 1 by push_cast; ring]
    exact RHTower.zetaResidueUnit_one
  simp only [hzero, hG1, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
    mul_zero, sub_zero, mul_one] at h
  have hζ0 : riemannZeta ((1 - ε : ℝ) : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_pos_of_lt_one (by linarith) (by linarith)
  exact (mul_eq_zero.1 h.symm).resolve_left hζ0

/-! ### Real kernels in the repairing ideal -/

theorem rePart_toWiener (g : ℕ → ℝ) (hg : CriticalWiener g) :
    rePart (toWiener g hg) = fun n => if n = 0 then 0 else g n := funext fun n => by
  rcases eq_or_ne n 0 with rfl | hn <;> simp [rePart, toWiener, toFn_mk, realFn, *]

theorem imPart_toWiener (g : ℕ → ℝ) (hg : CriticalWiener g) :
    imPart (toWiener g hg) = fun _ => 0 := funext fun n => by
  rcases eq_or_ne n 0 with rfl | hn <;> simp [imPart, toWiener, toFn_mk, realFn, *]

/-- A real kernel repairs `c` iff its convolution with `c` is paid. -/
theorem toWiener_mem_paidIdeal_iff (c : ℕ → ℝ) (hc : Summable fun d : ℕ => |c d / d|)
    (g : ℕ → ℝ) (hg : CriticalWiener g) :
    toWiener g hg ∈ paidIdeal c hc ↔ ReceiverBounded (RHTower.dirichletConv g c) := by
  rw [mem_paidIdeal, rePart_toWiener, imPart_toWiener, dirichletConv_zero_left]
  have h : RHTower.dirichletConv (fun n => if n = 0 then 0 else g n) c = RHTower.dirichletConv g c :=
    funext fun n => dirichletConv_congr (fun m hm => if_neg hm) (fun _ _ => rfl) n
  rw [h]
  exact ⟨fun h => h.1, fun h => ⟨h, receiverBounded_zero⟩⟩

theorem toWiener_mul (a b : ℕ → ℝ) (ha : CriticalWiener a) (hb : CriticalWiener b) :
    toWiener a ha * toWiener b hb =
      toWiener (RHTower.dirichletConv a b) (criticalWiener_dirichletConv ha hb) :=
  toFn_injective (by rw [toFn_mul]; exact (realFn_dirichletConv a b).symm)

/-! ### The local factor at the pole and its square -/

variable {ε : ℝ} {p : ℕ}

/-- `δ₁ − p^{1−ε} δ_p`, vanishing simply at the pole `1 − ε`. -/
abbrev poleFactor (ε : ℝ) (p : ℕ) : ℕ → ℝ := localFactorKernel p ((p : ℝ) ^ (1 - ε))

theorem poleFactor_conv_apply (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) :
    RHTower.dirichletConv (poleFactor ε p) (poleFactor ε p) n =
      if n = 1 then 1 else if n = p then -(2 * (p : ℝ) ^ (1 - ε))
        else if n = p ^ 2 then ((p : ℝ) ^ (1 - ε)) ^ 2 else 0 := by
  rw [dirichletConv_localFactorKernel hp _ _ hn]
  have hp1 : p ≠ 1 := hp.one_lt.ne'
  have hpp : p ≠ p ^ 2 := by
    intro h; have := Nat.pow_right_injective hp.two_le (h.symm.trans (pow_one p).symm); omega
  have h1p : (1 : ℕ) ≠ p ^ 2 := by
    intro h; have := (Nat.one_lt_pow two_ne_zero hp.one_lt).ne; exact this h
  by_cases h1 : n = 1
  · subst h1
    simp [localFactorKernel, hp.not_dvd_one]
  by_cases h2 : n = p
  · subst h2
    simp [localFactorKernel, hp1, Nat.div_self hp.pos]; ring
  by_cases h3 : n = p ^ 2
  · subst h3
    have hdvd : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
    rw [if_neg h1p.symm, if_neg hpp.symm, if_pos rfl, if_pos hdvd,
      Nat.pow_div (by norm_num) hp.pos]
    simp [localFactorKernel, hp1, hpp.symm, h1p.symm]; ring
  rw [if_neg h1, if_neg h2, if_neg h3]
  simp only [localFactorKernel, if_neg h1, if_neg h2]
  split_ifs with hd h4 h5
  · exfalso; exact h1 (by rw [← Nat.div_mul_cancel hd, h4, one_mul])
  · exfalso; exact h3 (by rw [← Nat.div_mul_cancel hd, h5, sq])
  · ring
  · ring

theorem poleFactor_conv_eq_zero (hp : p.Prime) {n : ℕ} (hn : p ^ 2 < n) :
    RHTower.dirichletConv (poleFactor ε p) (poleFactor ε p) n = 0 := by
  have hp2 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
  have hpp : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  rw [poleFactor_conv_apply hp (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem poleFactor_eq_zero (hp : p.Prime) {n : ℕ} (hn : p < n) : poleFactor ε p n = 0 := by
  have : n ≠ 1 := by have := hp.one_lt; omega
  simp [localFactorKernel, this, (by omega : n ≠ p)]

theorem rpow_pole (hp : p.Prime) : (p : ℝ) ^ (1 - ε) * (p : ℝ) ^ (-(1 - ε)) = 1 := by
  rw [← Real.rpow_add (by exact_mod_cast hp.pos)]; simp

/-- A sum over `Icc 1 J` of a function supported on `S ⊆ Icc 1 J`. -/
theorem sum_Icc_eq_of_support {f : ℕ → ℝ} {J : ℕ} (S : Finset ℕ) (hS : S ⊆ Icc 1 J)
    (hf : ∀ j ∈ Icc 1 J, j ∉ S → f j = 0) : ∑ j ∈ Icc 1 J, f j = ∑ j ∈ S, f j :=
  (sum_subset hS hf).symm

/-- The local factor at the pole does not repair `ℓ_ε`: its slope there is `−log p`. -/
theorem not_receiverBounded_poleFactor (hε : 0 < ε) (hε2 : ε < 1 / 2) (hp : p.Prime) :
    ¬ ReceiverBounded (RHTower.dirichletConv (poleFactor ε p) (logPower ε)) := by
  intro h
  have hp1 : p ≠ 1 := hp.one_lt.ne'
  have hsupp : ∀ j, p < j → poleFactor ε p j = 0 := fun j hj => poleFactor_eq_zero hp hj
  obtain ⟨-, hslope⟩ := (receiverBounded_dirichletConv_logWeight_unit_iff hε hε2.le hsupp).1 h
  have hS : ({1, p} : Finset ℕ) ⊆ Icc 1 p := by
    intro j hj; simp only [mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl <;> simp [hp.one_le]
  unfold poleSlope at hslope
  rw [sum_Icc_eq_of_support {1, p} hS fun j hj hjS => by
      simp only [mem_insert, mem_singleton, not_or] at hjS
      simp [localFactorKernel, hjS.1, hjS.2],
    sum_pair (Ne.symm hp1)] at hslope
  have hlog : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have := rpow_pole (ε := ε) hp
  simp [localFactorKernel, hp1] at hslope
  apply hlog
  nlinarith [this]

/-- Its square repairs `ℓ_ε`: value and slope at the pole vanish. -/
theorem receiverBounded_poleFactor_sq (hε : 0 < ε) (hε2 : ε < 1 / 2) (hp : p.Prime) :
    ReceiverBounded (RHTower.dirichletConv
      (RHTower.dirichletConv (poleFactor ε p) (poleFactor ε p)) (logPower ε)) := by
  have hp1 : p ≠ 1 := hp.one_lt.ne'
  have hp2 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
  have hpp : p ≠ p ^ 2 := by
    intro h; have := Nat.pow_right_injective hp.two_le (h.symm.trans (pow_one p).symm); omega
  have hsupp : ∀ j, p ^ 2 < j →
      RHTower.dirichletConv (poleFactor ε p) (poleFactor ε p) j = 0 := fun j hj =>
    poleFactor_conv_eq_zero hp hj
  have hS : ({1, p, p ^ 2} : Finset ℕ) ⊆ Icc 1 (p ^ 2) := by
    intro j hj; simp only [mem_insert, mem_singleton] at hj
    have : p ≤ p ^ 2 := Nat.le_self_pow two_ne_zero p
    rcases hj with rfl | rfl | rfl <;> simp only [mem_Icc] <;> omega
  have hval : ∀ j ∈ Icc 1 (p ^ 2), j ∉ ({1, p, p ^ 2} : Finset ℕ) →
      RHTower.dirichletConv (poleFactor ε p) (poleFactor ε p) j = 0 := fun j hj hjS => by
    simp only [mem_insert, mem_singleton, not_or] at hjS
    rw [poleFactor_conv_apply hp (by simp only [mem_Icc] at hj; omega), if_neg hjS.1,
      if_neg hjS.2.1, if_neg hjS.2.2]
  set b := (p : ℝ) ^ (1 - ε)
  set w := (p : ℝ) ^ (-(1 - ε))
  have hbw : b * w = 1 := rpow_pole hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hw2 : ((p ^ 2 : ℕ) : ℝ) ^ (-(1 - ε)) = w ^ 2 := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_natCast,
      ← Real.rpow_mul hp0.le]; ring_nf
  have hl2 : Real.log ((p ^ 2 : ℕ) : ℝ) = 2 * Real.log p := by
    rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hdist : (1 : ℕ) ∉ ({p, p ^ 2} : Finset ℕ) := by
    simp only [mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm hp1, by omega⟩
  have hdist' : p ∉ ({p ^ 2} : Finset ℕ) := by simpa using hpp
  refine (receiverBounded_dirichletConv_logWeight_unit_iff hε hε2.le hsupp).2 ⟨?_, ?_⟩
  · unfold poleValue
    rw [sum_Icc_eq_of_support _ hS fun j hj hjS => by rw [hval j hj hjS, zero_mul],
      sum_insert hdist, sum_insert hdist', sum_singleton,
      poleFactor_conv_apply hp one_ne_zero, poleFactor_conv_apply hp hp.ne_zero,
      poleFactor_conv_apply hp (by omega), hw2]
    simp only [if_true, if_neg (Ne.symm hp1), if_neg (by omega : p ^ 2 ≠ 1),
      if_neg (Ne.symm hpp), Nat.cast_one, Real.one_rpow]
    nlinarith [hbw]
  · unfold poleSlope
    rw [sum_Icc_eq_of_support _ hS fun j hj hjS => by rw [hval j hj hjS, zero_mul, zero_mul],
      sum_insert hdist, sum_insert hdist', sum_singleton,
      poleFactor_conv_apply hp one_ne_zero, poleFactor_conv_apply hp hp.ne_zero,
      poleFactor_conv_apply hp (by omega), hw2, hl2]
    simp only [if_true, if_neg (Ne.symm hp1), if_neg (by omega : p ^ 2 ≠ 1),
      if_neg (Ne.symm hpp), Nat.cast_one, Real.log_one, mul_zero, zero_mul]
    have : b ^ 2 * w ^ 2 = 1 := by rw [← mul_pow, hbw, one_pow]
    nlinarith [hbw, this]

/-- The Bohr transform of the local factor at the pole. -/
theorem bohrEval_poleFactor (hp : p.Prime) (ω : BohrPoint) :
    bohrEval (1 / 2) (toWiener _ (criticalWiener_localFactorKernel p ((p : ℝ) ^ (1 - ε)))).toFn ω =
      1 - ((p : ℝ) ^ (1 - ε) : ℂ) * ω.ω p / (p : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) := by
  have hp1 : p ≠ 1 := hp.one_lt.ne'
  unfold bohrEval LSeries
  rw [tsum_eq_sum (s := {1, p}) fun m hm => ?_, sum_pair (Ne.symm hp1)]
  · rw [term_of_ne_zero one_ne_zero, term_of_ne_zero hp.ne_zero]
    simp [toWiener, toFn_mk, realFn, localFactorKernel, hp1, hp.ne_zero, ω.map_one]
    ring
  · simp only [mem_insert, mem_singleton, not_or] at hm
    rcases eq_or_ne m 0 with rfl | hm0
    · simp
    rw [term_of_ne_zero hm0]
    simp [toWiener, toFn_mk, realFn, localFactorKernel, hm.1, hm.2, hm0]

theorem bohrEval_poleFactor_polePoint (hε2 : ε < 1 / 2) (hp : p.Prime) :
    bohrEval (1 / 2) (toWiener _ (criticalWiener_localFactorKernel p ((p : ℝ) ^ (1 - ε)))).toFn
      (polePoint ε hε2.le) = 0 := by
  rw [bohrEval_poleFactor hp]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hω : (polePoint ε hε2.le).ω p = (p : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) * (p : ℂ) ^ (-((1 - ε : ℝ) : ℂ)) := by
    simp only [polePoint, halfPlanePoint, hp.ne_zero, if_false]
    rw [← cpow_add _ _ hpc]; congr 1; ring
  have hsq : (p : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hpc h.1
  have hb : (((p : ℝ) ^ (1 - ε) : ℝ) : ℂ) * (p : ℂ) ^ (-((1 - ε : ℝ) : ℂ)) = 1 := by
    rw [ofReal_cpow hp0.le, ofReal_natCast, ← cpow_add _ _ hpc]; simp
  rw [hω]
  field_simp
  linear_combination hb

/-! ### The theorems -/

variable (hε : 0 < ε) (hε2 : ε < 1 / 2)
include hε hε2

/-- Every repairing kernel of `ℓ_ε` vanishes at the pole point. -/
theorem bohrEval_polePoint_eq_zero_of_mem {k : WienerAlgebraAt (1 / 2)}
    (hk : k ∈ paidIdeal (logPower ε) (summable_abs_logPower_div hε)) :
    bohrEval (1 / 2) k.toFn (polePoint ε hε2.le) = 0 := by
  rw [mem_paidIdeal] at hk
  have hs : (1 / 2 : ℝ) ≤ (((1 - ε : ℝ)) : ℂ).re := by simp; linarith
  rw [polePoint, bohrEval_halfPlanePoint, lSeries_toFn_eq k hs,
    lSeries_eq_zero_of_repairs_logPower hε hε2 (criticalWiener_rePart k) hk.1,
    lSeries_eq_zero_of_repairs_logPower hε hε2 (criticalWiener_imPart k) hk.2, mul_zero, add_zero]

/-- **The hull of `ℓ_ε` is the pole point**, as for the smooth power. -/
theorem mem_obstructionHull_logPower_iff (ω : BohrPoint) :
    ω ∈ obstructionHull (logPower ε) (summable_abs_logPower_div hε) ↔
      ∀ q : ℕ, q.Prime → ω.ω q = (polePoint ε hε2.le).ω q := by
  constructor
  · intro hω q hq
    by_contra hne
    set H := toWiener _ (criticalWiener_localFactorKernel q ((q : ℝ) ^ (1 - ε)))
    have hmem : H * H ∈ paidIdeal (logPower ε) (summable_abs_logPower_div hε) := by
      rw [toWiener_mul, toWiener_mem_paidIdeal_iff]
      exact receiverBounded_poleFactor_sq hε hε2 hq
    have h := hω _ hmem
    rw [← WienerAlgebraAt.bohrCharacter_apply, _root_.map_mul,
      WienerAlgebraAt.bohrCharacter_apply, bohrEval_poleFactor hq, ← sq, sq_eq_zero_iff,
      sub_eq_zero] at h
    apply hne
    have h0 := bohrEval_poleFactor_polePoint (ε := ε) hε2 hq
    rw [bohrEval_poleFactor hq, sub_eq_zero] at h0
    have hb : (((q : ℝ) ^ (1 - ε) : ℝ) : ℂ) ≠ 0 :=
      ofReal_ne_zero.2 (Real.rpow_pos_of_pos (by exact_mod_cast hq.pos) _).ne'
    have hsq : (q : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; exact fun h' => hq.ne_zero (by exact_mod_cast h'.1)
    have := h.symm.trans h0
    field_simp at this
    exact mul_left_cancel₀ hb this
  · intro h k hk
    rw [bohrEval_congr k.toFn (BohrPoint.eq_of_primes h)]
    exact bohrEval_polePoint_eq_zero_of_mem hε hε2 hk

/-- `P(ℓ_ε) ⊆ P(d^{−ε})`. -/
theorem paidIdeal_logPower_le_smoothPower :
    paidIdeal (logPower ε) (summable_abs_logPower_div hε) ≤
      paidIdeal (dampedSignWeight unitSign ε) (summable_abs_smoothPower_div hε) := fun k hk =>
  (mem_paidIdeal_smoothPower_iff hε hε2 k).2 (bohrEval_polePoint_eq_zero_of_mem hε hε2 hk)

/-- The local factor `δ₁ − 2^{1−ε} δ₂` as an element of `𝒲_{1/2}`. -/
abbrev poleFactorTwo (ε : ℝ) : WienerAlgebraAt (1 / 2) :=
  toWiener _ (criticalWiener_localFactorKernel 2 ((2 : ℝ) ^ (1 - ε)))

omit hε in
theorem poleFactorTwo_mem_smoothPower (hε : 0 < ε) :
    poleFactorTwo ε ∈ paidIdeal (dampedSignWeight unitSign ε) (summable_abs_smoothPower_div hε) :=
  (mem_paidIdeal_smoothPower_iff hε hε2 _).2 (by
    simpa using bohrEval_poleFactor_polePoint (ε := ε) (p := 2) hε2 Nat.prime_two)

theorem poleFactorTwo_not_mem :
    poleFactorTwo ε ∉ paidIdeal (logPower ε) (summable_abs_logPower_div hε) := by
  rw [toWiener_mem_paidIdeal_iff]
  exact not_receiverBounded_poleFactor hε hε2 Nat.prime_two

theorem poleFactorTwo_sq_mem :
    poleFactorTwo ε * poleFactorTwo ε ∈ paidIdeal (logPower ε) (summable_abs_logPower_div hε) := by
  rw [toWiener_mul, toWiener_mem_paidIdeal_iff]
  exact receiverBounded_poleFactor_sq hε hε2 Nat.prime_two

/-- **Same hull, smaller ideal**: `P(ℓ_ε) ⊊ P(d^{−ε})`. -/
theorem paidIdeal_logPower_lt_smoothPower :
    paidIdeal (logPower ε) (summable_abs_logPower_div hε) <
      paidIdeal (dampedSignWeight unitSign ε) (summable_abs_smoothPower_div hε) :=
  lt_of_le_of_ne (paidIdeal_logPower_le_smoothPower hε hε2) fun h =>
    poleFactorTwo_not_mem hε hε2 (h ▸ poleFactorTwo_mem_smoothPower hε2 hε)

/-- **The repairing ideal is not radical.** -/
theorem not_isRadical_paidIdeal_logPower :
    ¬ (paidIdeal (logPower ε) (summable_abs_logPower_div hε)).IsRadical := by
  intro hrad
  exact poleFactorTwo_not_mem hε hε2 (hrad ⟨2, by rw [sq]; exact poleFactorTwo_sq_mem hε hε2⟩)

/-- **The index reads the order of the pole**: the quotient by `P(ℓ_ε)` has rank at least `2`. -/
theorem two_le_rank_quotient_paidIdeal_logPower :
    (2 : Cardinal) ≤ Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸
      paidIdeal (logPower ε) (summable_abs_logPower_div hε)) := by
  set P := paidIdeal (logPower ε) (summable_abs_logPower_div hε)
  set π := Ideal.Quotient.mkₐ ℂ P
  have hli : LinearIndependent ℂ ![π 1, π (poleFactorTwo ε)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [← map_smul, ← map_smul, ← map_add, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem] at hst
    have hval := bohrEval_polePoint_eq_zero_of_mem hε hε2 hst
    rw [← WienerAlgebraAt.bohrCharacter_apply, map_add, map_smul, map_smul, _root_.map_one,
      WienerAlgebraAt.bohrCharacter_apply,
      show bohrEval (1 / 2) (poleFactorTwo ε).toFn (polePoint ε hε2.le) = 0 by
        simpa using bohrEval_poleFactor_polePoint (ε := ε) (p := 2) hε2 Nat.prime_two,
      smul_eq_mul, smul_eq_mul, mul_one, mul_zero, add_zero] at hval
    subst hval
    refine ⟨rfl, ?_⟩
    by_contra ht
    rw [zero_smul, zero_add] at hst
    apply poleFactorTwo_not_mem hε hε2
    have := P.smul_mem t⁻¹ hst
    rwa [smul_smul, inv_mul_cancel₀ ht, one_smul] at this
  have := hli.cardinal_le_rank
  simpa using this

end

end GaloisForLFunctions.ArithmeticOrientationTheory
