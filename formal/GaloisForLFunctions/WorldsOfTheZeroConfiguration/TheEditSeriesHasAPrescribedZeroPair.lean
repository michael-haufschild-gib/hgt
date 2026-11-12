import GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimesRoundAnOscillatingDensity
import GaloisForLFunctions.HeckeLFunctions.HeckeLFunctionsContinuePastTheLineReOne
import GaloisForLFunctions.HTGeometry.RightHalfPlanePrimitive
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# The edit series has a prescribed factor

Let `ε` be the greedy edit of the primes against a target `m`, and `E(s) = Σ_p ε(p) p^{−s}`.

**Prescribed factor** (`exists_exp_geditSeries_eq`).  Suppose the discrepancy of the edit is
`O(n^c)`, `0 < c ≤ 1`, and on `Re s > 1` a function `L` without zeros has logarithmic derivative
`L′/L = −Σ m(k) k^{−s} − Φ₀` with `Φ₀` holomorphic on `Re s > c`.  Then on `Re s > 1`

`exp(E(s)) = C · L(s) · exp(K(s))`, `C ≠ 0`, `K` holomorphic on `Re s > c`.

**Proof.**  `E′(s) = −Σ ε(k) log k · k^{−s}`.  The coefficients `ε(k) log k − m(k)` have partial
sums `O(n^c)`, so their Dirichlet series `D` is holomorphic on `Re s > c`, and
`E′ = −Σ m(k) k^{−s} − D = L′/L + Φ₀ − D`.  For a primitive `K` of `Φ₀ − D` on the half-plane,
`exp(E − K)/L` has derivative zero on `Re s > 1`.

**A zero pair** (`exists_exp_editSeries_eq`).  For the target `m(k) = −2 Re k^{ρ−1}`,
`Σ m(k) k^{−s} = −ζ(s + 1 − ρ) − ζ(s + 1 − ρ̄)` and `ζ(w) = 1/(w − 1) + ζ_reg(w)`, so
`L(s) = (s − ρ)(s − ρ̄)`: `exp(E(s)) = C (s − ρ)(s − ρ̄) exp(K(s))`.
-/

open Complex Filter Topology Finset

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimeEdits

open GaloisForLFunctions.HeckeLFunctions GaloisForLFunctions.HTGeometry _root_.RHTower

/-! ## The regular part of `ζ` -/

/-- `ζ(w) − 1/(w − 1)`, as an entire function. -/
def zetaRegular (w : ℂ) : ℂ := dslope zetaResidueUnit 1 w

theorem differentiable_zetaRegular : Differentiable ℂ zetaRegular := by
  have h : Differentiable ℂ zetaResidueUnit :=
    fun s => (analyticAt_zetaResidueUnit s).differentiableAt
  exact differentiableOn_univ.mp
    ((Complex.differentiableOn_dslope (s := Set.univ) Filter.univ_mem).mpr h.differentiableOn)

theorem riemannZeta_eq_zetaRegular {w : ℂ} (hw : w ≠ 1) :
    riemannZeta w = (w - 1)⁻¹ + zetaRegular w := by
  have hu : zetaResidueUnit w = (w - 1) * riemannZeta w := by
    simp [zetaResidueUnit, Function.update_of_ne hw]
  have h1 : w - 1 ≠ 0 := sub_ne_zero.mpr hw
  rw [zetaRegular, dslope_of_ne _ hw, slope_def_field, zetaResidueUnit_one, hu, sub_div,
    mul_div_cancel_left₀ _ h1, one_div]
  ring

/-! ## The Dirichlet series of the target -/

/-- `Σ n^a n^{−s} = ζ(s − a)` for `Re(s − a) > 1`. -/
theorem lseriesHasSum_cpow {a s : ℂ} (hs : 1 < (s - a).re) :
    LSeriesHasSum (fun n : ℕ => (n : ℂ) ^ a) s (riemannZeta (s - a)) := by
  have h := ((Complex.summable_one_div_nat_cpow (p := s - a)).mpr hs).hasSum
  rw [← zeta_eq_tsum_one_div_nat_cpow hs] at h
  have hne : s - a ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at hs
    linarith
  have e : LSeries.term (fun n : ℕ => (n : ℂ) ^ a) s = fun n : ℕ => 1 / (n : ℂ) ^ (s - a) := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Complex.zero_cpow hne]
    · rw [LSeries.term_of_ne_zero hn, Complex.cpow_sub _ _ (Nat.cast_ne_zero.mpr hn), one_div_div]
  rw [LSeriesHasSum, e]
  exact h

theorem conj_natCast_cpow (k : ℕ) (w : ℂ) :
    (starRingEnd ℂ) ((k : ℂ) ^ w) = (k : ℂ) ^ (starRingEnd ℂ) w := by
  have h := Complex.conj_cpow (k : ℂ) ((starRingEnd ℂ) w)
    (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm)
  rw [Complex.conj_natCast, Complex.conj_conj] at h
  exact h.symm

/-- The target is minus the coefficient of `ζ(s + 1 − ρ) + ζ(s + 1 − ρ̄)`. -/
theorem target_eq (ρ : ℂ) (k : ℕ) :
    (target ρ k : ℂ) = -((k : ℂ) ^ (ρ - 1) + (k : ℂ) ^ ((starRingEnd ℂ) ρ - 1)) := by
  have h : (k : ℂ) ^ ((starRingEnd ℂ) ρ - 1) = (starRingEnd ℂ) ((k : ℂ) ^ (ρ - 1)) := by
    rw [conj_natCast_cpow]; simp
  rw [h, Complex.add_conj, target, Complex.ofReal_neg]

theorem lseriesHasSum_target {ρ s : ℂ} (hs : ρ.re < s.re) :
    LSeriesHasSum (fun k : ℕ => (target ρ k : ℂ)) s
      (-(riemannZeta (s - (ρ - 1)) + riemannZeta (s - ((starRingEnd ℂ) ρ - 1)))) := by
  have h1 : 1 < (s - (ρ - 1)).re := by simp; linarith
  have h2 : 1 < (s - ((starRingEnd ℂ) ρ - 1)).re := by simp; linarith
  have hfun : (fun k : ℕ => (target ρ k : ℂ)) =
      -((fun n : ℕ => (n : ℂ) ^ (ρ - 1)) + fun n : ℕ => (n : ℂ) ^ ((starRingEnd ℂ) ρ - 1)) := by
    funext k
    simp [target_eq]
  rw [hfun]
  exact ((lseriesHasSum_cpow h1).add (lseriesHasSum_cpow h2)).neg

/-! ## The correction series -/

/-- The coefficients `ε(k) log k − m(k)`; their partial sums are minus the discrepancy. -/
def corrCoeff (m : ℕ → ℝ) (k : ℕ) : ℂ := ((gedit m k * Real.log k - m k : ℝ) : ℂ)

theorem corrCoeff_zero {m : ℕ → ℝ} (hm0 : m 0 = 0) : corrCoeff m 0 = 0 := by
  simp [corrCoeff, hm0]

theorem sum_corrCoeff (m : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Icc 1 n, corrCoeff m k = ((-gdisc m n : ℝ) : ℂ) := by
  have hI : Ioc 0 n = Icc 1 n := by
    ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [gdisc_eq_sum, hI, ← Finset.sum_neg_distrib, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [corrCoeff]
  congr 1
  ring

theorem norm_sum_corrCoeff_le {m : ℕ → ℝ} {K₀ c : ℝ} (hK₀ : 0 ≤ K₀) (hc : 0 ≤ c)
    (hdisc : ∀ n : ℕ, 1 ≤ n → |gdisc m n| ≤ K₀ * (n : ℝ) ^ c) (x : ℝ) (hx : 1 ≤ x) :
    ‖∑ k ∈ Icc 1 ⌊x⌋₊, corrCoeff m k‖ ≤ K₀ * x ^ c := by
  have hn : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  rw [sum_corrCoeff, Complex.norm_real, Real.norm_eq_abs, abs_neg]
  refine (hdisc _ hn).trans (mul_le_mul_of_nonneg_left ?_ hK₀)
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) hc

/-! ## The prescribed factor -/

/-- **The edit series has a prescribed factor.**  If the discrepancy of the greedy edit of `m` is
`O(n^c)`, `0 < c ≤ 1`, and `L′/L = −Σ m(k) k^{−s} − Φ₀` on `Re s > 1` with `Φ₀` holomorphic on
`Re s > c`, then `exp(Σ_p ε(p) p^{−s}) = C · L(s) · exp(K(s))` on `Re s > 1`, with `K` holomorphic
on `Re s > c`. -/
theorem exists_exp_geditSeries_eq {m : ℕ → ℝ} {K₀ c : ℝ} (hm0 : m 0 = 0) (hK₀ : 0 ≤ K₀)
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hdisc : ∀ n : ℕ, 1 ≤ n → |gdisc m n| ≤ K₀ * (n : ℝ) ^ c)
    (hsumm : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun k => (m k : ℂ)) s)
    {L Φ₀ : ℂ → ℂ} (hΦ₀ : DifferentiableOn ℂ Φ₀ {s : ℂ | c < s.re})
    (hL : ∀ s : ℂ, 1 < s.re → L s ≠ 0 ∧ DifferentiableAt ℂ L s ∧
      logDeriv L s = -LSeries (fun k => (m k : ℂ)) s - Φ₀ s) :
    ∃ (C : ℂ) (K : ℂ → ℂ), C ≠ 0 ∧ DifferentiableOn ℂ K {s : ℂ | c < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        Complex.exp (LSeries (fun k => (gedit m k : ℂ)) s) = C * L s * Complex.exp (K s) := by
  set ε : ℕ → ℂ := fun k => (gedit m k : ℂ) with hε
  -- the correction series and its continuation
  have hc0 : corrCoeff m 0 = 0 := corrCoeff_zero hm0
  have hgrow : ∀ x : ℝ, 1 ≤ x → ‖∑ k ∈ Icc 1 ⌊x⌋₊, corrCoeff m k‖ ≤ K₀ * x ^ c :=
    norm_sum_corrCoeff_le hK₀ hc.le hdisc
  have hDdiff : DifferentiableOn ℂ (growthCont (corrCoeff m) c) {s : ℂ | c < s.re} :=
    differentiableOn_growthCont hc0 hc.le hgrow
  obtain ⟨Kf, -, hKf⟩ := (isExactOn_rightHalfPlane (hΦ₀.sub hDdiff)).with_val_at (2 : ℂ) 0
  -- the derivative of the edit series
  have hE : ∀ s : ℂ, 1 < s.re → HasDerivAt (LSeries ε)
      (-LSeries (fun k => (m k : ℂ)) s - growthCont (corrCoeff m) c s) s := by
    intro s hs
    have habs : LSeries.abscissaOfAbsConv ε < s.re := by
      have hle : LSeries.abscissaOfAbsConv ε ≤ 1 :=
        LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => by
          rw [hε, Complex.norm_intCast]
          exact abs_gedit_le_one m n⟩
      exact lt_of_le_of_lt hle (by exact_mod_cast hs)
    have hsumL : LSeriesSummable (LSeries.logMul ε) s := LSeriesSummable_logMul_of_lt_re habs
    have hfun : LSeries.logMul ε = corrCoeff m + fun k : ℕ => (m k : ℂ) := by
      funext k
      simp only [LSeries.logMul, Pi.add_apply, corrCoeff, hε]
      rw [← Complex.natCast_log]
      push_cast
      ring
    have hsumC : LSeriesSummable (corrCoeff m) s := by
      have hsub : corrCoeff m = LSeries.logMul ε - fun k : ℕ => (m k : ℂ) := by
        rw [hfun]; simp
      rw [hsub]
      exact hsumL.sub (hsumm s hs)
    have hD : growthCont (corrCoeff m) c s = LSeries (corrCoeff m) s :=
      growthCont_eq_LSeries hc0 hc.le hgrow (lt_of_le_of_lt hc1 hs) hsumC
    refine (LSeries_hasDerivAt habs).congr_deriv ?_
    rw [hfun, LSeries_add hsumC (hsumm s hs), ← hD]
    ring
  -- `exp(E − K)/L` is constant on `Re s > 1`
  set F : ℂ → ℂ := fun x => Complex.exp (LSeries ε x - Kf x) / L x with hF
  have hFd : ∀ s : ℂ, 1 < s.re → HasDerivAt F 0 s := by
    intro s hs
    obtain ⟨hL0, hLd, hLlog⟩ := hL s hs
    have h1 := ((hE s hs).sub (hKf s (lt_of_le_of_lt hc1 hs))).cexp
    have hderiv : deriv L s = (-LSeries (fun k => (m k : ℂ)) s - Φ₀ s) * L s := by
      rw [logDeriv_apply] at hLlog
      exact (div_eq_iff hL0).mp hLlog
    refine (h1.div hLd.hasDerivAt hL0).congr_deriv ?_
    rw [div_eq_zero_iff]
    left
    rw [hderiv]
    simp only [Pi.sub_apply]
    ring
  have hUo : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2U : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by
    show (1 : ℝ) < (2 : ℂ).re
    norm_num
  have hconst : ∀ s : ℂ, 1 < s.re → F s = F 2 := fun s hs =>
    hUo.is_const_of_deriv_eq_zero (convex_halfSpace_re_gt 1).isPreconnected
      (fun z hz => (hFd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hFd z hz).deriv) hs h2U
  refine ⟨F 2, Kf, div_ne_zero (Complex.exp_ne_zero _) (hL 2 h2U).1,
    fun z hz => (hKf z hz).differentiableAt.differentiableWithinAt, fun s hs => ?_⟩
  have h' : Complex.exp (LSeries ε s - Kf s) = F 2 * L s := by
    rw [← hconst s hs]
    exact (div_mul_cancel₀ _ (hL s hs).1).symm
  calc Complex.exp (LSeries ε s)
      = Complex.exp (LSeries ε s - Kf s) * Complex.exp (Kf s) := by
        rw [← Complex.exp_add]; ring_nf
    _ = F 2 * L s * Complex.exp (Kf s) := by rw [h']

/-! ## A zero pair -/

theorem target_zero {ρ : ℂ} (hρ1 : ρ.re < 1) : target ρ 0 = 0 := by
  have hne : ρ - 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at h'
    linarith
  simp [target, Complex.zero_cpow hne]

/-- The logarithmic derivative of `(s − ρ)(s − ρ̄)` against the target of the pair. -/
theorem logDeriv_pair_eq {ρ s : ℂ} (hρ1 : ρ.re < 1) (hs : 1 < s.re) :
    (s - ρ) * (s - (starRingEnd ℂ) ρ) ≠ 0 ∧
      DifferentiableAt ℂ (fun z : ℂ => (z - ρ) * (z - (starRingEnd ℂ) ρ)) s ∧
      logDeriv (fun z : ℂ => (z - ρ) * (z - (starRingEnd ℂ) ρ)) s =
        -LSeries (fun k => (target ρ k : ℂ)) s -
          (zetaRegular (s - (ρ - 1)) + zetaRegular (s - ((starRingEnd ℂ) ρ - 1))) := by
  set ρc : ℂ := (starRingEnd ℂ) ρ with hρc
  have hρcre : ρc.re = ρ.re := by rw [hρc, Complex.conj_re]
  have h1 : s - ρ ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    rw [Complex.sub_re, Complex.zero_re] at h'
    linarith
  have h2 : s - ρc ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    rw [Complex.sub_re, Complex.zero_re, hρcre] at h'
    linarith
  have hd : HasDerivAt (fun z : ℂ => (z - ρ) * (z - ρc)) (1 * (s - ρc) + (s - ρ) * 1) s :=
    ((hasDerivAt_id s).sub_const ρ).mul ((hasDerivAt_id s).sub_const ρc)
  have hT := lseriesHasSum_target (ρ := ρ) (s := s) (by linarith)
  have hz1 : s - (ρ - 1) ≠ 1 := fun h => h1 (by linear_combination h)
  have hz2 : s - (ρc - 1) ≠ 1 := fun h => h2 (by linear_combination h)
  refine ⟨mul_ne_zero h1 h2, hd.differentiableAt, ?_⟩
  rw [logDeriv_apply, hd.deriv, hT.LSeries_eq, riemannZeta_eq_zetaRegular hz1,
    riemannZeta_eq_zetaRegular hz2,
    show s - (ρ - 1) - 1 = s - ρ by ring, show s - (ρc - 1) - 1 = s - ρc by ring]
  field_simp
  ring

/-- **The edit series has the zero pair `ρ, ρ̄` and no other zero.**  If the discrepancy of the
edit is `O(n^c)`, `0 < c ≤ 1`, then `exp(Σ_p ε(p) p^{−s}) = C (s − ρ)(s − ρ̄) exp(K(s))` on
`Re s > 1`, with `K` holomorphic on `Re s > c`. -/
theorem exists_exp_editSeries_eq_of_disc {ρ : ℂ} {K₀ c : ℝ} (hρ1 : ρ.re < 1)
    (hK₀ : 0 ≤ K₀) (hc : 0 < c) (hc1 : c ≤ 1)
    (hdisc : ∀ n : ℕ, 1 ≤ n → |editDisc ρ n| ≤ K₀ * (n : ℝ) ^ c) :
    ∃ (C : ℂ) (K : ℂ → ℂ), C ≠ 0 ∧ DifferentiableOn ℂ K {s : ℂ | c < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        Complex.exp (LSeries (fun k => (edit ρ k : ℂ)) s) =
          C * (s - ρ) * (s - (starRingEnd ℂ) ρ) * Complex.exp (K s) := by
  have hΦ₀ : DifferentiableOn ℂ (fun s : ℂ => zetaRegular (s - (ρ - 1)) +
      zetaRegular (s - ((starRingEnd ℂ) ρ - 1))) {s : ℂ | c < s.re} :=
    ((differentiable_zetaRegular.comp (differentiable_id.sub_const _)).add
      (differentiable_zetaRegular.comp (differentiable_id.sub_const _))).differentiableOn
  obtain ⟨C, K, hC, hK, h⟩ := exists_exp_geditSeries_eq (m := target ρ) (target_zero hρ1) hK₀ hc
    hc1 hdisc (fun s hs => (lseriesHasSum_target (ρ := ρ) (s := s) (by linarith)).LSeriesSummable)
    (L := fun z : ℂ => (z - ρ) * (z - (starRingEnd ℂ) ρ)) hΦ₀
    (fun s hs => logDeriv_pair_eq hρ1 hs)
  refine ⟨C, K, hC, hK, fun s hs => ?_⟩
  rw [h s hs]
  ring

/-- **The factorization from the prime window bound.**  If the primes satisfy
`θ(y + L) − θ(y) ≥ (L − (y + L)^α)/2` for `y ≥ X`, the edit series at `ρ` satisfies
`exp(Σ_p ε(p) p^{−s}) = C (s − ρ)(s − ρ̄) exp(K(s))` with `K` holomorphic on `Re s > c`, for every
`0 < c ≤ 1` with `c ≥ α − (1 − Re ρ)`. -/
theorem exists_exp_editSeries_eq {ρ : ℂ} {α X c : ℝ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hα1 : α < 1) (hc : 0 < c) (hc1 : c ≤ 1) (hαc : α - (1 - ρ.re) ≤ c)
    (hwin : ∀ y L : ℝ, X ≤ y → 0 ≤ L →
      (L - (y + L) ^ α) / 2 ≤ Chebyshev.theta (y + L) - Chebyshev.theta y) :
    ∃ (C : ℂ) (K : ℂ → ℂ), C ≠ 0 ∧ DifferentiableOn ℂ K {s : ℂ | c < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        Complex.exp (LSeries (fun k => (edit ρ k : ℂ)) s) =
          C * (s - ρ) * (s - (starRingEnd ℂ) ρ) * Complex.exp (K s) := by
  obtain ⟨K₀, hK₀, hdisc⟩ := exists_abs_editDisc_le_rpow hρ0 hρ1 hα1 hc hαc hwin
  exact exists_exp_editSeries_eq_of_disc hρ1 hK₀ hc hc1 hdisc

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimeEdits
