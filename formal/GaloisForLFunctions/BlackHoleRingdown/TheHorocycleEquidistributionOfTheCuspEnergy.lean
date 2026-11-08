import GaloisForLFunctions.BlackHoleRingdown.TheMeanSquareLawOfTheCuspModes
import GaloisForLFunctions.BlackHoleRingdown.TheVerticalBoundsOfTheEisensteinTail
import GaloisForLFunctions.RHTower.KontorovichLebedevTransform
import GaloisForLFunctions.RHTower.EisensteinCuspTailImaginaryOrderBound
import GaloisForLFunctions.RHTower.MaassWhittakerUniqueness

/-!
# Long horocycles equidistribute the energy of a cusp mode

For a cusp form `g` of the modular horizon the mean of its energy density along the closed horocycle of
height `y` converges to the spatial mean as `y → 0`:

  `∫_{-1/2}^{1/2} |g(x + iy)|² dx → (3/π) ∫_𝒟 |g|² dμ = ‖g‖²/vol(𝒟)`   (`tendsto_slice`).

**Proof.** Parseval on the horocycle and pairing `±k` give `m(y) = Σ_k f(k) · y k(ky)` with
`f(k) = |ρ(k)|² + |ρ(-k)|²` and `k(u) = K_ν(2πu)²`. Abel summation against `S(t) = Σ_{k ≤ t} f(k)` and the
substitution `u = ty` turn this into `m(y) = -∫_0^∞ k'(u) · y S(u/y) du`. The mean-square law
(`CuspMS.tendsto_mean_square`) gives `y S(u/y) → A u`, and `|y S(u/y)| ≤ C u`; since
`|K_ν(x)| ≤ M(x^{-1/4} + 1)e^{-x}` (from the logarithmic and exponential bounds of `K_{iτ}`) and
`|K_ν'(x)| ≤ 2/x` (`K_{ν±1}` is bounded by `∫ e^t e^{-x e^t/2} dt = (2/x)e^{-x/2}`), `u k'(u)` is dominated by an
integrable function and dominated convergence gives `m(y) → -A ∫ u k'(u) du = A ∫ k`. Finally
`∫_0^∞ K_ν(2πu)² du = (2π)^{-1} G(1) = π/(8 cosh πt)` by the two-`K` Mellin formula, and
`A = (24/π²) cosh(πt) ‖g‖²`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.DeckPointPair

namespace CuspHE

open HeckeCusp CuspL CuspMS
open GaloisForLFunctions.RHTower.MaassWhittaker (besK besKd hasDerivAt_besK hasDerivAt_besKd
  hasDerivAt_besK_comp)

variable {lamE : ℝ} {g : UpperHalfPlane → ℂ} {ρ : ℤ → ℂ}

/-! ### Bessel bounds on the imaginary-order line -/

theorem nu_eq (lamE : ℝ) : nu lamE = ((Real.sqrt (lamE - 1 / 4) : ℝ) : ℂ) * I := rfl

/-- `|K_ν(x)| ≤ M (x^{-1/4} + 1) e^{-x}` for `x > 0`. -/
theorem exists_norm_K_le (lamE : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 0 < x →
    ‖modifiedBesselKOrder x (nu lamE)‖ ≤ M * (x ^ (-(1 / 4 : ℝ)) + 1) * Real.exp (-x) := by
  have hL : 0 ≤ Real.log (2 + |Real.sqrt (lamE - 1 / 4)|) :=
    Real.log_nonneg (by linarith [abs_nonneg (Real.sqrt (lamE - 1 / 4))])
  refine ⟨Real.exp 3 * (Real.log (2 + |Real.sqrt (lamE - 1 / 4)|) + 7) + Real.exp 1, by positivity,
    fun x hx => ?_⟩
  rw [nu_eq]
  have hp : 0 ≤ x ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hx.le _
  rcases le_or_gt 1 x with h1 | h1
  · have h := _root_.RHTower.norm_modifiedBesselKOrder_I_mul_le_exp h1 (Real.sqrt (lamE - 1 / 4))
    have h3 : Real.exp 1 ≤ (Real.exp 3 * (Real.log (2 + |Real.sqrt (lamE - 1 / 4)|) + 7) + Real.exp 1) *
        (x ^ (-(1 / 4 : ℝ)) + 1) := by
      have : 0 ≤ Real.exp 3 * (Real.log (2 + |Real.sqrt (lamE - 1 / 4)|) + 7) := by positivity
      nlinarith [Real.exp_pos 1]
    exact h.trans (mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le)
  · have h := GaloisForLFunctions.RHTower.KontorovichLebedev.norm_modifiedBesselKOrder_I_mul_le_log hx
      (Real.sqrt (lamE - 1 / 4))
    have hlog : |Real.log x| ≤ 4 * x ^ (-(1 / 4 : ℝ)) := by
      rw [abs_of_neg (Real.log_neg hx h1), ← Real.log_inv]
      have := Real.log_le_rpow_div (inv_nonneg.2 hx.le) (by norm_num : (0 : ℝ) < 1 / 4)
      rw [Real.inv_rpow hx.le, ← Real.rpow_neg hx.le] at this
      linarith
    have he : Real.exp (-(Real.pi * |Real.sqrt (lamE - 1 / 4)|) / 2) ≤ 1 :=
      Real.exp_le_one_iff.2 (by have := abs_nonneg (Real.sqrt (lamE - 1 / 4)); have := Real.pi_pos; nlinarith)
    have hex : Real.exp (-1) ≤ Real.exp (-x) := Real.exp_le_exp.2 (by linarith)
    have he3 : Real.exp 2 = Real.exp 3 * Real.exp (-1) := by rw [← Real.exp_add]; norm_num
    have hLp := mul_nonneg hL hp
    calc ‖_‖ ≤ Real.exp 2 * (|Real.log x| + Real.log (2 + |Real.sqrt (lamE - 1 / 4)|) + 3) *
          Real.exp (-(Real.pi * |Real.sqrt (lamE - 1 / 4)|) / 2) := h
      _ ≤ Real.exp 2 * (|Real.log x| + Real.log (2 + |Real.sqrt (lamE - 1 / 4)|) + 3) * 1 :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ Real.exp 2 * ((Real.log (2 + |Real.sqrt (lamE - 1 / 4)|) + 7) * (x ^ (-(1 / 4 : ℝ)) + 1)) := by
          rw [mul_one]; refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          nlinarith
      _ = Real.exp 3 * (Real.log (2 + |Real.sqrt (lamE - 1 / 4)|) + 7) * (x ^ (-(1 / 4 : ℝ)) + 1) *
          Real.exp (-1) := by rw [he3]; ring
      _ ≤ (Real.exp 3 * (Real.log (2 + |Real.sqrt (lamE - 1 / 4)|) + 7) + Real.exp 1) *
          (x ^ (-(1 / 4 : ℝ)) + 1) * Real.exp (-x) := by
          refine mul_le_mul ?_ hex (Real.exp_pos _).le (by positivity)
          have : 0 ≤ Real.exp 1 * (x ^ (-(1 / 4 : ℝ)) + 1) := by positivity
          nlinarith

/-- `|K_μ(s)| ≤ 2/s` for `|Re μ| ≤ 1`: the kernel is at most `e^t e^{-s e^t/2}`. -/
theorem norm_K_le_two_div {μ : ℂ} (hμ : |μ.re| ≤ 1) {s : ℝ} (hs : 0 < s) :
    ‖modifiedBesselKOrder s μ‖ ≤ 2 / s := by
  have hG : ∀ t, HasDerivAt (fun t => -(2 / s) * Real.exp (-(s / 2 * Real.exp t)))
      (Real.exp t * Real.exp (-(s / 2 * Real.exp t))) t := fun t => by
    have h1 := ((Real.hasDerivAt_exp t).const_mul (s / 2)).neg
    refine ((h1.exp).const_mul (-(2 / s))).congr_deriv ?_
    have hss : 2 / s * (s / 2) = 1 := by
      rw [div_mul_div_comm, mul_comm 2 s, div_self (by positivity)]
    calc -(2 / s) * (Real.exp (-(s / 2 * Real.exp t)) * -(s / 2 * Real.exp t))
        = (2 / s * (s / 2)) * (Real.exp t * Real.exp (-(s / 2 * Real.exp t))) := by ring
      _ = _ := by rw [hss, one_mul]
  have hG'0 : ∀ t, 0 ≤ Real.exp t * Real.exp (-(s / 2 * Real.exp t)) := fun t => by positivity
  have hlim : Tendsto (fun t => -(2 / s) * Real.exp (-(s / 2 * Real.exp t))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t => s / 2 * Real.exp t) atTop atTop :=
      Real.tendsto_exp_atTop.const_mul_atTop (by positivity)
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul (-(2 / s))
    simpa using this
  have hint : IntegrableOn (fun t => Real.exp t * Real.exp (-(s / 2 * Real.exp t))) (Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun t _ => hG t) (fun t _ => hG'0 t) hlim
  have hval : ∫ t in Ioi (0 : ℝ), Real.exp t * Real.exp (-(s / 2 * Real.exp t)) =
      2 / s * Real.exp (-(s / 2)) := by
    rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun t _ => hG t) (fun t _ => hG'0 t) hlim]
    simp only [Real.exp_zero, mul_one]
    ring
  have hbound : ‖modifiedBesselKOrder s μ‖ ≤
      ∫ t in Ioi (0 : ℝ), Real.exp t * Real.exp (-(s / 2 * Real.exp t)) := by
    refine norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun t ht => ?_))
    have ht0 : (0 : ℝ) < t := ht
    refine (norm_besselOrderKernel_le_re s μ t).trans ?_
    have hc1 : Real.cosh (μ.re * t) ≤ Real.cosh t := Real.cosh_le_cosh.2 (by
      rw [abs_mul]; nlinarith [abs_nonneg t, abs_nonneg μ.re])
    have hc2 : Real.cosh t ≤ Real.exp t := by
      rw [Real.cosh_eq]; linarith [Real.exp_le_exp.2 (by linarith : -t ≤ t)]
    have hc3 : Real.exp t / 2 ≤ Real.cosh t := by
      rw [Real.cosh_eq]; linarith [Real.exp_pos (-t)]
    have he : Real.exp (-s * Real.cosh t) ≤ Real.exp (-(s / 2 * Real.exp t)) :=
      Real.exp_le_exp.2 (by nlinarith)
    calc Real.exp (-s * Real.cosh t) * Real.cosh (μ.re * t) ≤
          Real.exp (-(s / 2 * Real.exp t)) * Real.exp t :=
          mul_le_mul he (hc1.trans hc2) (Real.cosh_pos _).le (Real.exp_pos _).le
      _ = Real.exp t * Real.exp (-(s / 2 * Real.exp t)) := by ring
  calc _ ≤ 2 / s * Real.exp (-(s / 2)) := hbound.trans hval.le
    _ ≤ 2 / s * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (by linarith)) (by positivity)
    _ = 2 / s := mul_one _

theorem norm_besKd_le (lamE : ℝ) {s : ℝ} (hs : 0 < s) : ‖besKd (nu lamE) s‖ ≤ 2 / s := by
  have h1 := norm_K_le_two_div (μ := nu lamE + 1) (by simp [nu_re]) hs
  have h2 := norm_K_le_two_div (μ := nu lamE - 1) (by simp [nu_re]) hs
  unfold besKd
  rw [norm_mul, show ‖-(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  calc 1 / 2 * ‖besK (nu lamE + 1) s + besK (nu lamE - 1) s‖ ≤ 1 / 2 * (2 / s + 2 / s) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h1 h2)) (by norm_num)
    _ = 2 / s := by ring

/-! ### The horocyclic profile `K_ν(2πu)²` -/

/-- `k(u) = K_ν(2πu)²`. -/
def kk (lamE : ℝ) (u : ℝ) : ℂ :=
  modifiedBesselKOrder (2 * Real.pi * u) (nu lamE) * modifiedBesselKOrder (2 * Real.pi * u) (nu lamE)

/-- `k'(u) = 4π K_ν(2πu) K_ν'(2πu)`. -/
def kkd (lamE : ℝ) (u : ℝ) : ℂ :=
  2 * ((2 * Real.pi : ℝ) : ℂ) *
    (modifiedBesselKOrder (2 * Real.pi * u) (nu lamE) * besKd (nu lamE) (2 * Real.pi * u))

theorem hasDerivAt_kk {u : ℝ} (hu : 0 < u) : HasDerivAt (kk lamE) (kkd lamE u) u := by
  have h := hasDerivAt_besK_comp (k := 2 * Real.pi) (by positivity) (nu lamE) hu
  exact (h.mul h).congr_deriv (by unfold kkd; ring)

theorem continuousOn_kk : ContinuousOn (kk lamE) (Ioi 0) := fun _ hu =>
  (hasDerivAt_kk hu).continuousAt.continuousWithinAt

theorem continuousOn_kkd : ContinuousOn (kkd lamE) (Ioi 0) := by
  intro u hu
  have hu0 : (0 : ℝ) < u := hu
  have hx : 0 < 2 * Real.pi * u := by positivity
  have h1 : ContinuousAt (fun u => modifiedBesselKOrder (2 * Real.pi * u) (nu lamE)) u :=
    (hasDerivAt_besK_comp (k := 2 * Real.pi) (by positivity) (nu lamE) hu0).continuousAt
  have h2 : ContinuousAt (fun u : ℝ => besKd (nu lamE) (2 * Real.pi * u)) u :=
    ContinuousAt.comp (g := besKd (nu lamE)) (hasDerivAt_besKd (nu lamE) hx).continuousAt
      (by fun_prop : ContinuousAt (fun u : ℝ => 2 * Real.pi * u) u)
  exact (continuousAt_const.mul (h1.mul h2)).continuousWithinAt

theorem norm_kkd_le {u : ℝ} (hu : 0 < u) :
    ‖kkd lamE u‖ ≤ 4 * ‖modifiedBesselKOrder (2 * Real.pi * u) (nu lamE)‖ / u := by
  have hx : 0 < 2 * Real.pi * u := by positivity
  have hd := norm_besKd_le lamE hx
  have hpi := Real.pi_pos
  unfold kkd
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    show ‖(2 : ℂ)‖ = 2 by norm_num]
  calc 2 * (2 * Real.pi) * (‖modifiedBesselKOrder (2 * Real.pi * u) (nu lamE)‖ *
        ‖besKd (nu lamE) (2 * Real.pi * u)‖)
      ≤ 2 * (2 * Real.pi) * (‖modifiedBesselKOrder (2 * Real.pi * u) (nu lamE)‖ *
          (2 / (2 * Real.pi * u))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd (norm_nonneg _)) (by positivity)
    _ = 4 * ‖modifiedBesselKOrder (2 * Real.pi * u) (nu lamE)‖ / u := by
        field_simp; ring

/-- `|k(u)| ≤ 2M² ((2πu)^{-1/2} + 1) e^{-4πu}`. -/
theorem norm_kk_le {M : ℝ}
    (hM : ∀ x : ℝ, 0 < x → ‖modifiedBesselKOrder x (nu lamE)‖ ≤ M * (x ^ (-(1 / 4 : ℝ)) + 1) * Real.exp (-x))
    {u : ℝ} (hu : 0 < u) :
    ‖kk lamE u‖ ≤ 2 * M ^ 2 * ((2 * Real.pi * u) ^ (-(1 / 2 : ℝ)) + 1) * Real.exp (-(4 * Real.pi * u)) := by
  have hx : 0 < 2 * Real.pi * u := by positivity
  have hK := hM (2 * Real.pi * u) hx
  have hp : 0 ≤ (2 * Real.pi * u) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hx.le _
  have hp2 : ((2 * Real.pi * u) ^ (-(1 / 4 : ℝ))) ^ 2 = (2 * Real.pi * u) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have he : Real.exp (-(2 * Real.pi * u)) ^ 2 = Real.exp (-(4 * Real.pi * u)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  unfold kk
  rw [norm_mul, ← sq]
  calc ‖modifiedBesselKOrder (2 * Real.pi * u) (nu lamE)‖ ^ 2
      ≤ (M * ((2 * Real.pi * u) ^ (-(1 / 4 : ℝ)) + 1) * Real.exp (-(2 * Real.pi * u))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hK 2
    _ = M ^ 2 * ((2 * Real.pi * u) ^ (-(1 / 4 : ℝ)) + 1) ^ 2 * Real.exp (-(2 * Real.pi * u)) ^ 2 := by
        ring
    _ ≤ M ^ 2 * (2 * (((2 * Real.pi * u) ^ (-(1 / 4 : ℝ))) ^ 2 + 1)) *
          Real.exp (-(2 * Real.pi * u)) ^ 2 := by
        gcongr; nlinarith [sq_nonneg ((2 * Real.pi * u) ^ (-(1 / 4 : ℝ)) - 1)]
    _ = 2 * M ^ 2 * ((2 * Real.pi * u) ^ (-(1 / 2 : ℝ)) + 1) * Real.exp (-(4 * Real.pi * u)) := by
        rw [hp2, he]; ring

theorem integrableOn_rpow_exp {a b c : ℝ} (ha : -1 < a) (hb : 0 < b) (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => ((c * u) ^ a + 1) * Real.exp (-(b * u))) (Ioi 0) := by
  have h1 : IntegrableOn (fun u : ℝ => u ^ a * Real.exp (-b * u ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow ha le_rfl hb
  have h2 : IntegrableOn (fun u : ℝ => Real.exp (-b * u)) (Ioi 0) := exp_neg_integrableOn_Ioi 0 hb
  have h3 : IntegrableOn (fun u : ℝ => c ^ a * (u ^ a * Real.exp (-b * u ^ (1 : ℝ))) +
      Real.exp (-b * u)) (Ioi 0) := (h1.const_mul (c ^ a)).add h2
  refine h3.congr_fun (fun u (hu : 0 < u) => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  rw [Real.mul_rpow hc.le hu.le, show -b * u = -(b * u) by ring]
  ring

/-! ### Partial sums of the Rankin–Selberg coefficients -/

/-- `S(t) = Σ_{0 ≤ k ≤ t} (|ρ(k)|² + |ρ(-k)|²)`. -/
def partialRS (ρ : ℤ → ℂ) (t : ℝ) : ℝ := ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, rsCoeff ρ k

theorem partialRS_nonneg (t : ℝ) : 0 ≤ partialRS ρ t :=
  Finset.sum_nonneg fun k _ => by unfold rsCoeff; positivity

theorem partialRS_of_lt_one (hρ0 : ρ 0 = 0) {t : ℝ} (ht : t < 1) : partialRS ρ t = 0 := by
  unfold partialRS
  rw [Nat.floor_eq_zero.2 ht, Finset.Icc_self, Finset.sum_singleton]
  simp [rsCoeff, hρ0]

theorem measurable_partialRS : Measurable (partialRS ρ) :=
  (measurable_from_nat (f := fun n => ∑ k ∈ Finset.Icc 0 n, rsCoeff ρ k)).comp Nat.measurable_floor

theorem Icc_eq_range (n : ℕ) : Finset.Icc 0 n = Finset.range (n + 1) := by
  ext k; simp

theorem tendsto_partialRS_div (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) :
    Tendsto (fun x : ℝ => partialRS ρ x / x) atTop (𝓝 (msConst lamE g)) := by
  have hm : Tendsto (fun N : ℕ => (∑ m ∈ Finset.range N, rsCoeff ρ m) / N) atTop
      (𝓝 (msConst lamE g)) := tendsto_mean_square hg hρ0 hρ
  have hN : Tendsto (fun x : ℝ => ⌊x⌋₊ + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp (tendsto_nat_floor_atTop (α := ℝ))
  have h2 : Tendsto (fun x : ℝ => ((⌊x⌋₊ + 1 : ℕ) : ℝ) / x) atTop (𝓝 1) := by
    have hu : Tendsto (fun x : ℝ => 1 + x⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_inv_atTop_zero (𝕜 := ℝ))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℝ => (1 : ℝ))
      (h := fun x : ℝ => 1 + x⁻¹) tendsto_const_nhds hu ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx
      rw [le_div_iff₀ hx]; push_cast; linarith [Nat.lt_floor_add_one x]
    · filter_upwards [eventually_gt_atTop 0] with x hx
      rw [div_le_iff₀ hx]; push_cast
      have := Nat.floor_le hx.le
      rw [add_mul, one_mul, inv_mul_cancel₀ hx.ne']; linarith
  have h3 := (hm.comp hN).mul h2
  rw [mul_one] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hN0 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [Function.comp_apply, partialRS, Icc_eq_range]
  field_simp

theorem exists_partialRS_le (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → partialRS ρ t ≤ C * t := by
  have hm : Tendsto (fun N : ℕ => (∑ m ∈ Finset.range N, rsCoeff ρ m) / N) atTop
      (𝓝 (msConst lamE g)) := tendsto_mean_square hg hρ0 hρ
  obtain ⟨B, hB⟩ := hm.bddAbove_range
  refine ⟨2 * max B 0, by positivity, fun t ht => ?_⟩
  rcases lt_or_ge t 1 with h1 | h1
  · rw [partialRS_of_lt_one hρ0 h1]; exact mul_nonneg (by positivity) ht
  · have hB' : (∑ m ∈ Finset.range (⌊t⌋₊ + 1), rsCoeff ρ m) / ((⌊t⌋₊ + 1 : ℕ) : ℝ) ≤ B :=
      hB ⟨⌊t⌋₊ + 1, rfl⟩
    have hN : (0 : ℝ) < ((⌊t⌋₊ + 1 : ℕ) : ℝ) := by positivity
    rw [div_le_iff₀ hN] at hB'
    have hfl : ((⌊t⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * t := by push_cast; linarith [Nat.floor_le ht]
    unfold partialRS; rw [Icc_eq_range]
    calc _ ≤ B * ((⌊t⌋₊ + 1 : ℕ) : ℝ) := hB'
      _ ≤ max B 0 * ((⌊t⌋₊ + 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_right (le_max_left _ _) hN.le
      _ ≤ max B 0 * (2 * t) := mul_le_mul_of_nonneg_left hfl (le_max_right _ _)
      _ = 2 * max B 0 * t := by ring

/-! ### Abel summation of the horocycle mass -/

/-- **Parseval on the horocycle**: `m(y) = Σ_k f(k) · y K_ν(2πky)²`. -/
theorem hasSum_slice_nat (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {y : ℝ} (hy : 0 < y) :
    HasSum (fun k : ℕ => (y : ℂ) * kk lamE (k * y) * ((rsCoeff ρ k : ℝ) : ℂ))
      (WeylUpper.slice g y : ℂ) := by
  have hterm : ∀ n : ℤ, ((‖fourierCoeff g n y‖ ^ 2 : ℝ) : ℂ) = ((‖ρ n‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) *
      (modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE) *
        modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) := by
    intro n
    rw [hρ n y hy, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, mul_pow, Real.sq_sqrt hy.le]
    rw [← CuspRSI.K_real lamE (2 * Real.pi * |(n : ℝ)| * y), Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
    push_cast; ring
  have h := (Complex.hasSum_ofReal.2 (WeylUpper.hasSum_slice hg hy)).nat_add_neg
  have h0 : ((‖fourierCoeff g 0 y‖ ^ 2 : ℝ) : ℂ) = 0 := by rw [hρ 0 y hy, hρ0]; simp
  rw [h0, add_zero] at h
  refine h.congr_fun fun k => ?_
  rw [hterm, hterm]
  have e1 : |(((k : ℤ)) : ℝ)| = (k : ℝ) := by simp
  have e2 : |((-(k : ℤ) : ℤ) : ℝ)| = (k : ℝ) := by simp
  rw [e1, e2]
  unfold kk rsCoeff
  rw [show 2 * Real.pi * (k : ℝ) * y = 2 * Real.pi * ((k : ℝ) * y) by ring]
  push_cast; ring

theorem hasDerivAt_phi {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    HasDerivAt (fun t => (y : ℂ) * kk lamE (t * y)) ((y : ℂ) * (kkd lamE (t * y) * y)) t := by
  have h := (hasDerivAt_kk (lamE := lamE) (mul_pos ht hy)).scomp t (hasDerivAt_mul_const y)
  exact (h.const_mul (y : ℂ)).congr_deriv (by rw [Complex.real_smul]; ring)

/-- **Abel summation up to `N`.** -/
theorem abel_N (hρ0 : ρ 0 = 0) {y : ℝ} (hy : 0 < y) (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Ioc 0 N, (y : ℂ) * kk lamE (k * y) * ((rsCoeff ρ k : ℝ) : ℂ) =
      (y : ℂ) * kk lamE (N * y) * ((partialRS ρ N : ℝ) : ℂ) -
        ∫ t in Ioc (1 / 2 : ℝ) N, (y : ℂ) * (kkd lamE (t * y) * y) * ((partialRS ρ t : ℝ) : ℂ) := by
  have hderiv : ∀ t : ℝ, 0 < t → deriv (fun t => (y : ℂ) * kk lamE (t * y)) t =
      (y : ℂ) * (kkd lamE (t * y) * y) := fun t ht => (hasDerivAt_phi hy ht).deriv
  have hN' : (1 / 2 : ℝ) ≤ N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hS : ∀ t : ℝ, ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ((rsCoeff ρ k : ℝ) : ℂ) = ((partialRS ρ t : ℝ) : ℂ) :=
    fun t => by rw [partialRS, Complex.ofReal_sum]
  have hint : IntegrableOn (deriv fun t => (y : ℂ) * kk lamE (t * y)) (Icc (1 / 2 : ℝ) N) := by
    have hc : ContinuousOn (fun t : ℝ => (y : ℂ) * (kkd lamE (t * y) * y)) (Icc (1 / 2 : ℝ) N) := by
      refine continuousOn_const.mul (ContinuousOn.mul ?_ continuousOn_const)
      exact continuousOn_kkd.comp (by fun_prop : Continuous fun t : ℝ => t * y).continuousOn
        fun t ht => (mul_pos (by linarith [ht.1]) hy : (0 : ℝ) < t * y)
    exact (hc.congr fun t ht => hderiv t (by linarith [ht.1])).integrableOn_Icc
  have hab := sum_mul_eq_sub_sub_integral_mul (fun k => ((rsCoeff ρ k : ℝ) : ℂ))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hN'
    (fun t ht => (hasDerivAt_phi (lamE := lamE) hy (by linarith [ht.1] : (0 : ℝ) < t)).differentiableAt)
    hint
  simp only [hS] at hab
  rw [Nat.floor_eq_zero.2 (by norm_num : (1 / 2 : ℝ) < 1), Nat.floor_natCast] at hab
  refine hab.trans ?_
  rw [partialRS_of_lt_one hρ0 (by norm_num : (1 / 2 : ℝ) < 1), ofReal_zero, mul_zero, sub_zero]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  rw [hderiv t (by linarith [ht.1])]

/-- **The horocycle mass as an integral**: `m(y) = -∫_{1/2}^∞ y² k'(ty) S(t) dt`. -/
theorem slice_eq_integral (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {y : ℝ} (hy : 0 < y) :
    (WeylUpper.slice g y : ℂ) =
      -∫ t in Ioi (1 / 2 : ℝ), (y : ℂ) * (kkd lamE (t * y) * y) * ((partialRS ρ t : ℝ) : ℂ) := by
  obtain ⟨C, hC0, hC⟩ := exists_partialRS_le hg hρ0 hρ
  obtain ⟨M, hM0, hM⟩ := exists_norm_K_le lamE
  set F : ℝ → ℂ := fun t => (y : ℂ) * (kkd lamE (t * y) * y) * ((partialRS ρ t : ℝ) : ℂ)
  have hFint : IntegrableOn F (Ioi (1 / 2 : ℝ)) := by
    have hb : 0 < 2 * Real.pi * y := by positivity
    refine Integrable.mono' ((exp_neg_integrableOn_Ioi (1 / 2) hb).const_mul
      (4 * C * y * (M * ((Real.pi * y) ^ (-(1 / 4 : ℝ)) + 1)))) ?_ ?_
    · have hc : ContinuousOn (fun t : ℝ => (y : ℂ) * (kkd lamE (t * y) * y)) (Ioi (1 / 2 : ℝ)) := by
        refine continuousOn_const.mul (ContinuousOn.mul ?_ continuousOn_const)
        exact continuousOn_kkd.comp (by fun_prop : Continuous fun t : ℝ => t * y).continuousOn
          fun t (ht : 1 / 2 < t) => (mul_pos (by linarith) hy : (0 : ℝ) < t * y)
      exact (hc.aestronglyMeasurable measurableSet_Ioi).mul
        (Complex.measurable_ofReal.comp measurable_partialRS).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 1 / 2 < t) => ?_)
      have ht0 : 0 < t := by linarith
      have hty : 0 < t * y := mul_pos ht0 hy
      have hkd := norm_kkd_le (lamE := lamE) hty
      have hK := hM (2 * Real.pi * (t * y)) (by positivity)
      have hS := hC t ht0.le
      have hp : (2 * Real.pi * (t * y)) ^ (-(1 / 4 : ℝ)) ≤ (Real.pi * y) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [Real.pi_pos]) (by norm_num)
      have he : Real.exp (-(2 * Real.pi * (t * y))) = Real.exp (-(2 * Real.pi * y) * t) := by
        congr 1; ring
      simp only [F]
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hy.le, Real.norm_of_nonneg (partialRS_nonneg _)]
      calc y * (‖kkd lamE (t * y)‖ * y) * partialRS ρ t
          ≤ y * (4 * ‖modifiedBesselKOrder (2 * Real.pi * (t * y)) (nu lamE)‖ / (t * y) * y) * (C * t) := by
            gcongr; exact partialRS_nonneg _
        _ = 4 * C * y * ‖modifiedBesselKOrder (2 * Real.pi * (t * y)) (nu lamE)‖ := by
            field_simp
        _ ≤ 4 * C * y * (M * ((2 * Real.pi * (t * y)) ^ (-(1 / 4 : ℝ)) + 1) *
              Real.exp (-(2 * Real.pi * (t * y)))) := by gcongr
        _ ≤ 4 * C * y * (M * ((Real.pi * y) ^ (-(1 / 4 : ℝ)) + 1) *
              Real.exp (-(2 * Real.pi * (t * y)))) := by gcongr
        _ = 4 * C * y * (M * ((Real.pi * y) ^ (-(1 / 4 : ℝ)) + 1)) *
              Real.exp (-(2 * Real.pi * y) * t) := by rw [he]; ring
  have hsum := (hasSum_slice_nat hg hρ0 hρ hy).tendsto_sum_nat
  have hL : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Ioc 0 N, (y : ℂ) * kk lamE (k * y) *
      ((rsCoeff ρ k : ℝ) : ℂ)) atTop (𝓝 (WeylUpper.slice g y : ℂ)) := by
    refine (hsum.comp (tendsto_add_atTop_nat 1)).congr fun N => ?_
    simp only [Function.comp_apply]
    rw [← Icc_eq_range, ← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le N)]
    simp [rsCoeff, hρ0]
  have hB : Tendsto (fun N : ℕ => (y : ℂ) * kk lamE (N * y) * ((partialRS ρ N : ℝ) : ℂ)) atTop
      (𝓝 0) := by
    have hr : 0 < 4 * Real.pi * y := by positivity
    have h0 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hr)).const_mul
        (C * Real.exp 1 ^ 2 * y / (4 * Real.pi * y))
    rw [mul_zero] at h0
    refine squeeze_zero_norm' ?_ h0
    have hev : ∀ᶠ N : ℕ in atTop, 1 ≤ 2 * Real.pi * (N * y) :=
      ((tendsto_natCast_atTop_atTop.atTop_mul_const hy).const_mul_atTop
        (by positivity : 0 < 2 * Real.pi)).eventually_ge_atTop 1
    filter_upwards [hev] with N hN
    have hK := _root_.RHTower.norm_modifiedBesselKOrder_I_mul_le_exp hN (Real.sqrt (lamE - 1 / 4))
    rw [← nu_eq] at hK
    have hS := hC N (Nat.cast_nonneg N)
    have he2 : Real.exp (-(2 * Real.pi * (N * y))) ^ 2 = Real.exp (-(4 * Real.pi * y * N)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    simp only [Function.comp_apply]
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hy.le,
      Real.norm_of_nonneg (partialRS_nonneg _)]
    unfold kk
    rw [norm_mul, ← sq]
    calc y * ‖modifiedBesselKOrder (2 * Real.pi * (N * y)) (nu lamE)‖ ^ 2 * partialRS ρ N
        ≤ y * (Real.exp 1 * Real.exp (-(2 * Real.pi * (N * y)))) ^ 2 * (C * N) := by
          gcongr; exact partialRS_nonneg _
      _ = C * Real.exp 1 ^ 2 * y / (4 * Real.pi * y) *
            ((4 * Real.pi * y * N) ^ 1 * Real.exp (-(4 * Real.pi * y * N))) := by
          rw [mul_pow, he2, pow_one]; field_simp
  have hI : Tendsto (fun N : ℕ => ∫ t in Ioc (1 / 2 : ℝ) N, F t) atTop
      (𝓝 (∫ t in Ioi (1 / 2 : ℝ), F t)) := by
    have h := intervalIntegral_tendsto_integral_Ioi (1 / 2 : ℝ) hFint tendsto_natCast_atTop_atTop
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [intervalIntegral.integral_of_le (by linarith)]
  have hR := hB.sub hI
  rw [zero_sub] at hR
  refine tendsto_nhds_unique hL (hR.congr' ?_)
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (abel_N hρ0 hy N hN).symm

/-- **Substitution `u = ty`**: `∫_{1/2}^∞ y² k'(ty) S(t) dt = ∫_0^∞ y k'(u) S(u/y) du`. -/
theorem integral_subst (hρ0 : ρ 0 = 0) {y : ℝ} (hy : 0 < y) :
    ∫ t in Ioi (1 / 2 : ℝ), (y : ℂ) * (kkd lamE (t * y) * y) * ((partialRS ρ t : ℝ) : ℂ) =
      ∫ u in Ioi (0 : ℝ), (y : ℂ) * kkd lamE u * ((partialRS ρ (u / y) : ℝ) : ℂ) := by
  have hyC : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy.ne'
  set G : ℝ → ℂ := fun u => (y : ℂ) * (kkd lamE u * y) * ((partialRS ρ (u / y) : ℝ) : ℂ)
  calc ∫ t in Ioi (1 / 2 : ℝ), (y : ℂ) * (kkd lamE (t * y) * y) * ((partialRS ρ t : ℝ) : ℂ)
      = ∫ t in Ioi (1 / 2 : ℝ), G (t * y) :=
        setIntegral_congr_fun measurableSet_Ioi fun t _ => by
          simp only [G, mul_div_cancel_right₀ t hy.ne']
    _ = (y⁻¹ : ℝ) • ∫ u in Ioi (1 / 2 * y), G u := integral_comp_mul_right_Ioi G (1 / 2) hy
    _ = ∫ u in Ioi (1 / 2 * y), (y : ℂ) * kkd lamE u * ((partialRS ρ (u / y) : ℝ) : ℂ) := by
        rw [Complex.real_smul, ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
        simp only [G]
        generalize ((partialRS ρ (u / y) : ℝ) : ℂ) = S'
        rw [ofReal_inv, show (y : ℂ)⁻¹ * ((y : ℂ) * (kkd lamE u * y) * S') =
          ((y : ℂ)⁻¹ * y) * (y * kkd lamE u * S') by ring, inv_mul_cancel₀ hyC, one_mul]
    _ = ∫ u in Ioi (0 : ℝ), (y : ℂ) * kkd lamE u * ((partialRS ρ (u / y) : ℝ) : ℂ) := by
        refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi ?_ ?_).symm
        · intro u hu; simp only [mem_Ioi] at hu ⊢; linarith
        · rintro u ⟨hu0, hu1⟩
          simp only [mem_Ioi, not_lt] at hu0 hu1
          rw [partialRS_of_lt_one hρ0 (by rw [div_lt_one hy]; linarith)]
          simp

/-! ### The limit `y → 0` -/

theorem tendsto_integral (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) :
    Tendsto (fun y : ℝ => ∫ u in Ioi (0 : ℝ), (y : ℂ) * kkd lamE u * ((partialRS ρ (u / y) : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 (∫ u in Ioi (0 : ℝ), ((msConst lamE g : ℝ) : ℂ) * ((u : ℂ) * kkd lamE u))) := by
  obtain ⟨C, hC0, hC⟩ := exists_partialRS_le hg hρ0 hρ
  obtain ⟨M, hM0, hM⟩ := exists_norm_K_le lamE
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u => 4 * C * (M * ((2 * Real.pi * u) ^ (-(1 / 4 : ℝ)) + 1) * Real.exp (-(2 * Real.pi * u))))
    ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact ((continuousOn_const.mul continuousOn_kkd).aestronglyMeasurable measurableSet_Ioi).mul
      (Complex.measurable_ofReal.comp (measurable_partialRS.comp
        (measurable_id.div_const y))).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : (0 : ℝ) < y := hy
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u (hu : 0 < u) => ?_)
    have hkd := norm_kkd_le (lamE := lamE) hu
    have hK := hM (2 * Real.pi * u) (by positivity)
    have hS := hC (u / y) (by positivity)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hy0.le,
      Real.norm_of_nonneg (partialRS_nonneg _)]
    calc y * ‖kkd lamE u‖ * partialRS ρ (u / y)
        ≤ y * (4 * ‖modifiedBesselKOrder (2 * Real.pi * u) (nu lamE)‖ / u) * (C * (u / y)) := by
          gcongr; exact partialRS_nonneg _
      _ = 4 * C * ‖modifiedBesselKOrder (2 * Real.pi * u) (nu lamE)‖ := by field_simp
      _ ≤ _ := by gcongr
  · have hI : IntegrableOn (fun u : ℝ => 4 * C * M * (((2 * Real.pi * u) ^ (-(1 / 4 : ℝ)) + 1) *
        Real.exp (-(2 * Real.pi * u)))) (Ioi 0) :=
      (integrableOn_rpow_exp (a := -(1 / 4)) (b := 2 * Real.pi) (c := 2 * Real.pi) (by norm_num)
        (by positivity) (by positivity)).const_mul (4 * C * M)
    exact hI.congr_fun (fun u _ => by ring) measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u (hu : 0 < u) => ?_)
    have hlim := tendsto_partialRS_div hg hρ0 hρ
    have hu' : Tendsto (fun y : ℝ => u / y) (𝓝[>] 0) atTop := by
      simpa [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop hu
    have h1 := (hlim.comp hu').const_mul u
    have h2 : Tendsto (fun y : ℝ => y * partialRS ρ (u / y)) (𝓝[>] 0) (𝓝 (u * msConst lamE g)) := by
      refine h1.congr' (eventually_nhdsWithin_of_forall fun y (hy : 0 < y) => ?_)
      have := hu.ne'
      have := hy.ne'
      simp only [Function.comp_apply]
      field_simp
    have e : (fun y : ℝ => (y : ℂ) * kkd lamE u * ((partialRS ρ (u / y) : ℝ) : ℂ)) =
        fun y : ℝ => kkd lamE u * ((y * partialRS ρ (u / y) : ℝ) : ℂ) := by
      funext y; push_cast; ring
    show Tendsto (fun y : ℝ => (y : ℂ) * kkd lamE u * ((partialRS ρ (u / y) : ℝ) : ℂ)) _ _
    rw [e, show ((msConst lamE g : ℝ) : ℂ) * ((u : ℂ) * kkd lamE u) =
      kkd lamE u * ((u * msConst lamE g : ℝ) : ℂ) by push_cast; ring]
    exact tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp h2)

/-- **Integration by parts**: `∫_0^∞ u k'(u) du = -∫_0^∞ k(u) du`. -/
theorem integral_mul_kkd (lamE : ℝ) :
    ∫ u in Ioi (0 : ℝ), (u : ℂ) * kkd lamE u = -∫ u in Ioi (0 : ℝ), kk lamE u := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_K_le lamE
  have hderiv : ∀ u ∈ Ioi (0 : ℝ), HasDerivAt (fun u : ℝ => (u : ℂ) * kk lamE u)
      (kk lamE u + (u : ℂ) * kkd lamE u) u := by
    intro u hu
    have h1 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 u := by
      simpa using (hasDerivAt_id u).ofReal_comp
    exact (h1.mul (hasDerivAt_kk hu)).congr_deriv (by ring)
  have hint_kk : IntegrableOn (kk lamE) (Ioi 0) := by
    refine Integrable.mono' ((integrableOn_rpow_exp (a := -(1 / 2)) (b := 4 * Real.pi)
      (c := 2 * Real.pi) (by norm_num) (by positivity) (by positivity)).const_mul (2 * M ^ 2))
      (continuousOn_kk.aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u (hu : 0 < u) => ?_)
    refine (norm_kk_le hM hu).trans (le_of_eq ?_)
    ring
  have hint_ukkd : IntegrableOn (fun u : ℝ => (u : ℂ) * kkd lamE u) (Ioi 0) := by
    refine Integrable.mono' ((integrableOn_rpow_exp (a := -(1 / 4)) (b := 2 * Real.pi)
      (c := 2 * Real.pi) (by norm_num) (by positivity) (by positivity)).const_mul (4 * M))
      ((Complex.continuous_ofReal.continuousOn.mul continuousOn_kkd).aestronglyMeasurable
        measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u (hu : 0 < u) => ?_)
    have hkd := norm_kkd_le (lamE := lamE) hu
    have hK := hM (2 * Real.pi * u) (by positivity)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu.le]
    calc u * ‖kkd lamE u‖ ≤ u * (4 * ‖modifiedBesselKOrder (2 * Real.pi * u) (nu lamE)‖ / u) := by
          gcongr
      _ = 4 * ‖modifiedBesselKOrder (2 * Real.pi * u) (nu lamE)‖ := by field_simp
      _ ≤ 4 * (M * ((2 * Real.pi * u) ^ (-(1 / 4 : ℝ)) + 1) * Real.exp (-(2 * Real.pi * u))) := by
          gcongr
      _ = _ := by ring
  have hcont : ContinuousWithinAt (fun u : ℝ => (u : ℂ) * kk lamE u) (Ici 0) 0 := by
    have hβ : Continuous fun u : ℝ =>
        2 * M ^ 2 * ((2 * Real.pi) ^ (-(1 / 2 : ℝ)) * u ^ (1 / 2 : ℝ) + u) :=
      continuous_const.mul ((continuous_const.mul (Real.continuous_rpow_const (by norm_num))).add
        continuous_id)
    have hβ0 : Tendsto (fun u : ℝ => 2 * M ^ 2 * ((2 * Real.pi) ^ (-(1 / 2 : ℝ)) * u ^ (1 / 2 : ℝ) + u))
        (𝓝[Ici 0] 0) (𝓝 0) := by
      have := (hβ.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ici (0 : ℝ)))
      simpa using this
    rw [ContinuousWithinAt, show ((0 : ℝ) : ℂ) * kk lamE 0 = 0 by simp]
    refine squeeze_zero_norm' ?_ hβ0
    filter_upwards [self_mem_nhdsWithin] with u hu
    rcases (show (0 : ℝ) ≤ u from hu).eq_or_lt with h | h
    · subst h; simp
    · have hk := norm_kk_le hM h
      have hx : 0 < 2 * Real.pi * u := by positivity
      have hsplit : u * (2 * Real.pi * u) ^ (-(1 / 2 : ℝ)) =
          (2 * Real.pi) ^ (-(1 / 2 : ℝ)) * u ^ (1 / 2 : ℝ) := by
        have hu2 : u ^ (1 / 2 : ℝ) = u * u ^ (-(1 / 2) : ℝ) := by
          rw [← Real.rpow_one_add' h.le (by norm_num)]; norm_num
        rw [Real.mul_rpow (by positivity) h.le, hu2]
        ring
      have he : Real.exp (-(4 * Real.pi * u)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
      have hp : 0 ≤ (2 * Real.pi * u) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx.le _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h.le]
      calc u * ‖kk lamE u‖ ≤ u * (2 * M ^ 2 * ((2 * Real.pi * u) ^ (-(1 / 2 : ℝ)) + 1) *
            Real.exp (-(4 * Real.pi * u))) := by gcongr
        _ ≤ u * (2 * M ^ 2 * ((2 * Real.pi * u) ^ (-(1 / 2 : ℝ)) + 1) * 1) := by gcongr
        _ = 2 * M ^ 2 * (u * (2 * Real.pi * u) ^ (-(1 / 2 : ℝ)) + u) := by ring
        _ = _ := by rw [hsplit]
  have hlim : Tendsto (fun u : ℝ => (u : ℂ) * kk lamE u) atTop (𝓝 0) := by
    have h0 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < 4 * Real.pi))).const_mul
        (Real.exp 1 ^ 2 / (4 * Real.pi))
    rw [mul_zero] at h0
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_ge_atTop (1 / (2 * Real.pi))] with u hu
    have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu
    have hx : 1 ≤ 2 * Real.pi * u := by
      rw [div_le_iff₀ (by positivity)] at hu; linarith
    have hK := _root_.RHTower.norm_modifiedBesselKOrder_I_mul_le_exp hx (Real.sqrt (lamE - 1 / 4))
    rw [← nu_eq] at hK
    have he2 : Real.exp (-(2 * Real.pi * u)) ^ 2 = Real.exp (-(4 * Real.pi * u)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0.le]
    unfold kk
    rw [norm_mul, ← sq]
    simp only [Function.comp_apply, id]
    calc u * ‖modifiedBesselKOrder (2 * Real.pi * u) (nu lamE)‖ ^ 2
        ≤ u * (Real.exp 1 * Real.exp (-(2 * Real.pi * u))) ^ 2 := by gcongr
      _ = Real.exp 1 ^ 2 / (4 * Real.pi) * ((4 * Real.pi * u) ^ 1 * Real.exp (-(4 * Real.pi * u))) := by
          rw [mul_pow, he2, pow_one]; field_simp
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv (hint_kk.add hint_ukkd) hlim
  rw [integral_add hint_kk hint_ukkd, ofReal_zero, zero_mul, sub_zero] at h
  linear_combination h

/-! ### The constant -/

theorem gammaFactor_one (lamE : ℝ) :
    CuspRSI.gammaFactor (nu lamE) 1 =
      ((Real.pi ^ 2 / (4 * Real.cosh (Real.pi * Real.sqrt (lamE - 1 / 4))) : ℝ) : ℂ) := by
  set t := Real.sqrt (lamE - 1 / 4)
  have hpi0 : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hch : (Real.cosh (Real.pi * t) : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.cosh_pos _).ne'
  have hν : nu lamE = (t : ℂ) * I := rfl
  have hrefl : Gamma ((1 + nu lamE + nu lamE) / 2) * Gamma ((1 - nu lamE - nu lamE) / 2) =
      (Real.pi : ℂ) / (Real.cosh (Real.pi * t) : ℂ) := by
    rw [show (1 - nu lamE - nu lamE) / 2 = 1 - (1 + nu lamE + nu lamE) / 2 by ring,
      Gamma_mul_Gamma_one_sub,
      show (Real.pi : ℂ) * ((1 + nu lamE + nu lamE) / 2) = ((Real.pi * t : ℝ) : ℂ) * I + Real.pi / 2 by
        rw [hν]; push_cast; ring, sin_add_pi_div_two, cos_mul_I, ← ofReal_cosh]
  have hhalf : Gamma (1 / 2) * Gamma (1 / 2) = (Real.pi : ℂ) := by
    rw [Gamma_one_half_eq, ← cpow_add _ _ hpi0]; norm_num
  have h2 : (2 : ℂ) ^ ((1 : ℂ) - 3) = 1 / 4 := by
    rw [show (1 : ℂ) - 3 = -((2 : ℕ) : ℂ) by norm_num, cpow_neg, cpow_natCast]; norm_num
  unfold CuspRSI.gammaFactor
  rw [h2, Gamma_one,
    show (1 + nu lamE - nu lamE) / 2 = (1 / 2 : ℂ) by ring,
    show (1 - nu lamE + nu lamE) / 2 = (1 / 2 : ℂ) by ring,
    show Gamma ((1 + nu lamE + nu lamE) / 2) * Gamma (1 / 2) * Gamma (1 / 2) *
        Gamma ((1 - nu lamE - nu lamE) / 2) = (Gamma ((1 + nu lamE + nu lamE) / 2) *
          Gamma ((1 - nu lamE - nu lamE) / 2)) * (Gamma (1 / 2) * Gamma (1 / 2)) by ring,
    hrefl, hhalf]
  push_cast
  field_simp

/-- `∫_0^∞ K_ν(2πu)² du = π/(8 cosh πt)`. -/
theorem integral_kk (lamE : ℝ) :
    ∫ u in Ioi (0 : ℝ), kk lamE u =
      ((Real.pi / (8 * Real.cosh (Real.pi * Real.sqrt (lamE - 1 / 4))) : ℝ) : ℂ) := by
  have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
  have hch : Real.cosh (Real.pi * Real.sqrt (lamE - 1 / 4)) ≠ 0 := (Real.cosh_pos _).ne'
  have h := CuspRSI.integral_scaled_KK (lamE := lamE) (s := 1) (c := 2 * Real.pi) (by positivity)
  rw [GaloisForLFunctions.RHTower.integral_cpow_mul_modifiedBesselKOrder_mul_modifiedBesselKOrder
    (by simp [nu_re])] at h
  have e : ∫ u in Ioi (0 : ℝ), kk lamE u = ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ ((1 : ℂ) - 1) *
      (modifiedBesselKOrder (2 * Real.pi * y) (nu lamE) *
        modifiedBesselKOrder (2 * Real.pi * y) (nu lamE)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp [kk]
  have hg := gammaFactor_one lamE
  unfold CuspRSI.gammaFactor at hg
  rw [e, h, hg, cpow_neg_one]
  push_cast
  field_simp
  ring

/-! ### Equidistribution -/

/-- **Long closed horocycles equidistribute the energy of a cusp mode**:
`∫_{-1/2}^{1/2} |g(x + iy)|² dx → (3/π) ∫_𝒟 |g|² dμ` as `y → 0⁺`. -/
theorem tendsto_slice (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) :
    Tendsto (WeylUpper.slice g) (𝓝[>] 0) (𝓝 (3 / Real.pi * ∫ z in ModularGroup.fd, ‖g z‖ ^ 2)) := by
  have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
  have hch : Real.cosh (Real.pi * Real.sqrt (lamE - 1 / 4)) ≠ 0 := (Real.cosh_pos _).ne'
  have hD := tendsto_integral hg hρ0 hρ
  rw [integral_const_mul, integral_mul_kkd, integral_kk] at hD
  have hreal : msConst lamE g * (Real.pi / (8 * Real.cosh (Real.pi * Real.sqrt (lamE - 1 / 4)))) =
      3 / Real.pi * ∫ z in ModularGroup.fd, ‖g z‖ ^ 2 := by
    unfold msConst; field_simp; ring
  have hval : -(((msConst lamE g : ℝ) : ℂ) *
      -((Real.pi / (8 * Real.cosh (Real.pi * Real.sqrt (lamE - 1 / 4))) : ℝ) : ℂ)) =
      ((3 / Real.pi * ∫ z in ModularGroup.fd, ‖g z‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_neg, neg_neg, ← ofReal_mul, hreal]
  have hC : Tendsto (fun y : ℝ => (WeylUpper.slice g y : ℂ)) (𝓝[>] 0)
      (𝓝 ((3 / Real.pi * ∫ z in ModularGroup.fd, ‖g z‖ ^ 2 : ℝ) : ℂ)) := by
    rw [← hval]
    refine hD.neg.congr' (eventually_nhdsWithin_of_forall fun y (hy : 0 < y) => ?_)
    show _ = (WeylUpper.slice g y : ℂ)
    rw [slice_eq_integral hg hρ0 hρ hy, integral_subst hρ0 hy]
  have := (Complex.continuous_re.tendsto _).comp hC
  simp only [Function.comp_def, ofReal_re] at this
  exact this

end CuspHE

end GaloisForLFunctions.BlackHoleRingdown
