import GaloisForLFunctions.RHTower.EulerFisherCurvature
import GaloisForLFunctions.HTGeometry.CanonicalEulerLog

/-!
# The Poincare boundary of the zeta Fisher superspace

On the physical half-plane `1 < beta` the Euler prime-power cumulants

```text
M_j(beta) = sum_p sum_{k >= 1} (k log p)^j p^{-k beta} / k
```

are the derivatives of the real Euler logarithm `F(beta) = log zeta(beta)`: termwise
differentiation gives `M_j' = -M_{j+1}`, so the second, third and fourth derivatives of `F` are
`M_2`, `-M_3` and `M_4`.

The temperature-clock superspace carries the conformal metric `M_2(beta) (dbeta^2 + dtau^2)`.  Its
Liouville scalar curvature `-Laplacian(log M_2)/M_2` is exactly the moment expression
`-(M_2 M_4 - M_3^2)/M_2^3` whose strict negativity is proved in `EulerFisherCurvature`.

At the pole the analytic unit `u(s) = (s-1) zeta(s)` has `u(1) = 1`, so
`F(beta) = -log(beta-1) + log u(beta)` with an analytic remainder.  Differentiating four times
isolates the singular parts `M_2 ~ delta^{-2}`, `M_3 ~ 2 delta^{-3}`, `M_4 ~ 6 delta^{-4}`, and the
curvature tends to `-2`: the metric is asymptotically the Poincare half-plane metric of Gaussian
curvature `-1`.
-/

open Set Filter Topology Complex

namespace RHTower

noncomputable section

/-- Scalar curvature of the conformal surface metric `G (dx² + dy²)`, in the Liouville form
`Scal = -Δ(log G)/G`, for a scale factor depending on the first coordinate only. -/
def conformalScalarCurvature (G : ℝ → ℝ) (β : ℝ) : ℝ :=
  -deriv (deriv fun t => Real.log (G t)) β / G β

theorem conformalScalarCurvature_eq_of_hasDerivAt
    {G G' : ℝ → ℝ} {G'' β : ℝ}
    (hpos : ∀ᶠ t in 𝓝 β, 0 < G t)
    (hG : ∀ᶠ t in 𝓝 β, HasDerivAt G (G' t) t)
    (hG' : HasDerivAt G' G'' β) :
    conformalScalarCurvature G β = -(G β * G'' - G' β ^ 2) / G β ^ 3 := by
  have hGβ : 0 < G β := hpos.self_of_nhds
  have hlog : ∀ᶠ t in 𝓝 β, deriv (fun r => Real.log (G r)) t = G' t / G t := by
    filter_upwards [hpos, hG] with t ht hgt
    exact (hgt.log ht.ne').deriv
  have h2 : HasDerivAt (fun t => G' t / G t) ((G'' * G β - G' β * G' β) / G β ^ 2) β := by
    have hGd : HasDerivAt G (G' β) β := hG.self_of_nhds
    exact hG'.div hGd hGβ.ne'
  have hd : deriv (deriv fun t => Real.log (G t)) β = (G'' * G β - G' β * G' β) / G β ^ 2 := by
    rw [Filter.EventuallyEq.deriv_eq hlog]
    exact h2.deriv
  rw [conformalScalarCurvature, hd]
  field_simp

/-! ## Termwise differentiation of the Euler moments -/

theorem two_le_eulerPrimePowerNat' (z : Nat.Primes × ℕ) : 2 ≤ eulerPrimePowerNat z := by
  have h2 : 2 ≤ z.1.1 := z.1.2.two_le
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ z.1.1 ^ (z.2 + 1) := Nat.pow_le_pow_left h2 _ |>.trans' (by
        exact Nat.pow_le_pow_right (by norm_num) (by omega))
    _ = eulerPrimePowerNat z := rfl

theorem one_le_eulerPrimePowerNat_real (z : Nat.Primes × ℕ) :
    (1 : ℝ) ≤ (eulerPrimePowerNat z : ℝ) := by
  have := two_le_eulerPrimePowerNat' z
  exact_mod_cast le_trans (by norm_num) this

/-- Summability of the pure energy-power tail without the harmonic weight. -/
theorem summable_eulerPrimePowerEnergy_pow_rpow (m : ℕ) {c : ℝ} (hc : 1 < c) :
    Summable (fun z : Nat.Primes × ℕ =>
      eulerPrimePowerEnergy z ^ m * (eulerPrimePowerNat z : ℝ) ^ (-c)) := by
  have hsNat : Summable (fun n : ℕ => |Real.log n| ^ m * (n : ℝ) ^ (-c)) :=
    summable_abs_log_natCast_pow_mul_rpow_neg m c hc
  have hsComp := hsNat.comp_injective eulerPrimePowerNat_injective
  apply hsComp.congr
  intro z
  have hlog : 0 ≤ Real.log (eulerPrimePowerNat z) := Real.log_natCast_nonneg _
  simp only [eulerPrimePowerEnergy, Function.comp_apply]
  rw [abs_of_nonneg hlog]

theorem hasDerivAt_eulerMoment (j : ℕ) {β : ℝ} (hβ : 1 < β) :
    HasDerivAt
      (fun t : ℝ =>
        fisherWeightedTsumMoment (eulerPrimePowerWeight t) eulerPrimePowerEnergy j)
      (-(fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy (j + 1)))
      β := by
  classical
  set c : ℝ := (1 + β) / 2 with hcdef
  have hc1 : 1 < c := by rw [hcdef]; linarith
  have hcβ : c < β := by rw [hcdef]; linarith
  set g : (Nat.Primes × ℕ) → ℝ → ℝ := fun z t =>
    eulerPrimePowerWeight t z * eulerPrimePowerEnergy z ^ j with hg
  set g' : (Nat.Primes × ℕ) → ℝ → ℝ := fun z t =>
    -(eulerPrimePowerWeight t z * eulerPrimePowerEnergy z ^ (j + 1)) with hg'
  have hderiv : ∀ (z : Nat.Primes × ℕ), ∀ t ∈ Set.Ioi c, HasDerivAt (g z) (g' z t) t := by
    intro z t _
    have hn : (0 : ℝ) < (eulerPrimePowerNat z : ℝ) :=
      lt_of_lt_of_le zero_lt_one (one_le_eulerPrimePowerNat_real z)
    have hbase := HasDerivAt.const_rpow (a := (eulerPrimePowerNat z : ℝ)) hn (hasDerivAt_neg t)
    have h2 := (hbase.div_const ((z.2 : ℝ) + 1)).mul_const (eulerPrimePowerEnergy z ^ j)
    have hval : Real.log (eulerPrimePowerNat z : ℝ) * -1 * (eulerPrimePowerNat z : ℝ) ^ (-t) /
          ((z.2 : ℝ) + 1) * eulerPrimePowerEnergy z ^ j
        = -((eulerPrimePowerNat z : ℝ) ^ (-t) / ((z.2 : ℝ) + 1) *
            eulerPrimePowerEnergy z ^ (j + 1)) := by
      simp only [eulerPrimePowerEnergy]
      ring
    have hgoal := h2.congr_deriv hval
    simpa [hg, hg', eulerPrimePowerWeight] using hgoal
  have hbound : ∀ (z : Nat.Primes × ℕ), ∀ t ∈ Set.Ioi c,
      ‖g' z t‖ ≤ eulerPrimePowerEnergy z ^ (j + 1) * (eulerPrimePowerNat z : ℝ) ^ (-c) := by
    intro z t ht
    have hn1 : (1 : ℝ) ≤ (eulerPrimePowerNat z : ℝ) := one_le_eulerPrimePowerNat_real z
    have hlog : 0 ≤ eulerPrimePowerEnergy z := Real.log_natCast_nonneg _
    have hrpow : (eulerPrimePowerNat z : ℝ) ^ (-t) ≤ (eulerPrimePowerNat z : ℝ) ^ (-c) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by simp only [neg_le_neg_iff]; exact le_of_lt ht)
    have hden : (1 : ℝ) ≤ (z.2 : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (z.2 : ℝ) := Nat.cast_nonneg _
      linarith
    have hpos : 0 ≤ (eulerPrimePowerNat z : ℝ) ^ (-t) := Real.rpow_nonneg (by linarith) _
    simp only [hg', eulerPrimePowerWeight, Real.norm_eq_abs, abs_neg]
    rw [abs_of_nonneg (by positivity)]
    calc (eulerPrimePowerNat z : ℝ) ^ (-t) / ((z.2 : ℝ) + 1) * eulerPrimePowerEnergy z ^ (j + 1)
        ≤ (eulerPrimePowerNat z : ℝ) ^ (-t) * eulerPrimePowerEnergy z ^ (j + 1) := by
          gcongr
          exact div_le_self hpos hden
      _ ≤ (eulerPrimePowerNat z : ℝ) ^ (-c) * eulerPrimePowerEnergy z ^ (j + 1) := by
          gcongr
      _ = eulerPrimePowerEnergy z ^ (j + 1) * (eulerPrimePowerNat z : ℝ) ^ (-c) := by ring
  have hsum0 : Summable fun z : Nat.Primes × ℕ => g z β := by
    refine Summable.of_abs ?_
    simpa [hg] using summable_abs_eulerPrimePower_moment j β hβ
  have hmain := hasDerivAt_tsum_of_isPreconnected
    (summable_eulerPrimePowerEnergy_pow_rpow (j + 1) hc1)
    isOpen_Ioi (isPreconnected_Ioi) hderiv hbound (Set.mem_Ioi.mpr hcβ) hsum0
    (Set.mem_Ioi.mpr hcβ)
  have hneg : (∑' z : Nat.Primes × ℕ, g' z β)
      = -(fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy (j + 1)) := by
    simp only [hg', fisherWeightedTsumMoment]
    exact tsum_neg
  rw [hneg] at hmain
  exact hmain

/-! ## The Euler logarithm as the zeroth moment -/

/-- The zeroth Euler prime-power moment: the real Euler logarithm of zeta. -/
def eulerLogMoment (β : ℝ) : ℝ :=
  fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy 0

theorem eulerLogMoment_eq_tsum (β : ℝ) :
    eulerLogMoment β = ∑' z : Nat.Primes × ℕ, eulerPrimePowerWeight β z := by
  simp [eulerLogMoment, fisherWeightedTsumMoment]

theorem term_eulerLogDirichletCoeff_eulerPrimePowerNat (β : ℝ) (z : Nat.Primes × ℕ) :
    LSeries.term eulerLogDirichletCoeff (β : ℂ) (eulerPrimePowerNat z)
      = ((eulerPrimePowerWeight β z : ℝ) : ℂ) := by
  obtain ⟨p, k⟩ := z
  have hN : eulerPrimePowerNat (p, k) = p.1 ^ (k + 1) := rfl
  have hpos : 0 < p.1 ^ (k + 1) := pow_pos p.2.pos _
  have hne : eulerPrimePowerNat (p, k) ≠ 0 := by rw [hN]; omega
  have hnR : (0 : ℝ) < ((p.1 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hpos
  rw [LSeries.term_of_ne_zero hne, hN, eulerLogDirichletCoeff_prime_pow_succ p.1 k p.2]
  rw [show ((p.1 ^ (k + 1) : ℕ) : ℂ) = (((p.1 ^ (k + 1) : ℕ) : ℝ) : ℂ) by push_cast; ring]
  rw [← Complex.ofReal_cpow hnR.le]
  simp only [eulerPrimePowerWeight, eulerPrimePowerNat, Real.rpow_neg hnR.le]
  push_cast
  ring

theorem support_term_eulerLogDirichletCoeff_subset (β : ℝ) :
    Function.support (LSeries.term eulerLogDirichletCoeff (β : ℂ)) ⊆
      Set.range eulerPrimePowerNat := by
  intro n hn
  simp only [Function.mem_support] at hn
  rcases eq_or_ne n 0 with rfl | hn0
  · exact absurd (LSeries.term_zero _ _) hn
  by_cases hpp : IsPrimePow n
  · obtain ⟨q, k, hq, hk, hqk⟩ := hpp
    have hqn : Nat.Prime q := Nat.prime_iff.mpr hq
    refine ⟨(⟨q, hqn⟩, k - 1), ?_⟩
    show q ^ (k - 1 + 1) = n
    rw [Nat.sub_add_cancel hk]
    exact hqk
  · exact absurd (by
      rw [LSeries.term_of_ne_zero hn0,
        eulerLogDirichletCoeff_eq_zero_of_not_primePower hpp]
      simp) hn

/-- The canonical Euler logarithm of zeta at a real point is the real zeroth Euler moment. -/
theorem canonicalEulerLogZeta_ofReal (β : ℝ) :
    canonicalEulerLogZeta (β : ℂ) = ((eulerLogMoment β : ℝ) : ℂ) := by
  rw [canonicalEulerLogZeta, LSeries]
  rw [← (eulerPrimePowerNat_injective).tsum_eq (support_term_eulerLogDirichletCoeff_subset β)]
  rw [eulerLogMoment_eq_tsum, Complex.ofReal_tsum]
  exact tsum_congr fun z => term_eulerLogDirichletCoeff_eulerPrimePowerNat β z

/-- On the physical half-plane, zeta at a real point is the exponential of the real Euler
logarithm; in particular it is real and strictly positive. -/
theorem riemannZeta_ofReal_eq_exp_eulerLogMoment {β : ℝ} (hβ : 1 < β) :
    riemannZeta (β : ℂ) = ((Real.exp (eulerLogMoment β) : ℝ) : ℂ) := by
  have hre : (1 : ℝ) < ((β : ℂ)).re := by simpa using hβ
  rw [← exp_canonicalEulerLogZeta_eq_riemannZeta hre, canonicalEulerLogZeta_ofReal,
    ← Complex.ofReal_exp]

/-! ## The analytic unit of the zeta pole -/

/-- The analytic unit of the simple pole of `ζ` at `s = 1`: it agrees with `(s-1) ζ(s)` away
from `1` and takes the value `1` at `1`. -/
def zetaPoleUnit (s : ℂ) : ℂ :=
  (s - 1) * (riemannZeta s - 1 / (s - 1) / Complex.Gammaℝ s) + (Complex.Gammaℝ s)⁻¹

@[simp] theorem zetaPoleUnit_one : zetaPoleUnit 1 = 1 := by
  simp [zetaPoleUnit, Complex.Gammaℝ_one]

theorem zetaPoleUnit_eq_of_ne {s : ℂ} (hs : s ≠ 1) :
    zetaPoleUnit s = (s - 1) * riemannZeta s := by
  have h : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have key : (s - 1) * (1 / (s - 1) / Complex.Gammaℝ s) = (Complex.Gammaℝ s)⁻¹ := by
    by_cases hG : Complex.Gammaℝ s = 0
    · simp [hG]
    · field_simp
  rw [zetaPoleUnit, mul_sub, key, sub_add_cancel]

theorem differentiable_zetaPoleUnit : Differentiable ℂ zetaPoleUnit := by
  intro s
  have hsub : DifferentiableAt ℂ (fun r : ℂ => r - 1) s := differentiableAt_id.sub_const 1
  have hinv : DifferentiableAt ℂ (fun r : ℂ => (Complex.Gammaℝ r)⁻¹) s :=
    Complex.differentiable_Gammaℝ_inv s
  have hrw : (fun r : ℂ => 1 / (r - 1) / Complex.Gammaℝ r)
      = fun r : ℂ => (1 / (r - 1)) * (Complex.Gammaℝ r)⁻¹ := by
    funext r; rw [div_eq_mul_inv]
  rcases eq_or_ne s 1 with rfl | hs
  · have hz : DifferentiableAt ℂ
        (fun r : ℂ => riemannZeta r - 1 / (r - 1) / Complex.Gammaℝ r) 1 := by
      have := HurwitzZeta.differentiableAt_hurwitzZetaEven_sub_one_div 0
      rwa [HurwitzZeta.hurwitzZetaEven_zero] at this
    exact (hsub.mul hz).add hinv
  · have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    have hz : DifferentiableAt ℂ
        (fun r : ℂ => riemannZeta r - 1 / (r - 1) / Complex.Gammaℝ r) s := by
      refine (differentiableAt_riemannZeta hs).sub ?_
      rw [hrw]
      exact ((differentiableAt_const (1 : ℂ)).div hsub hs1).mul hinv
    exact (hsub.mul hz).add hinv

theorem analyticAt_zetaPoleUnit (s : ℂ) : AnalyticAt ℂ zetaPoleUnit s :=
  (differentiable_zetaPoleUnit.differentiableOn.analyticOnNhd isOpen_univ) s (Set.mem_univ s)

/-- The analytic logarithm of the pole unit near `s = 1`. -/
def zetaPoleLog (s : ℂ) : ℂ := Complex.log (zetaPoleUnit s)

theorem analyticAt_zetaPoleLog : AnalyticAt ℂ zetaPoleLog 1 := by
  have hslit : (zetaPoleUnit 1) ∈ Complex.slitPlane := by
    rw [zetaPoleUnit_one]
    simp [Complex.mem_slitPlane_iff]
  have hlogOn : DifferentiableOn ℂ Complex.log Complex.slitPlane :=
    fun z hz => (Complex.differentiableAt_log hz).differentiableWithinAt
  have hlog : AnalyticAt ℂ Complex.log (zetaPoleUnit 1) :=
    hlogOn.analyticOnNhd Complex.isOpen_slitPlane _ hslit
  exact hlog.comp (analyticAt_zetaPoleUnit 1)

/-- The regular part of the real Euler logarithm at the pole. -/
def eulerLogRegular (β : ℝ) : ℝ := (zetaPoleLog (β : ℂ)).re

theorem analyticAt_eulerLogRegular : AnalyticAt ℝ eulerLogRegular 1 := by
  have h1 : AnalyticAt ℝ (fun β : ℝ => (β : ℂ)) 1 :=
    Complex.ofRealCLM.analyticAt 1
  have h2 : AnalyticAt ℝ zetaPoleLog ((1 : ℝ) : ℂ) := by
    have := analyticAt_zetaPoleLog
    rw [show (((1 : ℝ) : ℂ)) = (1 : ℂ) by norm_num]
    exact this.restrictScalars
  exact (Complex.reCLM.analyticAt _).comp (h2.comp h1)

theorem eulerLogRegular_eq {β : ℝ} (hβ : 1 < β) :
    eulerLogRegular β = Real.log (β - 1) + eulerLogMoment β := by
  have hne : ((β : ℂ)) ≠ 1 := by
    intro h
    have : (β : ℝ) = 1 := by exact_mod_cast h
    linarith
  have hz := riemannZeta_ofReal_eq_exp_eulerLogMoment hβ
  have hval : zetaPoleUnit (β : ℂ)
      = (((β - 1) * Real.exp (eulerLogMoment β) : ℝ) : ℂ) := by
    rw [zetaPoleUnit_eq_of_ne hne, hz]
    push_cast
    ring
  have hpos : 0 < (β - 1) * Real.exp (eulerLogMoment β) := by
    have : 0 < β - 1 := by linarith
    positivity
  rw [eulerLogRegular, zetaPoleLog, Complex.log_re, hval, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hpos, Real.log_mul (by linarith) (Real.exp_ne_zero _),
    Real.log_exp]

/-! ## The singular part of the Euler moments at the pole -/

/-- The `j`-th Euler prime-power moment as a function of the inverse temperature. -/
def eulerMoment (j : ℕ) (β : ℝ) : ℝ :=
  fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy j

theorem eulerMoment_zero_eq (β : ℝ) : eulerMoment 0 β = eulerLogMoment β := rfl

theorem hasDerivAt_eulerMoment' (j : ℕ) {β : ℝ} (hβ : 1 < β) :
    HasDerivAt (eulerMoment j) (-(eulerMoment (j + 1) β)) β :=
  hasDerivAt_eulerMoment j hβ

theorem hasDerivAt_inv_pow_succ_sub_one {t : ℝ} (ht : t - 1 ≠ 0) (n : ℕ) :
    HasDerivAt (fun r : ℝ => ((r - 1) ^ (n + 1))⁻¹)
      (-((n + 1 : ℝ) * ((t - 1) ^ (n + 2))⁻¹)) t := by
  have hf : HasDerivAt (fun r : ℝ => (r - 1) ^ (n + 1)) ((n + 1 : ℝ) * (t - 1) ^ n) t := by
    simpa using ((hasDerivAt_id t).sub_const (1 : ℝ)).fun_pow (n + 1)
  have hne : ((t - 1) ^ (n + 1)) ≠ 0 := pow_ne_zero _ ht
  refine (hf.inv hne).congr_deriv ?_
  field_simp
  ring

/-- Regular derivatives of the pole-regularized Euler logarithm. -/
def eulerLogRegularDeriv : ℕ → ℝ → ℝ
  | 0 => eulerLogRegular
  | (n + 1) => deriv (eulerLogRegularDeriv n)

theorem analyticAt_eulerLogRegularDeriv (n : ℕ) {t : ℝ}
    (h : AnalyticAt ℝ eulerLogRegular t) : AnalyticAt ℝ (eulerLogRegularDeriv n) t := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.deriv

theorem hasDerivAt_eulerLogRegularDeriv (n : ℕ) {t : ℝ}
    (h : AnalyticAt ℝ eulerLogRegular t) :
    HasDerivAt (eulerLogRegularDeriv n) (eulerLogRegularDeriv (n + 1) t) t :=
  ((analyticAt_eulerLogRegularDeriv n h).differentiableAt).hasDerivAt

/-- A right window at the pole on which the regular part is analytic. -/
theorem exists_poincare_window :
    ∃ ε > 0, ∀ t ∈ Set.Ioo (1 : ℝ) (1 + ε), AnalyticAt ℝ eulerLogRegular t := by
  have h := analyticAt_eulerLogRegular.eventually_analyticAt
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨ε, hε, hball⟩ := h
  refine ⟨ε, hε, fun t ht => hball ?_⟩
  rw [Real.dist_eq, abs_of_pos (by linarith [ht.1])]
  linarith [ht.2]

section Window

variable {ε : ℝ}

theorem eulerMoment_one_eq_of_window 
    (hA : ∀ t ∈ Set.Ioo (1 : ℝ) (1 + ε), AnalyticAt ℝ eulerLogRegular t)
    {t : ℝ} (ht : t ∈ Set.Ioo (1 : ℝ) (1 + ε)) :
    eulerMoment 1 t = ((t - 1) ^ 1)⁻¹ - eulerLogRegularDeriv 1 t := by
  have hopen : Set.Ioo (1 : ℝ) (1 + ε) ∈ nhds t := (isOpen_Ioo).mem_nhds ht
  have ht1 : (1 : ℝ) < t := ht.1
  have hne : t - 1 ≠ 0 := by linarith
  have h1 : HasDerivAt (eulerMoment 0) (-(eulerMoment 1 t)) t :=
    hasDerivAt_eulerMoment' 0 ht1
  have heq : eulerMoment 0 =ᶠ[nhds t] fun r => eulerLogRegular r - Real.log (r - 1) := by
    filter_upwards [hopen] with r hr
    rw [eulerMoment_zero_eq, eulerLogRegular_eq hr.1]
    ring
  have hlog : HasDerivAt (fun r : ℝ => Real.log (r - 1)) ((t - 1)⁻¹) t := by
    simpa using (((hasDerivAt_id t).sub_const (1 : ℝ)).log hne)
  have h2 : HasDerivAt (fun r => eulerLogRegular r - Real.log (r - 1))
      (eulerLogRegularDeriv 1 t - (t - 1)⁻¹) t :=
    (hasDerivAt_eulerLogRegularDeriv 0 (hA t ht)).fun_sub hlog
  have := (h1.congr_of_eventuallyEq heq.symm).unique h2
  simp only [pow_one]
  linarith [this]

theorem eulerMoment_two_eq_of_window 
    (hA : ∀ t ∈ Set.Ioo (1 : ℝ) (1 + ε), AnalyticAt ℝ eulerLogRegular t)
    {t : ℝ} (ht : t ∈ Set.Ioo (1 : ℝ) (1 + ε)) :
    eulerMoment 2 t = ((t - 1) ^ 2)⁻¹ + eulerLogRegularDeriv 2 t := by
  have hopen : Set.Ioo (1 : ℝ) (1 + ε) ∈ nhds t := (isOpen_Ioo).mem_nhds ht
  have ht1 : (1 : ℝ) < t := ht.1
  have hne : t - 1 ≠ 0 := by linarith
  have h1 : HasDerivAt (eulerMoment 1) (-(eulerMoment 2 t)) t :=
    hasDerivAt_eulerMoment' 1 ht1
  have heq : eulerMoment 1 =ᶠ[nhds t]
      fun r => ((r - 1) ^ 1)⁻¹ - eulerLogRegularDeriv 1 r := by
    filter_upwards [hopen] with r hr
    exact eulerMoment_one_eq_of_window hA hr
  have h2 : HasDerivAt (fun r : ℝ => ((r - 1) ^ 1)⁻¹ - eulerLogRegularDeriv 1 r)
      (-(((t - 1) ^ 2)⁻¹) - eulerLogRegularDeriv 2 t) t := by
    refine ((hasDerivAt_inv_pow_succ_sub_one hne 0).fun_sub
      (hasDerivAt_eulerLogRegularDeriv 1 (hA t ht))).congr_deriv ?_
    norm_num
  have := (h1.congr_of_eventuallyEq heq.symm).unique h2
  linarith [this]

theorem eulerMoment_three_eq_of_window 
    (hA : ∀ t ∈ Set.Ioo (1 : ℝ) (1 + ε), AnalyticAt ℝ eulerLogRegular t)
    {t : ℝ} (ht : t ∈ Set.Ioo (1 : ℝ) (1 + ε)) :
    eulerMoment 3 t = 2 * ((t - 1) ^ 3)⁻¹ - eulerLogRegularDeriv 3 t := by
  have hopen : Set.Ioo (1 : ℝ) (1 + ε) ∈ nhds t := (isOpen_Ioo).mem_nhds ht
  have ht1 : (1 : ℝ) < t := ht.1
  have hne : t - 1 ≠ 0 := by linarith
  have h1 : HasDerivAt (eulerMoment 2) (-(eulerMoment 3 t)) t :=
    hasDerivAt_eulerMoment' 2 ht1
  have heq : eulerMoment 2 =ᶠ[nhds t]
      fun r => ((r - 1) ^ 2)⁻¹ + eulerLogRegularDeriv 2 r := by
    filter_upwards [hopen] with r hr
    exact eulerMoment_two_eq_of_window hA hr
  have h2 : HasDerivAt (fun r : ℝ => ((r - 1) ^ 2)⁻¹ + eulerLogRegularDeriv 2 r)
      (-(2 * ((t - 1) ^ 3)⁻¹) + eulerLogRegularDeriv 3 t) t := by
    refine ((hasDerivAt_inv_pow_succ_sub_one hne 1).fun_add
      (hasDerivAt_eulerLogRegularDeriv 2 (hA t ht))).congr_deriv ?_
    norm_num
  have := (h1.congr_of_eventuallyEq heq.symm).unique h2
  linarith [this]

theorem eulerMoment_four_eq_of_window 
    (hA : ∀ t ∈ Set.Ioo (1 : ℝ) (1 + ε), AnalyticAt ℝ eulerLogRegular t)
    {t : ℝ} (ht : t ∈ Set.Ioo (1 : ℝ) (1 + ε)) :
    eulerMoment 4 t = 6 * ((t - 1) ^ 4)⁻¹ + eulerLogRegularDeriv 4 t := by
  have hopen : Set.Ioo (1 : ℝ) (1 + ε) ∈ nhds t := (isOpen_Ioo).mem_nhds ht
  have ht1 : (1 : ℝ) < t := ht.1
  have hne : t - 1 ≠ 0 := by linarith
  have h1 : HasDerivAt (eulerMoment 3) (-(eulerMoment 4 t)) t :=
    hasDerivAt_eulerMoment' 3 ht1
  have heq : eulerMoment 3 =ᶠ[nhds t]
      fun r => 2 * ((r - 1) ^ 3)⁻¹ - eulerLogRegularDeriv 3 r := by
    filter_upwards [hopen] with r hr
    exact eulerMoment_three_eq_of_window hA hr
  have h2 : HasDerivAt (fun r : ℝ => 2 * ((r - 1) ^ 3)⁻¹ - eulerLogRegularDeriv 3 r)
      (-(6 * ((t - 1) ^ 4)⁻¹) - eulerLogRegularDeriv 4 t) t := by
    refine ((HasDerivAt.const_mul (2 : ℝ)
      (hasDerivAt_inv_pow_succ_sub_one hne 2)).fun_sub
      (hasDerivAt_eulerLogRegularDeriv 3 (hA t ht))).congr_deriv ?_
    norm_num
    ring
  have := (h1.congr_of_eventuallyEq heq.symm).unique h2
  linarith [this]

end Window

/-! ## Identification with the conformal scalar curvature -/

theorem eulerFisherScalarCurvature_eq_moments (β : ℝ) :
    eulerFisherScalarCurvature β =
      -(eulerMoment 2 β * eulerMoment 4 β - eulerMoment 3 β ^ 2) / eulerMoment 2 β ^ 3 :=
  rfl

theorem eulerMoment_two_pos {β : ℝ} (hβ : 1 < β) : 0 < eulerMoment 2 β :=
  eulerPrimePowerMoment_two_pos β hβ

/-- **The Euler Fisher curvature expression is the scalar curvature of the conformal
temperature–clock metric.**  For the conformal surface metric `M₂(β) (dβ² + dτ²)` the Liouville
scalar curvature `-Δ(log M₂)/M₂` equals `-(M₂M₄ - M₃²)/M₂³`. -/
theorem conformalScalarCurvature_eulerMoment_two {β : ℝ} (hβ : 1 < β) :
    conformalScalarCurvature (eulerMoment 2) β = eulerFisherScalarCurvature β := by
  have hIoi : Set.Ioi (1 : ℝ) ∈ nhds β := (isOpen_Ioi).mem_nhds hβ
  have hpos : ∀ᶠ t in nhds β, 0 < eulerMoment 2 t := by
    filter_upwards [hIoi] with t ht
    exact eulerMoment_two_pos ht
  have hG : ∀ᶠ t in nhds β, HasDerivAt (eulerMoment 2) (-(eulerMoment 3 t)) t := by
    filter_upwards [hIoi] with t ht
    exact hasDerivAt_eulerMoment' 2 ht
  have hG' : HasDerivAt (fun t => -(eulerMoment 3 t)) (eulerMoment 4 β) β := by
    have := (hasDerivAt_eulerMoment' 3 hβ).fun_neg
    simpa using this
  rw [conformalScalarCurvature_eq_of_hasDerivAt hpos hG hG',
    eulerFisherScalarCurvature_eq_moments]
  ring

/-! ## The Poincaré boundary value -/

/-- Numerator of the curvature after clearing the pole. -/
def poincareNum (t : ℝ) : ℝ :=
  (1 + (t - 1) ^ 2 * eulerLogRegularDeriv 2 t) *
      (6 + (t - 1) ^ 4 * eulerLogRegularDeriv 4 t) -
    (2 - (t - 1) ^ 3 * eulerLogRegularDeriv 3 t) ^ 2

/-- Denominator of the curvature after clearing the pole. -/
def poincareDen (t : ℝ) : ℝ := (1 + (t - 1) ^ 2 * eulerLogRegularDeriv 2 t) ^ 3

theorem eulerFisherScalarCurvature_eq_poincare_ratio {ε : ℝ}
    (hA : ∀ t ∈ Set.Ioo (1 : ℝ) (1 + ε), AnalyticAt ℝ eulerLogRegular t)
    {t : ℝ} (ht : t ∈ Set.Ioo (1 : ℝ) (1 + ε)) :
    eulerFisherScalarCurvature t = -poincareNum t / poincareDen t := by
  have ht1 : (1 : ℝ) < t := ht.1
  have hu : t - 1 ≠ 0 := by intro h; apply absurd (sub_eq_zero.mp h); intro h'; linarith
  have hm2 := eulerMoment_two_eq_of_window hA ht
  have hm3 := eulerMoment_three_eq_of_window hA ht
  have hm4 := eulerMoment_four_eq_of_window hA ht
  have hM2pos : 0 < eulerMoment 2 t := eulerMoment_two_pos ht1
  have hsq : (0 : ℝ) < (t - 1) ^ 2 := by positivity
  have hfac : eulerMoment 2 t * (t - 1) ^ 2 = 1 + (t - 1) ^ 2 * eulerLogRegularDeriv 2 t := by
    rw [hm2]
    field_simp
  have hDfac : 0 < 1 + (t - 1) ^ 2 * eulerLogRegularDeriv 2 t := by
    rw [← hfac]
    exact mul_pos hM2pos hsq
  have hDne : poincareDen t ≠ 0 := by
    rw [poincareDen]
    positivity
  rw [eulerFisherScalarCurvature_eq_moments, hm2, hm3, hm4, poincareNum, poincareDen]
  have hM2ne : ((t - 1) ^ 2)⁻¹ + eulerLogRegularDeriv 2 t ≠ 0 := by
    rw [← hm2]
    exact hM2pos.ne'
  field_simp

theorem tendsto_poincareNum : Filter.Tendsto poincareNum (nhds 1) (nhds 2) := by
  have hsub : Filter.Tendsto (fun t : ℝ => t - 1) (nhds 1) (nhds 0) := by
    have h := (continuous_sub_right (1 : ℝ)).continuousAt (x := (1 : ℝ))
    simpa [ContinuousAt] using h
  have hc2 := (analyticAt_eulerLogRegularDeriv 2 analyticAt_eulerLogRegular).continuousAt
  have hc3 := (analyticAt_eulerLogRegularDeriv 3 analyticAt_eulerLogRegular).continuousAt
  have hc4 := (analyticAt_eulerLogRegularDeriv 4 analyticAt_eulerLogRegular).continuousAt
  have h1 : Filter.Tendsto
      (fun t : ℝ => 1 + (t - 1) ^ 2 * eulerLogRegularDeriv 2 t) (nhds 1) (nhds 1) := by
    simpa using tendsto_const_nhds.add ((hsub.pow 2).mul hc2)
  have h4 : Filter.Tendsto
      (fun t : ℝ => 6 + (t - 1) ^ 4 * eulerLogRegularDeriv 4 t) (nhds 1) (nhds 6) := by
    simpa using tendsto_const_nhds.add ((hsub.pow 4).mul hc4)
  have h3 : Filter.Tendsto
      (fun t : ℝ => 2 - (t - 1) ^ 3 * eulerLogRegularDeriv 3 t) (nhds 1) (nhds 2) := by
    simpa using tendsto_const_nhds.sub ((hsub.pow 3).mul hc3)
  have h := (h1.mul h4).sub (h3.pow 2)
  norm_num at h
  exact h

theorem tendsto_poincareDen : Filter.Tendsto poincareDen (nhds 1) (nhds 1) := by
  have hsub : Filter.Tendsto (fun t : ℝ => t - 1) (nhds 1) (nhds 0) := by
    have h := (continuous_sub_right (1 : ℝ)).continuousAt (x := (1 : ℝ))
    simpa [ContinuousAt] using h
  have hc2 := (analyticAt_eulerLogRegularDeriv 2 analyticAt_eulerLogRegular).continuousAt
  have h1 : Filter.Tendsto
      (fun t : ℝ => 1 + (t - 1) ^ 2 * eulerLogRegularDeriv 2 t) (nhds 1) (nhds 1) := by
    simpa using tendsto_const_nhds.add ((hsub.pow 2).mul hc2)
  have h := h1.pow 3
  norm_num at h
  exact h

/-- **Poincaré boundary value.**  The Euler Fisher scalar curvature tends to `-2` as the inverse
temperature approaches the pole from the right; the temperature–clock superspace is
asymptotically hyperbolic with Gaussian curvature `-1` at the critical wall. -/
theorem tendsto_eulerFisherScalarCurvature_nhdsGT_one :
    Filter.Tendsto eulerFisherScalarCurvature (nhdsWithin 1 (Set.Ioi 1)) (nhds (-2)) := by
  obtain ⟨ε, hε, hA⟩ := exists_poincare_window
  have hwin : Set.Ioo (1 : ℝ) (1 + ε) ∈ nhdsWithin 1 (Set.Ioi 1) :=
    Ioo_mem_nhdsGT (by linarith)
  have hratio : Filter.Tendsto (fun t => -poincareNum t / poincareDen t) (nhds 1) (nhds (-2)) := by
    have h := Filter.Tendsto.div (Filter.Tendsto.neg tendsto_poincareNum)
      tendsto_poincareDen one_ne_zero
    rw [div_one] at h
    exact h
  refine Filter.Tendsto.congr' ?_ (hratio.mono_left nhdsWithin_le_nhds)
  filter_upwards [hwin] with t ht
  exact (eulerFisherScalarCurvature_eq_poincare_ratio hA ht).symm

/-! ## Capstone -/

theorem deriv_eulerLogMoment {β : ℝ} (hβ : 1 < β) :
    deriv eulerLogMoment β = -(eulerMoment 1 β) :=
  (hasDerivAt_eulerMoment' 0 hβ).deriv

/-- The Fisher conformal scale factor is the second derivative of the Euler logarithm of zeta. -/
theorem deriv_deriv_eulerLogMoment {β : ℝ} (hβ : 1 < β) :
    deriv (deriv eulerLogMoment) β = eulerMoment 2 β := by
  have hIoi : Set.Ioi (1 : ℝ) ∈ nhds β := (isOpen_Ioi).mem_nhds hβ
  have heq : deriv eulerLogMoment =ᶠ[nhds β] fun t => -(eulerMoment 1 t) := by
    filter_upwards [hIoi] with t ht
    exact deriv_eulerLogMoment ht
  rw [Filter.EventuallyEq.deriv_eq heq]
  have h : HasDerivAt (fun t => -(eulerMoment 1 t)) (eulerMoment 2 β) β := by
    simpa using (hasDerivAt_eulerMoment' 1 hβ).fun_neg
  exact h.deriv

/-- **The zeta Fisher superspace has globally negative curvature and a Poincare critical
boundary.**  On `1 < beta` the Liouville scalar curvature of the conformal temperature-clock
metric `M_2(beta) (dbeta^2 + dtau^2)` equals the Euler moment expression
`-(M_2 M_4 - M_3^2)/M_2^3`, which is strictly negative everywhere and converges to `-2` at the
critical wall `beta = 1`. -/
theorem zeta_fisher_superspace_negative_curvature_poincare_boundary :
    (∀ β : ℝ, 1 < β →
        deriv (deriv eulerLogMoment) β = eulerMoment 2 β ∧
        conformalScalarCurvature (eulerMoment 2) β = eulerFisherScalarCurvature β ∧
        eulerFisherScalarCurvature β < 0) ∧
      Filter.Tendsto eulerFisherScalarCurvature (nhdsWithin 1 (Set.Ioi 1)) (nhds (-2)) :=
  ⟨fun β hβ => ⟨deriv_deriv_eulerLogMoment hβ, conformalScalarCurvature_eulerMoment_two hβ,
      eulerFisherScalarCurvature_neg β hβ⟩,
    tendsto_eulerFisherScalarCurvature_nhdsGT_one⟩

end

end RHTower
