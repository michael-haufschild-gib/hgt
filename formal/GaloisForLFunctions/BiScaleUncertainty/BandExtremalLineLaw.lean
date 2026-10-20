import GaloisForLFunctions.BiScaleUncertainty.BandSlopeZeroEnergyLaw
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.RHTower.SeamStripRamification

/-!
# The leading constant of the band reads the extremal zeros

The exponential rate of the mean-square band `∫_0^L Ẽ²` is the zero width
(`xiZeroHalfPlaneBound_iff_meanSquareBandRate`). Its leading constant reads the zeros on the
extremal line, and at rate zero it is bounded below unconditionally.

* **Extremal-line law.** If `∫_0^L Ẽ² ≤ C e^{2βL} + K` with `0 < β < 1/2`, then for every finite
  family of distinct ordinates `γ_k`, with `n_k` the order of `(s − 1)ζ(s)` at
  `ρ_k = 1/2 + β + iγ_k`, `Σ_k n_k²/|ρ_k|² ≤ 2βC`.
* **The barrier is never sublinear.** No bound `∫_0^L Ẽ² ≤ c(1 + L) + K` holds for every
  `c > 0`: Hardy's theorem supplies a critical zero, and the band slope bounds its energy.
* **Off-line floor.** A zero of order `n` at `ρ`, `Re ρ = 1/2 + β`, `0 < β < 1/2`, makes
  `∫_0^L Ẽ² − C e^{2βL}` unbounded above for every `C` with `2βC < n²/|ρ|²`.

Mechanism: the tilted error `e^{-βt}Ẽ(t)` has Abel energy `σ ∫_0^∞ e^{-(2β+σ)t}Ẽ² ≤ C(2β+σ) + Kσ`
by integration by parts, and Abel coefficients `σ L(β + σ + iγ_k) → −n_k/ρ_k`; the Abel–Bessel
inequality concludes.
-/

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar

noncomputable section
set_option autoImplicit false

/-! ## Abel energy of an exponential band -/

/-- **Abel energy of an exponential band.** `∫_0^L Ẽ² ≤ C e^{2βL} + K` with `β > 0`, `C ≥ 0`
gives `σ ∫_0^∞ e^{-σt} (e^{-βt} Ẽ)² ≤ C(2β + σ) + Kσ`. -/
theorem abel_energy_of_exponential_band {β C K : ℝ} (hβ : 0 < β) (hC : 0 ≤ C)
    (hband : ∀ L : ℝ, 0 ≤ L →
      ∫ t in Icc 0 L, normalizedLogError t ^ 2 ≤ C * Real.exp (2 * β * L) + K)
    {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun t => Real.exp (-σ * t) * (Real.exp (-β * t) * normalizedLogError t) ^ 2)
        (Ioi 0) ∧
      σ * ∫ t in Ioi 0, Real.exp (-σ * t) * (Real.exp (-β * t) * normalizedLogError t) ^ 2 ≤
        C * (2 * β + σ) + K * σ := by
  set a := 2 * β + σ with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have htilt : (fun t => Real.exp (-σ * t) * (Real.exp (-β * t) * normalizedLogError t) ^ 2) =
      fun t => Real.exp (-a * t) * normalizedLogError t ^ 2 := by
    funext t
    rw [mul_pow, ← Real.exp_nat_mul, ← mul_assoc, ← Real.exp_add]
    congr 2; rw [ha]; push_cast; ring
  -- the primitive of `a e^{-aT}(C e^{2βT} + K)`
  have hd : ∀ (c : ℝ) (T : ℝ), HasDerivAt (fun T : ℝ => Real.exp (-c * T))
      (Real.exp (-c * T) * -c) T :=
    fun c T => by simpa using ((hasDerivAt_id T).const_mul (-c)).exp
  have hF : ∀ R : ℝ, a * ∫ T in (0 : ℝ)..R, Real.exp (-a * T) * (C * Real.exp (2 * β * T) + K) =
      C * (a / σ) + K - (C * (a / σ) * Real.exp (-σ * R) + K * Real.exp (-a * R)) := by
    intro R
    have hderiv : ∀ T : ℝ, HasDerivAt
        (fun T : ℝ => -(C / σ * Real.exp (-σ * T) + K / a * Real.exp (-a * T)))
        (Real.exp (-a * T) * (C * Real.exp (2 * β * T) + K)) T := by
      intro T
      have h1 := (((hd σ T).const_mul (C / σ)).add ((hd a T).const_mul (K / a))).neg
      refine h1.congr_deriv ?_
      have he : Real.exp (-a * T) * Real.exp (2 * β * T) = Real.exp (-σ * T) := by
        rw [← Real.exp_add]; congr 1; rw [ha]; ring
      rw [mul_add, show Real.exp (-a * T) * (C * Real.exp (2 * β * T)) = C * Real.exp (-σ * T) by
        rw [mul_left_comm, he]]
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun T _ => hderiv T)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp only [mul_zero, Real.exp_zero, mul_one]
    field_simp
    ring
  obtain ⟨hint, hle⟩ := abel_integral_le_of_primitive measurable_normalizedLogError
    integrableOn_normalizedLogError_sq (a := a) (M := C * (a / σ) + K) ha0
    (g := fun T => C * Real.exp (2 * β * T) + K) (by fun_prop) hband (fun R hR => by
      rw [hF R]
      have hER : Real.exp (-a * R) * (C * Real.exp (2 * β * R) + K) =
          C * Real.exp (-σ * R) + K * Real.exp (-a * R) := by
        have he : Real.exp (-a * R) * Real.exp (2 * β * R) = Real.exp (-σ * R) := by
          rw [← Real.exp_add]; congr 1; rw [ha]; ring
        rw [mul_add, mul_left_comm, he]; ring
      rw [hER]
      have hσa : 1 ≤ a / σ := by rw [le_div_iff₀ hσ, ha]; linarith
      have hexp := (Real.exp_pos (-σ * R)).le
      nlinarith [mul_nonneg hC hexp, mul_nonneg (mul_nonneg hC hexp) (sub_nonneg.mpr hσa)])
  rw [htilt]
  refine ⟨hint, ?_⟩
  calc σ * ∫ t in Ioi 0, Real.exp (-a * t) * normalizedLogError t ^ 2
      ≤ σ * (C * (a / σ) + K) := mul_le_mul_of_nonneg_left hle hσ.le
    _ = C * (2 * β + σ) + K * σ := by rw [ha]; field_simp

/-! ## The extremal-line law -/

/-- **Extremal-line law.** If `∫_0^L Ẽ² ≤ C e^{2βL} + K` with `0 < β < 1/2` and `C ≥ 0`, then
for every finite family of distinct ordinates `γ_k`, with `n_k` the order of `(s − 1)ζ(s)` at
`ρ_k = 1/2 + β + iγ_k`, `Σ_k n_k² / ((1/2 + β)² + γ_k²) ≤ 2βC`. -/
theorem sum_order_sq_div_le_of_exponential_band {β C K : ℝ} (hβ : 0 < β) (hβ1 : β < 1 / 2)
    (hC : 0 ≤ C)
    (hband : ∀ L : ℝ, 0 ≤ L →
      ∫ t in Icc 0 L, normalizedLogError t ^ 2 ≤ C * Real.exp (2 * β * L) + K)
    {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (hγ : Set.InjOn γ s) (n : ι → ℤ)
    (horder : ∀ k ∈ s, meromorphicOrderAt _root_.RHTower.zetaResidueUnit
      (((1 / 2 + β : ℝ) : ℂ) + γ k * I) = n k) :
    ∑ k ∈ s, (n k : ℝ) ^ 2 / ((1 / 2 + β) ^ 2 + γ k ^ 2) ≤ 2 * β * C := by
  have hrate : MeanSquareBandRate β := ⟨C + |K|, by positivity, fun L hL =>
    (hband L hL).trans (by
      have h1 : 1 ≤ Real.exp (2 * β * L) := Real.one_le_exp (by positivity)
      nlinarith [le_abs_self K, abs_nonneg K])⟩
  have hXi := xiZeroHalfPlaneBound_of_meanSquareBandRate hβ.le hβ1 hrate
  set F : ℝ → ℝ := fun t => Real.exp (-β * t) * normalizedLogError t with hF
  have hcoef : ∀ k ∈ s, Tendsto (fun σ : ℝ => (σ : ℂ) * ∫ t in Ioi (0 : ℝ),
      ((Real.exp (-σ * t) * F t : ℝ) : ℂ) * criticalCharacter (γ k) t)
      (𝓝[>] 0) (𝓝 (-(n k : ℂ) / (((1 / 2 + β : ℝ) : ℂ) + γ k * I))) := by
    intro k hk
    refine (tendsto_abel_laplace_of_halfPlane hβ.le hβ1 hXi (horder k hk)).congr fun σ => ?_
    rw [laplace_eq_integral_criticalCharacter]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hF]
    congr 2
    rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
  have h := sum_norm_sq_le_of_abel
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (-β * t)).measurable.mul
      measurable_normalizedLogError)
    (fun σ hσ => (abel_energy_of_exponential_band hβ hC hband hσ).1)
    (fun σ hσ => (abel_energy_of_exponential_band hβ hC hband hσ).2)
    (a := fun σ => C * (2 * β + σ) + K * σ) (A := 2 * β * C)
    (by
      have hσ : Tendsto (fun σ : ℝ => σ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have := ((tendsto_const_nhds (x := 2 * β)).add hσ).const_mul C |>.add (hσ.const_mul K)
      simpa [mul_comm] using this)
    s γ hγ _ hcoef
  refine le_of_eq_of_le (Finset.sum_congr rfl fun k _ => ?_) h
  have hnormρ : ‖(((1 / 2 + β : ℝ) : ℂ) + γ k * I)‖ ^ 2 = (1 / 2 + β) ^ 2 + γ k ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  rw [norm_div, norm_neg, div_pow, hnormρ, Complex.norm_intCast, sq_abs]

/-! ## Floors -/

/-- A zero of `(s − 1)ζ(s)` has a positive integer order. -/
theorem exists_order_of_zetaResidueUnit_eq_zero {ρ : ℂ}
    (h : _root_.RHTower.zetaResidueUnit ρ = 0) :
    ∃ n : ℤ, 1 ≤ n ∧ meromorphicOrderAt _root_.RHTower.zetaResidueUnit ρ = n := by
  have hA := RHTower.Sieve.zetaResidueUnit_analyticOnNhd_univ ρ (mem_univ _)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (RHTower.Sieve.zetaResidueUnit_order_ne_top ρ)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (hA.analyticOrderAt_eq_zero.mp (by rw [← hm]; rfl)) h
  refine ⟨m, by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0, ?_⟩
  rw [hA.meromorphicOrderAt_eq, ← hm]
  rfl

/-- Hardy's theorem gives a critical point of positive order. -/
theorem exists_critical_order :
    ∃ γ : ℝ, ∃ n : ℤ, 1 ≤ n ∧
      meromorphicOrderAt _root_.RHTower.zetaResidueUnit (1 / 2 + γ * I) = n := by
  obtain ⟨t, ht1, ht0⟩ := _root_.RHTower.exists_Xi_zero_gt 1
  have hxi : _root_.RHTower.xi (1 / 2 + (t : ℂ) * I) = 0 := by
    rw [_root_.RHTower.xi_eq_XiC_comp]
    have e : ((1 / 2 + (t : ℂ) * I - 1 / 2) * -I) = (t : ℂ) := by
      ring_nf; simp [Complex.I_sq]
    rw [e, _root_.RHTower.XiC_ofReal, ht0]
    simp
  have hre : (1 / 2 + (t : ℂ) * I).re = 1 / 2 := by simp
  have hζ : riemannZeta (1 / 2 + (t : ℂ) * I) = 0 :=
    (_root_.RHTower.xi_zero_iff_zeta_zero_of_mem_strip (by rw [hre]; norm_num)
      (by rw [hre]; norm_num)).mp hxi
  have hne : (1 / 2 + (t : ℂ) * I) ≠ 1 := fun h => by
    have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  have hu : _root_.RHTower.zetaResidueUnit (1 / 2 + (t : ℂ) * I) = 0 := by
    rw [_root_.RHTower.zetaResidueUnit, Function.update_of_ne hne, hζ, mul_zero]
  obtain ⟨n, hn, hord⟩ := exists_order_of_zetaResidueUnit_eq_zero hu
  exact ⟨t, n, hn, hord⟩

/-- **Linear floor.** At a critical point of order `n`, no band slope below `n²/|ρ|²` holds with
any offset: `∫_0^L Ẽ² > C(1 + L) + K` for some `L ≥ 0`. -/
theorem exists_band_gt_of_lt_zero_energy {γ : ℝ} {n : ℤ}
    (horder : meromorphicOrderAt _root_.RHTower.zetaResidueUnit (1 / 2 + γ * I) = n)
    {C K : ℝ} (hC : C * (1 / 4 + γ ^ 2) < (n : ℝ) ^ 2) :
    ∃ L : ℝ, 0 ≤ L ∧ C * (1 + L) + K < ∫ t in Icc 0 L, normalizedLogError t ^ 2 := by
  by_contra hno
  push Not at hno
  exact absurd (order_sq_le_of_band hno horder) (not_le.mpr hC)

/-- **The square-root barrier is never sublinear.** Unconditionally, no bound
`∫_0^L Ẽ² ≤ c(1 + L) + K` holds for every slope `c > 0`. -/
theorem not_forall_band_sublinear :
    ¬ ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ L : ℝ, 0 ≤ L →
      ∫ t in Icc 0 L, normalizedLogError t ^ 2 ≤ c * (1 + L) + K := by
  intro h
  obtain ⟨γ, n, hn, hord⟩ := exists_critical_order
  have hpos : (0 : ℝ) < 1 / 4 + γ ^ 2 := by positivity
  obtain ⟨K, hK⟩ := h (1 / (2 * (1 / 4 + γ ^ 2))) (by positivity)
  obtain ⟨L, hL, hgt⟩ := exists_band_gt_of_lt_zero_energy hord (K := K)
    (C := 1 / (2 * (1 / 4 + γ ^ 2))) (by
      have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ (by positivity)]
      nlinarith)
  exact absurd (hK L hL) (not_le.mpr hgt)

/-- **Off-line floor.** A zero of order `n` at `ρ = 1/2 + β + iγ`, `0 < β < 1/2`, makes
`∫_0^L Ẽ² > C e^{2βL} + K` for some `L ≥ 0` whenever `0 ≤ C` and `2βC|ρ|² < n²`. -/
theorem exists_exponential_band_gt_of_zero {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1 / 2)
    {γ : ℝ} {n : ℤ}
    (horder : meromorphicOrderAt _root_.RHTower.zetaResidueUnit
      (((1 / 2 + β : ℝ) : ℂ) + γ * I) = n)
    {C K : ℝ} (hC : 0 ≤ C) (hlt : 2 * β * C * ((1 / 2 + β) ^ 2 + γ ^ 2) < (n : ℝ) ^ 2) :
    ∃ L : ℝ, 0 ≤ L ∧ C * Real.exp (2 * β * L) + K < ∫ t in Icc 0 L, normalizedLogError t ^ 2 := by
  by_contra hno
  push Not at hno
  have h := sum_order_sq_div_le_of_exponential_band hβ hβ1 hC hno ({()} : Finset Unit)
    (fun _ => γ) (Set.injOn_of_subsingleton _ _) (fun _ => n) (fun _ _ => horder)
  simp only [Finset.sum_singleton] at h
  have hpos : (0 : ℝ) < (1 / 2 + β) ^ 2 + γ ^ 2 := by positivity
  rw [div_le_iff₀ hpos] at h
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
