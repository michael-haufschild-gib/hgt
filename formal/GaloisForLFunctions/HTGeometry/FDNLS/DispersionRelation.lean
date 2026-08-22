import GaloisForLFunctions.HTGeometry.FDNLS.CouplingDecay

/-!
# The exact dispersion relation of the fractional discrete NLS lattice

Zhong--Malomed--Yan, arXiv:2407.12441, Section II D, equations (32)--(35) and (38)--(39).

The linearized quasi-Riesz lattice supports plane waves `v_n ∼ exp(i k n)`, whose frequency is the
lattice sum `ω(k) = C ∑_{ℓ ∈ ℤ} D_ℓ^{(α)} cos(ℓ k)` of equation (32).  The paper's central
analytical claim is that this sum is *exactly* `C |k|^α` for every Lévy index — equation (33).

Mathematically the claim is Fourier inversion on the circle `ℝ/2πℤ`: the coupling coefficients
`D_ℓ^{(α)}` of equation (10) are by construction the Fourier cosine coefficients of the symbol
`k ↦ |k|^α`, and that symbol is continuous on the circle (it matches at the seam `±π`), so the
absolute summability established in `CouplingDecay` upgrades the `L²` theory to pointwise
summation.

## Main results

* `rieszSymbolCircle` — the symbol `|k|^α` as a continuous function on `AddCircle (2π)`.
* `fourierCoeff_rieszSymbolCircle` — its `n`-th Fourier coefficient is exactly `D_n^{(α)}`.
* `hasSum_quasiRieszCoupling_cos` — **equation (33)**:
  `∑_{ℓ ∈ ℤ} D_ℓ^{(α)} cos(ℓ k) = |k|^α` for every `k ∈ [-π, π]`.
* `fdnlsDispersion`, `fdnlsDispersion_eq` — the frequency `ω(k) = C|k|^α`.
* `fdnlsDispersion_zero`, `fdnlsDispersion_pi` — **equations (34) and (35)**.
* `fdnlsDispersion_mem_band` — **equation (38)**: the propagation band is `0 ≤ ω ≤ C π^α`.
* `hasDerivAt_fdnlsDispersion`, `fdnlsGroupVelocity_tendsto_atTop` — **equation (39)** and the
  group-velocity singularity at `k → 0` for `α < 1`.
-/

open MeasureTheory Set Filter Topology intervalIntegral

namespace GaloisForLFunctions.HTGeometry.FDNLS

/-- The circle `ℝ/2πℤ` carries a positive period. -/
instance fdnlsFactTwoPi : Fact ((0:ℝ) < 2 * Real.pi) := ⟨by positivity⟩

/-! ## The symbol on the circle -/

/-- The quasi-Riesz symbol `k ↦ |k|^α`, viewed as a complex-valued function of a real variable. -/
noncomputable def rieszSymbol (α : ℝ) : ℝ → ℂ := fun x => ((|x| ^ α : ℝ) : ℂ)

theorem continuous_rieszSymbol {α : ℝ} (hα : 0 ≤ α) : Continuous (rieszSymbol α) :=
  Complex.continuous_ofReal.comp ((continuous_rpow_const hα).comp continuous_abs)

/-- The symbol matches at the two ends of a period: this is what makes it continuous on the
circle. -/
theorem rieszSymbol_endpoints (α : ℝ) :
    rieszSymbol α (-Real.pi) = rieszSymbol α (-Real.pi + 2 * Real.pi) := by
  have h : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [h]
  simp [rieszSymbol, abs_of_nonneg Real.pi_pos.le]

/-- The quasi-Riesz symbol as a function on the circle `ℝ/2πℤ`. -/
noncomputable def rieszSymbolCircle (α : ℝ) : AddCircle (2 * Real.pi) → ℂ :=
  AddCircle.liftIoc (2 * Real.pi) (-Real.pi) (rieszSymbol α)

theorem continuous_rieszSymbolCircle {α : ℝ} (hα : 0 ≤ α) : Continuous (rieszSymbolCircle α) :=
  AddCircle.liftIoc_continuous (rieszSymbol_endpoints α) (continuous_rieszSymbol hα).continuousOn

/-- On the *closed* fundamental interval the circle symbol is the honest `|x|^α`; at the left
endpoint this uses the identification `-π ≡ π`. -/
theorem rieszSymbolCircle_coe {α : ℝ} {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    rieszSymbolCircle α (x : AddCircle (2 * Real.pi)) = rieszSymbol α x := by
  have hend : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rcases eq_or_lt_of_le hx.1 with h | h
  · have hxv : x = -Real.pi := h.symm
    subst hxv
    have hper := AddCircle.coe_add_period (2 * Real.pi) (-Real.pi)
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at hper
    rw [← hper]
    simp only [rieszSymbolCircle]
    rw [AddCircle.liftIoc_coe_apply
      (show Real.pi ∈ Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) by
        rw [hend]; exact ⟨by linarith [Real.pi_pos], le_rfl⟩)]
    simp [rieszSymbol, abs_of_nonneg Real.pi_pos.le]
  · exact AddCircle.liftIoc_coe_apply (by rw [hend]; exact ⟨h, hx.2⟩)

/-! ## The Fourier coefficients of the symbol -/

/-- The lattice character in explicit exponential form. -/
theorem fourier_coe_exp (n : ℤ) (x : ℝ) :
    (fourier n : C(AddCircle (2 * Real.pi), ℂ)) (x : AddCircle (2 * Real.pi))
      = Complex.exp ((n : ℂ) * (x : ℂ) * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

theorem fourier_neg_coe (n : ℤ) (x : ℝ) :
    (fourier (-n) : C(AddCircle (2 * Real.pi), ℂ)) (x : AddCircle (2 * Real.pi))
      = Complex.exp (-((n : ℂ) * (x : ℂ) * Complex.I)) := by
  rw [fourier_coe_exp]
  congr 1
  push_cast
  ring

/-- The integrand of the Fourier coefficient. -/
noncomputable def rieszFourierIntegrand (α : ℝ) (n : ℤ) : ℝ → ℂ :=
  fun x => Complex.exp (-((n : ℂ) * (x : ℂ) * Complex.I)) * ((|x| ^ α : ℝ) : ℂ)

theorem continuous_rieszFourierIntegrand {α : ℝ} (hα : 0 ≤ α) (n : ℤ) :
    Continuous (rieszFourierIntegrand α n) := by
  refine Continuous.mul ?_ (continuous_rieszSymbol hα)
  exact Complex.continuous_exp.comp
    (((continuous_const.mul Complex.continuous_ofReal).mul continuous_const).neg)

/-- **The coupling coefficients are the Fourier coefficients of the symbol.**  This is the exact
content of equation (10): `D_n^{(α)}` is the `n`-th Fourier coefficient of `k ↦ |k|^α` on the
circle of circumference `2π`. -/
theorem fourierCoeff_rieszSymbolCircle {α : ℝ} (hα : 0 ≤ α) (n : ℤ) :
    fourierCoeff (rieszSymbolCircle α) n = ((quasiRieszCoupling α n : ℝ) : ℂ) := by
  have hpi := Real.pi_pos
  have hcont := continuous_rieszFourierIntegrand hα n
  show fourierCoeff (rieszSymbolCircle α) n
      = (((1 / Real.pi) * ∫ k in (0:ℝ)..Real.pi, Real.cos ((n : ℝ) * k) * k ^ α : ℝ) : ℂ)
  rw [fourierCoeff_eq_intervalIntegral (rieszSymbolCircle α) n (-Real.pi),
    show -Real.pi + 2 * Real.pi = Real.pi by ring]
  have hcongr : ∀ x ∈ uIcc (-Real.pi) Real.pi,
      (fourier (-n) : C(AddCircle (2 * Real.pi), ℂ)) (x : AddCircle (2 * Real.pi))
          • rieszSymbolCircle α (x : AddCircle (2 * Real.pi)) = rieszFourierIntegrand α n x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith : -Real.pi ≤ Real.pi)] at hx
    rw [rieszSymbolCircle_coe hx, fourier_neg_coe, smul_eq_mul]
    rfl
  rw [intervalIntegral.integral_congr hcongr]
  have hint1 : IntervalIntegrable (rieszFourierIntegrand α n) volume (-Real.pi) 0 :=
    hcont.intervalIntegrable _ _
  have hint2 : IntervalIntegrable (rieszFourierIntegrand α n) volume 0 Real.pi :=
    hcont.intervalIntegrable _ _
  have hadj : (∫ x in (-Real.pi)..(0:ℝ), rieszFourierIntegrand α n x)
      + (∫ x in (0:ℝ)..Real.pi, rieszFourierIntegrand α n x)
      = ∫ x in (-Real.pi)..Real.pi, rieszFourierIntegrand α n x :=
    intervalIntegral.integral_add_adjacent_intervals hint1 hint2
  have hneg : (∫ x in (0:ℝ)..Real.pi, rieszFourierIntegrand α n (-x))
      = ∫ x in (-Real.pi)..(0:ℝ), rieszFourierIntegrand α n x := by
    simp [intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := Real.pi)
      (rieszFourierIntegrand α n)]
  have hA : IntervalIntegrable (fun x : ℝ => rieszFourierIntegrand α n (-x)) volume 0 Real.pi :=
    (hcont.comp continuous_neg).intervalIntegrable _ _
  have hsum : (∫ x in (0:ℝ)..Real.pi,
        (rieszFourierIntegrand α n (-x) + rieszFourierIntegrand α n x))
      = (∫ x in (0:ℝ)..Real.pi, rieszFourierIntegrand α n (-x))
        + (∫ x in (0:ℝ)..Real.pi, rieszFourierIntegrand α n x) :=
    intervalIntegral.integral_add hA hint2
  have hcomb : (∫ x in (-Real.pi)..Real.pi, rieszFourierIntegrand α n x)
      = ∫ x in (0:ℝ)..Real.pi,
          (rieszFourierIntegrand α n (-x) + rieszFourierIntegrand α n x) := by
    rw [hsum, hneg, hadj]
  have hptw : ∀ x ∈ uIcc (0:ℝ) Real.pi,
      rieszFourierIntegrand α n (-x) + rieszFourierIntegrand α n x
        = ((2 * Real.cos ((n : ℝ) * x) * x ^ α : ℝ) : ℂ) := by
    intro x hx
    rw [Set.uIcc_of_le hpi.le] at hx
    have habs : |x| = x := abs_of_nonneg hx.1
    have habsneg : |(-x)| = x := by rw [abs_neg, habs]
    simp only [rieszFourierIntegrand, habs, habsneg]
    push_cast
    have e1 : (-((n : ℂ) * (-(x : ℂ)) * Complex.I)) = ((n : ℂ) * (x : ℂ)) * Complex.I := by ring
    have e2 : (-((n : ℂ) * (x : ℂ) * Complex.I)) = (-((n : ℂ) * (x : ℂ))) * Complex.I := by ring
    rw [e1, e2, Complex.two_cos]
    ring
  rw [hcomb, intervalIntegral.integral_congr hptw, intervalIntegral.integral_ofReal,
    show (fun k : ℝ => 2 * Real.cos ((n : ℝ) * k) * k ^ α)
      = fun k : ℝ => 2 * (Real.cos ((n : ℝ) * k) * k ^ α) by funext k; ring,
    intervalIntegral.integral_const_mul, Complex.real_smul]
  push_cast
  field_simp

/-- The coupling coefficient as a raw Fourier integral over one period. -/
theorem quasiRieszCoupling_eq_fourierIntegral {α : ℝ} (hα : 0 ≤ α) (n : ℤ) :
    ((quasiRieszCoupling α n : ℝ) : ℂ)
      = (1 / (2 * Real.pi) : ℝ) • ∫ x in (-Real.pi)..Real.pi, rieszFourierIntegrand α n x := by
  have hcongr : ∀ x ∈ uIcc (-Real.pi) Real.pi,
      (fourier (-n) : C(AddCircle (2 * Real.pi), ℂ)) (x : AddCircle (2 * Real.pi))
          • rieszSymbolCircle α (x : AddCircle (2 * Real.pi)) = rieszFourierIntegrand α n x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] at hx
    rw [rieszSymbolCircle_coe hx, fourier_neg_coe, smul_eq_mul]
    rfl
  rw [← fourierCoeff_rieszSymbolCircle hα n,
    fourierCoeff_eq_intervalIntegral (rieszSymbolCircle α) n (-Real.pi),
    show -Real.pi + 2 * Real.pi = Real.pi by ring, intervalIntegral.integral_congr hcongr]

/-! ## Pointwise Fourier inversion -/

/-- The symbol as a bundled continuous function on the circle. -/
noncomputable def rieszSymbolCM {α : ℝ} (hα : 0 ≤ α) : C(AddCircle (2 * Real.pi), ℂ) :=
  ⟨rieszSymbolCircle α, continuous_rieszSymbolCircle hα⟩

theorem summable_fourierCoeff_rieszSymbolCircle {α : ℝ} (hα0 : 0 < α) (hα2 : α ≤ 2) :
    Summable fun n : ℤ => fourierCoeff (rieszSymbolCircle α) n := by
  refine Summable.of_norm ?_
  refine (quasiRieszCoupling_summable_abs hα0 hα2).congr fun n => ?_
  rw [fourierCoeff_rieszSymbolCircle hα0.le n, Complex.norm_real, Real.norm_eq_abs]

/-- Complex-valued pointwise Fourier inversion for the quasi-Riesz symbol. -/
theorem hasSum_rieszSymbolCircle {α : ℝ} (hα0 : 0 < α) (hα2 : α ≤ 2)
    (x : AddCircle (2 * Real.pi)) :
    HasSum (fun n : ℤ => ((quasiRieszCoupling α n : ℝ) : ℂ)
        * (fourier n : C(AddCircle (2 * Real.pi), ℂ)) x) (rieszSymbolCircle α x) := by
  have hF : ⇑(rieszSymbolCM hα0.le) = rieszSymbolCircle α := rfl
  have hsum : Summable (fourierCoeff ⇑(rieszSymbolCM hα0.le)) := by
    rw [hF]; exact summable_fourierCoeff_rieszSymbolCircle hα0 hα2
  have h := has_pointwise_sum_fourier_series_of_summable hsum x
  rw [hF] at h
  refine h.congr_fun fun n => ?_
  rw [smul_eq_mul, fourierCoeff_rieszSymbolCircle hα0.le n]

/-- **Equation (33).**  The lattice dispersion sum of equation (32) is exactly `|k|^α` on the whole
Brillouin zone `[-π, π]`. -/
theorem hasSum_quasiRieszCoupling_cos {α : ℝ} (hα0 : 0 < α) (hα2 : α ≤ 2) {k : ℝ}
    (hk : k ∈ Icc (-Real.pi) Real.pi) :
    HasSum (fun ℓ : ℤ => quasiRieszCoupling α ℓ * Real.cos ((ℓ : ℝ) * k)) (|k| ^ α) := by
  have h := hasSum_rieszSymbolCircle hα0 hα2 (k : AddCircle (2 * Real.pi))
  rw [rieszSymbolCircle_coe hk] at h
  have hre := ((Complex.hasSum_iff _ _).mp h).1
  have hval : (rieszSymbol α k).re = |k| ^ α := by rw [rieszSymbol]; simp
  rw [hval] at hre
  refine hre.congr_fun fun n => ?_
  rw [fourier_coe_exp]
  have e : ((n : ℂ) * (k : ℂ) * Complex.I) = (((n : ℝ) * k : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [e, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- The `tsum` form of equation (33). -/
theorem tsum_quasiRieszCoupling_cos {α : ℝ} (hα0 : 0 < α) (hα2 : α ≤ 2) {k : ℝ}
    (hk : k ∈ Icc (-Real.pi) Real.pi) :
    ∑' ℓ : ℤ, quasiRieszCoupling α ℓ * Real.cos ((ℓ : ℝ) * k) = |k| ^ α :=
  (hasSum_quasiRieszCoupling_cos hα0 hα2 hk).tsum_eq

/-! ## The dispersion relation and the propagation band -/

/-- **Equation (32).**  The frequency of the lattice wave of wavenumber `k` at coupling `C`. -/
noncomputable def fdnlsDispersion (C α : ℝ) (k : ℝ) : ℝ :=
  C * ∑' ℓ : ℤ, quasiRieszCoupling α ℓ * Real.cos ((ℓ : ℝ) * k)

/-- **Equation (33).**  `ω(k) = C |k|^α`. -/
theorem fdnlsDispersion_eq {C α : ℝ} (hα0 : 0 < α) (hα2 : α ≤ 2) {k : ℝ}
    (hk : k ∈ Icc (-Real.pi) Real.pi) : fdnlsDispersion C α k = C * |k| ^ α := by
  rw [fdnlsDispersion, tsum_quasiRieszCoupling_cos hα0 hα2 hk]

/-- **Equation (34).**  The bottom of the band: `ω(0) = 0`, i.e. `∑_ℓ D_ℓ^{(α)} = 0`. -/
theorem fdnlsDispersion_zero {C α : ℝ} (hα0 : 0 < α) (hα2 : α ≤ 2) :
    fdnlsDispersion C α 0 = 0 := by
  rw [fdnlsDispersion_eq hα0 hα2 ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩]
  rw [abs_zero, Real.zero_rpow (ne_of_gt hα0), mul_zero]

/-- The vanishing of the total coupling, in raw form. -/
theorem tsum_quasiRieszCoupling_eq_zero {α : ℝ} (hα0 : 0 < α) (hα2 : α ≤ 2) :
    ∑' ℓ : ℤ, quasiRieszCoupling α ℓ = 0 := by
  have h := tsum_quasiRieszCoupling_cos hα0 hα2
    (k := 0) ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [abs_zero, Real.zero_rpow (ne_of_gt hα0)] at h
  rw [← h]
  exact tsum_congr fun ℓ => by simp

/-- **Equation (35).**  The top of the band: `ω(π) = C π^α`. -/
theorem fdnlsDispersion_pi {C α : ℝ} (hα0 : 0 < α) (hα2 : α ≤ 2) :
    fdnlsDispersion C α Real.pi = C * Real.pi ^ α := by
  rw [fdnlsDispersion_eq hα0 hα2 ⟨by linarith [Real.pi_pos], le_rfl⟩,
    abs_of_nonneg Real.pi_pos.le]

/-- The alternating coupling sum, in raw form: `∑_ℓ (-1)^ℓ D_ℓ^{(α)} = π^α`. -/
theorem tsum_alternating_quasiRieszCoupling {α : ℝ} (hα0 : 0 < α) (hα2 : α ≤ 2) :
    ∑' ℓ : ℤ, (-1 : ℝ) ^ ℓ * quasiRieszCoupling α ℓ = Real.pi ^ α := by
  have h := tsum_quasiRieszCoupling_cos hα0 hα2 (k := Real.pi) ⟨by linarith [Real.pi_pos], le_rfl⟩
  rw [abs_of_nonneg Real.pi_pos.le] at h
  rw [← h]
  exact tsum_congr fun ℓ => by
    rw [Real.cos_int_mul_pi]
    ring

/-- **Equation (38).**  The propagation band of the linear lattice waves is `0 ≤ ω ≤ C π^α`. -/
theorem fdnlsDispersion_mem_band {C α : ℝ} (hC : 0 < C) (hα0 : 0 < α) (hα2 : α ≤ 2) {k : ℝ}
    (hk : k ∈ Icc (-Real.pi) Real.pi) :
    fdnlsDispersion C α k ∈ Icc (0:ℝ) (C * Real.pi ^ α) := by
  rw [fdnlsDispersion_eq hα0 hα2 hk]
  have habs : |k| ≤ Real.pi := abs_le.mpr ⟨hk.1, hk.2⟩
  refine ⟨by positivity, ?_⟩
  have : |k| ^ α ≤ Real.pi ^ α := Real.rpow_le_rpow (abs_nonneg k) habs hα0.le
  nlinarith

/-! ## The group velocity -/

/-- **Equation (39).**  The group velocity `dω/dk = C α |k|^{α-1} sgn k`, away from `k = 0`. -/
theorem hasDerivAt_fdnlsDispersion {C α : ℝ} {k : ℝ} (hk : 0 < k) :
    HasDerivAt (fun t : ℝ => C * t ^ α) (C * α * |k| ^ (α - 1) * (1 : ℝ)) k := by
  have h := (Real.hasDerivAt_rpow_const (x := k) (p := α) (Or.inl (ne_of_gt hk))).const_mul C
  refine h.congr_deriv ?_
  rw [abs_of_pos hk]
  ring

/-- The group velocity blows up at the bottom of the band when `α < 1`: the lattice waves have no
finite propagation speed there, which is the decay mechanism the paper records after
equation (39). -/
theorem fdnlsGroupVelocity_tendsto_atTop {C α : ℝ} (hC : 0 < C) (hα0 : 0 < α) (hα1 : α < 1) :
    Tendsto (fun k : ℝ => C * α * k ^ (α - 1)) (𝓝[>] (0:ℝ)) atTop := by
  have hrpow : Tendsto (fun k : ℝ => k ^ (α - 1)) (𝓝[>] (0:ℝ)) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (by linarith)
  exact Filter.Tendsto.const_mul_atTop (by positivity) hrpow

end GaloisForLFunctions.HTGeometry.FDNLS
