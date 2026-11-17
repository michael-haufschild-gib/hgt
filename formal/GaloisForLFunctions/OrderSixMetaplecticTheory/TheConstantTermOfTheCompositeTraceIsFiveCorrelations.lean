import GaloisForLFunctions.OrderSixMetaplecticTheory.TheCompositeHeckeTraceIsAThetaSquareMultipleUpToABoundedRemainder
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheTwistedCosetsOfTheHeckeTraceReadTheDilateCorrelation

/-!
# The constant term of the composite trace is five correlations

For coprime primary primes `p, q` (`m = pq`) the five blocks of `Tr_mθ_s` (`heckeTrace_eq_blocks`) are series in
`z` after averaging over `O/m`:

* `Σ_{x mod m} S_c((z + 3x)/m) = N(m)S_{c(·m)}(z)` (`sum_crt_cuspCharacterSeries`, from the prime averages with a unit
  multiplier, `x = e_px₁ + e_qx₂`);
* `S_a(πz) = S_{a_π}(z)` with `a_π(kπ) = a(k)` and `a_π = 0` off `πO` (`cuspCharacterSeries_dilate`).

Hence (`integral_sourceTrace`) the constant term of the trace at height `v` is `N(m)|P|` times

`2Σ_h a_{hh}(h)a_{ll}(−m²h) + 2(p/q)₃Σ_l a_{hl}(lq²)a_{lh}(−lp²) + 2Σ_y(3y/q)₃ C^{ul}_y(0) + 2Σ_y(3y/p)₃ C^{lu}_y(0)
  + Σ_y (3y/m)₃ C^{ll}_y(0)`,

the `C_y` being the convolutions of the phased ratio and low amplitudes.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover

/-! ### Dilated and translated cusp series -/

theorem mul_right_injective_O {π : O} (hπ : π ≠ 0) : Function.Injective (fun k : O => k * π) :=
  fun _ _ h => mul_right_cancel₀ hπ h

/-- The coefficients of `S_a(πz)` as a series in `z`: `a(k)` at `kπ`, `0` off `πO`. -/
def dilateSeriesCoeff (π : O) (a : O → ℂ) : O → ℂ := Function.extend (fun k : O => k * π) a 0

theorem dilateSeriesCoeff_mul {π : O} (hπ : π ≠ 0) (a : O → ℂ) (k : O) : dilateSeriesCoeff π a (k * π) = a k :=
  (mul_right_injective_O hπ).extend_apply a 0 k

theorem dilateSeriesCoeff_off {π : O} (a : O → ℂ) (j : O) (hj : j ∉ Set.range (fun k : O => k * π)) :
    dilateSeriesCoeff π a j = 0 := by
  rw [dilateSeriesCoeff, Function.extend_apply' _ _ _ hj, Pi.zero_apply]

theorem summable_dilateSeriesCoeff {π : O} (hπ : π ≠ 0) {a : O → ℂ} (ha : Summable (fun h => ‖a h‖)) :
    Summable (fun j => ‖dilateSeriesCoeff π a j‖) := by
  refine ((mul_right_injective_O hπ).summable_iff (f := fun j => ‖dilateSeriesCoeff π a j‖)
    fun j hj => by rw [dilateSeriesCoeff_off a j hj, norm_zero]).mp ?_
  simpa only [Function.comp_def, dilateSeriesCoeff_mul hπ] using ha

/-- `S_a(πz) = S_{a_π}(z)`. -/
theorem cuspCharacterSeries_dilate {π : O} (hπ : π ≠ 0) (a : O → ℂ) (z : ℂ) :
    cuspCharacterSeries a (ringComplex π * z) = cuspCharacterSeries (dilateSeriesCoeff π a) z := by
  unfold cuspCharacterSeries
  have hsupp : Function.support (fun j => dilateSeriesCoeff π a j * tracePhase (cuspFrequency j * z)) ⊆
      Set.range (fun k : O => k * π) := fun j hj => by
    by_contra hn
    exact hj (by simp only [dilateSeriesCoeff_off a j hn, zero_mul])
  rw [← (mul_right_injective_O hπ).tsum_eq hsupp]
  refine tsum_congr fun k => ?_
  simp only [dilateSeriesCoeff_mul hπ, cuspFrequency_mul_right, mul_assoc]

/-- `C(0)` for a dilated left factor: `Σ_j a_π(j)d(−j) = Σ_k a(k)d(−kπ)`. -/
theorem cuspConv_dilate_zero {π : O} (hπ : π ≠ 0) (c d : O → ℂ) :
    cuspConv (dilateSeriesCoeff π c) d 0 = ∑' k : O, c k * d (-(k * π)) := by
  rw [cuspConv]
  have hsupp : Function.support (fun j => dilateSeriesCoeff π c j * d (0 - j)) ⊆
      Set.range (fun k : O => k * π) := fun j hj => by
    by_contra hn
    exact hj (by simp only [dilateSeriesCoeff_off c j hn, zero_mul])
  rw [← (mul_right_injective_O hπ).tsum_eq hsupp]
  refine tsum_congr fun k => ?_
  simp only [dilateSeriesCoeff_mul hπ, zero_sub]

/-- The coefficients `a(h)e(ξ_hc)` of `S_a(· + c)`. -/
def phasedCoeff (a : O → ℂ) (c : ℂ) : O → ℂ := fun h => a h * tracePhase (cuspFrequency h * c)

theorem summable_phasedCoeff {a : O → ℂ} (ha : Summable (fun h => ‖a h‖)) (c : ℂ) :
    Summable (fun h => ‖phasedCoeff a c h‖) := by
  simpa only [phasedCoeff, norm_mul, tracePhase_norm, mul_one] using ha

theorem cuspCharacterSeries_add_phase (a : O → ℂ) (c z : ℂ) :
    cuspCharacterSeries a (z + c) = cuspCharacterSeries (phasedCoeff a c) z :=
  cuspCharacterSeries_translate a c z

theorem sum_three_comm {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℂ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c :=
  calc ∑ a, ∑ b, ∑ c, f a b c = ∑ a, ∑ c, ∑ b, f a b c := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, f a b c := Finset.sum_comm

/-! ### Averaging over `O/p` with a unit multiplier -/

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- `Σ_x S_c((z + 3ux)/p) = N(p)S_{c(·p)}(z)` for `p ∤ u`. -/
theorem sum_cuspCharacterSeries_low_mul (u : O) (hu : ¬ P.p ∣ u) (c : O → ℂ) (hc : Summable (fun h => ‖c h‖))
    (z : ℂ) :
    ∑ x : P.Res, cuspCharacterSeries c ((z + 3 * ringComplex (u * P.lift x)) / ringComplex P.p) =
      (Fintype.card P.Res : ℂ) * cuspCharacterSeries (fun m => c (m * P.p)) z := by
  have hP := P.ringComplex_ne_zero
  have hu' : P.res u ≠ 0 := fun h => hu ((P.res_eq_zero_iff u).mp h)
  have hpt : ∀ x : P.Res, cuspCharacterSeries c ((z + 3 * ringComplex (u * P.lift x)) / ringComplex P.p) =
      cuspCharacterSeries c ((z + 3 * ringComplex (P.lift (P.res u * x))) / ringComplex P.p) := by
    intro x
    obtain ⟨j, hj⟩ : P.p ∣ u * P.lift x - P.lift (P.res u * x) := by
      rw [← P.res_eq_zero_iff, map_sub, map_mul, res_lift, res_lift, sub_self]
    have harg : (z + 3 * ringComplex (u * P.lift x)) / ringComplex P.p =
        (z + 3 * ringComplex (P.lift (P.res u * x))) / ringComplex P.p + 3 * ringComplex j := by
      rw [show u * P.lift x = P.lift (P.res u * x) + P.p * j by linear_combination hj, map_add, map_mul]
      field_simp
      ring
    rw [harg, cuspCharacterSeries_period]
  simp_rw [hpt]
  rw [Fintype.sum_bijective (fun x => P.res u * x)
    ⟨fun x y h => mul_left_cancel₀ hu' h, fun y => ⟨(P.res u)⁻¹ * y, by
      show P.res u * ((P.res u)⁻¹ * y) = y
      rw [← mul_assoc, mul_inv_cancel₀ hu', one_mul]⟩⟩
    (fun x => cuspCharacterSeries c ((z + 3 * ringComplex (P.lift (P.res u * x))) / ringComplex P.p))
    (fun y => cuspCharacterSeries c ((z + 3 * ringComplex (P.lift y)) / ringComplex P.p)) (fun x => rfl)]
  exact P.sum_cuspCharacterSeries_low c hc z

end PrimaryPrime

namespace PrimaryPair

variable (R : PrimaryPair)

theorem not_dvd_crtV : ¬ R.P.p ∣ R.crtV := fun h => by
  have h1 : R.P.p ∣ 1 := by
    rw [← R.crt_spec]
    exact dvd_add (dvd_mul_left _ _) (h.mul_right _)
  exact R.P.prime.not_unit (isUnit_of_dvd_one h1)

theorem not_dvd_crtU_mul : ¬ R.Q.p ∣ R.crtU * R.P.p := fun h => by
  have h1 : R.Q.p ∣ 1 := by
    rw [← R.crt_spec]
    exact dvd_add h (dvd_mul_left _ _)
  exact R.Q.prime.not_unit (isUnit_of_dvd_one h1)

theorem Q_not_dvd_P : ¬ R.Q.p ∣ R.P.p := fun h =>
  R.Q.prime.not_unit (R.coprime.isUnit_of_dvd' h (dvd_refl _))

theorem P_not_dvd_Q : ¬ R.P.p ∣ R.Q.p := fun h =>
  R.P.prime.not_unit (R.coprime.isUnit_of_dvd' (dvd_refl _) h)

/-- **Averaging over `O/m`.** `Σ_{x mod m} S_c((z + 3x)/m) = N(m)S_{c(·m)}(z)`. -/
theorem sum_crt_cuspCharacterSeries (c : O → ℂ) (hc : Summable (fun h => ‖c h‖)) (z : ℂ) :
    ∑ x₁ : R.P.Res, ∑ x₂ : R.Q.Res,
        cuspCharacterSeries c ((z + 3 * ringComplex (R.crt x₁ x₂)) / ringComplex R.Q.p / ringComplex R.P.p) =
      (Fintype.card R.P.Res : ℂ) * (Fintype.card R.Q.Res : ℂ) *
        cuspCharacterSeries (fun m => c (m * R.Q.p * R.P.p)) z := by
  have hP := R.P.ringComplex_ne_zero
  have hQ := R.Q.ringComplex_ne_zero
  have hpt : ∀ (x₁ : R.P.Res) (x₂ : R.Q.Res),
      (z + 3 * ringComplex (R.crt x₁ x₂)) / ringComplex R.Q.p / ringComplex R.P.p =
      ((z + 3 * ringComplex (R.crtU * R.P.p * R.Q.lift x₂)) / ringComplex R.Q.p +
        3 * ringComplex (R.crtV * R.P.lift x₁)) / ringComplex R.P.p := by
    intro x₁ x₂
    simp only [crt, ep, eq, map_add, map_mul]
    field_simp
    ring
  simp_rw [hpt]
  rw [Finset.sum_comm]
  simp_rw [R.P.sum_cuspCharacterSeries_low_mul _ R.not_dvd_crtV c hc]
  rw [← Finset.mul_sum, R.Q.sum_cuspCharacterSeries_low_mul _ R.not_dvd_crtU_mul _
    (hc.comp_injective (mul_right_injective_O R.P.ne_zero)) z]
  ring

/-! ### The Hecke points as cusp series -/

/-- The amplitudes of `θ_s` at the heights of the four kinds of Hecke points. -/
def ampHH (v : ℝ) : O → ℂ := rationalSourceModeAmplitude (‖ringComplex R.P.p‖ * (‖ringComplex R.Q.p‖ * v))
def ampLL (v : ℝ) : O → ℂ := rationalSourceModeAmplitude (v / ‖ringComplex R.Q.p‖ / ‖ringComplex R.P.p‖)
def ampHL (v : ℝ) : O → ℂ := rationalSourceModeAmplitude (‖ringComplex R.P.p‖ * v / ‖ringComplex R.Q.p‖)
def ampLH (v : ℝ) : O → ℂ := rationalSourceModeAmplitude (‖ringComplex R.Q.p‖ * v / ‖ringComplex R.P.p‖)

theorem summable_ampHH (v : ℝ) (hv : 0 < v) : Summable (fun h => ‖R.ampHH v h‖) :=
  rationalSourceModeAmplitude_summable _ (mul_pos R.P.norm_pos (mul_pos R.Q.norm_pos hv))

theorem summable_ampLL (v : ℝ) (hv : 0 < v) : Summable (fun h => ‖R.ampLL v h‖) :=
  rationalSourceModeAmplitude_summable _ (div_pos (div_pos hv R.Q.norm_pos) R.P.norm_pos)

theorem summable_ampHL (v : ℝ) (hv : 0 < v) : Summable (fun h => ‖R.ampHL v h‖) :=
  rationalSourceModeAmplitude_summable _ (div_pos (mul_pos R.P.norm_pos hv) R.Q.norm_pos)

theorem summable_ampLH (v : ℝ) (hv : 0 < v) : Summable (fun h => ‖R.ampLH v h‖) :=
  rationalSourceModeAmplitude_summable _ (div_pos (mul_pos R.Q.norm_pos hv) R.P.norm_pos)

theorem hh_source (z : ℂ) (v : ℝ) (hv : 0 < v) :
    R.hh sourceTheta (upperPoint z v hv) =
      cuspCharacterSeries (R.ampHH v) (ringComplex R.P.p * (ringComplex R.Q.p * z)) := by
  rw [R.hh_point, sourceTheta, cubicSourceResidualFunction_fourier_expansion, ampHH]

theorem ll_source (t : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    R.ll sourceTheta t (upperPoint z v hv) =
      cuspCharacterSeries (R.ampLL v) ((z + 3 * ringComplex t) / ringComplex R.Q.p / ringComplex R.P.p) := by
  rw [R.ll_point, sourceTheta, cubicSourceResidualFunction_fourier_expansion, ampLL]

theorem hl_source (t : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    R.hl sourceTheta t (upperPoint z v hv) =
      cuspCharacterSeries (R.ampHL v) ((ringComplex R.P.p * z + 3 * ringComplex t) / ringComplex R.Q.p) := by
  rw [R.hl_point, sourceTheta, cubicSourceResidualFunction_fourier_expansion, ampHL]

theorem lh_source (t : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    R.lh sourceTheta t (upperPoint z v hv) =
      cuspCharacterSeries (R.ampLH v) ((ringComplex R.Q.p * z + 3 * ringComplex t) / ringComplex R.P.p) := by
  rw [R.lh_point, sourceTheta, cubicSourceResidualFunction_fourier_expansion, ampLH]

/-! ### The five blocks as cusp series -/

/-- The convolution carried by the `(U, L)` coset with phase point `β`. -/
def ulConv (v : ℝ) (β : O) : O → ℂ :=
  cuspConv (dilateSeriesCoeff (R.P.p * R.P.p) (phasedCoeff (R.ampHL v) (-(3 * ringComplex β) / ringComplex R.Q.p)))
    (R.ampLL v)

/-- The convolution carried by the `(L, U)` coset with phase point `β`. -/
def luConv (v : ℝ) (β : O) : O → ℂ :=
  cuspConv (dilateSeriesCoeff (R.Q.p * R.Q.p) (phasedCoeff (R.ampLH v) (-(3 * ringComplex β) / ringComplex R.P.p)))
    (R.ampLL v)

/-- The convolution carried by the `(L, L)` coset with phase point `β`. -/
def llConv (v : ℝ) (β : O) : O → ℂ :=
  cuspConv (phasedCoeff (R.ampLL v) (-(3 * ringComplex β) / ringComplex R.Q.p / ringComplex R.P.p)) (R.ampLL v)

theorem PP_ne_zero : R.P.p * R.P.p ≠ 0 := mul_ne_zero R.P.ne_zero R.P.ne_zero

theorem QQ_ne_zero : R.Q.p * R.Q.p ≠ 0 := mul_ne_zero R.Q.ne_zero R.Q.ne_zero

theorem summable_ulConv (v : ℝ) (hv : 0 < v) (β : O) : Summable (fun h => ‖R.ulConv v β h‖) :=
  summable_cuspConv (summable_dilateSeriesCoeff R.PP_ne_zero (summable_phasedCoeff (R.summable_ampHL v hv) _))
    (R.summable_ampLL v hv)

theorem summable_luConv (v : ℝ) (hv : 0 < v) (β : O) : Summable (fun h => ‖R.luConv v β h‖) :=
  summable_cuspConv (summable_dilateSeriesCoeff R.QQ_ne_zero (summable_phasedCoeff (R.summable_ampLH v hv) _))
    (R.summable_ampLL v hv)

theorem summable_llConv (v : ℝ) (hv : 0 < v) (β : O) : Summable (fun h => ‖R.llConv v β h‖) :=
  summable_cuspConv (summable_phasedCoeff (R.summable_ampLL v hv) _) (R.summable_ampLL v hv)

theorem summable_comp_m {c : O → ℂ} (hc : Summable (fun h => ‖c h‖)) :
    Summable (fun m => ‖c (m * R.Q.p * R.P.p)‖) := by
  have h := hc.comp_injective (mul_right_injective_O (mul_ne_zero R.Q.ne_zero R.P.ne_zero))
  simpa only [Function.comp_def, mul_assoc] using h

theorem ul_term (c : ℂ) (x₁ : R.P.Res) (x₂ : R.Q.Res) (β : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    c * R.hl sourceTheta (R.P.p * R.crt x₁ x₂ - β) (upperPoint z v hv) *
        R.ll sourceTheta (R.crt x₁ x₂) (upperPoint z v hv) =
      c * cuspCharacterSeries (R.ulConv v β)
        ((z + 3 * ringComplex (R.crt x₁ x₂)) / ringComplex R.Q.p / ringComplex R.P.p) := by
  have hP := R.P.ringComplex_ne_zero
  have hQ := R.Q.ringComplex_ne_zero
  have harg : (ringComplex R.P.p * z + 3 * ringComplex (R.P.p * R.crt x₁ x₂ - β)) / ringComplex R.Q.p =
      ringComplex (R.P.p * R.P.p) * ((z + 3 * ringComplex (R.crt x₁ x₂)) / ringComplex R.Q.p / ringComplex R.P.p) +
        -(3 * ringComplex β) / ringComplex R.Q.p := by
    simp only [map_mul, map_sub]
    field_simp
    ring
  rw [R.hl_source, R.ll_source, harg, cuspCharacterSeries_add_phase, cuspCharacterSeries_dilate R.PP_ne_zero,
    mul_assoc, cuspCharacterSeries_mul (summable_dilateSeriesCoeff R.PP_ne_zero
      (summable_phasedCoeff (R.summable_ampHL v hv) _)) (R.summable_ampLL v hv), ulConv]

theorem lu_term (c : ℂ) (x₁ : R.P.Res) (x₂ : R.Q.Res) (β : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    c * R.lh sourceTheta (R.Q.p * R.crt x₁ x₂ - β) (upperPoint z v hv) *
        R.ll sourceTheta (R.crt x₁ x₂) (upperPoint z v hv) =
      c * cuspCharacterSeries (R.luConv v β)
        ((z + 3 * ringComplex (R.crt x₁ x₂)) / ringComplex R.Q.p / ringComplex R.P.p) := by
  have hP := R.P.ringComplex_ne_zero
  have hQ := R.Q.ringComplex_ne_zero
  have harg : (ringComplex R.Q.p * z + 3 * ringComplex (R.Q.p * R.crt x₁ x₂ - β)) / ringComplex R.P.p =
      ringComplex (R.Q.p * R.Q.p) * ((z + 3 * ringComplex (R.crt x₁ x₂)) / ringComplex R.Q.p / ringComplex R.P.p) +
        -(3 * ringComplex β) / ringComplex R.P.p := by
    simp only [map_mul, map_sub]
    field_simp
    ring
  rw [R.lh_source, R.ll_source, harg, cuspCharacterSeries_add_phase, cuspCharacterSeries_dilate R.QQ_ne_zero,
    mul_assoc, cuspCharacterSeries_mul (summable_dilateSeriesCoeff R.QQ_ne_zero
      (summable_phasedCoeff (R.summable_ampLH v hv) _)) (R.summable_ampLL v hv), luConv]

theorem ll_term (c : ℂ) (x : O) (β : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    c * R.ll sourceTheta (x - β) (upperPoint z v hv) * R.ll sourceTheta x (upperPoint z v hv) =
      c * cuspCharacterSeries (R.llConv v β) ((z + 3 * ringComplex x) / ringComplex R.Q.p / ringComplex R.P.p) := by
  have hP := R.P.ringComplex_ne_zero
  have hQ := R.Q.ringComplex_ne_zero
  have harg : (z + 3 * ringComplex (x - β)) / ringComplex R.Q.p / ringComplex R.P.p =
      (z + 3 * ringComplex x) / ringComplex R.Q.p / ringComplex R.P.p +
        -(3 * ringComplex β) / ringComplex R.Q.p / ringComplex R.P.p := by
    rw [map_sub]
    field_simp
    ring
  rw [R.ll_source, R.ll_source, harg, cuspCharacterSeries_add_phase, mul_assoc,
    cuspCharacterSeries_mul (summable_phasedCoeff (R.summable_ampLL v hv) _) (R.summable_ampLL v hv), llConv]

/-- `N(m)` as a complex number. -/
def normM : ℂ := (Fintype.card R.P.Res : ℂ) * (Fintype.card R.Q.Res : ℂ)

theorem llSum_source (z : ℂ) (v : ℝ) (hv : 0 < v) :
    R.llSum sourceTheta (upperPoint z v hv) =
      R.normM * cuspCharacterSeries (fun m => R.ampLL v (m * R.Q.p * R.P.p)) z := by
  unfold llSum
  simp_rw [R.ll_source]
  exact R.sum_crt_cuspCharacterSeries _ (R.summable_ampLL v hv) z

theorem hlSum_source (z : ℂ) (v : ℝ) (hv : 0 < v) :
    R.hlSum sourceTheta (upperPoint z v hv) =
      (Fintype.card R.Q.Res : ℂ) * cuspCharacterSeries (fun m => R.ampHL v (m * R.Q.p)) (ringComplex R.P.p * z) := by
  unfold hlSum
  simp_rw [R.hl_source]
  exact R.Q.sum_cuspCharacterSeries_low _ (R.summable_ampHL v hv) _

theorem lhSum_source (z : ℂ) (v : ℝ) (hv : 0 < v) :
    R.lhSum sourceTheta (upperPoint z v hv) =
      (Fintype.card R.P.Res : ℂ) * cuspCharacterSeries (fun m => R.ampLH v (m * R.P.p)) (ringComplex R.Q.p * z) := by
  unfold lhSum
  simp_rw [R.lh_source]
  exact R.P.sum_cuspCharacterSeries_low _ (R.summable_ampLH v hv) _

theorem ulBlock_source (z : ℂ) (v : ℝ) (hv : 0 < v) :
    R.ulBlock sourceTheta (upperPoint z v hv) =
      ∑ y₂ : {y : R.Q.Res // y ≠ 0}, ringComplex (symbol (3 * R.yUL y₂) R.Q.p) *
        (R.normM * cuspCharacterSeries (fun m => R.ulConv v (R.Q.lowBeta (R.yUL y₂)) (m * R.Q.p * R.P.p)) z) := by
  unfold ulBlock
  simp_rw [R.ul_term]
  rw [sum_three_comm]
  refine Finset.sum_congr rfl fun y₂ _ => ?_
  rw [normM, ← R.sum_crt_cuspCharacterSeries _ (R.summable_ulConv v hv _) z, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x₁ _ => by rw [Finset.mul_sum]

theorem luBlock_source (z : ℂ) (v : ℝ) (hv : 0 < v) :
    R.luBlock sourceTheta (upperPoint z v hv) =
      ∑ y₁ : {y : R.P.Res // y ≠ 0}, ringComplex (symbol (3 * R.yLU y₁) R.P.p) *
        (R.normM * cuspCharacterSeries (fun m => R.luConv v (R.P.lowBeta (R.yLU y₁)) (m * R.Q.p * R.P.p)) z) := by
  unfold luBlock
  simp_rw [R.lu_term]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y₁ _ => ?_
  rw [normM, ← R.sum_crt_cuspCharacterSeries _ (R.summable_luConv v hv _) z, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x₁ _ => by rw [Finset.mul_sum]

theorem llBlock_source (z : ℂ) (v : ℝ) (hv : 0 < v) :
    R.llBlock sourceTheta (upperPoint z v hv) =
      ∑ y₁ : {y : R.P.Res // y ≠ 0}, ∑ y₂ : {y : R.Q.Res // y ≠ 0},
        ringComplex (symbol (3 * R.crt y₁.1 y₂.1) (R.P.p * R.Q.p)) *
          (R.normM * cuspCharacterSeries (fun m => R.llConv v (R.mLowBeta (R.crt y₁.1 y₂.1)) (m * R.Q.p * R.P.p)) z) := by
  unfold llBlock
  simp_rw [R.ll_term]
  have h : ∀ (x₁ : R.P.Res) (y₁ : {y : R.P.Res // y ≠ 0}),
      ∑ x₂ : R.Q.Res, ∑ y₂ : {y : R.Q.Res // y ≠ 0}, ringComplex (symbol (3 * R.crt y₁.1 y₂.1) (R.P.p * R.Q.p)) *
          cuspCharacterSeries (R.llConv v (R.mLowBeta (R.crt y₁.1 y₂.1)))
            ((z + 3 * ringComplex (R.crt x₁ x₂)) / ringComplex R.Q.p / ringComplex R.P.p) =
        ∑ y₂ : {y : R.Q.Res // y ≠ 0}, ∑ x₂ : R.Q.Res, ringComplex (symbol (3 * R.crt y₁.1 y₂.1) (R.P.p * R.Q.p)) *
          cuspCharacterSeries (R.llConv v (R.mLowBeta (R.crt y₁.1 y₂.1)))
            ((z + 3 * ringComplex (R.crt x₁ x₂)) / ringComplex R.Q.p / ringComplex R.P.p) :=
    fun _ _ => Finset.sum_comm
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y₁ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y₂ _ => ?_
  rw [normM, ← R.sum_crt_cuspCharacterSeries _ (R.summable_llConv v hv _) z, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x₁ _ => by rw [Finset.mul_sum]

/-! ### The constant term -/

theorem integral_mul_dilate_pair (c d : O → ℂ) (hc : Summable (fun h => ‖c h‖)) (hd : Summable (fun h => ‖d h‖)) :
    ∫ z in periodDomain, cuspCharacterSeries c (ringComplex R.P.p * z) * cuspCharacterSeries d (ringComplex R.Q.p * z) =
      periodArea * ∑' l : O, c (l * R.Q.p) * d (-(l * R.P.p)) := by
  simp_rw [cuspCharacterSeries_dilate R.Q.ne_zero d]
  rw [integral_cuspCharacterSeries_mul_dilate R.P.p c _ hc (summable_dilateSeriesCoeff R.Q.ne_zero hd)]
  congr 1
  have hsupp : Function.support (fun h => c h * dilateSeriesCoeff R.Q.p d (-(h * R.P.p))) ⊆
      Set.range (fun l : O => l * R.Q.p) := fun h hh => by
    by_contra hn
    apply hh
    have hq : ¬ R.Q.p ∣ h := fun ⟨l, hl⟩ => hn ⟨l, by rw [hl, mul_comm]⟩
    have hr : -(h * R.P.p) ∉ Set.range (fun l : O => l * R.Q.p) := by
      rintro ⟨j, hj⟩
      have hd' : R.Q.p ∣ h * R.P.p := ⟨-j, by linear_combination hj⟩
      rcases R.Q.prime.dvd_or_dvd hd' with h1 | h1
      · exact hq h1
      · exact R.Q_not_dvd_P h1
    simp only [dilateSeriesCoeff_off d _ hr, mul_zero]
  rw [← (mul_right_injective_O R.Q.ne_zero).tsum_eq hsupp]
  refine tsum_congr fun l => ?_
  simp only [show -(l * R.Q.p * R.P.p) = -(l * R.P.p) * R.Q.p by ring, dilateSeriesCoeff_mul R.Q.ne_zero]

theorem continuous_blocks (v : ℝ) (hv : 0 < v) :
    Continuous (fun z => R.hh sourceTheta (upperPoint z v hv) * R.llSum sourceTheta (upperPoint z v hv)) ∧
    Continuous (fun z => R.hlSum sourceTheta (upperPoint z v hv) * R.lhSum sourceTheta (upperPoint z v hv)) ∧
    Continuous (fun z => R.ulBlock sourceTheta (upperPoint z v hv)) ∧
    Continuous (fun z => R.luBlock sourceTheta (upperPoint z v hv)) ∧
    Continuous (fun z => R.llBlock sourceTheta (upperPoint z v hv)) := by
  simp_rw [R.hh_source, R.llSum_source, R.hlSum_source, R.lhSum_source, R.ulBlock_source, R.luBlock_source,
    R.llBlock_source]
  have hcm : Continuous (fun z : ℂ => ringComplex R.P.p * z) := continuous_const.mul continuous_id
  have hcq : Continuous (fun z : ℂ => ringComplex R.Q.p * z) := continuous_const.mul continuous_id
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ((cuspCharacterSeries_continuous _ (R.summable_ampHH v hv)).comp (hcm.comp hcq)).mul
      (continuous_const.mul (cuspCharacterSeries_continuous _ (R.summable_comp_m (R.summable_ampLL v hv))))
  · exact (continuous_const.mul ((cuspCharacterSeries_continuous _ ((R.summable_ampHL v hv).comp_injective
      (mul_right_injective_O R.Q.ne_zero))).comp hcm)).mul
      (continuous_const.mul ((cuspCharacterSeries_continuous _ ((R.summable_ampLH v hv).comp_injective
        (mul_right_injective_O R.P.ne_zero))).comp hcq))
  · exact continuous_finsetSum _ fun y _ => continuous_const.mul (continuous_const.mul
      (cuspCharacterSeries_continuous _ (R.summable_comp_m (R.summable_ulConv v hv _))))
  · exact continuous_finsetSum _ fun y _ => continuous_const.mul (continuous_const.mul
      (cuspCharacterSeries_continuous _ (R.summable_comp_m (R.summable_luConv v hv _))))
  · exact continuous_finsetSum _ fun y₁ _ => continuous_finsetSum _ fun y₂ _ => continuous_const.mul
      (continuous_const.mul (cuspCharacterSeries_continuous _ (R.summable_comp_m (R.summable_llConv v hv _))))

theorem integral_hh_llSum (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, R.hh sourceTheta (upperPoint z v hv) * R.llSum sourceTheta (upperPoint z v hv) =
      R.normM * periodArea * ∑' h : O, R.ampHH v h * R.ampLL v (-(h * (R.P.p * R.Q.p)) * R.Q.p * R.P.p) := by
  simp_rw [R.hh_source, R.llSum_source]
  have e : ∀ z : ℂ, cuspCharacterSeries (R.ampHH v) (ringComplex R.P.p * (ringComplex R.Q.p * z)) *
      (R.normM * cuspCharacterSeries (fun m => R.ampLL v (m * R.Q.p * R.P.p)) z) =
      R.normM * (cuspCharacterSeries (R.ampHH v) (ringComplex (R.P.p * R.Q.p) * z) *
        cuspCharacterSeries (fun m => R.ampLL v (m * R.Q.p * R.P.p)) z) := fun z => by
    rw [map_mul, mul_assoc]
    ring
  simp_rw [e]
  rw [integral_const_mul, integral_cuspCharacterSeries_mul_dilate _ _ _ (R.summable_ampHH v hv)
    (R.summable_comp_m (R.summable_ampLL v hv))]
  ring

theorem integral_hlSum_lhSum (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, R.hlSum sourceTheta (upperPoint z v hv) * R.lhSum sourceTheta (upperPoint z v hv) =
      R.normM * periodArea * ∑' l : O, R.ampHL v (l * R.Q.p * R.Q.p) * R.ampLH v (-(l * R.P.p) * R.P.p) := by
  simp_rw [R.hlSum_source, R.lhSum_source]
  have e : ∀ z : ℂ, (Fintype.card R.Q.Res : ℂ) * cuspCharacterSeries (fun m => R.ampHL v (m * R.Q.p)) (ringComplex R.P.p * z) *
      ((Fintype.card R.P.Res : ℂ) * cuspCharacterSeries (fun m => R.ampLH v (m * R.P.p)) (ringComplex R.Q.p * z)) =
      R.normM * (cuspCharacterSeries (fun m => R.ampHL v (m * R.Q.p)) (ringComplex R.P.p * z) *
        cuspCharacterSeries (fun m => R.ampLH v (m * R.P.p)) (ringComplex R.Q.p * z)) := fun z => by
    rw [normM]
    ring
  simp_rw [e]
  rw [integral_const_mul, R.integral_mul_dilate_pair _ _ ((R.summable_ampHL v hv).comp_injective
    (mul_right_injective_O R.Q.ne_zero)) ((R.summable_ampLH v hv).comp_injective (mul_right_injective_O R.P.ne_zero))]
  ring

theorem integral_ulBlock (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, R.ulBlock sourceTheta (upperPoint z v hv) =
      R.normM * periodArea * ∑ y₂ : {y : R.Q.Res // y ≠ 0}, ringComplex (symbol (3 * R.yUL y₂) R.Q.p) *
        R.ulConv v (R.Q.lowBeta (R.yUL y₂)) 0 := by
  simp_rw [R.ulBlock_source]
  have hc : ∀ y₂ : {y : R.Q.Res // y ≠ 0}, Continuous (fun z => ringComplex (symbol (3 * R.yUL y₂) R.Q.p) *
      (R.normM * cuspCharacterSeries (fun m => R.ulConv v (R.Q.lowBeta (R.yUL y₂)) (m * R.Q.p * R.P.p)) z)) :=
    fun y => continuous_const.mul (continuous_const.mul
      (cuspCharacterSeries_continuous _ (R.summable_comp_m (R.summable_ulConv v hv _))))
  rw [integral_finsetSum _ fun y _ => integrableOn_periodDomain_of_continuous _ (hc y), Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [integral_const_mul, integral_const_mul,
    PrimaryPrime.integral_cuspCharacterSeries _ (R.summable_comp_m (R.summable_ulConv v hv _)), zero_mul, zero_mul]
  ring

theorem integral_luBlock (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, R.luBlock sourceTheta (upperPoint z v hv) =
      R.normM * periodArea * ∑ y₁ : {y : R.P.Res // y ≠ 0}, ringComplex (symbol (3 * R.yLU y₁) R.P.p) *
        R.luConv v (R.P.lowBeta (R.yLU y₁)) 0 := by
  simp_rw [R.luBlock_source]
  have hc : ∀ y₁ : {y : R.P.Res // y ≠ 0}, Continuous (fun z => ringComplex (symbol (3 * R.yLU y₁) R.P.p) *
      (R.normM * cuspCharacterSeries (fun m => R.luConv v (R.P.lowBeta (R.yLU y₁)) (m * R.Q.p * R.P.p)) z)) :=
    fun y => continuous_const.mul (continuous_const.mul
      (cuspCharacterSeries_continuous _ (R.summable_comp_m (R.summable_luConv v hv _))))
  rw [integral_finsetSum _ fun y _ => integrableOn_periodDomain_of_continuous _ (hc y), Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [integral_const_mul, integral_const_mul,
    PrimaryPrime.integral_cuspCharacterSeries _ (R.summable_comp_m (R.summable_luConv v hv _)), zero_mul, zero_mul]
  ring

theorem integral_llBlock (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, R.llBlock sourceTheta (upperPoint z v hv) =
      R.normM * periodArea * ∑ y₁ : {y : R.P.Res // y ≠ 0}, ∑ y₂ : {y : R.Q.Res // y ≠ 0},
        ringComplex (symbol (3 * R.crt y₁.1 y₂.1) (R.P.p * R.Q.p)) * R.llConv v (R.mLowBeta (R.crt y₁.1 y₂.1)) 0 := by
  simp_rw [R.llBlock_source]
  have hc : ∀ (y₁ : {y : R.P.Res // y ≠ 0}) (y₂ : {y : R.Q.Res // y ≠ 0}), Continuous (fun z =>
      ringComplex (symbol (3 * R.crt y₁.1 y₂.1) (R.P.p * R.Q.p)) *
        (R.normM * cuspCharacterSeries (fun m => R.llConv v (R.mLowBeta (R.crt y₁.1 y₂.1)) (m * R.Q.p * R.P.p)) z)) :=
    fun y₁ y₂ => continuous_const.mul (continuous_const.mul
      (cuspCharacterSeries_continuous _ (R.summable_comp_m (R.summable_llConv v hv _))))
  have hc' : ∀ y₁ : {y : R.P.Res // y ≠ 0}, Continuous (fun z => ∑ y₂ : {y : R.Q.Res // y ≠ 0},
      ringComplex (symbol (3 * R.crt y₁.1 y₂.1) (R.P.p * R.Q.p)) *
        (R.normM * cuspCharacterSeries (fun m => R.llConv v (R.mLowBeta (R.crt y₁.1 y₂.1)) (m * R.Q.p * R.P.p)) z)) :=
    fun y₁ => continuous_finsetSum _ fun y₂ _ => hc y₁ y₂
  rw [integral_finsetSum _ fun y₁ _ => integrableOn_periodDomain_of_continuous _ (hc' y₁), Finset.mul_sum]
  refine Finset.sum_congr rfl fun y₁ _ => ?_
  rw [integral_finsetSum _ fun y₂ _ => integrableOn_periodDomain_of_continuous _ (hc y₁ y₂), Finset.mul_sum]
  refine Finset.sum_congr rfl fun y₂ _ => ?_
  rw [integral_const_mul, integral_const_mul,
    PrimaryPrime.integral_cuspCharacterSeries _ (R.summable_comp_m (R.summable_llConv v hv _)), zero_mul, zero_mul]
  ring

/-- **The constant term of the composite trace as five correlations.** -/
theorem integral_sourceTrace (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, R.sourceTrace (upperPoint z v hv) =
      R.normM * periodArea *
        (2 * ∑' h : O, R.ampHH v h * R.ampLL v (-(h * (R.P.p * R.Q.p)) * R.Q.p * R.P.p) +
          2 * ringComplex (symbol R.P.p R.Q.p) *
            ∑' l : O, R.ampHL v (l * R.Q.p * R.Q.p) * R.ampLH v (-(l * R.P.p) * R.P.p) +
          2 * ∑ y₂ : {y : R.Q.Res // y ≠ 0}, ringComplex (symbol (3 * R.yUL y₂) R.Q.p) *
            R.ulConv v (R.Q.lowBeta (R.yUL y₂)) 0 +
          2 * ∑ y₁ : {y : R.P.Res // y ≠ 0}, ringComplex (symbol (3 * R.yLU y₁) R.P.p) *
            R.luConv v (R.P.lowBeta (R.yLU y₁)) 0 +
          ∑ y₁ : {y : R.P.Res // y ≠ 0}, ∑ y₂ : {y : R.Q.Res // y ≠ 0},
            ringComplex (symbol (3 * R.crt y₁.1 y₂.1) (R.P.p * R.Q.p)) * R.llConv v (R.mLowBeta (R.crt y₁.1 y₂.1)) 0) := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := R.continuous_blocks v hv
  have i1 := (integrableOn_periodDomain_of_continuous _ c1).const_mul 2
  have i2 := (integrableOn_periodDomain_of_continuous _ c2).const_mul (2 * ringComplex (symbol R.P.p R.Q.p))
  have i3 := (integrableOn_periodDomain_of_continuous _ c3).const_mul 2
  have i4 := (integrableOn_periodDomain_of_continuous _ c4).const_mul 2
  have i5 := integrableOn_periodDomain_of_continuous _ c5
  set F1 := fun z => 2 * (R.hh sourceTheta (upperPoint z v hv) * R.llSum sourceTheta (upperPoint z v hv))
  set F2 := fun z => 2 * ringComplex (symbol R.P.p R.Q.p) *
    (R.hlSum sourceTheta (upperPoint z v hv) * R.lhSum sourceTheta (upperPoint z v hv))
  set F3 := fun z => 2 * R.ulBlock sourceTheta (upperPoint z v hv)
  set F4 := fun z => 2 * R.luBlock sourceTheta (upperPoint z v hv)
  set F5 := fun z => R.llBlock sourceTheta (upperPoint z v hv)
  have j2 : IntegrableOn (fun z => F1 z + F2 z) periodDomain := i1.add i2
  have j3 : IntegrableOn (fun z => F1 z + F2 z + F3 z) periodDomain := j2.add i3
  have j4 : IntegrableOn (fun z => F1 z + F2 z + F3 z + F4 z) periodDomain := j3.add i4
  have hsum : ∀ z, R.sourceTrace (upperPoint z v hv) = F1 z + F2 z + F3 z + F4 z + F5 z := fun z => by
    rw [sourceTrace, R.heckeTrace_eq_blocks sourceTheta sourceTheta_automorphy]
  simp_rw [hsum]
  rw [integral_add j4 i5, integral_add j3 i4, integral_add j2 i3, integral_add i1 i2]
  simp only [F1, F2, F3, F4, F5]
  rw [ integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, R.integral_hh_llSum v hv, R.integral_hlSum_lhSum v hv, R.integral_ulBlock v hv,
    R.integral_luBlock v hv, R.integral_llBlock v hv]
  ring

end PrimaryPair

end GaloisForLFunctions.OrderSixMetaplecticTheory
