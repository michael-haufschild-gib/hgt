/-
The semilocal `{∞,p}` Hardy--Titchmarsh line and the `θ_p`/`ι'_p` square.

The semilocal weighted line carries the measure of the archimedean line multiplied by the
positive Euler density `|1-p^{-1/2-is}|²`. Multiplication by the finite Euler factor
`(1-p^{-1/2-is})⁻¹` is a unitary from the archimedean onto the semilocal line, and composing
it with the archimedean dual Hardy--Titchmarsh unitary produces the semilocal dual unitary
`υ_{∞,p}`. The forward map `ι'_p` obtained by adjoining the place `p` is the set-identity
between the two weighted spaces: it is bounded with bounded inverse but not unitary, and its
Radon--Nikodym/Gram operator is exactly multiplication by the positive Euler weight,

`(ι'_p)† ∘ ι'_p = M_{w_p}`.

The commuting square `υ_{∞,p} ∘ θ_p = ι'_p ∘ υ_∞` holds with `θ_p` the even physical local
factor: the finite Euler factor cancels against the local factor transported by `υ_∞`.
-/
import GaloisForLFunctions.RHTower.HardyTitchmarshEulerConcrete

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace RHTower

/-! ### The finite Euler factor on the critical line -/

/-- The local-factor symbol `1 - p^{-1/2-is}` on the critical line. -/
def semilocalPrimeSymbol (p s : ℝ) : ℂ :=
  1 - ((Real.sqrt p : ℂ))⁻¹ * (MellinL2.mellinCharacter p s)⁻¹

theorem norm_sqrt_inv_mul_character_inv (p s : ℝ) :
    ‖((Real.sqrt p : ℂ))⁻¹ * (MellinL2.mellinCharacter p s)⁻¹‖ = (Real.sqrt p)⁻¹ := by
  rw [norm_mul, norm_inv, norm_inv, MellinL2.norm_mellinCharacter, inv_one, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg p)]

theorem le_norm_semilocalPrimeSymbol (p s : ℝ) :
    1 - (Real.sqrt p)⁻¹ ≤ ‖semilocalPrimeSymbol p s‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (((Real.sqrt p : ℂ))⁻¹ * (MellinL2.mellinCharacter p s)⁻¹)
  rw [norm_one, norm_sqrt_inv_mul_character_inv] at h
  exact h

theorem norm_semilocalPrimeSymbol_le (p s : ℝ) :
    ‖semilocalPrimeSymbol p s‖ ≤ 1 + (Real.sqrt p)⁻¹ := by
  have h := norm_sub_le (1 : ℂ) (((Real.sqrt p : ℂ))⁻¹ * (MellinL2.mellinCharacter p s)⁻¹)
  rw [norm_one, norm_sqrt_inv_mul_character_inv] at h
  exact h

theorem sqrt_inv_lt_one (p : ℝ) (hp : 1 < p) : (Real.sqrt p)⁻¹ < 1 := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hsqrt1 : 1 < Real.sqrt p := by
    nlinarith [Real.sq_sqrt hp0.le, Real.sqrt_nonneg p]
  exact inv_lt_one_of_one_lt₀ hsqrt1

theorem semilocalPrimeSymbol_ne_zero (p : ℝ) (hp : 1 < p) (s : ℝ) :
    semilocalPrimeSymbol p s ≠ 0 := by
  have hlow := le_norm_semilocalPrimeSymbol p s
  have hlt := sqrt_inv_lt_one p hp
  intro h0
  rw [h0, norm_zero] at hlow
  linarith

theorem semilocalPrimeSymbol_continuous (p : ℝ) :
    Continuous fun s => semilocalPrimeSymbol p s := by
  unfold semilocalPrimeSymbol MellinL2.mellinCharacter
  simp only [← Complex.exp_neg]
  fun_prop

/-- The finite Euler factor `(1 - p^{-1/2-is})⁻¹` at the place `p`. -/
def primeEulerFactor (p s : ℝ) : ℂ := (semilocalPrimeSymbol p s)⁻¹

theorem primeEulerFactor_ne_zero (p : ℝ) (hp : 1 < p) (s : ℝ) :
    primeEulerFactor p s ≠ 0 :=
  inv_ne_zero (semilocalPrimeSymbol_ne_zero p hp s)

theorem primeEulerFactor_continuous (p : ℝ) (hp : 1 < p) :
    Continuous fun s => primeEulerFactor p s :=
  (semilocalPrimeSymbol_continuous p).inv₀ (semilocalPrimeSymbol_ne_zero p hp)

/-! ### The semilocal weighted measure -/

/-- The positive Euler density `|1 - p^{-1/2-is}|²`. -/
def semilocalPrimeWeight (p s : ℝ) : ℝ≥0 := (‖primeEulerFactor p s‖₊)⁻¹ ^ 2

theorem semilocalPrimeWeight_eq_symbol_sq (p s : ℝ) :
    semilocalPrimeWeight p s = ‖semilocalPrimeSymbol p s‖₊ ^ 2 := by
  rw [semilocalPrimeWeight, primeEulerFactor, nnnorm_inv, inv_inv]

theorem semilocalPrimeWeight_ne_zero (p : ℝ) (hp : 1 < p) (s : ℝ) :
    semilocalPrimeWeight p s ≠ 0 :=
  pow_ne_zero _ (inv_ne_zero (nnnorm_ne_zero_iff.mpr (primeEulerFactor_ne_zero p hp s)))

theorem semilocalPrimeWeight_measurable (p : ℝ) (hp : 1 < p) :
    Measurable fun s => semilocalPrimeWeight p s := by
  have hcont : Continuous fun s => semilocalPrimeWeight p s := by
    unfold semilocalPrimeWeight
    exact (((primeEulerFactor_continuous p hp).nnnorm).inv₀
      (fun s => nnnorm_ne_zero_iff.mpr (primeEulerFactor_ne_zero p hp s))).pow 2
  exact hcont.measurable

/-- The `{∞,p}` semilocal measure: the archimedean weighted measure multiplied by the
positive Euler density. -/
def semilocalWeightedMeasure (p : ℝ) : Measure ℝ :=
  archimedeanWeightedMeasure.withDensity fun s => (semilocalPrimeWeight p s : ℝ≥0∞)

abbrev SemilocalWeightedL2 (p : ℝ) := Lp (α := ℝ) ℂ 2 (semilocalWeightedMeasure p)

theorem semilocalWeightedMeasure_absolutelyContinuous (p : ℝ) :
    semilocalWeightedMeasure p ≪ archimedeanWeightedMeasure :=
  withDensity_absolutelyContinuous _ _

theorem archimedeanWeightedMeasure_absolutelyContinuous_semilocal (p : ℝ) (hp : 1 < p) :
    archimedeanWeightedMeasure ≪ semilocalWeightedMeasure p := by
  unfold semilocalWeightedMeasure
  apply withDensity_absolutelyContinuous'
  · exact (semilocalPrimeWeight_measurable p hp).coe_nnreal_ennreal.aemeasurable
  · filter_upwards with s
    exact_mod_cast semilocalPrimeWeight_ne_zero p hp s

/-! ### The pointwise weight algebra -/

theorem semilocalPrimeWeight_mul_norm_sq (p : ℝ) (hp : 1 < p) (s : ℝ) (z : ℂ) :
    (semilocalPrimeWeight p s : ℝ) * ‖primeEulerFactor p s * z‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [norm_mul]
  change ‖primeEulerFactor p s‖⁻¹ ^ 2 * (‖primeEulerFactor p s‖ * ‖z‖) ^ 2 = ‖z‖ ^ 2
  field_simp [norm_ne_zero_iff.mpr (primeEulerFactor_ne_zero p hp s)]

theorem norm_primeEulerFactor_inv_mul_sq (p s : ℝ) (z : ℂ) :
    ‖(primeEulerFactor p s)⁻¹ * z‖ ^ 2 = (semilocalPrimeWeight p s : ℝ) * ‖z‖ ^ 2 := by
  rw [norm_mul, norm_inv]
  change (‖primeEulerFactor p s‖⁻¹ * ‖z‖) ^ 2 = ‖primeEulerFactor p s‖⁻¹ ^ 2 * ‖z‖ ^ 2
  ring

theorem semilocalPrimeWeight_mul_enorm_rpow_two (p : ℝ) (hp : 1 < p) (s : ℝ) (z : ℂ) :
    (semilocalPrimeWeight p s : ℝ≥0∞) * ‖primeEulerFactor p s * z‖ₑ ^ (2 : ℝ) =
      ‖z‖ₑ ^ (2 : ℝ) := by
  simp only [semilocalPrimeWeight, enorm_eq_nnnorm, ENNReal.rpow_two, nnnorm_mul]
  have hnn : ‖primeEulerFactor p s‖₊ ≠ 0 :=
    nnnorm_ne_zero_iff.mpr (primeEulerFactor_ne_zero p hp s)
  have h0 : (‖primeEulerFactor p s‖₊ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hnn
  have htop : (‖primeEulerFactor p s‖₊ : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  push_cast
  rw [ENNReal.coe_inv hnn]
  rw [← mul_pow, ← mul_assoc, ENNReal.inv_mul_cancel h0 htop, one_mul]

/-! ### Multiplication by the finite Euler factor is a unitary onto the semilocal line -/

theorem memLp_primeEulerFactor_mul (p : ℝ) (hp : 1 < p) (f : ArchimedeanWeightedL2) :
    MemLp (fun s => primeEulerFactor p s * f s) 2 (semilocalWeightedMeasure p) := by
  rw [memLp_two_iff_integrable_sq_norm]
  · unfold semilocalWeightedMeasure
    rw [integrable_withDensity_iff_integrable_smul (E := ℝ)
      (semilocalPrimeWeight_measurable p hp)]
    have hf : Integrable (fun s => ‖f s‖ ^ 2) archimedeanWeightedMeasure :=
      (memLp_two_iff_integrable_sq_norm (Lp.memLp f).1).mp (Lp.memLp f)
    convert hf using 1
    ext s
    simpa [NNReal.smul_def] using semilocalPrimeWeight_mul_norm_sq p hp s (f s)
  · exact (primeEulerFactor_continuous p hp).aestronglyMeasurable.mul
      (AEStronglyMeasurable.mono_ac (semilocalWeightedMeasure_absolutelyContinuous p)
        (Lp.memLp f).1)

theorem memLp_primeEulerFactor_inv_mul (p : ℝ) (hp : 1 < p) (g : SemilocalWeightedL2 p) :
    MemLp (fun s => (primeEulerFactor p s)⁻¹ * g s) 2 archimedeanWeightedMeasure := by
  rw [memLp_two_iff_integrable_sq_norm]
  · have hg : Integrable (fun s => ‖g s‖ ^ 2) (semilocalWeightedMeasure p) :=
      (memLp_two_iff_integrable_sq_norm (Lp.memLp g).1).mp (Lp.memLp g)
    unfold semilocalWeightedMeasure at hg
    rw [integrable_withDensity_iff_integrable_smul (E := ℝ)
      (semilocalPrimeWeight_measurable p hp)] at hg
    convert hg using 1
    ext s
    simpa [NNReal.smul_def] using norm_primeEulerFactor_inv_mul_sq p s (g s)
  · exact ((primeEulerFactor_continuous p hp).inv₀
      (fun s => primeEulerFactor_ne_zero p hp s)).aestronglyMeasurable.mul
      (AEStronglyMeasurable.mono_ac
        (archimedeanWeightedMeasure_absolutelyContinuous_semilocal p hp)
        (Lp.memLp g).1)

/-- Multiplication by the finite Euler factor, valued in the semilocal space. -/
def semilocalMulAux (p : ℝ) (hp : 1 < p) (f : ArchimedeanWeightedL2) :
    SemilocalWeightedL2 p :=
  (memLp_primeEulerFactor_mul p hp f).toLp _

theorem semilocalMulAux_ae (p : ℝ) (hp : 1 < p) (f : ArchimedeanWeightedL2) :
    semilocalMulAux p hp f =ᵐ[semilocalWeightedMeasure p]
      fun s => primeEulerFactor p s * f s :=
  (memLp_primeEulerFactor_mul p hp f).coeFn_toLp

/-- Multiplication by the local-factor symbol, valued in the archimedean space. -/
def semilocalMulInvAux (p : ℝ) (hp : 1 < p) (g : SemilocalWeightedL2 p) :
    ArchimedeanWeightedL2 :=
  (memLp_primeEulerFactor_inv_mul p hp g).toLp _

theorem semilocalMulInvAux_ae (p : ℝ) (hp : 1 < p) (g : SemilocalWeightedL2 p) :
    semilocalMulInvAux p hp g =ᵐ[archimedeanWeightedMeasure]
      fun s => (primeEulerFactor p s)⁻¹ * g s :=
  (memLp_primeEulerFactor_inv_mul p hp g).coeFn_toLp

theorem semilocalMulAux_add (p : ℝ) (hp : 1 < p) (f g : ArchimedeanWeightedL2) :
    semilocalMulAux p hp (f + g) = semilocalMulAux p hp f + semilocalMulAux p hp g := by
  apply Lp.ext
  have hinput := (semilocalWeightedMeasure_absolutelyContinuous p).ae_eq (Lp.coeFn_add f g)
  filter_upwards [semilocalMulAux_ae p hp (f + g), semilocalMulAux_ae p hp f,
    semilocalMulAux_ae p hp g, hinput,
    Lp.coeFn_add (semilocalMulAux p hp f) (semilocalMulAux p hp g)] with s hsum hf hg hin hout
  rw [hsum, hout, hin]
  change primeEulerFactor p s * (f s + g s) = semilocalMulAux p hp f s + semilocalMulAux p hp g s
  rw [hf, hg]
  ring

theorem semilocalMulAux_smul (p : ℝ) (hp : 1 < p) (c : ℂ) (f : ArchimedeanWeightedL2) :
    semilocalMulAux p hp (c • f) = c • semilocalMulAux p hp f := by
  apply Lp.ext
  have hinput := (semilocalWeightedMeasure_absolutelyContinuous p).ae_eq (Lp.coeFn_smul c f)
  filter_upwards [semilocalMulAux_ae p hp (c • f), semilocalMulAux_ae p hp f,
    hinput, Lp.coeFn_smul c (semilocalMulAux p hp f)] with s hcf hf hin hout
  rw [hcf, hout, hin]
  change primeEulerFactor p s * (c * f s) = c * semilocalMulAux p hp f s
  rw [hf]
  ring

theorem eLpNorm_primeEulerFactor_mul (p : ℝ) (hp : 1 < p) (f : ArchimedeanWeightedL2) :
    eLpNorm (fun s => primeEulerFactor p s * f s) 2 (semilocalWeightedMeasure p) =
      eLpNorm (fun s => f s) 2 archimedeanWeightedMeasure := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  unfold semilocalWeightedMeasure
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable archimedeanWeightedMeasure
    (semilocalPrimeWeight_measurable p hp).coe_nnreal_ennreal
    (Filter.Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
  apply lintegral_congr
  intro s
  simpa only [Pi.mul_apply] using semilocalPrimeWeight_mul_enorm_rpow_two p hp s (f s)

theorem norm_semilocalMulAux (p : ℝ) (hp : 1 < p) (f : ArchimedeanWeightedL2) :
    ‖semilocalMulAux p hp f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (semilocalMulAux_ae p hp f),
    eLpNorm_primeEulerFactor_mul p hp f]

def semilocalMulLinear (p : ℝ) (hp : 1 < p) :
    ArchimedeanWeightedL2 →ₗ[ℂ] SemilocalWeightedL2 p where
  toFun := semilocalMulAux p hp
  map_add' := semilocalMulAux_add p hp
  map_smul' c f := by simpa using semilocalMulAux_smul p hp c f

def semilocalMulIsometry (p : ℝ) (hp : 1 < p) :
    ArchimedeanWeightedL2 →ₗᵢ[ℂ] SemilocalWeightedL2 p where
  __ := semilocalMulLinear p hp
  norm_map' := norm_semilocalMulAux p hp

/-- **The semilocal factor unitary.** Multiplication by the finite Euler factor
`(1-p^{-1/2-is})⁻¹` from the archimedean onto the `{∞,p}` semilocal line. -/
def semilocalMulUnitary (p : ℝ) (hp : 1 < p) :
    ArchimedeanWeightedL2 ≃ₗᵢ[ℂ] SemilocalWeightedL2 p where
  __ := semilocalMulIsometry p hp
  invFun := semilocalMulInvAux p hp
  left_inv f := by
    change semilocalMulInvAux p hp (semilocalMulAux p hp f) = f
    apply Lp.ext
    have hmul := (archimedeanWeightedMeasure_absolutelyContinuous_semilocal p hp).ae_eq
      (semilocalMulAux_ae p hp f)
    filter_upwards [semilocalMulInvAux_ae p hp (semilocalMulAux p hp f), hmul] with s hout hin
    rw [hout, hin, ← mul_assoc, inv_mul_cancel₀ (primeEulerFactor_ne_zero p hp s), one_mul]
  right_inv g := by
    change semilocalMulAux p hp (semilocalMulInvAux p hp g) = g
    apply Lp.ext
    have hinv := (semilocalWeightedMeasure_absolutelyContinuous p).ae_eq
      (semilocalMulInvAux_ae p hp g)
    filter_upwards [semilocalMulAux_ae p hp (semilocalMulInvAux p hp g), hinv] with s hout hin
    rw [hout, hin, ← mul_assoc, mul_inv_cancel₀ (primeEulerFactor_ne_zero p hp s), one_mul]

theorem semilocalMulUnitary_ae (p : ℝ) (hp : 1 < p) (f : ArchimedeanWeightedL2) :
    semilocalMulUnitary p hp f =ᵐ[semilocalWeightedMeasure p]
      fun s => primeEulerFactor p s * f s :=
  semilocalMulAux_ae p hp f

/-! ### The forward map `ι'_p` and its Gram operator -/

/-- The forward map `ι'_p` obtained by adjoining the place `p`: the set-identity from the
archimedean onto the semilocal line, realized as the factor unitary composed with the local
factor. -/
def semilocalForwardMap (p : ℝ) (hp : 1 < p) :
    ArchimedeanWeightedL2 →L[ℂ] SemilocalWeightedL2 p :=
  (semilocalMulUnitary p hp : ArchimedeanWeightedL2 →L[ℂ] SemilocalWeightedL2 p) ∘L
    archimedeanPrimeLocalFactor p

/-- `ι'_p` is the identity on measurable representatives: adjoining a place does not move the
function, only the norm. -/
theorem semilocalForwardMap_ae (p : ℝ) (hp : 1 < p) (f : ArchimedeanWeightedL2) :
    semilocalForwardMap p hp f =ᵐ[semilocalWeightedMeasure p] ⇑f := by
  have hlocal := (semilocalWeightedMeasure_absolutelyContinuous p).ae_eq
    (archimedeanPrimeLocalFactor_ae p f)
  have hmul := semilocalMulUnitary_ae p hp (archimedeanPrimeLocalFactor p f)
  filter_upwards [hmul, hlocal] with s hout hin
  change semilocalMulUnitary p hp (archimedeanPrimeLocalFactor p f) s = f s
  rw [hout, hin]
  show primeEulerFactor p s * (semilocalPrimeSymbol p s * f s) = f s
  rw [primeEulerFactor, ← mul_assoc,
    inv_mul_cancel₀ (semilocalPrimeSymbol_ne_zero p hp s), one_mul]

/-- **The Radon--Nikodym/Gram identity** `(ι'_p)† ∘ ι'_p = M_{w_p}`: the Gram operator of the
place-adjoining map is exactly multiplication by the positive Euler weight. -/
theorem adjoint_semilocalForwardMap_comp_self (p : ℝ) (hp : 1 < p) :
    ContinuousLinearMap.adjoint (semilocalForwardMap p hp) ∘L semilocalForwardMap p hp =
      archimedeanPrimeEulerGram p := by
  rw [semilocalForwardMap, ContinuousLinearMap.adjoint_comp,
    LinearIsometryEquiv.adjoint_eq_symm]
  apply ContinuousLinearMap.ext
  intro f
  change (ContinuousLinearMap.adjoint (archimedeanPrimeLocalFactor p))
      ((semilocalMulUnitary p hp).symm
        ((semilocalMulUnitary p hp) (archimedeanPrimeLocalFactor p f))) =
    archimedeanPrimeEulerGram p f
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

/-! ### The semilocal dual Hardy--Titchmarsh unitary and the square -/

/-- The semilocal dual Hardy--Titchmarsh unitary `υ_{∞,p}`: the archimedean dual unitary
followed by the finite Euler factor. -/
def semilocalDualHardyTitchmarshUnitary (p : ℝ) (hp : 1 < p) :
    evenSubspace ≃ₗᵢ[ℂ] SemilocalWeightedL2 p :=
  archimedeanDualHardyTitchmarshUnitary.trans (semilocalMulUnitary p hp)

/-- The transported local factor: `υ_∞` intertwines the even physical local factor `θ_p` with
the archimedean spectral local factor. -/
theorem archimedeanPrimeLocalFactor_comp_dualUnitary (p : ℝ) (hp : 1 < p) :
    archimedeanPrimeLocalFactor p ∘L
        (archimedeanDualHardyTitchmarshUnitary : evenSubspace →L[ℂ] ArchimedeanWeightedL2) =
      (archimedeanDualHardyTitchmarshUnitary : evenSubspace →L[ℂ] ArchimedeanWeightedL2) ∘L
        evenPrimeLocalFactor p hp := by
  have h := hardyTitchmarshLocalFactor_archimedean_eq p hp
  rw [hardyTitchmarshLocalFactor] at h
  apply ContinuousLinearMap.ext
  intro f
  rw [← h]
  change unitaryPush archimedeanDualHardyTitchmarshUnitary (evenPrimeLocalFactor p hp)
      (archimedeanDualHardyTitchmarshUnitary f) =
    archimedeanDualHardyTitchmarshUnitary (evenPrimeLocalFactor p hp f)
  rw [unitaryPush_apply, LinearIsometryEquiv.symm_apply_apply]

/-- **The semilocal square** `υ_{∞,p} ∘ θ_p = ι'_p ∘ υ_∞`: the finite Euler factor introduced
by the semilocal dual unitary cancels against the transported local factor, so adjoining the
place `p` commutes with the Hardy--Titchmarsh realizations. -/
theorem semilocalDualHardyTitchmarshUnitary_comp_localFactor (p : ℝ) (hp : 1 < p) :
    (semilocalDualHardyTitchmarshUnitary p hp :
        evenSubspace →L[ℂ] SemilocalWeightedL2 p) ∘L evenPrimeLocalFactor p hp =
      semilocalForwardMap p hp ∘L
        (archimedeanDualHardyTitchmarshUnitary : evenSubspace →L[ℂ] ArchimedeanWeightedL2) := by
  apply ContinuousLinearMap.ext
  intro f
  have hkey := DFunLike.congr_fun (archimedeanPrimeLocalFactor_comp_dualUnitary p hp) f
  change archimedeanPrimeLocalFactor p (archimedeanDualHardyTitchmarshUnitary f) =
    archimedeanDualHardyTitchmarshUnitary (evenPrimeLocalFactor p hp f) at hkey
  change semilocalMulUnitary p hp (archimedeanDualHardyTitchmarshUnitary
      (evenPrimeLocalFactor p hp f)) =
    semilocalMulUnitary p hp (archimedeanPrimeLocalFactor p
      (archimedeanDualHardyTitchmarshUnitary f))
  rw [hkey]

/-- `θ_p` is boundedly invertible (though not unitary), so the square transports invertibly. -/
theorem evenPrimeLocalFactor_isUnit' (p : ℝ) (hp : 1 < p) :
    IsUnit (evenPrimeLocalFactor p hp) :=
  evenPrimeLocalFactor_isUnit p hp

end RHTower
