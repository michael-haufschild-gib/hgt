import Mathlib.Analysis.Distribution.Sobolev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The Klein–Gordon propagator symbols

The free Klein–Gordon evolution is, on the Fourier side, multiplication by

`cos(t⟨ξ⟩)`  and  `sin(t⟨ξ⟩)/⟨ξ⟩`,  where `⟨ξ⟩ = √(1 + ‖ξ‖²)`.

Both are **bounded**, so mathlib's `MemSobolev.fourierMultiplierCLM_of_bounded` turns them into
operators preserving every Sobolev space — that is the energy estimate of the evolution. What the
multiplier calculus asks first is that the symbols have temperate growth, and that is the content of
this file.

The Klein–Gordon frequency `⟨ξ⟩` is used rather than the wave frequency `‖ξ‖` deliberately: `‖ξ‖` is
not smooth at the origin, whereas `⟨ξ⟩` is bounded below by `1` and is already known to mathlib to
have temperate growth. Since the physical equation carries a mass term anyway, nothing is lost.

Along the way this file supplies two facts mathlib does not have: the sine and the cosine have
temperate growth. They are the model case of a smooth function all of whose derivatives are bounded.
-/

namespace GaloisForLFunctions.HTGeometry

open Function

open scoped SchwartzMap

/-! ## The trigonometric functions have temperate growth -/

theorem hasTemperateGrowth_realCos : Function.HasTemperateGrowth Real.cos := by
  refine ⟨Real.contDiff_cos, fun n => ⟨0, 1, fun x => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hbound : ‖iteratedDeriv n Real.cos x‖ ≤ 1 := by
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨m, hm⟩ := he
      have hn : n = 2 * m := by omega
      rw [hn, Real.iteratedDeriv_even_cos]
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, Real.norm_eq_abs,
        abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact Real.abs_cos_le_one x
    · obtain ⟨m, hm⟩ := ho
      rw [hm, Real.iteratedDeriv_odd_cos]
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, Real.norm_eq_abs,
        abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact Real.abs_sin_le_one x
  simpa using hbound

theorem hasTemperateGrowth_realSin : Function.HasTemperateGrowth Real.sin := by
  refine ⟨Real.contDiff_sin, fun n => ⟨0, 1, fun x => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hbound : ‖iteratedDeriv n Real.sin x‖ ≤ 1 := by
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨m, hm⟩ := he
      have hn : n = 2 * m := by omega
      rw [hn, Real.iteratedDeriv_even_sin]
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, Real.norm_eq_abs,
        abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact Real.abs_sin_le_one x
    · obtain ⟨m, hm⟩ := ho
      rw [hm, Real.iteratedDeriv_odd_sin]
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, Real.norm_eq_abs,
        abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact Real.abs_cos_le_one x
  simpa using hbound

/-! ## The Klein–Gordon frequency -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Klein–Gordon frequency `⟨ξ⟩ = √(1 + ‖ξ‖²)`. -/
noncomputable def kgFreq (ξ : E) : ℝ := Real.sqrt (1 + ‖ξ‖ ^ 2)

omit [InnerProductSpace ℝ E] in
theorem one_le_kgFreq (ξ : E) : 1 ≤ kgFreq ξ := by
  have h : (1 : ℝ) ≤ 1 + ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg ‖ξ‖]
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + ‖ξ‖ ^ 2) := Real.sqrt_le_sqrt h

omit [InnerProductSpace ℝ E] in
theorem kgFreq_pos (ξ : E) : 0 < kgFreq ξ := lt_of_lt_of_le zero_lt_one (one_le_kgFreq ξ)

omit [InnerProductSpace ℝ E] in
theorem kgFreq_eq_rpow (ξ : E) : kgFreq ξ = (1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) := by
  rw [kgFreq]
  exact Real.sqrt_eq_rpow _

variable (E) in
theorem hasTemperateGrowth_kgFreq : Function.HasTemperateGrowth (kgFreq (E := E)) := by
  have hEq : (kgFreq (E := E)) = fun ξ : E => (1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) := by
    funext ξ
    exact kgFreq_eq_rpow ξ
  rw [hEq]
  exact hasTemperateGrowth_one_add_norm_sq_rpow E (1 / 2 : ℝ)

variable (E) in
theorem hasTemperateGrowth_kgFreq_inv :
    Function.HasTemperateGrowth fun ξ : E => (kgFreq ξ)⁻¹ := by
  have hEq : (fun ξ : E => (kgFreq ξ)⁻¹) = fun ξ : E => (1 + ‖ξ‖ ^ 2) ^ (-(1 / 2) : ℝ) := by
    funext ξ
    rw [kgFreq_eq_rpow, ← Real.rpow_neg (by positivity)]
  rw [hEq]
  exact hasTemperateGrowth_one_add_norm_sq_rpow E (-(1 / 2) : ℝ)

/-! ## The propagator symbols -/

/-- The symbol of the Klein–Gordon cosine propagator. -/
noncomputable def kgCosSymbol (t : ℝ) (ξ : E) : ℂ := ((Real.cos (t * kgFreq ξ) : ℝ) : ℂ)

/-- The symbol of the Klein–Gordon sine propagator. -/
noncomputable def kgSinSymbol (t : ℝ) (ξ : E) : ℂ :=
  ((Real.sin (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ)

theorem hasTemperateGrowth_scaledFreq (t : ℝ) :
    Function.HasTemperateGrowth fun ξ : E => t * kgFreq ξ :=
  (Function.HasTemperateGrowth.const t).mul (hasTemperateGrowth_kgFreq E)

theorem hasTemperateGrowth_kgCosSymbol (t : ℝ) :
    Function.HasTemperateGrowth (kgCosSymbol (E := E) t) := by
  have hreal : Function.HasTemperateGrowth fun ξ : E => Real.cos (t * kgFreq ξ) :=
    hasTemperateGrowth_realCos.comp (hasTemperateGrowth_scaledFreq t)
  exact Complex.hasTemperateGrowth_ofReal.comp hreal

theorem hasTemperateGrowth_kgSinSymbol (t : ℝ) :
    Function.HasTemperateGrowth (kgSinSymbol (E := E) t) := by
  have hsin : Function.HasTemperateGrowth fun ξ : E => Real.sin (t * kgFreq ξ) :=
    hasTemperateGrowth_realSin.comp (hasTemperateGrowth_scaledFreq t)
  have hreal : Function.HasTemperateGrowth
      fun ξ : E => Real.sin (t * kgFreq ξ) / kgFreq ξ := by
    have hEq : (fun ξ : E => Real.sin (t * kgFreq ξ) / kgFreq ξ)
        = fun ξ : E => Real.sin (t * kgFreq ξ) * (kgFreq ξ)⁻¹ := by
      funext ξ
      rw [div_eq_mul_inv]
    rw [hEq]
    exact hsin.mul (hasTemperateGrowth_kgFreq_inv E)
  exact Complex.hasTemperateGrowth_ofReal.comp hreal

omit [InnerProductSpace ℝ E] in
/-- **The cosine symbol is bounded by one.** -/
theorem norm_kgCosSymbol_le (t : ℝ) (ξ : E) : ‖kgCosSymbol t ξ‖ ≤ 1 := by
  rw [kgCosSymbol, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_cos_le_one _

omit [InnerProductSpace ℝ E] in
/-- **The sine symbol is bounded by the elapsed time.** -/
theorem norm_kgSinSymbol_le (t : ℝ) (ξ : E) : ‖kgSinSymbol t ξ‖ ≤ |t| := by
  rw [kgSinSymbol, Complex.norm_real, Real.norm_eq_abs, abs_div]
  have hpos : 0 < kgFreq ξ := kgFreq_pos ξ
  have habs : |kgFreq ξ| = kgFreq ξ := abs_of_pos hpos
  rw [habs, div_le_iff₀ hpos]
  have hsin : |Real.sin (t * kgFreq ξ)| ≤ |t * kgFreq ξ| := Real.abs_sin_le_abs
  calc |Real.sin (t * kgFreq ξ)| ≤ |t * kgFreq ξ| := hsin
    _ = |t| * kgFreq ξ := by rw [abs_mul, habs]

/-! ## The energy estimate -/

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

open TemperedDistribution

/-- A bounded multiplier of temperate growth preserves every Sobolev space. -/
theorem memSobolev_of_bounded_symbol {s : ℝ} {u : 𝓢'(E, F)} (hu : MemSobolev s 2 u)
    {g : E → ℂ} (hg : Function.HasTemperateGrowth g) (hb : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    MemSobolev s 2 (fourierMultiplierCLM F g u) :=
  hu.fourierMultiplierCLM_of_bounded hg hb

/-- **The cosine propagator preserves every Sobolev space**: the energy estimate of the free
Klein–Gordon evolution. -/
theorem memSobolev_kgCosSymbol {s : ℝ} {u : 𝓢'(E, F)} (hu : MemSobolev s 2 u) (t : ℝ) :
    MemSobolev s 2 (fourierMultiplierCLM F (kgCosSymbol t) u) :=
  memSobolev_of_bounded_symbol hu (hasTemperateGrowth_kgCosSymbol t)
    ⟨1, fun ξ => norm_kgCosSymbol_le t ξ⟩

/-- **The sine propagator preserves every Sobolev space.** -/
theorem memSobolev_kgSinSymbol {s : ℝ} {u : 𝓢'(E, F)} (hu : MemSobolev s 2 u) (t : ℝ) :
    MemSobolev s 2 (fourierMultiplierCLM F (kgSinSymbol t) u) :=
  memSobolev_of_bounded_symbol hu (hasTemperateGrowth_kgSinSymbol t)
    ⟨|t|, fun ξ => norm_kgSinSymbol_le t ξ⟩

end GaloisForLFunctions.HTGeometry
