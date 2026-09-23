import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIISelectedCellCount
import GaloisForLFunctions.RHTower.Sieve.PolylogRpowDomination

/-!
# Canonical Type-II amplitude grid and loss budget

The Type-II cell theorem saves `T^(eps^(2 : ℕ)/10)` before summing cells. This file proves that the
literal dyadic grid and every fixed product-distortion loss are only polylogarithmic, so the full
remaining `T^(eps^(2 : ℕ)/20)` saving survives. Real powers of the fixed polylogarithm are first
majorized by one fixed natural power; no positive height power is spent.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- Number of dyadic amplitude levels needed to cover `[T⁻¹, 1]`. -/
noncomputable def matomakiTeravainenDyadicHeight (T : ℝ) : ℕ :=
  ⌈Real.log T / Real.log 2⌉₊ + 1

/-- Fixed linear-log majorant for the canonical dyadic height. -/
noncomputable def matomakiTeravainenDyadicGridConstant : ℝ :=
  1 / Real.log 2 + 2

/-- The terminal level of the canonical dyadic amplitude grid lies strictly above `1`. -/
theorem lt_two_pow_matomakiTeravainenDyadicHeight {T : ℝ} (hT : 1 ≤ T) :
    T < (2 : ℝ) ^ matomakiTeravainenDyadicHeight T := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hxlt : Real.log T / Real.log 2 <
      (matomakiTeravainenDyadicHeight T : ℝ) := by
    calc
      Real.log T / Real.log 2 ≤
          (⌈Real.log T / Real.log 2⌉₊ : ℕ) := Nat.le_ceil _
      _ < (⌈Real.log T / Real.log 2⌉₊ : ℕ) + 1 := by norm_num
      _ = (matomakiTeravainenDyadicHeight T : ℕ) := by
        simp only [matomakiTeravainenDyadicHeight, Nat.cast_add, Nat.cast_one]
  have hloglt : Real.log T <
      Real.log 2 * (matomakiTeravainenDyadicHeight T : ℝ) := by
    calc
      Real.log T = (Real.log T / Real.log 2) * Real.log 2 := by field_simp
      _ < (matomakiTeravainenDyadicHeight T : ℝ) * Real.log 2 :=
        mul_lt_mul_of_pos_right hxlt hlog2
      _ = Real.log 2 * (matomakiTeravainenDyadicHeight T : ℝ) := by ring
  calc
    T = Real.exp (Real.log T) := (Real.exp_log hT0).symm
    _ < Real.exp (Real.log 2 * (matomakiTeravainenDyadicHeight T : ℝ)) :=
      Real.exp_lt_exp.mpr hloglt
    _ = (2 : ℝ) ^ matomakiTeravainenDyadicHeight T := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]

/-- The canonical dyadic height is bounded by a fixed multiple of `1 + |log T|`. -/
theorem matomakiTeravainen_dyadicHeight_le_polylog {T : ℝ} (hT : 1 ≤ T) :
    (matomakiTeravainenDyadicHeight T : ℝ) ≤
      matomakiTeravainenDyadicGridConstant * (1 + |Real.log T|) := by
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx0 : 0 ≤ Real.log T / Real.log 2 := div_nonneg hlog hlog2.le
  have hceil := Nat.ceil_lt_add_one hx0
  have hheight : (matomakiTeravainenDyadicHeight T : ℝ) <
      Real.log T / Real.log 2 + 2 := by
    dsimp only [matomakiTeravainenDyadicHeight]
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hupper : Real.log T / Real.log 2 + 2 ≤
      matomakiTeravainenDyadicGridConstant * (1 + |Real.log T|) := by
    rw [abs_of_nonneg hlog]
    dsimp only [matomakiTeravainenDyadicGridConstant]
    rw [div_eq_mul_inv, one_div]
    have hdiff : 0 ≤ (Real.log 2)⁻¹ + 2 * Real.log T :=
      add_nonneg (by positivity) (mul_nonneg (by norm_num) hlog)
    nlinarith
  exact hheight.le.trans hupper

/-- The set of nonempty cells never exceeds the full product grid. -/
theorem card_matomakiTeravainenActiveAmplitudeIndices_le
    {α : Type*} [DecidableEq α] (S : Finset α) (F₁ F₂ : α → ℝ)
    (V₁ V₂ : ℝ) (J₁ J₂ : ℕ) :
    (matomakiTeravainenActiveAmplitudeIndices S F₁ F₂ V₁ V₂ J₁ J₂).card ≤
      J₁ * J₂ := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (by
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin])

/-- The actual nonempty canonical product grid has quadratic polylogarithmic size. -/
theorem card_matomakiTeravainenActiveAmplitudeIndices_dyadicHeight_le_polylog
    {α : Type*} [DecidableEq α] (S : Finset α) (F₁ F₂ : α → ℝ)
    (V₁ V₂ : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    ((matomakiTeravainenActiveAmplitudeIndices S F₁ F₂ V₁ V₂
      (matomakiTeravainenDyadicHeight T) (matomakiTeravainenDyadicHeight T)).card : ℝ) ≤
        matomakiTeravainenDyadicGridConstant ^ 2 *
          (1 + |Real.log T|) ^ 2 := by
  have hcard := card_matomakiTeravainenActiveAmplitudeIndices_le S F₁ F₂ V₁ V₂
    (matomakiTeravainenDyadicHeight T) (matomakiTeravainenDyadicHeight T)
  have hcardR :
      ((matomakiTeravainenActiveAmplitudeIndices S F₁ F₂ V₁ V₂
        (matomakiTeravainenDyadicHeight T)
        (matomakiTeravainenDyadicHeight T)).card : ℝ) ≤
          (matomakiTeravainenDyadicHeight T : ℝ) *
            (matomakiTeravainenDyadicHeight T : ℝ) := by
    exact_mod_cast hcard
  have hJ := matomakiTeravainen_dyadicHeight_le_polylog hT
  have hJ0 : 0 ≤ (matomakiTeravainenDyadicHeight T : ℝ) := by positivity
  have hCP0 : 0 ≤
      matomakiTeravainenDyadicGridConstant * (1 + |Real.log T|) := by
    have hconst : 0 ≤ matomakiTeravainenDyadicGridConstant := by
      dsimp only [matomakiTeravainenDyadicGridConstant]
      have : 0 < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    positivity
  calc
    ((matomakiTeravainenActiveAmplitudeIndices S F₁ F₂ V₁ V₂
      (matomakiTeravainenDyadicHeight T)
      (matomakiTeravainenDyadicHeight T)).card : ℝ)
        ≤ (matomakiTeravainenDyadicHeight T : ℝ) *
          (matomakiTeravainenDyadicHeight T : ℝ) := hcardR
    _ ≤ (matomakiTeravainenDyadicGridConstant * (1 + |Real.log T|)) *
        (matomakiTeravainenDyadicGridConstant * (1 + |Real.log T|)) :=
      mul_le_mul hJ hJ hJ0 hCP0
    _ = matomakiTeravainenDyadicGridConstant ^ 2 *
        (1 + |Real.log T|) ^ 2 := by ring

/-- Every fixed grid/product-distortion loss fits inside the remaining Type-II saving. The real
exponent of the product distortion is converted to one fixed natural polylogarithmic exponent,
so the proof spends no positive power of `T`. -/
theorem eventually_matomakiTeravainen_typeII_dyadic_budget
    {eps sigma₀ eta C Cprod Cgrid : ℝ}
    (heps : 0 < eps) (hC : 0 ≤ C) (hCprod : 1 ≤ Cprod) (hCgrid : 0 ≤ Cgrid)
    (k q : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {I corr : ℝ},
        0 ≤ I →
        I ≤ Cgrid * (1 + |Real.log T|) ^ q →
        corr ≤ eta →
        I * (16 * C *
          (Cprod * (1 + |Real.log T|) ^ k) ^ (2 * (sigma₀ + corr))) ≤
            T ^ (eps ^ 2 / 20) := by
  let R : ℝ := 2 * max 0 (sigma₀ + eta)
  let E : ℕ := ⌈(k : ℝ) * R⌉₊
  let D : ℝ := Cgrid * (16 * C * Cprod ^ R)
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact mul_nonneg (by norm_num) (le_max_left _ _)
  have hkR : 0 ≤ (k : ℝ) * R := mul_nonneg (Nat.cast_nonneg k) hR
  have hkRE : (k : ℝ) * R ≤ (E : ℝ) := by
    dsimp only [E]
    exact Nat.le_ceil _
  have hbeta : 0 < eps ^ 2 / 20 := by positivity
  have hdom := eventually_const_mul_rpow_polylog_le_rpow
    (C := D) (α := (0 : ℝ)) (β := eps ^ 2 / 20) (q + E) hbeta
  filter_upwards [hdom, Filter.eventually_ge_atTop (1 : ℝ)] with T hdomT hT
  intro I corr hI0 hI hcorr
  have hP : 1 ≤ 1 + |Real.log T| := by linarith [abs_nonneg (Real.log T)]
  have hP0 : 0 ≤ 1 + |Real.log T| := by positivity
  have hK : 1 ≤ Cprod * (1 + |Real.log T|) ^ k := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ Cprod * (1 + |Real.log T|) ^ k :=
        mul_le_mul hCprod (one_le_pow₀ hP) (by norm_num) (by linarith)
  have hrR : 2 * (sigma₀ + corr) ≤ R := by
    dsimp only [R]
    have := le_max_right (0 : ℝ) (sigma₀ + eta)
    linarith
  have hKr :
      (Cprod * (1 + |Real.log T|) ^ k) ^ (2 * (sigma₀ + corr)) ≤
        (Cprod * (1 + |Real.log T|) ^ k) ^ R :=
    Real.rpow_le_rpow_of_exponent_le hK hrR
  have hpolyR :
      ((1 + |Real.log T|) ^ k : ℝ) ^ R ≤
        (1 + |Real.log T|) ^ E := by
    have hrewrite :
        ((1 + |Real.log T|) ^ k : ℝ) ^ R =
          (1 + |Real.log T|) ^ ((k : ℝ) * R) := by
      rw [← Real.rpow_natCast (1 + |Real.log T|) k, ← Real.rpow_mul hP0]
    rw [hrewrite, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hP hkRE
  have hKR :
      (Cprod * (1 + |Real.log T|) ^ k) ^ R ≤
        Cprod ^ R * (1 + |Real.log T|) ^ E := by
    rw [Real.mul_rpow (by positivity) (by positivity)]
    exact mul_le_mul_of_nonneg_left hpolyR (Real.rpow_nonneg (by positivity) _)
  have hfactor0 : 0 ≤ 16 * C := mul_nonneg (by norm_num) hC
  have hKpow0 : 0 ≤
      (Cprod * (1 + |Real.log T|) ^ k) ^ (2 * (sigma₀ + corr)) :=
    Real.rpow_nonneg (by positivity) _
  calc
    I * (16 * C *
          (Cprod * (1 + |Real.log T|) ^ k) ^ (2 * (sigma₀ + corr)))
        ≤ (Cgrid * (1 + |Real.log T|) ^ q) *
          (16 * C *
            (Cprod * (1 + |Real.log T|) ^ k) ^ (2 * (sigma₀ + corr))) := by
      exact mul_le_mul_of_nonneg_right hI (mul_nonneg hfactor0 hKpow0)
    _ ≤ (Cgrid * (1 + |Real.log T|) ^ q) *
          (16 * C * (Cprod * (1 + |Real.log T|) ^ k) ^ R) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hKr hfactor0) (mul_nonneg hCgrid (by positivity))
    _ ≤ (Cgrid * (1 + |Real.log T|) ^ q) *
          (16 * C * (Cprod ^ R * (1 + |Real.log T|) ^ E)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hKR hfactor0) (mul_nonneg hCgrid (by positivity))
    _ = D * T ^ (0 : ℝ) * (1 + |Real.log T|) ^ (q + E) := by
      simp only [Real.rpow_zero, mul_one, D]
      rw [pow_add]
      ring
    _ ≤ T ^ (eps ^ 2 / 20) := hdomT

end

end RHTower.Sieve
