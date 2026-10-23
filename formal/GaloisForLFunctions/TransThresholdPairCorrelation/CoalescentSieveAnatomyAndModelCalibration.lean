import GaloisForLFunctions.TransThresholdPairCorrelation.FormFactorThresholdAndShiftInequality
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Coalescent Sieve Anatomy, Frullani Cancellation, and Model-Sequence Calibration

This module resolves Open Problem 3 (*Close pairs in short multiplicative intervals*) together with
Research Topics 2 (*The coalescent band as a sieve problem*) and 3 (*Calibration*) of
`TransThresholdPairCorrelation`:

1. **Multiplicative-to-additive linearization in short multiplicative intervals
   (`log_one_add_div_bounds`, `coalescent_term_linearization_bound`,
   `coalescent_sum_linearization_bound`):**
   For `0 < m` and `0 ≤ h`, the logarithmic shift `θ(m, h) = log(1 + h/m)` satisfies the sharp
   two-sided sandwich
   `h / (m + h) ≤ log(1 + h/m) ≤ h / m` and `0 ≤ h/m − log(1 + h/m) ≤ h² / m²`,
   while the symmetric weight `1 / √(m(m + h))` satisfies
   `0 ≤ 1/m − 1/√(m(m + h)) ≤ h / (2 m²)`.
   Consequently, in the coalescent band `0 ≤ h ≤ c m / T`, replacing the logarithmic correlation
   `Σ_{m,h} Λ(m)Λ(m + h) (m(m + h))^{-1/2} K(T log(1 + h/m))` by the additive shifted-prime
   correlation `Σ_{m,h} Λ(m)Λ(m + h) m⁻¹ K(T h / m)` incurs an explicit error at most
   `((L_K c² + M_K c / 2) / T) Σ_{m,h} Λ(m)Λ(m + h) m⁻¹`.

2. **Frullani cancellation of the Poisson main term and favourable sign of the Hardy–Littlewood
   logarithmic deficit (`dyadicCosineKernel_eq_div`, `integral_sin_div_two_mul`,
   `abs_integral_dyadic_frullani_le`, `hl_coalescent_deficit_integral`):**
   The signed dyadic difference-frequency kernel `f_dyadic(u) = ∫₁² cos(t u) dt = (sin 2u − sin u)/u`
   satisfies the exact Frullani scale identity
   `∫_ε^R (sin 2u − sin u)/u du = ∫_R^{2R} (sin u)/u du − ∫_ε^{2ε} (sin u)/u du`,
   coupled with the integration-by-parts bound `|∫_R^{2R} (sin u)/u du| ≤ 2/R`, yielding
   `|∫_ε^R (sin 2u − sin u)/u du| ≤ ε + 2/R → 0`.
   Thus the continuum Poisson linear term `H` in the Hardy–Littlewood cumulative pair weight
   `C_HL(H) = H − ½ log H + O(1)` integrates to zero against the signed dyadic kernel, while the
   Hardy–Littlewood singular-series logarithmic deficit `−½(y − l)` integrates against the
   trans-threshold autocorrelation weight `g(y) = L − y` on `[l, L]` to
   `∫_l^L (L − y)(−(y − l)) dy = −(L − l)³/6 < 0`,
   producing the strictly negative normalized prime-surplus ratio `−(λ − 1)³/(3λ²) < 0`
   (equal to `−1/144 < 0` at `λ = 4/3`) before any error term is estimated.

3. **General-`λ` prime-surplus bridge and five-model calibration
   (`frobeniusFormFactor_eq_diag_add_generalPrimeSurplusRatio`,
   `generalPrimeSurplusRatio_affineTransModel`, `calibration_five_models_four_thirds`):**
   For every bandwidth `λ ≥ 1`, the spectral Frobenius form factor decomposes into the prime
   diagonal `1/λ + λ/3` plus `generalPrimeSurplusRatio F λ = (2/λ²) ∫₁^λ (λ − α)(F(α) − α) dα`.
   Evaluating this functional on the two-parameter affine family `F_{β,γ}(α) = β + γ(α − 1)` for
   `α ≥ 1` gives the exact calibration law
   `generalPrimeSurplusRatio(F_{β,γ}, λ) = ((λ − 1)²/λ²)(β − 1) + ((λ − 1)³/(3λ²))(γ − 1)`,
   which calibrates five benchmark models at `λ = 4/3`:
   - *Hardy–Littlewood / Function-Field / GUE (`β = 1, γ = 0`):* `−1/144 < 0` (slack `1/16` below `1/18`);
   - *Uncorrelated / Diagonal-Only (`β = 1, γ = 1`):* `0` (slack `1/18`);
   - *Naive Poisson Off-Diagonal without HL Repulsion (`β = 2, γ = 1`):* `+1/16 > 1/18` (fails the
     `1/18` budget by `1/144`, proving that the budget genuinely uses arithmetic repulsion);
   - *Spectral Sieve (`β = Υ, γ = 0`):* `(9Υ − 10)/144 ≤ 1/18 ↔ Υ ≤ 2` (the exact factor-two parity
     threshold);
   - *Unsigned Additive Sieve (`β = 1 + Υ, γ = 1`):* `Υ/16 ≤ 1/18 ↔ Υ ≤ 8/9 < 1` (impossible for
     any upper-bound sieve `Υ ≥ 1`, and equal to `1/8 > 1/18` at `Υ = 2`).
-/

open MeasureTheory Real Set intervalIntegral Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-! ## 1. Multiplicative-to-Additive Linearization in Short Multiplicative Intervals -/

/-- **Sharp two-sided sandwich for the multiplicative logarithmic shift `log(1 + h/m)`:**
for `0 < m` and `0 ≤ h`, `h / (m + h) ≤ log(1 + h / m) ≤ h / m`. -/
theorem log_one_add_div_bounds {m h : ℝ} (hm : 0 < m) (hh : 0 ≤ h) :
    h / (m + h) ≤ Real.log (1 + h / m) ∧ Real.log (1 + h / m) ≤ h / m := by
  have hmh : 0 < m + h := by linarith
  have h1 : 0 < 1 + h / m := by positivity
  have hup : Real.log (1 + h / m) ≤ h / m := by
    have := Real.log_le_sub_one_of_pos h1
    linarith
  have hlo : h / (m + h) ≤ Real.log (1 + h / m) := by
    have heq : 1 + h / m = (m + h) / m := by field_simp
    have hinv : Real.log ((m + h) / m) = -Real.log (m / (m + h)) := by
      rw [← Real.log_inv, inv_div]
    have h2 : Real.log (m / (m + h)) ≤ m / (m + h) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hm hmh)
    have h3 : m / (m + h) - 1 = -(h / (m + h)) := by field_simp; ring
    rw [heq, hinv]
    linarith
  exact ⟨hlo, hup⟩

/-- **Quadratic Taylor remainder bound for `log(1 + h/m)`:**
for `0 < m` and `0 ≤ h`, `0 ≤ h/m − log(1 + h/m) ≤ h² / (m(m + h)) ≤ h² / m²`. -/
theorem sub_log_one_add_div_bounds {m h : ℝ} (hm : 0 < m) (hh : 0 ≤ h) :
    0 ≤ h / m - Real.log (1 + h / m) ∧
      h / m - Real.log (1 + h / m) ≤ h ^ 2 / (m * (m + h)) ∧
      h ^ 2 / (m * (m + h)) ≤ h ^ 2 / m ^ 2 := by
  obtain ⟨hlo, hup⟩ := log_one_add_div_bounds hm hh
  have hmh : 0 < m + h := by linarith
  have hdiff : h / m - h / (m + h) = h ^ 2 / (m * (m + h)) := by field_simp; ring
  have hle : h ^ 2 / (m * (m + h)) ≤ h ^ 2 / m ^ 2 := by
    rw [sq m]
    exact div_le_div_of_nonneg_left (sq_nonneg h) (mul_pos hm hm)
      (mul_le_mul_of_nonneg_left (by linarith) hm.le)
  exact ⟨by linarith, by linarith, hle⟩

/-- **Scaled coalescent phase linearization:** in the coalescent band `0 ≤ h ≤ c * m / T`
(`0 < T`, `0 < m`, `0 ≤ c`), the scaled phase `T * log(1 + h/m)` differs from the linear shift
ratio `T * h / m` by at most `c² / T`. -/
theorem coalescent_phase_linearization_error {T m h c : ℝ} (hT : 0 < T) (hm : 0 < m)
    (hh0 : 0 ≤ h) (hhc : h ≤ c * m / T) :
    0 ≤ T * (h / m) - T * Real.log (1 + h / m) ∧
      T * (h / m) - T * Real.log (1 + h / m) ≤ c ^ 2 / T := by
  obtain ⟨h1, h2, h3⟩ := sub_log_one_add_div_bounds hm hh0
  have hsub : T * (h / m) - T * Real.log (1 + h / m) = T * (h / m - Real.log (1 + h / m)) := by
    ring
  rw [hsub]
  refine ⟨mul_nonneg hT.le h1, ?_⟩
  have hhm : h / m ≤ c / T := by
    rw [div_le_iff₀ hm, div_mul_eq_mul_div]
    exact hhc
  have hsq : h ^ 2 / m ^ 2 ≤ (c / T) ^ 2 := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (div_nonneg hh0 hm.le) hhm 2
  calc T * (h / m - Real.log (1 + h / m))
      ≤ T * (h ^ 2 / m ^ 2) := mul_le_mul_of_nonneg_left (h2.trans h3) hT.le
    _ ≤ T * (c / T) ^ 2 := mul_le_mul_of_nonneg_left hsq hT.le
    _ = c ^ 2 / T := by field_simp

/-- **Geometric-to-harmonic weight linearization:** for `0 < m` and `0 ≤ h`,
`0 ≤ 1/m − 1/√(m(m + h)) ≤ h / (2 m²)`. -/
theorem inv_sub_inv_sqrt_mul_bounds {m h : ℝ} (hm : 0 < m) (hh : 0 ≤ h) :
    0 ≤ 1 / m - 1 / Real.sqrt (m * (m + h)) ∧
      1 / m - 1 / Real.sqrt (m * (m + h)) ≤ h / (2 * m ^ 2) := by
  set S := Real.sqrt (m * (m + h)) with hSdef
  have hmh : m ^ 2 ≤ m * (m + h) := by nlinarith
  have hmS : m ≤ S := by
    rw [← Real.sqrt_sq hm.le, hSdef]
    exact Real.sqrt_le_sqrt hmh
  have hS0 : 0 < S := lt_of_lt_of_le hm hmS
  have hnonneg : 0 ≤ 1 / m - 1 / S := by
    rw [sub_nonneg, one_div_le_one_div hS0 hm]
    exact hmS
  refine ⟨hnonneg, ?_⟩
  have hSsq : S ^ 2 = m * (m + h) := Real.sq_sqrt (by positivity)
  have hconj : (S - m) * (S + m) = m * h := by
    calc (S - m) * (S + m) = S ^ 2 - m ^ 2 := by ring
      _ = m * (m + h) - m ^ 2 := by rw [hSsq]
      _ = m * h := by ring
  have hSm : S - m = m * h / (S + m) := by
    rw [eq_div_iff (by positivity : S + m ≠ 0)]
    exact hconj
  have hdiff : 1 / m - 1 / S = h / (S * (S + m)) := by
    have h1 : 1 / m - 1 / S = (S - m) / (m * S) := by field_simp
    rw [h1, hSm]
    field_simp
  rw [hdiff]
  have hden : 2 * m ^ 2 ≤ S * (S + m) := by nlinarith
  exact div_le_div_of_nonneg_left hh (by positivity) hden

/-- **Pointwise coalescent term linearization bound:** for any kernel `K : ℝ → ℝ` with Lipschitz
constant `L_K ≥ 0` and uniform bound `|K u| ≤ M_K`, and any `0 < T`, `0 < m`, `0 ≤ c`,
`0 ≤ h ≤ c * m / T`, replacing `(m(m + h))^{-1/2} K(T log(1 + h/m))` by `m⁻¹ K(T h / m)` incurs an
error at most `m⁻¹ * ((L_K * c² + M_K * c / 2) / T)`. -/
theorem coalescent_term_linearization_bound {K : ℝ → ℝ} {L_K M_K T m h c : ℝ}
    (hL : 0 ≤ L_K) (hM : 0 ≤ M_K)
    (hLip : ∀ u v : ℝ, |K u - K v| ≤ L_K * |u - v|)
    (hBnd : ∀ u : ℝ, |K u| ≤ M_K)
    (hT : 0 < T) (hm : 0 < m) (hc : 0 ≤ c) (hh0 : 0 ≤ h) (hhc : h ≤ c * m / T) :
    |1 / Real.sqrt (m * (m + h)) * K (T * Real.log (1 + h / m)) - 1 / m * K (T * (h / m))|
      ≤ 1 / m * ((L_K * c ^ 2 + M_K * c / 2) / T) := by
  set u := T * Real.log (1 + h / m)
  set v := T * (h / m)
  set S := Real.sqrt (m * (m + h))
  obtain ⟨hvu0, hvu⟩ := coalescent_phase_linearization_error hT hm hh0 hhc
  obtain ⟨hS0, hS⟩ := inv_sub_inv_sqrt_mul_bounds hm hh0
  have hmS : m ≤ S := by
    rw [← Real.sqrt_sq hm.le]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hSpos : 0 < S := lt_of_lt_of_le hm hmS
  have hinvS : 1 / S ≤ 1 / m := (one_div_le_one_div hSpos hm).mpr hmS
  have hsplit : 1 / S * K u - 1 / m * K v = 1 / S * (K u - K v) - (1 / m - 1 / S) * K v := by ring
  have habs_uv : |u - v| ≤ c ^ 2 / T := by
    rw [abs_sub_comm, abs_of_nonneg hvu0]
    exact hvu
  have h1 : |1 / S * (K u - K v)| ≤ 1 / m * (L_K * (c ^ 2 / T)) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / S)]
    calc 1 / S * |K u - K v|
        ≤ 1 / m * (L_K * |u - v|) := mul_le_mul hinvS (hLip u v) (abs_nonneg _) (by positivity)
      _ ≤ 1 / m * (L_K * (c ^ 2 / T)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left habs_uv hL) (by positivity)
  have h2 : |(1 / m - 1 / S) * K v| ≤ 1 / m * (M_K * c / (2 * T)) := by
    rw [abs_mul, abs_of_nonneg hS0]
    have hhm : 1 / m - 1 / S ≤ 1 / m * (c / (2 * T)) := by
      refine hS.trans ?_
      calc h / (2 * m ^ 2)
          ≤ (c * m / T) / (2 * m ^ 2) :=
            div_le_div_of_nonneg_right hhc (by positivity)
        _ = 1 / m * (c / (2 * T)) := by field_simp
    calc (1 / m - 1 / S) * |K v|
        ≤ (1 / m * (c / (2 * T))) * M_K := mul_le_mul hhm (hBnd v) (abs_nonneg _) (by positivity)
      _ = 1 / m * (M_K * c / (2 * T)) := by ring
  rw [hsplit]
  calc |1 / S * (K u - K v) - (1 / m - 1 / S) * K v|
      ≤ |1 / S * (K u - K v)| + |(1 / m - 1 / S) * K v| := abs_sub _ _
    _ ≤ 1 / m * (L_K * (c ^ 2 / T)) + 1 / m * (M_K * c / (2 * T)) := add_le_add h1 h2
    _ = 1 / m * ((L_K * c ^ 2 + M_K * c / 2) / T) := by ring

/-- **Global coalescent correlation linearization theorem:** summing over any finite set of
pairs `(m, h)` in the coalescent band `1 ≤ m`, `0 ≤ h ≤ c m / T` with nonnegative arithmetic
weights `w(m, h) = Λ(m)Λ(m + h)`, the difference between the logarithmic correlation sum and the
linearized shifted-prime correlation sum is bounded by
`((L_K c² + M_K c / 2) / T) Σ_{(m,h)} Λ(m)Λ(m + h) / m`. -/
theorem coalescent_sum_linearization_bound {K : ℝ → ℝ} {L_K M_K T c : ℝ}
    (P : Finset (ℕ × ℕ))
    (hL : 0 ≤ L_K) (hM : 0 ≤ M_K)
    (hLip : ∀ u v : ℝ, |K u - K v| ≤ L_K * |u - v|)
    (hBnd : ∀ u : ℝ, |K u| ≤ M_K)
    (hT : 0 < T) (hc : 0 ≤ c)
    (hP : ∀ p ∈ P, 1 ≤ p.1 ∧ (p.2 : ℝ) ≤ c * (p.1 : ℝ) / T) :
    |(∑ p ∈ P, (Λ p.1 : ℝ) * (Λ (p.1 + p.2) : ℝ) *
        (1 / Real.sqrt ((p.1 : ℝ) * ((p.1 : ℝ) + (p.2 : ℝ))) *
          K (T * Real.log (1 + (p.2 : ℝ) / (p.1 : ℝ)))))
      - ∑ p ∈ P, (Λ p.1 : ℝ) * (Λ (p.1 + p.2) : ℝ) *
          (1 / (p.1 : ℝ) * K (T * ((p.2 : ℝ) / (p.1 : ℝ))))|
      ≤ (L_K * c ^ 2 + M_K * c / 2) / T *
          ∑ p ∈ P, (Λ p.1 : ℝ) * (Λ (p.1 + p.2) : ℝ) * (1 / (p.1 : ℝ)) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  obtain ⟨hm1, hhc⟩ := hP p hp
  have hm0 : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast hm1
  have hh0 : (0 : ℝ) ≤ (p.2 : ℝ) := Nat.cast_nonneg _
  have hw0 : 0 ≤ (Λ p.1 : ℝ) * (Λ (p.1 + p.2) : ℝ) :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
  have hsub : (Λ p.1 : ℝ) * (Λ (p.1 + p.2) : ℝ) *
        (1 / Real.sqrt ((p.1 : ℝ) * ((p.1 : ℝ) + (p.2 : ℝ))) *
          K (T * Real.log (1 + (p.2 : ℝ) / (p.1 : ℝ)))) -
      (Λ p.1 : ℝ) * (Λ (p.1 + p.2) : ℝ) *
        (1 / (p.1 : ℝ) * K (T * ((p.2 : ℝ) / (p.1 : ℝ))))
      = (Λ p.1 : ℝ) * (Λ (p.1 + p.2) : ℝ) *
        (1 / Real.sqrt ((p.1 : ℝ) * ((p.1 : ℝ) + (p.2 : ℝ))) *
          K (T * Real.log (1 + (p.2 : ℝ) / (p.1 : ℝ))) -
          1 / (p.1 : ℝ) * K (T * ((p.2 : ℝ) / (p.1 : ℝ)))) := by ring
  rw [hsub, abs_mul, abs_of_nonneg hw0]
  have hterm := coalescent_term_linearization_bound hL hM hLip hBnd hT hm0 hc hh0 hhc
  calc (Λ p.1 : ℝ) * (Λ (p.1 + p.2) : ℝ) *
        |1 / Real.sqrt ((p.1 : ℝ) * ((p.1 : ℝ) + (p.2 : ℝ))) *
          K (T * Real.log (1 + (p.2 : ℝ) / (p.1 : ℝ))) -
          1 / (p.1 : ℝ) * K (T * ((p.2 : ℝ) / (p.1 : ℝ)))|
      ≤ (Λ p.1 : ℝ) * (Λ (p.1 + p.2) : ℝ) *
          (1 / (p.1 : ℝ) * ((L_K * c ^ 2 + M_K * c / 2) / T)) :=
        mul_le_mul_of_nonneg_left hterm hw0
    _ = (L_K * c ^ 2 + M_K * c / 2) / T *
          ((Λ p.1 : ℝ) * (Λ (p.1 + p.2) : ℝ) * (1 / (p.1 : ℝ))) := by ring

/-! ## 2. The Signed Dyadic Difference-Frequency Kernel and Frullani Cancellation -/

/-- The smooth dyadic difference-frequency kernel `f_dyadic(u) = ∫₁² cos(t u) dt`, which equals
`1` at `u = 0` and `(sin(2u) − sin u) / u` for `u ≠ 0`. -/
def dyadicCosineKernel (u : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..2, Real.cos (t * u)

/-- At `u = 0`, `dyadicCosineKernel 0 = 1`. -/
theorem dyadicCosineKernel_zero : dyadicCosineKernel 0 = 1 := by
  unfold dyadicCosineKernel
  simp
  norm_num

/-- For `u ≠ 0`, `dyadicCosineKernel u = (sin(2u) − sin u) / u`. -/
theorem dyadicCosineKernel_eq_div {u : ℝ} (hu : u ≠ 0) :
    dyadicCosineKernel u = (Real.sin (2 * u) - Real.sin u) / u := by
  unfold dyadicCosineKernel
  rw [intervalIntegral.integral_comp_mul_right (fun t => Real.cos t) hu, integral_cos,
    smul_eq_mul, one_mul, inv_mul_eq_div, mul_comm 2 u]

/-- **Exact Frullani scale identity for the dyadic difference-frequency kernel:**
for any `0 < ε` and `0 < R`,
`∫_ε^R (sin(2u) − sin u)/u du = ∫_R^{2R} (sin u)/u du − ∫_ε^{2ε} (sin u)/u du`. -/
theorem integral_sin_div_two_mul {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    (∫ u in ε..R, (Real.sin (2 * u) - Real.sin u) / u)
      = (∫ u in R..(2 * R), Real.sin u / u) - ∫ u in ε..(2 * ε), Real.sin u / u := by
  have hcont : ContinuousOn (fun u : ℝ => Real.sin u / u) {0}ᶜ :=
    Real.continuous_sin.continuousOn.div continuousOn_id fun x hx => hx
  have hsub : ∀ a b : ℝ, 0 < a → 0 < b → Set.uIcc a b ⊆ ({0}ᶜ : Set ℝ) := by
    intro a b ha hb x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have hmin : min a b ≤ x := hx.1
    have hpos : 0 < min a b := lt_min ha hb
    linarith
  have hint : ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable (fun u : ℝ => Real.sin u / u) volume a b :=
    fun a b ha hb => (hcont.mono (hsub a b ha hb)).intervalIntegrable
  have hint2 : IntervalIntegrable (fun u : ℝ => Real.sin (2 * u) / u) volume ε R := by
    have hcont2 : ContinuousOn (fun u : ℝ => Real.sin (2 * u) / u) {0}ᶜ :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn.div
        continuousOn_id fun x hx => hx
    exact (hcont2.mono (hsub ε R hε hR)).intervalIntegrable
  have hsplit : (∫ u in ε..R, (Real.sin (2 * u) - Real.sin u) / u)
      = (∫ u in ε..R, Real.sin (2 * u) / u) - ∫ u in ε..R, Real.sin u / u := by
    have heq : (fun u : ℝ => (Real.sin (2 * u) - Real.sin u) / u)
        = fun u => Real.sin (2 * u) / u - Real.sin u / u := by funext u; ring
    rw [heq, intervalIntegral.integral_sub hint2 (hint ε R hε hR)]
  have hscale : (∫ u in ε..R, Real.sin (2 * u) / u) = ∫ u in (2 * ε)..(2 * R), Real.sin u / u := by
    have hcomp := intervalIntegral.integral_comp_mul_right (fun u : ℝ => Real.sin u / u)
      (by norm_num : (2 : ℝ) ≠ 0) (a := ε) (b := R)
    simp only [smul_eq_mul, mul_comm _ (2 : ℝ)] at hcomp
    calc ∫ u in ε..R, Real.sin (2 * u) / u
        = 2 * ∫ u in ε..R, Real.sin (2 * u) / (2 * u) := by
          rw [← intervalIntegral.integral_const_mul]
          refine intervalIntegral.integral_congr fun u _ => ?_
          ring
      _ = 2 * (2⁻¹ * ∫ u in (2 * ε)..(2 * R), Real.sin u / u) := by rw [← hcomp]
      _ = ∫ u in (2 * ε)..(2 * R), Real.sin u / u := by ring
  rw [hsplit, hscale]
  have hadj1 := intervalIntegral.integral_add_adjacent_intervals
    (hint ε R hε hR) (hint R (2 * R) hR (by positivity))
  have hadj2 := intervalIntegral.integral_add_adjacent_intervals
    (hint ε (2 * ε) hε (by positivity)) (hint (2 * ε) (2 * R) (by positivity) (by positivity))
  linarith

/-- **Integration-by-parts identity for the Dirichlet tail `∫_R^{2R} (sin u)/u du`:**
for `0 < R`, `∫_R^{2R} (sin u / u + cos u / u²) du = cos R / R − cos(2R) / (2R)`. -/
theorem integral_sin_div_add_cos_div_sq {R : ℝ} (hR : 0 < R) :
    (∫ u in R..(2 * R), (Real.sin u / u + Real.cos u / u ^ 2))
      = Real.cos R / R - Real.cos (2 * R) / (2 * R) := by
  have hRle : R ≤ 2 * R := by linarith
  have hderiv : ∀ u ∈ Set.uIcc R (2 * R),
      HasDerivAt (fun u : ℝ => -(Real.cos u / u)) (Real.sin u / u + Real.cos u / u ^ 2) u := by
    intro u hu
    rw [Set.uIcc_of_le hRle] at hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    have hd := ((Real.hasDerivAt_cos u).div (hasDerivAt_id u) hu0).neg
    refine hd.congr_deriv ?_
    simp only [id_eq]
    field_simp
    ring
  have hcont : ContinuousOn (fun u : ℝ => Real.sin u / u + Real.cos u / u ^ 2)
      (Set.uIcc R (2 * R)) := by
    rw [Set.uIcc_of_le hRle]
    refine ContinuousOn.add ?_ ?_
    · exact Real.continuous_sin.continuousOn.div continuousOn_id fun u hu => by linarith [hu.1]
    · exact Real.continuous_cos.continuousOn.div (continuousOn_id.pow 2) fun u hu =>
        pow_ne_zero 2 (by linarith [hu.1])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  ring

/-- **Tail bound `|∫_R^{2R} (sin u)/u du| ≤ 2/R` for `R > 0`.** -/
theorem abs_integral_sin_div_two_mul_le {R : ℝ} (hR : 0 < R) :
    |∫ u in R..(2 * R), Real.sin u / u| ≤ 2 / R := by
  have hRle : R ≤ 2 * R := by linarith
  have hint1 : IntervalIntegrable (fun u : ℝ => Real.sin u / u) volume R (2 * R) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hRle]
    exact Real.continuous_sin.continuousOn.div continuousOn_id fun u hu => by linarith [hu.1]
  have hint2 : IntervalIntegrable (fun u : ℝ => Real.cos u / u ^ 2) volume R (2 * R) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hRle]
    exact Real.continuous_cos.continuousOn.div (continuousOn_id.pow 2) fun u hu =>
      pow_ne_zero 2 (by linarith [hu.1])
  have hint_inv : IntervalIntegrable (fun u : ℝ => 1 / u ^ 2) volume R (2 * R) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hRle]
    exact continuousOn_const.div (continuousOn_id.pow 2) fun u hu =>
      pow_ne_zero 2 (by linarith [hu.1])
  have hparts := integral_sin_div_add_cos_div_sq hR
  rw [intervalIntegral.integral_add hint1 hint2] at hparts
  have heq : (∫ u in R..(2 * R), Real.sin u / u)
      = Real.cos R / R - Real.cos (2 * R) / (2 * R) - ∫ u in R..(2 * R), Real.cos u / u ^ 2 := by
    linarith
  have hinv_eval : (∫ u in R..(2 * R), 1 / u ^ 2) = 1 / (2 * R) := by
    have hderiv : ∀ u ∈ Set.uIcc R (2 * R), HasDerivAt (fun u : ℝ => -(1 / u)) (1 / u ^ 2) u := by
      intro u hu
      rw [Set.uIcc_of_le hRle] at hu
      have hu0 : u ≠ 0 := by linarith [hu.1]
      have hd := ((hasDerivAt_const u (1 : ℝ)).div (hasDerivAt_id u) hu0).neg
      refine hd.congr_deriv ?_
      simp only [id_eq]
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_inv]
    field_simp
    ring
  have hcos_le : |∫ u in R..(2 * R), Real.cos u / u ^ 2| ≤ 1 / (2 * R) := by
    rw [← hinv_eval]
    refine (intervalIntegral.abs_integral_le_integral_abs hRle).trans ?_
    refine intervalIntegral.integral_mono_on hRle hint2.abs hint_inv fun u hu => ?_
    have hupos : 0 < u := by linarith [hu.1]
    rw [abs_div, abs_of_pos (sq_pos_of_pos hupos)]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one u) (sq_nonneg u)
  have hc1 : |Real.cos R / R| ≤ 1 / R := by
    rw [abs_div, abs_of_pos hR]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one R) hR.le
  have h2R : 0 < 2 * R := by linarith
  have hc2 : |Real.cos (2 * R) / (2 * R)| ≤ 1 / (2 * R) := by
    rw [abs_div, abs_of_pos h2R]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one (2 * R)) h2R.le
  rw [heq]
  calc |Real.cos R / R - Real.cos (2 * R) / (2 * R) - ∫ u in R..(2 * R), Real.cos u / u ^ 2|
      ≤ |Real.cos R / R - Real.cos (2 * R) / (2 * R)| + |∫ u in R..(2 * R), Real.cos u / u ^ 2| :=
        abs_sub _ _
    _ ≤ |Real.cos R / R| + |Real.cos (2 * R) / (2 * R)| + |∫ u in R..(2 * R), Real.cos u / u ^ 2| := by
        linarith [abs_sub (Real.cos R / R) (Real.cos (2 * R) / (2 * R))]
    _ ≤ 1 / R + 1 / (2 * R) + 1 / (2 * R) := by linarith
    _ = 2 / R := by ring

/-- **Frullani cancellation bound for the Poisson main term (`|∫_ε^R (sin 2u − sin u)/u du| ≤ ε + 2/R`):**
the continuum Poisson linear term in the Hardy–Littlewood pair density integrates to zero against
the signed dyadic window kernel as `ε → 0⁺` and `R → ∞`. -/
theorem abs_integral_dyadic_frullani_le {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    |∫ u in ε..R, (Real.sin (2 * u) - Real.sin u) / u| ≤ ε + 2 / R := by
  rw [integral_sin_div_two_mul hε hR]
  have hεle : ε ≤ 2 * ε := by linarith
  have hintε : IntervalIntegrable (fun u : ℝ => Real.sin u / u) volume ε (2 * ε) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hεle]
    exact Real.continuous_sin.continuousOn.div continuousOn_id fun u hu => by linarith [hu.1]
  have hsmall : |∫ u in ε..(2 * ε), Real.sin u / u| ≤ ε := by
    calc |∫ u in ε..(2 * ε), Real.sin u / u|
        ≤ ∫ u in ε..(2 * ε), |Real.sin u / u| := intervalIntegral.abs_integral_le_integral_abs hεle
      _ ≤ ∫ _ in ε..(2 * ε), (1 : ℝ) := by
          refine intervalIntegral.integral_mono_on hεle hintε.abs intervalIntegrable_const
            fun u hu => ?_
          have hu0 : 0 < u := by linarith [hu.1]
          rw [abs_div, abs_of_pos hu0, div_le_one hu0]
          exact (Real.abs_sin_le_abs u).trans (le_of_eq (abs_of_pos hu0))
      _ = ε := by simp [intervalIntegral.integral_const]; ring
  have htail := abs_integral_sin_div_two_mul_le hR
  calc |(∫ u in R..(2 * R), Real.sin u / u) - ∫ u in ε..(2 * ε), Real.sin u / u|
      ≤ |∫ u in R..(2 * R), Real.sin u / u| + |∫ u in ε..(2 * ε), Real.sin u / u| := abs_sub _ _
    _ ≤ 2 / R + ε := add_le_add htail hsmall
    _ = ε + 2 / R := by ring

/-- **Favourable sign of the Hardy–Littlewood logarithmic deficit in the coalescent band:**
integrating the trans-threshold singular-series deficit `−(y − l)` against the autocorrelation
weight `g(y) = L − y` over `[l, L]` (`l < L`) gives `−(L − l)³ / 6 < 0`, and normalizing by
`½ L² l` (`L = λ l`, `λ > 1`) yields `−(λ − 1)³ / (3 λ²) < 0` (`= −1/144` at `λ = 4/3`). -/
theorem hl_coalescent_deficit_integral {l L : ℝ} (hlL : l < L) :
    (∫ y in l..L, (L - y) * (-(y - l))) = -((L - l) ^ 3 / 6) ∧
      -((L - l) ^ 3 / 6) < 0 := by
  have hderiv : ∀ y ∈ Set.uIcc l L,
      HasDerivAt (fun y : ℝ => -((y - l) ^ 2 * L / 2 - (y - l) ^ 3 / 3 - l * (y - l) ^ 2 / 2))
        ((L - y) * (-(y - l))) y := by
    intro y _
    have hd1 : HasDerivAt (fun y : ℝ => y - l) 1 y := (hasDerivAt_id y).sub_const l
    have hd2 := ((hd1.pow 2).mul_const L).div_const 2
    have hd3 := (hd1.pow 3).div_const 3
    have hd4 := ((hd1.pow 2).const_mul l).div_const 2
    exact ((hd2.sub hd3).sub hd4).neg.congr_deriv (by ring)
  have hcont : Continuous (fun y : ℝ => (L - y) * (-(y - l))) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable l L)]
  have hpos : 0 < L - l := sub_pos.mpr hlL
  exact ⟨by ring, neg_lt_zero.mpr (by positivity)⟩

/-! ## 3. General-`λ` Prime-Surplus Bridge and Five-Model Calibration -/

/-- The normalized prime-pair surplus ratio at general bandwidth `λ`:
`generalPrimeSurplusRatio F λ = (2/λ²) ∫₁^λ (λ − α) (F(α) − α) dα`. -/
def generalPrimeSurplusRatio (F : ℝ → ℝ) (lam : ℝ) : ℝ :=
  (2 / lam ^ 2) * ∫ α in (1 : ℝ)..lam, (lam - α) * (F α - α)

/-- **Exact general-`λ` reconciliation of the spectral form factor and the prime-side diagonal:**
for every `λ ≠ 0` and continuous `F` with `F(α) = α` on `[0, 1]`,
`frobeniusFormFactor F λ = (1/λ + λ/3) + generalPrimeSurplusRatio F λ`, and
`generalPrimeSurplusRatio F λ = (2/λ²) transThresholdIntegral F λ − (λ − 1)²(λ + 2)/(3λ²)`. -/
theorem frobeniusFormFactor_eq_diag_add_generalPrimeSurplusRatio {F : ℝ → ℝ} {lam : ℝ}
    (hlam : lam ≠ 0) (hF_cont : Continuous F) (hF_sub : ∀ α ∈ Icc (0 : ℝ) 1, F α = α) :
    frobeniusFormFactor F lam = (1 / lam + lam / 3) + generalPrimeSurplusRatio F lam ∧
      generalPrimeSurplusRatio F lam
        = (2 / lam ^ 2) * transThresholdIntegral F lam - (lam - 1) ^ 2 * (lam + 2) / (3 * lam ^ 2) := by
  have hsplit := frobeniusFormFactor_eq_split hlam hF_cont hF_sub
  unfold generalPrimeSurplusRatio transThresholdIntegral at *
  have hintF : IntervalIntegrable (fun α => (lam - α) * F α) volume 1 lam :=
    ((by fun_prop : Continuous fun α => (lam - α) * F α)).intervalIntegrable 1 lam
  have hintα : IntervalIntegrable (fun α => (lam - α) * α) volume 1 lam :=
    ((by fun_prop : Continuous fun α => (lam - α) * α)).intervalIntegrable 1 lam
  have heq : (fun α : ℝ => (lam - α) * (F α - α)) = fun α => (lam - α) * F α - (lam - α) * α := by
    funext α; ring
  have hdiag : ∫ α in (1 : ℝ)..lam, (lam - α) * α = (lam - 1) ^ 2 * (lam + 2) / 6 := by
    have e : (fun α : ℝ => (lam - α) * α) = fun α => lam * α - α ^ 2 := by funext α; ring
    rw [e, intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun α : ℝ => lam * α).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun α : ℝ => α ^ 2).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_id, integral_pow]
    ring
  have hsurp : (2 / lam ^ 2) * (∫ α in (1 : ℝ)..lam, (lam - α) * (F α - α))
      = (2 / lam ^ 2) * (∫ α in (1 : ℝ)..lam, (lam - α) * F α)
        - (lam - 1) ^ 2 * (lam + 2) / (3 * lam ^ 2) := by
    rw [heq, intervalIntegral.integral_sub hintF hintα, hdiag]
    field_simp
    ring
  refine ⟨?_, hsurp⟩
  rw [hsplit, hsurp]
  field_simp
  ring

/-- At `λ = 4/3`, `generalPrimeSurplusRatio F (4/3)` agrees identically with
`primeSurplusRatioOfIntegral (transThresholdIntegral F (4/3))`. -/
theorem generalPrimeSurplusRatio_four_thirds_eq {F : ℝ → ℝ} (hF_cont : Continuous F)
    (hF_sub : ∀ α ∈ Icc (0 : ℝ) 1, F α = α) :
    generalPrimeSurplusRatio F (4 / 3)
      = primeSurplusRatioOfIntegral (transThresholdIntegral F (4 / 3)) := by
  rw [(frobeniusFormFactor_eq_diag_add_generalPrimeSurplusRatio (by norm_num) hF_cont hF_sub).2]
  unfold primeSurplusRatioOfIntegral
  ring

/-- The two-parameter affine trans-threshold pair-correlation model `F_{β,γ}(α) = β + γ(α − 1)`
for `α ≥ 1` (with `F_{β,γ}(α) = α` on `[0, 1]` when `β = 1`, or evaluated directly on `[1, λ]`). -/
def affineTransModel (β γ α : ℝ) : ℝ :=
  β + γ * (α - 1)

/-- **Master calibration formula for the two-parameter affine model `F_{β,γ}(α) = β + γ(α − 1)`:**
for every `λ ≠ 0`,
`generalPrimeSurplusRatio (affineTransModel β γ) λ = ((λ − 1)²/λ²)(β − 1) + ((λ − 1)³/(3λ²))(γ − 1)`. -/
theorem generalPrimeSurplusRatio_affineTransModel (β γ : ℝ) {lam : ℝ} (hlam : lam ≠ 0) :
    generalPrimeSurplusRatio (affineTransModel β γ) lam
      = (lam - 1) ^ 2 / lam ^ 2 * (β - 1) + (lam - 1) ^ 3 / (3 * lam ^ 2) * (γ - 1) := by
  unfold generalPrimeSurplusRatio affineTransModel
  have hderiv : ∀ α ∈ Set.uIcc (1 : ℝ) lam,
      HasDerivAt (fun α : ℝ =>
        (β - 1) * ((lam - 1) * (α - 1) - (α - 1) ^ 2 / 2) +
          (γ - 1) * ((lam - 1) * (α - 1) ^ 2 / 2 - (α - 1) ^ 3 / 3))
        ((lam - α) * (β + γ * (α - 1) - α)) α := by
    intro α _
    have hd : HasDerivAt (fun α : ℝ => α - 1) 1 α := (hasDerivAt_id α).sub_const 1
    have h1 := ((hd.const_mul (lam - 1)).sub ((hd.pow 2).div_const 2)).const_mul (β - 1)
    have h2 := (((hd.pow 2).const_mul (lam - 1)).div_const 2 |>.sub ((hd.pow 3).div_const 3)).const_mul (γ - 1)
    exact (h1.add h2).congr_deriv (by ring)
  have hcont : Continuous (fun α : ℝ => (lam - α) * (β + γ * (α - 1) - α)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 1 lam)]
  field_simp
  ring

/-- **Complete Five-Model Calibration Theorem at bandwidth `λ = 4/3`:**
1. *Hardy–Littlewood / Function-Field / GUE (`β = 1, γ = 0`):* surplus is `−1/144 < 0` (slack `1/16`
   below `1/18`).
2. *Uncorrelated / Diagonal-Only (`β = 1, γ = 1`):* surplus is `0` (slack `1/18`).
3. *Naive Poisson Off-Diagonal without HL Repulsion (`β = 2, γ = 1`):* surplus is `1/16 > 1/18`
   (exceeds the `1/18` budget by `1/144`, proving that the `1/18` budget genuinely relies on
   Hardy–Littlewood arithmetic repulsion).
4. *Spectral Sieve (`β = Υ, γ = 0`):* surplus is `(9Υ − 10)/144`, which satisfies `≤ 1/18` if and
   only if `Υ ≤ 2` (the exact factor-two sieve parity threshold).
5. *Unsigned Additive Sieve (`β = 1 + Υ, γ = 1`):* surplus is `Υ/16`, which satisfies `≤ 1/18` if
   and only if `Υ ≤ 8/9 < 1` (impossible for any upper-bound sieve `Υ ≥ 1`, and equal to `1/8 > 1/18`
   at `Υ = 2`). -/
theorem calibration_five_models_four_thirds (Υ : ℝ) :
    generalPrimeSurplusRatio (affineTransModel 1 0) (4 / 3) = -(1 / 144) ∧
    generalPrimeSurplusRatio (affineTransModel 1 1) (4 / 3) = 0 ∧
    generalPrimeSurplusRatio (affineTransModel 2 1) (4 / 3) = 1 / 16 ∧
    (1 / 16 : ℝ) - 1 / 18 = 1 / 144 ∧
    generalPrimeSurplusRatio (affineTransModel Υ 0) (4 / 3) = (9 * Υ - 10) / 144 ∧
    (generalPrimeSurplusRatio (affineTransModel Υ 0) (4 / 3) ≤ 1 / 18 ↔ Υ ≤ 2) ∧
    generalPrimeSurplusRatio (affineTransModel (1 + Υ) 1) (4 / 3) = Υ / 16 ∧
    (generalPrimeSurplusRatio (affineTransModel (1 + Υ) 1) (4 / 3) ≤ 1 / 18 ↔ Υ ≤ 8 / 9) := by
  have h1 := generalPrimeSurplusRatio_affineTransModel 1 0 (lam := 4 / 3) (by norm_num)
  have h2 := generalPrimeSurplusRatio_affineTransModel 1 1 (lam := 4 / 3) (by norm_num)
  have h3 := generalPrimeSurplusRatio_affineTransModel 2 1 (lam := 4 / 3) (by norm_num)
  have h4 := generalPrimeSurplusRatio_affineTransModel Υ 0 (lam := 4 / 3) (by norm_num)
  have h5 := generalPrimeSurplusRatio_affineTransModel (1 + Υ) 1 (lam := 4 / 3) (by norm_num)
  refine ⟨by linarith, by linarith, by linarith, by norm_num, by linarith, ?_, by linarith, ?_⟩
  · rw [h4]; constructor <;> intro h <;> linarith
  · rw [h5]; constructor <;> intro h <;> linarith

end GaloisForLFunctions.TransThresholdPairCorrelation
