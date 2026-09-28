import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIIAmplifiedMeanValue

/-!
# One amplitude cell of Matomäki–Teräväinen §5.3

On the cell `E_j` of `U` where `2^{-j-1} ≤ |F₁(1+it)| ≤ 2^{-j}`, `|F₁| ≤ A₁^{-σ₀}` and
`|F₂| ≤ B₂ A₂^{-σ₀}`, both amplified bounds hold (Heath-Brown's Lemma 3.4 against `F₂` and against
`F₁^5`), and the exponent inequality turns their minimum into
`∫_{E_j} |F₁F₂|² ≤ K₀ X^{ε_U/5 + 6η} · 8 X^{-δ₀}`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The constant of the amplified cell bound. -/
def typeIICellConstant (η : ℝ) : ℝ := 2 ^ 10 * 144 * 128 * 2 * heathBrownLemma34Coefficient η

/-- The amplitude cell `E_j`. -/
def typeIICell (U : Set ℝ) (F₁ F₂ : ℝ → ℂ) (j : ℕ) (θ₁ θ₂ : ℝ) : Set ℝ :=
  U ∩ {t | (1 / 2 : ℝ) ^ (j + 1) ≤ ‖F₁ t‖ ∧ ‖F₁ t‖ ≤ (1 / 2 : ℝ) ^ j} ∩
    {t | ‖F₁ t‖ ≤ θ₁} ∩ {t | ‖F₂ t‖ ≤ θ₂}

theorem measurableSet_typeIICell {U : Set ℝ} (hU : MeasurableSet U) {F₁ F₂ : ℝ → ℂ}
    (hF₁ : Continuous F₁) (hF₂ : Continuous F₂) (j : ℕ) (θ₁ θ₂ : ℝ) :
    MeasurableSet (typeIICell U F₁ F₂ j θ₁ θ₂) := by
  refine ((hU.inter ?_).inter ?_).inter ?_
  · exact (isClosed_le continuous_const hF₁.norm).measurableSet.inter
      (isClosed_le hF₁.norm continuous_const).measurableSet
  · exact (isClosed_le hF₁.norm continuous_const).measurableSet
  · exact (isClosed_le hF₂.norm continuous_const).measurableSet

/-- The amplifier is not small where the prime polynomial is not small. -/
theorem one_le_amplifier_perronPoly {B : Finset ℕ} (hBp : ∀ p ∈ B, p.Prime) {P X εU : ℝ}
    (hP : 1 ≤ P) (hB : ∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) {k : ℕ} (hk : 1 ≤ k)
    (hkX : (2 * P) ^ k ≤ X) {t : ℝ}
    (hSt : P ^ (-εU / 10) ≤ ‖∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖) :
    1 ≤ (k.factorial : ℝ) ^ 2 * (P ^ k) ^ (εU / 5) *
      ‖perronPoly (primeSetAmplifierCoeff B k) ⌊X⌋₊ 1 t‖ ^ 2 := by
  rw [perronPoly_primeSetAmplifierCoeff_floor hBp (by linarith) hB hk hkX]
  exact one_le_factorial_sq_mul_rpow_mul_normSq (by linarith) hSt

theorem typeIICellConstant_nonneg (η : ℝ) : 0 ≤ typeIICellConstant η := by
  unfold typeIICellConstant
  have := heathBrownLemma34Coefficient_nonneg η
  positivity

/-- `1 + Z/⌊M⌋ ≤ 2(1 + Z/M)` for `M ≥ 1`, `Z ≥ 0`. -/
theorem one_add_div_floor_le {Z M : ℝ} (hZ : 0 ≤ Z) (hM : 1 ≤ M) :
    1 + Z / (⌊M⌋₊ : ℝ) ≤ 2 * (1 + Z / M) := by
  have hfl := Nat.lt_floor_add_one M
  have h1 : (1 : ℝ) ≤ ⌊M⌋₊ := by exact_mod_cast Nat.le_floor (by exact_mod_cast hM : ((1 : ℕ) : ℝ) ≤ M)
  have hM0 : 0 < M := by linarith
  have hpos : (0 : ℝ) < ⌊M⌋₊ := by linarith
  have hhalf : M ≤ 2 * (⌊M⌋₊ : ℝ) := by linarith
  have : Z / (⌊M⌋₊ : ℝ) ≤ (2 * Z) / M := by
    rw [div_le_div_iff₀ hpos hM0]
    nlinarith
  have h2 : (2 * Z) / M = 2 * (Z / M) := by ring
  linarith

/-- **First cell bound of §5.3**: the long factor against the amplifier. -/
theorem setIntegral_typeII_long_le {X Y z₀ z δ ε : ℝ} (data : MTTypeIIPieceData X Y z₀ z δ ε)
    (hβ : MTUniformDivisorBounded 5 data.β)
    {B : Finset ℕ} (hBp : ∀ p ∈ B, p.Prime) {P a η εU Δ : ℝ} (hP : 1 ≤ P)
    (hB : ∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) {k : ℕ} (hk : 1 ≤ k) (hkX : (2 * P) ^ k ≤ X)
    (hlo : X ^ (1 - η) ≤ P ^ k) (hstars : (P + k) ^ k ≤ P ^ k * X ^ η)
    (hfac : (k.factorial : ℝ) ≤ (P ^ k) ^ (1 / a)) (ha1 : 1 ≤ a) (ha43 : a ≤ 4 / 3)
    (hη : 0 < η) (hη1 : η ≤ 1) (hεU : 0 ≤ εU)
    {E : Set ℝ} (hE : MeasurableSet E) (hEX : E ⊆ Set.Icc (-X) X)
    (hΔ : ∀ t ∈ E, ‖mtTypeIIPrimeFactor data 1 t‖ ≤ Δ)
    (hlam : ∀ t ∈ E, 1 ≤ (k.factorial : ℝ) ^ 2 * (P ^ k) ^ (εU / 5) *
      ‖perronPoly (primeSetAmplifierCoeff B k) ⌊X⌋₊ 1 t‖ ^ 2)
    (hM₂2 : 2 ≤ data.M₂) (hM₂X : data.M₂ ≤ 8 * X) (hX16 : 16 ≤ X)
    (hdiv5 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ X ^ 2 → (n.divisors.card : ℝ) ^ 5 ≤ X ^ η) :
    ∫ t in E, ‖mtTypeIIPrimeFactor data 1 t * mtTypeIILongFactor data 1 t‖ ^ 2 ≤
      typeIICellConstant η * X ^ (εU / 5 + 6 * η) * (Δ ^ 2 * (1 + X ^ (1 / a) / data.M₂)) := by
  have hX0 : 0 < X := by linarith
  have hXη0 : 0 < X ^ η := Real.rpow_pos_of_pos hX0 η
  have hN₂ : 2 ≤ ⌊data.M₂⌋₊ := Nat.le_floor (by exact_mod_cast hM₂2)
  have hcoef₂ : ∀ n, ‖mtRealIntervalAF data.β data.M₂ (2 * data.M₂) n‖ ≤ X ^ η := by
    intro n
    by_cases hc : mtRealIntervalAF data.β data.M₂ (2 * data.M₂) n = 0
    · rw [hc, norm_zero]; exact hXη0.le
    · obtain ⟨hn0, _, hn2⟩ := mtRealIntervalAF_scaleSupported data.β data.M₂ (2 * data.M₂) hc
      refine (norm_mtRealIntervalAF_le_of_uniform hβ _ _ n).trans (hdiv5 n hn0 ?_)
      have : (n : ℝ) ≤ 16 * X := by linarith
      nlinarith
  have hNX : ((⌊data.M₂⌋₊ * 2 ^ 2 : ℕ) : ℝ) ≤ 64 * X := by
    have := Nat.floor_le (by linarith : 0 ≤ data.M₂)
    push_cast; linarith
  have hLS := factorial_sq_mul_integral_amplifier_le hBp hP hB hk hkX hlo hstars hfac ha1 ha43
    hη hη1 (fun n => mtRealIntervalAF data.β data.M₂ (2 * data.M₂) n) hN₂
    (mtTypeIILongFactor_coeff_support data (by linarith)) hcoef₂ hNX
  have hcell := setIntegral_normSq_mul_le_amplified (continuous_perronPoly _ _ 1)
    (continuous_mtTypeIILongFactor data 1) (continuous_perronPoly _ _ 1) hE hEX hΔ
    (by positivity) hlam
  refine hcell.trans ?_
  change (k.factorial : ℝ) ^ 2 * ∫ t in Set.Icc (-X) X,
      ‖perronPoly (primeSetAmplifierCoeff B k) ⌊X⌋₊ 1 t * mtTypeIILongFactor data 1 t‖ ^ 2 ≤ _
    at hLS
  obtain ⟨I, hI⟩ : ∃ I, I = ∫ t in Set.Icc (-X) X,
      ‖perronPoly (primeSetAmplifierCoeff B k) ⌊X⌋₊ 1 t * mtTypeIILongFactor data 1 t‖ ^ 2 :=
    ⟨_, rfl⟩
  rw [← hI]
  rw [← hI] at hLS
  obtain ⟨C, hC⟩ : ∃ C, C = heathBrownLemma34Coefficient η := ⟨_, rfl⟩
  rw [← hC] at hLS
  have hC0 : 0 ≤ C := hC ▸ heathBrownLemma34Coefficient_nonneg η
  have hratio := one_add_div_floor_le (Z := X ^ (1 / a)) (by positivity) (by linarith : 1 ≤ data.M₂)
  have hPk : P ^ k ≤ X := (pow_le_pow_left₀ (by linarith) (by linarith) k).trans hkX
  have hMamp : (P ^ k) ^ (εU / 5) ≤ X ^ (εU / 5) :=
    Real.rpow_le_rpow (by positivity) hPk (by positivity)
  have hXe : X ^ (εU / 5 + 6 * η) = X ^ (εU / 5) * ((X ^ η) ^ 2 * X ^ (4 * η)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0, ← Real.rpow_add hX0]
    ring_nf
  have hconst : typeIICellConstant η = 2 ^ 10 * 144 * 128 * 2 * C := by
    rw [typeIICellConstant, hC]
  rw [hXe, hconst]
  set Q := 1 + X ^ (1 / a) / data.M₂ with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hLS' : (k.factorial : ℝ) ^ 2 * I ≤ 4 * 4 * C * ((X ^ η) ^ 2 * X ^ (4 * η)) * 128 * (2 * Q) := by
    have hW : 0 ≤ 4 * ((2 : ℕ) : ℝ) ^ 2 * C * (X ^ η) ^ 2 * (128 * X ^ (4 * η)) := by
      have : 0 ≤ (X ^ η) ^ 2 * X ^ (4 * η) := by positivity
      have h4 : (0 : ℝ) ≤ 4 * ((2 : ℕ) : ℝ) ^ 2 * 128 := by norm_num
      nlinarith [mul_nonneg hC0 this]
    calc (k.factorial : ℝ) ^ 2 * I
        ≤ 4 * ((2 : ℕ) : ℝ) ^ 2 * C * (X ^ η) ^ 2 *
            (128 * X ^ (4 * η) * (1 + X ^ (1 / a) / (⌊data.M₂⌋₊ : ℝ))) := hLS
      _ = 4 * ((2 : ℕ) : ℝ) ^ 2 * C * (X ^ η) ^ 2 * (128 * X ^ (4 * η)) *
            (1 + X ^ (1 / a) / (⌊data.M₂⌋₊ : ℝ)) := by ring
      _ ≤ 4 * ((2 : ℕ) : ℝ) ^ 2 * C * (X ^ η) ^ 2 * (128 * X ^ (4 * η)) * (2 * Q) :=
          mul_le_mul_of_nonneg_left hratio hW
      _ = 4 * 4 * C * ((X ^ η) ^ 2 * X ^ (4 * η)) * 128 * (2 * Q) := by push_cast; ring
  have hW0 : 0 ≤ (X ^ η) ^ 2 * X ^ (4 * η) := by positivity
  have hΔ2 : 0 ≤ Δ ^ 2 := sq_nonneg Δ
  have hI0 : 0 ≤ I := by
    rw [hI]; exact setIntegral_nonneg measurableSet_Icc fun t _ => sq_nonneg _
  have hkI : 0 ≤ (k.factorial : ℝ) ^ 2 * I := by positivity
  calc Δ ^ 2 * ((k.factorial : ℝ) ^ 2 * (P ^ k) ^ (εU / 5)) * I
      = Δ ^ 2 * (P ^ k) ^ (εU / 5) * ((k.factorial : ℝ) ^ 2 * I) := by ring
    _ ≤ Δ ^ 2 * X ^ (εU / 5) * (4 * 4 * C * ((X ^ η) ^ 2 * X ^ (4 * η)) * 128 * (2 * Q)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hMamp hΔ2) hLS' hkI (by positivity)
    _ = 2 ^ 10 * 144 * 128 * 2 * C * (X ^ (εU / 5) * ((X ^ η) ^ 2 * X ^ (4 * η))) *
          (Δ ^ 2 * Q) / 9216 := by ring
    _ ≤ 2 ^ 10 * 144 * 128 * 2 * C * (X ^ (εU / 5) * ((X ^ η) ^ 2 * X ^ (4 * η))) *
          (Δ ^ 2 * Q) := by
        have hbase : 0 ≤ 2 ^ 10 * 144 * 128 * 2 * C * (X ^ (εU / 5) * ((X ^ η) ^ 2 * X ^ (4 * η))) *
            (Δ ^ 2 * Q) := by
          have : 0 ≤ X ^ (εU / 5) * ((X ^ η) ^ 2 * X ^ (4 * η)) * (Δ ^ 2 * Q) := by positivity
          have h' := mul_nonneg hC0 this
          nlinarith
        linarith

/-- **Second cell bound of §5.3**: the fifth power of the short factor against the amplifier. -/
theorem setIntegral_typeII_short_le {X Y z₀ z δ ε : ℝ} (data : MTTypeIIPieceData X Y z₀ z δ ε)
    (hprime : MTUniformDivisorBounded 0 (mtTypeIIPrimeCoefficient data.indices data.block))
    {B : Finset ℕ} (hBp : ∀ p ∈ B, p.Prime) {P a η εU Δ Γ : ℝ} (hP : 1 ≤ P)
    (hB : ∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) {k : ℕ} (hk : 1 ≤ k) (hkX : (2 * P) ^ k ≤ X)
    (hlo : X ^ (1 - η) ≤ P ^ k) (hstars : (P + k) ^ k ≤ P ^ k * X ^ η)
    (hfac : (k.factorial : ℝ) ≤ (P ^ k) ^ (1 / a)) (ha1 : 1 ≤ a) (ha43 : a ≤ 4 / 3)
    (hη : 0 < η) (hη1 : η ≤ 1) (hεU : 0 ≤ εU)
    {E : Set ℝ} (hE : MeasurableSet E) (hEX : E ⊆ Set.Icc (-X) X) (hΔ0 : 0 < Δ)
    (hΔlo : ∀ t ∈ E, Δ / 2 ≤ ‖mtTypeIIPrimeFactor data 1 t‖)
    (hΔhi : ∀ t ∈ E, ‖mtTypeIIPrimeFactor data 1 t‖ ≤ Δ)
    (hΓ : ∀ t ∈ E, ‖mtTypeIILongFactor data 1 t‖ ≤ Γ)
    (hlam : ∀ t ∈ E, 1 ≤ (k.factorial : ℝ) ^ 2 * (P ^ k) ^ (εU / 5) *
      ‖perronPoly (primeSetAmplifierCoeff B k) ⌊X⌋₊ 1 t‖ ^ 2)
    (hM₁2 : 2 ≤ data.M₁) (hdil : (1 + δ) ^ data.indices.card ≤ 2) (hM₁X : data.M₁ ^ 5 ≤ X)
    (hX64 : 64 ≤ X)
    (hdiv4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ X ^ 2 → (n.divisors.card : ℝ) ^ 4 ≤ X ^ η) :
    ∫ t in E, ‖mtTypeIIPrimeFactor data 1 t * mtTypeIILongFactor data 1 t‖ ^ 2 ≤
      typeIICellConstant η * X ^ (εU / 5 + 6 * η) *
        (Γ ^ 2 * (Δ ^ 8)⁻¹ * (1 + X ^ (1 / a) / data.M₁ ^ 5)) := by
  have hX0 : 0 < X := by linarith
  have hXη0 : 0 < X ^ η := Real.rpow_pos_of_pos hX0 η
  have hM5 : 32 ≤ data.M₁ ^ 5 := by
    have := pow_le_pow_left₀ (by norm_num) hM₁2 5
    norm_num at this; linarith
  have hN₅ : 2 ≤ ⌊data.M₁ ^ 5⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hcoef : ∀ n, ‖(mtTypeIIShortAF data ^ 5) n‖ ≤ X ^ η := by
    intro n
    by_cases hc : (mtTypeIIShortAF data ^ 5) n = 0
    · rw [hc, norm_zero]; exact hXη0.le
    · obtain ⟨_, _, hn2⟩ := mtTypeIIShortAF_pow_five_dyadic data (by linarith) hdil n hc
      have hn0 : 0 < n := (Finset.mem_Icc.1 (mtTypeIIShortAF_pow_five_support_nat data n hc)).1
      refine (norm_mtTypeIIShortAF_pow_five_le data hprime n).trans (hdiv4 n hn0 ?_)
      have hfl := Nat.floor_le (by positivity : (0 : ℝ) ≤ data.M₁ ^ 5)
      have : (n : ℝ) ≤ 64 * X := by
        have h' : (n : ℝ) ≤ ((⌊data.M₁ ^ 5⌋₊ * 2 ^ 6 : ℕ) : ℝ) := by exact_mod_cast hn2
        push_cast at h'; linarith
      nlinarith
  have hNX : ((⌊data.M₁ ^ 5⌋₊ * 2 ^ 6 : ℕ) : ℝ) ≤ 64 * X := by
    have := Nat.floor_le (by positivity : (0 : ℝ) ≤ data.M₁ ^ 5)
    push_cast; linarith
  have hLS := factorial_sq_mul_integral_amplifier_le hBp hP hB hk hkX hlo hstars hfac ha1 ha43
    hη hη1 (fun n => (mtTypeIIShortAF data ^ 5) n) hN₅
    (mtTypeIIShortAF_pow_five_dyadic data (by linarith) hdil) hcoef hNX
  have hcell := setIntegral_normSq_mul_le_amplified_pow (continuous_perronPoly _ _ 1)
    (continuous_mtTypeIILongFactor data 1) (continuous_perronPoly _ _ 1) hE hEX hΔ0 hΔlo hΔhi hΓ
    (by positivity) hlam
  refine hcell.trans ?_
  change 2 ^ 10 * Γ ^ 2 * (Δ ^ 8)⁻¹ * ((k.factorial : ℝ) ^ 2 * (P ^ k) ^ (εU / 5)) *
      ∫ t in Set.Icc (-X) X, ‖perronPoly (primeSetAmplifierCoeff B k) ⌊X⌋₊ 1 t *
        mtTypeIIPrimeFactor data 1 t ^ 5‖ ^ 2 ≤ _
  have hpow : (fun t => ‖perronPoly (primeSetAmplifierCoeff B k) ⌊X⌋₊ 1 t *
      mtTypeIIPrimeFactor data 1 t ^ 5‖ ^ 2) = fun t =>
      ‖perronPoly (primeSetAmplifierCoeff B k) ⌊X⌋₊ 1 t *
        perronPoly (fun n => (mtTypeIIShortAF data ^ 5) n)
          (⌈(1 + δ) ^ data.indices.card * data.M₁⌉₊ ^ 5) 1 t‖ ^ 2 := by
    funext t; rw [mtTypeIIPrimeFactor_pow_five]
  rw [hpow]
  obtain ⟨I, hI⟩ : ∃ I, I = ∫ t in Set.Icc (-X) X,
      ‖perronPoly (primeSetAmplifierCoeff B k) ⌊X⌋₊ 1 t *
        perronPoly (fun n => (mtTypeIIShortAF data ^ 5) n)
          (⌈(1 + δ) ^ data.indices.card * data.M₁⌉₊ ^ 5) 1 t‖ ^ 2 := ⟨_, rfl⟩
  rw [← hI]
  rw [← hI] at hLS
  obtain ⟨C, hC⟩ : ∃ C, C = heathBrownLemma34Coefficient η := ⟨_, rfl⟩
  rw [← hC] at hLS
  have hC0 : 0 ≤ C := hC ▸ heathBrownLemma34Coefficient_nonneg η
  have hratio := one_add_div_floor_le (Z := X ^ (1 / a)) (by positivity) (by linarith : 1 ≤ data.M₁ ^ 5)
  have hPk : P ^ k ≤ X := (pow_le_pow_left₀ (by linarith) (by linarith) k).trans hkX
  have hMamp : (P ^ k) ^ (εU / 5) ≤ X ^ (εU / 5) :=
    Real.rpow_le_rpow (by positivity) hPk (by positivity)
  have hXe : X ^ (εU / 5 + 6 * η) = X ^ (εU / 5) * ((X ^ η) ^ 2 * X ^ (4 * η)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0, ← Real.rpow_add hX0]
    ring_nf
  have hconst : typeIICellConstant η = 2 ^ 10 * 144 * 128 * 2 * C := by
    rw [typeIICellConstant, hC]
  rw [hXe, hconst]
  set Q := 1 + X ^ (1 / a) / data.M₁ ^ 5 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hLS' : (k.factorial : ℝ) ^ 2 * I ≤ 144 * C * ((X ^ η) ^ 2 * X ^ (4 * η)) * 128 * (2 * Q) := by
    have hW : 0 ≤ 4 * ((6 : ℕ) : ℝ) ^ 2 * C * (X ^ η) ^ 2 * (128 * X ^ (4 * η)) := by
      have : 0 ≤ (X ^ η) ^ 2 * X ^ (4 * η) := by positivity
      have h4 : (0 : ℝ) ≤ 4 * ((6 : ℕ) : ℝ) ^ 2 * 128 := by norm_num
      nlinarith [mul_nonneg hC0 this]
    calc (k.factorial : ℝ) ^ 2 * I
        ≤ 4 * ((6 : ℕ) : ℝ) ^ 2 * C * (X ^ η) ^ 2 *
            (128 * X ^ (4 * η) * (1 + X ^ (1 / a) / (⌊data.M₁ ^ 5⌋₊ : ℝ))) := hLS
      _ = 4 * ((6 : ℕ) : ℝ) ^ 2 * C * (X ^ η) ^ 2 * (128 * X ^ (4 * η)) *
            (1 + X ^ (1 / a) / (⌊data.M₁ ^ 5⌋₊ : ℝ)) := by ring
      _ ≤ 4 * ((6 : ℕ) : ℝ) ^ 2 * C * (X ^ η) ^ 2 * (128 * X ^ (4 * η)) * (2 * Q) :=
          mul_le_mul_of_nonneg_left hratio hW
      _ = 144 * C * ((X ^ η) ^ 2 * X ^ (4 * η)) * 128 * (2 * Q) := by push_cast; ring
  have hI0 : 0 ≤ I := by
    rw [hI]; exact setIntegral_nonneg measurableSet_Icc fun t _ => sq_nonneg _
  have hkI : 0 ≤ (k.factorial : ℝ) ^ 2 * I := by positivity
  have hG0 : 0 ≤ 2 ^ 10 * Γ ^ 2 * (Δ ^ 8)⁻¹ := by positivity
  calc 2 ^ 10 * Γ ^ 2 * (Δ ^ 8)⁻¹ * ((k.factorial : ℝ) ^ 2 * (P ^ k) ^ (εU / 5)) * I
      = 2 ^ 10 * Γ ^ 2 * (Δ ^ 8)⁻¹ * (P ^ k) ^ (εU / 5) * ((k.factorial : ℝ) ^ 2 * I) := by ring
    _ ≤ 2 ^ 10 * Γ ^ 2 * (Δ ^ 8)⁻¹ * X ^ (εU / 5) *
          (144 * C * ((X ^ η) ^ 2 * X ^ (4 * η)) * 128 * (2 * Q)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hMamp hG0) hLS' hkI (by positivity)
    _ = 2 ^ 10 * 144 * 128 * 2 * C * (X ^ (εU / 5) * ((X ^ η) ^ 2 * X ^ (4 * η))) *
          (Γ ^ 2 * (Δ ^ 8)⁻¹ * Q) := by ring

/-- **One amplitude cell of §5.3.** -/
theorem setIntegral_typeIICell_le {X Y z₀ z δ ε : ℝ} (data : MTTypeIIPieceData X Y z₀ z δ ε)
    (hprime : MTUniformDivisorBounded 0 (mtTypeIIPrimeCoefficient data.indices data.block))
    (hβ : MTUniformDivisorBounded 5 data.β)
    {B : Finset ℕ} (hBp : ∀ p ∈ B, p.Prime) {P a η εU σ₀ ζ ε₁ δ₀ B₂ : ℝ} (hP : 1 ≤ P)
    (hB : ∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) {k : ℕ} (hk : 1 ≤ k) (hkX : (2 * P) ^ k ≤ X)
    (hlo : X ^ (1 - η) ≤ P ^ k) (hstars : (P + k) ^ k ≤ P ^ k * X ^ η)
    (hfac : (k.factorial : ℝ) ≤ (P ^ k) ^ (1 / a)) (ha1 : 1 ≤ a) (ha43 : a ≤ 4 / 3)
    (hη : 0 < η) (hη1 : η ≤ 1) (hεU : 0 ≤ εU)
    {U : Set ℝ} (hU : MeasurableSet U) (hUX : U ⊆ Set.Icc (-X) X)
    (hS : ∀ t ∈ U, P ^ (-εU / 10) ≤
      ‖∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖)
    (hM₁2 : 2 ≤ data.M₁) (hM₂2 : 2 ≤ data.M₂) (hdil : (1 + δ) ^ data.indices.card ≤ 2)
    (hM₂X : data.M₂ ≤ 8 * X) (hM₁X : data.M₁ ^ 5 ≤ X) (hX64 : 64 ≤ X)
    (hdiv5 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ X ^ 2 → (n.divisors.card : ℝ) ^ 5 ≤ X ^ η)
    (hdiv4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ X ^ 2 → (n.divisors.card : ℝ) ^ 4 ≤ X ^ η)
    (h1 : X ^ (ε / 2) ≤ data.M₁) (h2 : data.M₁ ^ 5 ≤ X ^ (1 / a))
    (h3 : X ^ (1 - ζ) ≤ data.M₁ * data.M₂) (hB₂1 : 1 ≤ B₂) (hB₂ : B₂ ≤ X ^ ζ)
    (hσ₀ : 0 ≤ σ₀) (hσ₀' : σ₀ ≤ 1 / 2) (hζ : 0 ≤ ζ)
    (m1 : δ₀ ≤ σ₀ * ε) (m2 : δ₀ ≤ ε₁) (m3 : 6 / a - 5 - 2 * σ₀ + 5 * ε₁ + 8 * ζ ≤ -δ₀)
    (j : ℕ) :
    ∫ t in typeIICell U (mtTypeIIPrimeFactor data 1) (mtTypeIILongFactor data 1) j
        ((⌈data.M₁⌉₊ : ℝ) ^ (-σ₀)) (B₂ * (⌈data.M₂⌉₊ : ℝ) ^ (-σ₀)),
        ‖mtTypeIIPrimeFactor data 1 t * mtTypeIILongFactor data 1 t‖ ^ 2 ≤
      typeIICellConstant η * X ^ (εU / 5 + 6 * η) * (8 * X ^ (-δ₀)) := by
  have hX0 : 0 < X := by linarith
  have hF₁c : Continuous (mtTypeIIPrimeFactor data 1) := continuous_perronPoly _ _ 1
  have hF₂c := continuous_mtTypeIILongFactor data 1
  have hEm := measurableSet_typeIICell hU hF₁c hF₂c j ((⌈data.M₁⌉₊ : ℝ) ^ (-σ₀))
    (B₂ * (⌈data.M₂⌉₊ : ℝ) ^ (-σ₀))
  obtain ⟨E, hE⟩ : ∃ E, E = typeIICell U (mtTypeIIPrimeFactor data 1) (mtTypeIILongFactor data 1) j
      ((⌈data.M₁⌉₊ : ℝ) ^ (-σ₀)) (B₂ * (⌈data.M₂⌉₊ : ℝ) ^ (-σ₀)) := ⟨_, rfl⟩
  rw [← hE] at hEm ⊢
  have hEU : E ⊆ U := fun t ht => by rw [hE] at ht; exact ht.1.1.1
  have hEX : E ⊆ Set.Icc (-X) X := hEU.trans hUX
  have hK0 : 0 ≤ typeIICellConstant η * X ^ (εU / 5 + 6 * η) :=
    mul_nonneg (typeIICellConstant_nonneg η) (Real.rpow_nonneg hX0.le _)
  have hlam : ∀ t ∈ E, 1 ≤ (k.factorial : ℝ) ^ 2 * (P ^ k) ^ (εU / 5) *
      ‖perronPoly (primeSetAmplifierCoeff B k) ⌊X⌋₊ 1 t‖ ^ 2 := fun t ht =>
    one_le_amplifier_perronPoly hBp hP hB hk hkX (hS t (hEU ht))
  by_cases hne : (1 / 2 : ℝ) ^ (j + 1) ≤ (⌈data.M₁⌉₊ : ℝ) ^ (-σ₀)
  swap
  · have hE0 : E = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun t ht => hne ?_
      rw [hE] at ht
      exact ht.1.1.2.1.trans ht.1.2
    rw [hE0, Measure.restrict_empty, integral_zero_measure]
    exact mul_nonneg hK0 (by positivity)
  have hM₁0 : 0 < data.M₁ := by linarith
  have hM₂0 : 0 < data.M₂ := by linarith
  set Δ : ℝ := (1 / 2 : ℝ) ^ j with hΔdef
  set Γ : ℝ := B₂ * (⌈data.M₂⌉₊ : ℝ) ^ (-σ₀) with hΓdef
  have hΔ0 : 0 < Δ := by positivity
  have hΓpos : 0 < Γ := by positivity
  have hb1 := setIntegral_typeII_long_le data hβ hBp hP hB hk hkX hlo hstars hfac ha1 ha43 hη hη1
    hεU hEm hEX (Δ := Δ) (fun t ht => by rw [hE] at ht; exact ht.1.1.2.2) hlam hM₂2 hM₂X
    (by linarith) hdiv5
  have hb2 := setIntegral_typeII_short_le data hprime hBp hP hB hk hkX hlo hstars hfac ha1 ha43 hη
    hη1 hεU hEm hEX hΔ0 (Γ := Γ)
    (fun t ht => by
      rw [hE] at ht
      have := ht.1.1.2.1
      have h' : Δ / 2 = (1 / 2 : ℝ) ^ (j + 1) := by rw [hΔdef, pow_succ]; ring
      rw [h']; exact this)
    (fun t ht => by rw [hE] at ht; exact ht.1.1.2.2)
    (fun t ht => by rw [hE] at ht; exact ht.2) hlam hM₁2 hdil hM₁X hX64 hdiv4
  have hA₁ : data.M₁ ≤ (⌈data.M₁⌉₊ : ℝ) := Nat.le_ceil _
  have hA₂ : data.M₂ ≤ (⌈data.M₂⌉₊ : ℝ) := Nat.le_ceil _
  have h4 : Δ ≤ 2 * data.M₁ ^ (-σ₀) := by
    have hθ : (⌈data.M₁⌉₊ : ℝ) ^ (-σ₀) ≤ data.M₁ ^ (-σ₀) :=
      Real.rpow_le_rpow_of_nonpos hM₁0 hA₁ (by linarith)
    have : Δ = 2 * (1 / 2 : ℝ) ^ (j + 1) := by rw [hΔdef, pow_succ]; ring
    rw [this]; linarith
  have h5 : Γ ≤ X ^ ζ * data.M₂ ^ (-σ₀) := by
    have : (⌈data.M₂⌉₊ : ℝ) ^ (-σ₀) ≤ data.M₂ ^ (-σ₀) :=
      Real.rpow_le_rpow_of_nonpos hM₂0 hA₂ (by linarith)
    exact mul_le_mul hB₂ this (by positivity) (by positivity)
  have hmin := typeII_cell_min_le (by linarith) hM₁0 hM₂0 hΔ0 hΓpos hσ₀ hσ₀' hζ h1 h2 h3 h4 h5
    m1 m2 m3
  calc ∫ t in E, ‖mtTypeIIPrimeFactor data 1 t * mtTypeIILongFactor data 1 t‖ ^ 2
      ≤ min (typeIICellConstant η * X ^ (εU / 5 + 6 * η) *
            (Δ ^ 2 * (1 + X ^ (1 / a) / data.M₂)))
          (typeIICellConstant η * X ^ (εU / 5 + 6 * η) *
            (Γ ^ 2 * (Δ ^ 8)⁻¹ * (1 + X ^ (1 / a) / data.M₁ ^ 5))) := le_min hb1 hb2
    _ = typeIICellConstant η * X ^ (εU / 5 + 6 * η) *
          min (Δ ^ 2 * (1 + X ^ (1 / a) / data.M₂))
            (Γ ^ 2 * (Δ ^ 8)⁻¹ * (1 + X ^ (1 / a) / data.M₁ ^ 5)) :=
        (mul_min_of_nonneg _ _ hK0).symm
    _ ≤ typeIICellConstant η * X ^ (εU / 5 + 6 * η) * (8 * X ^ (-δ₀)) :=
        mul_le_mul_of_nonneg_left hmin hK0

end

end RHTower.Sieve
