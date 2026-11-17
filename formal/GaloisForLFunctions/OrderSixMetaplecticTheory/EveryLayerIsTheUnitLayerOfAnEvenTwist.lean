import GaloisForLFunctions.OrderSixMetaplecticTheory.TheWeilIndexIsAKleinCombination

/-!
# Every layer is the unit layer of an even twist

Three characters on `O` move layers without touching the cube frequencies:

* `μ_λ(c) = [λ ∤ c]` (`unramifiedChar`) keeps the unramified frequencies;
* `ξ_{h₀}(c) = (h₀/c)₃²` on `λ ∤ c` (`layerChar`) moves the layer `h₀` to the unit layer:
  `S^ψ_{h₀} = S^{ψξ_{h₀}}_1`;
* the sign `η₃(c) = ±1` with `c³ ≡ ±1 mod λ²` (`cubeSign`) is trivial on primary elements and odd.

The unramified twisted theta square `D₀^ψ(s) = Σ_{λ ∤ h} ψ(h)T(h)²(4π|ξ_h|)^{−s}` sees only the unit layer
(`T(u) = 0` unless `u = ±1`; `unramifiedTwist_eq`):

`D₀^ψ(s) = C̄² Z_{ψ³}(3s/2 − 1) (ψ(1) + ψ(−1)) (4π|ξ₁|)^{−s} S^ψ_1(s/2)`.

A twist of odd parity kills its theta square (`twistDirichletG_eq_zero_of_odd`), but `η₃` flips the parity without
changing a layer. So every layer of every bounded multiplicative twist is the unit layer of an **even** unramified
twisted theta square (`layer_eq_unramifiedTwist`):

`2 C̄² Z_{ψ³}(3s/2 − 1)(4π|ξ₁|)^{−s} S^ψ_{uλ^m}(s/2) = D₀^{ψ'}(s)`,  `ψ' = ψ ξ_{uλ^m}` or `ψ ξ_{uλ^m} η₃`.

No layer, in particular no layer of the order-six family, is hidden by parity, and the unknown 3-adic coefficients
`T(uλ^m)` drop out: the family at every column is a combination of unramified theta squares twisted by
characters with 3-adic components `ξ_{ω²λ²}`, `η₃`.
-/

noncomputable section

open MeasureTheory UniqueFactorizationMonoid
open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open FamilyContinuationTheory MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicKubota MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicJacobi
  SpectralTheoryOfTheCubicCover

/-! ### Three characters -/

theorem lambda_not_dvd_one : ¬ lambda ∣ (1 : O) := fun h => lambda_not_isUnit (isUnit_of_dvd_one h)

theorem lambda_not_dvd_of_primary {g : O} (hg : lambda ^ 2 ∣ g - 1) : ¬ lambda ∣ g := by
  intro h
  have h1 : lambda ∣ g - 1 := (dvd_pow_self lambda (by decide : (2 : ℕ) ≠ 0)).trans hg
  exact lambda_not_dvd_one (by simpa using dvd_sub h h1)

/-- `μ_λ(c) = [λ ∤ c]`. -/
def unramifiedChar : O →* ℂ where
  toFun c := if lambda ∣ c then 0 else 1
  map_one' := by rw [if_neg lambda_not_dvd_one]
  map_mul' a b := by
    by_cases ha : lambda ∣ a
    · rw [if_pos (dvd_mul_of_dvd_left ha b), if_pos ha, zero_mul]
    by_cases hb : lambda ∣ b
    · rw [if_pos (dvd_mul_of_dvd_right hb a), if_pos hb, mul_zero]
    rw [if_neg (fun h => (residue_lambda_prime.dvd_or_dvd h).elim ha hb), if_neg ha, if_neg hb, mul_one]

theorem unramifiedChar_apply_of_primary {g : O} (hg : lambda ^ 2 ∣ g - 1) : unramifiedChar g = 1 := by
  change (if lambda ∣ g then 0 else 1) = (1 : ℂ)
  rw [if_neg (lambda_not_dvd_of_primary hg)]

theorem unramifiedChar_norm_le (c : O) : ‖unramifiedChar c‖ ≤ 1 := by
  change ‖(if lambda ∣ c then 0 else 1 : ℂ)‖ ≤ 1
  split_ifs <;> simp

theorem lambda_dvd_three : lambda ∣ (3 : O) :=
  ⟨-(lambda * omega ^ 2), by linear_combination omega ^ 2 * lambda_sq_eq' - 3 * omega_primitive.pow_eq_one⟩

theorem not_lambda_sq_dvd_two : ¬ lambda ^ 2 ∣ (2 : O) := by
  intro h
  have h2 : lambda ∣ (2 : O) := (dvd_pow_self lambda (by decide : (2 : ℕ) ≠ 0)).trans h
  have h3 := dvd_sub lambda_dvd_three h2
  rw [show (3 : O) - 2 = 1 by norm_num] at h3
  exact lambda_not_dvd_one h3

/-- Away from `λ` a cube is `±1` modulo `λ²`: `c = u g` with `g` primary and `u³ = ±1`. -/
theorem cube_sign (c : O) (hc : ¬ lambda ∣ c) : lambda ^ 2 ∣ c ^ 3 - 1 ∨ lambda ^ 2 ∣ c ^ 3 + 1 := by
  have hc0 : c ≠ 0 := fun h => hc (h ▸ dvd_zero _)
  obtain ⟨⟨u, m, I, hI⟩, hp⟩ := frequencySplit_surjective c hc0
  simp only [frequencySplit] at hp
  have hm : m = 0 := by
    by_contra hm
    exact hc (hp ▸ dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self lambda hm) _) _)
  subst hm
  have hg := (primaryIdealGenerator_spec I hI).2
  set g := primaryIdealGenerator I
  have hg3 : lambda ^ 2 ∣ g ^ 3 - 1 := by
    obtain ⟨k, hk⟩ := hg
    exact ⟨k * (g ^ 2 + g + 1), by linear_combination (g ^ 2 + g + 1) * hk⟩
  have h6 : ((u : O) ^ 3) ^ 2 = 1 := by
    rw [← pow_mul]
    exact CanonicalRowCompletion.unit_pow_six u
  rw [← hp, pow_zero, mul_one, mul_pow]
  obtain ⟨k, hk⟩ := hg3
  rcases mul_self_eq_one_iff.mp (show (u : O) ^ 3 * (u : O) ^ 3 = 1 by rw [← sq]; exact h6) with hu | hu
  · left
    exact ⟨(u : O) ^ 3 * k, by rw [hu]; linear_combination hk⟩
  · right
    exact ⟨-k, by rw [hu]; linear_combination -hk⟩

/-- The sign `η₃(c) = ±1` with `c³ ≡ ±1 mod λ²`; `0` on `λ ∣ c`. -/
def cubeSign : O →* ℂ where
  toFun c := if lambda ∣ c then 0 else if lambda ^ 2 ∣ c ^ 3 - 1 then 1 else -1
  map_one' := by rw [if_neg lambda_not_dvd_one, if_pos (by simp)]
  map_mul' a b := by
    by_cases ha : lambda ∣ a
    · rw [if_pos (dvd_mul_of_dvd_left ha b), if_pos ha, zero_mul]
    by_cases hb : lambda ∣ b
    · rw [if_pos (dvd_mul_of_dvd_right hb a), if_pos hb, mul_zero]
    have hab : ¬ lambda ∣ a * b := fun h => (residue_lambda_prime.dvd_or_dvd h).elim ha hb
    rw [if_neg hab, if_neg ha, if_neg hb]
    have hnot : ∀ x : O, lambda ^ 2 ∣ x - 1 → ¬ lambda ^ 2 ∣ x + 1 := fun x h1 h2 => by
      have h3 := dvd_sub h2 h1
      rw [show x + 1 - (x - 1) = (2 : O) by ring] at h3
      exact not_lambda_sq_dvd_two h3
    rcases cube_sign a ha with ha1 | ha1 <;> rcases cube_sign b hb with hb1 | hb1
    · have : lambda ^ 2 ∣ (a * b) ^ 3 - 1 := by
        rw [mul_pow, show a ^ 3 * b ^ 3 - 1 = (a ^ 3 - 1) * b ^ 3 + (b ^ 3 - 1) by ring]
        exact dvd_add (dvd_mul_of_dvd_left ha1 _) hb1
      rw [if_pos this, if_pos ha1, if_pos hb1, mul_one]
    · have : lambda ^ 2 ∣ (a * b) ^ 3 + 1 := by
        rw [mul_pow, show a ^ 3 * b ^ 3 + 1 = (a ^ 3 - 1) * b ^ 3 + (b ^ 3 + 1) by ring]
        exact dvd_add (dvd_mul_of_dvd_left ha1 _) hb1
      rw [if_neg (fun h => hnot _ h this), if_pos ha1, if_neg (fun h => hnot _ h hb1), one_mul]
    · have : lambda ^ 2 ∣ (a * b) ^ 3 + 1 := by
        rw [mul_pow, show a ^ 3 * b ^ 3 + 1 = (a ^ 3 + 1) * b ^ 3 - (b ^ 3 - 1) by ring]
        exact dvd_sub (dvd_mul_of_dvd_left ha1 _) hb1
      rw [if_neg (fun h => hnot _ h this), if_neg (fun h => hnot _ h ha1), if_pos hb1, mul_one]
    · have : lambda ^ 2 ∣ (a * b) ^ 3 - 1 := by
        rw [mul_pow, show a ^ 3 * b ^ 3 - 1 = (a ^ 3 + 1) * b ^ 3 - (b ^ 3 + 1) by ring]
        exact dvd_sub (dvd_mul_of_dvd_left ha1 _) hb1
      rw [if_pos this, if_neg (fun h => hnot _ h ha1), if_neg (fun h => hnot _ h hb1)]
      norm_num

theorem cubeSign_apply_of_primary {g : O} (hg : lambda ^ 2 ∣ g - 1) : cubeSign g = 1 := by
  change (if lambda ∣ g then 0 else if lambda ^ 2 ∣ g ^ 3 - 1 then 1 else -1) = (1 : ℂ)
  obtain ⟨k, hk⟩ := hg
  rw [if_neg (lambda_not_dvd_of_primary ⟨k, hk⟩),
    if_pos ⟨k * (g ^ 2 + g + 1), by linear_combination (g ^ 2 + g + 1) * hk⟩]

theorem cubeSign_neg_one : cubeSign (-1) = -1 := by
  change (if lambda ∣ (-1 : O) then 0 else if lambda ^ 2 ∣ (-1 : O) ^ 3 - 1 then 1 else -1) = (-1 : ℂ)
  have h1 : ¬ lambda ∣ (-1 : O) := fun h => lambda_not_dvd_one (by simpa using h.neg_right)
  have h2 : ¬ lambda ^ 2 ∣ (-1 : O) ^ 3 - 1 := fun h => by
    have h3 := h.neg_right
    rw [show -((-1 : O) ^ 3 - 1) = 2 by ring] at h3
    exact not_lambda_sq_dvd_two h3
  rw [if_neg h1, if_neg h2]

theorem cubeSign_norm_le (c : O) : ‖cubeSign c‖ ≤ 1 := by
  change ‖(if lambda ∣ c then 0 else if lambda ^ 2 ∣ c ^ 3 - 1 then 1 else -1 : ℂ)‖ ≤ 1
  split_ifs <;> simp

theorem symbol_eq_gen (h₀ c : O) (hc : ¬ lambda ∣ c) :
    symbol h₀ c = symbol h₀ (primaryIdealGenerator (Ideal.span {c})) := by
  have hg : primaryIdealGenerator (Ideal.span {c}) ≠ 0 := (primaryIdealGenerator_span_ne_zero_iff c).mpr hc
  unfold symbol
  rw [(primaryIdealGenerator_spec _ hg).1]

/-- `ξ_{h₀}(c) = (h₀/c)₃²` on `λ ∤ c`, `0` on `λ ∣ c`. -/
def layerChar (h₀ : O) : O →* ℂ where
  toFun c := if lambda ∣ c then 0 else ringComplex (symbol h₀ c) ^ 2
  map_one' := by rw [if_neg lambda_not_dvd_one, symbol_one, map_one, one_pow]
  map_mul' a b := by
    by_cases ha : lambda ∣ a
    · rw [if_pos (dvd_mul_of_dvd_left ha b), if_pos ha, zero_mul]
    by_cases hb : lambda ∣ b
    · rw [if_pos (dvd_mul_of_dvd_right hb a), if_pos hb, mul_zero]
    rw [if_neg (fun h => (residue_lambda_prime.dvd_or_dvd h).elim ha hb), if_neg ha, if_neg hb,
      symbol_mul_denominator, map_mul, mul_pow]

theorem layerChar_apply_of_primary (h₀ : O) {g : O} (hg : lambda ^ 2 ∣ g - 1) :
    layerChar h₀ g = ringComplex (symbol h₀ g) ^ 2 := by
  change (if lambda ∣ g then 0 else ringComplex (symbol h₀ g) ^ 2) = _
  rw [if_neg (lambda_not_dvd_of_primary hg)]

theorem layerChar_neg_one (h₀ : O) : layerChar h₀ (-1) = 1 := by
  change (if lambda ∣ (-1 : O) then 0 else ringComplex (symbol h₀ (-1)) ^ 2) = (1 : ℂ)
  have h1 : ¬ lambda ∣ (-1 : O) := fun h => lambda_not_dvd_one (by simpa using h.neg_right)
  rw [if_neg h1]
  have : symbol h₀ (-1) = 1 := by
    unfold symbol
    rw [Ideal.span_singleton_neg, ← symbol, symbol_one]
  rw [this, map_one, one_pow]

theorem layerChar_norm_le (h₀ c : O) : ‖layerChar h₀ c‖ ≤ 1 := by
  change ‖(if lambda ∣ c then 0 else ringComplex (symbol h₀ c) ^ 2 : ℂ)‖ ≤ 1
  split_ifs with hc
  · simp
  · rw [symbol_eq_gen h₀ c hc, norm_pow]
    have hg : primaryIdealGenerator (Ideal.span {c}) ≠ 0 := (primaryIdealGenerator_span_ne_zero_iff c).mpr hc
    exact pow_le_one₀ (norm_nonneg _) (norm_symbol_le _ _ (primaryIdealGenerator_spec _ hg).2)

/-! ### Odd twists vanish -/

/-- **An odd twist kills the theta square:** `T(−h) = T(h)`. -/
theorem twistDirichletG_eq_zero_of_odd (ψ : O →* ℂ) (hodd : ψ (-1) = -1) (s : ℂ) : twistDirichletG ψ s = 0 :=
  besselDirichlet_eq_zero_of_odd _ (fun h => by
    rw [rationalSourceResidualFourierCoefficient_neg, show -h = -1 * h by ring, map_mul, hodd]
    ring) s

/-! ### The unramified twisted theta square sees the unit layer -/

theorem sourceCoefficient_one_ne_zero : rationalSourceResidualFourierCoefficient 1 ≠ 0 := fun hz =>
  rationalSourceThetaScalar_ne_zero (by rw [rationalSourceThetaScalar, hz, star_zero])

theorem twistedSquarefreeSeriesG_neg_one (ψ : O →* ℂ) (w : ℂ) :
    twistedSquarefreeSeriesG ψ (-1) w = twistedSquarefreeSeriesG ψ 1 w := by
  unfold twistedSquarefreeSeriesG
  refine tsum_congr fun A => ?_
  split_ifs with hsq
  · by_cases hA : primaryIdealGenerator A = 0
    · rw [unramifiedNormWeight_of_bad w A hA, zero_mul, zero_mul]
    · have hp := (primaryIdealGenerator_spec A hA).2
      rw [symbol_neg_one hp, symbol_one_numerator _ hp, map_one]
  · rfl

theorem cubeZetaG_mul_eq (ψ χ : O →* ℂ) (hχ : ∀ g : O, lambda ^ 2 ∣ g - 1 → χ g ^ 3 = 1) (z : ℂ) :
    cubeZetaG (ψ * χ) z = cubeZetaG ψ z := by
  unfold cubeZetaG
  refine tsum_congr fun B => ?_
  by_cases hB : primaryIdealGenerator B = 0
  · rw [unramifiedNormWeight_of_bad z B hB, zero_mul, zero_mul]
  · rw [MonoidHom.mul_apply, mul_pow, hχ _ (primaryIdealGenerator_spec B hB).2, mul_one]

theorem twistedSquarefreeSeriesG_mul_eq (ψ χ : O →* ℂ) (hχ : ∀ g : O, lambda ^ 2 ∣ g - 1 → χ g = 1)
    (h₀ : O) (w : ℂ) : twistedSquarefreeSeriesG (ψ * χ) h₀ w = twistedSquarefreeSeriesG ψ h₀ w := by
  unfold twistedSquarefreeSeriesG
  refine tsum_congr fun A => ?_
  split_ifs
  · by_cases hA : primaryIdealGenerator A = 0
    · rw [unramifiedNormWeight_of_bad w A hA, zero_mul, zero_mul]
    · rw [MonoidHom.mul_apply, hχ _ (primaryIdealGenerator_spec A hA).2, mul_one]
  · rfl

/-- **The unramified twisted theta square is the unit layer.** For `Re s > 4`,
`D₀^ψ(s) = C̄² Z_{ψ³}(3s/2 − 1)(ψ(1) + ψ(−1))(4π|ξ₁|)^{−s} S^ψ_1(s/2)`. -/
theorem unramifiedTwist_eq (ψ : O →* ℂ) (hψb : ∀ x, ‖ψ x‖ ≤ 1) (s : ℂ) (hs : 4 < s.re) :
    twistDirichletG (ψ * unramifiedChar) s = star rationalSourceThetaScalar ^ 2 * cubeZetaG ψ (3 * (s / 2) - 1) *
      ((ψ 1 + ψ (-1)) * ((4 * Real.pi * ‖cuspFrequency 1‖ : ℝ) : ℂ) ^ (-s) * twistedSquarefreeSeriesG ψ 1 (s / 2)) := by
  have hb : ∀ x, ‖(ψ * unramifiedChar) x‖ ≤ 1 := fun x => by
    rw [MonoidHom.mul_apply, norm_mul]
    exact mul_le_one₀ (hψb x) (norm_nonneg _) (unramifiedChar_norm_le x)
  rw [twistDirichletG_eq_zeta_mul _ hb s hs,
    cubeZetaG_mul_eq ψ unramifiedChar (fun g hg => by rw [unramifiedChar_apply_of_primary hg, one_pow])]
  congr 1
  have hS : ∀ h₀, twistedSquarefreeSeriesG (ψ * unramifiedChar) h₀ (s / 2) = twistedSquarefreeSeriesG ψ h₀ (s / 2) :=
    fun h₀ => twistedSquarefreeSeriesG_mul_eq ψ unramifiedChar (fun g hg => unramifiedChar_apply_of_primary hg) h₀ _
  set f : Oˣ → ℕ → ℂ := fun u m => (ψ * unramifiedChar) ((u : O) * lambda ^ m) *
    (rationalSourceResidualFourierCoefficient ((u : O) * lambda ^ m) / rationalSourceResidualFourierCoefficient 1) ^ 2 *
      ((4 * Real.pi * ‖cuspFrequency ((u : O) * lambda ^ m)‖ : ℝ) : ℂ) ^ (-s) *
        twistedSquarefreeSeriesG (ψ * unramifiedChar) ((u : O) * lambda ^ m) (s / 2) with hf
  have hm : ∀ u : Oˣ, ∑' m : ℕ, f u m = f u 0 := by
    intro u
    refine tsum_eq_single 0 fun m hm => ?_
    have hz : (ψ * unramifiedChar) ((u : O) * lambda ^ m) = 0 := by
      rw [MonoidHom.mul_apply]
      change ψ _ * (if lambda ∣ (u : O) * lambda ^ m then 0 else 1) = 0
      rw [if_pos (dvd_mul_of_dvd_right (dvd_pow_self lambda hm) _), mul_zero]
    simp only [hf, hz, zero_mul]
  have hu : ∀ u : Oˣ, u ∉ ({1, -1} : Finset Oˣ) → f u 0 = 0 := by
    intro u hu
    have hT : rationalSourceResidualFourierCoefficient (u : O) = 0 := by
      by_contra hT
      rcases sourceCoefficient_unit_eq u hT with h | h
      · exact hu (Finset.mem_insert.mpr (Or.inl (Units.ext (by rw [h, Units.val_one]))))
      · exact hu (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
          (Units.ext (by rw [h, Units.val_neg, Units.val_one])))))
    simp only [hf, pow_zero, mul_one, hT, zero_div]
    ring
  have h1ne : (1 : Oˣ) ≠ -1 := by
    intro h
    have := congrArg (fun x : Oˣ => (x : O)) h
    simp only [Units.val_one, Units.val_neg] at this
    have h2 : (2 : O) = 0 := by linear_combination this
    exact not_lambda_sq_dvd_two (h2 ▸ dvd_zero _)
  rw [tsum_congr hm, tsum_eq_sum (s := ({1, -1} : Finset Oˣ)) (fun u hu' => hu u hu'),
    Finset.sum_pair h1ne]
  have hT1 := sourceCoefficient_one_ne_zero
  simp only [hf, pow_zero, mul_one, Units.val_one, Units.val_neg, hS, twistedSquarefreeSeriesG_neg_one,
    rationalSourceResidualFourierCoefficient_neg, cuspFrequency_neg, norm_neg, div_self hT1, one_pow,
    MonoidHom.mul_apply, unramifiedChar_apply_of_primary (show lambda ^ 2 ∣ (1 : O) - 1 by simp)]
  have hneg : unramifiedChar (-1) = 1 := by
    change (if lambda ∣ (-1 : O) then 0 else 1) = (1 : ℂ)
    rw [if_neg (fun h => lambda_not_dvd_one (by simpa using h.neg_right))]
  rw [hneg]
  ring

/-! ### Every layer is visible -/

theorem layerChar_cube (u : Oˣ) (m : ℕ) (g : O) (hg : lambda ^ 2 ∣ g - 1) :
    layerChar ((u : O) * lambda ^ m) g ^ 3 = 1 := by
  rw [layerChar_apply_of_primary _ hg, ← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, ← map_pow,
    symbol_cube_of_isCoprime _ _ hg
      ((ramified_primary_coprime u m _ hg).of_mul_left_right), map_one, one_pow]

theorem twistedSquarefreeSeriesG_layer (ψ : O →* ℂ) (h₀ : O) (w : ℂ) :
    twistedSquarefreeSeriesG ψ h₀ w = twistedSquarefreeSeriesG (ψ * layerChar h₀) 1 w := by
  unfold twistedSquarefreeSeriesG
  refine tsum_congr fun A => ?_
  split_ifs
  · by_cases hA : primaryIdealGenerator A = 0
    · rw [unramifiedNormWeight_of_bad w A hA, zero_mul, zero_mul]
    · have hp := (primaryIdealGenerator_spec A hA).2
      rw [MonoidHom.mul_apply, layerChar_apply_of_primary _ hp, symbol_one_numerator _ hp, map_one, one_pow]
      ring
  · rfl

/-- **Every layer is the unit layer of an even unramified twist.** For every bounded multiplicative `ψ` and every
layer `uλ^m` there is an even `ψ'` (`ψξ_{uλ^m}` if `ψ` is even, `ψξ_{uλ^m}η₃` if it is odd) with
`D₀^{ψ'}(s) = 2C̄² Z_{ψ³}(3s/2 − 1)(4π|ξ₁|)^{−s} S^ψ_{uλ^m}(s/2)` for `Re s > 4`. -/
theorem layer_eq_unramifiedTwist (ψ : O →* ℂ) (hψb : ∀ x, ‖ψ x‖ ≤ 1) (hsign : ψ (-1) = 1 ∨ ψ (-1) = -1)
    (u : Oˣ) (m : ℕ) (s : ℂ) (hs : 4 < s.re) :
    ∃ ψ' : O →* ℂ, ψ' (-1) = 1 ∧ (∀ x, ‖ψ' x‖ ≤ 1) ∧
      twistDirichletG (ψ' * unramifiedChar) s = 2 * star rationalSourceThetaScalar ^ 2 *
        cubeZetaG ψ (3 * (s / 2) - 1) * ((4 * Real.pi * ‖cuspFrequency 1‖ : ℝ) : ℂ) ^ (-s) *
          twistedSquarefreeSeriesG ψ ((u : O) * lambda ^ m) (s / 2) := by
  set ξ := layerChar ((u : O) * lambda ^ m)
  have hξb : ∀ x, ‖ξ x‖ ≤ 1 := layerChar_norm_le _
  have key : ∀ ψ' : O →* ℂ, (∀ x, ‖ψ' x‖ ≤ 1) → ψ' (-1) = 1 →
      (∀ g, lambda ^ 2 ∣ g - 1 → ψ' g = (ψ * ξ) g) →
      twistDirichletG (ψ' * unramifiedChar) s = 2 * star rationalSourceThetaScalar ^ 2 *
        cubeZetaG ψ (3 * (s / 2) - 1) * ((4 * Real.pi * ‖cuspFrequency 1‖ : ℝ) : ℂ) ^ (-s) *
          twistedSquarefreeSeriesG ψ ((u : O) * lambda ^ m) (s / 2) := by
    intro ψ' hb hev hprim
    have hZ : cubeZetaG ψ' (3 * (s / 2) - 1) = cubeZetaG ψ (3 * (s / 2) - 1) := by
      unfold cubeZetaG
      refine tsum_congr fun B => ?_
      by_cases hB : primaryIdealGenerator B = 0
      · rw [unramifiedNormWeight_of_bad _ B hB, zero_mul, zero_mul]
      · have hp := (primaryIdealGenerator_spec B hB).2
        rw [hprim _ hp, MonoidHom.mul_apply, mul_pow, layerChar_cube u m _ hp, mul_one]
    have hS : twistedSquarefreeSeriesG ψ' 1 (s / 2) = twistedSquarefreeSeriesG ψ ((u : O) * lambda ^ m) (s / 2) := by
      rw [twistedSquarefreeSeriesG_layer ψ]
      unfold twistedSquarefreeSeriesG
      refine tsum_congr fun A => ?_
      split_ifs
      · by_cases hA : primaryIdealGenerator A = 0
        · rw [unramifiedNormWeight_of_bad _ A hA, zero_mul, zero_mul]
        · rw [hprim _ (primaryIdealGenerator_spec A hA).2]
      · rfl
    rw [unramifiedTwist_eq ψ' hb s hs, hZ, hS, hev, map_one]
    ring
  rcases hsign with he | ho
  · refine ⟨ψ * ξ, by rw [MonoidHom.mul_apply, he, layerChar_neg_one, one_mul], fun x => ?_, ?_⟩
    · rw [MonoidHom.mul_apply, norm_mul]
      exact mul_le_one₀ (hψb x) (norm_nonneg _) (hξb x)
    · exact key _ (fun x => by rw [MonoidHom.mul_apply, norm_mul]; exact mul_le_one₀ (hψb x) (norm_nonneg _) (hξb x))
        (by rw [MonoidHom.mul_apply, he, layerChar_neg_one, one_mul]) (fun g _ => rfl)
  · have hb' : ∀ x, ‖(ψ * ξ * cubeSign) x‖ ≤ 1 := fun x => by
      rw [MonoidHom.mul_apply, MonoidHom.mul_apply, norm_mul, norm_mul]
      exact mul_le_one₀ (mul_le_one₀ (hψb x) (norm_nonneg _) (hξb x)) (norm_nonneg _) (cubeSign_norm_le x)
    have hev : (ψ * ξ * cubeSign) (-1) = 1 := by
      rw [MonoidHom.mul_apply, MonoidHom.mul_apply, ho, layerChar_neg_one, cubeSign_neg_one]
      ring
    refine ⟨ψ * ξ * cubeSign, hev, hb', key _ hb' hev (fun g hg => ?_)⟩
    rw [MonoidHom.mul_apply, cubeSign_apply_of_primary hg, mul_one]

end GaloisForLFunctions.OrderSixMetaplecticTheory
