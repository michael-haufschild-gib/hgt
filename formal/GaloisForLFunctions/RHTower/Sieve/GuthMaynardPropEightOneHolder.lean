import Mathlib

set_option autoImplicit false

/-!
# Hölder `(2, 4, 4)`, comparison under a change of variables, and frequency-box counts

Real-analysis tools for the proof of Guth–Maynard Proposition 8.1 (`GuthMaynardPropEightOne`):

* `setIntegral_mul_mul_le`: if `∫_S f² ≤ a²`, `∫_S g⁴ ≤ b⁴`, `∫_S h⁴ ≤ c⁴` (`a, b, c ≥ 0`), then
  `∫_S fgh ≤ abc` — from the pointwise Young inequality `XYZ ≤ X²/2 + Y⁴/4 + Z⁴/4`;
* `setIntegral_comp_le_inv_mul_integral`: `∫_S G(φ(v)) dv ≤ λ⁻¹ ∫_ℝ G` when `φ` is injective on
  `S` with `|φ'| ≥ λ > 0` — the one-dimensional change of variables
  `∫_{φ(S)} G = ∫_S |φ'| G∘φ`;
* the Möbius maps `v ↦ (pv + q)/(rv)` (derivative `-q/(rv²)`, injective) and the affine maps
  `v ↦ (pv + q)/r`;
* `card_le_of_mem_box`: a set of integer triples with `|mᵢ| ≤ Xᵢ` has at most
  `Π(2Xᵢ + 1)` elements.
-/

open MeasureTheory Set Finset

namespace RHTower.GuthMaynard

noncomputable section

/-! ### Hölder with exponents `(2, 4, 4)` -/

/-- Pointwise Young inequality `XYZ ≤ X²/2 + Y⁴/4 + Z⁴/4`. -/
theorem mul_mul_le_sq_add_pow_four_add_pow_four (X Y Z : ℝ) :
    X * Y * Z ≤ X ^ 2 / 2 + Y ^ 4 / 4 + Z ^ 4 / 4 := by
  nlinarith [sq_nonneg (X - Y * Z), sq_nonneg (Y ^ 2 - Z ^ 2)]

/-- The weighted form `xyz ≤ (bc/2a) x² + (ac/4b³) y⁴ + (ab/4c³) z⁴` for `a, b, c > 0`. -/
theorem mul_mul_le_weighted {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (x y z : ℝ) :
    x * y * z ≤ b * c / (2 * a) * x ^ 2 + a * c / (4 * b ^ 3) * y ^ 4
      + a * b / (4 * c ^ 3) * z ^ 4 := by
  have key := mul_mul_le_sq_add_pow_four_add_pow_four (x / a) (y / b) (z / c)
  calc x * y * z = (a * b * c) * (x / a * (y / b) * (z / c)) := by field_simp
    _ ≤ (a * b * c) * ((x / a) ^ 2 / 2 + (y / b) ^ 4 / 4 + (z / c) ^ 4 / 4) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = b * c / (2 * a) * x ^ 2 + a * c / (4 * b ^ 3) * y ^ 4
          + a * b / (4 * c ^ 3) * z ^ 4 := by
        field_simp

/-- **Hölder `(2, 4, 4)` on a set, positive majorants.** If `∫_S f² ≤ a²`, `∫_S g⁴ ≤ b⁴`,
`∫_S h⁴ ≤ c⁴` with `a, b, c > 0`, then `∫_S fgh ≤ abc`. -/
theorem setIntegral_mul_mul_le_of_pos {S : Set ℝ} (hS : MeasurableSet S) {f g h : ℝ → ℝ}
    (hf2 : IntegrableOn (fun v => f v ^ 2) S) (hg4 : IntegrableOn (fun v => g v ^ 4) S)
    (hh4 : IntegrableOn (fun v => h v ^ 4) S)
    (hfgh : IntegrableOn (fun v => f v * g v * h v) S) {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hF : ∫ v in S, f v ^ 2 ≤ a ^ 2) (hG : ∫ v in S, g v ^ 4 ≤ b ^ 4)
    (hH : ∫ v in S, h v ^ 4 ≤ c ^ 4) :
    ∫ v in S, f v * g v * h v ≤ a * b * c := by
  have hsum : IntegrableOn (fun v => b * c / (2 * a) * f v ^ 2 + a * c / (4 * b ^ 3) * g v ^ 4
      + a * b / (4 * c ^ 3) * h v ^ 4) S :=
    ((hf2.const_mul _).add (hg4.const_mul _)).add (hh4.const_mul _)
  calc ∫ v in S, f v * g v * h v
      ≤ ∫ v in S, (b * c / (2 * a) * f v ^ 2 + a * c / (4 * b ^ 3) * g v ^ 4
          + a * b / (4 * c ^ 3) * h v ^ 4) :=
        setIntegral_mono_on hfgh hsum hS fun v hv =>
          mul_mul_le_weighted ha hb hc (f v) (g v) (h v)
    _ = b * c / (2 * a) * (∫ v in S, f v ^ 2) + a * c / (4 * b ^ 3) * (∫ v in S, g v ^ 4)
          + a * b / (4 * c ^ 3) * (∫ v in S, h v ^ 4) := by
        rw [integral_add (f := fun v => b * c / (2 * a) * f v ^ 2 + a * c / (4 * b ^ 3) * g v ^ 4)
            (g := fun v => a * b / (4 * c ^ 3) * h v ^ 4)
            ((hf2.const_mul _).add (hg4.const_mul _)) (hh4.const_mul _),
          integral_add (f := fun v => b * c / (2 * a) * f v ^ 2)
            (g := fun v => a * c / (4 * b ^ 3) * g v ^ 4) (hf2.const_mul _) (hg4.const_mul _),
          integral_const_mul, integral_const_mul, integral_const_mul]
    _ ≤ b * c / (2 * a) * a ^ 2 + a * c / (4 * b ^ 3) * b ^ 4 + a * b / (4 * c ^ 3) * c ^ 4 := by
        gcongr
    _ = a * b * c := by
        field_simp
        ring

/-- **Hölder `(2, 4, 4)` on a set.** If `∫_S f² ≤ a²`, `∫_S g⁴ ≤ b⁴`, `∫_S h⁴ ≤ c⁴` with
`a, b, c ≥ 0`, then `∫_S fgh ≤ abc` (positive majorants `a + η`, `b + η`, `c + η`, `η → 0`). -/
theorem setIntegral_mul_mul_le {S : Set ℝ} (hS : MeasurableSet S) {f g h : ℝ → ℝ}
    (hf2 : IntegrableOn (fun v => f v ^ 2) S) (hg4 : IntegrableOn (fun v => g v ^ 4) S)
    (hh4 : IntegrableOn (fun v => h v ^ 4) S)
    (hfgh : IntegrableOn (fun v => f v * g v * h v) S) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hF : ∫ v in S, f v ^ 2 ≤ a ^ 2) (hG : ∫ v in S, g v ^ 4 ≤ b ^ 4)
    (hH : ∫ v in S, h v ^ 4 ≤ c ^ 4) :
    ∫ v in S, f v * g v * h v ≤ a * b * c := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨K, hK⟩ : ∃ K, K = a * b + b * c + c * a + a + b + c + 1 := ⟨_, rfl⟩
  have hKpos : 0 < K := by rw [hK]; positivity
  obtain ⟨η, hη⟩ : ∃ η, η = min 1 (ε / K) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; exact lt_min one_pos (div_pos hε hKpos)
  have hη1 : η ≤ 1 := by rw [hη]; exact min_le_left _ _
  have hηK : η * K ≤ ε := by
    have : η ≤ ε / K := by rw [hη]; exact min_le_right _ _
    rwa [le_div_iff₀ hKpos] at this
  have hmain := setIntegral_mul_mul_le_of_pos hS hf2 hg4 hh4 hfgh
    (add_pos_of_nonneg_of_pos ha hη0) (add_pos_of_nonneg_of_pos hb hη0)
    (add_pos_of_nonneg_of_pos hc hη0)
    (hF.trans (pow_le_pow_left₀ ha (by linarith) 2))
    (hG.trans (pow_le_pow_left₀ hb (by linarith) 4))
    (hH.trans (pow_le_pow_left₀ hc (by linarith) 4))
  refine hmain.trans ?_
  have hη2 : η * η ≤ η := by nlinarith
  have hη3 : η * η * η ≤ η := by nlinarith
  have hexp : (a + η) * (b + η) * (c + η)
      = a * b * c + η * (a * b + b * c + c * a) + η * η * (a + b + c) + η * η * η := by ring
  have hab : 0 ≤ a + b + c := by positivity
  calc (a + η) * (b + η) * (c + η)
      ≤ a * b * c + η * (a * b + b * c + c * a) + η * (a + b + c) + η := by
        rw [hexp]
        nlinarith [mul_le_mul_of_nonneg_right hη2 hab]
    _ = a * b * c + η * K := by rw [hK]; ring
    _ ≤ a * b * c + ε := by linarith

/-! ### Changes of variables -/

/-- **Comparison under a change of variables.** If `|φ'| ≥ λ > 0` on `S` and `φ` is injective on
`S`, then `∫_S G(φ(v)) dv ≤ λ⁻¹ ∫_ℝ G` for nonnegative integrable `G`. -/
theorem setIntegral_comp_le_inv_mul_integral {S : Set ℝ} (hS : MeasurableSet S)
    {φ φ' : ℝ → ℝ} (hφ : ∀ v ∈ S, HasDerivWithinAt φ (φ' v) S v) (hinj : InjOn φ S)
    {lam : ℝ} (hlam : 0 < lam) (hφ' : ∀ v ∈ S, lam ≤ |φ' v|) {G : ℝ → ℝ} (hG : Integrable G)
    (hG0 : ∀ u, 0 ≤ G u) (hGφ : IntegrableOn (fun v => G (φ v)) S) :
    ∫ v in S, G (φ v) ≤ lam⁻¹ * ∫ u, G u := by
  have hcov := integral_image_eq_integral_abs_deriv_smul hS hφ hinj G
  have hint := (integrableOn_image_iff_integrableOn_abs_deriv_smul hS hφ hinj G).mp
    hG.integrableOn
  have h1 : lam * ∫ v in S, G (φ v) ≤ ∫ v in S, |φ' v| • G (φ v) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hGφ.const_mul lam) hint hS fun v hv => ?_
    rw [smul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hφ' v hv) (hG0 _)
  have h2 : ∫ u in φ '' S, G u ≤ ∫ u, G u :=
    setIntegral_le_integral hG (Filter.Eventually.of_forall hG0)
  rw [hcov] at h2
  rw [le_inv_mul_iff₀ hlam]
  exact h1.trans h2

/-- Derivative of the Möbius map `v ↦ (pv + q)/(rv)`: it is `-q/(rv²)`. -/
theorem hasDerivAt_mobius (p q r : ℝ) {v : ℝ} (hv : v ≠ 0) (hr : r ≠ 0) :
    HasDerivAt (fun v => (p * v + q) / (r * v)) (-q / (r * v ^ 2)) v := by
  have h := (((hasDerivAt_id' v).const_mul p).add_const q).div
    ((hasDerivAt_id' v).const_mul r) (mul_ne_zero hr hv)
  refine h.congr_deriv ?_
  field_simp
  ring

/-- The Möbius map `v ↦ (pv + q)/(rv)` is injective on `v ≠ 0` when `q, r ≠ 0`. -/
theorem injOn_mobius {p q r : ℝ} (hq : q ≠ 0) (hr : r ≠ 0) {S : Set ℝ} (hS : ∀ v ∈ S, v ≠ 0) :
    InjOn (fun v => (p * v + q) / (r * v)) S := by
  intro v hv w hw hvw
  have hv0 := hS v hv
  have hw0 := hS w hw
  simp only at hvw
  rw [div_eq_div_iff (mul_ne_zero hr hv0) (mul_ne_zero hr hw0)] at hvw
  have h : q * r * (w - v) = 0 := by linear_combination hvw
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (mul_ne_zero hq hr)
  · linarith

/-- The affine map `v ↦ (pv + q)/r` is injective when `p, r ≠ 0`. -/
theorem injective_affine {p q r : ℝ} (hp : p ≠ 0) (hr : r ≠ 0) :
    Function.Injective fun v : ℝ => (p * v + q) / r := by
  intro v w hvw
  simp only at hvw
  rw [div_left_inj' hr] at hvw
  exact mul_left_cancel₀ hp (by linarith)

/-! ### The number of frequency triples -/

/-- The integer box `[-⌊X⌋, ⌊X⌋]` has at most `2X + 1` points. -/
theorem card_Icc_neg_floor_le {X : ℝ} (hX : 0 ≤ X) :
    ((Finset.Icc (-⌊X⌋) ⌊X⌋).card : ℝ) ≤ 2 * X + 1 := by
  have hfl : 0 ≤ ⌊X⌋ := Int.floor_nonneg.mpr hX
  rw [Int.card_Icc]
  have hnn : 0 ≤ ⌊X⌋ + 1 - -⌊X⌋ := by linarith
  have hcast : (((⌊X⌋ + 1 - -⌊X⌋).toNat : ℤ) : ℝ) = 2 * (⌊X⌋ : ℝ) + 1 := by
    rw [Int.toNat_of_nonneg hnn]
    push_cast
    ring
  rw [← Int.cast_natCast, hcast]
  linarith [Int.floor_le X]

/-- An integer with `|m| ≤ X` lies in `[-⌊X⌋, ⌊X⌋]`. -/
theorem mem_Icc_neg_floor {X : ℝ} {m : ℤ} (hm : |(m : ℝ)| ≤ X) : m ∈ Finset.Icc (-⌊X⌋) ⌊X⌋ := by
  rw [Finset.mem_Icc]
  constructor
  · have : -m ≤ ⌊X⌋ := Int.le_floor.mpr (by push_cast; linarith [neg_abs_le (m : ℝ)])
    linarith
  · exact Int.le_floor.mpr (le_trans (le_abs_self _) hm)

/-- A set of integer triples in the box `|m₁| ≤ X₁`, `|m₂| ≤ X₂`, `|m₃| ≤ X₃` has at most
`(2X₁ + 1)(2X₂ + 1)(2X₃ + 1)` elements. -/
theorem card_le_of_mem_box (𝓜 : Finset (ℤ × ℤ × ℤ)) {X₁ X₂ X₃ : ℝ} (h₁ : 0 ≤ X₁) (h₂ : 0 ≤ X₂)
    (h₃ : 0 ≤ X₃) (h : ∀ m ∈ 𝓜, |(m.1 : ℝ)| ≤ X₁ ∧ |(m.2.1 : ℝ)| ≤ X₂ ∧ |(m.2.2 : ℝ)| ≤ X₃) :
    (𝓜.card : ℝ) ≤ (2 * X₁ + 1) * ((2 * X₂ + 1) * (2 * X₃ + 1)) := by
  have hsub : 𝓜 ⊆ Finset.Icc (-⌊X₁⌋) ⌊X₁⌋ ×ˢ (Finset.Icc (-⌊X₂⌋) ⌊X₂⌋ ×ˢ
      Finset.Icc (-⌊X₃⌋) ⌊X₃⌋) := by
    intro m hm
    obtain ⟨hm₁, hm₂, hm₃⟩ := h m hm
    exact Finset.mem_product.mpr ⟨mem_Icc_neg_floor hm₁,
      Finset.mem_product.mpr ⟨mem_Icc_neg_floor hm₂, mem_Icc_neg_floor hm₃⟩⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_product] at hcard
  calc (𝓜.card : ℝ)
      ≤ ((Finset.Icc (-⌊X₁⌋) ⌊X₁⌋).card * ((Finset.Icc (-⌊X₂⌋) ⌊X₂⌋).card *
          (Finset.Icc (-⌊X₃⌋) ⌊X₃⌋).card) : ℕ) := by exact_mod_cast hcard
    _ ≤ (2 * X₁ + 1) * ((2 * X₂ + 1) * (2 * X₃ + 1)) := by
        push_cast
        gcongr
        · exact card_Icc_neg_floor_le h₁
        · exact card_Icc_neg_floor_le h₂
        · exact card_Icc_neg_floor_le h₃

end

end RHTower.GuthMaynard
