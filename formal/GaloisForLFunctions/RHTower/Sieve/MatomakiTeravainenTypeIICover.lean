import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIICells

/-!
# Covering the set `U` of Matomäki–Teräväinen §5.3

`U` is covered by the Proposition 4.2 region, the set where the short factor is `≤ 1/X`, and
`⌊log₂ X⌋ + 1` dyadic amplitude cells.  The three contributions are bounded separately.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- Every `y ∈ (1/X, 1]` lies in a dyadic level `[2^{-j-1}, 2^{-j}]` with `j ≤ log₂ X`. -/
theorem exists_half_pow_level {y X : ℝ} (hX : 1 ≤ X) (hy : 1 / X < y) (hy1 : y ≤ 1) :
    ∃ j, j < Nat.log 2 ⌊X⌋₊ + 1 ∧ (1 / 2 : ℝ) ^ (j + 1) ≤ y ∧ y ≤ (1 / 2 : ℝ) ^ j := by
  classical
  have hX0 : 0 < X := by linarith
  have hy0 : 0 < y := lt_trans (by positivity) hy
  have hex : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < y := exists_pow_lt_of_lt_one hy0 (by norm_num)
  have hn : (1 / 2 : ℝ) ^ Nat.find hex < y := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro h; rw [h, pow_zero] at hn; linarith
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hmin : ¬ (1 / 2 : ℝ) ^ j < y := Nat.find_min hex (by omega)
  have hup : y ≤ (1 / 2 : ℝ) ^ j := not_lt.1 hmin
  have hj' : j + 1 = Nat.find hex := hj.symm
  refine ⟨j, ?_, by rw [hj']; exact hn.le, hup⟩
  have h2j : (2 : ℝ) ^ j < X := by
    have h : 1 / X < 1 / 2 ^ j := by rw [← one_div_pow]; exact hy.trans_le hup
    rwa [one_div_lt_one_div hX0 (by positivity)] at h
  have hfl : 2 ^ j ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast h2j.le)
  have := Nat.le_log_of_pow_le (by norm_num) hfl
  omega

/-- The number of dyadic levels is `≤ 2 log X + 1`. -/
theorem natLog_two_floor_le {X : ℝ} (hX : 1 ≤ X) :
    ((Nat.log 2 ⌊X⌋₊ : ℕ) : ℝ) ≤ 2 * Real.log X := by
  have hfl : ⌊X⌋₊ ≠ 0 := (Nat.floor_pos.2 hX).ne'
  have hpow : ((2 ^ Nat.log 2 ⌊X⌋₊ : ℕ) : ℝ) ≤ X :=
    (Nat.cast_le.2 (Nat.pow_log_le_self 2 hfl)).trans (Nat.floor_le (by linarith))
  have hlog := Real.log_le_log (by positivity) hpow
  push_cast at hlog
  rw [Real.log_pow] at hlog
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 ⌊X⌋₊)]

/-- **The cover of `U`.** -/
theorem setIntegral_le_of_typeII_cover {F₁ F₂ : ℝ → ℂ} (hF₁ : Continuous F₁)
    (hF₂ : Continuous F₂) {U R : Set ℝ} {X θ₁ θ₂ : ℝ} (hX : 1 ≤ X)
    (hUX : U ⊆ Set.Icc (-X) X)
    (hcov : ∀ t ∈ U, t ∉ R → ‖F₁ t‖ ≤ θ₁ ∧ ‖F₂ t‖ ≤ θ₂) (h1 : ∀ t ∈ U, ‖F₁ t‖ ≤ 1) :
    ∫ t in U, ‖F₁ t * F₂ t‖ ^ 2 ≤
      (∫ t in U ∩ R, ‖F₁ t * F₂ t‖ ^ 2) + (∫ t in U ∩ {t | ‖F₁ t‖ ≤ 1 / X}, ‖F₁ t * F₂ t‖ ^ 2) +
        ∑ j : Fin (Nat.log 2 ⌊X⌋₊ + 1), ∫ t in typeIICell U F₁ F₂ j θ₁ θ₂, ‖F₁ t * F₂ t‖ ^ 2 := by
  set J := Nat.log 2 ⌊X⌋₊ + 1 with hJ
  let S : Option (Option (Fin J)) → Set ℝ := fun o =>
    match o with
    | none => U ∩ R
    | some none => U ∩ {t | ‖F₁ t‖ ≤ 1 / X}
    | some (some j) => typeIICell U F₁ F₂ j θ₁ θ₂
  have hS : ∀ o, S o ⊆ Set.Icc (-X) X := by
    intro o
    rcases o with _ | _ | j
    · exact fun t ht => hUX ht.1
    · exact fun t ht => hUX ht.1
    · exact fun t ht => hUX ht.1.1.1
  have hcover : U ⊆ ⋃ o, S o := by
    intro t ht
    simp only [Set.mem_iUnion]
    by_cases hR : t ∈ R
    · exact ⟨none, ht, hR⟩
    by_cases hsmall : ‖F₁ t‖ ≤ 1 / X
    · exact ⟨some none, ht, hsmall⟩
    push Not at hsmall
    obtain ⟨j, hjJ, hlo, hhi⟩ := exists_half_pow_level hX hsmall (h1 t ht)
    obtain ⟨hθ₁, hθ₂⟩ := hcov t ht hR
    exact ⟨some (some ⟨j, hjJ⟩), ⟨⟨⟨ht, hlo, hhi⟩, hθ₁⟩, hθ₂⟩⟩
  have hmain := setIntegral_le_sum_setIntegral_of_subset_iUnion
    (f := fun t => ‖F₁ t * F₂ t‖ ^ 2) (((hF₁.mul hF₂).norm).pow 2) hS hcover
    (fun t => sq_nonneg _)
  refine hmain.trans (le_of_eq ?_)
  rw [Fintype.sum_option, Fintype.sum_option]
  ring

/-- The Proposition 4.2 part: on the region the integrand is `B₂²` times the product of the two
normalised amplitudes. -/
theorem setIntegral_inter_region_le {F₁ F₂ : ℝ → ℂ} {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) {U R : Set ℝ} {X B₂ : ℝ} (hRX : R ⊆ Set.Icc (-X) X)
    (hpt : ∀ t, ‖F₁ t * F₂ t‖ ^ 2 = B₂ ^ 2 * (f t ^ 2 * g t ^ 2)) :
    ∫ t in U ∩ R, ‖F₁ t * F₂ t‖ ^ 2 ≤ B₂ ^ 2 * ∫ t in R, f t ^ 2 * g t ^ 2 := by
  have hcont : Continuous fun t => f t ^ 2 * g t ^ 2 := (hf.pow 2).mul (hg.pow 2)
  have hint : IntegrableOn (fun t => f t ^ 2 * g t ^ 2) R :=
    hcont.integrableOn_Icc.mono_set hRX
  simp_rw [hpt]
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  exact setIntegral_mono_set hint (Filter.Eventually.of_forall fun t => by positivity)
    (Filter.Eventually.of_forall Set.inter_subset_right)

/-- The part where the short factor is `≤ 1/X`. -/
theorem setIntegral_small_le {F₁ F₂ : ℝ → ℂ} (hF₁ : Continuous F₁) (hF₂ : Continuous F₂)
    {E : Set ℝ} (hE : MeasurableSet E) {X B₂ : ℝ} (hX : 0 < X) (hEX : E ⊆ Set.Icc (-X) X)
    (h₁ : ∀ t ∈ E, ‖F₁ t‖ ≤ 1 / X) (h₂ : ∀ t ∈ E, ‖F₂ t‖ ≤ B₂) :
    ∫ t in E, ‖F₁ t * F₂ t‖ ^ 2 ≤ 2 * X * (B₂ / X) ^ 2 := by
  have hint : IntegrableOn (fun t => ‖F₁ t * F₂ t‖ ^ 2) E :=
    (((hF₁.mul hF₂).norm).pow 2).integrableOn_Icc.mono_set hEX
  have hcint : IntegrableOn (fun _ : ℝ => (B₂ / X) ^ 2) (Set.Icc (-X) X) :=
    continuous_const.integrableOn_Icc
  calc ∫ t in E, ‖F₁ t * F₂ t‖ ^ 2 ≤ ∫ _t in E, (B₂ / X) ^ 2 := by
        refine setIntegral_mono_on hint (hcint.mono_set hEX) hE fun t ht => ?_
        rw [norm_mul, mul_pow, div_pow]
        have ha := pow_le_pow_left₀ (norm_nonneg _) (h₁ t ht) 2
        have hb := pow_le_pow_left₀ (norm_nonneg _) (h₂ t ht) 2
        calc ‖F₁ t‖ ^ 2 * ‖F₂ t‖ ^ 2 ≤ (1 / X) ^ 2 * B₂ ^ 2 :=
              mul_le_mul ha hb (sq_nonneg _) (sq_nonneg _)
          _ = B₂ ^ 2 / X ^ 2 := by ring
    _ ≤ ∫ _t in Set.Icc (-X) X, (B₂ / X) ^ 2 :=
        setIntegral_mono_set hcint (Filter.Eventually.of_forall fun _ => sq_nonneg _)
          (Filter.Eventually.of_forall hEX)
    _ = 2 * X * (B₂ / X) ^ 2 := by
        rw [setIntegral_const, measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith),
          smul_eq_mul]
        ring

/-- **§5.3 with explicit bounds.**  The Type-II contribution to `(5.3)` is at most the
Proposition 4.2 bound (times `B₂²`), plus `2X (B₂/X)²` for the small part, plus
`⌊log₂ X⌋ + 1` amplified cell bounds. -/
theorem setIntegral_typeII_le_explicit {X Y z₀ z δ ε : ℝ} (data : MTTypeIIPieceData X Y z₀ z δ ε)
    (hprime : MTUniformDivisorBounded 0 (mtTypeIIPrimeCoefficient data.indices data.block))
    (hβ : MTUniformDivisorBounded 5 data.β)
    {B : Finset ℕ} (hBp : ∀ p ∈ B, p.Prime) {P a η εU σ₀ ζ ε₁ δ₀ B₂ Bnd : ℝ} (hP : 1 ≤ P)
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
    {R : Set ℝ} (hRX : R ⊆ Set.Icc (-X) X)
    (hcovR : ∀ t ∈ U, t ∉ R → ‖mtTypeIIPrimeFactor data 1 t‖ ≤ (⌈data.M₁⌉₊ : ℝ) ^ (-σ₀) ∧
      ‖mtTypeIILongFactor data 1 t‖ ≤ B₂ * (⌈data.M₂⌉₊ : ℝ) ^ (-σ₀))
    (hF₁1 : ∀ t ∈ U, ‖mtTypeIIPrimeFactor data 1 t‖ ≤ 1)
    (hF₂B : ∀ t ∈ U, ‖mtTypeIILongFactor data 1 t‖ ≤ B₂)
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hpt : ∀ t, ‖mtTypeIIPrimeFactor data 1 t * mtTypeIILongFactor data 1 t‖ ^ 2 =
      B₂ ^ 2 * (f t ^ 2 * g t ^ 2))
    (hBnd : ∫ t in R, f t ^ 2 * g t ^ 2 ≤ Bnd) :
    ∫ t in U, ‖mtTypeIIPrimeFactor data 1 t * mtTypeIILongFactor data 1 t‖ ^ 2 ≤
      B₂ ^ 2 * Bnd + 2 * X * (B₂ / X) ^ 2 +
        ((Nat.log 2 ⌊X⌋₊ + 1 : ℕ) : ℝ) *
          (typeIICellConstant η * X ^ (εU / 5 + 6 * η) * (8 * X ^ (-δ₀))) := by
  have hX0 : 0 < X := by linarith
  have hF₁c : Continuous (mtTypeIIPrimeFactor data 1) := continuous_perronPoly _ _ 1
  have hF₂c := continuous_mtTypeIILongFactor data 1
  have hcover := setIntegral_le_of_typeII_cover hF₁c hF₂c (by linarith) hUX hcovR hF₁1
  refine hcover.trans ?_
  have hpart1 := setIntegral_inter_region_le (U := U) hf hg hRX hpt
  have hEm : MeasurableSet (U ∩ {t | ‖mtTypeIIPrimeFactor data 1 t‖ ≤ 1 / X}) :=
    hU.inter (isClosed_le hF₁c.norm continuous_const).measurableSet
  have hpart3 := setIntegral_small_le hF₁c hF₂c hEm hX0
    (fun t ht => hUX ht.1) (fun t ht => ht.2) (fun t ht => hF₂B t ht.1)
  have hcells : ∀ j : Fin (Nat.log 2 ⌊X⌋₊ + 1),
      ∫ t in typeIICell U (mtTypeIIPrimeFactor data 1) (mtTypeIILongFactor data 1) j
          ((⌈data.M₁⌉₊ : ℝ) ^ (-σ₀)) (B₂ * (⌈data.M₂⌉₊ : ℝ) ^ (-σ₀)),
          ‖mtTypeIIPrimeFactor data 1 t * mtTypeIILongFactor data 1 t‖ ^ 2 ≤
        typeIICellConstant η * X ^ (εU / 5 + 6 * η) * (8 * X ^ (-δ₀)) := fun j =>
    setIntegral_typeIICell_le data hprime hβ hBp hP hB hk hkX hlo hstars hfac ha1 ha43 hη hη1 hεU
      hU hUX hS hM₁2 hM₂2 hdil hM₂X hM₁X hX64 hdiv5 hdiv4 h1 h2 h3 hB₂1 hB₂ hσ₀ hσ₀' hζ m1 m2 m3 j
  have hsum := Finset.sum_le_sum fun (j : Fin (Nat.log 2 ⌊X⌋₊ + 1)) (_ : j ∈ Finset.univ) =>
    hcells j
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hBnd' := mul_le_mul_of_nonneg_left hBnd (sq_nonneg B₂)
  linarith

end

end RHTower.Sieve
