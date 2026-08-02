import GaloisForLFunctions.HTGeometry.UniformGammaDatumAlgebra

/-!
# The boundary datum is ultrametric

The `Γ`-exponent cannot drop on a sum.  If it did, both summands would be negligible against the
shape of the sum, so the sum would be negligible against its own shape — and its residue is nonzero.

Together with additivity on products this makes the `Γ`-exponent a discrete valuation of `K_Γ`.
-/

open Filter Set Topology Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance ultrametricDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance ultrametricIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance ultrametricDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance ultrametricComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance ultrametricRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

/-- An element with a datum is nonzero. -/
theorem HasGammaDatum.ne_zero {σ : ℝ} {x : upperEndMeroField} {k a b : ℤ} {c : ℂ}
    (h : HasGammaDatum σ x k a b c) : x ≠ 0 := by
  intro hx0
  obtain ⟨hc, φ, hrep, hlim⟩ := h
  rw [hx0] at hrep
  obtain ⟨t, ht⟩ :=
    ((representsOnLine_zero_eventually hrep).and (eventually_ne_zero_of_datum hc hlim)).exists
  exact ht.2 ht.1

/-- An element whose datum has a positive `Γ`-exponent is negligible on the line. -/
theorem tendsto_zero_of_hasGammaDatum_gamma_pos {σ : ℝ} (hσ : 0 < σ) {x : upperEndMeroField}
    {k a b : ℤ} {c : ℂ} (hk : 0 < k) (h : HasGammaDatum σ x k a b c) :
    ∃ φ : ℝ → ℂ, RepresentsOnLine σ x φ ∧ (∀ᶠ t : ℝ in atTop, φ t ≠ 0)
      ∧ Tendsto φ atTop (nhds 0) := by
  obtain ⟨hc, φ, hrep, hlim⟩ := h
  refine ⟨φ, hrep, eventually_ne_zero_of_datum hc hlim, ?_⟩
  have hmul := hlim.mul (tendsto_gammaShapeZ_zero_of_gamma_pos hσ hk a b)
  rw [mul_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gammaShapeZ_ne_zero (σ := σ) hσ k a b] with t hS
  rw [div_mul_cancel₀ _ hS]

/-- **The `Γ`-exponent cannot drop on a sum.**  The exponent of `x + y` is at least the smaller of
the exponents of `x` and `y`. -/
theorem hasGammaDatum_add_exponent_ge {σ : ℝ} (hσ : 0 < σ) {x y : upperEndMeroField}
    {k a b k' a' b' m A B : ℤ} {c c' C : ℂ}
    (hx : HasGammaDatum σ x k a b c) (hy : HasGammaDatum σ y k' a' b' c')
    (hsum : HasGammaDatum σ (x + y) m A B C) : min k k' ≤ m := by
  classical
  by_contra hcon
  have hm : m < min k k' := lt_of_not_ge hcon
  have hmk : m < k := lt_of_lt_of_le hm (min_le_left _ _)
  have hmk' : m < k' := lt_of_lt_of_le hm (min_le_right _ _)
  have hu0 : x + y ≠ 0 := hsum.ne_zero
  -- the two summands, divided by the sum
  have hp : HasGammaDatum σ (x * (x + y)⁻¹) (k + -m) (a + -A) (b + -B) (c * C⁻¹) :=
    hx.mul hσ (hsum.inv hσ)
  have hq : HasGammaDatum σ (y * (x + y)⁻¹) (k' + -m) (a' + -A) (b' + -B) (c' * C⁻¹) :=
    hy.mul hσ (hsum.inv hσ)
  obtain ⟨φ₁, hrep₁, hne₁, hzero₁⟩ :=
    tendsto_zero_of_hasGammaDatum_gamma_pos hσ (by omega) hp
  obtain ⟨φ₂, hrep₂, hne₂, hzero₂⟩ :=
    tendsto_zero_of_hasGammaDatum_gamma_pos hσ (by omega) hq
  obtain ⟨U₁, V₁, G₁, H₁, hU₁, hV₁, hV₁0, hx₁, hφ₁⟩ := hrep₁
  obtain ⟨U₂, V₂, G₂, H₂, hU₂, hV₂, hV₂0, hx₂, hφ₂⟩ := hrep₂
  -- the two quotients add up to one
  have hone : x * (x + y)⁻¹ + y * (x + y)⁻¹ = 1 := by
    rw [← add_mul, mul_inv_cancel₀ hu0]
  rw [hx₁, hx₂] at hone
  have hcross : algebraMap upperEndAnalyticSubring upperEndMeroField (U₁ * V₂ + U₂ * V₁)
      = algebraMap upperEndAnalyticSubring upperEndMeroField (V₁ * V₂) := by
    rw [map_add, map_mul, map_mul, map_mul]
    field_simp at hone
    linear_combination hone
  have hprod : U₁ * V₂ + U₂ * V₁ = V₁ * V₂ :=
    IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField hcross
  have hgerm : Germ.coeRingHom upperEndFilter (fun z : ℂ => G₁ z * H₂ z + G₂ z * H₁ z)
      = Germ.coeRingHom upperEndFilter (fun z : ℂ => H₁ z * H₂ z) := by
    have h1 : upperEndAnalyticSubring.subtype (U₁ * V₂ + U₂ * V₁)
        = Germ.coeRingHom upperEndFilter (fun z : ℂ => G₁ z * H₂ z + G₂ z * H₁ z) := by
      rw [map_add, map_mul, map_mul, hU₁, hV₂, hU₂, hV₁, ← map_mul, ← map_mul, ← map_add]
      rfl
    have h2 : upperEndAnalyticSubring.subtype (V₁ * V₂)
        = Germ.coeRingHom upperEndFilter (fun z : ℂ => H₁ z * H₂ z) := by
      rw [map_mul, hV₁, hV₂, ← map_mul]
      rfl
    rw [← h1, ← h2, hprod]
  have hev : ∀ᶠ z : ℂ in upperEndFilter, G₁ z * H₂ z + G₂ z * H₁ z = H₁ z * H₂ z :=
    Filter.Germ.coe_eq.mp hgerm
  have hline := eventually_line_of_upperEnd hev σ
  -- the sum of the two line functions is eventually one, but both tend to zero
  have hsmall : ∀ᶠ t : ℝ in atTop, φ₁ t + φ₂ t ∈ Metric.ball (0 : ℂ) 1 := by
    have hlim0 : Tendsto (fun t : ℝ => φ₁ t + φ₂ t) atTop (nhds 0) := by
      have := hzero₁.add hzero₂
      rwa [add_zero] at this
    exact hlim0.eventually (Metric.ball_mem_nhds 0 one_pos)
  obtain ⟨t, ⟨⟨⟨ht, ht₁⟩, ht₂⟩, htsmall⟩⟩ :=
    (((hline.and hne₁).and hne₂).and hsmall).exists
  have hH₁ : H₁ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    exact ht₁ (by rw [hφ₁ t, h0, div_zero])
  have hH₂ : H₂ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    exact ht₂ (by rw [hφ₂ t, h0, div_zero])
  have hsum1 : φ₁ t + φ₂ t = 1 := by
    rw [hφ₁ t, hφ₂ t, div_add_div _ _ hH₁ hH₂, div_eq_one_iff_eq (mul_ne_zero hH₁ hH₂)]
    linear_combination ht
  rw [hsum1, Metric.mem_ball, dist_eq_norm, sub_zero, norm_one] at htsmall
  exact lt_irrefl 1 htsmall

/-- **The tube datum is ultrametric.** -/
theorem hasGammaTubeDatum_add_exponent_ge {M : ℝ} (hM : 0 < M) {x y : upperEndMeroField}
    {k a b k' a' b' m A B : ℤ} {c c' C : ℂ}
    (hx : HasGammaTubeDatum M x k a b c) (hy : HasGammaTubeDatum M y k' a' b' c')
    (hsum : HasGammaTubeDatum M (x + y) m A B C) : min k k' ≤ m :=
  hasGammaDatum_add_exponent_ge hM (hx.hasGammaDatum hM le_rfl) (hy.hasGammaDatum hM le_rfl)
    (hsum.hasGammaDatum hM le_rfl)

end

end GaloisForLFunctions.HTGeometry
