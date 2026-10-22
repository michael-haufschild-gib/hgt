import GaloisForLFunctions.RHTower.CCM.CCMParityTopLayerAlternation

/-!
# The parity law of the restricted Weil ground state under a finite top layer

**Theorem** (`groundParity_law`). Under `FiniteTopLayer δ t`, for every `g > 0` there is `A` such
that at every aperture `a ≥ A`:
* if `F(θ(a)) ≥ g`, every ground state of the CCM restricted Weil form is reflection-odd;
* if `F(θ(a)) ≤ −g`, every ground state is reflection-even.

Here `F = λ_max(T(θ)) − λ_max(T(θ + π𝟙))` is the leading-order parity balance at the aperture
phases `θ_j(a) = −2t_j a`. So the ground-state parity is decided pointwise by the sign of an explicit
almost periodic function of the aperture, outside the band `|F| < g`.

**Proof.** At a single aperture with `F ≥ g` and error rate below `g/2`, the odd test lies below the
even floor (`oddTest_below_evenFloor`), so the even part of a ground state vanishes; symmetrically
for `F ≤ −g` with the even test and the odd floor (`evenTest_below_oddFloor`). The error rate tends
to zero (`tendsto_errorRate`).
-/

open Matrix Complex Filter Topology MeasureTheory Set
open RHTower.CCMParityQuartet RHTower.CCMParityCauchy GaloisForLFunctions.HTGeometry

namespace RHTower.CCMParityTopLayer

noncomputable section

variable {m : ℕ}

/-- **Odd ground states at one aperture.** -/
theorem ground_odd_of_balance_ge {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t)
    {κ : ℝ} (hκ : 0 < κ) (hcoer : ∀ x, κ * ‖x‖ ^ 2 ≤ normForm δ t x)
    (a : SuzukiPositiveAperture) {g : ℝ} (hg0 : 0 < g)
    (hga₀ : g ≤ ccmParityBalance δ t h.mult (aperturePhase t a.1))
    (hR : errorRate h (2 * m * max 1 (1 / κ)) ((∑ j, |h.mult j|) * (1 / (2 * δ)))
      (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) a.1 < g / 2) :
    ∀ u : CCMArchimedeanFormDomain a,
      ccmRestrictedWeilSourceQuadratic a u =
          ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 →
        ccmArchimedeanFormReflection a u = -u := by
  have hδ := h.pos
  have ht := h.injective
  have htpos := h.t_pos
  have hm := h.nonempty
  set C₀ : ℝ := 2 * m * max 1 (1 / κ) with hC₀
  set Blam : ℝ := (∑ j, |h.mult j|) * (1 / (2 * δ)) with hBlam
  -- the maximizer and the odd model
  obtain ⟨x, hx, hmax, -⟩ := exists_isMaxOn_quadForm hδ ht htpos hm h.mult (aperturePhase t a.1)
  have hCx : profileBound x ≤ C₀ := profileBound_le_of_coercive hκ hcoer hx
  have hBlamx : max (ccmLambdaMax δ t h.mult (halfTurn (aperturePhase t a.1))) 0 ≤ Blam := by
    refine max_le (lambdaMax_le hδ ht htpos hm h.mult _) ?_
    positivity
  have hgap := gap_ge_of_balance_ge hδ ht htpos hm h.mult (aperturePhase t a.1) hga₀ hg0
  have hlt := oddTest_below_evenFloor h a hx hmax hCx hBlamx hgap hR
  set W := oddProfileModel δ t x a.1 with hW
  have hWs := contDiff_oddProfileModel δ t x a.1
  have hD : ∀ y ∈ Icc (-a.1) a.1, |W y| ≤ 2 * profileBound x := fun y hy =>
    abs_oddProfileModel_le hδ.le t x hy
  have hD' : ∀ y ∈ Icc (-a.1) a.1, |deriv W y| ≤ 2 * profileBound x * (δ + ∑ j, |t j|) :=
    fun y hy => abs_deriv_oddProfileModel_le hδ.le t x hy
  obtain ⟨v, hv⟩ := exists_smooth_below_model h a W hWs hD hD' hlt
  -- the ground energy lies strictly below the even floor
  set ce := evenFloorConst h a.1 with hce
  have hμv := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a v.toCCMFormVector
  intro u hu
  obtain ⟨heven, -⟩ := ccmRestrictedWeil_ground_evenOdd_components a u hu
  set e := ccmRestrictedWeilEvenPart a u with he
  have hRe : ccmArchimedeanFormReflection a e = e := ccmArchimedeanFormReflection_evenPart a u
  have hfloor := sourceQuadratic_ge_of_isEven h e hRe
  have hvpos : 0 < ‖ccmArchimedeanFormToAperture a v.toCCMFormVector‖ ^ 2 := by
    by_contra hle
    push Not at hle
    have h0 : ‖ccmArchimedeanFormToAperture a v.toCCMFormVector‖ ^ 2 = 0 :=
      le_antisymm hle (by positivity)
    rw [h0] at hv hμv
    linarith
  have hμ : ccmRestrictedWeilGroundEnergy a < ce := by
    by_contra hge
    push Not at hge
    have := mul_le_mul_of_nonneg_right hge hvpos.le
    linarith
  have hJe : ‖ccmArchimedeanFormToAperture a e‖ ^ 2 = 0 := by
    have hfl : ce * ‖ccmArchimedeanFormToAperture a e‖ ^ 2 ≤
        ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a e‖ ^ 2 := by
      rw [← heven]
      exact hfloor
    have hnn : 0 ≤ ‖ccmArchimedeanFormToAperture a e‖ ^ 2 := by positivity
    obtain ⟨X, hXdef⟩ : ∃ X, X = ‖ccmArchimedeanFormToAperture a e‖ ^ 2 := ⟨_, rfl⟩
    obtain ⟨μ, hμdef⟩ : ∃ μ, μ = ccmRestrictedWeilGroundEnergy a := ⟨_, rfl⟩
    rw [← hXdef] at hfl hnn ⊢
    rw [← hμdef] at hfl hμ
    have hpos : 0 < ce - μ := sub_pos.mpr hμ
    have hprod : (ce - μ) * X ≤ 0 := by rw [sub_mul]; linarith
    by_contra hX
    have hXpos : 0 < X := lt_of_le_of_ne hnn (Ne.symm hX)
    have := mul_pos hpos hXpos
    linarith
  have he0 : e = 0 := by
    apply ccmArchimedeanFormToAperture_injective a
    rw [map_zero]
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hJe)
  have hsum : u + ccmArchimedeanFormReflection a u = 0 := by
    have h2 : (2 : ℂ)⁻¹ • (u + ccmArchimedeanFormReflection a u) = 0 := he0
    rwa [smul_eq_zero, or_iff_right (inv_ne_zero two_ne_zero)] at h2
  exact eq_neg_of_add_eq_zero_right hsum

/-- **Even ground states at one aperture.** -/
theorem ground_even_of_balance_le {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t)
    {κ : ℝ} (hκ : 0 < κ) (hcoer : ∀ x, κ * ‖x‖ ^ 2 ≤ normForm δ t x)
    (a : SuzukiPositiveAperture) {g : ℝ} (hg0 : 0 < g)
    (hga₀ : ccmParityBalance δ t h.mult (aperturePhase t a.1) ≤ -g)
    (hR : errorRate h (2 * m * max 1 (1 / κ)) ((∑ j, |h.mult j|) * (1 / (2 * δ)))
      (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) a.1 < g / 2) :
    ∀ u : CCMArchimedeanFormDomain a,
      ccmRestrictedWeilSourceQuadratic a u =
          ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 →
        ccmArchimedeanFormReflection a u = u := by
  have hδ := h.pos
  have ht := h.injective
  have htpos := h.t_pos
  have hm := h.nonempty
  set C₀ : ℝ := 2 * m * max 1 (1 / κ) with hC₀
  set Blam : ℝ := (∑ j, |h.mult j|) * (1 / (2 * δ)) with hBlam
  have hgap : g / 2 ≤ ccmLambdaMax δ t h.mult (halfTurn (aperturePhase t a.1)) -
      max (ccmLambdaMax δ t h.mult (aperturePhase t a.1)) 0 := by
    have hge : g ≤ ccmParityBalance δ t h.mult (halfTurn (aperturePhase t a.1)) := by
      rw [ccmParityBalance_halfTurn]; linarith
    have := gap_ge_of_balance_ge hδ ht htpos hm h.mult _ hge hg0
    rwa [ccmLambdaMax_halfTurn_halfTurn] at this
  obtain ⟨x, hx, hmax, -⟩ := exists_isMaxOn_quadForm hδ ht htpos hm h.mult
    (halfTurn (aperturePhase t a.1))
  have hCx : profileBound x ≤ C₀ := profileBound_le_of_coercive hκ hcoer hx
  have hBlamx : max (ccmLambdaMax δ t h.mult (aperturePhase t a.1)) 0 ≤ Blam := by
    refine max_le (lambdaMax_le hδ ht htpos hm h.mult _) ?_
    positivity
  have hlt := evenTest_below_oddFloor h a hx hmax hCx hBlamx hgap hR
  set W := evenProfileModel δ t x a.1 with hW
  have hWs := contDiff_evenProfileModel δ t x a.1
  have hD : ∀ y ∈ Icc (-a.1) a.1, |W y| ≤ 2 * profileBound x := fun y hy =>
    abs_evenProfileModel_le hδ.le t x hy
  have hD' : ∀ y ∈ Icc (-a.1) a.1, |deriv W y| ≤ 2 * profileBound x * (δ + ∑ j, |t j|) :=
    fun y hy => abs_deriv_evenProfileModel_le hδ.le t x hy
  obtain ⟨v, hv⟩ := exists_smooth_below_model h a W hWs hD hD' hlt
  set co := oddFloorConst h a.1 with hco
  have hμv := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a v.toCCMFormVector
  intro u hu
  obtain ⟨-, hodd⟩ := ccmRestrictedWeil_ground_evenOdd_components a u hu
  set o := ccmRestrictedWeilOddPart a u with ho
  have hRo : ccmArchimedeanFormReflection a o = -o := ccmArchimedeanFormReflection_oddPart a u
  have hfloor := sourceQuadratic_ge_of_isOdd h o hRo
  have hvpos : 0 < ‖ccmArchimedeanFormToAperture a v.toCCMFormVector‖ ^ 2 := by
    by_contra hle
    push Not at hle
    have h0 : ‖ccmArchimedeanFormToAperture a v.toCCMFormVector‖ ^ 2 = 0 :=
      le_antisymm hle (by positivity)
    rw [h0] at hv hμv
    linarith
  have hμ : ccmRestrictedWeilGroundEnergy a < co := by
    by_contra hge
    push Not at hge
    have := mul_le_mul_of_nonneg_right hge hvpos.le
    linarith
  have hJo : ‖ccmArchimedeanFormToAperture a o‖ ^ 2 = 0 := by
    have hfl : co * ‖ccmArchimedeanFormToAperture a o‖ ^ 2 ≤
        ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a o‖ ^ 2 := by
      rw [← hodd]
      exact hfloor
    have hnn : 0 ≤ ‖ccmArchimedeanFormToAperture a o‖ ^ 2 := by positivity
    obtain ⟨X, hXdef⟩ : ∃ X, X = ‖ccmArchimedeanFormToAperture a o‖ ^ 2 := ⟨_, rfl⟩
    obtain ⟨μ, hμdef⟩ : ∃ μ, μ = ccmRestrictedWeilGroundEnergy a := ⟨_, rfl⟩
    rw [← hXdef] at hfl hnn ⊢
    rw [← hμdef] at hfl hμ
    have hpos : 0 < co - μ := sub_pos.mpr hμ
    have hprod : (co - μ) * X ≤ 0 := by rw [sub_mul]; linarith
    by_contra hX
    have hXpos : 0 < X := lt_of_le_of_ne hnn (Ne.symm hX)
    have := mul_pos hpos hXpos
    linarith
  have ho0 : o = 0 := by
    apply ccmArchimedeanFormToAperture_injective a
    rw [map_zero]
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hJo)
  have hdiff : u - ccmArchimedeanFormReflection a u = 0 := by
    have h2 : (2 : ℂ)⁻¹ • (u - ccmArchimedeanFormReflection a u) = 0 := ho0
    rwa [smul_eq_zero, or_iff_right (inv_ne_zero two_ne_zero)] at h2
  exact (sub_eq_zero.mp hdiff).symm

/-- **The parity law.** -/
theorem groundParity_law {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t) {g : ℝ}
    (hg : 0 < g) :
    ∃ A : ℝ, ∀ a : SuzukiPositiveAperture, A ≤ a.1 →
      (g ≤ ccmParityBalance δ t h.mult (aperturePhase t a.1) →
        ∀ u : CCMArchimedeanFormDomain a,
          ccmRestrictedWeilSourceQuadratic a u =
              ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 →
            ccmArchimedeanFormReflection a u = -u) ∧
      (ccmParityBalance δ t h.mult (aperturePhase t a.1) ≤ -g →
        ∀ u : CCMArchimedeanFormDomain a,
          ccmRestrictedWeilSourceQuadratic a u =
              ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 →
            ccmArchimedeanFormReflection a u = u) := by
  obtain ⟨κ, hκ, hcoer⟩ := exists_normForm_coercive h.pos h.injective h.t_pos
  obtain ⟨A, hA⟩ := eventually_atTop.mp ((tendsto_errorRate h (2 * m * max 1 (1 / κ))
    ((∑ j, |h.mult j|) * (1 / (2 * δ)))
      (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))).eventually
        (gt_mem_nhds (show (0 : ℝ) < g / 2 by linarith)))
  exact ⟨A, fun a ha => ⟨fun hF => ground_odd_of_balance_ge h hκ hcoer a hg hF (hA a.1 ha),
    fun hF => ground_even_of_balance_le h hκ hcoer a hg hF (hA a.1 ha)⟩⟩

end

end RHTower.CCMParityTopLayer
