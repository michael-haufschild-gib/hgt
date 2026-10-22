import GaloisForLFunctions.RHTower.CCM.CCMParityTopLayerEvenModel
import GaloisForLFunctions.RHTower.CCM.CCMParityTopLayerNoGo

/-!
# The ground-state parity of the restricted Weil form alternates under a finite top layer

**Theorem** (`exists_aperture_ground_even`). Under `FiniteTopLayer δ t`, if the leading-order
parity balance is negative at one aperture phase, `F(θ(a₁)) < 0`, then at arbitrarily large
apertures every ground state of the CCM restricted Weil form is reflection-even.

**Theorem** (`ground_parity_alternates_of_even_relations`). If moreover every integer relation
among the top ordinates has even coefficient sum, both happen: arbitrarily large apertures have
only odd ground states, and arbitrarily large apertures have only even ground states.

**Proof.** Mirror of `exists_aperture_ground_odd` with the roles of the sectors exchanged:
* the odd floor `Q ≥ −(e^{2δa}(max(λ_max(θ), 0)/2 + O(e^{−δa})) + L(a))‖u‖²`
  (`sourceQuadratic_ge_of_isOdd`);
* the even test `(P(a − ·) + P(a + ·)) · 1_{(−a,a)}` built from a maximizer for `θ + π𝟙`, whose top
  layer contributes `e^{2δa} T(θ)[·] ≤ −e^{2δa}(λ_max(θ + π𝟙) − O(a e^{−δa}))`;
* `F(θ(a)) ≤ −g` along returns of the aperture line, where
  `λ_max(θ + π𝟙) − max(λ_max(θ), 0) ≥ g/2`.
Under even relations the line returns near `θ(a₂) + π𝟙` for a point with `F(θ(a₂)) > 0`, so both
signs of `F` occur on the line.
-/

open Matrix Complex Filter Topology MeasureTheory Set
open RHTower.CCMParityQuartet RHTower.CCMParityCauchy GaloisForLFunctions.HTGeometry

namespace RHTower.CCMParityTopLayer

noncomputable section

variable {m : ℕ}

/-- **The off-line part of the truncated even model.** -/
theorem offLine_truncModel_even_le {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t)
    (x : Fin m → ℂ) {a : ℝ} (ha : 0 ≤ a) :
    ∑ q ∈ h.offLine,
        (zeroSumTerm (fun y => ((truncModel (evenProfileModel δ t x a) a y : ℝ) : ℂ))
          (xiSpectralPoint q)).re ≤
      Real.exp (2 * δ * a) * halfLineForm δ t h.mult (aperturePhase t a)
          (fun s => truncModel (evenProfileModel δ t x a) a (a - s)) +
        (∫ y, truncModel (evenProfileModel δ t x a) a y ^ 2) * h.lowWeight a := by
  set f : ℝ → ℝ := truncModel (evenProfileModel δ t x a) a with hf
  have hI : RealIntervalSource a f := realIntervalSource_truncModel_even t x a
  set N := ∫ y, f y ^ 2 with hN
  rw [h.sum_offLine_eq, sum_top_truncModel_even_eq h x a]
  have hlow : ∀ q ∈ h.lowSet, (zeroSumTerm (fun y => ((f y : ℝ) : ℂ)) (xiSpectralPoint q)).re ≤
      N * (2 * a * Real.exp (2 * a * |(xiSpectralPoint q).im|)) := by
    intro q _
    have h1 := norm_testTransform_sq_le_of_realIntervalSource ha hI (-xiSpectralPoint q)
    have h2 := norm_testTransform_sq_le_of_realIntervalSource ha hI
      (-(starRingEnd ℂ) (xiSpectralPoint q))
    simp only [Complex.neg_im, Complex.conj_im, neg_neg, abs_neg] at h1 h2
    refine (Complex.re_le_norm _).trans ?_
    unfold zeroSumTerm
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg (testTransform (fun y => ((f y : ℝ) : ℂ)) (-xiSpectralPoint q)),
      norm_nonneg (testTransform (fun y => ((f y : ℝ) : ℂ)) (-(starRingEnd ℂ) (xiSpectralPoint q))),
      sq_nonneg (‖testTransform (fun y => ((f y : ℝ) : ℂ)) (-xiSpectralPoint q)‖ -
        ‖testTransform (fun y => ((f y : ℝ) : ℂ)) (-(starRingEnd ℂ) (xiSpectralPoint q))‖)]
  have hlowsum : ∑ q ∈ h.lowSet,
      (zeroSumTerm (fun y => ((f y : ℝ) : ℂ)) (xiSpectralPoint q)).re ≤ N * h.lowWeight a := by
    rw [FiniteTopLayer.lowWeight, Finset.mul_sum]
    exact Finset.sum_le_sum hlow
  linarith

/-- **The decisive inequality for the even test.** -/
theorem evenTest_below_oddFloor {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t)
    (a : SuzukiPositiveAperture) {x : Fin m → ℂ} (hx : x ∈ unitLevel δ t)
    (hmax : quadForm δ t h.mult (halfTurn (aperturePhase t a.1)) x =
      ccmLambdaMax δ t h.mult (halfTurn (aperturePhase t a.1)))
    {C₀ Blam g : ℝ} (hC₀ : profileBound x ≤ C₀)
    (hBlam : max (ccmLambdaMax δ t h.mult (aperturePhase t a.1)) 0 ≤ Blam)
    (hgap : g / 2 ≤ ccmLambdaMax δ t h.mult (halfTurn (aperturePhase t a.1)) -
      max (ccmLambdaMax δ t h.mult (aperturePhase t a.1)) 0)
    (hR : errorRate h C₀ Blam (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) a.1 <
      g / 2) :
    ∑ q ∈ h.offLine,
        (zeroSumTerm (fun y => ((truncModel (evenProfileModel δ t x a.1) a.1 y : ℝ) : ℂ))
          (xiSpectralPoint q)).re +
      (2 * a.1 * (2 * profileBound x * (δ + ∑ j, |t j|)) + 2 * (2 * profileBound x)) ^ 2 *
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) <
      oddFloorConst h a.1 * ∫ y, truncModel (evenProfileModel δ t x a.1) a.1 y ^ 2 := by
  have hδ := h.pos
  have ha : 0 ≤ a.1 := a.2.le
  have hn : normForm δ t x = 1 := hx
  set θ := aperturePhase t a.1 with hθ
  set S : ℝ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => by positivity
  set N := ∫ y, truncModel (evenProfileModel δ t x a.1) a.1 y ^ 2 with hN
  have hN0 : 0 ≤ N := integral_nonneg fun _ => sq_nonneg _
  set Mt := ∑ j, |h.mult j| with hMt
  have hMt0 : 0 ≤ Mt := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set κ₁ := 1 + 1 / (2 * δ) with hκ₁
  have hκ₁0 : 0 ≤ κ₁ := by positivity
  set τ := δ + ∑ j, |t j| with hτ
  have hτ0 : 0 ≤ τ := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => abs_nonneg (t j))
    linarith
  set Cx := profileBound x with hCx
  have hCx0 : 0 ≤ Cx := profileBound_nonneg x
  have hC₀0 : 0 ≤ C₀ := hCx0.trans hC₀
  set E := Real.exp (-(δ * a.1)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set E2 := Real.exp (-(2 * δ * a.1)) with hE2
  have hE20 : 0 ≤ E2 := (Real.exp_pos _).le
  set X := Real.exp (2 * δ * a.1) with hX
  have hX0 : 0 < X := Real.exp_pos _
  have hXE2 : X * E2 = 1 := by rw [hX, hE2, ← Real.exp_add]; simp
  set Lw := h.lowWeight a.1 with hLw
  have hLw0 : 0 ≤ Lw := h.lowWeight_nonneg ha
  set lam := ccmLambdaMax δ t h.mult (halfTurn θ) with hlam
  set Λo := max (ccmLambdaMax δ t h.mult θ) 0 with hΛo
  have hΛo0 : 0 ≤ Λo := le_max_right _ _
  have hoff := offLine_truncModel_even_le h x ha
  have hform := halfLineForm_truncModel_even_le hδ t h.mult θ x hn ha
  have hq : quadForm δ t h.mult θ x = -lam := by
    have := quadForm_halfTurn δ t h.mult θ x
    rw [hmax] at this
    linarith
  rw [hq] at hform
  have hεx : (2 * a.1 * Cx + κ₁) * E ≤ (2 * a.1 * C₀ + κ₁) * E := by gcongr
  have hεx0 : 0 ≤ (2 * a.1 * Cx + κ₁) * E := by positivity
  have herr : Mt * (((2 * a.1 * Cx + κ₁) * E) * (2 * κ₁ + (2 * a.1 * Cx + κ₁) * E)) ≤
      Mt * (((2 * a.1 * C₀ + κ₁) * E) * (2 * κ₁ + (2 * a.1 * C₀ + κ₁) * E)) := by
    gcongr
  set err := Mt * (((2 * a.1 * C₀ + κ₁) * E) * (2 * κ₁ + (2 * a.1 * C₀ + κ₁) * E)) with herr_def
  have hhalf : halfLineForm δ t h.mult θ
      (fun s => truncModel (evenProfileModel δ t x a.1) a.1 (a.1 - s)) ≤ -lam + err := by
    linarith
  have hmass := integral_truncModel_even_sq_le hδ t x hn ha
  set η := 4 * a.1 * C₀ ^ 2 * E2 with hη
  have hη0 : 0 ≤ η := by positivity
  have hNle : N ≤ 2 + η := by
    have : 4 * a.1 * Cx ^ 2 * E2 ≤ η := by
      rw [hη]; gcongr
    linarith
  set K := 2 * a.1 * (2 * C₀ * τ) + 2 * (2 * C₀) with hK
  have hKx : (2 * a.1 * (2 * Cx * τ) + 2 * (2 * Cx)) ^ 2 ≤ K ^ 2 := by
    have h0 : 0 ≤ 2 * a.1 * (2 * Cx * τ) + 2 * (2 * Cx) := by positivity
    have h1 : 2 * a.1 * (2 * Cx * τ) + 2 * (2 * Cx) ≤ K := by rw [hK]; gcongr
    exact pow_le_pow_left₀ h0 h1 2
  set C₁ := 3 / (2 * δ) * E * Mt with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hRdef : errorRate h C₀ Blam S a.1 =
      err + Blam * η / 2 + C₁ * (2 + η) + (2 * Lw * (2 + η) + K ^ 2 * S) * E2 := by
    unfold errorRate
    simp only [hη, hC₁, herr_def, hK, hτ, hκ₁, hMt, hE, hE2, hLw]
  rw [hRdef] at hR
  have hBlam0 : 0 ≤ Blam := hΛo0.trans hBlam
  have hfloor : oddFloorConst h a.1 = -(X * (Λo / 2 + C₁) + Lw) := by
    unfold oddFloorConst; rw [← hΛo]
  rw [hfloor]
  have hkey : X * (g / 2 - err - Blam * η / 2 - C₁ * (2 + η)) > 2 * Lw * (2 + η) + K ^ 2 * S := by
    have h1 : (2 * Lw * (2 + η) + K ^ 2 * S) * E2 < g / 2 - err - Blam * η / 2 - C₁ * (2 + η) := by
      linarith
    have h2 := mul_lt_mul_of_pos_left h1 hX0
    rw [← mul_assoc, mul_comm X, mul_assoc, hXE2, mul_one] at h2
    linarith
  have hΛη : Λo * η ≤ Blam * η := mul_le_mul_of_nonneg_right hBlam hη0
  have hlow2 : N * Lw ≤ (2 + η) * Lw := mul_le_mul_of_nonneg_right hNle hLw0
  have hc0 : 0 ≤ X * (Λo / 2 + C₁) + Lw := by positivity
  have hfloorN : (X * (Λo / 2 + C₁) + Lw) * N ≤ (X * (Λo / 2 + C₁) + Lw) * (2 + η) :=
    mul_le_mul_of_nonneg_left hNle hc0
  have hupper : X * halfLineForm δ t h.mult θ
      (fun s => truncModel (evenProfileModel δ t x a.1) a.1 (a.1 - s)) ≤ X * (-lam + err) :=
    mul_le_mul_of_nonneg_left hhalf hX0.le
  have hKS : (2 * a.1 * (2 * Cx * τ) + 2 * (2 * Cx)) ^ 2 * S ≤ K ^ 2 * S :=
    mul_le_mul_of_nonneg_right hKx hS0
  have hinner : g / 2 - err - Blam * η / 2 - C₁ * (2 + η) ≤
      lam - err - Λo - Λo * η / 2 - C₁ * (2 + η) := by linarith
  have hmono := mul_le_mul_of_nonneg_left hinner hX0.le
  have e1 : (X * (Λo / 2 + C₁) + Lw) * (2 + η) =
      X * (Λo + Λo * η / 2 + C₁ * (2 + η)) + Lw * (2 + η) := by ring
  have e2 : X * (lam - err - Λo - Λo * η / 2 - C₁ * (2 + η)) =
      X * (lam - err) - X * (Λo + Λo * η / 2 + C₁ * (2 + η)) := by ring
  have e3 : X * (-lam + err) = -(X * (lam - err)) := by ring
  have e4 : -(X * (Λo / 2 + C₁) + Lw) * N = -((X * (Λo / 2 + C₁) + Lw) * N) := by ring
  rw [e4]
  linarith [hoff, hkey, hfloorN, hupper, hKS, hlow2, hmono, e1, e2, e3]

/-- **Returns with a uniformly negative balance.** -/
theorem exists_balance_le_frequently {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M : Fin m → ℝ)
    (hneg : ∃ a₁ : ℝ, ccmParityBalance δ t M (aperturePhase t a₁) < 0) :
    ∃ g : ℝ, 0 < g ∧ ∀ N : ℝ, ∃ a : ℝ, N ≤ a ∧
      ccmParityBalance δ t M (aperturePhase t a) ≤ -g := by
  obtain ⟨a₁, ha₁⟩ := hneg
  set θ₁ := aperturePhase t a₁ with hθ₁
  have hpos : 0 < ccmParityBalance δ t M (halfTurn θ₁) := by
    rw [ccmParityBalance_halfTurn]; linarith
  obtain ⟨η, hη, hwin⟩ := exists_phase_window_balance_ge hδ ht htpos hm M _ hpos
  refine ⟨ccmParityBalance δ t M (halfTurn θ₁) / 2, by linarith, fun N => ?_⟩
  obtain ⟨a, haN, z, hz⟩ := exists_large_aperture_phase_near (x := fun j => a₁ * (t j / Real.pi))
    (fun k hk => ⟨0, by
      rw [Int.cast_zero]
      have : ∑ j, (k j : ℝ) * (a₁ * (t j / Real.pi)) = a₁ / Real.pi * ∑ j, (k j : ℝ) * t j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, hk, mul_zero]⟩) hη N
  refine ⟨a, haN, ?_⟩
  have hnear := hwin (halfTurn (aperturePhase t a)) z fun j => by
    rw [halfTurn_sub]
    have h := hz j
    rwa [show -2 * Real.pi * (a₁ * (t j / Real.pi)) = -2 * t j * a₁ by field_simp] at h
  have := ccmParityBalance_halfTurn δ t M (aperturePhase t a)
  linarith

/-- **Parity selection prefers the even sector.** If the leading-order parity balance is negative
at one aperture phase, then arbitrarily large apertures have only reflection-even ground states of
the CCM restricted Weil form. -/
theorem exists_aperture_ground_even {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t)
    (hneg : ∃ a₁ : ℝ, ccmParityBalance δ t h.mult (aperturePhase t a₁) < 0) (A : ℝ) :
    ∃ a : SuzukiPositiveAperture, A < a.1 ∧
      ∀ u : CCMArchimedeanFormDomain a,
        ccmRestrictedWeilSourceQuadratic a u =
            ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 →
          ccmArchimedeanFormReflection a u = u := by
  have hδ := h.pos
  have ht := h.injective
  have htpos := h.t_pos
  have hm := h.nonempty
  obtain ⟨g, hg0, hret⟩ := exists_balance_le_frequently hδ ht htpos hm h.mult hneg
  obtain ⟨κ, hκ, hcoer⟩ := exists_normForm_coercive hδ ht htpos
  set C₀ : ℝ := 2 * m * max 1 (1 / κ) with hC₀
  set Blam : ℝ := (∑ j, |h.mult j|) * (1 / (2 * δ)) with hBlam
  set S : ℝ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) with hS
  have hev := (tendsto_errorRate h C₀ Blam S).eventually (gt_mem_nhds (show (0 : ℝ) < g / 2 by
    linarith))
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.mp hev
  obtain ⟨a₀, ha₀N, hga₀⟩ := hret (max (max A₀ (A + 1)) 1)
  have ha₀pos : 0 < a₀ := by
    have := le_max_right (max A₀ (A + 1)) 1
    linarith
  set a : SuzukiPositiveAperture := ⟨a₀, ha₀pos⟩ with ha_def
  have haA : A < a.1 := by
    have := le_max_right A₀ (A + 1)
    have := le_max_left (max A₀ (A + 1)) 1
    show A < a₀
    linarith
  refine ⟨a, haA, ?_⟩
  have hR : errorRate h C₀ Blam S a.1 < g / 2 := by
    apply hA₀
    have := le_max_left A₀ (A + 1)
    have := le_max_left (max A₀ (A + 1)) 1
    show A₀ ≤ a₀
    linarith
  obtain ⟨x, hx, hmax, -⟩ := exists_isMaxOn_quadForm hδ ht htpos hm h.mult
    (halfTurn (aperturePhase t a.1))
  have hCx : profileBound x ≤ C₀ := profileBound_le_of_coercive hκ hcoer hx
  have hBlamx : max (ccmLambdaMax δ t h.mult (aperturePhase t a.1)) 0 ≤ Blam := by
    refine max_le (lambdaMax_le hδ ht htpos hm h.mult _) ?_
    positivity
  have hgap : g / 2 ≤ ccmLambdaMax δ t h.mult (halfTurn (aperturePhase t a.1)) -
      max (ccmLambdaMax δ t h.mult (aperturePhase t a.1)) 0 := by
    have hge : g ≤ ccmParityBalance δ t h.mult (halfTurn (aperturePhase t a.1)) := by
      rw [ccmParityBalance_halfTurn]; linarith
    have := gap_ge_of_balance_ge hδ ht htpos hm h.mult _ hge hg0
    rwa [ccmLambdaMax_halfTurn_halfTurn] at this
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

/-- Under even relations the balance is negative somewhere on the aperture line. -/
theorem exists_balance_neg_of_even_relations {δ : ℝ} {t M : Fin m → ℝ} (hδ : 0 < δ)
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hM : ∀ j, 0 < M j) (hm : 0 < m)
    (heven : ∀ k : Fin m → ℤ, ∑ j, (k j : ℝ) * t j = 0 → Even (∑ j, k j)) :
    ∃ a₁ : ℝ, ccmParityBalance δ t M (aperturePhase t a₁) < 0 := by
  obtain ⟨a₂, -, ha₂⟩ := ccm_exists_large_aperture_odd_wins_of_even_relations hδ ht htpos hM hm
    heven 0
  set θ₂ := aperturePhase t a₂ with hθ₂
  have ha₂' : 0 < ccmParityBalance δ t M θ₂ := ha₂
  obtain ⟨η, hη, hwin⟩ := exists_phase_window_balance_ge hδ ht htpos hm M _ ha₂'
  have hrel : ∀ k : Fin m → ℤ, ∑ j, (k j : ℝ) * t j = 0 →
      ∃ z : ℤ, ∑ j, (k j : ℝ) * (a₂ * (t j / Real.pi) - 1 / 2) = z := by
    intro k h1
    obtain ⟨n, hn⟩ := heven k h1
    refine ⟨-n, ?_⟩
    have hk : (∑ j, (k j : ℝ)) = n + n := by exact_mod_cast hn
    have : ∑ j, (k j : ℝ) * (a₂ * (t j / Real.pi) - 1 / 2) =
        a₂ / Real.pi * (∑ j, (k j : ℝ) * t j) - (∑ j, (k j : ℝ)) / 2 := by
      rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, h1, hk]
    push_cast
    ring
  obtain ⟨a, -, z, hz⟩ := exists_large_aperture_phase_near hrel hη 0
  refine ⟨a, ?_⟩
  have hnear := hwin (halfTurn (aperturePhase t a)) (fun j => z j + 1) fun j => by
    have h := hz j
    have e : -2 * Real.pi * (a₂ * (t j / Real.pi) - 1 / 2) = θ₂ j + Real.pi := by
      simp only [hθ₂, aperturePhase]; field_simp; ring
    rw [e] at h
    have e2 : halfTurn (aperturePhase t a) j - θ₂ j - ((z j + 1 : ℤ) : ℝ) * (2 * Real.pi) =
        -2 * t j * a - (θ₂ j + Real.pi) - (z j : ℝ) * (2 * Real.pi) := by
      simp only [halfTurn, aperturePhase]; push_cast; ring
    rw [e2]
    exact h
  have := ccmParityBalance_halfTurn δ t M (aperturePhase t a)
  linarith

/-- **The ground-state parity alternates.** Under a finite top layer whose ordinate relations all
have even coefficient sum, arbitrarily large apertures have only reflection-odd ground states, and
arbitrarily large apertures have only reflection-even ground states. -/
theorem ground_parity_alternates_of_even_relations {δ : ℝ} {t : Fin m → ℝ}
    (h : FiniteTopLayer δ t)
    (heven : ∀ k : Fin m → ℤ, ∑ j, (k j : ℝ) * t j = 0 → Even (∑ j, k j)) (A : ℝ) :
    (∃ a : SuzukiPositiveAperture, A < a.1 ∧
      ∀ u : CCMArchimedeanFormDomain a,
        ccmRestrictedWeilSourceQuadratic a u =
            ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 →
          ccmArchimedeanFormReflection a u = -u) ∧
    (∃ a : SuzukiPositiveAperture, A < a.1 ∧
      ∀ u : CCMArchimedeanFormDomain a,
        ccmRestrictedWeilSourceQuadratic a u =
            ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 →
          ccmArchimedeanFormReflection a u = u) :=
  ⟨exists_aperture_ground_odd_of_even_relations h heven A,
    exists_aperture_ground_even h (exists_balance_neg_of_even_relations h.pos h.injective
      h.t_pos h.mult_pos h.nonempty heven) A⟩

end

end RHTower.CCMParityTopLayer
