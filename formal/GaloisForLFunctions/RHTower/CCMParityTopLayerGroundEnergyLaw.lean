import GaloisForLFunctions.RHTower.CCMParityTopLayerAlternation

/-!
# The ground-energy law of the restricted Weil form under a finite top layer

Let `Λ*(a) = max(λ_max(T(θ(a))), λ_max(T(θ(a) + π𝟙)))` be the spectral radius of the leading-order
Cauchy model at the aperture phases `θ_j(a) = −2t_j a`.

**Theorem** (`groundEnergy_law`). Under `FiniteTopLayer δ t`, for every `ε > 0` and all
sufficiently large apertures,

`−(e^{2δa}/2)(Λ*(a) + ε) ≤ μ₀(a) ≤ −(e^{2δa}/2)(Λ*(a) − ε)`,

where `μ₀(a)` is the ground energy of the CCM restricted Weil form. Moreover `Λ*` is bounded above
and below by positive constants, so `c e^{2δa} ≤ −μ₀(a) ≤ C e^{2δa}` for large `a`
(`exists_groundEnergy_exponential_bounds`): the ground energy detects the top height `δ` exactly.

**Proof.**
* Lower bound: a pure-parity ground state lies above the even or the odd floor, and the larger of
  the two floor constants is `−(e^{2δa}(Λ*/2 + O(e^{−δa})) + L(a))`.
* Upper bound: the odd test (maximizer for `θ`) and the even test (maximizer for `θ + π𝟙`) have
  Rayleigh quotients below `−(e^{2δa}/2)(λ_max − ε)` once the error rate is below `ε`.
* `λ_max(θ) ≥ c₀ > 0` uniformly: the real-span vector whose pairings are
  `(e^{−iθ_{j₀}/2}, 0, …)` has form value `M_{j₀}` and norm bounded through `G⁻¹`.
-/

open Matrix Complex Filter Topology MeasureTheory Set
open RHTower.CCMParityQuartet RHTower.CCMParityCauchy GaloisForLFunctions.HTGeometry

namespace RHTower.CCMParityTopLayer

noncomputable section

variable {m : ℕ}

/-! ## A uniform lower bound for the top of the model spectrum -/

theorem exists_lambdaMax_lower {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) (hm : 0 < m) {M : Fin m → ℝ} (hM : ∀ j, 0 < M j) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ θ : Fin m → ℝ, c₀ ≤ ccmLambdaMax δ t M θ := by
  classical
  set G := cauchyGram (ccmNodes δ t) with hG
  have hdet : G.det ≠ 0 := det_cauchyGram_ccmNodes_ne_zero hδ ht htpos
  set j₀ : Fin m := ⟨0, hm⟩ with hj₀
  set K : ℝ := ∑ i, ∑ l, ‖G⁻¹ i l‖ with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨M j₀ / (K + 1), div_pos (hM j₀) (by linarith), fun θ => ?_⟩
  set w : Fin m → ℂ := Pi.single j₀ (Complex.exp (-(((θ j₀ / 2 : ℝ) : ℂ) * I))) with hw
  set b := realLift w with hb
  obtain ⟨x, hx0⟩ := exists_realLift_cauchyGram_mulVec_eq hδ ht htpos (isRealVec_realLift w)
  have hx : G *ᵥ realLift x = b := hx0
  have hy : realLift x = G⁻¹ *ᵥ b := by
    rw [← hx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hdet), Matrix.one_mulVec]
  have hbnorm : ∀ l, ‖b l‖ ≤ 1 := by
    intro l
    rcases l with j | j <;>
    · simp only [hb, realLift, Sum.elim_inl, Sum.elim_inr, Complex.norm_conj, hw]
      by_cases hj : j = j₀
      · subst hj
        rw [Pi.single_eq_same]
        rw [show -(((θ j₀ / 2 : ℝ) : ℂ) * I) = ((-(θ j₀ / 2) : ℝ) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I]
      · rw [Pi.single_eq_of_ne hj, norm_zero]; norm_num
  -- the form value
  have hq : quadForm δ t M θ x = M j₀ := by
    unfold quadForm
    rw [hx, Fintype.sum_sum_type]
    have hinl : ∀ j, phaseWeight M θ (Sum.inl j) * b (Sum.inl j) ^ 2 =
        if j = j₀ then ((M j₀ / 2 : ℝ) : ℂ) else 0 := by
      intro j
      simp only [phaseWeight, Sum.elim_inl, hb, realLift, hw]
      by_cases hj : j = j₀
      · subst hj
        rw [Pi.single_eq_same, if_pos rfl, ← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
        rw [show ((θ j₀ : ℂ) * I + ((2 : ℕ) : ℂ) * -(((θ j₀ / 2 : ℝ) : ℂ) * I)) = 0 by
          push_cast; ring, Complex.exp_zero, mul_one]
      · rw [Pi.single_eq_of_ne hj, if_neg hj]; simp
    have hinr : ∀ j, phaseWeight M θ (Sum.inr j) * b (Sum.inr j) ^ 2 =
        if j = j₀ then ((M j₀ / 2 : ℝ) : ℂ) else 0 := by
      intro j
      simp only [phaseWeight, Sum.elim_inr, hb, realLift, hw]
      by_cases hj : j = j₀
      · subst hj
        rw [Pi.single_eq_same, if_pos rfl, ← Complex.exp_conj, ← Complex.exp_nat_mul, mul_assoc,
          ← Complex.exp_add]
        rw [show (-((θ j₀ : ℂ) * I) + ((2 : ℕ) : ℂ) * (starRingEnd ℂ) (-(((θ j₀ / 2 : ℝ) : ℂ) * I)))
          = 0 by simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring,
          Complex.exp_zero, mul_one]
      · rw [Pi.single_eq_of_ne hj, if_neg hj]; simp
    simp_rw [hinl, hinr]
    rw [Finset.sum_ite_eq' Finset.univ j₀]
    simp only [Finset.mem_univ, if_true]
    rw [← Complex.ofReal_add, Complex.ofReal_re]
    ring
  -- the norm bound
  have hn : normForm δ t x ≤ K := by
    unfold normForm
    rw [hx, hy]
    refine (Complex.re_le_norm _).trans ?_
    simp only [dotProduct]
    refine (norm_sum_le _ _).trans ?_
    rw [hK]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul]
    calc ‖(G⁻¹ *ᵥ b) i‖ * ‖b i‖ ≤ ‖(G⁻¹ *ᵥ b) i‖ * 1 :=
          mul_le_mul_of_nonneg_left (hbnorm i) (norm_nonneg _)
      _ = ‖(G⁻¹ *ᵥ b) i‖ := mul_one _
      _ ≤ ∑ l, ‖G⁻¹ i l‖ := by
          simp only [mulVec, dotProduct]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
          rw [norm_mul]
          calc ‖G⁻¹ i l‖ * ‖b l‖ ≤ ‖G⁻¹ i l‖ * 1 :=
                mul_le_mul_of_nonneg_left (hbnorm l) (norm_nonneg _)
            _ = ‖G⁻¹ i l‖ := mul_one _
  have hxne : x ≠ 0 := by
    intro h0
    have hb0 : b = 0 := by
      rw [← hx, h0]
      funext i
      rcases i with j | j <;> simp [realLift, Matrix.mulVec, dotProduct]
    have h1 := congr_fun hb0 (Sum.inl j₀)
    rw [hb] at h1
    simp only [realLift, Sum.elim_inl, hw, Pi.single_eq_same, Pi.zero_apply] at h1
    exact Complex.exp_ne_zero _ h1
  have hpos := normForm_pos hδ ht htpos hxne
  have hle := quadForm_le_lambdaMax_mul hδ ht htpos hm M θ x
  rw [hq] at hle
  have hlam : 0 < ccmLambdaMax δ t M θ := by
    by_contra hneg
    push Not at hneg
    have := mul_le_mul_of_nonneg_right hneg hpos.le
    linarith [hM j₀]
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem lambdaMax_add_lambdaMax_halfTurn_nonneg {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M θ : Fin m → ℝ) :
    0 ≤ ccmLambdaMax δ t M θ + ccmLambdaMax δ t M (halfTurn θ) := by
  obtain ⟨x, hx, hmax, -⟩ := exists_isMaxOn_quadForm hδ ht htpos hm M θ
  have h1 := lambdaMax_halfTurn_mul_ge hδ ht htpos hm M θ x
  have hn : normForm δ t x = 1 := hx
  rw [hn, mul_one] at h1
  linarith

/-! ## Ground energy versus tests and floors -/

theorem groundEnergy_lt_of_smooth_below {a : SuzukiPositiveAperture} {c : ℝ}
    (hv : ∃ v : CCMComplexSmoothInteriorSource a,
      ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector <
        c * ‖ccmArchimedeanFormToAperture a v.toCCMFormVector‖ ^ 2) :
    ccmRestrictedWeilGroundEnergy a < c := by
  obtain ⟨v, hv⟩ := hv
  have hμv := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a v.toCCMFormVector
  have hvpos : 0 < ‖ccmArchimedeanFormToAperture a v.toCCMFormVector‖ ^ 2 := by
    by_contra hle
    push Not at hle
    have h0 : ‖ccmArchimedeanFormToAperture a v.toCCMFormVector‖ ^ 2 = 0 :=
      le_antisymm hle (by positivity)
    rw [h0] at hv hμv
    linarith
  by_contra hge
  push Not at hge
  have := mul_le_mul_of_nonneg_right hge hvpos.le
  linarith

theorem groundEnergy_ge_min_floor {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t)
    (a : SuzukiPositiveAperture) :
    min (evenFloorConst h a.1) (oddFloorConst h a.1) ≤ ccmRestrictedWeilGroundEnergy a := by
  obtain ⟨f, hf0, hpar, hground⟩ := exists_ccmRestrictedWeil_pureParity_groundFormState a
  have hpos : 0 < ‖ccmArchimedeanFormToAperture a f‖ ^ 2 := by positivity
  rcases hpar with he | ho
  · have hfl := sourceQuadratic_ge_of_isEven h f he
    rw [hground] at hfl
    have := le_of_mul_le_mul_right hfl hpos
    exact (min_le_left _ _).trans this
  · have hfl := sourceQuadratic_ge_of_isOdd h f ho
    rw [hground] at hfl
    have := le_of_mul_le_mul_right hfl hpos
    exact (min_le_right _ _).trans this

/-- **The test inequality with a prescribed level.** If the off-line part of a test is at most
`−X(λ − err) + N L` and the error rate is below `ε ≤ λ`, the test lies below `−(X/2)(λ − ε)`. -/
theorem test_below_level {X E2 lam err Blam η C₁ Lw K S N Kx ε offline : ℝ} (hX0 : 0 < X)
    (hε0 : 0 ≤ ε)
    (hE2 : X * E2 = 1) (hE20 : 0 ≤ E2) (hlam : lam ≤ Blam) (hε : ε ≤ lam) (hη0 : 0 ≤ η)
    (hC₁0 : 0 ≤ C₁) (hLw0 : 0 ≤ Lw) (hS0 : 0 ≤ S) (hNle : N ≤ 2 + η)
    (hKx : Kx ^ 2 ≤ K ^ 2)
    (hoff : offline ≤ -(X * (lam - err)) + N * Lw)
    (hR : err + Blam * η / 2 + C₁ * (2 + η) + (2 * Lw * (2 + η) + K ^ 2 * S) * E2 < ε) :
    offline + Kx ^ 2 * S < -(X / 2 * (lam - ε)) * N := by
  have hKS : Kx ^ 2 * S ≤ K ^ 2 * S := mul_le_mul_of_nonneg_right hKx hS0
  have h1 : ((2 + η) * Lw + K ^ 2 * S) * E2 < ε - err - Blam * η / 2 := by
    have : ((2 + η) * Lw + K ^ 2 * S) * E2 ≤ (2 * Lw * (2 + η) + K ^ 2 * S) * E2 := by
      apply mul_le_mul_of_nonneg_right _ hE20
      nlinarith
    have : 0 ≤ C₁ * (2 + η) := by positivity
    linarith
  have h2 := mul_lt_mul_of_pos_left h1 hX0
  rw [← mul_assoc, mul_comm X, mul_assoc, hE2, mul_one] at h2
  have hlow : N * Lw ≤ (2 + η) * Lw := mul_le_mul_of_nonneg_right hNle hLw0
  have hle1 : (lam - ε) * η ≤ Blam * η := mul_le_mul_of_nonneg_right (by linarith) hη0
  have hmono : X * (ε - err - Blam * η / 2) ≤ X * (ε - err - (lam - ε) * η / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hX0.le
  have hN2 : (lam - ε) * N ≤ (lam - ε) * (2 + η) :=
    mul_le_mul_of_nonneg_left hNle (by linarith)
  have hN3 := mul_le_mul_of_nonneg_left hN2 (show 0 ≤ X / 2 by positivity)
  have e1 : X / 2 * ((lam - ε) * (2 + η)) = X * (lam - ε) + X * ((lam - ε) * η / 2) := by ring
  have e2 : X * (ε - err - (lam - ε) * η / 2) =
      X * (lam - err) - X * (lam - ε) - X * ((lam - ε) * η / 2) := by ring
  have e3 : -(X / 2 * (lam - ε)) * N = -(X / 2 * ((lam - ε) * N)) := by ring
  rw [e3]
  linarith

/-! ## The law -/

/-- The spectral radius `Λ*(a)` of the leading-order model at aperture `a`. -/
def topRadius (δ : ℝ) (t M : Fin m → ℝ) (a : ℝ) : ℝ :=
  max (ccmLambdaMax δ t M (aperturePhase t a)) (ccmLambdaMax δ t M (halfTurn (aperturePhase t a)))

theorem tendsto_floorError {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t) :
    Tendsto (fun a => 2 * (3 / (2 * δ) * Real.exp (-(δ * a)) * ∑ j, |h.mult j|) +
      2 * (h.lowWeight a * Real.exp (-(2 * δ * a)))) atTop (𝓝 0) := by
  have hδ := h.pos
  have tE : Tendsto (fun a : ℝ => Real.exp (-(δ * a))) atTop (𝓝 0) := by
    have := tendsto_pow_mul_exp_neg_mul hδ 0
    simpa using this
  have := ((tE.const_mul (3 / (2 * δ))).mul_const (∑ j, |h.mult j|)).const_mul 2 |>.add
    ((tendsto_lowWeight_mul_exp h).const_mul 2)
  simpa using this

/-- The pairing error `Σ_j|M_j| ε(2κ + ε)`, `ε = (2aC + κ) e^{−δa}`, `κ = 1 + 1/(2δ)`. -/
def pairingError (δ C : ℝ) (Mt a : ℝ) : ℝ :=
  Mt * (((2 * a * C + (1 + 1 / (2 * δ))) * Real.exp (-(δ * a))) *
    (2 * (1 + 1 / (2 * δ)) + (2 * a * C + (1 + 1 / (2 * δ))) * Real.exp (-(δ * a))))

theorem pairingError_mono {δ : ℝ} (hδ : 0 < δ) {C C' Mt a : ℝ} (hMt : 0 ≤ Mt) (ha : 0 ≤ a)
    (hC : 0 ≤ C) (hCC' : C ≤ C') : pairingError δ C Mt a ≤ pairingError δ C' Mt a := by
  unfold pairingError
  have hκ : 0 ≤ 1 + 1 / (2 * δ) := by positivity
  have hE : 0 ≤ Real.exp (-(δ * a)) := (Real.exp_pos _).le
  have h1 : 0 ≤ (2 * a * C + (1 + 1 / (2 * δ))) * Real.exp (-(δ * a)) := by positivity
  have h2 : (2 * a * C + (1 + 1 / (2 * δ))) * Real.exp (-(δ * a)) ≤
      (2 * a * C' + (1 + 1 / (2 * δ))) * Real.exp (-(δ * a)) := by gcongr
  apply mul_le_mul_of_nonneg_left _ hMt
  apply mul_le_mul h2 (by linarith) (by positivity) (h1.trans h2)

theorem errorRate_eq {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t) (C₀ Blam S a : ℝ) :
    errorRate h C₀ Blam S a =
      pairingError δ C₀ (∑ j, |h.mult j|) a +
        Blam * (4 * a * C₀ ^ 2 * Real.exp (-(2 * δ * a))) / 2 +
        3 / (2 * δ) * Real.exp (-(δ * a)) * (∑ j, |h.mult j|) *
          (2 + 4 * a * C₀ ^ 2 * Real.exp (-(2 * δ * a))) +
        (2 * h.lowWeight a * (2 + 4 * a * C₀ ^ 2 * Real.exp (-(2 * δ * a))) +
          (2 * a * (2 * C₀ * (δ + ∑ j, |t j|)) + 2 * (2 * C₀)) ^ 2 * S) *
          Real.exp (-(2 * δ * a)) := rfl

/-- **A model test below a level.** -/
theorem groundEnergy_lt_of_model {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t)
    (a : SuzukiPositiveAperture) {C₀ Blam ε lam : ℝ} (hε0 : 0 ≤ ε)
    (hR : errorRate h C₀ Blam (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) a.1 < ε)
    (hlamB : lam ≤ Blam) (hε : ε ≤ lam) {Cx : ℝ} (hCx0 : 0 ≤ Cx) (hCx : Cx ≤ C₀)
    (W : ℝ → ℝ) (hW : ContDiff ℝ (⊤ : ℕ∞) W) (hD : ∀ y ∈ Icc (-a.1) a.1, |W y| ≤ 2 * Cx)
    (hD' : ∀ y ∈ Icc (-a.1) a.1, |deriv W y| ≤ 2 * Cx * (δ + ∑ j, |t j|))
    (hoff : ∑ q ∈ h.offLine, (zeroSumTerm (fun y => ((truncModel W a.1 y : ℝ) : ℂ))
        (xiSpectralPoint q)).re ≤
      -(Real.exp (2 * δ * a.1) * (lam - pairingError δ C₀ (∑ j, |h.mult j|) a.1)) +
        (∫ y, truncModel W a.1 y ^ 2) * h.lowWeight a.1)
    (hN : ∫ y, truncModel W a.1 y ^ 2 ≤ 2 + 4 * a.1 * C₀ ^ 2 * Real.exp (-(2 * δ * a.1))) :
    ccmRestrictedWeilGroundEnergy a < -(Real.exp (2 * δ * a.1) / 2 * (lam - ε)) := by
  have hδ := h.pos
  have ha0 : 0 ≤ a.1 := a.2.le
  have hC₀0 : 0 ≤ C₀ := hCx0.trans hCx
  have hτ0 : 0 ≤ δ + ∑ j, |t j| := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => abs_nonneg (t j))
    linarith
  have hKx : (2 * a.1 * (2 * Cx * (δ + ∑ j, |t j|)) + 2 * (2 * Cx)) ^ 2 ≤
      (2 * a.1 * (2 * C₀ * (δ + ∑ j, |t j|)) + 2 * (2 * C₀)) ^ 2 := by
    have h0 : 0 ≤ 2 * a.1 * (2 * Cx * (δ + ∑ j, |t j|)) + 2 * (2 * Cx) := by positivity
    have h1 : 2 * a.1 * (2 * Cx * (δ + ∑ j, |t j|)) + 2 * (2 * Cx) ≤
        2 * a.1 * (2 * C₀ * (δ + ∑ j, |t j|)) + 2 * (2 * C₀) := by gcongr
    exact pow_le_pow_left₀ h0 h1 2
  rw [errorRate_eq] at hR
  apply groundEnergy_lt_of_smooth_below
  apply exists_smooth_below_model h a W hW hD hD'
  have hXE2 : Real.exp (2 * δ * a.1) * Real.exp (-(2 * δ * a.1)) = 1 := by
    rw [← Real.exp_add]; simp
  exact test_below_level (Real.exp_pos _) hε0 hXE2 (Real.exp_pos _).le hlamB hε
    (by positivity) (by positivity) (h.lowWeight_nonneg ha0) (tsum_nonneg fun _ => by positivity)
    hN hKx hoff hR

/-- The odd test at aperture `a`: `μ₀(a) < −(e^{2δa}/2)(λ_max(θ(a)) − ε)`. -/
theorem groundEnergy_lt_oddTest {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t)
    (a : SuzukiPositiveAperture) {κ : ℝ} (hκ : 0 < κ)
    (hcoer : ∀ x, κ * ‖x‖ ^ 2 ≤ normForm δ t x) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hR : errorRate h (2 * m * max 1 (1 / κ)) ((∑ j, |h.mult j|) * (1 / (2 * δ)))
      (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) a.1 < ε)
    (hε : ε ≤ ccmLambdaMax δ t h.mult (aperturePhase t a.1)) :
    ccmRestrictedWeilGroundEnergy a <
      -(Real.exp (2 * δ * a.1) / 2 * (ccmLambdaMax δ t h.mult (aperturePhase t a.1) - ε)) := by
  have hδ := h.pos
  have ha0 : 0 ≤ a.1 := a.2.le
  obtain ⟨x, hx, hmax, -⟩ := exists_isMaxOn_quadForm hδ h.injective h.t_pos h.nonempty h.mult
    (aperturePhase t a.1)
  have hn : normForm δ t x = 1 := hx
  have hCx := profileBound_le_of_coercive hκ hcoer hx
  have hCx0 := profileBound_nonneg x
  have hMt : 0 ≤ ∑ j, |h.mult j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine groundEnergy_lt_of_model h a hε0 hR
    (lambdaMax_le hδ h.injective h.t_pos h.nonempty h.mult _) hε hCx0 hCx
    (oddProfileModel δ t x a.1) (contDiff_oddProfileModel δ t x a.1)
    (fun y hy => abs_oddProfileModel_le hδ.le t x hy)
    (fun y hy => abs_deriv_oddProfileModel_le hδ.le t x hy) ?_ ?_
  · have hoff := offLine_truncModel_le h x ha0
    have hform := halfLineForm_truncModel_ge hδ t h.mult (aperturePhase t a.1) x hn ha0
    rw [hmax] at hform
    have herr := pairingError_mono hδ hMt ha0 hCx0 hCx
    unfold pairingError at herr
    have h1 := mul_le_mul_of_nonneg_left hform (Real.exp_pos (2 * δ * a.1)).le
    have h2 := mul_le_mul_of_nonneg_left herr (Real.exp_pos (2 * δ * a.1)).le
    unfold pairingError
    linarith
  · have hmass := integral_truncModel_sq_le hδ t x hn ha0
    have : 4 * a.1 * profileBound x ^ 2 * Real.exp (-(2 * δ * a.1)) ≤
        4 * a.1 * (2 * m * max 1 (1 / κ)) ^ 2 * Real.exp (-(2 * δ * a.1)) := by gcongr
    linarith

/-- The even test at aperture `a`: `μ₀(a) < −(e^{2δa}/2)(λ_max(θ(a) + π𝟙) − ε)`. -/
theorem groundEnergy_lt_evenTest {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t)
    (a : SuzukiPositiveAperture) {κ : ℝ} (hκ : 0 < κ)
    (hcoer : ∀ x, κ * ‖x‖ ^ 2 ≤ normForm δ t x) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hR : errorRate h (2 * m * max 1 (1 / κ)) ((∑ j, |h.mult j|) * (1 / (2 * δ)))
      (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) a.1 < ε)
    (hε : ε ≤ ccmLambdaMax δ t h.mult (halfTurn (aperturePhase t a.1))) :
    ccmRestrictedWeilGroundEnergy a < -(Real.exp (2 * δ * a.1) / 2 *
      (ccmLambdaMax δ t h.mult (halfTurn (aperturePhase t a.1)) - ε)) := by
  have hδ := h.pos
  have ha0 : 0 ≤ a.1 := a.2.le
  obtain ⟨x, hx, hmax, -⟩ := exists_isMaxOn_quadForm hδ h.injective h.t_pos h.nonempty h.mult
    (halfTurn (aperturePhase t a.1))
  have hn : normForm δ t x = 1 := hx
  have hCx := profileBound_le_of_coercive hκ hcoer hx
  have hCx0 := profileBound_nonneg x
  have hMt : 0 ≤ ∑ j, |h.mult j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine groundEnergy_lt_of_model h a hε0 hR
    (lambdaMax_le hδ h.injective h.t_pos h.nonempty h.mult _) hε hCx0 hCx
    (evenProfileModel δ t x a.1) (contDiff_evenProfileModel δ t x a.1)
    (fun y hy => abs_evenProfileModel_le hδ.le t x hy)
    (fun y hy => abs_deriv_evenProfileModel_le hδ.le t x hy) ?_ ?_
  · have hoff := offLine_truncModel_even_le h x ha0
    have hform := halfLineForm_truncModel_even_le hδ t h.mult (aperturePhase t a.1) x hn ha0
    have hq : quadForm δ t h.mult (aperturePhase t a.1) x =
        -ccmLambdaMax δ t h.mult (halfTurn (aperturePhase t a.1)) := by
      have := quadForm_halfTurn δ t h.mult (aperturePhase t a.1) x
      rw [hmax] at this
      linarith
    rw [hq] at hform
    have herr := pairingError_mono hδ hMt ha0 hCx0 hCx
    unfold pairingError at herr
    have h1 := mul_le_mul_of_nonneg_left hform (Real.exp_pos (2 * δ * a.1)).le
    have h2 := mul_le_mul_of_nonneg_left herr (Real.exp_pos (2 * δ * a.1)).le
    unfold pairingError
    linarith
  · have hmass := integral_truncModel_even_sq_le hδ t x hn ha0
    have : 4 * a.1 * profileBound x ^ 2 * Real.exp (-(2 * δ * a.1)) ≤
        4 * a.1 * (2 * m * max 1 (1 / κ)) ^ 2 * Real.exp (-(2 * δ * a.1)) := by gcongr
    linarith

/-- The floor side: `μ₀(a) ≥ −(e^{2δa}/2)(Λ*(a) + ε)` once the floor errors are below `ε`. -/
theorem groundEnergy_ge_topRadius {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t)
    (a : SuzukiPositiveAperture) {ε : ℝ}
    (herr : 2 * (3 / (2 * δ) * Real.exp (-(δ * a.1)) * ∑ j, |h.mult j|) +
      2 * (h.lowWeight a.1 * Real.exp (-(2 * δ * a.1))) ≤ ε) :
    -(Real.exp (2 * δ * a.1) / 2 * (topRadius δ t h.mult a.1 + ε)) ≤
      ccmRestrictedWeilGroundEnergy a := by
  have hδ := h.pos
  have hmin := groundEnergy_ge_min_floor h a
  set X := Real.exp (2 * δ * a.1) with hX
  have hX0 : 0 < X := Real.exp_pos _
  have hXE2 : X * Real.exp (-(2 * δ * a.1)) = 1 := by rw [hX, ← Real.exp_add]; simp
  set l₁ := ccmLambdaMax δ t h.mult (aperturePhase t a.1)
  set l₂ := ccmLambdaMax δ t h.mult (halfTurn (aperturePhase t a.1))
  have hsum := lambdaMax_add_lambdaMax_halfTurn_nonneg hδ h.injective h.t_pos h.nonempty h.mult
    (aperturePhase t a.1)
  have hR : topRadius δ t h.mult a.1 = max l₁ l₂ := rfl
  have hmax0 : 0 ≤ max l₁ l₂ := by
    rcases le_total l₁ l₂ with hl | hl
    · rw [max_eq_right hl]; linarith
    · rw [max_eq_left hl]; linarith
  set C₁ := 3 / (2 * δ) * Real.exp (-(δ * a.1)) * ∑ j, |h.mult j| with hC₁
  set Lw := h.lowWeight a.1 with hLw
  have he : -(X * (max l₁ l₂ / 2 + C₁) + Lw) ≤ evenFloorConst h a.1 := by
    unfold evenFloorConst
    have : max l₂ 0 ≤ max l₁ l₂ := max_le (le_max_right _ _) hmax0
    have := mul_le_mul_of_nonneg_left (show max l₂ 0 / 2 + C₁ ≤ max l₁ l₂ / 2 + C₁ by linarith)
      hX0.le
    linarith
  have ho : -(X * (max l₁ l₂ / 2 + C₁) + Lw) ≤ oddFloorConst h a.1 := by
    unfold oddFloorConst
    have : max l₁ 0 ≤ max l₁ l₂ := max_le (le_max_left _ _) hmax0
    have := mul_le_mul_of_nonneg_left (show max l₁ 0 / 2 + C₁ ≤ max l₁ l₂ / 2 + C₁ by linarith)
      hX0.le
    linarith
  have hLwX : Lw = X * (Lw * Real.exp (-(2 * δ * a.1))) := by
    rw [← mul_assoc, mul_comm X, mul_assoc, hXE2, mul_one]
  have hkey : -(X / 2 * (topRadius δ t h.mult a.1 + ε)) ≤ -(X * (max l₁ l₂ / 2 + C₁) + Lw) := by
    have h1 := mul_le_mul_of_nonneg_left herr hX0.le
    have h2 : X * (Lw * Real.exp (-(2 * δ * a.1))) = Lw := hLwX.symm
    rw [hR]
    linarith
  exact hkey.trans ((le_min he ho).trans hmin)

/-- **The ground-energy law.** -/
theorem groundEnergy_law {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ A : ℝ, ∀ a : SuzukiPositiveAperture, A ≤ a.1 →
      -(Real.exp (2 * δ * a.1) / 2 * (topRadius δ t h.mult a.1 + ε)) ≤
          ccmRestrictedWeilGroundEnergy a ∧
        ccmRestrictedWeilGroundEnergy a ≤
          -(Real.exp (2 * δ * a.1) / 2 * (topRadius δ t h.mult a.1 - ε)) := by
  have hδ := h.pos
  obtain ⟨c₀, hc₀, hlow⟩ := exists_lambdaMax_lower hδ h.injective h.t_pos h.nonempty h.mult_pos
  set ε' := min ε c₀ with hε'
  have hε'0 : 0 < ε' := lt_min hε hc₀
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'c : ε' ≤ c₀ := min_le_right _ _
  obtain ⟨κ, hκ, hcoer⟩ := exists_normForm_coercive hδ h.injective h.t_pos
  obtain ⟨A₁, hA₁⟩ := eventually_atTop.mp ((tendsto_errorRate h (2 * m * max 1 (1 / κ))
    ((∑ j, |h.mult j|) * (1 / (2 * δ))) (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))
    ).eventually (gt_mem_nhds hε'0))
  obtain ⟨A₂, hA₂⟩ := eventually_atTop.mp ((tendsto_floorError h).eventually (gt_mem_nhds hε))
  refine ⟨max A₁ A₂, fun a ha => ⟨?_, ?_⟩⟩
  · exact groundEnergy_ge_topRadius h a (hA₂ a.1 ((le_max_right _ _).trans ha)).le
  · have hR := hA₁ a.1 ((le_max_left _ _).trans ha)
    have hX0 : 0 ≤ Real.exp (2 * δ * a.1) / 2 := by positivity
    have hodd := groundEnergy_lt_oddTest h a hκ hcoer hε'0.le hR (hε'c.trans (hlow _))
    have heven := groundEnergy_lt_evenTest h a hκ hcoer hε'0.le hR (hε'c.trans (hlow _))
    have e1 := mul_le_mul_of_nonneg_left (show ccmLambdaMax δ t h.mult (aperturePhase t a.1) - ε ≤
      ccmLambdaMax δ t h.mult (aperturePhase t a.1) - ε' by linarith) hX0
    have e2 := mul_le_mul_of_nonneg_left
      (show ccmLambdaMax δ t h.mult (halfTurn (aperturePhase t a.1)) - ε ≤
        ccmLambdaMax δ t h.mult (halfTurn (aperturePhase t a.1)) - ε' by linarith) hX0
    unfold topRadius
    rcases le_total (ccmLambdaMax δ t h.mult (aperturePhase t a.1))
      (ccmLambdaMax δ t h.mult (halfTurn (aperturePhase t a.1))) with hl | hl
    · rw [max_eq_right hl]; linarith
    · rw [max_eq_left hl]; linarith

/-- **The ground energy detects the top height.** Under a finite top layer there are constants
`0 < c ≤ C` with `c e^{2δa} ≤ −μ₀(a) ≤ C e^{2δa}` for all large apertures. -/
theorem exists_groundEnergy_exponential_bounds {δ : ℝ} {t : Fin m → ℝ}
    (h : FiniteTopLayer δ t) :
    ∃ c C A : ℝ, 0 < c ∧ ∀ a : SuzukiPositiveAperture, A ≤ a.1 →
      c * Real.exp (2 * δ * a.1) ≤ -ccmRestrictedWeilGroundEnergy a ∧
        -ccmRestrictedWeilGroundEnergy a ≤ C * Real.exp (2 * δ * a.1) := by
  have hδ := h.pos
  obtain ⟨c₀, hc₀, hlow⟩ := exists_lambdaMax_lower hδ h.injective h.t_pos h.nonempty h.mult_pos
  obtain ⟨A, hA⟩ := groundEnergy_law h (show 0 < c₀ / 2 by linarith)
  set B := (∑ j, |h.mult j|) * (1 / (2 * δ)) with hB
  refine ⟨c₀ / 4, (B + c₀ / 2) / 2, A, by linarith, fun a ha => ?_⟩
  obtain ⟨h1, h2⟩ := hA a ha
  have hX0 : 0 < Real.exp (2 * δ * a.1) := Real.exp_pos _
  have hR1 : c₀ ≤ topRadius δ t h.mult a.1 :=
    (hlow _).trans (le_max_left _ _)
  have hR2 : topRadius δ t h.mult a.1 ≤ B :=
    max_le (lambdaMax_le hδ h.injective h.t_pos h.nonempty h.mult _)
      (lambdaMax_le hδ h.injective h.t_pos h.nonempty h.mult _)
  constructor
  · have := mul_le_mul_of_nonneg_left (show c₀ / 2 ≤ topRadius δ t h.mult a.1 - c₀ / 2 by
      linarith) (show 0 ≤ Real.exp (2 * δ * a.1) / 2 by positivity)
    nlinarith
  · have := mul_le_mul_of_nonneg_left (show topRadius δ t h.mult a.1 + c₀ / 2 ≤ B + c₀ / 2 by
      linarith) (show 0 ≤ Real.exp (2 * δ * a.1) / 2 by positivity)
    nlinarith

end

end RHTower.CCMParityTopLayer
