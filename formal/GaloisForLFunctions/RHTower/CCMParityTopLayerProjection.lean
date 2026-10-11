import GaloisForLFunctions.RHTower.CCMParityLeadingOrderSign

/-!
# The leading-order parity form on all square-integrable half-line functions

Let `ψ_j(s) = e^{−(δ − it_j)s}` on `(0, ∞)` and, for a real function `v`,

`T(θ)[v] = Re Σ_j M_j e^{iθ_j} ⟨v, ψ_j⟩²`, `⟨v, ψ_j⟩ = ∫_0^∞ v ψ_j`  (`halfLineForm`).

On the real span of the `ψ_j, ψ̄_j` this is the form `quadForm` of the Cauchy model
(`quadForm_eq_halfLineForm`).

**Theorem** (`halfLineForm_ge`). For every real `v ∈ L²(0, ∞)`,

`T(θ)[v] ≥ −max(λ_max(T(θ + π𝟙)), 0) · ∫_0^∞ v²`.

**Proof.** The moments `b_l = ∫ v e^{−p_l s}` (`p = (δ − it_j, δ + it_j)`) form a real-structured
vector, and the Cauchy matrix `G` is invertible and commutes with the swap up to conjugation. So
`G y = b` has a real-structured solution `y = realLift x`. The profile `P` with coefficients `x` has
the same pairings with every `ψ_j` as `v`. Since `∫ P² = ∫ v P` (`G` is the Gram matrix), the
pointwise inequality `2vP ≤ v² + P²` gives `∫ P² ≤ ∫ v²` (`exists_realProfile_projection`). Finally
`T(θ)[v] = T(θ)[P] = −quadForm(θ + π𝟙) ≥ −λ_max(θ + π𝟙) ∫ P²`.

Also: a positive parity balance forces `λ_max(θ) > max(λ_max(θ + π𝟙), 0)`
(`max_lambdaMax_halfTurn_lt_of_balance_pos`).
-/

open Matrix Complex Filter Topology MeasureTheory Set

namespace RHTower.CCMParityCauchy

noncomputable section

variable {m : ℕ}

/-- `⟨v, ψ_j⟩ = ∫_0^∞ v(s) e^{−(δ − it_j)s} ds`. -/
def halfLinePairing (δ : ℝ) (t : Fin m → ℝ) (v : ℝ → ℝ) (j : Fin m) : ℂ :=
  ∫ s in Ioi (0 : ℝ), (v s : ℂ) * Complex.exp (-((δ : ℂ) - I * t j) * s)

/-- `T(θ)[v] = Re Σ_j M_j e^{iθ_j} ⟨v, ψ_j⟩²`. -/
def halfLineForm (δ : ℝ) (t M θ : Fin m → ℝ) (v : ℝ → ℝ) : ℝ :=
  (∑ j, (M j : ℂ) * Complex.exp ((θ j : ℂ) * I) * halfLinePairing δ t v j ^ 2).re

/-- The moments `∫_0^∞ v(s) e^{−p_l s} ds` at the Cauchy nodes. -/
def nodeMoment (δ : ℝ) (t : Fin m → ℝ) (v : ℝ → ℝ) (l : Fin m ⊕ Fin m) : ℂ :=
  ∫ s in Ioi (0 : ℝ), (v s : ℂ) * Complex.exp (-ccmNodes δ t l * s)

theorem nodeMoment_inl (δ : ℝ) (t : Fin m → ℝ) (v : ℝ → ℝ) (j : Fin m) :
    nodeMoment δ t v (Sum.inl j) = halfLinePairing δ t v j := rfl

theorem nodeMoment_inr (δ : ℝ) (t : Fin m → ℝ) (v : ℝ → ℝ) (j : Fin m) :
    nodeMoment δ t v (Sum.inr j) = (starRingEnd ℂ) (halfLinePairing δ t v j) := by
  unfold nodeMoment halfLinePairing
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only [ccmNodes, Sum.elim_inr, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg,
    map_sub, Complex.conj_I]
  ring_nf

theorem isRealVec_nodeMoment (δ : ℝ) (t : Fin m → ℝ) (v : ℝ → ℝ) :
    IsRealVec (nodeMoment δ t v) := by
  intro i
  rcases i with j | j
  · simp only [Sum.swap_inl, nodeMoment_inr, nodeMoment_inl]
  · simp only [Sum.swap_inr, nodeMoment_inr, nodeMoment_inl, Complex.conj_conj]

/-- The moments of a profile are the Cauchy matrix applied to its coefficients. -/
theorem cauchyGram_mulVec_realLift {δ : ℝ} (hδ : 0 < δ) (t : Fin m → ℝ) (x : Fin m → ℂ) :
    cauchyGram (ccmNodes δ t) *ᵥ realLift x = nodeMoment δ t (realProfile δ t x) := by
  funext l
  rw [cauchyGram_mulVec_eq_integral (ccmNodes_re_add_pos hδ t)]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [nodeProfile_realLift, mul_comm]

/-- **On the real span the model form is the half-line form.** -/
theorem quadForm_eq_halfLineForm {δ : ℝ} (hδ : 0 < δ) (t M θ : Fin m → ℝ) (x : Fin m → ℂ) :
    quadForm δ t M θ x = halfLineForm δ t M θ (realProfile δ t x) := by
  unfold quadForm halfLineForm
  rw [cauchyGram_mulVec_realLift hδ, Fintype.sum_sum_type]
  simp only [nodeMoment_inl, nodeMoment_inr, phaseWeight, Sum.elim_inl, Sum.elim_inr]
  rw [← Finset.sum_add_distrib, Complex.re_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  set h := halfLinePairing δ t (realProfile δ t x) j
  have hc : ((M j / 2 : ℝ) : ℂ) * Complex.exp (-((θ j : ℂ) * I)) * (starRingEnd ℂ) h ^ 2 =
      (starRingEnd ℂ) (((M j / 2 : ℝ) : ℂ) * Complex.exp ((θ j : ℂ) * I) * h ^ 2) := by
    rw [map_mul, map_mul, map_pow, ← Complex.exp_conj, Complex.conj_ofReal]
    simp [Complex.conj_ofReal, Complex.conj_I]
  rw [hc, Complex.add_re, Complex.conj_re]
  rw [show ((M j / 2 : ℝ) : ℂ) * Complex.exp ((θ j : ℂ) * I) * h ^ 2 =
    ((1 / 2 : ℝ) : ℂ) * ((M j : ℂ) * Complex.exp ((θ j : ℂ) * I) * h ^ 2) by push_cast; ring,
    Complex.re_ofReal_mul]
  ring

/-- The half-line form depends on `v` only through its pairings. -/
theorem halfLineForm_congr {δ : ℝ} {t : Fin m → ℝ} (M θ : Fin m → ℝ) {v w : ℝ → ℝ}
    (h : ∀ j, halfLinePairing δ t v j = halfLinePairing δ t w j) :
    halfLineForm δ t M θ v = halfLineForm δ t M θ w := by
  unfold halfLineForm
  simp only [h]

/-! ## Projection onto the real span -/

theorem memLp_exp_neg_Ioi {p : ℂ} (hp : 0 < p.re) :
    MemLp (fun s : ℝ => Complex.exp (-p * s)) 2 (volume.restrict (Ioi 0)) := by
  have hmeas : AEStronglyMeasurable (fun s : ℝ => Complex.exp (-p * s))
      (volume.restrict (Ioi 0)) := (by fun_prop : Continuous fun s : ℝ =>
        Complex.exp (-p * s)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have := exp_neg_integrableOn_Ioi 0 (show 0 < 2 * p.re by linarith)
  refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioi
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp [Complex.mul_re]
  ring

theorem integrableOn_mul_exp_neg {v : ℝ → ℝ} (hv : MemLp v 2 (volume.restrict (Ioi 0)))
    {p : ℂ} (hp : 0 < p.re) :
    IntegrableOn (fun s : ℝ => (v s : ℂ) * Complex.exp (-p * s)) (Ioi 0) :=
  (hv.ofReal (K := ℂ)).integrable_mul (memLp_exp_neg_Ioi hp)

theorem memLp_realProfile {δ : ℝ} (hδ : 0 < δ) (t : Fin m → ℝ) (x : Fin m → ℂ) :
    MemLp (realProfile δ t x) 2 (volume.restrict (Ioi 0)) := by
  rw [memLp_two_iff_integrable_sq_norm (continuous_realProfile δ t x).aestronglyMeasurable]
  refine (integrableOn_realProfile_sq hδ t x).congr_fun (fun s _ => ?_) measurableSet_Ioi
  rw [Real.norm_eq_abs, sq_abs]

theorem ccmNodes_re_pos {δ : ℝ} (hδ : 0 < δ) (t : Fin m → ℝ) (l : Fin m ⊕ Fin m) :
    0 < (ccmNodes δ t l).re := by
  rcases l with j | j <;> simp [ccmNodes, hδ]

theorem det_cauchyGram_ccmNodes_ne_zero {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) : (cauchyGram (ccmNodes δ t)).det ≠ 0 := by
  have := det_cauchyGram_submatrix_ne_zero (ccmNodes_injective ht htpos)
    (fun i l h => by
      have := ccmNodes_re_add_pos hδ t i l
      rw [h, Complex.zero_re] at this
      exact lt_irrefl _ this) (e := id) Function.injective_id
  simpa using this

/-- A real-structured right-hand side has a real-structured Cauchy preimage. -/
theorem exists_realLift_cauchyGram_mulVec_eq {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) {b : Fin m ⊕ Fin m → ℂ}
    (hb : IsRealVec b) : ∃ x : Fin m → ℂ, cauchyGram (ccmNodes δ t) *ᵥ realLift x = b := by
  set G := cauchyGram (ccmNodes δ t) with hG
  have hdet : G.det ≠ 0 := det_cauchyGram_ccmNodes_ne_zero hδ ht htpos
  set y := G⁻¹ *ᵥ b with hy
  have hGy : G *ᵥ y = b := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hdet), Matrix.one_mulVec]
  set y' : Fin m ⊕ Fin m → ℂ := fun i => (starRingEnd ℂ) (y (Sum.swap i)) with hy'
  have hGy' : G *ᵥ y' = b := by
    funext i
    have h1 : (G *ᵥ y') i = (starRingEnd ℂ) ((G *ᵥ y) (Sum.swap i)) := by
      simp only [mulVec, dotProduct, hy', map_sum, map_mul]
      rw [← (Equiv.sumComm (Fin m) (Fin m)).sum_comp]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [Equiv.sumComm_apply, Sum.swap_swap]
      have hsw := cauchyGram_ccmNodes_swap δ t (Sum.swap i) l
      rw [Sum.swap_swap] at hsw
      rw [hG, hsw]
    rw [h1, hGy, hb i, Complex.conj_conj]
  have hyy : y' = y := by
    have h0 : G *ᵥ (y' - y) = 0 := by rw [Matrix.mulVec_sub, hGy, hGy', sub_self]
    by_contra hne
    exact hdet ((Matrix.exists_mulVec_eq_zero_iff).mp ⟨_, sub_ne_zero.mpr hne, h0⟩)
  refine ⟨fun j => y (Sum.inl j), ?_⟩
  have hlift : realLift (fun j => y (Sum.inl j)) = y := by
    funext i
    rcases i with j | j
    · rfl
    · have := congr_fun hyy (Sum.inl j)
      simp only [hy', Sum.swap_inl] at this
      simp only [realLift, Sum.elim_inr]
      rw [← this, Complex.conj_conj]
  rw [hlift, hGy]

/-- **Projection onto the real span.** Every real `v ∈ L²(0, ∞)` has a profile `P` with the same
pairings against every `ψ_j` and `∫ P² ≤ ∫ v²`. -/
theorem exists_realProfile_projection {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) {v : ℝ → ℝ}
    (hv : MemLp v 2 (volume.restrict (Ioi 0))) :
    ∃ x : Fin m → ℂ, (∀ j, halfLinePairing δ t (realProfile δ t x) j = halfLinePairing δ t v j) ∧
      normForm δ t x ≤ ∫ s in Ioi (0 : ℝ), v s ^ 2 := by
  obtain ⟨x, hx⟩ := exists_realLift_cauchyGram_mulVec_eq hδ ht htpos (isRealVec_nodeMoment δ t v)
  have hmom : nodeMoment δ t (realProfile δ t x) = nodeMoment δ t v := by
    rw [← cauchyGram_mulVec_realLift hδ, hx]
  refine ⟨x, fun j => congr_fun hmom (Sum.inl j), ?_⟩
  set P := realProfile δ t x with hP
  -- `normForm x = ∫ v P`
  have hvP : normForm δ t x = ∫ s in Ioi (0 : ℝ), v s * P s := by
    unfold normForm
    rw [hx]
    simp only [dotProduct, nodeMoment]
    have hint : ∀ l, IntegrableOn (fun s : ℝ => realLift x l *
        ((v s : ℂ) * Complex.exp (-ccmNodes δ t l * s))) (Ioi 0) :=
      fun l => (integrableOn_mul_exp_neg hv (ccmNodes_re_pos hδ t l)).const_mul _
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ fun l _ => hint l]
    have hfun : ∀ s : ℝ, ∑ l, realLift x l * ((v s : ℂ) * Complex.exp (-ccmNodes δ t l * s)) =
        ((v s * P s : ℝ) : ℂ) := by
      intro s
      have := nodeProfile_realLift δ t x s
      unfold nodeProfile at this
      rw [Complex.ofReal_mul, ← this, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    simp_rw [hfun]
    rw [integral_complex_ofReal, Complex.ofReal_re]
  have hPP : normForm δ t x = ∫ s in Ioi (0 : ℝ), P s ^ 2 := normForm_eq_integral hδ t x
  have hPm := memLp_realProfile hδ t x
  have hint_vP : IntegrableOn (fun s => v s * P s) (Ioi 0) := hv.integrable_mul hPm
  have hint_v2 : IntegrableOn (fun s => v s ^ 2) (Ioi 0) := hv.integrable_sq
  have hint_P2 : IntegrableOn (fun s => P s ^ 2) (Ioi 0) := hPm.integrable_sq
  have hle : ∫ s in Ioi (0 : ℝ), 2 * (v s * P s) ≤ ∫ s in Ioi (0 : ℝ), (v s ^ 2 + P s ^ 2) :=
    integral_mono (hint_vP.const_mul 2) (hint_v2.add hint_P2) fun s => by
      nlinarith [sq_nonneg (v s - P s)]
  rw [integral_const_mul, integral_add hint_v2 hint_P2, ← hvP, ← hPP] at hle
  linarith

/-! ## Spectral bounds on all of `L²(0, ∞)` -/

theorem lambdaMax_halfTurn_mul_ge {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M θ : Fin m → ℝ)
    (x : Fin m → ℂ) :
    -(ccmLambdaMax δ t M (halfTurn θ) * normForm δ t x) ≤ quadForm δ t M θ x := by
  have h := quadForm_le_lambdaMax_mul hδ ht htpos hm M (halfTurn θ) x
  rw [quadForm_halfTurn] at h
  linarith

/-- **The even-sector floor of the model:** `T(θ)[v] ≥ −max(λ_max(θ + π𝟙), 0) ∫_0^∞ v²`. -/
theorem halfLineForm_ge {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M θ : Fin m → ℝ) {v : ℝ → ℝ}
    (hv : MemLp v 2 (volume.restrict (Ioi 0))) :
    -(max (ccmLambdaMax δ t M (halfTurn θ)) 0 * ∫ s in Ioi (0 : ℝ), v s ^ 2) ≤
      halfLineForm δ t M θ v := by
  obtain ⟨x, hpair, hnorm⟩ := exists_realProfile_projection hδ ht htpos hv
  rw [← halfLineForm_congr M θ hpair, ← quadForm_eq_halfLineForm hδ]
  have h1 := lambdaMax_halfTurn_mul_ge hδ ht htpos hm M θ x
  have hn0 := normForm_nonneg hδ t x
  have h2 : ccmLambdaMax δ t M (halfTurn θ) * normForm δ t x ≤
      max (ccmLambdaMax δ t M (halfTurn θ)) 0 * ∫ s in Ioi (0 : ℝ), v s ^ 2 :=
    calc ccmLambdaMax δ t M (halfTurn θ) * normForm δ t x
        ≤ max (ccmLambdaMax δ t M (halfTurn θ)) 0 * normForm δ t x :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hn0
      _ ≤ max (ccmLambdaMax δ t M (halfTurn θ)) 0 * ∫ s in Ioi (0 : ℝ), v s ^ 2 :=
          mul_le_mul_of_nonneg_left hnorm (le_max_right _ _)
  linarith

/-- **A positive balance separates the top from the reflected top and from zero.** -/
theorem max_lambdaMax_halfTurn_lt_of_balance_pos {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M θ : Fin m → ℝ)
    (hF : 0 < ccmParityBalance δ t M θ) :
    max (ccmLambdaMax δ t M (halfTurn θ)) 0 < ccmLambdaMax δ t M θ := by
  unfold ccmParityBalance at hF
  refine max_lt (by linarith) ?_
  by_cases h0 : 0 ≤ ccmLambdaMax δ t M (halfTurn θ)
  · linarith
  · push Not at h0
    obtain ⟨x, hx, -, -⟩ := exists_isMaxOn_quadForm hδ ht htpos hm M θ
    have h1 := lambdaMax_halfTurn_mul_ge hδ ht htpos hm M θ x
    have hn : normForm δ t x = 1 := hx
    rw [hn, mul_one] at h1
    obtain ⟨-, -, -, hle⟩ := exists_isMaxOn_quadForm hδ ht htpos hm M θ
    have := hle x hx
    linarith

end

end RHTower.CCMParityCauchy
