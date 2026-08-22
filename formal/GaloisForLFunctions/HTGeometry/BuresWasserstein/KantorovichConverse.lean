import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinEquation

/-!
# The Kantorovich converse of the arithmetic–geometric mean inequality

Kim–Mer–Pálfia (arXiv:2607.29142), Lemma 6.16: for strictly positive `a, b` confined to Loewner
intervals `[m₁, M₁]` and `[m₂, M₂]`,

`a ∇ b ≤ κ (a # b)`,   `κ = max {K(M₁/m₂), K(M₂/m₁)}`,   `K(h) = (1+h)/(2√h)`.

The proof reduces by congruence to `2⁻¹(1 + X) ≤ κ √X` for `X = a^{-1/2} b a^{-1/2}` confined to
`[m₂/M₁, M₂/m₁]`, and this is the continuous functional calculus applied to the scalar inequality
`(1+x)/2 ≤ κ√x`, which holds on an interval as soon as it holds at both endpoints (the quadratic
`t² - 2κt + 1` is convex in `t = √x`).
-/

open scoped NNReal Ring

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The **Kantorovich constant** `K(h) = (1+h)/(2√h)`. -/
noncomputable def kantorovich (h : ℝ) : ℝ := (1 + h) / (2 * Real.sqrt h)

lemma kantorovich_inv {h : ℝ} (hh : 0 < h) : kantorovich h⁻¹ = kantorovich h := by
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have hsq : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh.le
  unfold kantorovich
  rw [Real.sqrt_inv, div_eq_div_iff (by positivity) (by positivity)]
  field_simp
  nlinarith [hsq]

/-- The scalar Kantorovich inequality on an interval: convexity of `t ↦ t² - 2κt + 1` in `t = √x`
propagates the endpoint inequalities. -/
lemma one_add_div_two_le_mul_sqrt {c d κ x : ℝ} (hc : 0 < c) (hx : c ≤ x) (hxd : x ≤ d)
    (hκc : (1 + c) / 2 ≤ κ * Real.sqrt c) (hκd : (1 + d) / 2 ≤ κ * Real.sqrt d) :
    (1 + x) / 2 ≤ κ * Real.sqrt x := by
  have hx0 : 0 < x := lt_of_lt_of_le hc hx
  have hd0 : 0 < d := lt_of_lt_of_le hx0 hxd
  have hu : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hv : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hd0.le
  have hus : Real.sqrt c ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
  have hsv : Real.sqrt x ≤ Real.sqrt d := Real.sqrt_le_sqrt hxd
  have hpu : Real.sqrt c * Real.sqrt c - 2 * κ * Real.sqrt c + 1 ≤ 0 := by
    rw [hu]; linarith
  have hpv : Real.sqrt d * Real.sqrt d - 2 * κ * Real.sqrt d + 1 ≤ 0 := by
    rw [hv]; linarith
  have hkey : Real.sqrt x * Real.sqrt x - 2 * κ * Real.sqrt x + 1 ≤ 0 := by
    rcases eq_or_lt_of_le (le_trans hus hsv) with heq | hlt
    · have hxc : Real.sqrt x = Real.sqrt c := le_antisymm (heq ▸ hsv) hus
      rw [hxc]; exact hpu
    · have hpos : 0 < Real.sqrt d - Real.sqrt c := sub_pos.mpr hlt
      have hid : (Real.sqrt d - Real.sqrt c)
            * (Real.sqrt x * Real.sqrt x - 2 * κ * Real.sqrt x + 1)
          = (Real.sqrt d - Real.sqrt x) * (Real.sqrt c * Real.sqrt c - 2 * κ * Real.sqrt c + 1)
            + (Real.sqrt x - Real.sqrt c) * (Real.sqrt d * Real.sqrt d - 2 * κ * Real.sqrt d + 1)
            - (Real.sqrt d - Real.sqrt x) * (Real.sqrt x - Real.sqrt c)
              * (Real.sqrt d - Real.sqrt c) := by ring
      have hle : (Real.sqrt d - Real.sqrt c)
          * (Real.sqrt x * Real.sqrt x - 2 * κ * Real.sqrt x + 1) ≤ 0 := by
        rw [hid]
        have h1 : (Real.sqrt d - Real.sqrt x)
            * (Real.sqrt c * Real.sqrt c - 2 * κ * Real.sqrt c + 1) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hsv) hpu
        have h2 : (Real.sqrt x - Real.sqrt c)
            * (Real.sqrt d * Real.sqrt d - 2 * κ * Real.sqrt d + 1) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hus) hpv
        have h3 : 0 ≤ (Real.sqrt d - Real.sqrt x) * (Real.sqrt x - Real.sqrt c)
            * (Real.sqrt d - Real.sqrt c) :=
          mul_nonneg (mul_nonneg (sub_nonneg.mpr hsv) (sub_nonneg.mpr hus)) hpos.le
        linarith
      nlinarith [hle, hpos]
  rw [hs] at hkey
  linarith

/-- The operator form: `2⁻¹ (1 + X) ≤ κ √X` on a Loewner interval `[c, d]` with `c > 0`. -/
theorem smul_one_add_le_smul_cfcSqrt {X : A} (hX : IsStrictlyPositive X) {c d κ : ℝ}
    (hc : 0 < c) (hXc : c • (1 : A) ≤ X) (hXd : X ≤ d • (1 : A))
    (hκc : (1 + c) / 2 ≤ κ * Real.sqrt c) (hκd : (1 + d) / 2 ≤ κ * Real.sqrt d) :
    (2 : ℝ)⁻¹ • ((1 : A) + X) ≤ κ • CFC.sqrt X := by
  have hXsa : IsSelfAdjoint X := hX.isSelfAdjoint
  have hspecc : ∀ x ∈ spectrum ℝ X, c ≤ x := by
    rw [← algebraMap_le_iff_le_spectrum (a := X) hXsa, Algebra.algebraMap_eq_smul_one]
    exact hXc
  have hspecd : ∀ x ∈ spectrum ℝ X, x ≤ d := by
    rw [← le_algebraMap_iff_spectrum_le (a := X) hXsa, Algebra.algebraMap_eq_smul_one]
    exact hXd
  have hfg : ∀ x ∈ spectrum ℝ X, (1 + x) / 2 ≤ κ * Real.sqrt x := fun x hx =>
    one_add_div_two_le_mul_sqrt hc (hspecc x hx) (hspecd x hx) hκc hκd
  have hcont1 : ContinuousOn (fun x : ℝ => (1 + x) / 2) (spectrum ℝ X) := by fun_prop
  have hcont2 : ContinuousOn (fun x : ℝ => κ * Real.sqrt x) (spectrum ℝ X) := by fun_prop
  have hmono := cfc_mono (R := ℝ) (a := X) hfg hcont1 hcont2
  have hL : cfc (fun x : ℝ => (1 + x) / 2) X = (2 : ℝ)⁻¹ • ((1 : A) + X) := by
    rw [show (fun x : ℝ => (1 + x) / 2) = (fun x : ℝ => (2 : ℝ)⁻¹ * (1 + x)) by
      funext x; ring]
    rw [cfc_const_mul _ _ X, cfc_const_add _ _ X, cfc_id' ℝ X, map_one]
  have hR : cfc (fun x : ℝ => κ * Real.sqrt x) X = κ • CFC.sqrt X := by
    rw [cfc_const_mul _ _ X, CFC.sqrt_eq_real_sqrt X hX.nonneg, cfcₙ_eq_cfc]
  rwa [hL, hR] at hmono

/-! ### Loewner bounds transported to the inverse -/

lemma ringInverse_le_of_smul_one_le {a : A} {m : ℝ} (hm : 0 < m)
    (h : m • (1 : A) ≤ a) : a⁻¹ʳ ≤ m⁻¹ • (1 : A) := by
  have hpos : IsStrictlyPositive (m • (1 : A)) :=
    IsStrictlyPositive.smul hm isStrictlyPositive_one
  have hcmp := CStarAlgebra.ringInverse_le_ringInverse h hpos
  rwa [ringInverse_smul hm (isStrictlyPositive_one (A := A)), Ring.inverse_one] at hcmp

lemma smul_one_le_ringInverse_of_le_smul_one {a : A} (ha : IsStrictlyPositive a) {M : ℝ}
    (hM : 0 < M) (h : a ≤ M • (1 : A)) : M⁻¹ • (1 : A) ≤ a⁻¹ʳ := by
  have hcmp := CStarAlgebra.ringInverse_le_ringInverse h ha
  rwa [ringInverse_smul hM (isStrictlyPositive_one (A := A)), Ring.inverse_one] at hcmp

/-! ### Lemma 6.16 -/

/-- **Kantorovich converse of the arithmetic–geometric mean inequality.** -/
theorem arith_le_smul_gm {a b : A} (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b)
    {m₁ M₁ m₂ M₂ : ℝ} (hm₁ : 0 < m₁) (hM₁ : 0 < M₁) (hm₂ : 0 < m₂) (hM₂ : 0 < M₂)
    (ha₁ : m₁ • (1 : A) ≤ a) (ha₂ : a ≤ M₁ • (1 : A))
    (hb₁ : m₂ • (1 : A) ≤ b) (hb₂ : b ≤ M₂ • (1 : A)) :
    (2 : ℝ)⁻¹ • (a + b)
      ≤ (max (kantorovich (M₁ / m₂)) (kantorovich (M₂ / m₁))) • gm a b := by
  set κ := max (kantorovich (M₁ / m₂)) (kantorovich (M₂ / m₁)) with hκ
  have hPsa : IsSelfAdjoint (a ^ (-(1/2) : ℝ)) := isSelfAdjoint_rpow a _
  have hXpos : IsStrictlyPositive (a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ)) :=
    conj_strictlyPositive ha hb
  have hcpos : 0 < m₂ / M₁ := div_pos hm₂ hM₁
  have hdpos : 0 < M₂ / m₁ := div_pos hM₂ hm₁
  have hainv : a ^ (-(1/2) : ℝ) * a ^ (-(1/2) : ℝ) = a⁻¹ʳ := rpow_neg_half_mul_rpow_neg_half ha
  -- the Loewner interval for `X = a^{-1/2} b a^{-1/2}`
  have hXc : (m₂ / M₁) • (1 : A) ≤ a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ) := by
    have h1 : m₂ • a⁻¹ʳ ≤ a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ) := by
      have := hPsa.conjugate_le_conjugate hb₁
      rwa [mul_smul_comm, smul_mul_assoc, mul_one, hainv] at this
    calc (m₂ / M₁) • (1 : A) = m₂ • (M₁⁻¹ • (1 : A)) := by rw [smul_smul, ← div_eq_mul_inv]
      _ ≤ m₂ • a⁻¹ʳ := smul_le_smul_of_nonneg_left
          (smul_one_le_ringInverse_of_le_smul_one ha hM₁ ha₂) hm₂.le
      _ ≤ a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ) := h1
  have hXd : a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ) ≤ (M₂ / m₁) • (1 : A) := by
    have h1 : a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ) ≤ M₂ • a⁻¹ʳ := by
      have := hPsa.conjugate_le_conjugate hb₂
      rwa [mul_smul_comm, smul_mul_assoc, mul_one, hainv] at this
    calc a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ) ≤ M₂ • a⁻¹ʳ := h1
      _ ≤ M₂ • (m₁⁻¹ • (1 : A)) := smul_le_smul_of_nonneg_left
          (ringInverse_le_of_smul_one_le hm₁ ha₁) hM₂.le
      _ = (M₂ / m₁) • (1 : A) := by rw [smul_smul, ← div_eq_mul_inv]
  -- the Kantorovich constant dominates both endpoints
  have hκc : (1 + m₂ / M₁) / 2 ≤ κ * Real.sqrt (m₂ / M₁) := by
    have hle : kantorovich (m₂ / M₁) ≤ κ := by
      rw [show m₂ / M₁ = (M₁ / m₂)⁻¹ by rw [inv_div], kantorovich_inv (div_pos hM₁ hm₂)]
      exact le_max_left _ _
    unfold kantorovich at hle
    rw [div_le_iff₀ (by positivity)] at hle
    linarith
  have hκd : (1 + M₂ / m₁) / 2 ≤ κ * Real.sqrt (M₂ / m₁) := by
    have hle : kantorovich (M₂ / m₁) ≤ κ := le_max_right _ _
    unfold kantorovich at hle
    rw [div_le_iff₀ (by positivity)] at hle
    linarith
  have hcore := smul_one_add_le_smul_cfcSqrt hXpos hcpos hXc hXd hκc hκd
  have hconj := (isSelfAdjoint_rpow a (1/2 : ℝ)).conjugate_le_conjugate hcore
  have hL : a ^ (1/2 : ℝ) * ((2 : ℝ)⁻¹ • ((1 : A)
      + a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ))) * a ^ (1/2 : ℝ) = (2 : ℝ)⁻¹ • (a + b) := by
    rw [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one,
      rpow_half_mul_rpow_half ha, sandwich_peel ha]
  have hR : a ^ (1/2 : ℝ) * (κ • CFC.sqrt (a ^ (-(1/2) : ℝ) * b * a ^ (-(1/2) : ℝ)))
      * a ^ (1/2 : ℝ) = κ • gm a b := by
    rw [mul_smul_comm, smul_mul_assoc, gm_eq_sqrt]
  rwa [hL, hR] at hconj

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
