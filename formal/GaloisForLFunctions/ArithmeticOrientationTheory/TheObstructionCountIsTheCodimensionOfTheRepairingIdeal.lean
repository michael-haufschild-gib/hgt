import GaloisForLFunctions.ArithmeticOrientationTheory.TheZerosOfZetaAreWhereTheObstructionVanishes

/-!
# The obstruction count is the codimension of the repairing ideal

The obstruction hull of a weight is a set of points of the Bohr spectrum; the repairing ideal
`P(c)` is a subspace of the Wiener algebra.  On the computed families the two are tied by a count:

    dim_ℂ (𝒲_{1/2} / P(c)) = #(obstruction points).

* **One point** (`finrank_quotient_paidIdeal_smoothPower`): for `0 < ε < ½` the repairing ideal
  of `d^{−ε}` is the kernel of the Bohr character at the pole, a surjection onto `ℂ`, so the
  quotient has dimension `1`.
* **Two points** (`finrank_quotient_paidIdeal_oscillating`): for the probe `d^{−ε} cos(t log d)`,
  `t ≠ 0`, off the zeros of `ζ`, the repairing ideal is the kernel of the pair of characters at
  `ρ` and `ρ̄`; they differ at the prime `2` or `3` (`exists_prime_ne_osc`, since `3^a ≠ 2^b`), so
  the pair is onto `ℂ²` and the quotient has dimension `2`.
* **No point at a zero** (`finrank_quotient_paidIdeal_oscillating_of_zeta_eq_zero`): at
  `ζ(ρ) = 0` the ideal is everything and the quotient is `0`.

The receiver reads its obstruction as a dimension: each point of the hull is one linear condition
on the repairing kernels, and the conditions are independent.
-/

open Finset ArithmeticFunction LSeries Complex

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open TransHorizonIncidenceMechanics WienerAlgebraAt

noncomputable section
set_option autoImplicit false

/-! ### Characters onto `ℂ` and `ℂ²` -/

theorem bohrCharacter_smul_one (ω : BohrPoint) (c : ℂ) :
    WienerAlgebraAt.bohrCharacter (1 / 2) ω (c • (1 : WienerAlgebraAt (1 / 2))) = c := by
  rw [map_smul, map_one, smul_eq_mul, mul_one]

theorem bohrCharacter_surjective (ω : BohrPoint) :
    Function.Surjective (WienerAlgebraAt.bohrCharacter (1 / 2) ω) :=
  fun c => ⟨c • 1, bohrCharacter_smul_one ω c⟩

/-- The kernel of a Bohr character has codimension one. -/
theorem finrank_quotient_ker_bohrCharacter (ω : BohrPoint) :
    Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸ RingHom.ker (WienerAlgebraAt.bohrCharacter (1 / 2) ω)) = 1 := by
  rw [(Ideal.quotientKerAlgEquivOfSurjective (bohrCharacter_surjective ω)).toLinearEquiv.finrank_eq,
    Module.finrank_self]

/-- The value of a Bohr character at a point mass. -/
theorem bohrCharacter_pointMass (ω : BohrPoint) {p : ℕ} (hp : p ≠ 0) :
    WienerAlgebraAt.bohrCharacter (1 / 2) ω (pointMass p) = ω.ω p / (p : ℂ) ^ ((1 / 2 : ℝ) : ℂ) := by
  rw [bohrCharacter_apply, toFn_pointMass, bohrEval_pointMass hp]

/-- The pair of characters at two Bohr points. -/
def bohrPair (ω₁ ω₂ : BohrPoint) : WienerAlgebraAt (1 / 2) →ₐ[ℂ] ℂ × ℂ :=
  (WienerAlgebraAt.bohrCharacter (1 / 2) ω₁).prod (WienerAlgebraAt.bohrCharacter (1 / 2) ω₂)

/-- Two Bohr points that differ at a prime give a pair of characters onto `ℂ²`. -/
theorem bohrPair_surjective {ω₁ ω₂ : BohrPoint} {p : ℕ} (hp : p.Prime) (hne : ω₁.ω p ≠ ω₂.ω p) :
    Function.Surjective (bohrPair ω₁ ω₂) := by
  set z₁ := ω₁.ω p / (p : ℂ) ^ ((1 / 2 : ℝ) : ℂ)
  set z₂ := ω₂.ω p / (p : ℂ) ^ ((1 / 2 : ℝ) : ℂ)
  have hp0 : (p : ℂ) ^ ((1 / 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hp.ne_zero (by exact_mod_cast h.1)
  have hz : z₁ - z₂ ≠ 0 := by
    rw [sub_ne_zero]; intro h; exact hne ((div_left_inj' hp0).1 h)
  rintro ⟨a, b⟩
  set e₁ : WienerAlgebraAt (1 / 2) := (z₁ - z₂)⁻¹ • (pointMass p - z₂ • 1)
  set e₂ : WienerAlgebraAt (1 / 2) := (z₂ - z₁)⁻¹ • (pointMass p - z₁ • 1)
  have hz' : z₂ - z₁ ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.2 hz
  have hv : ∀ (ω : BohrPoint) (c z : ℂ), WienerAlgebraAt.bohrCharacter (1 / 2) ω
      (c • (pointMass p - z • 1)) = c * (ω.ω p / (p : ℂ) ^ ((1 / 2 : ℝ) : ℂ) - z) := fun ω c z => by
    rw [map_smul, map_sub, map_smul, map_one, bohrCharacter_pointMass _ hp.ne_zero, smul_eq_mul,
      smul_eq_mul, mul_one]
  set φ₁ := WienerAlgebraAt.bohrCharacter (1 / 2) ω₁
  set φ₂ := WienerAlgebraAt.bohrCharacter (1 / 2) ω₂
  have h11 : φ₁ e₁ = 1 := by
    show φ₁ ((z₁ - z₂)⁻¹ • (pointMass p - z₂ • 1)) = 1
    rw [hv]; exact inv_mul_cancel₀ hz
  have h21 : φ₂ e₁ = 0 := by
    show φ₂ ((z₁ - z₂)⁻¹ • (pointMass p - z₂ • 1)) = 0
    rw [hv]; exact mul_eq_zero_of_right _ (sub_self z₂)
  have h12 : φ₁ e₂ = 0 := by
    show φ₁ ((z₂ - z₁)⁻¹ • (pointMass p - z₁ • 1)) = 0
    rw [hv]; exact mul_eq_zero_of_right _ (sub_self z₁)
  have h22 : φ₂ e₂ = 1 := by
    show φ₂ ((z₂ - z₁)⁻¹ • (pointMass p - z₁ • 1)) = 1
    rw [hv]; exact inv_mul_cancel₀ hz'
  refine ⟨a • e₁ + b • e₂, Prod.ext ?_ ?_⟩
  · show φ₁ (a • e₁ + b • e₂) = a
    rw [map_add, map_smul φ₁ a e₁, map_smul φ₁ b e₂, h11, h12, smul_eq_mul, smul_eq_mul]; ring
  · show φ₂ (a • e₁ + b • e₂) = b
    rw [map_add, map_smul φ₂ a e₁, map_smul φ₂ b e₂, h21, h22, smul_eq_mul, smul_eq_mul]; ring

/-- The common kernel of two characters differing at a prime has codimension two. -/
theorem finrank_quotient_ker_bohrPair {ω₁ ω₂ : BohrPoint} {p : ℕ} (hp : p.Prime)
    (hne : ω₁.ω p ≠ ω₂.ω p) :
    Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸ RingHom.ker (bohrPair ω₁ ω₂)) = 2 := by
  rw [(Ideal.quotientKerAlgEquivOfSurjective (bohrPair_surjective hp hne)).toLinearEquiv.finrank_eq,
    Module.finrank_prod, Module.finrank_self]

/-! ### The smooth power: one condition -/

theorem paidIdeal_smoothPower_eq_ker {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    paidIdeal (dampedSignWeight unitSign ε) (summable_abs_smoothPower_div hε) =
      RingHom.ker (WienerAlgebraAt.bohrCharacter (1 / 2) (polePoint ε hε2.le)) := by
  ext k
  rw [mem_paidIdeal_smoothPower_iff hε hε2, RingHom.mem_ker, bohrCharacter_apply]

/-- **The smooth power imposes one condition.** -/
theorem finrank_quotient_paidIdeal_smoothPower {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
      paidIdeal (dampedSignWeight unitSign ε) (summable_abs_smoothPower_div hε)) = 1 := by
  rw [paidIdeal_smoothPower_eq_ker hε hε2]
  exact finrank_quotient_ker_bohrCharacter _

/-! ### The oscillating probe: two conditions off the zeros -/

/-- `p^{−ρ} = p^{−ρ̄}` forces `t log p ∈ πℤ`. -/
theorem exists_int_of_cpow_eq {p : ℕ} (hp : 0 < p) {ρ : ℂ}
    (h : (p : ℂ) ^ (-ρ) = (p : ℂ) ^ (-(starRingEnd ℂ ρ))) :
    ∃ n : ℤ, ρ.im * Real.log p = n * Real.pi := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [Complex.cpow_def_of_ne_zero hp0, Complex.cpow_def_of_ne_zero hp0] at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  refine ⟨-n, ?_⟩
  have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg p)]
  have hre : (Complex.log (p : ℂ)).re = Real.log p := by rw [hlog, Complex.ofReal_re]
  have him0 : (Complex.log (p : ℂ)).im = 0 := by rw [hlog, Complex.ofReal_im]
  have him := congrArg Complex.im hn
  simp [Complex.mul_im] at him
  rw [hre, him0] at him
  push_cast
  linarith

/-- `3^a = 2^b` with integers forces `a = 0`. -/
theorem int_eq_zero_of_three_zpow_eq_two_zpow {a b : ℤ} (h : (3 : ℝ) ^ a = (2 : ℝ) ^ b) : a = 0 := by
  by_contra ha
  -- reduce to positive exponents
  have key : ∀ a b : ℤ, 0 < a → (3 : ℝ) ^ a = (2 : ℝ) ^ b → False := by
    intro a b ha h
    have hb : 0 < b := by
      by_contra hb
      push Not at hb
      have h1 : (1 : ℝ) < (3 : ℝ) ^ a := one_lt_zpow₀ (by norm_num) ha
      have h2 : (2 : ℝ) ^ b ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hb
      linarith
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le ha.le
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hb.le
    simp only [zpow_natCast] at h
    have h' : (3 : ℕ) ^ m = 2 ^ n := by exact_mod_cast h
    have hn : n ≠ 0 := by rintro rfl; simp at hb
    have h2 : 2 ∣ 3 ^ m := h' ▸ dvd_pow_self 2 hn
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2) (by norm_num)
  rcases lt_or_gt_of_ne ha with ha' | ha'
  · exact key (-a) (-b) (by omega) (by rw [zpow_neg, zpow_neg, h])
  · exact key a b ha' h

/-- **The two pole points of the probe differ at `2` or at `3`** when `t ≠ 0`. -/
theorem exists_prime_ne_osc {ε t : ℝ} (hε2 : ε < 1 / 2) (ht : t ≠ 0) :
    ∃ p : ℕ, p.Prime ∧ (oscPoint ε t hε2).ω p ≠ (oscPointConj ε t hε2).ω p := by
  by_contra hno
  push Not at hno
  set ρ := oscillationExponent ε t
  have hpt : ∀ p : ℕ, p.Prime → (p : ℂ) ^ (-ρ) = (p : ℂ) ^ (-(starRingEnd ℂ ρ)) := fun p hp => by
    have h := hno p hp
    simp only [oscPoint, oscPointConj, halfPlanePoint, if_neg hp.ne_zero] at h
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hh : (p : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h' => hp0 h'.1
    rw [Complex.cpow_sub _ _ hp0, Complex.cpow_sub _ _ hp0, div_eq_mul_inv, div_eq_mul_inv] at h
    rw [Complex.cpow_neg, Complex.cpow_neg]
    exact mul_left_cancel₀ hh h
  have him : ρ.im = t := by simp [ρ, oscillationExponent]
  obtain ⟨a, ha⟩ := exists_int_of_cpow_eq (by norm_num) (hpt 2 Nat.prime_two)
  obtain ⟨b, hb⟩ := exists_int_of_cpow_eq (by norm_num) (hpt 3 Nat.prime_three)
  rw [him] at ha hb
  push_cast at ha hb
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  -- `b log 2 = a log 3`, hence `3^a = 2^b`
  have hab : (a : ℝ) * Real.log 3 = b * Real.log 2 := by
    have h1 : (a : ℝ) * Real.pi * Real.log 3 = (b : ℝ) * Real.pi * Real.log 2 := by
      rw [← ha, ← hb]; ring
    exact mul_right_cancel₀ Real.pi_ne_zero (by linarith [h1] :
      (a : ℝ) * Real.log 3 * Real.pi = b * Real.log 2 * Real.pi)
  have hpow : (3 : ℝ) ^ a = (2 : ℝ) ^ b := by
    rw [← Real.exp_log (zpow_pos (by norm_num : (0 : ℝ) < 3) a),
      ← Real.exp_log (zpow_pos (by norm_num : (0 : ℝ) < 2) b), Real.log_zpow, Real.log_zpow, hab]
  have ha0 := int_eq_zero_of_three_zpow_eq_two_zpow hpow
  rw [ha0] at ha
  push_cast at ha
  rcases mul_eq_zero.1 (by linarith : t * Real.log 2 = 0) with h | h
  · exact ht h
  · linarith

theorem paidIdeal_oscillating_eq_ker {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {t : ℝ}
    (hz : riemannZeta (oscillationExponent ε t) ≠ 0) :
    paidIdeal (oscillatingSmoothPower ε t) (summable_abs_oscillatingSmoothPower_div hε t) =
      RingHom.ker (bohrPair (oscPoint ε t hε2) (oscPointConj ε t hε2)) := by
  ext k
  rw [mem_paidIdeal_oscillating_iff hε hε2 hz, RingHom.mem_ker]
  simp only [bohrPair, AlgHom.prod_apply, bohrCharacter_apply, Prod.mk_eq_zero]

/-- **The oscillating probe imposes two conditions off the zeros of `ζ`.** -/
theorem finrank_quotient_paidIdeal_oscillating {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {t : ℝ}
    (ht : t ≠ 0) (hz : riemannZeta (oscillationExponent ε t) ≠ 0) :
    Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
      paidIdeal (oscillatingSmoothPower ε t) (summable_abs_oscillatingSmoothPower_div hε t)) = 2 := by
  rw [paidIdeal_oscillating_eq_ker hε hε2 hz]
  obtain ⟨p, hp, hne⟩ := exists_prime_ne_osc hε2 ht
  exact finrank_quotient_ker_bohrPair hp hne

/-- **At a zero of `ζ` the probe imposes no condition.** -/
theorem finrank_quotient_paidIdeal_oscillating_of_zeta_eq_zero {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε < 1 / 2) {t : ℝ} (hz : riemannZeta (oscillationExponent ε t) = 0) :
    Module.finrank ℂ (WienerAlgebraAt (1 / 2) ⧸
      paidIdeal (oscillatingSmoothPower ε t) (summable_abs_oscillatingSmoothPower_div hε t)) = 0 := by
  have htop : paidIdeal (oscillatingSmoothPower ε t) (summable_abs_oscillatingSmoothPower_div hε t) = ⊤ :=
    (Ideal.eq_top_iff_one _).2 ((one_mem_paidIdeal_iff _ _).2
      ((receiverBounded_oscillatingSmoothPower_iff hε hε2.le t).2 hz))
  rw [htop]
  haveI : Subsingleton (WienerAlgebraAt (1 / 2) ⧸ (⊤ : Ideal (WienerAlgebraAt (1 / 2)))) :=
    Ideal.Quotient.subsingleton_iff.2 rfl
  exact Module.finrank_zero_of_subsingleton

end

end GaloisForLFunctions.ArithmeticOrientationTheory
