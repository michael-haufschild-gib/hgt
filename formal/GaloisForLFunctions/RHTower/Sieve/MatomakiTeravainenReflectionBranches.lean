import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenReflectionArithmetic

/-!
# The three unconditional branches of Matomäki–Teräväinen Lemma 3.5 beyond `N² ≤ T`

Fix a numerator `Num ≥ T + A²√T` and an energy `E ≥ (1/A)∑_{A<m≤2A}|a_m|²`.  Write
`Q = (T + A)/(T⁴A)`.  For `T ≥ 2`, `1 ≤ N < N' ≤ 2N` and `N² > T`:

* **over-height** (`T ≤ N`): `∫_{T/2}^{T} |U_N|⁴|𝒜|² ≤ K_O Q E` (`mt_branch_overHeight`);
* **short dual** (`N < T`, `T/(2πN) ≤ 11`): `≤ K (1 + log T)⁴ (Num/(N²A)) E`
  (`exists_mt_branch_shortDual`);
* **reflection** (`N < T`, `T/(2πN) > 11`): if the dual blocks `U_B`, `B ∈ {M, 2M, 4M}`, have
  twisted fourth moments at most `G = S (5T/4)^{η/2}((5/4)Num/(M²A) + 20Q)E` on the three windows,
  then `≤ K_η (1 + S) T^η (Num/(N²A) + Q) E` (`exists_mt_branch_reflection`).
-/

open Complex Set MeasureTheory Filter
open scoped Real

namespace RHTower.Sieve

noncomputable section

/-- The coefficient energy `∑_{A<m≤2A}|a_m|²`. -/
def mtEnergy (a : ℕ → ℂ) (A : ℕ) : ℝ := ∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ 2

theorem mtEnergy_nonneg (a : ℕ → ℂ) (A : ℕ) : 0 ≤ mtEnergy a A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Over-height branch.** -/
theorem mt_branch_overHeight (a : ℕ → ℂ) {A N N' : ℕ} (hA : 1 ≤ A) (hN : 1 ≤ N) (hNN' : N < N')
    (hN' : N' ≤ 2 * N) {T E : ℝ} (hT : 2 ≤ T) (hTN : T ≤ N)
    (hE : 1 / (A : ℝ) * mtEnergy a A ≤ E) :
    (∫ t in (T / 2)..T, ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
      (2 * (6 * π + 1)) ^ 4 * (5 * π * Real.exp 1) * ((T + A) / (T ^ 4 * A) * E) := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have h := integral_mtWatt_overHeight_le_energy a hA hN hNN' hN' (by linarith : (1 : ℝ) ≤ T) hTN
  have h2 := ub_overHeight_le (by linarith : (0 : ℝ) < T) hA0 (mtEnergy_nonneg a A)
  rw [mtEnergy] at h2 hE
  refine le_trans h (le_trans h2 ?_)
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE (by positivity)) (by positivity)

/-- **The reflection error against the energy.** -/
theorem mt_reflection_error_le (a : ℕ → ℂ) {A N : ℕ} (hA : 1 ≤ A) (hN : 1 ≤ N) {T E Num : ℝ}
    (hT : 2 ≤ T) (hNT : (N : ℝ) < T) (hE : 1 / (A : ℝ) * mtEnergy a A ≤ E)
    (hNum : T + (A : ℝ) ^ 2 * Real.sqrt T ≤ Num) :
    ((1 + Real.log T) / N + 1 / Real.sqrt T) ^ 4 *
        (∫ t in (T / 2)..T, ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
      16 * (5 * π * Real.exp 1 + 5 * π / 2) * (1 + Real.log T) ^ 4 *
        (Num / ((N : ℝ) ^ 2 * A) * E) := by
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hMV := integral_normSq_mtWattCoefficientBlock_window_le a hA (by linarith : (1 : ℝ) ≤ T)
  have herr := ub_error_le (by linarith) hN1 hNT hA1 (mtEnergy_nonneg a A)
  rw [mtEnergy] at herr hE
  refine le_trans (mul_le_mul_of_nonneg_left hMV (by positivity)) (le_trans herr ?_)
  refine mul_le_mul_of_nonneg_left (mul_le_mul (div_le_div_of_nonneg_right hNum
    (by positivity)) hE (by positivity) ?_) (by positivity)
  exact div_nonneg (le_trans (by positivity) hNum) (by positivity)

/-- **Short-dual branch.** -/
theorem exists_mt_branch_shortDual :
    ∃ K : ℝ, 0 < K ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ) (T E Num : ℝ), 1 ≤ A → 1 ≤ N → N < N' →
      N' ≤ 2 * N → 2 ≤ T → (N : ℝ) < T → T < (N : ℝ) ^ 2 → T / (2 * π * N) ≤ 11 →
      1 / (A : ℝ) * mtEnergy a A ≤ E → T + (A : ℝ) ^ 2 * Real.sqrt T ≤ Num →
      (∫ t in (T / 2)..T, ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
        K * (1 + Real.log T) ^ 4 * (Num / ((N : ℝ) ^ 2 * A) * E) := by
  obtain ⟨C, hC, hpt⟩ := exists_norm_mtWattUnitBlock_le_short_dual
  refine ⟨C ^ 4 * (16 * (5 * π * Real.exp 1 + 5 * π / 2)), by positivity,
    fun a A N N' T E Num hA hN hNN' hN' hT hNT hTN hY hE hNum => ?_⟩
  set X := (1 + Real.log T) / N + 1 / Real.sqrt T
  have hcA : Continuous fun t => ‖mtWattCoefficientBlock a A t‖ ^ 2 :=
    (continuous_perronPoly _ _ _ : Continuous (mtWattCoefficientBlock a A)).norm.pow 2
  have hpoint : ∀ t ∈ Icc (T / 2) T, ‖mtWattUnitBlock N N' t‖ ^ 4 *
      ‖mtWattCoefficientBlock a A t‖ ^ 2 ≤ (C * X) ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2 :=
    fun t ht => mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _)
      (hpt N N' hN hNN' hN' T hT hNT hTN hY t ht) 4) (sq_nonneg _)
  have hmono := intervalIntegral.integral_mono_on (by linarith)
    ((((continuous_mtWattUnitBlock N N').norm.pow 4).mul hcA).intervalIntegrable _ _)
    ((hcA.const_mul _).intervalIntegrable (μ := volume) _ _) hpoint
  rw [intervalIntegral.integral_const_mul, mul_pow] at hmono
  have herr := mt_reflection_error_le a hA hN hT hNT hE hNum
  refine le_trans hmono ?_
  rw [mul_assoc]
  calc C ^ 4 * (X ^ 4 * ∫ t in (T / 2)..T, ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
      C ^ 4 * (16 * (5 * π * Real.exp 1 + 5 * π / 2) * (1 + Real.log T) ^ 4 *
        (Num / ((N : ℝ) ^ 2 * A) * E)) := mul_le_mul_of_nonneg_left herr (by positivity)
    _ = _ := by ring

/-- The reflection-branch bookkeeping over plain reals. -/
private theorem mt_reflection_combine {c₁ c₂ KE KL I1 IA X4 L4 lg Y4T sh S E P Q Tη2 Tη Kp : ℝ}
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hKE : 0 ≤ KE) (hKL : 0 ≤ KL) (hS : 0 ≤ S) (hE : 0 ≤ E)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hTη2 : 0 ≤ Tη2) (hKp : 0 ≤ Kp)
    (hcore : I1 ≤ c₁ * X4 * IA + c₂ * Y4T * lg * (S * (Kp * Tη2) * sh * E))
    (herr : X4 * IA ≤ KE * L4 * (P * E)) (hL4 : L4 ≤ KL * Tη2) (hlgL : lg ≤ L4)
    (hshape : Y4T * sh ≤ 4 * (P + Q)) (hη2 : Tη2 ≤ Tη) (hηη : Tη2 * Tη2 = Tη)
    (hY4T : 0 ≤ Y4T) (hsh : 0 ≤ sh) :
    I1 ≤ (c₁ * KE * KL + 4 * c₂ * KL * Kp) * (1 + S) * Tη * ((P + Q) * E) := by
  have hTη : 0 ≤ Tη := le_trans hTη2 hη2
  have a1 : c₁ * X4 * IA ≤ c₁ * KE * KL * Tη * ((P + Q) * E) := by
    have h1 : X4 * IA ≤ KE * (KL * Tη2) * (P * E) :=
      le_trans herr (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL4 hKE)
        (mul_nonneg hP hE))
    have h2 : KE * (KL * Tη2) * (P * E) ≤ KE * KL * Tη * ((P + Q) * E) := by
      have : P * E ≤ (P + Q) * E := mul_le_mul_of_nonneg_right (by linarith) hE
      calc KE * (KL * Tη2) * (P * E) = KE * KL * Tη2 * (P * E) := by ring
        _ ≤ KE * KL * Tη * ((P + Q) * E) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hη2 (mul_nonneg hKE hKL)) this
              (mul_nonneg hP hE) (by positivity)
    calc c₁ * X4 * IA = c₁ * (X4 * IA) := by ring
      _ ≤ c₁ * (KE * KL * Tη * ((P + Q) * E)) := mul_le_mul_of_nonneg_left (h1.trans h2) hc₁
      _ = c₁ * KE * KL * Tη * ((P + Q) * E) := by ring
  have a2 : c₂ * Y4T * lg * (S * (Kp * Tη2) * sh * E) ≤
      4 * c₂ * KL * Kp * S * Tη * ((P + Q) * E) := by
    have hlg' : lg ≤ KL * Tη2 := hlgL.trans hL4
    have e : c₂ * Y4T * lg * (S * (Kp * Tη2) * sh * E) =
        c₂ * S * Kp * Tη2 * E * lg * (Y4T * sh) := by ring
    rw [e]
    have b1 : c₂ * S * Kp * Tη2 * E * lg * (Y4T * sh) ≤
        c₂ * S * Kp * Tη2 * E * (KL * Tη2) * (4 * (P + Q)) := by
      have h0 : 0 ≤ c₂ * S * Kp * Tη2 * E := by positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_left hlg' h0) hshape (mul_nonneg hY4T hsh)
        (mul_nonneg h0 (by positivity))
    have e2 : c₂ * S * Kp * Tη2 * E * (KL * Tη2) * (4 * (P + Q)) =
        4 * c₂ * KL * Kp * S * (Tη2 * Tη2) * ((P + Q) * E) := by ring
    rw [e2, hηη] at b1
    exact b1
  have hsum : (c₁ * KE * KL + 4 * c₂ * KL * Kp) * (1 + S) * Tη * ((P + Q) * E) =
      c₁ * KE * KL * Tη * ((P + Q) * E) + c₁ * KE * KL * S * Tη * ((P + Q) * E) +
        4 * c₂ * KL * Kp * S * Tη * ((P + Q) * E) + 4 * c₂ * KL * Kp * Tη * ((P + Q) * E) := by
    ring
  have hx1 : 0 ≤ c₁ * KE * KL * S * Tη * ((P + Q) * E) := by
    have : 0 ≤ P + Q := by linarith
    positivity
  have hx2 : 0 ≤ 4 * c₂ * KL * Kp * Tη * ((P + Q) * E) := by
    have : 0 ≤ P + Q := by linarith
    positivity
  rw [hsum]
  linarith

/-- **Reflection branch.** -/
theorem exists_mt_branch_reflection {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ) (T E Num S : ℝ), 1 ≤ A → 1 ≤ N → N < N' →
      N' ≤ 2 * N → 2 ≤ T → (N : ℝ) < T → T < (N : ℝ) ^ 2 → 11 ≤ T / (2 * π * N) →
      1 / (A : ℝ) * mtEnergy a A ≤ E → T + (A : ℝ) ^ 2 * Real.sqrt T ≤ Num → 0 ≤ S →
      (∀ B : ℕ, (B = ubDualBase N' T ∨ B = 2 * ubDualBase N' T ∨ B = 4 * ubDualBase N' T) →
        ∀ u : ℝ, |u| ≤ T / 4 → ∀ T' : ℝ, (T' = T / 2 ∨ T' = T ∨ T' = 5 * T / 4) →
        ∫ τ in (T' / 2)..T', ‖mtWattUnitBlock B (2 * B) τ‖ ^ 4 *
          ‖mtWattCoefficientBlock (mtTwist a u) A τ‖ ^ 2 ≤
          S * (5 * T / 4) ^ (η / 2) * (5 / 4 * Num / ((ubDualBase N' T : ℝ) ^ 2 * A) +
            20 * ((T + A) / (T ^ 4 * A))) * E) →
      (∫ t in (T / 2)..T, ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
        K * (1 + S) * T ^ η * ((Num / ((N : ℝ) ^ 2 * A) + (T + A) / (T ^ 4 * A)) * E) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hcore⟩ := exists_integral_unitBlock_fourth_le_dual
  set KE := 16 * (5 * π * Real.exp 1 + 5 * π / 2) with hKE
  set KL := (1 + 1 / (η / 8)) ^ 4 with hKL
  set Kp := (5 / 4 : ℝ) ^ (η / 2) with hKp
  refine ⟨c₁ * KE * KL + 4 * c₂ * KL * Kp, by positivity,
    fun a A N N' T E Num S hA hN hNN' hN' hT hNT hTN hY hE hNum hS hG => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hT0 : 0 < T := by linarith
  have hE0 : 0 ≤ E := le_trans (by positivity [mtEnergy_nonneg a A]) hE
  have hNum0 : 0 ≤ Num := le_trans (by positivity) hNum
  have hQ : 0 ≤ (T + A) / (T ^ 4 * A) := by positivity
  have hP : 0 ≤ Num / ((N : ℝ) ^ 2 * A) := by positivity
  set M := ubDualBase N' T with hM
  have hY9 : 9 ≤ T / (2 * π * N) := by linarith
  have hMY := ub_dualBase_ge hN hNN' hN' hT0 hY9
  have hY2 := ub_Y_sq_le hN1 hT0 hTN
  have hTY : T = 2 * π * N * (T / (2 * π * N)) := by field_simp
  have hshape := ub_main_shape (Y := T / (2 * π * N)) (N := N) (M := M) (A := A) (Num := Num)
    (Q := (T + A) / (T ^ 4 * A)) (by linarith) hN1 hA0 hMY hY2 hTY hNum0 hQ
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le (by positivity) hMY
  -- the core estimate
  have hGnn : 0 ≤ S * (5 * T / 4) ^ (η / 2) * (5 / 4 * Num / ((M : ℝ) ^ 2 * A) +
      20 * ((T + A) / (T ^ 4 * A))) * E := by positivity
  have hc := hcore a A N N' T _ hN hNN' hN' hNT hTN hY hGnn hG
  have herr := mt_reflection_error_le a hA hN hT hNT hE hNum
  -- logarithms and powers
  have hL4 := one_add_log_pow_four_le_mul_rpow (ε := η / 8) (by positivity) (by linarith : (1 : ℝ) ≤ T)
  rw [show 4 * (η / 8) = η / 2 by ring] at hL4
  have hlgL : Real.log (1 + T / 4) ^ 4 ≤ (1 + Real.log T) ^ 4 := by
    have h1 : Real.log (1 + T / 4) ≤ Real.log T := Real.log_le_log (by positivity) (by linarith)
    have h0 : 0 ≤ Real.log (1 + T / 4) := Real.log_nonneg (by linarith)
    exact pow_le_pow_left₀ h0 (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)]) 4
  have hsplit : (5 * T / 4) ^ (η / 2) = Kp * T ^ (η / 2) := by
    rw [hKp, show 5 * T / 4 = 5 / 4 * T by ring, Real.mul_rpow (by norm_num) hT0.le]
  have hη2 : T ^ (η / 2) ≤ T ^ η :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hηη : T ^ (η / 2) * T ^ (η / 2) = T ^ η := by
    rw [← Real.rpow_add hT0]; ring_nf
  rw [hsplit] at hc
  have hY4T : 0 ≤ (T / (2 * π * N)) ^ 4 / T ^ 2 := by positivity
  have hsh : 0 ≤ 5 / 4 * Num / ((M : ℝ) ^ 2 * A) + 20 * ((T + A) / (T ^ 4 * A)) := by positivity
  exact mt_reflection_combine hc₁.le hc₂.le (by positivity) (by positivity) hS hE0 hP hQ
    (by positivity) (by positivity) hc herr hL4 hlgL hshape hη2 hηη hY4T hsh

end

end RHTower.Sieve
