import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheEulerExponentsOfSymmetricResidueFlips
import GaloisForLFunctions.RHTower.DirichletLReciprocalRightOfTheOneLine

/-!
# The quarter law of symmetric residue flips

Let `S ⊆ ZMod q` be closed under inversion on the units and `ρ = #(S ∩ units)/φ(q)` the proportion of
flipped unit classes. The half-damped weight `f_{q,S}(d) d^{-1/2}` is paid **iff** `ρ > 1/4`
(`receiverBounded_residueFlip_half_iff`).

* `ρ ≤ 1/4` is unpaid for every `S` (`not_receiverBounded_residueFlip_half_of_le`).
* For `ρ > 1/4` the Euler bound `|F| ≤ e^B |ζ|^{1−2ρ} Π_{χ≠1} |L(·, χ)|^{e_χ}`, `e_χ = −2s_χ/φ ∈ [−2, 2]`
  (`exists_norm_residueFlip_le_prod`), is controlled through `X^e ≤ max(X, 1/X)²`:
  on `|Im w| ≤ 9`, `|L|^{±1}` is bounded (`RHTower.exists_norm_LFunction_le_box`) and
  `|ζ|^{1−2ρ} ≲ |Im w|^{-(1−2ρ)⁺}`; on `|Im w| ≥ 9`, `|L| ≲ log|t|`, `1/|L| ≲ log⁷|t|`
  (`RHTower.exists_norm_inv_LFunction_le_log_pow`) and `|ζ|^{±1} ≲ log¹⁰|t|`, so `|F| ≪ |t|^{1/4}`.
  The singularity `|t|^{-2(1−2ρ)⁺}` of the line integrand is integrable since `ρ > 1/4`.

For symmetric residue patterns the flipped proportion `1/4` is the exact threshold. For oscillating
patterns, by contrast, the real-axis prime data do not decide the receiver.
-/

open Filter Topology MeasureTheory Complex Set
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Elementary bounds -/

/-- `X^e ≤ Λ²` when `X, X⁻¹ ≤ Λ`, `Λ ≥ 1` and `|e| ≤ 2`. -/
theorem rpow_le_sq_of_bounds {X Λ e : ℝ} (hX : 0 < X) (hΛ : 1 ≤ Λ) (h1 : X ≤ Λ) (h2 : X⁻¹ ≤ Λ)
    (he : |e| ≤ 2) : X ^ e ≤ Λ ^ 2 := by
  have hΛ2 : Λ ^ |e| ≤ Λ ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hΛ he
  rw [show Λ ^ 2 = Λ ^ (2 : ℝ) by rw [Real.rpow_two]]
  rcases le_total 0 e with h | h
  · calc X ^ e ≤ Λ ^ e := Real.rpow_le_rpow hX.le h1 h
      _ = Λ ^ |e| := by rw [abs_of_nonneg h]
      _ ≤ _ := hΛ2
  · calc X ^ e = (X⁻¹) ^ (-e) := by rw [Real.inv_rpow hX.le, Real.rpow_neg hX.le, inv_inv]
      _ ≤ Λ ^ (-e) := Real.rpow_le_rpow (inv_nonneg.mpr hX.le) h2 (by linarith)
      _ = Λ ^ |e| := by rw [abs_of_nonpos h]
      _ ≤ _ := hΛ2

/-- `log^N x ≤ (4(N + 1))^N x^{1/4}` for `x ≥ 1`. -/
theorem log_pow_le_rpow_quarter {x : ℝ} (hx : 1 ≤ x) (N : ℕ) :
    Real.log x ^ N ≤ (4 * (N + 1)) ^ N * x ^ (1 / 4 : ℝ) := by
  have h0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hε : (0 : ℝ) < 1 / (4 * (N + 1)) := by positivity
  have hlog : Real.log x ≤ 4 * (N + 1) * x ^ (1 / (4 * (N + 1)) : ℝ) := by
    have h := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ x) hε
    rw [div_eq_mul_inv, one_div, inv_inv] at h
    linarith
  have h1 := pow_le_pow_left₀ h0 hlog N
  rw [mul_pow, ← Real.rpow_natCast (x ^ (1 / (4 * (N + 1)) : ℝ)),
    ← Real.rpow_mul (by linarith)] at h1
  have hexp : (1 / (4 * ((N : ℝ) + 1))) * N ≤ 1 / 4 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  calc Real.log x ^ N ≤ (4 * (N + 1)) ^ N * x ^ ((1 / (4 * (N + 1)) : ℝ) * N) := h1
    _ ≤ (4 * (N + 1)) ^ N * x ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hexp) (by positivity)

/-- The coefficients are at most `φ(q)` in size. -/
theorem abs_re_setCoeff_le {q : ℕ} [NeZero q] (S : Finset (ZMod q)) (χ : DirichletCharacter ℂ q) :
    |(setCoeff S χ).re| ≤ q.totient := by
  refine (Complex.abs_re_le_norm _).trans ?_
  unfold setCoeff
  refine (norm_sum_le _ _).trans ?_
  calc ∑ u : (ZMod q)ˣ, ‖if (u : ZMod q) ∈ S then χ ((u⁻¹ : (ZMod q)ˣ) : ZMod q) else 0‖
      ≤ ∑ _u : (ZMod q)ˣ, (1 : ℝ) := Finset.sum_le_sum fun u _ => by
        split_ifs
        · exact (χ.unit_norm_eq_one _).le
        · simp
    _ = q.totient := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul, mul_one]

/-! ### The series as a product of powers -/

/-- **The Euler bound as a product**: `|F(w)| ≤ e^B |ζ(w)|^{1 − 2s_1/φ} Π_{χ ≠ 1} |L(w, χ)|^{e_χ}`. -/
theorem exists_norm_residueFlip_le_prod {q : ℕ} [NeZero q] {S : Finset (ZMod q)}
    (hS : UnitSymmetric S) :
    ∃ B : ℝ, ∀ w : ℂ, 1 < w.re →
      ‖∑' n : ℕ, (residueFlip q S n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
        Real.exp B * ‖riemannZeta w‖ ^ (1 - 2 * (setCoeff S 1).re / q.totient) *
          ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            ‖LSeries (fun n => χ n) w‖ ^ (-(2 / q.totient * (setCoeff S χ).re)) := by
  obtain ⟨B, hB⟩ := exists_log_norm_residueFlip_le hS
  refine ⟨B, fun w hw => ?_⟩
  have hζ := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re hw.le)
  have hL : ∀ χ : DirichletCharacter ℂ q, 0 < ‖LSeries (fun n => χ n) w‖ := fun χ =>
    norm_pos_iff.mpr (DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hw)
  rcases (norm_nonneg (∑' n : ℕ, (residueFlip q S n : ℂ) * ((n : ℝ) : ℂ) ^ (-w))).eq_or_lt
    with h0 | hpos
  · rw [← h0]; positivity
  rw [← Real.exp_log hpos]
  have hprod : ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      ‖LSeries (fun n => χ n) w‖ ^ (-(2 / q.totient * (setCoeff S χ).re)) =
        Real.exp (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          -(2 / q.totient * (setCoeff S χ).re) * Real.log ‖LSeries (fun n => χ n) w‖) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun χ _ => ?_
    rw [Real.rpow_def_of_pos (hL χ), mul_comm]
  rw [hprod, Real.rpow_def_of_pos hζ, ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h := hB w hw
  have hsum : ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      -(2 / q.totient * (setCoeff S χ).re) * Real.log ‖LSeries (fun n => χ n) w‖ =
        -(2 / q.totient * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          (setCoeff S χ).re * Real.log ‖LSeries (fun n => χ n) w‖) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun χ _ => by ring
  rw [hsum]
  linarith

/-- **The nonprincipal factors.** For exponents `|e_χ| ≤ 2`, the product
`Π_{χ ≠ 1} |L(w, χ)|^{e_χ}` is bounded on `1 < Re w ≤ 2`, `|Im w| ≤ 9`, and `≤ C log^{14k}|Im w|` for
`|Im w| ≥ 9`, `k` the number of nonprincipal characters. -/
theorem exists_prod_LSeries_rpow_le {q : ℕ} [NeZero q] (e : DirichletCharacter ℂ q → ℝ)
    (he : ∀ χ, |e χ| ≤ 2) :
    ∃ Ml Cl : ℝ, 0 ≤ Ml ∧ 0 ≤ Cl ∧ ∀ w : ℂ, 1 < w.re → w.re ≤ 2 →
      (|w.im| ≤ 9 → ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ‖LSeries (fun n => χ n) w‖ ^ e χ ≤ Ml) ∧
      (9 ≤ |w.im| → ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ‖LSeries (fun n => χ n) w‖ ^ e χ ≤
            Cl * Real.log |w.im| ^ (14 * (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card)) := by
  have hbox : ∀ χ : DirichletCharacter ℂ q, ∃ M : ℝ, 1 ≤ M ∧ (χ ≠ 1 → ∀ s : ℂ, 1 ≤ s.re →
      s.re ≤ 2 → |s.im| ≤ 9 → ‖DirichletCharacter.LFunction χ s‖ ≤ M ∧
        ‖(DirichletCharacter.LFunction χ s)⁻¹‖ ≤ M) := fun χ => by
    by_cases hχ : χ = 1
    · exact ⟨1, le_rfl, fun h => absurd hχ h⟩
    · obtain ⟨M, hM1, hM⟩ := RHTower.exists_norm_LFunction_le_box hχ 9
      exact ⟨M, hM1, fun _ => hM⟩
  choose M hM1 hM using hbox
  have hinv : ∀ χ : DirichletCharacter ℂ q, ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
      9 ≤ |t| → ‖(DirichletCharacter.LFunction χ (σ + t * I))⁻¹‖ ≤ C * Real.log |t| ^ (7 : ℕ) :=
    fun χ => RHTower.exists_norm_inv_LFunction_le_log_pow χ
  choose C hC hCb using hinv
  set K := RHTower.characterLogStripConstant q
  have hK : 1 ≤ K := RHTower.one_le_characterLogStripConstant q
  set E := Finset.univ.erase (1 : DirichletCharacter ℂ q)
  refine ⟨∏ χ ∈ E, M χ ^ 2, ∏ χ ∈ E, (K + C χ) ^ 2,
    Finset.prod_nonneg fun χ _ => sq_nonneg _, Finset.prod_nonneg fun χ _ => sq_nonneg _,
    fun w hw hw2 => ⟨fun ht => ?_, fun ht => ?_⟩⟩
  · refine Finset.prod_le_prod (fun χ _ => Real.rpow_nonneg (norm_nonneg _) _) fun χ hχ => ?_
    have hχ1 : χ ≠ 1 := Finset.ne_of_mem_erase hχ
    rw [← DirichletCharacter.LFunction_eq_LSeries χ hw]
    have hpos := norm_pos_iff.mpr
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hw.le)
    obtain ⟨h1, h2⟩ := hM χ hχ1 w hw.le hw2 ht
    exact rpow_le_sq_of_bounds hpos (hM1 χ) h1 (by rwa [← norm_inv]) (he χ)
  · set L := Real.log |w.im|
    have hL2 : 2 < L := by
      have h := Real.log_lt_log (Real.exp_pos 2)
        (lt_of_lt_of_le RHTower.exp_two_lt_eight (by linarith : (8 : ℝ) ≤ |w.im|))
      rwa [Real.log_exp] at h
    have hL1 : 1 ≤ L := by linarith
    have hL7 : 1 ≤ L ^ (7 : ℕ) := one_le_pow₀ hL1
    have hwst : w = (w.re : ℂ) + (w.im : ℂ) * I := (Complex.re_add_im w).symm
    calc ∏ χ ∈ E, ‖LSeries (fun n => χ n) w‖ ^ e χ
        ≤ ∏ χ ∈ E, ((K + C χ) * L ^ (7 : ℕ)) ^ 2 := by
          refine Finset.prod_le_prod (fun χ _ => Real.rpow_nonneg (norm_nonneg _) _)
            fun χ hχ => ?_
          have hχ1 : χ ≠ 1 := Finset.ne_of_mem_erase hχ
          rw [← DirichletCharacter.LFunction_eq_LSeries χ hw]
          have hpos := norm_pos_iff.mpr
            (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hw.le)
          have hup : ‖DirichletCharacter.LFunction χ w‖ ≤ K * L := by
            have h := RHTower.norm_LFunction_le_log χ (σ := w.re) (t := w.im) (by linarith)
              (by have : 0 < 1 / L := by positivity
                  linarith) hw2
            rwa [← hwst] at h
          have hlow : ‖DirichletCharacter.LFunction χ w‖⁻¹ ≤ C χ * L ^ (7 : ℕ) := by
            have h := hCb χ w.re w.im hw.le hw2 ht
            rwa [← hwst, norm_inv] at h
          have hCpos := hC χ
          refine rpow_le_sq_of_bounds hpos ?_ ?_ ?_ (he χ)
          · nlinarith
          · calc ‖DirichletCharacter.LFunction χ w‖ ≤ K * L := hup
              _ ≤ K * L ^ (7 : ℕ) := mul_le_mul_of_nonneg_left
                  (by calc L = L ^ (1 : ℕ) := (pow_one L).symm
                      _ ≤ L ^ (7 : ℕ) := pow_le_pow_right₀ hL1 (by norm_num)) (by linarith)
              _ ≤ (K + C χ) * L ^ (7 : ℕ) := by nlinarith
          · exact hlow.trans (by nlinarith)
      _ = (∏ χ ∈ E, (K + C χ) ^ 2) * L ^ (14 * E.card) := by
          rw [Finset.prod_congr rfl fun χ _ => mul_pow (K + C χ) (L ^ (7 : ℕ)) 2,
            Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul, ← pow_mul]
          ring_nf

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
