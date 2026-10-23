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
    rw [div_div_eq_mul_div, div_one, mul_comm] at h
    exact h
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


/-! ### Size on the strip and the receiver -/

/-- **Size on the strip from an Euler bound.** Suppose `|F(w)| ≤ e^B |ζ(w)|^{1 − 2s_1/φ} Φ(w)` on
`Re w > 1` with `Φ ≥ 0`, `Φ ≤ M` for `|Im w| ≤ 9` and `Φ ≤ C log^N|Im w|` for `|Im w| ≥ 9`. With
`a₀ = max(1 − 2s_1/φ, 0)`: `|F(w)| ≤ A(|Im w|^{-a₀} + 1)` for `0 < |Im w| ≤ 9` and
`|F(w)| ≤ B₁|Im w|^{1/4}` for `|Im w| ≥ 9`, on `1 < Re w ≤ 2`. -/
theorem exists_norm_residueFlip_bounds_of {q : ℕ} [NeZero q] {S : Finset (ZMod q)}
    {Φ : ℂ → ℝ} {B Ml Cl : ℝ} {N : ℕ} (hΦ0 : ∀ w, 0 ≤ Φ w) (hMl : 0 ≤ Ml) (hCl : 0 ≤ Cl)
    (hB : ∀ w : ℂ, 1 < w.re →
      ‖∑' n : ℕ, (residueFlip q S n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
        Real.exp B * ‖riemannZeta w‖ ^ (1 - 2 * (setCoeff S 1).re / q.totient) * Φ w)
    (hΦbox : ∀ w : ℂ, 1 < w.re → w.re ≤ 2 → |w.im| ≤ 9 → Φ w ≤ Ml)
    (hΦlarge : ∀ w : ℂ, 1 < w.re → w.re ≤ 2 → 9 ≤ |w.im| → Φ w ≤ Cl * Real.log |w.im| ^ N) :
    ∃ A B₁ : ℝ, 0 ≤ A ∧ ∀ w : ℂ, 1 < w.re → w.re ≤ 2 →
      (0 < |w.im| → |w.im| ≤ 9 →
        ‖∑' n : ℕ, (residueFlip q S n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
          A * (|w.im| ^ (-max (1 - 2 * (setCoeff S 1).re / q.totient) 0) + 1)) ∧
      (9 ≤ |w.im| → ‖∑' n : ℕ, (residueFlip q S n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
          B₁ * |w.im| ^ (1 / 4 : ℝ)) := by
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hs₁0 : 0 ≤ (setCoeff S 1).re := by
    rw [setCoeff_one, Complex.natCast_re]; exact Nat.cast_nonneg _
  have hs₁ : (setCoeff S 1).re ≤ q.totient := (le_abs_self _).trans (abs_re_setCoeff_le S 1)
  set e₀ := 1 - 2 * (setCoeff S 1).re / q.totient
  have he₀1 : e₀ ≤ 1 := by
    have : 0 ≤ 2 * (setCoeff S 1).re / q.totient := by positivity
    simp only [e₀]; linarith
  have he₀m : -1 ≤ e₀ := by
    have : 2 * (setCoeff S 1).re / q.totient ≤ 2 := by
      rw [div_le_iff₀ hφ]; linarith
    simp only [e₀]; linarith
  obtain ⟨K₀, hK₀, hpole⟩ := exists_norm_zeta_mul_sub_one_le
  obtain ⟨K₂, hK₂, hbox⟩ := exists_inv_norm_zeta_le_box
  obtain ⟨K₁, hK₁, hlarge⟩ := exists_inv_norm_zeta_le_log_pow_large
  set Aζ : ℝ := max (max (K₀ ^ e₀) 14) (1 + K₂)
  have hAζ : 0 ≤ Aζ := le_max_of_le_right (by linarith)
  refine ⟨Real.exp B * Aζ * Ml,
    Real.exp B * (K₁ + 7) * Cl * (4 * ((10 + N : ℕ) + 1)) ^ (10 + N),
    by positivity, fun w hw hw2 => ⟨fun ht0 ht => ?_, fun ht => ?_⟩⟩
  · -- small heights
    have hF := hB w hw
    have hLp := hΦbox w hw hw2 ht
    have hζpos := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re hw.le)
    have hζf : ‖riemannZeta w‖ ^ e₀ ≤ Aζ * (|w.im| ^ (-max e₀ 0) + 1) := by
      have hpow0 : 0 ≤ |w.im| ^ (-max e₀ 0) := Real.rpow_nonneg (abs_nonneg _) _
      rcases le_total 0 e₀ with he0 | he0
      · rw [max_eq_left he0]
        rcases le_total |w.im| 2 with h2 | h2
        · have hp := hpole w hw hw2 h2
          have him : |w.im| ≤ ‖w - 1‖ := by
            have := Complex.abs_im_le_norm (w - 1)
            rwa [Complex.sub_im, Complex.one_im, sub_zero] at this
          have hz : ‖riemannZeta w‖ ≤ K₀ / |w.im| := by
            rw [le_div_iff₀ ht0]
            exact (mul_le_mul_of_nonneg_left him (norm_nonneg _)).trans hp
          calc ‖riemannZeta w‖ ^ e₀ ≤ (K₀ / |w.im|) ^ e₀ := Real.rpow_le_rpow hζpos.le hz he0
            _ = K₀ ^ e₀ * |w.im| ^ (-e₀) := by
                rw [Real.div_rpow hK₀.le (abs_nonneg _), Real.rpow_neg (abs_nonneg _),
                  div_eq_mul_inv]
            _ ≤ Aζ * (|w.im| ^ (-e₀) + 1) := by
                have h1 : K₀ ^ e₀ ≤ Aζ := le_max_of_le_left (le_max_left _ _)
                have h2 : 0 ≤ K₀ ^ e₀ := Real.rpow_nonneg hK₀.le _
                nlinarith [Real.rpow_nonneg (abs_nonneg w.im) (-e₀)]
        · have hz := RHTower.norm_riemannZeta_le_log_add (s := w) hw.le hw2 h2
          have hl9 : Real.log |w.im| ≤ 8 := by
            have := Real.log_le_sub_one_of_pos (show 0 < |w.im| by linarith); linarith
          have h1 := rpow_le_one_add_self (norm_nonneg (riemannZeta w)) he0 he₀1
          have h14 : (14 : ℝ) ≤ Aζ := le_max_of_le_left (le_max_right _ _)
          have hp : 0 ≤ Aζ * |w.im| ^ (-e₀) := mul_nonneg hAζ (Real.rpow_nonneg (abs_nonneg _) _)
          linarith
      · rw [max_eq_right he0, neg_zero, Real.rpow_zero]
        have hinv : ‖riemannZeta w‖ ^ e₀ = (‖riemannZeta w‖⁻¹) ^ (-e₀) := by
          rw [Real.inv_rpow hζpos.le, Real.rpow_neg hζpos.le, inv_inv]
        have h1 := rpow_le_one_add_self (inv_nonneg.mpr hζpos.le) (by linarith : 0 ≤ -e₀)
          (by linarith)
        have h2 := hbox w hw hw2 ht
        have h3 : 1 + K₂ ≤ Aζ := le_max_right _ _
        rw [hinv]
        nlinarith
    calc ‖∑' n : ℕ, (residueFlip q S n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖
        ≤ Real.exp B * ‖riemannZeta w‖ ^ e₀ * Φ w := hF
      _ ≤ Real.exp B * (Aζ * (|w.im| ^ (-max e₀ 0) + 1)) * Ml :=
          mul_le_mul (mul_le_mul_of_nonneg_left hζf (Real.exp_pos _).le) hLp (hΦ0 w) (by positivity)
      _ = Real.exp B * Aζ * Ml * (|w.im| ^ (-max e₀ 0) + 1) := by ring
  · -- large heights
    have hF := hB w hw
    have hLp := hΦlarge w hw hw2 ht
    have hζpos := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re hw.le)
    set L := Real.log |w.im|
    have hL2 : 2 < L := by
      have h := Real.log_lt_log (Real.exp_pos 2)
        (lt_of_lt_of_le RHTower.exp_two_lt_eight (by linarith : (8 : ℝ) ≤ |w.im|))
      rwa [Real.log_exp] at h
    have hL10 : 1 ≤ L ^ 10 := one_le_pow₀ (by linarith)
    have hLL : L ≤ L ^ 10 := by
      calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ 10 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have hζf : ‖riemannZeta w‖ ^ e₀ ≤ (K₁ + 7) * L ^ 10 := by
      rcases le_total 0 e₀ with he0 | he0
      · have hz := RHTower.norm_riemannZeta_le_log_add (s := w) hw.le hw2 (by linarith)
        have h1 := rpow_le_one_add_self (norm_nonneg (riemannZeta w)) he0 he₀1
        nlinarith
      · have hinv : ‖riemannZeta w‖ ^ e₀ = (‖riemannZeta w‖⁻¹) ^ (-e₀) := by
          rw [Real.inv_rpow hζpos.le, Real.rpow_neg hζpos.le, inv_inv]
        have h1 := rpow_le_one_add_self (inv_nonneg.mpr hζpos.le) (by linarith : 0 ≤ -e₀)
          (by linarith)
        have h2 := hlarge w hw hw2 ht
        rw [hinv]
        nlinarith
    have hlog := log_pow_le_rpow_quarter (show (1 : ℝ) ≤ |w.im| by linarith) (10 + N)
    have hsplit : L ^ 10 * L ^ N = L ^ (10 + N) := by rw [← pow_add]
    calc ‖∑' n : ℕ, (residueFlip q S n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖
        ≤ Real.exp B * ‖riemannZeta w‖ ^ e₀ * Φ w := hF
      _ ≤ Real.exp B * ((K₁ + 7) * L ^ 10) * (Cl * L ^ N) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hζf (Real.exp_pos _).le) hLp (hΦ0 w) (by positivity)
      _ = Real.exp B * (K₁ + 7) * Cl * L ^ (10 + N) := by rw [← hsplit]; ring
      _ ≤ Real.exp B * (K₁ + 7) * Cl *
            ((4 * ((10 + N : ℕ) + 1)) ^ (10 + N) * |w.im| ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by ring

/-- **The size of a symmetric residue flip on the strip.** -/
theorem exists_norm_residueFlip_bounds {q : ℕ} [NeZero q] {S : Finset (ZMod q)}
    (hS : UnitSymmetric S) :
    ∃ A B₁ : ℝ, 0 ≤ A ∧ ∀ w : ℂ, 1 < w.re → w.re ≤ 2 →
      (0 < |w.im| → |w.im| ≤ 9 →
        ‖∑' n : ℕ, (residueFlip q S n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
          A * (|w.im| ^ (-max (1 - 2 * (setCoeff S 1).re / q.totient) 0) + 1)) ∧
      (9 ≤ |w.im| → ‖∑' n : ℕ, (residueFlip q S n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
          B₁ * |w.im| ^ (1 / 4 : ℝ)) := by
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  set e : DirichletCharacter ℂ q → ℝ := fun χ => -(2 / q.totient * (setCoeff S χ).re)
  have he : ∀ χ, |e χ| ≤ 2 := fun χ => by
    simp only [e]
    rw [abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / q.totient), div_mul_eq_mul_div,
      div_le_iff₀ hφ]
    have := abs_re_setCoeff_le S χ
    linarith
  obtain ⟨B, hB⟩ := exists_norm_residueFlip_le_prod hS
  obtain ⟨Ml, Cl, hMl, hCl, hLprod⟩ := exists_prod_LSeries_rpow_le e he
  exact exists_norm_residueFlip_bounds_of
    (Φ := fun w => ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      ‖LSeries (fun n => χ n) w‖ ^ e χ)
    (fun w => Finset.prod_nonneg fun χ _ => Real.rpow_nonneg (norm_nonneg _) _) hMl hCl hB
    (fun w hw hw2 ht => (hLprod w hw hw2).1 ht) (fun w hw hw2 ht => (hLprod w hw hw2).2 ht)

/-- **Strip bounds above the quarter pay the receiver.** If `|F| ≤ A(|Im w|^{-a₀} + 1)` on
`0 < |Im w| ≤ 9` and `|F| ≤ B₁|Im w|^{1/4}` beyond, and more than a quarter of the unit classes are
flipped, `f_{q,S}(d) d^{-1/2}` is paid. -/
theorem receiverBounded_residueFlip_half_of_bounds {q : ℕ} [NeZero q] {S : Finset (ZMod q)}
    {A B₁ : ℝ} (hA : 0 ≤ A)
    (hbd : ∀ w : ℂ, 1 < w.re → w.re ≤ 2 →
      (0 < |w.im| → |w.im| ≤ 9 →
        ‖∑' n : ℕ, (residueFlip q S n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
          A * (|w.im| ^ (-max (1 - 2 * (setCoeff S 1).re / q.totient) 0) + 1)) ∧
      (9 ≤ |w.im| → ‖∑' n : ℕ, (residueFlip q S n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
          B₁ * |w.im| ^ (1 / 4 : ℝ)))
    (h4 : q.totient < 4 * (S.filter IsUnit).card) :
    ReceiverBounded (fun d => residueFlip q S d * (d : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  set a₀ := max (1 - 2 * (setCoeff S 1).re / q.totient) 0
  have ha₀0 : 0 ≤ a₀ := le_max_right _ _
  have ha₀ : 2 * a₀ < 1 := by
    have h4' : (q.totient : ℝ) < 4 * (S.filter IsUnit).card := by exact_mod_cast h4
    have hlt : 1 - 2 * (setCoeff S 1).re / q.totient < 1 / 2 := by
      rw [setCoeff_one, Complex.natCast_re]
      have : 1 / 2 < 2 * ((S.filter IsUnit).card : ℝ) / q.totient := by
        rw [lt_div_iff₀ hφ]; linarith
      linarith
    have : a₀ < 1 / 2 := max_lt hlt (by norm_num)
    linarith
  set c : ℕ → ℝ := fun d => residueFlip q S d * (d : ℝ) ^ (-(1 / 2 : ℝ))
  have hc : DampedClass 1 (1 / 2) c := fun d => by
    simp only [c]
    rw [one_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _)
      (abs_residueFlip_le_one q S d)
  set P : ℝ := ∑' d : ℕ, c d / d
  obtain ⟨Z₀, hZ₀, hZ⟩ := exists_norm_zeta_le_on_tall_box 9
  have hAint : 0 ≤ 4 * Z₀ ^ 2 * (4 * A ^ 2 + 2 * P ^ 2) := by positivity
  set Aint := 4 * Z₀ ^ 2 * (4 * A ^ 2 + 2 * P ^ 2)
  have hwre : ∀ σ t : ℝ, ((σ : ℂ) + t * I + 1 / 2).re = σ + 1 / 2 := fun σ t => by simp
  have hwim : ∀ σ t : ℝ, ((σ : ℂ) + t * I + 1 / 2).im = t := fun σ t => by simp
  have hg : IntegrableOn (fun t : ℝ => Aint * (|t - 0| ^ (-(2 * a₀)) + 1)) (Ioc 0 9) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (((intervalIntegrable_abs_sub_rpow (by linarith) 0 0 9).add
        intervalIntegrable_const).const_mul Aint)
  have hsmall : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 → 0 < t → t ≤ 9 → t ≠ 0 →
      lineIntegrand c P σ t ≤ Aint * (|t - 0| ^ (-(2 * a₀)) + 1) := by
    intro σ t hσ hσ' ht htT _
    rw [sub_zero, abs_of_pos ht]
    have hF := (hbd ((σ : ℂ) + t * I + 1 / 2) (by rw [hwre]; linarith) (by rw [hwre]; linarith)).1
      (by rw [hwim, abs_of_pos ht]; exact ht) (by rw [hwim, abs_of_pos ht]; exact htT)
    rw [hwim, abs_of_pos ht] at hF
    have hC : ‖weightDirichletSeries c ((σ : ℂ) + t * I) - (P : ℂ)‖ ≤
        A * (t ^ (-a₀) + 1) + |P| := by
      rw [weightDirichletSeries_pattern]
      refine (norm_sub_le _ _).trans (add_le_add hF (by rw [Complex.norm_real, Real.norm_eq_abs]))
    have hpw : (t ^ (-a₀)) ^ 2 = t ^ (-(2 * a₀)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; congr 1; push_cast; ring
    have hX0 : 0 ≤ t ^ (-(2 * a₀)) := Real.rpow_nonneg ht.le _
    have hsq : ‖weightDirichletSeries c ((σ : ℂ) + t * I) - (P : ℂ)‖ ^ 2 ≤
        (4 * A ^ 2 + 2 * P ^ 2) * (t ^ (-(2 * a₀)) + 1) := by
      have h := pow_le_pow_left₀ (norm_nonneg _) hC 2
      have hab : ∀ x y : ℝ, (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := fun x y => by
        nlinarith [sq_nonneg (x - y)]
      have h1 : (A * (t ^ (-a₀) + 1)) ^ 2 ≤ 2 * A ^ 2 * (t ^ (-(2 * a₀)) + 1) := by
        rw [mul_pow]
        have := hab (t ^ (-a₀)) 1
        rw [hpw] at this
        nlinarith [sq_nonneg A]
      refine h.trans ((hab _ _).trans ?_)
      rw [sq_abs]
      nlinarith [sq_nonneg P]
    have hζs := hZ σ t hσ.le hσ'.le (by rw [abs_of_pos ht]; exact htT)
    have hsn : σ ≤ ‖(σ : ℂ) + t * I‖ := by
      have := Complex.abs_re_le_norm ((σ : ℂ) + t * I)
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero] at this
      linarith [le_abs_self σ]
    have hs2 : (1 / 2 : ℝ) ^ 2 ≤ ‖(σ : ℂ) + t * I‖ ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have hden : 0 < ‖(σ : ℂ) + t * I‖ ^ 2 := lt_of_lt_of_le (by norm_num) hs2
    have hzsq : ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 ≤ Z₀ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hζs 2
    simp only [lineIntegrand, norm_div, norm_mul, div_pow, mul_pow]
    rw [div_le_iff₀ hden]
    calc ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 *
          ‖weightDirichletSeries c ((σ : ℂ) + t * I) - (P : ℂ)‖ ^ 2
        ≤ Z₀ ^ 2 * ((4 * A ^ 2 + 2 * P ^ 2) * (t ^ (-(2 * a₀)) + 1)) :=
          mul_le_mul hzsq hsq (sq_nonneg _) (sq_nonneg _)
      _ = Aint * (t ^ (-(2 * a₀)) + 1) * (1 / 2) ^ 2 := by simp only [Aint]; ring
      _ ≤ Aint * (t ^ (-(2 * a₀)) + 1) * ‖(σ : ℂ) + t * I‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hs2 (mul_nonneg hAint (by positivity))
  have hlarge : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 → 9 < t →
      ‖weightDirichletSeries c ((σ : ℂ) + t * I) - (P : ℂ)‖ ≤ (|B₁| + |P|) * t ^ (1 / 4 : ℝ) := by
    intro σ t hσ hσ' ht
    have hF := (hbd ((σ : ℂ) + t * I + 1 / 2) (by rw [hwre]; linarith) (by rw [hwre]; linarith)).2
      (by rw [hwim, abs_of_pos (by linarith)]; linarith)
    rw [hwim, abs_of_pos (by linarith)] at hF
    rw [weightDirichletSeries_pattern]
    refine (norm_sub_le _ _).trans ?_
    have h1 : 1 ≤ t ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    rw [Complex.norm_real, Real.norm_eq_abs]
    nlinarith [le_abs_self B₁, abs_nonneg P, abs_nonneg B₁,
      mul_le_mul_of_nonneg_right (le_abs_self B₁) (by positivity : (0 : ℝ) ≤ t ^ (1 / 4 : ℝ))]
  obtain ⟨M, hM⟩ := exists_lineEnergy_le_of_majorant (c := c) (t₁ := 0) (by norm_num) hg hsmall
    hlarge
  exact ⟨3 * M / (4 * Real.pi), weightPronicEnergy_le_of_lineEnergy_le hc hM⟩

/-- **Symmetric residue flips above the quarter are paid.** If `S` is closed under inversion on the
units and more than a quarter of the unit classes are flipped, `f_{q,S}(d) d^{-1/2}` is paid. -/
theorem receiverBounded_residueFlip_half {q : ℕ} [NeZero q] {S : Finset (ZMod q)}
    (hS : UnitSymmetric S) (h4 : q.totient < 4 * (S.filter IsUnit).card) :
    ReceiverBounded (fun d => residueFlip q S d * (d : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨A, B₁, hA, hbd⟩ := exists_norm_residueFlip_bounds hS
  exact receiverBounded_residueFlip_half_of_bounds hA hbd h4

/-- **The quarter law of symmetric residue flips.** For `S ⊆ ZMod q` closed under inversion on the
units, the half-damped weight `f_{q,S}(d) d^{-1/2}` is paid iff more than a quarter of the unit
classes are flipped: `φ(q) < 4 #(S ∩ (ZMod q)ˣ)`. -/
theorem receiverBounded_residueFlip_half_iff {q : ℕ} [NeZero q] {S : Finset (ZMod q)}
    (hS : UnitSymmetric S) :
    ReceiverBounded (fun d => residueFlip q S d * (d : ℝ) ^ (-(1 / 2 : ℝ))) ↔
      q.totient < 4 * (S.filter IsUnit).card := by
  constructor
  · intro h
    by_contra h4
    exact not_receiverBounded_residueFlip_half_of_le S (not_lt.mp h4) h
  · exact receiverBounded_residueFlip_half hS

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
