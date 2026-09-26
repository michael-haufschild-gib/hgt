import GaloisForLFunctions.RHTower.HalfWeightDualEisenstein
import GaloisForLFunctions.RHTower.HalfWeightTwistedL

/-!
# Coefficients of the dual weight-½ Eisenstein series

For `ψ₀` mod a prime `q ∤ 4M'`, the `n`-th coefficient of `Ê = eisDual` is
`D̂_n(w) = i^{1/2}/√2 · q^{1/2-2w} μN_q(n) · L(ψ₀ g_L, 2w - 1/2)`   (`DserK_dual_eq`),
where `μN_q(n) = N_q(n) - 1` counts square roots of `n` mod `q` and `ψ₀ g_L = Btw ψ₀⁻¹` is the
`q`-free part of the coefficients of `E*_ψ` with `ψ₀` replaced by `ψ₀⁻¹`. The exact power `q¹ ∥ c`
of the dual rows produces `q^{1/2-2w} μN_q(n)`, where the rows `q² ∣ c` of `E*_ψ` produce `L(Q, s)/τ(ψ₀)`.

* `DserK_dual_zero`: `D̂_0 = 0` (`μN_q(0) = 0`), so `Ê` has no constant term at `∞`.
* `Dhst`, `Dhst_eq`: the regularised coefficients
  `D̂*_n(w) = i^{1/2}/√2 · q^{1/2-2w} μN_q(n) · L(2w - 1/2, ψ₀χ_n) · L(ψ₀ e_L, 2w - 1/2) / ∏_{p ∣ qk}(1 - ψ₀²(p)p^{1-4w})`
  equal `L(4w-1, ψ₀²) D̂_n(w)` for `Re w > 3/4`.
* `differentiableAt_Dhst`: holomorphic on `Re w > 1/4`; `exists_bound_Dhst`: `‖D̂*_n(w)‖ ≤ C|n|^e` on
  closed balls there, with the exponent of `D*_n`.
-/

open Complex ArithmeticFunction
open scoped Real

namespace GaloisForLFunctions.RHTower.HalfWeight

noncomputable section

section DualCoefficients

variable {q : ℕ} [hq : Fact q.Prime] (ψ₀ : DirichletCharacter ℂ q)

theorem conjA_inv_apply (c : ℕ) : conjA ψ₀⁻¹ c = if c = 0 then 0 else ψ₀ c := by
  unfold conjA
  simp only [ArithmeticFunction.coe_mk]
  split_ifs with hc
  · rfl
  · rw [← MulChar.star_apply' ψ₀]
    exact star_star _

theorem kapQ_q_mul (c : ℕ) : kapQ ψ₀ ((q * c : ℕ) : ℤ) = ψ₀ c := by
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  unfold kapQ
  rw [if_pos ⟨c, by push_cast; ring⟩]
  push_cast
  rw [Int.mul_ediv_cancel_left _ hq0]
  simp

/-- **The dual coefficients as an `L`-series**: for `q ∤ 4M'`,
`D̂_n(w) = i^{1/2}/√2 · q^{1/2-2w} μN_q(n) · L(ψ₀ g_L, 2w - 1/2)`, where `μN_q(n) = N_q(n) - 1` and
`ψ₀ g_L = conjA ψ₀⁻¹ · g_L` is the `q`-free part `Btw ψ₀⁻¹` with the conjugate character. -/
theorem DserK_dual_eq (n : ℤ) (M' : ℕ) (hcop : q.Coprime (4 * M')) (w : ℂ) :
    DserK (M' * q) (kapQ ψ₀) n w = I ^ (1 / 2 : ℂ) / Real.sqrt 2 *
      ((q : ℂ) ^ (1 / 2 - 2 * w) * muN n q) *
        LSeries (fun c => Btw ψ₀⁻¹ n M' c) (2 * w - 1 / 2) := by
  rw [DserK_eq, mul_assoc]
  congr 1
  have hq1 := hq.out.one_lt
  set g : ℕ → ℕ := fun c => q * c - 1 with hg
  have hginj : Function.Injective g := by
    intro a b h
    simp only [hg] at h
    rcases Nat.eq_zero_or_pos a with ha | ha <;> rcases Nat.eq_zero_or_pos b with hb | hb
    · omega
    · subst ha; have : 1 ≤ q * b := Nat.one_le_iff_ne_zero.2 (by positivity); simp at h
      have : q * b ≥ q := Nat.le_mul_of_pos_right q hb; omega
    · subst hb; have : q * a ≥ q := Nat.le_mul_of_pos_right q ha; simp at h; omega
    · have h1 : q * a ≥ 1 := by nlinarith
      have h2 : q * b ≥ 1 := by nlinarith
      have : q * a = q * b := by omega
      exact Nat.eq_of_mul_eq_mul_left hq.out.pos this
  set F : ℕ → ℂ := fun k => if 4 * (M' * q) ∣ k + 1 then kapQ ψ₀ ((k + 1 : ℕ) : ℤ) *
    ((k + 1 : ℕ) : ℂ) ^ (1 / 2 - 2 * w) * muN n (k + 1) else 0 with hF
  have hsupp : Function.support F ⊆ Set.range g := by
    intro k hk
    rw [Function.mem_support] at hk
    simp only [hF] at hk
    split_ifs at hk with h4
    swap
    · exact absurd rfl hk
    obtain ⟨m, hm⟩ := h4
    exact ⟨4 * M' * m, by simp only [hg]; rw [show q * (4 * M' * m) = 4 * (M' * q) * m by ring, ← hm]; omega⟩
  change ∑' k, F k = _
  rw [← hginj.tsum_eq hsupp]
  unfold LSeries
  rw [← tsum_mul_left]
  refine tsum_congr fun c => ?_
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    have hF0 : F (g 0) = 0 := by
      simp only [hF, hg, mul_zero, Nat.zero_sub, zero_add]
      rw [if_neg]
      intro h
      have := Nat.le_of_dvd one_pos h
      have : 4 ≤ 4 * (M' * q) := by
        have : 1 ≤ M' * q := by
          rcases Nat.eq_zero_or_pos M' with h0 | h0
          · subst h0; simp at h
          · nlinarith
        omega
      omega
    rw [hF0, LSeries.term_zero, mul_zero]
  · have hk : g c + 1 = q * c := by simp only [hg]; have : q * c ≥ 1 := by nlinarith
                                    omega
    simp only [hF, hk]
    rw [LSeries.term_of_ne_zero hc.ne']
    have h4iff : 4 * (M' * q) ∣ q * c ↔ 4 * M' ∣ c := by
      constructor
      · intro h
        rw [show 4 * (M' * q) = q * (4 * M') by ring] at h
        exact Nat.dvd_of_mul_dvd_mul_left hq.out.pos h
      · intro h
        rw [show 4 * (M' * q) = q * (4 * M') by ring]
        exact Nat.mul_dvd_mul_left q h
    rw [Btw, ArithmeticFunction.pmul_apply, conjA_inv_apply, if_neg hc.ne', gL_apply, fN_apply]
    by_cases h4 : 4 * M' ∣ c
    · rw [if_pos (h4iff.2 h4), if_pos h4, kapQ_q_mul]
      by_cases hqc : q ∣ c
      · have hz : ψ₀ (c : ZMod q) = 0 := by
          rw [(ZMod.natCast_eq_zero_iff c q).2 hqc]; exact MulChar.map_zero ψ₀
        rw [hz]; simp
      · have hcop' : q.Coprime c := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hq.out).2 hqc)).symm
        rw [muN_mul_of_coprime n hcop']
        have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
        have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
        rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
        have hP : (c : ℂ) ^ (2 * w - 1 / 2) ≠ 0 := by
          rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h; exact absurd h hc0
        have hsplit : (c : ℂ) ^ (1 / 2 - 2 * w) = ((c : ℂ) ^ (2 * w - 1 / 2))⁻¹ := by
          rw [← Complex.cpow_neg]; congr 1; ring
        rw [hsplit]
        field_simp
    · rw [if_neg (fun h => h4 (h4iff.1 h)), if_neg h4]; simp

/-- `μN_q(0) = 0`: the constant coefficient of the dual series vanishes. -/
theorem muN_zero_prime : muN 0 q = 0 := by
  have h := muN_prime_pow 0 hq.out (i := 1) le_rfl
  rw [pow_one, pow_zero] at h
  rw [h]
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  have h1 : sqCount 0 q = 1 := by
    rw [sqCount_eq_rootCard]
    unfold rootCard
    have : (Finset.univ.filter fun x : ZMod q => x ^ 2 = ((0 : ℤ) : ZMod q)) = {0} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Int.cast_zero]
      exact pow_eq_zero_iff two_ne_zero
    rw [this]; simp
  have h0 : sqCount 0 1 = 1 := sqCount_one 0
  rw [h1, h0, sub_self]

theorem DserK_dual_zero (M' : ℕ) (hcop : q.Coprime (4 * M')) (w : ℂ) :
    DserK (M' * q) (kapQ ψ₀) 0 w = 0 := by
  rw [DserK_dual_eq ψ₀ 0 M' hcop w, muN_zero_prime]
  ring

variable {n : ℤ} {M' : ℕ} (hn : n ≠ 0) (hM : 0 < M')

theorem LSeries_Btw {s : ℂ} (hs : 1 < s.re) :
    haveI : NeZero (kmod n M') := ⟨(kmod_pos hn hM).ne'⟩
    LSeries (fun c => Btw ψ₀ n M' c) s =
      (DirichletCharacter.LFunction (chiTw ψ₀ hn hM) s /
        DirichletCharacter.LFunction (chiTw ψ₀ hn hM ^ 2) (2 * s)) *
        LSeries (fun c => eLtw ψ₀ (n := n) (M' := M') c) s := by
  haveI : NeZero (kmod n M') := ⟨(kmod_pos hn hM).ne'⟩
  have h0 : 0 < s.re := by linarith
  have hS := lseriesSummable_of_norm_le_one (norm_sqfG_le (chiTw ψ₀ hn hM)) hs
  have hE := lseriesSummable_eLtw ψ₀ hn (M' := M') h0
  rw [Btw_eq_mul ψ₀ hn hM, LSeries_mul' hS hE, LSeries_sqfG _ hs]

/-- **The regularised dual coefficients** `D̂*_n(w) = L(4w-1, ψ₀²) D̂_n(w)`:
`i^{1/2}/√2 · q^{1/2-2w} μN_q(n) · L(2w-1/2, ψ₀ χ_n) · L(ψ₀ e_L, 2w-1/2) / ∏_{p ∣ qk}(1 - ψ₀²(p)p^{1-4w})`. -/
def Dhst (w : ℂ) : ℂ :=
  haveI : NeZero (kmod n M') := ⟨(kmod_pos hn hM).ne'⟩
  I ^ (1 / 2 : ℂ) / Real.sqrt 2 * ((q : ℂ) ^ (1 / 2 - 2 * w) * muN n q) *
    DirichletCharacter.LFunction (chiTw ψ₀⁻¹ hn hM) (2 * w - 1 / 2) *
    LSeries (fun c => eLtw ψ₀⁻¹ (n := n) (M' := M') c) (2 * w - 1 / 2) *
    (eulerTw ψ₀⁻¹ (q * kmod n M') (4 * w - 1))⁻¹

/-- **`D̂*_n = L(4w-1, ψ₀²) D̂_n`** on `Re w > 3/4`. -/
theorem Dhst_eq (h2 : ψ₀ ^ 2 ≠ 1) (hcop : q.Coprime (4 * M')) {w : ℂ} (hw : 3 / 4 < w.re) :
    Dhst ψ₀ hn hM w = DirichletCharacter.LFunction (ψ₀⁻¹⁻¹ ^ 2) (4 * w - 1) *
      DserK (M' * q) (kapQ ψ₀) n w := by
  haveI : NeZero (kmod n M') := ⟨(kmod_pos hn hM).ne'⟩
  have hs : 1 < (2 * w - 1 / 2).re := by simp; linarith
  have h2' := inv_sq_ne_one ψ₀ h2
  rw [DserK_dual_eq ψ₀ n M' hcop w, LSeries_Btw ψ₀⁻¹ hn hM hs,
    show 2 * (2 * w - 1 / 2) = 4 * w - 1 by ring, LFunction_chiTw_sq ψ₀⁻¹ hn hM h2']
  have hL : DirichletCharacter.LFunction (ψ₀⁻¹⁻¹ ^ 2) (4 * w - 1) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (Or.inl (inv_sq_ne_one ψ₀⁻¹ h2'))
      (by simp; linarith)
  have hE := eulerTw_ne_zero ψ₀⁻¹ (q * kmod n M') (u := 4 * w - 1) (by simp; linarith)
  unfold Dhst
  set L := DirichletCharacter.LFunction (ψ₀⁻¹⁻¹ ^ 2) (4 * w - 1)
  set E := eulerTw ψ₀⁻¹ (q * kmod n M') (4 * w - 1)
  set B := DirichletCharacter.LFunction (chiTw ψ₀⁻¹ hn hM) (2 * w - 1 / 2)
  set C := LSeries (fun c => eLtw ψ₀⁻¹ (n := n) (M' := M') c) (2 * w - 1 / 2)
  field_simp

/-- **Holomorphy of `D̂*_n`** on `Re w > 1/4`. -/
theorem differentiableAt_Dhst (h2 : ψ₀ ^ 2 ≠ 1) {w₀ : ℂ} (hw : 1 / 4 < w₀.re) :
    DifferentiableAt ℂ (Dhst ψ₀ hn hM) w₀ := by
  haveI : NeZero (kmod n M') := ⟨(kmod_pos hn hM).ne'⟩
  haveI : NeZero (q * kmod n M') := ⟨mul_ne_zero hq.out.ne_zero (kmod_pos hn hM).ne'⟩
  have h2' := inv_sq_ne_one ψ₀ h2
  have hs : 0 < (2 * w₀ - 1 / 2).re := by simp; linarith
  have hu : 0 < (4 * w₀ - 1).re := by simp; linarith
  have hlin : ∀ a b : ℂ, DifferentiableAt ℂ (fun w : ℂ => a * w - b) w₀ := fun a b =>
    (differentiableAt_id.const_mul a).sub_const b
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hQ : DifferentiableAt ℂ (fun w : ℂ => (q : ℂ) ^ (1 / 2 - 2 * w) * muN n q) w₀ := by
    refine DifferentiableAt.mul_const ?_ _
    exact ((differentiableAt_const _).sub (differentiableAt_id.const_mul 2)).const_cpow (Or.inl hq0)
  have hL0 : DifferentiableAt ℂ (DirichletCharacter.LFunction (chiTw ψ₀⁻¹ hn hM)) (2 * w₀ - 1 / 2) :=
    DirichletCharacter.differentiable_LFunction (chiTw_ne_one ψ₀⁻¹ hn hM h2') _
  have hL := hL0.comp w₀ (hlin 2 (1 / 2))
  have hE0 : DifferentiableAt ℂ (LSeries (fun c => eLtw ψ₀⁻¹ (n := n) (M' := M') c)) (2 * w₀ - 1 / 2) :=
    differentiableAt_LSeries_of_summable (fun s hs => lseriesSummable_eLtw ψ₀⁻¹ hn hs) hs
  have hE := hE0.comp w₀ (hlin 2 (1 / 2))
  have hEu : DifferentiableAt ℂ (fun w => (eulerTw ψ₀⁻¹ (q * kmod n M') (4 * w - 1))⁻¹) w₀ :=
    ((differentiable_eulerTw ψ₀⁻¹ _ _).comp w₀ (hlin 4 1)).inv (eulerTw_ne_zero ψ₀⁻¹ _ hu)
  unfold Dhst
  exact ((((differentiableAt_const _).mul hQ).mul hL).mul hE).mul hEu

include hn in
theorem norm_muN_prime_le : ‖muN n q‖ ≤ 16 * n.natAbs := by
  have h := muN_prime_pow n hq.out (i := 1) le_rfl
  rw [pow_one, pow_zero] at h
  rw [h]
  refine (norm_sub_le _ _).trans ?_
  have h1 := norm_sqCount_prime_pow_le hn hq.out 1
  have h0 := norm_sqCount_prime_pow_le hn hq.out 0
  rw [pow_one] at h1; rw [pow_zero] at h0
  linarith

/-- **Uniform polynomial bound for the regularised dual coefficients** on a closed ball in
`Re w > 1/4`: `‖D̂*_n(w)‖ ≤ C |n|^{e}` with the exponent of `D*_n`. -/
theorem exists_bound_Dhst (h2 : ψ₀ ^ 2 ≠ 1) {M' : ℕ} (hM : 0 < M') {w₀ : ℂ} {r : ℝ}
    (h1 : 1 / 4 < w₀.re - r) :
    ∃ C, 0 ≤ C ∧ ∀ w ∈ Metric.closedBall w₀ r, ∀ n : ℤ, ∀ hn : n ≠ 0,
      ‖Dhst ψ₀ hn hM w‖ ≤ C * |(n : ℝ)| ^ expTw (w₀.re - r) := by
  have h2' := inv_sq_ne_one ψ₀ h2
  set τ₁ := w₀.re - r
  set σ₁ := 2 * τ₁ - 1 / 2
  set σ₁' := 4 * τ₁ - 1
  have hσ₁ : 0 < σ₁ := by simp only [σ₁]; linarith
  have hσ₁' : 0 < σ₁' := by simp only [σ₁']; linarith
  set E := expTw τ₁
  have hE0 : 0 ≤ E := expTw_nonneg h1
  set R : ℝ := 2 * (‖w₀‖ + |r|) + 9 / 2
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.out.one_lt
  have hC := stripC_pos
  set C₀ : ℝ := 1 / Real.sqrt 2 * 4 * (stripC * (q : ℝ) ^ 3 * R ^ 3 + 2) * (q : ℝ) ^ gammaE σ₁'
  have hC₀ : 0 ≤ C₀ := by positivity
  refine ⟨C₀ * (4 * M' : ℝ) ^ E, by positivity, fun w hw n hn => ?_⟩
  haveI : NeZero (kmod n M') := ⟨(kmod_pos hn hM).ne'⟩
  obtain ⟨hre1, _⟩ := re_ge_of_mem_closedBall hw
  set k : ℝ := (kmod n M' : ℝ)
  have hk := kmod_one_le hn hM
  have hk0 : 0 < k := by linarith
  have hk4 : (4 * n.natAbs : ℝ) ≤ k := by
    simp only [k, kmod]; push_cast
    have : (1 : ℝ) ≤ M' := by exact_mod_cast hM
    nlinarith [(Nat.cast_nonneg n.natAbs : (0 : ℝ) ≤ n.natAbs)]
  have hsre : (2 * w - 1 / 2).re = 2 * w.re - 1 / 2 := by simp
  have hure : (4 * w - 1).re = 4 * w.re - 1 := by simp
  have hs0 : 0 < (2 * w - 1 / 2).re := by rw [hsre]; linarith
  -- the `q`-factor
  have hqpow : ‖(q : ℂ) ^ (1 / 2 - 2 * w)‖ ≤ 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hq.out.pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos hq1.le
    simp; linarith
  have hA' : ‖(q : ℂ) ^ (1 / 2 - 2 * w) * muN n q‖ ≤ 4 * k := by
    rw [norm_mul]
    have := norm_muN_prime_le (q := q) hn
    calc _ ≤ (1 : ℝ) * (16 * (n.natAbs : ℝ)) := mul_le_mul hqpow this (norm_nonneg _) zero_le_one
      _ ≤ 4 * k := by nlinarith
  have hB := norm_LFunction_chiTw_le ψ₀⁻¹ hn hM h2' (s := 2 * w - 1 / 2) hs0.le
  have hsR : ‖2 * w - 1 / 2 - 4‖ ≤ R := by
    have := norm_le_of_mem_closedBall hw (-9 / 4)
    calc ‖2 * w - 1 / 2 - 4‖ = 2 * ‖w + (-9 / 4)‖ := by
          rw [show 2 * w - 1 / 2 - 4 = 2 * (w + (-9 / 4)) by ring, norm_mul]; norm_num
      _ ≤ 2 * (‖w₀‖ + |r| + ‖(-9 / 4 : ℂ)‖) := by linarith [le_abs_self r]
      _ = R := by simp only [R]; norm_num; ring
  have hB' : ‖DirichletCharacter.LFunction (chiTw ψ₀⁻¹ hn hM) (2 * w - 1 / 2)‖ ≤
      (stripC * (q : ℝ) ^ 3 * R ^ 3 + 2) * k ^ 3 :=
    hB.trans (mul_le_mul_of_nonneg_right (by gcongr) (by positivity))
  have hEL := norm_LSeries_eLtw_le ψ₀⁻¹ hn hM (s := 2 * w - 1 / 2) hs0
  rw [hsre] at hEL
  have hβ : betaE (2 * w.re - 1 / 2) ≤ betaE σ₁ := betaE_anti hσ₁ (by simp only [σ₁]; linarith)
  have hEL' : ‖LSeries (fun c => eLtw ψ₀⁻¹ (n := n) (M' := M') c) (2 * w - 1 / 2)‖ ≤
      k * k ^ betaE σ₁ :=
    hEL.trans (mul_le_mul hk4 (Real.rpow_le_rpow_of_exponent_le hk hβ) (by positivity) (by positivity))
  haveI : NeZero (q * kmod n M') := ⟨mul_ne_zero hq.out.ne_zero (kmod_pos hn hM).ne'⟩
  have hD := norm_eulerTw_inv_le ψ₀⁻¹ (N := q * kmod n M') (NeZero.ne _) (u := 4 * w - 1)
    (by rw [hure]; linarith)
  rw [hure] at hD
  have hγ : gammaE (4 * w.re - 1) ≤ gammaE σ₁' := gammaE_anti hσ₁' (by simp only [σ₁']; linarith)
  have hqk : (1 : ℝ) ≤ ((q * kmod n M' : ℕ) : ℝ) := by
    have : 1 ≤ q * kmod n M' := Nat.one_le_iff_ne_zero.2 (NeZero.ne _)
    exact_mod_cast this
  have hD' : ‖(eulerTw ψ₀⁻¹ (q * kmod n M') (4 * w - 1))⁻¹‖ ≤
      (q : ℝ) ^ gammaE σ₁' * k ^ gammaE σ₁' := by
    refine hD.trans ((Real.rpow_le_rpow_of_exponent_le hqk hγ).trans (le_of_eq ?_))
    rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
  have hnorm : ‖Dhst ψ₀ hn hM w‖ = 1 / Real.sqrt 2 *
      ‖(q : ℂ) ^ (1 / 2 - 2 * w) * muN n q‖ *
      ‖DirichletCharacter.LFunction (chiTw ψ₀⁻¹ hn hM) (2 * w - 1 / 2)‖ *
      ‖LSeries (fun c => eLtw ψ₀⁻¹ (n := n) (M' := M') c) (2 * w - 1 / 2)‖ *
      ‖(eulerTw ψ₀⁻¹ (q * kmod n M') (4 * w - 1))⁻¹‖ := by
    unfold Dhst
    simp only [norm_mul, norm_div, norm_I_cpow_half, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
  have hkE : k ^ (1 : ℝ) * k ^ (3 : ℝ) * (k * k ^ betaE σ₁) * k ^ gammaE σ₁' = k ^ E := by
    simp only [E, expTw]
    rw [show (5 : ℝ) + gammaE (4 * τ₁ - 1) + betaE (2 * τ₁ - 1 / 2) =
      1 + 3 + 1 + betaE σ₁ + gammaE σ₁' by simp only [σ₁, σ₁']; ring]
    rw [Real.rpow_add hk0, Real.rpow_add hk0, Real.rpow_add hk0, Real.rpow_add hk0, Real.rpow_one]
    ring
  have hkn' : k ^ E = (4 * M' : ℝ) ^ E * |(n : ℝ)| ^ E := by
    rw [← Real.mul_rpow (by positivity) (abs_nonneg _)]
    congr 1
    simp only [k, kmod]; push_cast; rw [Nat.cast_natAbs, Int.cast_abs]; ring
  rw [hnorm]
  calc 1 / Real.sqrt 2 * ‖(q : ℂ) ^ (1 / 2 - 2 * w) * muN n q‖ *
        ‖DirichletCharacter.LFunction (chiTw ψ₀⁻¹ hn hM) (2 * w - 1 / 2)‖ *
        ‖LSeries (fun c => eLtw ψ₀⁻¹ (n := n) (M' := M') c) (2 * w - 1 / 2)‖ *
        ‖(eulerTw ψ₀⁻¹ (q * kmod n M') (4 * w - 1))⁻¹‖
      ≤ 1 / Real.sqrt 2 * (4 * k) *
          ((stripC * (q : ℝ) ^ 3 * R ^ 3 + 2) * k ^ 3) * (k * k ^ betaE σ₁) *
          ((q : ℝ) ^ gammaE σ₁' * k ^ gammaE σ₁') := by
        gcongr
    _ = C₀ * (k ^ (1 : ℝ) * k ^ (3 : ℝ) * (k * k ^ betaE σ₁) * k ^ gammaE σ₁') := by
        simp only [C₀]
        rw [Real.rpow_one, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        ring
    _ = C₀ * (4 * M' : ℝ) ^ E * |(n : ℝ)| ^ E := by rw [hkE, hkn']; ring

end DualCoefficients

end

end GaloisForLFunctions.RHTower.HalfWeight
