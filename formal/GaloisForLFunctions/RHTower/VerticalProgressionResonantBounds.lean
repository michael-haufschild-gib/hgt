import GaloisForLFunctions.RHTower.VerticalProgressionFarey

/-!
# Bounds for resonant and large ratios

* **Decay sums** (`sum_decay_le`): quadruples with `mn ≥ X` contribute
  `≤ 4N (T+1) Ψ₀ K (3αT/2π)^A X^{−(A−1)} Σ(mn)^{−3/2}` (rapid decay of `V`).
* **Large ratios** (`pairProd_ge_of_huge`): a quadruple of ratio `a/b` has `mn ≥ ab/N²`.
* **The crude ratio-form bound** (`norm_ratioForm_le_crude`):
  `‖F(a,b,t)‖ ≤ C₀ (1 + log⁺ t) Σ_{h,k}(ha,kb)/(hk)`, from `‖𝓗(x)‖ ≤ C₀(1 + log⁺ x)` and
  `x_{hk}(t) ≤ t`.
* **Fibre terms** (`norm_fiberTerm_le`): `‖Φ_T(a,b)‖ ≤ (T+1) Ψ₀ (ab)^{−1/2} sup_t ‖F(a,b,t)‖`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower.VerticalAP

noncomputable section

open ZetaNotch (pairAmp pairFreq pairProd)

/-! ## Decay sums -/

/-- **Quadruples with `mn ≥ X`.** -/
theorem sum_decay_le {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2) {Ψ₀ : ℝ}
    (hΨ : ∀ y, |ψ y| ≤ Ψ₀) {α β : ℝ} (hα : 0 < α) {A : ℝ} (hA : 1 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) {T : ℝ}, 0 < T → 2 * |β| ≤ α * T →
      ∀ (S : ℕ → ℕ → Set (ℕ × ℕ)) {X : ℝ}, 0 < X →
      (∀ h ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N, ∀ P ∈ S h k, X ≤ pairProd P) →
      ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, ∑' P : ℕ × ℕ,
        (S h k).indicator (fun P => ‖quadTerm ψ α β N T P h k‖) P ≤
        4 * N * (((T + 1) * (Ψ₀ * (K * (3 * α * T / (2 * Real.pi)) ^ A)) * X ^ (-(A - 1))) *
          pairSum) := by
  obtain ⟨K, hK, hdec⟩ := exists_norm_latticeSum_cutoff_le_decay (by linarith : (0 : ℝ) < A)
  refine ⟨K, hK, fun N {T} hT hβ S {X} hX hSX => ?_⟩
  have hΨ0 : 0 ≤ Ψ₀ := (abs_nonneg _).trans (hΨ 0)
  have hsuppC := complex_support_subset hsupp
  have hΨC : ∀ y, ‖(ψ y : ℂ)‖ ≤ Ψ₀ := fun y => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hΨ y
  set B : ℝ := (T + 1) * (Ψ₀ * (K * (3 * α * T / (2 * Real.pi)) ^ A)) * X ^ (-(A - 1))
  have hB : 0 ≤ B := by positivity
  refine sum_quadruple_le (S := S) (f := fun P h k => ‖quadTerm ψ α β N T P h k‖) hB
    (fun h hh k hk P hP => ?_) (fun _ _ _ => norm_nonneg _)
  have hXP := hSX h hh k hk P hP
  have hprod := ZetaNotch.pairProd_pos P
  have hl := hdec hsuppC hΨC hα hT hβ (c := 2 * Real.pi * pairProd P) (by positivity)
    (α * quadFreq P h k / (2 * Real.pi))
  rw [norm_quadTerm_eq]
  have h0 : 0 ≤ |mollAmp N h| * |mollAmp N k| * pairAmp P := by
    have := (ZetaNotch.pairAmp_pos P).le; positivity
  refine mul_le_mul_of_nonneg_left (hl.trans ?_) h0
  have hsplit : (3 * α * T / (2 * Real.pi * pairProd P)) ^ A =
      (3 * α * T / (2 * Real.pi)) ^ A * (pairProd P ^ (-(A - 1)) * pairProd P ^ (-(1 : ℝ))) := by
    rw [← Real.rpow_add hprod, show -(A - 1) + -(1 : ℝ) = -A by ring, Real.rpow_neg hprod.le,
      ← div_eq_mul_inv, ← Real.div_rpow (by positivity) hprod.le, div_div]
  have hpow : pairProd P ^ (-(A - 1)) ≤ X ^ (-(A - 1)) :=
    Real.rpow_le_rpow_of_nonpos hX hXP (by linarith)
  rw [hsplit]
  have hr1 : 0 ≤ pairProd P ^ (-(1 : ℝ)) := Real.rpow_nonneg hprod.le _
  calc (T + 1) * (Ψ₀ * (K * ((3 * α * T / (2 * Real.pi)) ^ A *
        (pairProd P ^ (-(A - 1)) * pairProd P ^ (-(1 : ℝ))))))
      ≤ (T + 1) * (Ψ₀ * (K * ((3 * α * T / (2 * Real.pi)) ^ A *
          (X ^ (-(A - 1)) * pairProd P ^ (-(1 : ℝ)))))) := by gcongr
    _ = B * pairProd P ^ (-(1 : ℝ)) := by ring

/-! ## Large ratios -/

/-- The ratios with `ab > Z`. -/
def hugeRatio (Z : ℝ) : Set (ℕ × ℕ) := {c | Z < (c.1 : ℝ) * c.2}

/-- **A quadruple of ratio `a/b` has `mn ≥ ab/N²`.** -/
theorem pairProd_ge_of_huge {P : ℕ × ℕ} {h k N : ℕ} (hh : h ∈ Finset.Icc 1 N)
    (hk : k ∈ Finset.Icc 1 N) {Z : ℝ}
    (hc : Z < ((quadRatio P h k).1 : ℝ) * (quadRatio P h k).2) : Z / (N : ℝ) ^ 2 ≤ pairProd P := by
  obtain ⟨hh1, hhN⟩ := Finset.mem_Icc.mp hh
  obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
  have h1 : (quadRatio P h k).1 ≤ (P.2 + 1) * k := Nat.div_le_self _ _
  have h2 : (quadRatio P h k).2 ≤ (P.1 + 1) * h := Nat.div_le_self _ _
  have hle : ((quadRatio P h k).1 : ℝ) * (quadRatio P h k).2 ≤ pairProd P * (N : ℝ) ^ 2 := by
    have e1 : ((quadRatio P h k).1 : ℝ) ≤ ((P.2 : ℝ) + 1) * k := by exact_mod_cast h1
    have e2 : ((quadRatio P h k).2 : ℝ) ≤ ((P.1 : ℝ) + 1) * h := by exact_mod_cast h2
    have e3 : (h : ℝ) ≤ N := by exact_mod_cast hhN
    have e4 : (k : ℝ) ≤ N := by exact_mod_cast hkN
    have e5 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
    have e6 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have e7 : (0 : ℝ) ≤ (P.1 : ℝ) + 1 := by positivity
    have e8 : (0 : ℝ) ≤ (P.2 : ℝ) + 1 := by positivity
    calc ((quadRatio P h k).1 : ℝ) * (quadRatio P h k).2
        ≤ (((P.2 : ℝ) + 1) * k) * (((P.1 : ℝ) + 1) * h) :=
          mul_le_mul e1 e2 (Nat.cast_nonneg _) (by positivity)
      _ = pairProd P * ((h : ℝ) * k) := by unfold pairProd; ring
      _ ≤ pairProd P * (N : ℝ) ^ 2 := by
          gcongr
          · exact (ZetaNotch.pairProd_pos P).le
          · nlinarith
  have hN : (0 : ℝ) < (N : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast le_trans hh1 hhN
    positivity
  rw [div_le_iff₀ hN]
  linarith

/-! ## The crude ratio-form bound -/

theorem exists_norm_diagHarm_le :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ x : ℝ, 0 < x → ‖ZetaNotch.diagHarm x‖ ≤ C₀ * (1 + max 0 (Real.log x)) := by
  obtain ⟨C, hC0, hC⟩ := ZetaNotch.exists_norm_diagHarm_sub_le
  obtain ⟨K, hK, hV⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 1) one_pos
  have hs3 : Summable (fun s : ℕ => ((s : ℝ) + 1) ^ (-(3 : ℝ))) := by
    have := (Real.summable_nat_rpow.mpr (by norm_num : -(3 : ℝ) < -1)).comp_injective
      (add_left_injective 1)
    simpa [Function.comp_def] using this
  set Z3 : ℝ := ∑' s : ℕ, ((s : ℝ) + 1) ^ (-(3 : ℝ))
  have hZ3 : 0 ≤ Z3 := tsum_nonneg fun s => by positivity
  refine ⟨C + 1 + K * Z3, by positivity, fun x hx => ?_⟩
  by_cases hx1 : 1 ≤ x
  · have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
    rw [max_eq_right hl]
    have h := hC x hx
    have hrp : x ^ (-(1 / 4) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
    have hγ : Real.eulerMascheroniConstant ≤ 1 := by
      linarith [Real.eulerMascheroniConstant_lt_two_thirds]
    have hγ0 : 0 ≤ Real.eulerMascheroniConstant := by
      linarith [Real.one_half_lt_eulerMascheroniConstant]
    have hmain : ‖((Real.log x : ℂ) / 2 + Real.eulerMascheroniConstant)‖ ≤ Real.log x / 2 + 1 := by
      rw [show ((Real.log x : ℂ) / 2 + Real.eulerMascheroniConstant) =
        ((Real.log x / 2 + Real.eulerMascheroniConstant : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith
    calc ‖ZetaNotch.diagHarm x‖ ≤ ‖ZetaNotch.diagHarm x -
          ((Real.log x : ℂ) / 2 + Real.eulerMascheroniConstant)‖ +
            ‖((Real.log x : ℂ) / 2 + Real.eulerMascheroniConstant)‖ := norm_le_norm_sub_add _ _
      _ ≤ C * 1 + (Real.log x / 2 + 1) := add_le_add (h.trans (by gcongr)) hmain
      _ ≤ (C + 1 + K * Z3) * (1 + Real.log x) := by
          nlinarith [mul_nonneg hC0 hl, mul_nonneg (mul_nonneg hK hZ3) hl, mul_nonneg hK hZ3]
  · push Not at hx1
    have hterm : ∀ s : ℕ, ‖(((s : ℝ) + 1)⁻¹ : ℂ) * smoothAFECutoff (((s : ℝ) + 1) ^ 2 / x)‖ ≤
        K * x * ((s : ℝ) + 1) ^ (-(3 : ℝ)) := by
      intro s
      have hs : (0 : ℝ) < (s : ℝ) + 1 := by positivity
      rw [norm_mul, ZetaNotch.norm_inv_natCast_add_one]
      have hv := hV (div_pos (pow_pos hs 2) hx)
      rw [Real.rpow_neg_one, inv_div] at hv
      calc ((s : ℝ) + 1)⁻¹ * ‖smoothAFECutoff (((s : ℝ) + 1) ^ 2 / x)‖
          ≤ ((s : ℝ) + 1)⁻¹ * (K * (x / ((s : ℝ) + 1) ^ 2)) := by gcongr
        _ = K * x * ((s : ℝ) + 1) ^ (-(3 : ℝ)) := by
            rw [Real.rpow_neg hs.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            field_simp
    have hsum : Summable (fun s : ℕ => K * x * ((s : ℝ) + 1) ^ (-(3 : ℝ))) := hs3.mul_left _
    unfold ZetaNotch.diagHarm
    refine (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsum)).trans ?_
    refine (Summable.tsum_le_tsum hterm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsum) hsum).trans ?_
    rw [tsum_mul_left]
    have hlog : max 0 (Real.log x) = 0 := max_eq_left (Real.log_nonpos hx.le hx1.le)
    rw [hlog]
    nlinarith [hx.le, mul_nonneg hK hZ3, mul_le_mul_of_nonneg_left hx1.le (mul_nonneg hK hZ3)]

theorem abs_ratioWeight_le {N a b h k : ℕ} (hh : h ∈ Finset.Icc 1 N) (hk : k ∈ Finset.Icc 1 N)
    (ha : 0 < a) :
    |ratioWeight N a b h k| ≤ ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) / ((h : ℝ) * k) := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast (Finset.mem_Icc.mp hh).1
  have hkR : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
  have hg := gcd_mul_pos (b := b) (k := k) ha (Finset.mem_Icc.mp hh).1
  unfold ratioWeight
  rw [abs_div, abs_mul, abs_mul, abs_of_pos hg, abs_of_pos (mul_pos hhR hkR)]
  have h1 := abs_linearMollifierCoeff_le_one hh
  have h2 := abs_linearMollifierCoeff_le_one hk
  gcongr
  calc |Sieve.linearMollifierCoeff N h| * |Sieve.linearMollifierCoeff N k| *
        ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ)
      ≤ 1 * 1 * ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) := by gcongr
    _ = _ := by ring

theorem ratioArg_le {a b h k : ℕ} (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) (hk : 0 < k) {t : ℝ}
    (ht : 0 < t) : ratioArg a b h k t ≤ t := by
  have hg1 : ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) ≤ (h : ℝ) * a := by
    exact_mod_cast Nat.gcd_le_left _ (Nat.mul_pos hh ha)
  have hg2 : ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) ≤ (k : ℝ) * b := by
    exact_mod_cast Nat.gcd_le_right _ (Nat.mul_pos hk hb)
  have hg0 : (0 : ℝ) ≤ ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hden : 0 < 2 * Real.pi * ((h : ℝ) * a * ((k : ℝ) * b)) := by
    have : (0 : ℝ) < h := by exact_mod_cast hh
    have : (0 : ℝ) < k := by exact_mod_cast hk
    have : (0 : ℝ) < a := by exact_mod_cast ha
    have : (0 : ℝ) < b := by exact_mod_cast hb
    positivity
  unfold ratioArg
  rw [div_le_iff₀ hden]
  have hsq : ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) ^ 2 ≤ (h : ℝ) * a * ((k : ℝ) * b) := by
    rw [sq]; exact mul_le_mul hg1 hg2 hg0 (by positivity)
  have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hp : (0 : ℝ) ≤ (h : ℝ) * a * ((k : ℝ) * b) := by positivity
  calc t * ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) ^ 2 ≤ t * ((h : ℝ) * a * ((k : ℝ) * b)) :=
        mul_le_mul_of_nonneg_left hsq ht.le
    _ ≤ t * (2 * Real.pi * ((h : ℝ) * a * ((k : ℝ) * b))) := by
        apply mul_le_mul_of_nonneg_left _ ht.le
        nlinarith

/-- **The crude bound** `‖F(a,b,t)‖ ≤ C₀(1 + log⁺t) Σ(ha,kb)/(hk)`. -/
theorem norm_ratioForm_le_crude {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hH : ∀ x : ℝ, 0 < x → ‖ZetaNotch.diagHarm x‖ ≤ C₀ * (1 + max 0 (Real.log x)))
    (N : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 < t) :
    ‖ratioForm N a b t‖ ≤ C₀ * (1 + max 0 (Real.log t)) *
      ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) / ((h : ℝ) * k) := by
  unfold ratioForm
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h hh => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hh0 := (Finset.mem_Icc.mp hh).1
  have hk0 := (Finset.mem_Icc.mp hk).1
  have hx := ratioArg_pos ha hb hh0 hk0 ht
  have hxt := ratioArg_le ha hb hh0 hk0 ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := abs_ratioWeight_le (b := b) hh hk ha
  have h2 : ‖ZetaNotch.diagHarm (ratioArg a b h k t)‖ ≤ C₀ * (1 + max 0 (Real.log t)) := by
    refine (hH _ hx).trans ?_
    gcongr
  have hg : (0 : ℝ) ≤ ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) / ((h : ℝ) * k) := by positivity
  calc |ratioWeight N a b h k| * ‖ZetaNotch.diagHarm (ratioArg a b h k t)‖
      ≤ ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) / ((h : ℝ) * k) * (C₀ * (1 + max 0 (Real.log t))) :=
        mul_le_mul h1 h2 (norm_nonneg _) hg
    _ = _ := by ring

/-! ## Fibre terms -/

/-- **`‖Φ_T(a,b)‖ ≤ (T+1) Ψ₀ (ab)^{−1/2} M`** whenever `‖F(a,b,t)‖ ≤ M` on the progression. -/
theorem norm_fiberTerm_le {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2) {Ψ₀ : ℝ}
    (hΨ : ∀ y, |ψ y| ≤ Ψ₀) {α β : ℝ} (N : ℕ) {T : ℝ} (hT : 0 < T)
    (hpos : ∀ x : ℝ, ψ (x / T) ≠ 0 → 0 < α * x + β) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : 0 < a) (hb : 0 < b) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x : ℝ, ψ (x / T) ≠ 0 → ‖ratioForm N a b (α * x + β)‖ ≤ M) :
    ‖fiberTerm ψ α β N T (a, b)‖ ≤ (T + 1) * (Ψ₀ * ((Real.sqrt ((a : ℝ) * b))⁻¹ * M)) := by
  have hs := complex_support_subset hsupp
  have hΨ0 : 0 ≤ Ψ₀ := (abs_nonneg _).trans (hΨ 0)
  rw [fiberTerm_eq hsupp N hT hpos hab ha hb]
  have h := norm_latticeSum_le_of_bound (A := T) (B := 2 * T)
    (h := fun x => (ψ (x / T) : ℂ) * (((Real.sqrt ((a : ℝ) * b))⁻¹ : ℂ) *
      Complex.exp (((α * x + β) * (Real.log a - Real.log b) : ℝ) * I) *
        ratioForm N a b (α * x + β)))
    (M := Ψ₀ * ((Real.sqrt ((a : ℝ) * b))⁻¹ * M)) (by linarith)
    (support_cutoff_subset hs hT _) (fun x => ?_) 0
  · refine h.trans (le_of_eq ?_); ring
  by_cases h0 : ψ (x / T) = 0
  · simp only [h0, Complex.ofReal_zero, zero_mul, norm_zero]; positivity
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one,
    abs_of_pos (Real.sqrt_pos.mpr (by positivity))]
  gcongr
  · exact hΨ _
  · exact hM x h0

end

end RHTower.VerticalAP
