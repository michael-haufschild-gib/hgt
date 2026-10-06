import GaloisForLFunctions.RHTower.KuznetsovGeomModulusBound
import GaloisForLFunctions.RHTower.KuznetsovGammaZeroGeom

/-!
# The sum over moduls of the `Γ₀(Q)` geometric side

For coefficients `a` on `(N, 2N]` put `b_k = ā_k √(2πk)` (`gamma0Coeff`).  For every `δ ∈ (0, 1/4]`
there are constants with, for every modulus `c ≥ 1` and `K ≥ 1`,

`c^{−2} |Φ_b(c)| ≤ (P K N^{1+2δ} c^{−1−δ/2} + P₃ K² e^{−K²/2}(N² c^{−2} + N³ c^{−3})) Σ|a|²`

(`exists_modulus_bound_gamma0`): for `c ≤ N` the better of DI (5.6) (`N^{3/2+δ}c^{−3/2}`) and DI (5.7)
(`K² N^{1/2+δ} c^{−1/2}`) according as `N/c ≤ K²` or not; for `c > N` the better of the separated form
(`N/c`) and the trivial bound (`N³/c²`) according as `c ≤ N²` or not.
-/

open MeasureTheory Set Filter Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open KuznetsovSeparation KuznetsovGauss RHTower.Sieve

noncomputable section

/-- `b_k = ā_k √(2πk)`. -/
def gamma0Coeff (a : ℕ → ℂ) (k : ℕ) : ℂ := conj (a k) * (Real.sqrt (2 * Real.pi * k) : ℂ)

theorem norm_gamma0Coeff_sq (a : ℕ → ℂ) (k : ℕ) :
    ‖gamma0Coeff a k‖ ^ 2 = 2 * Real.pi * k * ‖a k‖ ^ 2 := by
  rw [gamma0Coeff, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg
    (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (by positivity)]
  ring

theorem sum_norm_gamma0Coeff_sq_le (a : ℕ → ℂ) (N : ℕ) :
    ∑ k ∈ Finset.Ioc N (N + N), ‖gamma0Coeff a k‖ ^ 2 ≤
      4 * Real.pi * N * ∑ k ∈ Finset.Ioc N (N + N), ‖a k‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [norm_gamma0Coeff_sq]
  rw [Finset.mem_Ioc] at hk
  have h1 : (k : ℝ) ≤ N + N := by exact_mod_cast hk.2
  have h2 : 2 * Real.pi * k ≤ 4 * Real.pi * N := by nlinarith [Real.pi_pos]
  exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

theorem sum_norm_sqrtNormalize_gamma0Coeff_sq (a : ℕ → ℂ) (N : ℕ) :
    ∑ k ∈ Finset.Ioc N (N + N), ‖sqrtNormalize (gamma0Coeff a) k‖ ^ 2 =
      2 * Real.pi * ∑ k ∈ Finset.Ioc N (N + N), ‖a k‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_Ioc] at hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_le N).trans_lt hk.1
  rw [sqrtNormalize, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), div_pow,
    norm_gamma0Coeff_sq, Real.sq_sqrt hk0.le]
  field_simp

/-! ## Elementary inequalities -/

/-- `min(p₁ r³, p₂ K² r) ≤ max(p₁, p₂) K r²` for `r, K ≥ 1`. -/
theorem min_main_le {p₁ p₂ K r : ℝ} (hp₁ : 0 ≤ p₁) (hK : 1 ≤ K) (hr : 1 ≤ r) :
    min (p₁ * r ^ 3) (p₂ * K ^ 2 * r) ≤ max p₁ p₂ * K * r ^ 2 := by
  have hK0 : 0 ≤ K := by linarith
  have hr0 : 0 ≤ r := by linarith
  have h1 := le_max_left p₁ p₂
  have h2 := le_max_right p₁ p₂
  by_cases hcase : r ≤ K
  · refine (min_le_left _ _).trans ?_
    calc p₁ * r ^ 3 = p₁ * r ^ 2 * r := by ring
      _ ≤ max p₁ p₂ * r ^ 2 * K := by gcongr
      _ = _ := by ring
  · push Not at hcase
    refine (min_le_right _ _).trans ?_
    calc p₂ * K ^ 2 * r = p₂ * K * (K * r) := by ring
      _ ≤ max p₁ p₂ * K * (r * r) := by gcongr
      _ = _ := by ring

/-- `(N/c) N^δ ≤ N^{1+2δ} c^{−1−δ/2}` for `1 ≤ c ≤ N²`. -/
theorem ratio_mul_rpow_le {c N δ : ℝ} (hc : 1 ≤ c) (hN : 1 ≤ N) (hcN : c ≤ N ^ 2) (hδ : 0 ≤ δ) :
    N / c * N ^ δ ≤ N ^ (1 + 2 * δ) * c ^ (-(1 + δ / 2)) := by
  have hc0 : 0 < c := by linarith
  have hN0 : 0 < N := by linarith
  have h1 : c ^ (δ / 2) ≤ N ^ δ := by
    calc c ^ (δ / 2) ≤ (N ^ 2) ^ (δ / 2) := Real.rpow_le_rpow hc0.le hcN (by positivity)
      _ = N ^ δ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num; ring_nf
  have e1 : N ^ (1 + 2 * δ) * c ^ (-(1 + δ / 2)) = N / c * N ^ δ * (N ^ δ / c ^ (δ / 2)) := by
    rw [Real.rpow_add hN0, Real.rpow_one, Real.rpow_neg hc0.le, Real.rpow_add hc0, Real.rpow_one,
      show 2 * δ = δ + δ by ring, Real.rpow_add hN0]
    field_simp
  rw [e1]
  have h2 : 1 ≤ N ^ δ / c ^ (δ / 2) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have h3 : 0 ≤ N / c * N ^ δ := by positivity
  nlinarith

/-- `N³/c² ≤ N^{1+2δ} c^{−1−δ/2}` for `c ≥ N² ≥ 1`, `δ ≤ 1`. -/
theorem cube_div_sq_le {c N δ : ℝ} (hN : 1 ≤ N) (hcN : N ^ 2 ≤ c) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    N ^ 3 * (c ^ 2)⁻¹ ≤ N ^ (1 + 2 * δ) * c ^ (-(1 + δ / 2)) := by
  have hN0 : 0 < N := by linarith
  have hc0 : 0 < c := by nlinarith
  have h1 : N ^ (2 - 2 * δ) ≤ c ^ (1 - δ / 2) := by
    calc N ^ (2 - 2 * δ) ≤ N ^ (2 - δ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      _ = (N ^ 2) ^ (1 - δ / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num; ring_nf
      _ ≤ c ^ (1 - δ / 2) := Real.rpow_le_rpow (by positivity) hcN (by linarith)
  have e1 : N ^ (1 + 2 * δ) * c ^ (-(1 + δ / 2)) =
      N ^ 3 * (c ^ 2)⁻¹ * (c ^ (1 - δ / 2) / N ^ (2 - 2 * δ)) := by
    have ea : N ^ (1 + 2 * δ) = N ^ 3 / N ^ (2 - 2 * δ) := by
      rw [eq_div_iff (by positivity), ← Real.rpow_add hN0,
        show 1 + 2 * δ + (2 - 2 * δ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have eb : c ^ (-(1 + δ / 2)) = (c ^ 2)⁻¹ * c ^ (1 - δ / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg hc0.le, ← Real.rpow_add hc0]; norm_num; ring_nf
    rw [ea, eb]
    field_simp
  rw [e1]
  have h2 : 1 ≤ c ^ (1 - δ / 2) / N ^ (2 - 2 * δ) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have h3 : 0 ≤ N ^ 3 * (c ^ 2)⁻¹ := by positivity
  nlinarith

/-! ## The two main terms in `√c, √N` -/

theorem sin_terms_eq {c N : ℝ} (hc : 0 < c) (hN : 0 < N) (C D A T C₀ X : ℝ) :
    (c ^ 2)⁻¹ * ((Real.pi / 2 * (C * Real.sqrt c * (Real.sqrt N * D)) + T * (4 * C₀ * N ^ 2 / c) * X) *
      (4 * Real.pi * N * A)) =
      2 * Real.pi ^ 2 * C * (Real.sqrt N / Real.sqrt c) ^ 3 * (D * A) +
        16 * Real.pi * T * C₀ * X * (N ^ 3 * (c ^ 3)⁻¹) * A := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ c = s ^ 2 := ⟨Real.sqrt c, Real.sqrt_pos.2 hc,
    (Real.sq_sqrt hc.le).symm⟩
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 < t ∧ N = t ^ 2 := ⟨Real.sqrt N, Real.sqrt_pos.2 hN,
    (Real.sq_sqrt hN.le).symm⟩
  rw [Real.sqrt_sq hs.le, Real.sqrt_sq ht.le]
  field_simp
  ring

theorem cos_terms_eq {c N : ℝ} (hc : 0 < c) (hN : 0 < N) (C D A T C₀ K X : ℝ) :
    (c ^ 2)⁻¹ * (c / (2 * Real.pi) * (C * Real.sqrt c * (Real.sqrt N * D) * ((Real.pi + Real.sqrt Real.pi) * K ^ 2) +
      (4 * C₀ * N ^ 2 / c) * (T * X)) * (2 * Real.pi * A)) =
      C * (Real.pi + Real.sqrt Real.pi) * K ^ 2 * (Real.sqrt N / Real.sqrt c) * (D * A) +
        4 * C₀ * T * X * (N ^ 2 * (c ^ 2)⁻¹) * A := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ c = s ^ 2 := ⟨Real.sqrt c, Real.sqrt_pos.2 hc,
    (Real.sq_sqrt hc.le).symm⟩
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 < t ∧ N = t ^ 2 := ⟨Real.sqrt N, Real.sqrt_pos.2 hN,
    (Real.sq_sqrt hN.le).symm⟩
  rw [Real.sqrt_sq hs.le, Real.sqrt_sq ht.le]
  field_simp

theorem sqrt_ratio_sq {c N : ℝ} (hc : 0 < c) (hN : 0 < N) :
    (Real.sqrt N / Real.sqrt c) ^ 2 = N / c := by
  rw [div_pow, Real.sq_sqrt hN.le, Real.sq_sqrt hc.le]

/-- Small moduli `c ≤ N`, as an inequality between real numbers. -/
theorem small_modulus_real {c N K δ C C₀ A Ab Φ γ T₁ T₂ : ℝ} (hc1 : 1 ≤ c) (hcN : c ≤ N)
    (hK : 1 ≤ K) (hδ : 0 < δ) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hA : 0 ≤ A) (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (hAb0 : 0 ≤ Ab)
    (hsin : Φ ≤ (Real.pi / 2 * (C * Real.sqrt c * N ^ (1 / 2 + δ)) +
      T₁ * γ * (K * Real.exp (-K ^ 2 / 2))) * Ab)
    (hcos : Φ ≤ c / (2 * Real.pi) * ((C * Real.sqrt c * N ^ (1 / 2 + δ)) *
      ((Real.pi + Real.sqrt Real.pi) * K ^ 2) + γ * (T₂ * K ^ 2 * Real.exp (-K ^ 2 / 2))) *
        (2 * Real.pi * A))
    (hγ : γ ≤ 4 * C₀ * N ^ 2 / c) (hAb : Ab ≤ 4 * Real.pi * N * A) :
    (c ^ 2)⁻¹ * Φ ≤ max (2 * Real.pi ^ 2 * C) (C * (Real.pi + Real.sqrt Real.pi)) * K *
        (N ^ (1 + 2 * δ) * c ^ (-(1 + δ / 2))) * A +
      (16 * Real.pi * T₁ * C₀ + 4 * C₀ * T₂) * K ^ 2 * Real.exp (-K ^ 2 / 2) *
        (N ^ 2 * (c ^ 2)⁻¹ + N ^ 3 * (c ^ 3)⁻¹) * A := by
  set p₁ := 2 * Real.pi ^ 2 * C
  set p₂ := C * (Real.pi + Real.sqrt Real.pi)
  have hp₁ : 0 ≤ p₁ := by positivity
  have hc0 : 0 < c := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hK0 : 0 < K := by linarith
  set E := Real.exp (-K ^ 2 / 2)
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hKK : K ≤ K ^ 2 := by
    calc K = K * 1 := (mul_one K).symm
      _ ≤ K * K := mul_le_mul_of_nonneg_left hK hK0.le
      _ = K ^ 2 := (sq K).symm
  set D := N ^ δ
  have hD : 0 ≤ D := by positivity
  have hND : N ^ (1 / 2 + δ) = Real.sqrt N * D := by
    rw [Real.rpow_add hN0, Real.sqrt_eq_rpow]
  rw [hND] at hsin hcos
  set r := Real.sqrt N / Real.sqrt c
  have hr1 : 1 ≤ r := by
    rw [le_div_iff₀ (Real.sqrt_pos.2 hc0), one_mul]; exact Real.sqrt_le_sqrt hcN
  have hS : (c ^ 2)⁻¹ * Φ ≤ p₁ * r ^ 3 * (D * A) + 16 * Real.pi * T₁ * C₀ * (K ^ 2 * E) *
      (N ^ 3 * (c ^ 3)⁻¹) * A := by
    calc (c ^ 2)⁻¹ * Φ ≤ (c ^ 2)⁻¹ * ((Real.pi / 2 * (C * Real.sqrt c * (Real.sqrt N * D)) +
          T₁ * (4 * C₀ * N ^ 2 / c) * (K ^ 2 * E)) * (4 * Real.pi * N * A)) := by
          refine mul_le_mul_of_nonneg_left (hsin.trans ?_) (by positivity)
          gcongr
      _ = _ := sin_terms_eq hc0 hN0 C D A T₁ C₀ (K ^ 2 * E)
  have hCo : (c ^ 2)⁻¹ * Φ ≤ p₂ * K ^ 2 * r * (D * A) + 4 * C₀ * T₂ * (K ^ 2 * E) *
      (N ^ 2 * (c ^ 2)⁻¹) * A := by
    calc (c ^ 2)⁻¹ * Φ ≤ (c ^ 2)⁻¹ * (c / (2 * Real.pi) * (C * Real.sqrt c * (Real.sqrt N * D) *
          ((Real.pi + Real.sqrt Real.pi) * K ^ 2) + (4 * C₀ * N ^ 2 / c) * (T₂ * (K ^ 2 * E))) *
            (2 * Real.pi * A)) := by
          refine mul_le_mul_of_nonneg_left (hcos.trans ?_) (by positivity)
          have e : T₂ * K ^ 2 * E = T₂ * (K ^ 2 * E) := by ring
          rw [e]
          gcongr
      _ = _ := cos_terms_eq hc0 hN0 C D A T₂ C₀ K (K ^ 2 * E)
  have hmin := min_main_le hp₁ hK hr1 (p₂ := p₂)
  have hr2 : r ^ 2 = N / c := sqrt_ratio_sq hc0 hN0
  have hrat := ratio_mul_rpow_le hc1 hN1 (by nlinarith : c ≤ N ^ 2) hδ.le
  have t1 : 0 ≤ 16 * Real.pi * T₁ * C₀ * (K ^ 2 * E) * (N ^ 3 * (c ^ 3)⁻¹) * A := by positivity
  have t2 : 0 ≤ 4 * C₀ * T₂ * (K ^ 2 * E) * (N ^ 2 * (c ^ 2)⁻¹) * A := by positivity
  have t3 : 0 ≤ 16 * Real.pi * T₁ * C₀ * (K ^ 2 * E) * (N ^ 2 * (c ^ 2)⁻¹) * A := by positivity
  have t4 : 0 ≤ 4 * C₀ * T₂ * (K ^ 2 * E) * (N ^ 3 * (c ^ 3)⁻¹) * A := by positivity
  have hG1 : (c ^ 2)⁻¹ * Φ ≤ min (p₁ * r ^ 3) (p₂ * K ^ 2 * r) * (D * A) +
      (16 * Real.pi * T₁ * C₀ * (K ^ 2 * E) * (N ^ 3 * (c ^ 3)⁻¹) * A +
        4 * C₀ * T₂ * (K ^ 2 * E) * (N ^ 2 * (c ^ 2)⁻¹) * A) := by
    rcases min_cases (p₁ * r ^ 3) (p₂ * K ^ 2 * r) with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]; linarith
    · rw [h]; linarith
  have hDA : 0 ≤ D * A := by positivity
  have h2 : min (p₁ * r ^ 3) (p₂ * K ^ 2 * r) * (D * A) ≤
      max p₁ p₂ * K * (N ^ (1 + 2 * δ) * c ^ (-(1 + δ / 2))) * A := by
    calc min (p₁ * r ^ 3) (p₂ * K ^ 2 * r) * (D * A) ≤ max p₁ p₂ * K * r ^ 2 * (D * A) := by
          gcongr
      _ = max p₁ p₂ * K * (N / c * D) * A := by rw [hr2]; ring
      _ ≤ max p₁ p₂ * K * (N ^ (1 + 2 * δ) * c ^ (-(1 + δ / 2))) * A := by
          have : 0 ≤ max p₁ p₂ * K := by
            have := le_max_left p₁ p₂; positivity
          gcongr
  have h3 : 16 * Real.pi * T₁ * C₀ * (K ^ 2 * E) * (N ^ 3 * (c ^ 3)⁻¹) * A +
      4 * C₀ * T₂ * (K ^ 2 * E) * (N ^ 2 * (c ^ 2)⁻¹) * A ≤
      (16 * Real.pi * T₁ * C₀ + 4 * C₀ * T₂) * K ^ 2 * E * (N ^ 2 * (c ^ 2)⁻¹ + N ^ 3 * (c ^ 3)⁻¹) * A := by
    have e : (16 * Real.pi * T₁ * C₀ + 4 * C₀ * T₂) * K ^ 2 * E * (N ^ 2 * (c ^ 2)⁻¹ +
        N ^ 3 * (c ^ 3)⁻¹) * A = 16 * Real.pi * T₁ * C₀ * (K ^ 2 * E) * (N ^ 3 * (c ^ 3)⁻¹) * A +
          4 * C₀ * T₂ * (K ^ 2 * E) * (N ^ 2 * (c ^ 2)⁻¹) * A +
          (16 * Real.pi * T₁ * C₀ * (K ^ 2 * E) * (N ^ 2 * (c ^ 2)⁻¹) * A +
            4 * C₀ * T₂ * (K ^ 2 * E) * (N ^ 3 * (c ^ 3)⁻¹) * A) := by ring
    rw [e]; linarith
  linarith

/-- Large moduli `c > N`, as an inequality between real numbers. -/
theorem large_modulus_real {c N δ C₀ A Ab Φ γ P₄ : ℝ} (hc1 : 1 ≤ c) (hcN : N < c) (hN1 : 1 ≤ N)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) (hC₀ : 0 ≤ C₀) (hA : 0 ≤ A) (hAb0 : 0 ≤ Ab)
    (hP₄ : 32 * Real.pi * C₀ * (Real.pi / 4 + 2 * Real.pi * Real.exp 1) ≤ P₄)
    (hP₄' : 64 * Real.pi ^ 4 * Real.exp 1 ≤ P₄)
    (hsep : Φ ≤ 2 * γ * (Real.pi / 4 + 2 * Real.pi * Real.exp 1) * Ab)
    (htriv : Φ ≤ 16 * Real.pi ^ 3 * Real.exp 1 * N ^ 2 * Ab)
    (hγ : γ ≤ 4 * C₀ * c) (hAb : Ab ≤ 4 * Real.pi * N * A) :
    (c ^ 2)⁻¹ * Φ ≤ P₄ * (N ^ (1 + 2 * δ) * c ^ (-(1 + δ / 2))) * A := by
  have hc0 : 0 < c := by linarith
  have hN0 : 0 < N := by linarith
  have hW : 0 ≤ Real.pi / 4 + 2 * Real.pi * Real.exp 1 := by positivity
  have hP₄0 : 0 ≤ P₄ := le_trans (by positivity) hP₄'
  set Mn := N ^ (1 + 2 * δ) * c ^ (-(1 + δ / 2))
  have h1 : (c ^ 2)⁻¹ * Φ ≤ P₄ * (N / c) * A := by
    calc (c ^ 2)⁻¹ * Φ ≤ (c ^ 2)⁻¹ * (2 * (4 * C₀ * c) * (Real.pi / 4 + 2 * Real.pi * Real.exp 1) *
          (4 * Real.pi * N * A)) := by
          refine mul_le_mul_of_nonneg_left (hsep.trans ?_) (by positivity)
          gcongr
      _ = 32 * Real.pi * C₀ * (Real.pi / 4 + 2 * Real.pi * Real.exp 1) * (N / c) * A := by
          field_simp; ring
      _ ≤ P₄ * (N / c) * A := by gcongr
  have h2 : (c ^ 2)⁻¹ * Φ ≤ P₄ * (N ^ 3 * (c ^ 2)⁻¹) * A := by
    calc (c ^ 2)⁻¹ * Φ ≤ (c ^ 2)⁻¹ * (16 * Real.pi ^ 3 * Real.exp 1 * N ^ 2 * (4 * Real.pi * N * A)) := by
          refine mul_le_mul_of_nonneg_left (htriv.trans ?_) (by positivity)
          gcongr
      _ = 64 * Real.pi ^ 4 * Real.exp 1 * (N ^ 3 * (c ^ 2)⁻¹) * A := by ring
      _ ≤ P₄ * (N ^ 3 * (c ^ 2)⁻¹) * A := by gcongr
  by_cases hc2 : c ≤ N ^ 2
  · refine h1.trans ?_
    have h3 := ratio_mul_rpow_le hc1 hN1 hc2 hδ.le
    have h4 : N / c ≤ N / c * N ^ δ := le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hN1 hδ.le)
    have : N / c ≤ Mn := h4.trans h3
    gcongr
  · push Not at hc2
    refine h2.trans ?_
    have h3 := cube_div_sq_le hN1 hc2.le hδ.le (by linarith)
    gcongr

/-- **The bound for one modulus.** -/
theorem exists_modulus_bound_gamma0 {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ P P₃ : ℝ, 0 ≤ P ∧ 0 ≤ P₃ ∧ ∀ (c : ℕ) [NeZero c] (N : ℕ), 1 ≤ N → ∀ (K : ℝ), 1 ≤ K →
      ∀ (a : ℕ → ℂ), ((c : ℝ) ^ 2)⁻¹ * ‖modulusForm c N K (gamma0Coeff a)‖ ≤
        (P * K * (N : ℝ) ^ (1 + 2 * δ) * (c : ℝ) ^ (-(1 + δ / 2)) +
          P₃ * K ^ 2 * Real.exp (-K ^ 2 / 2) * ((N : ℝ) ^ 2 * ((c : ℝ) ^ 2)⁻¹ +
            (N : ℝ) ^ 3 * ((c : ℝ) ^ 3)⁻¹)) * ∑ k ∈ Finset.Ioc N (N + N), ‖a k‖ ^ 2 := by
  obtain ⟨C, C₀, hC, hC₀, hmod⟩ := exists_norm_modulusForm_le hδ
  set p₁ := 2 * Real.pi ^ 2 * C
  set p₂ := C * (Real.pi + Real.sqrt Real.pi)
  set T₁ := 8 * Real.sqrt Real.pi * Real.exp 1
  set T₂ := (10 * Real.pi + 4 * Real.sqrt Real.pi) * Real.exp 1
  set P₄ := max (32 * Real.pi * C₀ * (Real.pi / 4 + 2 * Real.pi * Real.exp 1))
    (64 * Real.pi ^ 4 * Real.exp 1)
  set P₃ := 16 * Real.pi * T₁ * C₀ + 4 * C₀ * T₂
  have hp₁ : 0 ≤ p₁ := by positivity
  have hP₄ : 0 ≤ P₄ := le_max_of_le_right (by positivity)
  have hT₁ : 0 ≤ T₁ := by positivity
  have hT₂ : 0 ≤ T₂ := by positivity
  have hP₃ : 0 ≤ P₃ := by positivity
  have hmax : 0 ≤ max p₁ p₂ := le_max_of_le_left hp₁
  refine ⟨max p₁ p₂ + P₄, P₃, by positivity, hP₃, fun c _ N hN K hK a => ?_⟩
  have hA : 0 ≤ ∑ k ∈ Finset.Ioc N (N + N), ‖a k‖ ^ 2 := Finset.sum_nonneg fun k _ => by positivity
  have hAb := sum_norm_gamma0Coeff_sq_le a N
  have hAb' := sum_norm_sqrtNormalize_gamma0Coeff_sq a N
  have hAb0 : 0 ≤ ∑ k ∈ Finset.Ioc N (N + N), ‖gamma0Coeff a k‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => by positivity
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne c)
  have hc0 : (0 : ℝ) < c := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hK0 : 0 < K := by linarith
  have hMn : 0 ≤ (N : ℝ) ^ (1 + 2 * δ) * (c : ℝ) ^ (-(1 + δ / 2)) := by positivity
  have hY : 0 ≤ P₃ * K ^ 2 * Real.exp (-K ^ 2 / 2) * ((N : ℝ) ^ 2 * ((c : ℝ) ^ 2)⁻¹ +
      (N : ℝ) ^ 3 * ((c : ℝ) ^ 3)⁻¹) := by positivity
  obtain ⟨hsin, hcos, hbig⟩ := hmod c N hN K hK (gamma0Coeff a)
  clear hmod
  by_cases hcN : c ≤ N
  · have hcN' : (c : ℝ) ≤ N := by exact_mod_cast hcN
    have hγ : C₀ * (1 + (N : ℝ) / c) * ((N : ℝ) + c) ≤ 4 * C₀ * (N : ℝ) ^ 2 / c := by
      rw [le_div_iff₀ hc0]
      have h2 : (1 + (N : ℝ) / c) * c ≤ 2 * N := by
        rw [add_mul, div_mul_cancel₀ _ hc0.ne']; linarith
      have h3 : (N : ℝ) + c ≤ 2 * N := by linarith
      calc C₀ * (1 + (N : ℝ) / c) * ((N : ℝ) + c) * c =
            C₀ * ((1 + (N : ℝ) / c) * c) * ((N : ℝ) + c) := by ring
        _ ≤ C₀ * (2 * N) * (2 * N) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h2 hC₀) h3 (by positivity) (by positivity)
        _ = 4 * C₀ * (N : ℝ) ^ 2 := by ring
    have hcos' := hcos hcN
    rw [hAb'] at hcos'
    have key := small_modulus_real hc1 hcN' hK hδ hC hC₀ hA hT₁ hT₂ hAb0 (hsin hcN)
      (by
        refine hcos'.trans (le_of_eq ?_)
        simp only [T₂]) hγ hAb
    refine key.trans ?_
    have : max p₁ p₂ * K * ((N : ℝ) ^ (1 + 2 * δ) * (c : ℝ) ^ (-(1 + δ / 2))) ≤
        (max p₁ p₂ + P₄) * K * (N : ℝ) ^ (1 + 2 * δ) * (c : ℝ) ^ (-(1 + δ / 2)) := by
      calc max p₁ p₂ * K * ((N : ℝ) ^ (1 + 2 * δ) * (c : ℝ) ^ (-(1 + δ / 2))) =
            max p₁ p₂ * (K * ((N : ℝ) ^ (1 + 2 * δ) * (c : ℝ) ^ (-(1 + δ / 2)))) := by ring
        _ ≤ (max p₁ p₂ + P₄) * (K * ((N : ℝ) ^ (1 + 2 * δ) * (c : ℝ) ^ (-(1 + δ / 2)))) :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hP₄) (by positivity)
        _ = _ := by ring
    simp only [P₃]
    linarith [mul_le_mul_of_nonneg_right this hA]
  · push Not at hcN
    have hcN' : (N : ℝ) < c := by exact_mod_cast hcN
    have hγ : C₀ * (1 + (N : ℝ) / c) * ((N : ℝ) + c) ≤ 4 * C₀ * c := by
      have h1 : (N : ℝ) / c ≤ 1 := by rw [div_le_one hc0]; linarith
      have h2 : (1 + (N : ℝ) / c) ≤ 2 := by linarith
      have h3 : (N : ℝ) + c ≤ 2 * c := by linarith
      calc C₀ * (1 + (N : ℝ) / c) * ((N : ℝ) + c) ≤ C₀ * 2 * (2 * c) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h2 hC₀) h3 (by positivity) (by positivity)
        _ = 4 * C₀ * c := by ring
    have key := large_modulus_real hc1 hcN' hN1 hδ hδ1 hC₀ hA hAb0 (le_max_left _ _) (le_max_right _ _)
      (P₄ := P₄) (hbig hcN) (norm_modulusForm_le_trivial c N hK _) hγ hAb
    refine key.trans ?_
    have : P₄ * ((N : ℝ) ^ (1 + 2 * δ) * (c : ℝ) ^ (-(1 + δ / 2))) ≤
        (max p₁ p₂ + P₄) * K * (N : ℝ) ^ (1 + 2 * δ) * (c : ℝ) ^ (-(1 + δ / 2)) := by
      calc P₄ * ((N : ℝ) ^ (1 + 2 * δ) * (c : ℝ) ^ (-(1 + δ / 2))) ≤
            (max p₁ p₂ + P₄) * ((N : ℝ) ^ (1 + 2 * δ) * (c : ℝ) ^ (-(1 + δ / 2))) :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hmax) hMn
        _ = (max p₁ p₂ + P₄) * ((N : ℝ) ^ (1 + 2 * δ) * (c : ℝ) ^ (-(1 + δ / 2))) * 1 := (mul_one _).symm
        _ ≤ (max p₁ p₂ + P₄) * ((N : ℝ) ^ (1 + 2 * δ) * (c : ℝ) ^ (-(1 + δ / 2))) * K :=
            mul_le_mul_of_nonneg_left hK (by positivity)
        _ = _ := by ring
    linarith [mul_le_mul_of_nonneg_right this hA, mul_nonneg hY hA]

end

end GaloisForLFunctions.RHTower.DeckPointPair
