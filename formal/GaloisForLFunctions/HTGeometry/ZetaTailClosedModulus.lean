import GaloisForLFunctions.HTGeometry.GevreyFactorialNormalization

/-!
# The closed modulus of an irrational-power zeta tail

The tail coefficients of the Barnes expansion of an irrational-power canonical product are
`b_k = (-1)^k ζ(-s k)`.  The functional equation turns that into the closed modulus

`|b_k| = 2 |sin(π s k / 2)| Γ(1 + s k) ζ(1 + s k) / (2π)^{1 + s k}`,

which is what carries the exact Gevrey order.  Everything here is the functional equation plus the
identity `cos(π/2 + x) = -sin x`; no asymptotic analysis is involved.

The zeta factor is also pinned between `1` and `ζ(1 + s)` by the Dirichlet series, which is the
remaining input of the Gevrey bounds.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

/-! ### The functional equation in modulus form -/

theorem norm_riemannZeta_one_sub_ofReal {σ : ℝ} (hσ : 1 < σ) :
    ‖riemannZeta ((1 : ℂ) - (σ : ℂ))‖
      = 2 * (2 * Real.pi) ^ (-σ) * Real.Gamma σ * |Real.cos (Real.pi * σ / 2)|
        * ‖riemannZeta (σ : ℂ)‖ := by
  have hne : ∀ n : ℕ, (σ : ℂ) ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hne1 : (σ : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.one_re] at hre
    linarith
  rw [riemannZeta_one_sub hne hne1]
  have h2pi : ((2 : ℂ) * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  have hpipos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hcpow : ‖((2 : ℂ) * (Real.pi : ℂ)) ^ (-(σ : ℂ))‖ = (2 * Real.pi) ^ (-σ) := by
    rw [h2pi, Complex.norm_cpow_eq_rpow_re_of_pos hpipos, Complex.neg_re, Complex.ofReal_re]
  have hgam : ‖Complex.Gamma (σ : ℂ)‖ = Real.Gamma σ := by
    rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.Gamma_pos_of_pos (by linarith))]
  have hcos : ‖Complex.cos ((Real.pi : ℂ) * (σ : ℂ) / 2)‖ = |Real.cos (Real.pi * σ / 2)| := by
    have harg : (Real.pi : ℂ) * (σ : ℂ) / 2 = ((Real.pi * σ / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [harg, ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
  simp only [norm_mul, hcpow, hgam, hcos, Complex.norm_ofNat]

/-- **The closed modulus of the tail coefficient.**  For `s > 0` and `k ≥ 1`,

`|ζ(-s k)| = 2 |sin(π s k / 2)| Γ(1 + s k) |ζ(1 + s k)| / (2π)^{1 + s k}`. -/
theorem norm_riemannZeta_neg_eq {s : ℝ} (hs : 0 < s) {k : ℕ} (hk : k ≠ 0) :
    ‖riemannZeta ((-(s * k) : ℝ) : ℂ)‖
      = 2 * |Real.sin (Real.pi * s * k / 2)| * Real.Gamma (1 + s * k)
        * ‖riemannZeta ((1 + s * k : ℝ) : ℂ)‖ / (2 * Real.pi) ^ (1 + s * (k : ℝ)) := by
  have hkpos : (0 : ℝ) < k := by
    have : 0 < k := Nat.pos_of_ne_zero hk
    exact_mod_cast this
  have hσ : (1 : ℝ) < 1 + s * k := by nlinarith
  have harg : ((1 : ℂ) - ((1 + s * k : ℝ) : ℂ)) = ((-(s * k) : ℝ) : ℂ) := by push_cast; ring
  have hmain := norm_riemannZeta_one_sub_ofReal hσ
  rw [harg] at hmain
  have hcos : Real.cos (Real.pi * (1 + s * k) / 2) = -Real.sin (Real.pi * s * k / 2) := by
    have harg2 : Real.pi * (1 + s * k) / 2 = Real.pi / 2 + Real.pi * s * k / 2 := by ring
    rw [harg2, Real.cos_add]
    simp
  rw [hcos, abs_neg] at hmain
  rw [hmain]
  have hpipos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hrpow : (2 * Real.pi) ^ (-(1 + s * (k : ℝ)))
      = ((2 * Real.pi) ^ (1 + s * (k : ℝ)))⁻¹ := Real.rpow_neg hpipos.le _
  rw [hrpow]
  field_simp

/-! ### The zeta factor on the real axis -/

theorem riemannZeta_ofReal_eq_tsum {σ : ℝ} (hσ : 1 < σ) :
    riemannZeta (σ : ℂ) = ∑' n : ℕ, ((n : ℂ) ^ (-(σ : ℂ))) := by
  have hre : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have h := tsum_riemannZetaSummand hre
  rw [← h]
  rfl

theorem norm_riemannZeta_ofReal_eq_tsum {σ : ℝ} (hσ : 1 < σ) :
    ‖riemannZeta (σ : ℂ)‖ = ∑' n : ℕ, (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ)) := by
  have hterm : ∀ n : ℕ, ((n : ℂ) ^ (-(σ : ℂ)))
      = (((if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ)) : ℝ) : ℂ) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      have : (-(σ : ℂ)) ≠ 0 := by
        simp only [neg_ne_zero, ne_eq, Complex.ofReal_eq_zero]
        linarith
      simp [this]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by
        have : 0 < n := Nat.pos_of_ne_zero hn
        exact_mod_cast this
      rw [if_neg hn, Complex.ofReal_cpow hnpos.le]
      norm_cast
  rw [riemannZeta_ofReal_eq_tsum hσ]
  rw [tsum_congr hterm, ← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg]
  refine tsum_nonneg fun n => ?_
  by_cases hn : n = 0 <;> simp [hn]
  positivity

theorem summable_zeta_terms {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ)) := by
  have hbase : Summable fun n : ℕ => (n : ℝ) ^ (-σ) := by
    simpa using Real.summable_nat_rpow_inv.mpr hσ
  refine hbase.congr_cofinite ?_
  filter_upwards [Set.Finite.compl_mem_cofinite (Set.finite_singleton (0 : ℕ))] with n hn
  have hn0 : n ≠ 0 := by simpa using hn
  simp [hn0]

/-- **The zeta factor is at least one.** -/
theorem one_le_norm_riemannZeta_ofReal {σ : ℝ} (hσ : 1 < σ) :
    1 ≤ ‖riemannZeta (σ : ℂ)‖ := by
  rw [norm_riemannZeta_ofReal_eq_tsum hσ]
  have hsum := summable_zeta_terms hσ
  have hone : (if (1 : ℕ) = 0 then (0 : ℝ) else ((1 : ℕ) : ℝ) ^ (-σ)) = 1 := by
    norm_num
  have hle := hsum.le_tsum (i := 1) (fun n _ => by by_cases hn : n = 0 <;> simp [hn]; positivity)
  rw [hone] at hle
  exact hle

/-- **The zeta factor is bounded by its value at the smallest exponent.** -/
theorem norm_riemannZeta_ofReal_le {σ τ : ℝ} (hσ : 1 < σ) (hστ : σ ≤ τ) :
    ‖riemannZeta (τ : ℂ)‖ ≤ ‖riemannZeta (σ : ℂ)‖ := by
  have hτ : 1 < τ := lt_of_lt_of_le hσ hστ
  rw [norm_riemannZeta_ofReal_eq_tsum hσ, norm_riemannZeta_ofReal_eq_tsum hτ]
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_zeta_terms hτ) (summable_zeta_terms hσ)
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, if_neg hn]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      exact_mod_cast this
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)

/-! ### The exact Gevrey order of the zeta tail, unconditionally -/

/-- The tail coefficient modulus, with the irrelevant index `0` set to zero. -/
noncomputable def zetaTailModulus (s : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else ‖riemannZeta ((-(s * k) : ℝ) : ℂ)‖

/-- The zeta factor of the closed modulus, normalized to `1` at the irrelevant index `0`. -/
noncomputable def zetaTailFactor (s : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else ‖riemannZeta ((1 + s * k : ℝ) : ℂ)‖

theorem one_le_zetaTailFactor {s : ℝ} (hs : 0 < s) (k : ℕ) : 1 ≤ zetaTailFactor s k := by
  rw [zetaTailFactor]
  by_cases hk : k = 0
  · simp [hk]
  · rw [if_neg hk]
    have hkpos : (0 : ℝ) < k := by
      have : 0 < k := Nat.pos_of_ne_zero hk
      exact_mod_cast this
    exact one_le_norm_riemannZeta_ofReal (by nlinarith)

theorem zetaTailFactor_le {s : ℝ} (hs : 0 < s) (k : ℕ) :
    zetaTailFactor s k ≤ max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖ := by
  rw [zetaTailFactor]
  by_cases hk : k = 0
  · simp [hk]
  · rw [if_neg hk]
    refine le_trans ?_ (le_max_right _ _)
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
      have : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      exact_mod_cast this
    exact norm_riemannZeta_ofReal_le (by linarith) (by nlinarith)

theorem zetaTailModulus_eq {s : ℝ} (hs : 0 < s) (k : ℕ) :
    |zetaTailModulus s k|
      = 2 * |Real.sin (Real.pi * s * k / 2)| * Real.Gamma (1 + s * k) * zetaTailFactor s k
        / (2 * Real.pi) ^ (1 + s * (k : ℝ)) := by
  by_cases hk : k = 0
  · subst hk
    simp [zetaTailModulus, zetaTailFactor]
  · rw [zetaTailModulus, zetaTailFactor, if_neg hk, if_neg hk,
      abs_of_nonneg (norm_nonneg _), norm_riemannZeta_neg_eq hs hk]

/-- **The exact Gevrey order of the irrational-power zeta tail, unconditionally.**  With no
hypothesis beyond `s > 0` irrational, the tail coefficients `|ζ(-s k)|` obey

`|b k| ≤ C A^k (k!)^s` for every `k`,  and  `c a^k (k!)^s ≤ |b k|` for infinitely many `k`. -/
theorem gevrey_exact_order_zetaTail {s : ℝ} (hs : 0 < s) (hirr : Irrational s) :
    (∃ C A : ℝ, 0 < C ∧ 0 < A ∧
        ∀ k : ℕ, |zetaTailModulus s k| ≤ C * A ^ k * (k.factorial : ℝ) ^ s) ∧
      (∃ c a : ℝ, 0 < c ∧ 0 < a ∧
        {k : ℕ | c * a ^ k * (k.factorial : ℝ) ^ s ≤ |zetaTailModulus s k|}.Infinite) := by
  refine gevrey_exact_order_factorial (M := max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖) hs hirr
    (one_le_zetaTailFactor hs) (zetaTailFactor_le hs) (zetaTailModulus_eq hs) fun k => ?_
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  exact Real.Gamma_pos_of_pos (by nlinarith)

end GaloisForLFunctions.HTGeometry
