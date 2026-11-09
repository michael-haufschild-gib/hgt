import GaloisForLFunctions.SurfaceOfSpecZ.ARealTopKeepsTheLowerSideBounded

/-!
# The tensor powers have a common abscissa

For the virtual motive `M = Σ_z e_z ℤ(−z)` of the zeros, the Frobenius traces at `n = pᵐ` are
`2 Re S(log n)`, so `−L'/L(M^{⊗2k}, s) = Σ_n Λ(n) (2 Re S(log n))^{2k} n^{−s}` has nonnegative
coefficients. If `M` has top weight `b`, the abscissa of `M^{⊗2k}` is `1 + 2kb`: the weights of the
tensor powers grow linearly in `k` unless `b = 0`. Deligne's purity argument runs on this.

**Theorem** (`riemannHypothesis_iff_tensorPowers_commonAbscissa`). RH holds iff all even tensor
powers have a common half-plane of convergence: there is `σ₀` with
`Σ_n Λ(n) (2 Re S(log n))^{2k} n^{−σ₀} < ∞` for every `k ≥ 1`. Then every abscissa is `≤ 1`
(`riemannHypothesis_iff_tensorPowers_abscissa_le_one`).

**Proof.** Under RH every exponent has real part `0`, so `|2 Re S(u)| ≤ Σ_z |e_z|` on `u ≥ 0` and the
series is dominated by `Σ Λ(n) n^{−σ}`. Conversely one term at a prime gives
`|2 Re S(log p)| ≤ C_k p^{|σ₀|/(2k)}`, and the width law at the primes
(`zetaZeroWidth_le_iff_bddBelow_primeDegrees`) bounds the zero width by `|σ₀|/(2k)`; let `k → ∞`.
No attained maximum is needed: the width law is Landau's theorem for `ζ`.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
open ArithmeticFunction

/-- The `j`-th term of `−L'/L(M^{⊗2k}, σ)`, at `n = j + 1`. -/
def tensorLogDerivTerm (k : ℕ) (σ : ℝ) (j : ℕ) : ℝ :=
  Λ (j + 1) * (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log (j + 1))).re) ^ (2 * k) *
    ((j : ℝ) + 1) ^ (-σ)

theorem tensorLogDerivTerm_nonneg (k : ℕ) (σ : ℝ) (j : ℕ) : 0 ≤ tensorLogDerivTerm k σ j := by
  unfold tensorLogDerivTerm
  refine mul_nonneg (mul_nonneg vonMangoldt_nonneg ?_) (by positivity)
  rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _

/-- Under RH the spline traces are bounded by `Σ_z |e_z|`. -/
theorem abs_two_re_lagStructure_le_of_RH (hRH : RiemannHypothesis) {u : ℝ} (hu : 0 ≤ u) :
    |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re| ≤
      ∑' z, ‖evenCoeff zetaZeroConfig (boxSpline 1 3) z‖ := by
  have htop : TopDepth zetaZeroConfig 0 := by
    intro z hz
    rcases mem_of_evenCoeff_ne_zero hz with h | h
    · have := riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH _ h; simp at this; linarith
    · have := riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH _ h; simp at this; linarith
  have := abs_normTrace_le temperedConfig_zetaZeroConfig htop hu
  simpa [normTrace] using this

theorem summable_tensorLogDerivTerm_of_RH (hRH : RiemannHypothesis) (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Summable (tensorLogDerivTerm k σ) := by
  set E := ∑' z, ‖evenCoeff zetaZeroConfig (boxSpline 1 3) z‖
  refine Summable.of_nonneg_of_le (tensorLogDerivTerm_nonneg k σ) (fun j => ?_)
    ((summable_vonMangoldt_rpow hσ).mul_left (E ^ (2 * k)))
  have hb := abs_two_re_lagStructure_le_of_RH hRH (u := Real.log ((j : ℝ) + 1))
    (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j]))
  have hpow : (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log ((j : ℝ) + 1))).re) ^
      (2 * k) ≤ E ^ (2 * k) := by
    rw [pow_mul, pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg _) (by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2) k
  have hw : 0 ≤ Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ) := mul_nonneg vonMangoldt_nonneg (by positivity)
  unfold tensorLogDerivTerm
  calc Λ (j + 1) * (2 * (lagStructure zetaZeroConfig (boxSpline 1 3)
        (Real.log ((j : ℝ) + 1))).re) ^ (2 * k) * ((j : ℝ) + 1) ^ (-σ)
      = (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log ((j : ℝ) + 1))).re) ^ (2 * k) *
          (Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ)) := by ring
    _ ≤ E ^ (2 * k) * (Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ)) := mul_le_mul_of_nonneg_right hpow hw

/-- One term at a prime `p`: `log p · c^{2k} · p^{−σ₀} ≤ Σ`. -/
theorem prime_term_le_tsum {k : ℕ} {σ₀ : ℝ} (hs : Summable (tensorLogDerivTerm k σ₀)) {p : ℕ}
    (hp : p.Prime) :
    Real.log p * (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re) ^ (2 * k) *
      (p : ℝ) ^ (-σ₀) ≤ ∑' j, tensorLogDerivTerm k σ₀ j := by
  have h := hs.le_tsum (p - 1) (fun j _ => tensorLogDerivTerm_nonneg k σ₀ j)
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
  have hcast : ((p - 1 : ℕ) : ℝ) + 1 = p := by exact_mod_cast hp1
  unfold tensorLogDerivTerm at h
  rw [hp1, hcast, vonMangoldt_apply_prime hp] at h
  exact h

/-- **The tensor powers have a common abscissa iff RH.** -/
theorem riemannHypothesis_iff_tensorPowers_commonAbscissa :
    RiemannHypothesis ↔ ∃ σ₀ : ℝ, ∀ k : ℕ, 1 ≤ k → Summable (tensorLogDerivTerm k σ₀) := by
  constructor
  · intro hRH
    exact ⟨2, fun k _ => summable_tensorLogDerivTerm_of_RH hRH k (by norm_num)⟩
  · rintro ⟨σ₀, hσ₀⟩
    rw [riemannHypothesis_iff_zetaZeroWidth_le_zero]
    -- every large `k` bounds the width by `|σ₀|/(2k)`
    have hwidth : ∀ k : ℕ, 1 + |σ₀| < k → zetaZeroWidth ≤ |σ₀| / (2 * k) := by
      intro k hk
      have hk1 : 1 ≤ k := by
        have : (1 : ℝ) < k := by linarith [abs_nonneg σ₀]
        exact_mod_cast this.le
      have hk0 : (0 : ℝ) < k := by linarith [abs_nonneg σ₀]
      have hs := hσ₀ k hk1
      set T := ∑' j, tensorLogDerivTerm k σ₀ j with hT
      set a : ℝ := |σ₀| / (2 * k) with ha
      have ha0 : 0 ≤ a := by rw [ha]; positivity
      have ha1 : a < 1 / 2 := by
        rw [ha, div_lt_iff₀ (by positivity)]; linarith
      rw [zetaZeroWidth_le_iff_bddBelow_primeDegrees ha0 ha1]
      set B : ℝ := |T| / Real.log 2 with hB
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hB0 : 0 ≤ B := by rw [hB]; positivity
      refine ⟨B ^ ((1 : ℝ) / (2 * k)), fun p hp => ?_⟩
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
      have hp0 : (0 : ℝ) < p := by linarith
      have hlogp : Real.log 2 ≤ Real.log p :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
      set c := 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re with hc
      have hone := prime_term_le_tsum hs hp
      rw [← hc] at hone
      have hc2k0 : 0 ≤ c ^ (2 * k) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
      have hpσ : 0 < (p : ℝ) ^ (-σ₀) := by positivity
      have hc2k : |c| ^ (2 * k) ≤ B * (p : ℝ) ^ |σ₀| := by
        rw [show |c| ^ (2 * k) = c ^ (2 * k) by rw [pow_mul, pow_mul, sq_abs]]
        have h1 : Real.log 2 * c ^ (2 * k) * (p : ℝ) ^ (-σ₀) ≤ |T| :=
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlogp hc2k0) hpσ.le).trans
            (hone.trans (le_abs_self T))
        have hinv : (p : ℝ) ^ (-σ₀) * (p : ℝ) ^ σ₀ = 1 := by
          rw [← Real.rpow_add hp0]; simp
        have hpσ' : (p : ℝ) ^ σ₀ ≤ (p : ℝ) ^ |σ₀| :=
          Real.rpow_le_rpow_of_exponent_le hp1 (le_abs_self σ₀)
        have h2 : Real.log 2 * c ^ (2 * k) ≤ |T| * (p : ℝ) ^ σ₀ := by
          have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ σ₀)
          calc Real.log 2 * c ^ (2 * k) =
                Real.log 2 * c ^ (2 * k) * ((p : ℝ) ^ (-σ₀) * (p : ℝ) ^ σ₀) := by rw [hinv, mul_one]
            _ = Real.log 2 * c ^ (2 * k) * (p : ℝ) ^ (-σ₀) * (p : ℝ) ^ σ₀ := by ring
            _ ≤ _ := this
        have h3 : |T| * (p : ℝ) ^ σ₀ ≤ |T| * (p : ℝ) ^ |σ₀| :=
          mul_le_mul_of_nonneg_left hpσ' (abs_nonneg T)
        rw [hB, div_mul_eq_mul_div, le_div_iff₀ hlog2]
        linarith
      -- take the `2k`-th root
      have hroot : |c| ≤ B ^ ((1 : ℝ) / (2 * k)) * (p : ℝ) ^ a := by
        have h1 := Real.rpow_le_rpow (by positivity) hc2k (by positivity : (0 : ℝ) ≤ 1 / (2 * k))
        rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg c),
          show ((2 * k : ℕ) : ℝ) * (1 / (2 * k)) = 1 by push_cast; field_simp, Real.rpow_one,
          Real.mul_rpow hB0 (by positivity), ← Real.rpow_mul hp0.le] at h1
        rw [ha]
        convert h1 using 3
        ring
      linarith [neg_abs_le c]
    -- let `k → ∞`
    by_contra hpos
    push Not at hpos
    obtain ⟨k, hk⟩ := exists_nat_gt (max (1 + |σ₀|) (|σ₀| / (2 * zetaZeroWidth)))
    have hk1 : 1 + |σ₀| < k := (le_max_left _ _).trans_lt hk
    have hk2 : |σ₀| / (2 * zetaZeroWidth) < k := (le_max_right _ _).trans_lt hk
    have hk0 : (0 : ℝ) < k := by linarith [abs_nonneg σ₀]
    have := hwidth k hk1
    rw [div_lt_iff₀ (by positivity)] at hk2
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith

/-- **Every tensor power has abscissa `≤ 1` iff RH.** -/
theorem riemannHypothesis_iff_tensorPowers_abscissa_le_one :
    RiemannHypothesis ↔ ∀ k : ℕ, 1 ≤ k → ∀ σ : ℝ, 1 < σ → Summable (tensorLogDerivTerm k σ) := by
  constructor
  · exact fun hRH k _ σ hσ => summable_tensorLogDerivTerm_of_RH hRH k hσ
  · intro h
    exact riemannHypothesis_iff_tensorPowers_commonAbscissa.mpr
      ⟨2, fun k hk => h k hk 2 (by norm_num)⟩

end GaloisForLFunctions.SurfaceOfSpecZ
