import GaloisForLFunctions.ArithmeticDiscreteness.DistinctRootsOfIntegerPolynomialsRepel

/-!
# Impurity is quantized

The function-field model with its integral structure. For a curve over `𝔽_q` the Frobenius
eigenvalues pair as `α, q/α`, and the **trace points** `τ = α + q/α` are the roots of a monic
integer polynomial `h`. The configuration is pure (`|α| = √q`) exactly when every trace point is
real and lies in `[−2√q, 2√q]` (`IsPureTrace`). The two ways to leave purity are the two Frobenius
collisions: two pairs `{α, q/α}` meeting (a double trace point) and `α` meeting `q/α` (a trace
point at `±2√q`). Integrality makes both collide or repel.

* **Conjugate pairs repel** (`one_le_two_abs_im_mul_pow`). A non-real trace point `τ` and its
  conjugate are distinct roots of `h`: `1 ≤ 2|Im τ| (2R)^{(n−1)²+n−2}`.
* **Eigenvalue and inverse repel** (`frobenius_collide_or_repel`). Either `τ² = 4q` or
  `1 ≤ |τ² − 4q| (R² + 4q)^{n−1}`: the product `∏_σ (σ² − 4q)` over the conjugates of `τ` is the
  resultant of the minimal polynomial of `τ` and `X² − 4q`, a nonzero integer.
* **Impurity is quantized** (`impurity_is_quantized`). Every trace point is pure, or is non-real
  with `2|Im τ| ≥ ε₀`, or is real with `|τ| ≥ 2√q + ε₁`; `ε₀, ε₁` depend only on `n`, `q`, `R`.
* **Near purity is purity** (`isPureTrace_of_near`). If every trace point lies within `ε₀/2`
  (imaginary part) and `ε₁` (beyond the edge) of the segment, the configuration is pure.
* **Discreteness is not a producer** (`exists_impure_integral`). In every degree there are monic
  integer polynomials with an impure trace point: integrality quantizes impurity, it does not
  exclude it.
-/

open Polynomial Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- A trace point is **pure** for `q` when it is real and lies in `[−2√q, 2√q]`. -/
def IsPureTrace (q : ℝ) (τ : ℂ) : Prop := τ.im = 0 ∧ |τ.re| ≤ 2 * Real.sqrt q

/-- The conjugate of a root of an integer polynomial is a root. -/
theorem conj_mem_roots_toC {f : ℤ[X]} (hf : f.Monic) {z : ℂ} (hz : z ∈ (toC f).roots) :
    (starRingEnd ℂ) z ∈ (toC f).roots := by
  rw [mem_roots (toC_ne_zero hf), IsRoot, eval_map] at hz ⊢
  have h := congrArg (starRingEnd ℂ) hz
  rw [hom_eval₂, map_zero,
    RingHom.ext_int ((starRingEnd ℂ).comp (Int.castRingHom ℂ)) (Int.castRingHom ℂ)] at h
  exact h

/-- **Conjugate pairs repel.** A non-real root `τ` of a monic integer polynomial of degree `n`
with all roots in `|z| ≤ R`, `2R ≥ 1`, has `1 ≤ 2|Im τ| (2R)^{(n−1)²+n−2}`. -/
theorem one_le_two_abs_im_mul_pow {h : ℤ[X]} (hh : h.Monic) {R : ℝ} (hR1 : 1 ≤ 2 * R)
    (hR : ∀ z ∈ (toC h).roots, ‖z‖ ≤ R) {τ : ℂ} (hτ : τ ∈ (toC h).roots) (him : τ.im ≠ 0) :
    1 ≤ 2 * |τ.im| * (2 * R) ^ ((h.natDegree - 1) ^ 2 + (h.natDegree - 2)) := by
  have hne : τ ≠ (starRingEnd ℂ) τ := fun heq => him (conj_eq_iff_im.mp heq.symm)
  have key := one_le_norm_sub_mul_pow_of_ne hh hR1 hR hτ (conj_mem_roots_toC hh hτ) hne
  rwa [sub_conj, norm_mul, norm_real, norm_I, mul_one, Real.norm_eq_abs, abs_mul,
    abs_two] at key

/-- The polynomial `X² − 4q`. -/
abbrev edgePoly (q : ℕ) : ℤ[X] := X ^ 2 - C (4 * (q : ℤ))

theorem natDegree_edgePoly (q : ℕ) : (edgePoly q).natDegree = 2 := by
  rw [edgePoly, natDegree_sub_C, natDegree_X_pow]

theorem eval_toC_edgePoly (q : ℕ) (z : ℂ) : (toC (edgePoly q)).eval z = z ^ 2 - 4 * q := by
  simp [toC, edgePoly]

/-- Over the conjugates of `τ`, `∏_σ (σ² − 4q)` is the resultant of `minpoly τ` and `X² − 4q`. -/
theorem prod_edge_eq_resultant {A : ℤ[X]} (hA : A.Monic) (q : ℕ) :
    ((toC A).roots.map fun σ => σ ^ 2 - 4 * (q : ℂ)).prod =
      ((resultant A (edgePoly q) A.natDegree 2 : ℤ) : ℂ) := by
  have h1 := resultant_eq_prod_eval (toC A) (toC (edgePoly q)) 2
    (by rw [natDegree_toC, natDegree_edgePoly]) (IsAlgClosed.splits _)
  rw [(hA.map _).leadingCoeff, one_pow, one_mul, natDegree_toC, toC, toC, resultant_map_map] at h1
  rw [eq_intCast] at h1
  rw [h1]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun σ _ => (eval_toC_edgePoly q σ).symm)

/-- **Eigenvalue and inverse collide or repel.** A root `τ` of a monic integer polynomial of degree
`n` with all roots in `|z| ≤ R` has `τ² = 4q` (an eigenvalue `α = q/α = ±√q`) or
`1 ≤ |τ² − 4q| (R² + 4q)^{n−1}`. -/
theorem frobenius_collide_or_repel {h : ℤ[X]} (hh : h.Monic) {q : ℕ} (hq : 1 ≤ q) {R : ℝ}
    (hR : ∀ z ∈ (toC h).roots, ‖z‖ ≤ R) {τ : ℂ} (hτ : τ ∈ (toC h).roots) :
    τ ^ 2 = 4 * (q : ℂ) ∨ 1 ≤ ‖τ ^ 2 - 4 * (q : ℂ)‖ * (R ^ 2 + 4 * q) ^ (h.natDegree - 1) := by
  classical
  by_cases hedge : τ ^ 2 = 4 * (q : ℂ)
  · exact Or.inl hedge
  refine Or.inr ?_
  have hint := isIntegral_of_mem_roots hh hτ
  set A := minpoly ℤ τ with hAdef
  have hAm : A.Monic := minpoly.monic hint
  have hAh : (toC A).roots ≤ (toC h).roots := roots_toC_le_of_dvd hh (minpoly_dvd_of_mem_roots hh hτ)
  have hτA : τ ∈ (toC A).roots := mem_roots_toC_minpoly hint
  -- the resultant is a nonzero integer
  have hres : resultant A (edgePoly q) A.natDegree 2 ≠ 0 := by
    intro h0
    have hprod := prod_edge_eq_resultant hAm q
    rw [h0, Int.cast_zero, Multiset.prod_eq_zero_iff] at hprod
    obtain ⟨σ, hσ, hσ0⟩ := Multiset.mem_map.mp hprod
    have hσG : aeval σ (edgePoly q) = 0 := by
      rw [aeval_eq_eval_toC, eval_toC_edgePoly]; exact hσ0
    have hAσ : A = minpoly ℤ σ := eq_minpoly_of_irreducible (minpoly.irreducible hint) hAm hσ
    have hdvd : A ∣ edgePoly q := hAσ ▸
      minpoly.isIntegrallyClosed_dvd (isIntegral_of_mem_roots hAm hσ) hσG
    have hτG : τ ∈ (toC (edgePoly q)).roots :=
      Multiset.mem_of_le (roots_toC_le_of_dvd (by
        rw [edgePoly]; exact monic_X_pow_sub_C _ two_ne_zero) hdvd) hτA
    rw [mem_roots (toC_ne_zero (by rw [edgePoly]; exact monic_X_pow_sub_C _ two_ne_zero)),
      IsRoot, eval_toC_edgePoly, sub_eq_zero] at hτG
    exact hedge hτG
  have hone : 1 ≤ ‖((toC A).roots.map fun σ => σ ^ 2 - 4 * (q : ℂ)).prod‖ := by
    rw [prod_edge_eq_resultant hAm q, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hres
  rw [ZeroConfigurationGeometry.norm_multiset_prod_map, ← Multiset.prod_map_erase hτA] at hone
  -- the other conjugates contribute at most `R² + 4q` each
  have hbound : ∀ σ ∈ (toC A).roots, ‖σ ^ 2 - 4 * (q : ℂ)‖ ≤ R ^ 2 + 4 * q := by
    intro σ hσ
    have hσR := hR σ (Multiset.mem_of_le hAh hσ)
    calc ‖σ ^ 2 - 4 * (q : ℂ)‖ ≤ ‖σ‖ ^ 2 + 4 * q := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_pow, norm_mul, Complex.norm_natCast, show ‖(4 : ℂ)‖ = 4 by norm_num]
      _ ≤ R ^ 2 + 4 * q := by
          have := pow_le_pow_left₀ (norm_nonneg σ) hσR 2; linarith
  have hcardA : Multiset.card (toC A).roots = A.natDegree := card_roots_toC
  have hdegA : A.natDegree ≤ h.natDegree := by
    rw [← card_roots_toC, ← card_roots_toC (f := h)]; exact Multiset.card_le_card hAh
  have hq1 : (1 : ℝ) ≤ R ^ 2 + 4 * q := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith [sq_nonneg R]
  have hrest : (((toC A).roots.erase τ).map fun σ => ‖σ ^ 2 - 4 * (q : ℂ)‖).prod ≤
      (R ^ 2 + 4 * q) ^ (h.natDegree - 1) := by
    have := ZeroConfigurationGeometry.multiset_prod_le_pow ((toC A).roots.erase τ)
      (fun σ => ‖σ ^ 2 - 4 * (q : ℂ)‖) (fun _ _ => norm_nonneg _)
      (fun σ hσ => hbound σ (Multiset.mem_of_mem_erase hσ))
    rw [Multiset.card_erase_of_mem hτA, hcardA, Nat.pred_eq_sub_one] at this
    exact this.trans (pow_le_pow_right₀ hq1 (Nat.sub_le_sub_right hdegA 1))
  calc (1 : ℝ) ≤ ‖τ ^ 2 - 4 * (q : ℂ)‖ *
        (((toC A).roots.erase τ).map fun σ => ‖σ ^ 2 - 4 * (q : ℂ)‖).prod := hone
    _ ≤ ‖τ ^ 2 - 4 * (q : ℂ)‖ * (R ^ 2 + 4 * q) ^ (h.natDegree - 1) :=
        mul_le_mul_of_nonneg_left hrest (norm_nonneg _)

/-- For a real point, `|x² − 4q| = (|x| − 2√q)(|x| + 2√q)`. -/
theorem norm_sq_sub_four_q_of_real {q : ℕ} {x : ℝ} :
    ‖(x : ℂ) ^ 2 - 4 * (q : ℂ)‖ = |(|x| - 2 * Real.sqrt q) * (|x| + 2 * Real.sqrt q)| := by
  have hs : Real.sqrt q ^ 2 = q := Real.sq_sqrt (Nat.cast_nonneg q)
  have hx : |x| ^ 2 = x ^ 2 := sq_abs x
  have : ((x : ℂ) ^ 2 - 4 * (q : ℂ)) = (((|x| - 2 * Real.sqrt q) * (|x| + 2 * Real.sqrt q) : ℝ) : ℂ) := by
    push_cast
    have h2 : ((|x| : ℝ) : ℂ) ^ 2 = (x : ℂ) ^ 2 := by exact_mod_cast hx
    have h3 : ((Real.sqrt q : ℝ) : ℂ) ^ 2 = (q : ℂ) := by exact_mod_cast hs
    linear_combination -h2 + 4 * h3
  rw [this, norm_real, Real.norm_eq_abs]

/-- **Impurity is quantized.** Let `h ∈ ℤ[X]` be monic of degree `n` with all complex roots in
`|z| ≤ R`, `2R ≥ 1`, and `q ≥ 1`. Every root `τ` is pure, or non-real with
`1 ≤ 2|Im τ| (2R)^{(n−1)²+n−2}`, or real with `1 ≤ (|τ| − 2√q)(R + 2√q)(R² + 4q)^{n−1}`. -/
theorem impurity_is_quantized {h : ℤ[X]} (hh : h.Monic) {q : ℕ} (hq : 1 ≤ q) {R : ℝ}
    (hR1 : 1 ≤ 2 * R) (hR : ∀ z ∈ (toC h).roots, ‖z‖ ≤ R) {τ : ℂ} (hτ : τ ∈ (toC h).roots) :
    IsPureTrace q τ ∨
      1 ≤ 2 * |τ.im| * (2 * R) ^ ((h.natDegree - 1) ^ 2 + (h.natDegree - 2)) ∨
      (τ.im = 0 ∧ 1 ≤ (|τ.re| - 2 * Real.sqrt q) * (R + 2 * Real.sqrt q) *
        (R ^ 2 + 4 * q) ^ (h.natDegree - 1)) := by
  by_cases him : τ.im = 0
  · by_cases hin : |τ.re| ≤ 2 * Real.sqrt q
    · exact Or.inl ⟨him, hin⟩
    push Not at hin
    refine Or.inr (Or.inr ⟨him, ?_⟩)
    have hτre : τ = (τ.re : ℂ) := Complex.ext (by simp) (by simp [him])
    have hsq0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
    have hτR : |τ.re| ≤ R := by
      have := hR τ hτ
      rwa [hτre, norm_real, Real.norm_eq_abs] at this
    rcases frobenius_collide_or_repel hh hq hR hτ with hedge | hrep
    · exfalso
      have h0 : ‖τ ^ 2 - 4 * (q : ℂ)‖ = 0 := by rw [hedge, sub_self, norm_zero]
      rw [hτre, norm_sq_sub_four_q_of_real] at h0
      have : (|τ.re| - 2 * Real.sqrt q) * (|τ.re| + 2 * Real.sqrt q) ≠ 0 :=
        mul_ne_zero (by linarith) (by linarith [abs_nonneg τ.re])
      exact this (abs_eq_zero.mp h0)
    · rw [hτre, norm_sq_sub_four_q_of_real,
        abs_of_pos (mul_pos (by linarith) (by linarith [abs_nonneg τ.re]))] at hrep
      have hpow : 0 ≤ (R ^ 2 + 4 * q) ^ (h.natDegree - 1) := by positivity
      calc (1 : ℝ) ≤ (|τ.re| - 2 * Real.sqrt q) * (|τ.re| + 2 * Real.sqrt q) *
            (R ^ 2 + 4 * q) ^ (h.natDegree - 1) := hrep
        _ ≤ (|τ.re| - 2 * Real.sqrt q) * (R + 2 * Real.sqrt q) *
            (R ^ 2 + 4 * q) ^ (h.natDegree - 1) := by
          refine mul_le_mul_of_nonneg_right ?_ hpow
          exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  · exact Or.inr (Or.inl (one_le_two_abs_im_mul_pow hh hR1 hR hτ him))

/-- **Near purity is purity.** If every root of a monic integer polynomial `h` (degree `n`, roots
in `|z| ≤ R`, `2R ≥ 1`, `q ≥ 1`) has `2|Im τ| < ε₀ = (2R)^{−((n−1)²+n−2)}` and
`|Re τ| < 2√q + ε₁`, `ε₁ = ((R + 2√q)(R² + 4q)^{n−1})⁻¹`, then every root is pure. -/
theorem isPureTrace_of_near {h : ℤ[X]} (hh : h.Monic) {q : ℕ} (hq : 1 ≤ q) {R : ℝ}
    (hR1 : 1 ≤ 2 * R) (hR : ∀ z ∈ (toC h).roots, ‖z‖ ≤ R)
    (hnear : ∀ τ ∈ (toC h).roots,
      2 * |τ.im| < ((2 * R) ^ ((h.natDegree - 1) ^ 2 + (h.natDegree - 2)))⁻¹ ∧
      |τ.re| < 2 * Real.sqrt q +
        ((R + 2 * Real.sqrt q) * (R ^ 2 + 4 * q) ^ (h.natDegree - 1))⁻¹) :
    ∀ τ ∈ (toC h).roots, IsPureTrace q τ := by
  intro τ hτ
  obtain ⟨him, hre⟩ := hnear τ hτ
  have hR0 : 0 < 2 * R := by linarith
  have hsq0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  rcases impurity_is_quantized hh hq hR1 hR hτ with hp | hi | ⟨_, hr⟩
  · exact hp
  · have hpos : 0 < (2 * R) ^ ((h.natDegree - 1) ^ 2 + (h.natDegree - 2)) := pow_pos hR0 _
    have := mul_lt_mul_of_pos_right him hpos
    rw [inv_mul_cancel₀ hpos.ne'] at this
    linarith
  · have hpos : 0 < (R + 2 * Real.sqrt q) * (R ^ 2 + 4 * q) ^ (h.natDegree - 1) :=
      mul_pos (by linarith) (by positivity)
    have h' : |τ.re| - 2 * Real.sqrt q <
        ((R + 2 * Real.sqrt q) * (R ^ 2 + 4 * q) ^ (h.natDegree - 1))⁻¹ := by linarith
    have := mul_lt_mul_of_pos_right h' hpos
    rw [inv_mul_cancel₀ hpos.ne', ← mul_assoc] at this
    linarith

/-- **Discreteness is not a producer.** For every `q` and every degree `g ≥ 1` there is a monic
integer polynomial of degree `g` with an impure root: `X^{g−1}(X − m)`, `m = ⌊2√q⌋ + 1`. -/
theorem exists_impure_integral (q : ℕ) {g : ℕ} (hg : 1 ≤ g) :
    ∃ h : ℤ[X], h.Monic ∧ h.natDegree = g ∧ ∃ τ ∈ (toC h).roots, ¬ IsPureTrace q τ := by
  set m : ℕ := ⌊2 * Real.sqrt q⌋₊ + 1 with hm
  refine ⟨X ^ (g - 1) * (X - C (m : ℤ)), (monic_X_pow _).mul (monic_X_sub_C _), ?_,
    (m : ℂ), ?_, ?_⟩
  · rw [natDegree_mul (pow_ne_zero _ X_ne_zero) (X_sub_C_ne_zero _), natDegree_X_pow,
      natDegree_X_sub_C]; omega
  · rw [mem_roots (toC_ne_zero ((monic_X_pow _).mul (monic_X_sub_C _)))]
    simp [toC]
  · rintro ⟨-, hle⟩
    have hlt : 2 * Real.sqrt q < m := by
      rw [hm]; push_cast; exact Nat.lt_floor_add_one _
    simp only [natCast_re, Nat.abs_cast] at hle
    linarith

end GaloisForLFunctions.ArithmeticDiscreteness
