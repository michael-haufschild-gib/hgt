import GaloisForLFunctions.RHTower.SiegelRealAxis
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
# Auxiliary facts for Siegel's theorem

* `exists_prod_one_sub_inv_ge`: for every `δ > 0` there is `C > 0` with
  `∏_{p | M} (1 − 1/p) ≥ C M^{−δ}` for all `M ≥ 1` (primes `p ≥ 2^{1/δ}` satisfy
  `1 − 1/p ≥ p^{−δ}`; the others contribute at least `2^{−P₀}`).
* `LFunction_one_pos`: `L(1, χ)` is a positive real number for a nontrivial quadratic character.
* `productChar_sq`: the product of two quadratic characters is quadratic.
* `LFunction_one_ge_of_productChar_eq_one`: if `χ₁χ` is principal (the two characters agree on
  integers prime to `N₁N`), then `L(1, χ) ≥ L(1, χ₁) ∏_{p | N₁N} (1 − 1/p)²`, by comparing the two
  L-functions at the common level `N₁N`.
* `chiFourChar`: the nontrivial quadratic character modulo `4`.
-/

open DirichletCharacter Complex

noncomputable section

namespace RHTower

/-- **Euler factors are not too small.** -/
theorem exists_prod_one_sub_inv_ge {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, M ≠ 0 →
      C * (M : ℝ) ^ (-δ) ≤ ∏ p ∈ M.primeFactors, (1 - (p : ℝ)⁻¹) := by
  classical
  set P₀ : ℕ := ⌈(2 : ℝ) ^ (1 / δ)⌉₊ with hP₀
  refine ⟨(1 / 2 : ℝ) ^ P₀, by positivity, fun M hM => ?_⟩
  have hfac : ∀ p ∈ M.primeFactors,
      (if p < P₀ then (1 / 2 : ℝ) else 1) * (p : ℝ) ^ (-δ) ≤ 1 - (p : ℝ)⁻¹ := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hhalf : (1 / 2 : ℝ) ≤ 1 - (p : ℝ)⁻¹ := by
      have : (p : ℝ)⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ hp0 (by norm_num)]; linarith
      linarith
    have hpow1 : (p : ℝ) ^ (-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
      (by linarith)
    split_ifs with h
    · nlinarith [Real.rpow_nonneg hp0.le (-δ)]
    · push Not at h
      have hpP : (2 : ℝ) ^ (1 / δ) ≤ p := (Nat.le_ceil _).trans (by exact_mod_cast h)
      have h2 : (2 : ℝ) ≤ (p : ℝ) ^ δ := by
        have := Real.rpow_le_rpow (by positivity) hpP hδ.le
        rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hδ.ne', Real.rpow_one] at this
      have : (p : ℝ) ^ (-δ) ≤ 1 / 2 := by
        rw [Real.rpow_neg hp0.le, ← one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith
  have hprod := Finset.prod_le_prod (fun p hp => by
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
      split_ifs <;> positivity) hfac
  rw [Finset.prod_mul_distrib, Finset.prod_ite] at hprod
  simp only [Finset.prod_const, one_pow, mul_one] at hprod
  have hcard : (M.primeFactors.filter (· < P₀)).card ≤ P₀ := by
    calc (M.primeFactors.filter (· < P₀)).card ≤ (Finset.range P₀).card := by
          apply Finset.card_le_card
          intro p hp
          simp only [Finset.mem_filter] at hp
          exact Finset.mem_range.mpr hp.2
      _ = P₀ := Finset.card_range P₀
  have hhalf : (1 / 2 : ℝ) ^ P₀ ≤ (1 / 2 : ℝ) ^ (M.primeFactors.filter (· < P₀)).card :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard
  have hrad : (M : ℝ) ^ (-δ) ≤ ∏ p ∈ M.primeFactors, (p : ℝ) ^ (-δ) := by
    rw [Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg _)]
    have hd : (∏ p ∈ M.primeFactors, (p : ℝ)) ≤ M := by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hM) (Nat.prod_primeFactors_dvd M)
      have h2 : ((∏ p ∈ M.primeFactors, p : ℕ) : ℝ) ≤ M := by exact_mod_cast this
      push_cast at h2
      exact h2
    have hpos : (0 : ℝ) < ∏ p ∈ M.primeFactors, (p : ℝ) := Finset.prod_pos fun p hp => by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    exact Real.rpow_le_rpow_of_nonpos hpos hd (by linarith)
  calc (1 / 2 : ℝ) ^ P₀ * (M : ℝ) ^ (-δ)
      ≤ (1 / 2 : ℝ) ^ (M.primeFactors.filter (· < P₀)).card
          * ∏ p ∈ M.primeFactors, (p : ℝ) ^ (-δ) :=
        mul_le_mul hhalf hrad (by positivity) (by positivity)
    _ ≤ ∏ p ∈ M.primeFactors, (1 - (p : ℝ)⁻¹) := hprod

variable {N₁ N : ℕ} [NeZero N₁] [NeZero N]

/-- `L(1, χ)` is a positive real number for a nontrivial quadratic character. -/
theorem LFunction_one_pos {χ : DirichletCharacter ℂ N} (hq : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    0 < (LFunction χ 1).re ∧ (LFunction χ 1).im = 0 := by
  refine ⟨?_, ?_⟩
  · have := LFunction_re_pos_of_no_zero hq hχ (β := 1) one_pos
      (fun σ h1 h2 => absurd h2 (not_lt.mpr h1)) le_rfl (by norm_num)
    simpa using this
  · simpa using LFunction_ofReal_im hq hχ (σ := 1) one_pos

omit [NeZero N₁] [NeZero N] in
lemma productChar_sq {χ₁ : DirichletCharacter ℂ N₁} {χ : DirichletCharacter ℂ N}
    (hq₁ : χ₁ ^ 2 = 1) (hq : χ ^ 2 = 1) : (productChar χ₁ χ) ^ 2 = 1 := by
  unfold productChar
  rw [mul_pow, ← map_pow, ← map_pow, hq₁, hq, map_one, map_one, one_mul]

/-- **The equivalent-character case.**  If `χ₁χ` is principal then
`L(1, χ) ≥ L(1, χ₁) ∏_{p | N₁N} (1 − 1/p)²`. -/
theorem LFunction_one_ge_of_productChar_eq_one {χ₁ : DirichletCharacter ℂ N₁}
    {χ : DirichletCharacter ℂ N} (hq₁ : χ₁ ^ 2 = 1) (hq : χ ^ 2 = 1) (h₁ : χ₁ ≠ 1) (hχ : χ ≠ 1)
    (h₁₂ : productChar χ₁ χ = 1) :
    (LFunction χ₁ 1).re * (∏ p ∈ (N₁ * N).primeFactors, (1 - (p : ℝ)⁻¹)) ^ 2
      ≤ (LFunction χ 1).re := by
  set χ₁' := changeLevel (dvd_mul_right N₁ N) χ₁ with hχ₁'
  set χ' := changeLevel (dvd_mul_left N N₁) χ with hχ'
  have hsq₁ : χ₁' * χ₁' = 1 := by
    rw [← sq, hχ₁', ← map_pow, hq₁, map_one]
  have heq : χ' = χ₁' := by
    have h : χ₁' * χ' = 1 := h₁₂
    calc χ' = χ₁' * χ₁' * χ' := by rw [hsq₁, one_mul]
      _ = χ₁' * (χ₁' * χ') := by rw [mul_assoc]
      _ = χ₁' := by rw [h, mul_one]
  have hL : LFunction χ 1 * ∏ p ∈ (N₁ * N).primeFactors, (1 - χ p * (p : ℂ) ^ (-(1 : ℂ)))
      = LFunction χ₁ 1 * ∏ p ∈ (N₁ * N).primeFactors, (1 - χ₁ p * (p : ℂ) ^ (-(1 : ℂ))) := by
    rw [← LFunction_changeLevel (dvd_mul_left N N₁) χ (Or.inl hχ),
      ← LFunction_changeLevel (dvd_mul_right N₁ N) χ₁ (Or.inl h₁)]
    exact congrArg (fun ψ => LFunction ψ 1) heq
  -- norms of the Euler factors
  set S := (N₁ * N).primeFactors with hS
  have hfac_le : ∀ (ψ : ∀ p : ℕ, ℂ), (∀ p, ‖ψ p‖ ≤ 1) →
      ‖∏ p ∈ S, (1 - ψ p * (p : ℂ) ^ (-(1 : ℂ)))‖ ≤ ∏ p ∈ S, (1 + (p : ℝ)⁻¹) := by
    intro ψ hψ
    rw [norm_prod]
    refine Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p hp => ?_
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul, show ((p : ℂ)) ^ (-(1 : ℂ)) = (((p : ℝ)⁻¹ : ℝ) : ℂ) by
      rw [Complex.cpow_neg_one]; push_cast; rfl, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hp0)]
    have := hψ p
    nlinarith [inv_pos.mpr hp0]
  have hfac_ge : ∀ (ψ : ∀ p : ℕ, ℂ), (∀ p, ‖ψ p‖ ≤ 1) →
      ∏ p ∈ S, (1 - (p : ℝ)⁻¹) ≤ ‖∏ p ∈ S, (1 - ψ p * (p : ℂ) ^ (-(1 : ℂ)))‖ := by
    intro ψ hψ
    rw [norm_prod]
    refine Finset.prod_le_prod (fun p hp => ?_) fun p hp => ?_
    · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have : (p : ℝ)⁻¹ ≤ 1 / 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      linarith
    · have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
      have hcp : ((p : ℂ)) ^ (-(1 : ℂ)) = (((p : ℝ)⁻¹ : ℝ) : ℂ) := by
        rw [Complex.cpow_neg_one]; push_cast; rfl
      rw [hcp]
      have h := norm_sub_norm_le (1 : ℂ) (ψ p * (((p : ℝ)⁻¹ : ℝ) : ℂ))
      rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hp0)] at h
      have := hψ p
      nlinarith [inv_pos.mpr hp0]
  have hn₁ : ∀ p : ℕ, ‖χ₁ (p : ZMod N₁)‖ ≤ 1 := fun p => χ₁.norm_le_one _
  have hn : ∀ p : ℕ, ‖χ (p : ZMod N)‖ ≤ 1 := fun p => χ.norm_le_one _
  have hA := hfac_ge (fun p => χ₁ p) hn₁
  have hB := hfac_le (fun p => χ p) hn
  -- take norms in the identity
  have hnorm := congrArg norm hL
  rw [norm_mul, norm_mul] at hnorm
  obtain ⟨hpos, him⟩ := LFunction_one_pos hq hχ
  obtain ⟨hpos₁, him₁⟩ := LFunction_one_pos hq₁ h₁
  have hre : ‖LFunction χ 1‖ = (LFunction χ 1).re := by
    rw [← Complex.re_add_im (LFunction χ 1), him]; simp [abs_of_pos hpos]
  have hre₁ : ‖LFunction χ₁ 1‖ = (LFunction χ₁ 1).re := by
    rw [← Complex.re_add_im (LFunction χ₁ 1), him₁]; simp [abs_of_pos hpos₁]
  rw [hre, hre₁] at hnorm
  have hPpos : 0 ≤ ∏ p ∈ S, (1 - (p : ℝ)⁻¹) := Finset.prod_nonneg fun p hp => by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have : (p : ℝ)⁻¹ ≤ 1 := by rw [inv_le_one₀ (by linarith)]; linarith
    linarith
  have hprod : (∏ p ∈ S, (1 - (p : ℝ)⁻¹)) * ∏ p ∈ S, (1 + (p : ℝ)⁻¹) ≤ 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_one (fun p hp => ?_) fun p hp => ?_
    · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have : (p : ℝ)⁻¹ ≤ 1 := by rw [inv_le_one₀ (by linarith)]; linarith
      nlinarith [inv_pos.mpr (show (0:ℝ) < p by linarith)]
    · nlinarith [sq_nonneg ((p : ℝ)⁻¹)]
  -- L(1,χ₁)·P ≤ L(1,χ₁)·‖E₁‖ = L(1,χ)·‖E‖ ≤ L(1,χ)·∏(1 + 1/p), so L(1,χ₁)·P² ≤ L(1,χ)
  have hstep : (LFunction χ₁ 1).re * ∏ p ∈ S, (1 - (p : ℝ)⁻¹)
      ≤ (LFunction χ 1).re * ∏ p ∈ S, (1 + (p : ℝ)⁻¹) := by
    calc (LFunction χ₁ 1).re * ∏ p ∈ S, (1 - (p : ℝ)⁻¹)
        ≤ (LFunction χ₁ 1).re * ‖∏ p ∈ S, (1 - χ₁ p * (p : ℂ) ^ (-(1 : ℂ)))‖ :=
          mul_le_mul_of_nonneg_left hA hpos₁.le
      _ = (LFunction χ 1).re * ‖∏ p ∈ S, (1 - χ p * (p : ℂ) ^ (-(1 : ℂ)))‖ := hnorm.symm
      _ ≤ (LFunction χ 1).re * ∏ p ∈ S, (1 + (p : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left hB hpos.le
  have hPle : ∏ p ∈ S, (1 - (p : ℝ)⁻¹) ≤ 1 := by
    have hQ : 1 ≤ ∏ p ∈ S, (1 + (p : ℝ)⁻¹) := by
      calc (1 : ℝ) = ∏ p ∈ S, (1 : ℝ) := by simp
        _ ≤ ∏ p ∈ S, (1 + (p : ℝ)⁻¹) := Finset.prod_le_prod (fun _ _ => zero_le_one)
            fun p _ => by
              have : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
              linarith
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hstep hPpos]

/-- The nontrivial quadratic character modulo `4`, with complex values. -/
def chiFourChar : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

lemma chiFour_sq : chiFourChar ^ 2 = 1 :=
  MulChar.isQuadratic_iff_sq_eq_one.mp (ZMod.isQuadratic_χ₄.comp _)

lemma chiFour_ne_one : chiFourChar ≠ 1 := by
  intro h
  have h3 : chiFourChar (3 : ZMod 4) = -1 := by
    rw [chiFourChar, MulChar.ringHomComp_apply, show (3 : ZMod 4) = ((3 : ℕ) : ZMod 4) by rfl,
      ZMod.χ₄_nat_three_mod_four (by norm_num)]
    simp
  have hu : IsUnit (3 : ZMod 4) := by decide
  rw [h, MulChar.one_apply hu] at h3
  norm_num at h3

end RHTower
