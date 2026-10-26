import GaloisForLFunctions.ArithmeticPositiveDuality.GramSpaceOfAPositiveDefiniteFunction
import GaloisForLFunctions.ArithmeticPositiveDuality.AMautnerPhenomenonForTheAffineGroupOfQ

/-!
# A finite archimedean spectrum blinds the successor

Let `φ` be positive definite on `Aff(ℚ)` and suppose its dilation part is a positive combination of
finitely many archimedean characters,
`φ(x ↦ ux) = Σ_k c_k u^{iγ_k}` for `u > 0`, `c_k ≥ 0`, `γ_k` distinct
(a truncated zero sum of Weil's explicit formula has this shape).

**Theorem** (`extension_of_finite_archimedean`). There are `α_k ∈ [0, c_k]` with
`φ(x ↦ ux + b) = Σ_k α_k u^{iγ_k}` for `b ≠ 0`, `u > 0`: on `u > 0`, `φ` is the canonical extension
`archExtension`, the translation-invariant state `Σ_k α_k |slope|^{iγ_k}` plus the state
`Σ_k (c_k − α_k)|slope|^{iγ_k}` induced from the dilations, and every such choice is positive
definite (`isPosDefOnGroup_archExtension`). In particular the successor is blind:
`φ(x ↦ x + b) = α` for `b ≠ 0`, `0 ≤ α ≤ φ(1)` (`successor_blind_of_finite_archimedean`).

Mechanism, in the pre-Hilbert space of `φ`:
* **Eigenvectors.** For a prime `p` with distinct `p^{iγ_k}`, the Lagrange polynomials `L_k` give
  finite vectors `ξ_k = L_k(π(x ↦ px))δ_1` with `⟪ξ_k, ξ_l⟫ = c_kδ_{kl}`, `Σ_k ξ_k = δ_1`, and
  `π(x ↦ ux)ξ_k = u^{iγ_k}ξ_k` up to null vectors.
* **Covariance.** `m_{kl}(b) = ⟪ξ_k, π(x ↦ x + b)ξ_l⟫` obeys `m_{kl}(ub) = u^{i(γ_k−γ_l)}m_{kl}(b)`;
  the diagonal coefficients are constant on `b > 0`, and the constant is real (block doubling).
* **Orthogonality.** For `k ≠ l` and `r ∈ {2, 3}` with `r^{i(γ_k−γ_l)} ≠ 1`, the vectors
  `π(rnβ)ξ_l − π(nβ)ξ_l`, `N ≤ n < 2N`, are pairwise orthogonal of equal length, while each has
  inner product of modulus `|r^{i(γ_k−γ_l)} − 1|·|m_{kl}(β)|` with `ξ_k`; Bessel's inequality
  forces `m_{kl}(β) = 0`.

So positive-definite carriers of finitely many critical zeros on the affine group of `ℚ` are
exactly the two trivial constructions, translation-invariant and induced: their successor
coordinates see nothing.
-/

open Complex Finset Polynomial
open scoped Real

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-! ### Archimedean characters -/

/-- The archimedean character `u ↦ u^{iγ}`. -/
def archChar (γ : ℝ) (u : ℚ) : ℂ := cexp (I * γ * Real.log u)

theorem archChar_mul (γ : ℝ) {u v : ℚ} (hu : 0 < u) (hv : 0 < v) :
    archChar γ (u * v) = archChar γ u * archChar γ v := by
  have hu' : (u : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  simp only [archChar, Rat.cast_mul, Real.log_mul hu' hv', ofReal_add, mul_add, Complex.exp_add]

theorem archChar_one (γ : ℝ) : archChar γ 1 = 1 := by simp [archChar]

theorem norm_archChar (γ : ℝ) (u : ℚ) : ‖archChar γ u‖ = 1 := by
  rw [archChar, show I * γ * Real.log u = ((γ * Real.log u : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

theorem archChar_mul_star (γ : ℝ) (u : ℚ) : archChar γ u * star (archChar γ u) = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_archChar]; simp

theorem archChar_inv (γ : ℝ) {u : ℚ} (hu : 0 < u) : archChar γ u⁻¹ = star (archChar γ u) := by
  have h := archChar_mul γ hu (inv_pos.mpr hu)
  rw [mul_inv_cancel₀ hu.ne', archChar_one] at h
  have h2 := archChar_mul_star γ u
  have hne : archChar γ u ≠ 0 := by
    intro h0; have := norm_archChar γ u; rw [h0, norm_zero] at this; exact zero_ne_one this
  exact mul_left_cancel₀ hne (h.symm.trans h2.symm)

theorem archChar_pow (γ : ℝ) {u : ℚ} (hu : 0 < u) (n : ℕ) :
    archChar γ (u ^ n) = archChar γ u ^ n := by
  induction n with
  | zero => simp [archChar_one]
  | succ n ih => rw [pow_succ, archChar_mul γ (pow_pos hu n) hu, ih, pow_succ]

theorem archChar_sub (a b : ℝ) (u : ℚ) :
    archChar (a - b) u = archChar a u * star (archChar b u) := by
  rw [Complex.star_def, archChar, archChar, archChar, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast; ring

/-- `δ log p, δ log q ∈ 2πℤ` for distinct primes `p, q` forces `δ = 0`. -/
theorem eq_zero_of_archChar_eq_one {δ : ℝ} {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h1 : archChar δ p = 1) (h2 : archChar δ q = 1) : δ = 0 := by
  have hcoord : ∀ r : ℕ, r.Prime → archChar δ r = 1 → ∃ n : ℤ, δ * Real.log r = 2 * π * n := by
    intro r _ h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
    refine ⟨n, ?_⟩
    have hr : ((r : ℚ) : ℝ) = (r : ℝ) := Rat.cast_natCast r
    rw [hr] at hn
    have h' : ((δ * Real.log r : ℝ) : ℂ) * I = ((2 * π * n : ℝ) : ℂ) * I := by
      simp only [Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_ofNat]
      linear_combination hn
    exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h'
  obtain ⟨a, ha⟩ := hcoord p hp h1
  obtain ⟨b, hb⟩ := hcoord q hq h2
  by_contra hδ
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hπ : (0 : ℝ) < 2 * π := by positivity
  have hab : (a : ℝ) * Real.log q = b * Real.log p := by
    have : 2 * π * ((a : ℝ) * Real.log q) = 2 * π * (b * Real.log p) := by
      calc 2 * π * ((a : ℝ) * Real.log q) = (2 * π * a) * Real.log q := by ring
        _ = δ * Real.log p * Real.log q := by rw [← ha]
        _ = δ * Real.log q * Real.log p := by ring
        _ = 2 * π * b * Real.log p := by rw [hb]
        _ = 2 * π * (b * Real.log p) := by ring
    exact mul_left_cancel₀ hπ.ne' this
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Int.cast_zero, mul_zero] at ha
    rcases mul_eq_zero.mp ha with h | h
    · exact hδ h
    · exact hlp.ne' h
  have habs : (a.natAbs : ℝ) * Real.log q = b.natAbs * Real.log p := by
    have := congrArg abs hab
    rw [abs_mul, abs_mul, abs_of_pos hlp, abs_of_pos hlq] at this
    rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
    exact this
  have hpow : ((q ^ a.natAbs : ℕ) : ℝ) = ((p ^ b.natAbs : ℕ) : ℝ) := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by have := hq.pos; positivity))
      (Set.mem_Ioi.mpr (by have := hp.pos; positivity))
    push_cast
    rw [Real.log_pow, Real.log_pow, habs]
  have hnat : q ^ a.natAbs = p ^ b.natAbs := by exact_mod_cast hpow
  have hdvd : q ∣ p ^ b.natAbs := hnat ▸ dvd_pow_self q (Int.natAbs_ne_zero.mpr ha0)
  have := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hdvd)
  exact hpq this.symm

/-- A prime separating finitely many distinct archimedean characters. -/
theorem exists_prime_archChar_injective {K : ℕ} (γ : Fin K → ℝ) (hγ : Function.Injective γ) :
    ∃ p : ℕ, p.Prime ∧ Function.Injective fun k => archChar (γ k) p := by
  set S : Fin K × Fin K → Set ℕ := fun kl =>
    {p | p.Prime ∧ kl.1 ≠ kl.2 ∧ archChar (γ kl.1 - γ kl.2) p = 1} with hS
  have hsub : ∀ kl, (S kl).Subsingleton := by
    rintro ⟨k, l⟩ p ⟨hp, hkl, h1⟩ q ⟨hq, -, h2⟩
    by_contra hpq
    have := eq_zero_of_archChar_eq_one hp hq hpq h1 h2
    exact hkl (hγ (sub_eq_zero.mp this))
  have hfin : (⋃ kl, S kl).Finite := Set.finite_iUnion fun kl => (hsub kl).finite
  obtain ⟨p, hp, hpS⟩ := (Nat.infinite_setOf_prime.sdiff hfin).nonempty
  refine ⟨p, hp, fun k l hkl => ?_⟩
  by_contra hne
  apply hpS
  refine Set.mem_iUnion.mpr ⟨(k, l), hp, hne, ?_⟩
  simp only at hkl
  rw [archChar_sub, hkl, archChar_mul_star]

/-! ### Polynomial vectors in the pre-Hilbert space -/

section Vectors

variable (Φ : PosDefFn AffineGroupQ) (pu : ℚˣ)

/-- `P(π(x ↦ px))δ_1 = Σ_n P_n δ_{x ↦ pⁿx}`. -/
def polyVec (P : ℂ[X]) : PreGNS Φ :=
  ∑ n ∈ P.support, P.coeff n • gnsVec Φ (dilation (pu ^ n))

theorem polyVec_eq_sum (P : ℂ[X]) :
    polyVec Φ pu P = P.sum fun n a => a • gnsVec Φ (dilation (pu ^ n)) := by
  rw [Polynomial.sum_def]; rfl

theorem polyVec_add (P Q : ℂ[X]) : polyVec Φ pu (P + Q) = polyVec Φ pu P + polyVec Φ pu Q := by
  rw [polyVec_eq_sum, polyVec_eq_sum, polyVec_eq_sum,
    Polynomial.sum_add_index P Q (fun n a => a • gnsVec Φ (dilation (pu ^ n)))
      (fun n => zero_smul ℂ _) (fun n a b => add_smul a b _)]

theorem polyVec_zero : polyVec Φ pu 0 = 0 := by simp [polyVec]

theorem polyVec_finset_sum {ι : Type*} (s : Finset ι) (P : ι → ℂ[X]) :
    polyVec Φ pu (∑ i ∈ s, P i) = ∑ i ∈ s, polyVec Φ pu (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polyVec_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, polyVec_add, ih]

theorem polyVec_one : polyVec Φ pu 1 = gnsVec Φ 1 := by
  rw [polyVec_eq_sum, ← Polynomial.C_1, Polynomial.sum_C_index (by simp), one_smul, pow_zero,
    map_one]

end Vectors

section Spectral

variable {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ) {K : ℕ} (γ : Fin K → ℝ) (c : Fin K → ℝ)
  (hf : ∀ u : ℚˣ, 0 < (u : ℚ) → φ (dilation u) = ∑ k, (c k : ℂ) * archChar (γ k) u)
  {pu : ℚˣ} (hpu : 0 < (pu : ℚ))
include hf hpu

/-- **The spectral form of polynomial vectors.**
`⟪π(x ↦ ux)P(π_p)δ_1, Q(π_p)δ_1⟫ = Σ_k c_k conj(u^{iγ_k}) conj(P(z_k)) Q(z_k)`,
`z_k = p^{iγ_k}`. -/
theorem inner_translate_polyVec (u : ℚˣ) (hu : 0 < (u : ℚ)) (P Q : ℂ[X]) :
    inner ℂ (gnsTranslate ⟨φ, hφ⟩ (dilation u) (polyVec ⟨φ, hφ⟩ pu P)) (polyVec ⟨φ, hφ⟩ pu Q) =
      ∑ k, (c k : ℂ) * star (archChar (γ k) u) * star (P.eval (archChar (γ k) pu)) *
        Q.eval (archChar (γ k) pu) := by
  set Φ : PosDefFn AffineGroupQ := ⟨φ, hφ⟩
  set z : Fin K → ℂ := fun k => archChar (γ k) pu with hz
  have hentry : ∀ n m : ℕ, inner ℂ (gnsTranslate Φ (dilation u) (gnsVec Φ (dilation (pu ^ n))))
      (gnsVec Φ (dilation (pu ^ m))) =
        ∑ k, (c k : ℂ) * star (archChar (γ k) u) * star (z k) ^ n * z k ^ m := by
    intro n m
    rw [gnsTranslate_gnsVec, inner_gnsVec]
    show φ ((dilation u * dilation (pu ^ n))⁻¹ * dilation (pu ^ m)) = _
    rw [← map_mul, ← map_inv, ← map_mul]
    have hw : 0 < (((u * pu ^ n)⁻¹ * pu ^ m : ℚˣ) : ℚ) := by
      push_cast; positivity
    rw [hf _ hw]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hun : 0 < ((u : ℚ) * (pu : ℚ) ^ n) := by positivity
    push_cast
    rw [archChar_mul _ (inv_pos.mpr hun) (pow_pos hpu m), archChar_inv _ hun,
      archChar_mul _ hu (pow_pos hpu n), archChar_pow _ hpu, archChar_pow _ hpu, star_mul,
      star_pow]
    ring
  have hbil : inner ℂ (gnsTranslate Φ (dilation u) (polyVec Φ pu P)) (polyVec Φ pu Q) =
      ∑ n ∈ P.support, ∑ m ∈ Q.support, star (P.coeff n) * Q.coeff m *
        inner ℂ (gnsTranslate Φ (dilation u) (gnsVec Φ (dilation (pu ^ n))))
          (gnsVec Φ (dilation (pu ^ m))) := by
    unfold polyVec
    rw [map_sum, sum_inner]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_smul, inner_smul_left, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [inner_smul_right, Complex.star_def]
    ring
  rw [hbil]
  simp_rw [hentry]
  calc ∑ n ∈ P.support, ∑ m ∈ Q.support, star (P.coeff n) * Q.coeff m *
        ∑ k, (c k : ℂ) * star (archChar (γ k) u) * star (z k) ^ n * z k ^ m
      = ∑ n ∈ P.support, ∑ m ∈ Q.support, ∑ k, (c k : ℂ) * star (archChar (γ k) u) *
          (star (P.coeff n) * star (z k) ^ n * (Q.coeff m * z k ^ m)) := by
        refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = ∑ n ∈ P.support, ∑ k, ∑ m ∈ Q.support, (c k : ℂ) * star (archChar (γ k) u) *
          (star (P.coeff n) * star (z k) ^ n * (Q.coeff m * z k ^ m)) :=
        Finset.sum_congr rfl fun n _ => Finset.sum_comm
    _ = ∑ k, ∑ n ∈ P.support, ∑ m ∈ Q.support, (c k : ℂ) * star (archChar (γ k) u) *
          (star (P.coeff n) * star (z k) ^ n * (Q.coeff m * z k ^ m)) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum, Polynomial.sum_def,
          Polynomial.sum_def, star_sum, mul_assoc ((c k : ℂ) * star (archChar (γ k) u)),
          Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [star_mul, star_pow]
        ring

theorem inner_polyVec (P Q : ℂ[X]) :
    inner ℂ (polyVec ⟨φ, hφ⟩ pu P) (polyVec ⟨φ, hφ⟩ pu Q) =
      ∑ k, (c k : ℂ) * star (P.eval (archChar (γ k) pu)) * Q.eval (archChar (γ k) pu) := by
  have h := inner_translate_polyVec hφ γ c hf hpu 1 (by norm_num) P Q
  rw [map_one, gnsTranslate_one] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show ((1 : ℚˣ) : ℚ) = 1 from rfl, archChar_one, star_one, mul_one]

end Spectral

/-! ### Null vectors and the doubling lemma -/

section General

variable (Φ : PosDefFn AffineGroupQ)

theorem inner_eq_zero_of_inner_self {v : PreGNS Φ} (hv : inner ℂ v v = 0) (y : PreGNS Φ) :
    inner ℂ v y = 0 := by
  have hn : ‖v‖ = 0 := by rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), hv]; simp
  have := norm_inner_le_norm (𝕜 := ℂ) v y
  rw [hn, zero_mul] at this
  exact norm_le_zero_iff.mp this

theorem norm_gnsTranslate (a : AffineGroupQ) (x : PreGNS Φ) : ‖gnsTranslate Φ a x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) x, inner_gnsTranslate]

theorem inner_gnsTranslate_right (a : AffineGroupQ) (x y : PreGNS Φ) :
    inner ℂ x (gnsTranslate Φ a y) = inner ℂ (gnsTranslate Φ a⁻¹ x) y := by
  rw [inner_gnsTranslate_left, inv_inv]

/-- `⟪π(x+a)u, π(x+b)v⟫ = ⟪u, π(x + (b − a))v⟫`. -/
theorem inner_translate_translate (a b : ℚ) (x y : PreGNS Φ) :
    inner ℂ (gnsTranslate Φ (translation a) x) (gnsTranslate Φ (translation b) y) =
      inner ℂ x (gnsTranslate Φ (translation (b - a)) y) := by
  rw [inner_gnsTranslate_left, ← gnsTranslate_mul, translation_inv_mul]

/-- **Block doubling.** If `⟪x, π(x + b)x⟫ = α` for every `b > 0`, then `α` is real and
`|α| ≤ Re α`: the averages `A_{k+1} = (A_k + π(2^k)A_k)/2` keep `⟪A_k, π(2^k)A_k⟫ = α` while
`‖A_k‖² → Re α`. -/
theorem const_successor_real (x : PreGNS Φ) (α : ℂ)
    (h : ∀ b : ℚ, 0 < b → inner ℂ x (gnsTranslate Φ (translation b) x) = α) :
    α.im = 0 ∧ 0 ≤ α.re := by
  set A : ℕ → PreGNS Φ := fun k => Nat.rec x (fun k Ak =>
    (1 / 2 : ℂ) • (Ak + gnsTranslate Φ (translation ((2 : ℚ) ^ k)) Ak)) k with hA
  have hA0 : A 0 = x := rfl
  have hAs : ∀ k, A (k + 1) =
      (1 / 2 : ℂ) • (A k + gnsTranslate Φ (translation ((2 : ℚ) ^ k)) (A k)) := fun k => rfl
  have hshift : ∀ (y : PreGNS Φ) (b c : ℚ), gnsTranslate Φ (translation b)
      (gnsTranslate Φ (translation c) y) = gnsTranslate Φ (translation (b + c)) y := by
    intro y b c; rw [← gnsTranslate_mul, ← translation_add]
  have hQ : ∀ k, ∀ b : ℚ, (2 : ℚ) ^ k ≤ b →
      inner ℂ (A k) (gnsTranslate Φ (translation b) (A k)) = α := by
    intro k
    induction k with
    | zero => intro b hb; exact h b (by linarith [hb, show (0 : ℚ) < 2 ^ 0 by norm_num])
    | succ k ih =>
      intro b hb
      have hc : (0 : ℚ) < 2 ^ k := by positivity
      have h2 : (2 : ℚ) ^ (k + 1) = 2 * 2 ^ k := by ring
      have h2c : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
      rw [hAs, map_smul, inner_smul_left, inner_smul_right, map_add, inner_add_left,
        inner_add_right, inner_add_right, hshift, inner_translate_translate, inner_translate_translate,
        ih b (by linarith), ih _ (by linarith), ih _ (by linarith), ih _ (by linarith), h2c]
      ring
  have hs : ∀ k, (inner ℂ (A k) (A k)).re = α.re + ((inner ℂ x x).re - α.re) / 2 ^ k := by
    intro k
    induction k with
    | zero => simp [hA0]
    | succ k ih =>
      have hα := hQ k _ le_rfl
      have hα' : inner ℂ (gnsTranslate Φ (translation ((2 : ℚ) ^ k)) (A k)) (A k) = star α := by
        rw [← inner_conj_symm, hα]; rfl
      have hTT : inner ℂ (gnsTranslate Φ (translation ((2 : ℚ) ^ k)) (A k))
          (gnsTranslate Φ (translation ((2 : ℚ) ^ k)) (A k)) = inner ℂ (A k) (A k) :=
        inner_gnsTranslate Φ _ _ _
      rw [hAs, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
        inner_add_right, hα, hα', hTT]
      simp only [Complex.mul_re, Complex.add_re, Complex.star_def, Complex.conj_re,
        map_div₀, map_one, map_ofNat]
      rw [ih]
      norm_num
      ring
  -- `|α| ≤ ‖A_k‖² → Re α`
  have hle : ∀ k, ‖α‖ ≤ α.re + ((inner ℂ x x).re - α.re) / 2 ^ k := by
    intro k
    rw [← hs k, ← hQ k _ le_rfl]
    calc ‖inner ℂ (A k) (gnsTranslate Φ (translation ((2 : ℚ) ^ k)) (A k))‖
        ≤ ‖A k‖ * ‖gnsTranslate Φ (translation ((2 : ℚ) ^ k)) (A k)‖ := norm_inner_le_norm _ _
      _ = ‖A k‖ ^ 2 := by rw [norm_gnsTranslate]; ring
      _ = (inner ℂ (A k) (A k)).re := norm_sq_eq_re_inner (𝕜 := ℂ) _
  have hlim : ‖α‖ ≤ α.re := by
    by_contra hcon
    push Not at hcon
    set D := (inner ℂ x x).re - α.re
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (D / (‖α‖ - α.re)) (by norm_num : (1 : ℝ) < 2)
    have hpos : 0 < ‖α‖ - α.re := by linarith
    have h1 := hle k
    have h2 : D / 2 ^ k < ‖α‖ - α.re := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hpos] at hk
      linarith
    linarith
  have hre := Complex.re_le_norm α
  have him : α.im = 0 := by
    have h1 : ‖α‖ ^ 2 = α.re ^ 2 + α.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    nlinarith [norm_nonneg α, sq_nonneg α.im]
  exact ⟨him, (norm_nonneg α).trans hlim⟩

end General

/-! ### Eigenvectors and successor coefficients -/

section Blind

variable {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ) {K : ℕ} (γ : Fin K → ℝ) (c : Fin K → ℝ)
  (hf : ∀ u : ℚˣ, 0 < (u : ℚ) → φ (dilation u) = ∑ k, (c k : ℂ) * archChar (γ k) u)
  {pu : ℚˣ} (hpu : 0 < (pu : ℚ)) (hz : Function.Injective fun k => archChar (γ k) pu)

/-- The eigenvector `ξ_k = L_k(π_p)δ_1`, `L_k` the Lagrange polynomial at `z_j = p^{iγ_j}`. -/
def eigVec (pu : ℚˣ) (k : Fin K) : PreGNS ⟨φ, hφ⟩ :=
  polyVec ⟨φ, hφ⟩ pu (Lagrange.basis Finset.univ (fun j => archChar (γ j) pu) k)

/-- The successor coefficient `m_{kl}(b) = ⟪ξ_k, π(x ↦ x + b)ξ_l⟫`. -/
def succCoeff (pu : ℚˣ) (k l : Fin K) (b : ℚ) : ℂ :=
  inner ℂ (eigVec hφ γ pu k) (gnsTranslate ⟨φ, hφ⟩ (translation b) (eigVec hφ γ pu l))

include hz in
theorem eval_lagrange (k j : Fin K) :
    (Lagrange.basis Finset.univ (fun j => archChar (γ j) pu) k).eval (archChar (γ j) pu) =
      if j = k then 1 else 0 := by
  split_ifs with h
  · subst h
    exact Lagrange.eval_basis_self (v := fun j => archChar (γ j) pu) (s := Finset.univ) hz.injOn
      (Finset.mem_univ j)
  · exact Lagrange.eval_basis_of_ne (v := fun j => archChar (γ j) pu) (s := Finset.univ)
      (Ne.symm h) (Finset.mem_univ j)

include hf hpu hz in
theorem inner_translate_eigVec (u : ℚˣ) (hu : 0 < (u : ℚ)) (k l : Fin K) :
    inner ℂ (gnsTranslate ⟨φ, hφ⟩ (dilation u) (eigVec hφ γ pu k)) (eigVec hφ γ pu l) =
      if k = l then (c k : ℂ) * star (archChar (γ k) u) else 0 := by
  rw [eigVec, eigVec, inner_translate_polyVec hφ γ c hf hpu u hu]
  simp only [eval_lagrange γ hz]
  split_ifs with hkl
  · subst hkl
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
    simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = k
    · subst hj; simp [hkl]
    · simp [hj]

include hf hpu hz in
theorem inner_eigVec (k l : Fin K) :
    inner ℂ (eigVec hφ γ pu k) (eigVec hφ γ pu l) = if k = l then (c k : ℂ) else 0 := by
  have h := inner_translate_eigVec hφ γ c hf hpu hz 1 (by norm_num) k l
  rw [map_one, gnsTranslate_one] at h
  rw [h]
  simp [archChar_one]

include hz in
theorem sum_eigVec (hK : 0 < K) : ∑ k, eigVec hφ γ pu k = gnsVec ⟨φ, hφ⟩ 1 := by
  unfold eigVec
  rw [← polyVec_finset_sum, Lagrange.sum_basis hz.injOn ⟨⟨0, hK⟩, Finset.mem_univ _⟩, polyVec_one]

include hf hpu hz in
/-- `π(x ↦ ux)ξ_k = u^{iγ_k}ξ_k` up to a null vector, seen from the left. -/
theorem inner_translate_eigVec_left (u : ℚˣ) (hu : 0 < (u : ℚ)) (k : Fin K)
    (y : PreGNS ⟨φ, hφ⟩) :
    inner ℂ (gnsTranslate ⟨φ, hφ⟩ (dilation u) (eigVec hφ γ pu k)) y =
      star (archChar (γ k) u) * inner ℂ (eigVec hφ γ pu k) y := by
  set ξ := eigVec hφ γ pu k
  set T := gnsTranslate ⟨φ, hφ⟩ (dilation u)
  set lam := archChar (γ k) u
  have h1 : inner ℂ (T ξ) (T ξ) = (c k : ℂ) := by
    rw [inner_gnsTranslate, inner_eigVec hφ γ c hf hpu hz, if_pos rfl]
  have h2 : inner ℂ (T ξ) ξ = (c k : ℂ) * star lam := by
    rw [inner_translate_eigVec hφ γ c hf hpu hz u hu, if_pos rfl]
  have h3 : inner ℂ ξ (T ξ) = (c k : ℂ) * lam := by
    rw [← inner_conj_symm, h2]; simp
  have h4 : inner ℂ ξ ξ = (c k : ℂ) := by rw [inner_eigVec hφ γ c hf hpu hz, if_pos rfl]
  have hll : lam * star lam = 1 := archChar_mul_star _ _
  have hnull : inner ℂ (T ξ - lam • ξ) (T ξ - lam • ξ) = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_left, inner_smul_right,
      inner_smul_left, inner_smul_right, h1, h2, h3, h4]
    simp only [← Complex.star_def]
    linear_combination (-(c k : ℂ)) * hll
  have := inner_eq_zero_of_inner_self _ hnull y
  rw [inner_sub_left, inner_smul_left, sub_eq_zero] at this
  rw [this]; rfl

include hf hpu hz in
theorem inner_translate_eigVec_right (u : ℚˣ) (hu : 0 < (u : ℚ)) (k : Fin K)
    (y : PreGNS ⟨φ, hφ⟩) :
    inner ℂ y (gnsTranslate ⟨φ, hφ⟩ (dilation u) (eigVec hφ γ pu k)) =
      archChar (γ k) u * inner ℂ y (eigVec hφ γ pu k) := by
  rw [← inner_conj_symm, inner_translate_eigVec_left hφ γ c hf hpu hz u hu, map_mul,
    inner_conj_symm]
  simp

include hf hpu hz in
/-- **Covariance.** `m_{kl}(ub) = u^{i(γ_k − γ_l)} m_{kl}(b)` for `u > 0`. -/
theorem succCoeff_mul (u : ℚˣ) (hu : 0 < (u : ℚ)) (k l : Fin K) (b : ℚ) :
    succCoeff hφ γ pu k l ((u : ℚ) * b) =
      archChar (γ k - γ l) u * succCoeff hφ γ pu k l b := by
  set Φ : PosDefFn AffineGroupQ := ⟨φ, hφ⟩
  have hu' : 0 < ((u⁻¹ : ℚˣ) : ℚ) := by rw [Units.val_inv_eq_inv_val]; exact inv_pos.mpr hu
  unfold succCoeff
  rw [← dilation_mul_translation_mul_inv, gnsTranslate_mul, gnsTranslate_mul,
    inner_gnsTranslate_right, ← map_inv,
    inner_translate_eigVec_left hφ γ c hf hpu hz _ hu', inner_gnsTranslate_right,
    inner_translate_eigVec_right hφ γ c hf hpu hz _ hu', inner_gnsTranslate_left, inv_inv,
    Units.val_inv_eq_inv_val, archChar_inv _ hu, archChar_inv _ hu, archChar_sub, star_star]
  ring

include hz in
theorem gnsVec_successor (hK : 0 < K) (b : ℚ) :
    φ (translation b) = ∑ k, ∑ l, succCoeff hφ γ pu k l b := by
  have h : φ (translation b) = inner ℂ (gnsVec ⟨φ, hφ⟩ 1)
      (gnsTranslate ⟨φ, hφ⟩ (translation b) (gnsVec ⟨φ, hφ⟩ 1)) := by
    rw [gnsTranslate_gnsVec, inner_gnsVec, inv_one, one_mul, mul_one]
  rw [h, ← sum_eigVec hφ γ hz hK, map_sum, sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_sum]
  rfl

end Blind

/-! ### Vanishing of the cross coefficients -/

theorem translation_inv' (a : ℚ) : (translation a)⁻¹ = translation (-a) := by
  have := translation_inv_mul a 0
  rwa [translation_zero, mul_one, zero_sub] at this

theorem archChar_zero (u : ℚ) : archChar 0 u = 1 := by simp [archChar]

section Offdiag

variable {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ) {K : ℕ} (γ : Fin K → ℝ) (c : Fin K → ℝ)
  (hc : ∀ k, 0 ≤ c k)
  (hf : ∀ u : ℚˣ, 0 < (u : ℚ) → φ (dilation u) = ∑ k, (c k : ℂ) * archChar (γ k) u)
  {pu : ℚˣ} (hpu : 0 < (pu : ℚ)) (hz : Function.Injective fun k => archChar (γ k) pu)

include hf hpu hz in
theorem succCoeff_pos (k : Fin K) (b : ℚ) (hb : 0 < b) :
    succCoeff hφ γ pu k k b = succCoeff hφ γ pu k k 1 := by
  have := succCoeff_mul hφ γ c hf hpu hz (Units.mk0 b hb.ne') hb k k 1
  rw [Units.val_mk0, mul_one, sub_self, archChar_zero, one_mul] at this
  exact this

theorem succCoeff_neg (k : Fin K) (b : ℚ) :
    succCoeff hφ γ pu k k b = star (succCoeff hφ γ pu k k (-b)) := by
  unfold succCoeff
  rw [← inner_conj_symm, inner_gnsTranslate_left, translation_inv']
  rfl

include hf hpu hz in
/-- The diagonal coefficients are one real constant off `0`. -/
theorem succCoeff_diag (l : Fin K) :
    ∃ α : ℝ, ∀ b : ℚ, b ≠ 0 → succCoeff hφ γ pu l l b = α := by
  set α := succCoeff hφ γ pu l l 1
  have hpos : ∀ b : ℚ, 0 < b → inner ℂ (eigVec hφ γ pu l)
      (gnsTranslate ⟨φ, hφ⟩ (translation b) (eigVec hφ γ pu l)) = α :=
    fun b hb => succCoeff_pos hφ γ c hf hpu hz l b hb
  obtain ⟨him, -⟩ := const_successor_real ⟨φ, hφ⟩ (eigVec hφ γ pu l) α hpos
  have hα : α = (α.re : ℂ) := Complex.ext (by simp) (by simp [him])
  refine ⟨α.re, fun b hb => ?_⟩
  rcases hb.lt_or_gt with hneg | hb'
  · rw [succCoeff_neg hφ γ l b, succCoeff_pos hφ γ c hf hpu hz l (-b) (by linarith)]
    show star α = _
    rw [hα]
    simp
  · rw [succCoeff_pos hφ γ c hf hpu hz l b hb']
    exact hα

include hf hpu hz in
/-- **The cross coefficients vanish**: `m_{kl}(β) = 0` for `k ≠ l`, `β > 0`. -/
theorem succCoeff_offdiag {k l : Fin K} (hkl : k ≠ l) (β : ℚ) (hβ : 0 < β) :
    succCoeff hφ γ pu k l β = 0 := by
  set Φ : PosDefFn AffineGroupQ := ⟨φ, hφ⟩
  set m := succCoeff hφ γ pu k l β with hm
  set ω : ℚ → ℂ := fun u => archChar (γ k - γ l) u with hω
  have hγ : γ k ≠ γ l := fun h => hkl (hz (by simp only [h]))
  obtain ⟨r, hr2, hr⟩ : ∃ r : ℕ, 2 ≤ r ∧ ω r ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hγ (sub_eq_zero.mp (eq_zero_of_archChar_eq_one Nat.prime_two Nat.prime_three
      (by norm_num) (by exact_mod_cast hcon 2 le_rfl) (by exact_mod_cast hcon 3 (by norm_num))))
  obtain ⟨α, hα⟩ := succCoeff_diag hφ γ c hf hpu hz l
  set ξl := eigVec hφ γ pu l
  set ξk := eigVec hφ γ pu k
  have hcl : inner ℂ ξl ξl = (c l : ℂ) := by rw [inner_eigVec hφ γ c hf hpu hz, if_pos rfl]
  have hpair : ∀ a b : ℚ, inner ℂ (gnsTranslate Φ (translation a) ξl)
      (gnsTranslate Φ (translation b) ξl) = if b - a = 0 then (c l : ℂ) else α := by
    intro a b
    rw [inner_translate_translate]
    split_ifs with h
    · rw [h, translation_zero, gnsTranslate_one, hcl]
    · exact hα _ h
  set e : ℕ → PreGNS Φ := fun n => gnsTranslate Φ (translation ((r : ℚ) * n * β)) ξl -
    gnsTranslate Φ (translation ((n : ℚ) * β)) ξl with he
  have hr0 : (2 : ℚ) ≤ r := by exact_mod_cast hr2
  -- pairwise orthogonality on `[N, 2N)`
  have horth : ∀ N n n' : ℕ, N ≤ n → n < 2 * N → N ≤ n' → n' < 2 * N → n ≠ n' →
      inner ℂ (e n) (e n') = 0 := by
    intro N n n' hn1 hn2 hn1' hn2' hne
    have hq1 : (N : ℚ) ≤ n := by exact_mod_cast hn1
    have hq2 : (n : ℚ) < 2 * N := by exact_mod_cast hn2
    have hq1' : (N : ℚ) ≤ n' := by exact_mod_cast hn1'
    have hq2' : (n' : ℚ) < 2 * N := by exact_mod_cast hn2'
    have hqne : (n : ℚ) ≠ n' := by exact_mod_cast hne
    have d1 : (r : ℚ) * n' * β - r * n * β ≠ 0 := by
      have : (r : ℚ) * n' * β - r * n * β = r * β * (n' - n) := by ring
      rw [this]
      exact mul_ne_zero (mul_ne_zero (by positivity) hβ.ne') (sub_ne_zero.mpr hqne.symm)
    have d2 : (n' : ℚ) * β - r * n * β ≠ 0 := by
      have : (n' : ℚ) < r * n := by nlinarith
      have : (n' : ℚ) * β < r * n * β := mul_lt_mul_of_pos_right this hβ
      linarith
    have d3 : (r : ℚ) * n' * β - n * β ≠ 0 := by
      have : (n : ℚ) < r * n' := by nlinarith
      have : (n : ℚ) * β < r * n' * β := mul_lt_mul_of_pos_right this hβ
      linarith
    have d4 : (n' : ℚ) * β - n * β ≠ 0 := by
      have : (n' : ℚ) * β - n * β = β * (n' - n) := by ring
      rw [this]
      exact mul_ne_zero hβ.ne' (sub_ne_zero.mpr hqne.symm)
    simp only [he, inner_sub_left, inner_sub_right, hpair, if_neg d1, if_neg d2, if_neg d3,
      if_neg d4]
    ring
  have hnorm : ∀ n : ℕ, 1 ≤ n → inner ℂ (e n) (e n) = 2 * ((c l : ℂ) - α) := by
    intro n hn
    have hq : (1 : ℚ) ≤ n := by exact_mod_cast hn
    have d2 : (n : ℚ) * β - r * n * β ≠ 0 := by
      have : (n : ℚ) * β < r * n * β := mul_lt_mul_of_pos_right (by nlinarith) hβ
      linarith
    have d3 : (r : ℚ) * n * β - n * β ≠ 0 := by
      have : (n : ℚ) * β < r * n * β := mul_lt_mul_of_pos_right (by nlinarith) hβ
      linarith
    simp only [he, inner_sub_left, inner_sub_right, hpair, sub_self, if_true, if_neg d2,
      if_neg d3]
    ring
  -- inner products with `ξ_k`
  have hω_abs : ∀ u : ℚ, ‖ω u‖ = 1 := fun u => norm_archChar _ _
  have hcov : ∀ n : ℕ, 1 ≤ n → succCoeff hφ γ pu k l ((n : ℚ) * β) = ω n * m := by
    intro n hn
    have hn0 : (0 : ℚ) < n := by exact_mod_cast hn
    have := succCoeff_mul hφ γ c hf hpu hz (Units.mk0 (n : ℚ) hn0.ne') hn0 k l β
    rwa [Units.val_mk0] at this
  have hcovr : ∀ n : ℕ, 1 ≤ n → succCoeff hφ γ pu k l ((r : ℚ) * n * β) = ω r * ω n * m := by
    intro n hn
    have hn0 : (0 : ℚ) < (r : ℚ) * n := by
      have : (1 : ℚ) ≤ n := by exact_mod_cast hn
      positivity
    have := succCoeff_mul hφ γ c hf hpu hz (Units.mk0 ((r : ℚ) * n) hn0.ne') hn0 k l β
    rw [Units.val_mk0] at this
    rw [this, archChar_mul _ (by positivity) (by exact_mod_cast hn : (0 : ℚ) < n)]
  have hinner : ∀ n : ℕ, 1 ≤ n → ‖inner ℂ (e n) ξk‖ = ‖ω r - 1‖ * ‖m‖ := by
    intro n hn
    have h1 : ∀ b : ℚ, inner ℂ (gnsTranslate Φ (translation b) ξl) ξk =
        star (succCoeff hφ γ pu k l b) := fun b => by
      rw [succCoeff, ← inner_conj_symm]; rfl
    rw [he, inner_sub_left, h1, h1, hcovr n hn, hcov n hn, ← star_sub, norm_star,
      show ω r * ω n * m - ω n * m = ω n * ((ω r - 1) * m) by ring, norm_mul, hω_abs,
      norm_mul, one_mul]
  -- Bessel
  have hD : 0 ≤ 2 * ((c l : ℝ) - α) := by
    have h := inner_self_nonneg (𝕜 := ℂ) (x := e 1)
    rw [hnorm 1 le_rfl] at h
    simpa using h
  have hωr : 0 < ‖ω r - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hr)
  rcases hD.lt_or_eq with hDpos | hD0
  · -- `N ‖ω r − 1‖² ‖m‖² ≤ D c_k` for every `N`
    have hbound : ∀ N : ℕ, 1 ≤ N →
        (N : ℝ) * (‖ω r - 1‖ * ‖m‖) ^ 2 ≤ 2 * ((c l : ℝ) - α) * c k := by
      intro N hN
      set D := 2 * ((c l : ℝ) - α)
      set s : ℝ := (Real.sqrt D)⁻¹
      have hs2 : s ^ 2 * D = 1 := by
        rw [inv_pow, Real.sq_sqrt hD]; field_simp
      set v : Fin N → PreGNS Φ := fun i => (s : ℂ) • e (N + i)
      have hv : Orthonormal ℂ v := by
        rw [orthonormal_iff_ite]
        intro i j
        simp only [v, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
        split_ifs with hij
        · subst hij
          rw [hnorm _ (by omega)]
          have : ((s : ℂ) * (s * (2 * ((c l : ℂ) - α)))) = ((s ^ 2 * D : ℝ) : ℂ) := by
            simp only [D]; push_cast; ring
          rw [this, hs2]; simp
        · rw [horth N (N + i) (N + j) (by omega) (by omega) (by omega) (by omega)
            (fun h => hij (Fin.ext (by omega)))]
          simp
      have hb := hv.sum_inner_products_le (s := Finset.univ) ξk
      have hterm : ∀ i : Fin N, ‖inner ℂ (v i) ξk‖ ^ 2 = s ^ 2 * (‖ω r - 1‖ * ‖m‖) ^ 2 := by
        intro i
        simp only [v, inner_smul_left, Complex.conj_ofReal, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, hinner _ (by omega : 1 ≤ N + (i : ℕ))]
        rw [mul_pow, sq_abs]
      simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
      have hk : ‖ξk‖ ^ 2 = c k := by
        rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_eigVec hφ γ c hf hpu hz, if_pos rfl]; simp
      rw [hk] at hb
      have hD' : 0 < D := hDpos
      have : (N : ℝ) * (‖ω r - 1‖ * ‖m‖) ^ 2 = (N * (s ^ 2 * (‖ω r - 1‖ * ‖m‖) ^ 2)) * D := by
        rw [show (N : ℝ) * (s ^ 2 * (‖ω r - 1‖ * ‖m‖) ^ 2) * D =
          N * (‖ω r - 1‖ * ‖m‖) ^ 2 * (s ^ 2 * D) by ring, hs2, mul_one]
      rw [this]
      calc (N * (s ^ 2 * (‖ω r - 1‖ * ‖m‖) ^ 2)) * D ≤ c k * D :=
            mul_le_mul_of_nonneg_right hb hD'.le
        _ = D * c k := mul_comm _ _
    by_contra hm0
    have hmpos : 0 < ‖m‖ := norm_pos_iff.mpr hm0
    have hA : 0 < (‖ω r - 1‖ * ‖m‖) ^ 2 := by positivity
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * ((c l : ℝ) - α) * c k / (‖ω r - 1‖ * ‖m‖) ^ 2)
    have h := hbound (N + 1) (by omega)
    rw [div_lt_iff₀ hA] at hN
    push_cast at h
    nlinarith
  · -- `D = 0`: the vectors are null
    have hnull : inner ℂ (e 1) (e 1) = 0 := by
      rw [hnorm 1 le_rfl]
      have : ((c l : ℂ) - α) = (((c l : ℝ) - α : ℝ) : ℂ) := by push_cast; ring
      rw [this, show (c l : ℝ) - α = 0 by linarith]
      simp
    have h0 := inner_eq_zero_of_inner_self Φ hnull ξk
    have := hinner 1 le_rfl
    rw [h0, norm_zero] at this
    have hm : ‖m‖ = 0 := by
      rcases mul_eq_zero.mp this.symm with h | h
      · exact absurd h hωr.ne'
      · exact h
    exact norm_eq_zero.mp hm

end Offdiag

/-! ### Blindness -/

/-- **A finite archimedean spectrum blinds the successor.** If `φ` is positive definite on
`Aff(ℚ)` and `φ(x ↦ ux) = Σ_k c_k u^{iγ_k}` for `u > 0` with `c_k ≥ 0` and distinct `γ_k`, then
`φ(x ↦ x + b) = α` for every `b ≠ 0`, with `0 ≤ α ≤ φ(1)`. -/
theorem successor_blind_of_finite_archimedean {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ)
    {K : ℕ} (γ : Fin K → ℝ) (hγ : Function.Injective γ) (c : Fin K → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hf : ∀ u : ℚˣ, 0 < (u : ℚ) → φ (dilation u) = ∑ k, (c k : ℂ) * archChar (γ k) u) :
    ∃ α : ℝ, 0 ≤ α ∧ α ≤ (φ 1).re ∧ ∀ b : ℚ, b ≠ 0 → φ (translation b) = α := by
  obtain ⟨r0, hr0, h0⟩ := hφ.map_one_eq
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    have h1 : φ 1 = 0 := by
      have := hf 1 (by norm_num)
      rw [map_one] at this
      simpa using this
    refine ⟨0, le_rfl, by rw [h1]; simp, fun b _ => ?_⟩
    have := hφ.normSq_le (translation b)
    rw [h1, Complex.zero_re] at this
    have hz : Complex.normSq (φ (translation b)) = 0 :=
      le_antisymm (by simpa using this) (Complex.normSq_nonneg _)
    rw [Complex.normSq_eq_zero.mp hz]; simp
  obtain ⟨p, hp, hpinj⟩ := exists_prime_archChar_injective γ hγ
  set pu : ℚˣ := Units.mk0 (p : ℚ) (by exact_mod_cast hp.ne_zero) with hpu_def
  have hpu : 0 < (pu : ℚ) := by
    rw [hpu_def, Units.val_mk0]; exact_mod_cast hp.pos
  have hz : Function.Injective fun k => archChar (γ k) pu := by
    rw [hpu_def, Units.val_mk0]; exact hpinj
  have hconst : ∀ b : ℚ, 0 < b → φ (translation b) = ∑ k, succCoeff hφ γ pu k k 1 := by
    intro b hb
    rw [gnsVec_successor hφ γ hz hK b]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k (fun l _ hlk =>
      succCoeff_offdiag hφ γ c hf hpu hz (Ne.symm hlk) b hb) (by simp)]
    exact succCoeff_pos hφ γ c hf hpu hz k b hb
  set α := ∑ k, succCoeff hφ γ pu k k 1 with hα_def
  obtain ⟨him, hre⟩ := const_successor_real ⟨φ, hφ⟩ (gnsVec ⟨φ, hφ⟩ 1) α (fun b hb => by
    rw [gnsTranslate_gnsVec, inner_gnsVec, inv_one, one_mul, mul_one]
    exact hconst b hb)
  have hα : α = (α.re : ℂ) := Complex.ext (by simp) (by simp [him])
  refine ⟨α.re, hre, ?_, fun b hb => ?_⟩
  · have h := hφ.normSq_le (translation 1)
    rw [hconst 1 one_pos, hα, Complex.normSq_ofReal, h0, Complex.ofReal_re] at h
    rw [h0, Complex.ofReal_re]
    nlinarith
  · rcases hb.lt_or_gt with hneg | hpos
    · have h := hφ.map_inv (translation (-b))
      rw [translation_inv', neg_neg, hconst (-b) (by linarith), hα] at h
      rw [h]; simp
    · rw [hconst b hpos, ← hα]


/-! ### The positive-definite extensions of a finite archimedean correlation -/

theorem IsPosDefOnGroup.add {G : Type*} [Group G] {φ ψ : G → ℂ} (hφ : IsPosDefOnGroup φ)
    (hψ : IsPosDefOnGroup ψ) : IsPosDefOnGroup fun g => φ g + ψ g := by
  intro N x c
  obtain ⟨r, hr, h⟩ := hφ N x c
  obtain ⟨s, hs, h'⟩ := hψ N x c
  refine ⟨r + s, add_nonneg hr hs, ?_⟩
  push_cast
  rw [← h, ← h', ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem archChar_abs_slope_inv_mul (γ : ℝ) (g h : AffineGroupQ) :
    archChar γ |affSlope (g⁻¹ * h)| =
      star (archChar γ |affSlope g|) * archChar γ |affSlope h| := by
  have hg : 0 < |affSlope g| := abs_pos.mpr (affSlope_ne_zero g)
  have hh : 0 < |affSlope h| := abs_pos.mpr (affSlope_ne_zero h)
  rw [affSlope_mul, affSlope_inv, abs_mul, abs_inv, archChar_mul _ (inv_pos.mpr hg) hh,
    archChar_inv _ hg]

/-- `g ↦ |slope g|^{iγ}` is positive definite: its Gram form is `|Σ_j c_j |slope x_j|^{iγ}|²`. -/
theorem isPosDefOnGroup_archChar_slope (γ : ℝ) :
    IsPosDefOnGroup fun g : AffineGroupQ => archChar γ |affSlope g| := by
  intro N x c
  refine ⟨Complex.normSq (∑ j, c j * archChar γ |affSlope (x j)|), Complex.normSq_nonneg _, ?_⟩
  rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  dsimp only
  rw [archChar_abs_slope_inv_mul, map_mul, Complex.star_def]
  ring

theorem IsPosDefOnGroup.const_mul' {G : Type*} [Group G] {φ : G → ℂ} (hφ : IsPosDefOnGroup φ)
    {a : ℝ} (ha : 0 ≤ a) : IsPosDefOnGroup fun g => (a : ℂ) * φ g := by
  intro N x c
  obtain ⟨r, hr, h⟩ := hφ N x c
  refine ⟨a * r, mul_nonneg ha hr, ?_⟩
  push_cast
  rw [← h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem isPosDefOnGroup_finset_sum {G : Type*} [Group G] {ι : Type*} (s : Finset ι)
    (f : ι → G → ℂ) (hf : ∀ i ∈ s, IsPosDefOnGroup (f i)) :
    IsPosDefOnGroup fun g => ∑ i ∈ s, f i g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro N x c
    exact ⟨0, le_rfl, by simp⟩
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- `g ↦ Σ_k a_k |slope g|^{iγ_k}` is positive definite for `a_k ≥ 0`. -/
theorem isPosDefOnGroup_archSlope {K : ℕ} (γ : Fin K → ℝ) (a : Fin K → ℝ) (ha : ∀ k, 0 ≤ a k) :
    IsPosDefOnGroup fun g : AffineGroupQ => ∑ k, (a k : ℂ) * archChar (γ k) |affSlope g| :=
  isPosDefOnGroup_finset_sum _ _ fun k _ => (isPosDefOnGroup_archChar_slope (γ k)).const_mul' (ha k)

/-- The dilations, as a subgroup of `Aff(ℚ)`. -/
def dilationRange : Subgroup AffineGroupQ := dilation.range

theorem mem_dilationRange_iff (g : AffineGroupQ) : g ∈ dilationRange ↔ affShift g = 0 := by
  constructor
  · rintro ⟨u, rfl⟩; exact affShift_dilation u
  · intro h
    refine ⟨Units.mk0 (affSlope g) (affSlope_ne_zero g), affine_ext ?_ ?_⟩
    · rw [affSlope_dilation]; rfl
    · rw [affShift_dilation, h]

/-- The canonical extension: a translation-invariant part `Σ α_k u^{iγ_k}` plus the part
`Σ (c_k − α_k)u^{iγ_k}` induced from the dilations. -/
def archExtension {K : ℕ} (γ : Fin K → ℝ) (c α : Fin K → ℝ) (g : AffineGroupQ) : ℂ :=
  ∑ k, (α k : ℂ) * archChar (γ k) |affSlope g| +
    extendFromSubgroup dilationRange
      (fun h => ∑ k, ((c k - α k : ℝ) : ℂ) * archChar (γ k) |affSlope (h : AffineGroupQ)|) g

theorem isPosDefOnGroup_archExtension {K : ℕ} (γ : Fin K → ℝ) (c α : Fin K → ℝ)
    (hα : ∀ k, 0 ≤ α k ∧ α k ≤ c k) : IsPosDefOnGroup (archExtension γ c α) :=
  (isPosDefOnGroup_archSlope γ α fun k => (hα k).1).add
    (isPosDefOnGroup_extendFromSubgroup
      ((isPosDefOnGroup_archSlope γ (fun k => c k - α k) fun k =>
        sub_nonneg.mpr (hα k).2).restrict dilationRange))

theorem archExtension_apply {K : ℕ} (γ : Fin K → ℝ) (c α : Fin K → ℝ) (b : ℚ) (u : ℚˣ)
    (hu : 0 < (u : ℚ)) :
    archExtension γ c α (translation b * dilation u) =
      ∑ k, ((if b = 0 then c k else α k : ℝ) : ℂ) * archChar (γ k) u := by
  have hslope : affSlope (translation b * dilation u) = u := by
    rw [affSlope_mul, affSlope_translation, affSlope_dilation, one_mul]
  have hshift : affShift (translation b * dilation u) = b := by
    rw [affShift_mul, affSlope_translation, affShift_dilation, affShift_translation]; ring
  unfold archExtension extendFromSubgroup
  rw [hslope, abs_of_pos hu]
  by_cases hb : b = 0
  · rw [dif_pos ((mem_dilationRange_iff _).mpr (by rw [hshift, hb])), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hslope, abs_of_pos hu, if_pos hb]
    push_cast; ring
  · rw [dif_neg (fun h => hb ((mem_dilationRange_iff _).mp h ▸ hshift.symm)), add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [if_neg hb]

/-- **The positive-definite extensions of a finite archimedean correlation.** If `φ` is positive
definite on `Aff(ℚ)` and `φ(x ↦ ux) = Σ_k c_k u^{iγ_k}` for `u > 0`, then there are
`α_k ∈ [0, c_k]` with `φ(x ↦ ux + b) = Σ_k α_k u^{iγ_k}` for `b ≠ 0` and `u > 0`: on `u > 0`,
`φ` is the canonical extension (`archExtension`), a translation-invariant state plus a state
induced from the dilations. -/
theorem extension_of_finite_archimedean {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ)
    {K : ℕ} (γ : Fin K → ℝ) (hγ : Function.Injective γ) (c : Fin K → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hf : ∀ u : ℚˣ, 0 < (u : ℚ) → φ (dilation u) = ∑ k, (c k : ℂ) * archChar (γ k) u) :
    ∃ α : Fin K → ℝ, (∀ k, 0 ≤ α k ∧ α k ≤ c k) ∧ ∀ (b : ℚ) (u : ℚˣ), 0 < (u : ℚ) →
      φ (translation b * dilation u) = archExtension γ c α (translation b * dilation u) := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    refine ⟨fun k => k.elim0, fun k => k.elim0, fun b u hu => ?_⟩
    have h1 : φ 1 = 0 := by
      have := hf 1 (by norm_num)
      rw [map_one] at this
      simpa using this
    rw [archExtension_apply _ _ _ b u hu]
    have := hφ.normSq_le (translation b * dilation u)
    rw [h1, Complex.zero_re] at this
    have hz : Complex.normSq (φ (translation b * dilation u)) = 0 :=
      le_antisymm (by simpa using this) (Complex.normSq_nonneg _)
    rw [Complex.normSq_eq_zero.mp hz]; simp
  obtain ⟨p, hp, hpinj⟩ := exists_prime_archChar_injective γ hγ
  set pu : ℚˣ := Units.mk0 (p : ℚ) (by exact_mod_cast hp.ne_zero) with hpu_def
  have hpu : 0 < (pu : ℚ) := by rw [hpu_def, Units.val_mk0]; exact_mod_cast hp.pos
  have hz : Function.Injective fun k => archChar (γ k) pu := by
    rw [hpu_def, Units.val_mk0]; exact hpinj
  set Φ : PosDefFn AffineGroupQ := ⟨φ, hφ⟩
  set ξ := eigVec hφ γ pu
  set α : Fin K → ℝ := fun k => (succCoeff hφ γ pu k k 1).re with hα_def
  have hdiag : ∀ k (b : ℚ), b ≠ 0 → succCoeff hφ γ pu k k b = (α k : ℂ) := by
    intro k b hb
    obtain ⟨a, ha⟩ := succCoeff_diag hφ γ c hf hpu hz k
    rw [ha b hb, hα_def]
    simp only [ha 1 one_ne_zero, Complex.ofReal_re]
  have hbounds : ∀ k, 0 ≤ α k ∧ α k ≤ c k := by
    intro k
    have hreal := const_successor_real Φ (ξ k) (α k) fun b hb => hdiag k b hb.ne'
    refine ⟨by simpa using hreal.2, ?_⟩
    have hcs : ‖succCoeff hφ γ pu k k 1‖ ≤ c k := by
      unfold succCoeff
      calc _ ≤ ‖ξ k‖ * ‖gnsTranslate Φ (translation 1) (ξ k)‖ := norm_inner_le_norm _ _
        _ = ‖ξ k‖ ^ 2 := by rw [norm_gnsTranslate]; ring
        _ = c k := by
          rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_eigVec hφ γ c hf hpu hz, if_pos rfl]; simp
    rw [hdiag k 1 one_ne_zero, Complex.norm_real, Real.norm_eq_abs] at hcs
    exact (le_abs_self _).trans hcs
  have hoff : ∀ k l (b : ℚ), k ≠ l → succCoeff hφ γ pu k l b = 0 := by
    intro k l b hkl
    rcases lt_trichotomy b 0 with hneg | rfl | hpos
    · have h := succCoeff_offdiag hφ γ c hf hpu hz (Ne.symm hkl) (-b) (by linarith)
      unfold succCoeff at h ⊢
      rw [inner_gnsTranslate_right, translation_inv', ← inner_conj_symm, h, map_zero]
    · unfold succCoeff
      rw [translation_zero, gnsTranslate_one, inner_eigVec hφ γ c hf hpu hz, if_neg hkl]
    · exact succCoeff_offdiag hφ γ c hf hpu hz hkl b hpos
  refine ⟨α, hbounds, fun b u hu => ?_⟩
  rw [archExtension_apply _ _ _ b u hu]
  have hφgu : φ (translation b * dilation u) = inner ℂ (gnsVec Φ 1)
      (gnsTranslate Φ (translation b) (gnsTranslate Φ (dilation u) (gnsVec Φ 1))) := by
    rw [gnsTranslate_gnsVec, gnsTranslate_gnsVec, inner_gnsVec, inv_one, one_mul, mul_one]
  rw [hφgu, ← sum_eigVec hφ γ hz hK, map_sum, map_sum, sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_sum, Finset.sum_eq_single k]
  · -- the diagonal term
    rw [inner_gnsTranslate_right, inner_translate_eigVec_right hφ γ c hf hpu hz u hu,
      inner_gnsTranslate_left, inv_inv]
    by_cases hb : b = 0
    · subst hb
      rw [translation_zero, gnsTranslate_one, inner_eigVec hφ γ c hf hpu hz, if_pos rfl, if_pos rfl]
      ring
    · rw [show inner ℂ (ξ k) (gnsTranslate Φ (translation b) (ξ k)) = succCoeff hφ γ pu k k b
        from rfl, hdiag k b hb, if_neg hb]
      ring
  · intro l _ hlk
    rw [inner_gnsTranslate_right, inner_translate_eigVec_right hφ γ c hf hpu hz u hu,
      inner_gnsTranslate_left, inv_inv,
      show inner ℂ (ξ k) (gnsTranslate Φ (translation b) (ξ l)) = succCoeff hφ γ pu k l b from rfl,
      hoff k l b (Ne.symm hlk), mul_zero]
  · simp

end GaloisForLFunctions.ArithmeticPositiveDuality
