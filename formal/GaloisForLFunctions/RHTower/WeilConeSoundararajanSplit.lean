import GaloisForLFunctions.RHTower.WeilProducerLittlewoodBound
import GaloisForLFunctions.RHTower.WeilConePrimePolynomialMoments

/-!
# Splitting the cone Soundararajan polynomial

Soundararajan's inequality on the Weil cone (`re_producerLogZeta_le`) bounds `log|F_lam(σ + it)|`
by the weighted Dirichlet polynomial

`P_L(s)/L = Σ_{n < e^L} lam(n) n^{−s} (1 − log n/L)/log n`

plus archimedean terms.  This file splits `P_L/L` into
* the prime part `Σ_p a_p p^{−s}`, `a_p = lam(p)(1 − log p/L)/log p`;
* the prime-square part `Σ_p b_p p^{−2s}`, `b_p = lam(p²)(1 − 2 log p/L)/(2 log p)`;
* the rest (`n` neither a prime nor the square of a prime), bounded by
  `A_c = Σ_{rest} |lam(n)|/(√n log n)` on `Re s ≥ ½` (`norm_restPoly_div_le`).

The first two are prime-supported polynomials in the form of `edPoly`, to which the high-moment
bounds of `WeilConeMoments` apply (at `s` and at `2s`).
-/

open Complex Set Filter MeasureTheory

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz

/-! ### The three supports -/

/-- `n` is the square of a prime. -/
def IsPrimeSq (n : ℕ) : Prop := (Nat.sqrt n).Prime ∧ Nat.sqrt n ^ 2 = n

instance (n : ℕ) : Decidable (IsPrimeSq n) := by unfold IsPrimeSq; infer_instance

theorem isPrimeSq_sq {p : ℕ} (hp : p.Prime) : IsPrimeSq (p ^ 2) := by
  unfold IsPrimeSq
  rw [Nat.sqrt_eq' p]
  exact ⟨hp, rfl⟩

theorem not_prime_of_isPrimeSq {n : ℕ} (h : IsPrimeSq n) : ¬ n.Prime := by
  obtain ⟨hp, hn⟩ := h
  rw [← hn]
  exact Nat.Prime.not_prime_pow' (by norm_num)

/-- The rest weight `|lam(n)|/(√n log n)` off primes and prime squares. -/
def restWeight (lam : ℕ → ℝ) (n : ℕ) : ℝ :=
  if 2 ≤ n ∧ ¬ n.Prime ∧ ¬ IsPrimeSq n then |lam n| / (Real.sqrt n * Real.log n) else 0

theorem restWeight_nonneg (lam : ℕ → ℝ) (n : ℕ) : 0 ≤ restWeight lam n := by
  unfold restWeight
  split_ifs with h
  · have : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    positivity
  · exact le_rfl

/-- The `n`-th term of `P_L(s)/L`. -/
def polyTerm (lam : ℕ → ℝ) (L : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  LSeries.term (lamC lam) s n * ((max (L - Real.log n) 0 : ℝ) : ℂ) / Real.log n / L

/-- The length `N = ⌈e^L⌉`. -/
def polyLength (L : ℝ) : ℕ := ⌈Real.exp L⌉₊

theorem producerPoly_div_eq (lam : ℕ → ℝ) (L : ℝ) (s : ℂ) :
    producerPoly lam L s / L = ∑ n ∈ Finset.range (polyLength L), polyTerm lam L s n := by
  rw [producerPoly_eq_sum, Finset.sum_div]
  rfl

theorem polyLength_pos (L : ℝ) : 0 < polyLength L :=
  Nat.ceil_pos.mpr (Real.exp_pos L)

theorem polyTerm_eq_zero_of_le {lam : ℕ → ℝ} {L : ℝ} {s : ℂ} {n : ℕ} (hn : polyLength L ≤ n) :
    polyTerm lam L s n = 0 := by
  unfold polyTerm
  rw [max_sub_log_eq_zero hn]
  simp

/-! ### Coefficients -/

/-- Prime coefficients `a_p = lam(p)(L − log p)⁺/(L log p)` for `p < N`. -/
def primeCoeff (lam : ℕ → ℝ) (L : ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n.Prime ∧ n < polyLength L then
    ((lam n * max (L - Real.log n) 0 / (L * Real.log n) : ℝ) : ℂ) else 0, by simp⟩

/-- Prime-square coefficients `b_p = lam(p²)(L − 2 log p)⁺/(2L log p)` for `p² < N`. -/
def sqCoeff (lam : ℕ → ℝ) (L : ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n.Prime ∧ n ^ 2 < polyLength L then
    ((lam (n ^ 2) * max (L - Real.log (n ^ 2 : ℕ)) 0 / (L * Real.log (n ^ 2 : ℕ)) : ℝ) : ℂ)
      else 0, by simp⟩

theorem primeCoeff_apply (lam : ℕ → ℝ) (L : ℝ) (n : ℕ) :
    primeCoeff lam L n = if n.Prime ∧ n < polyLength L then
      ((lam n * max (L - Real.log n) 0 / (L * Real.log n) : ℝ) : ℂ) else 0 := rfl

theorem sqCoeff_apply (lam : ℕ → ℝ) (L : ℝ) (n : ℕ) :
    sqCoeff lam L n = if n.Prime ∧ n ^ 2 < polyLength L then
      ((lam (n ^ 2) * max (L - Real.log (n ^ 2 : ℕ)) 0 / (L * Real.log (n ^ 2 : ℕ)) : ℝ) : ℂ)
        else 0 := rfl

theorem primeCoeff_prime {lam : ℕ → ℝ} {L : ℝ} {k : ℕ} (h : primeCoeff lam L k ≠ 0) : k.Prime := by
  rw [primeCoeff_apply] at h
  split_ifs at h with hk
  · exact hk.1
  · exact absurd rfl h

theorem primeCoeff_le {lam : ℕ → ℝ} {L : ℝ} {k : ℕ} (h : primeCoeff lam L k ≠ 0) :
    k ≤ polyLength L := by
  rw [primeCoeff_apply] at h
  split_ifs at h with hk
  · exact hk.2.le
  · exact absurd rfl h

theorem sqCoeff_prime {lam : ℕ → ℝ} {L : ℝ} {k : ℕ} (h : sqCoeff lam L k ≠ 0) : k.Prime := by
  rw [sqCoeff_apply] at h
  split_ifs at h with hk
  · exact hk.1
  · exact absurd rfl h

theorem sqCoeff_le {lam : ℕ → ℝ} {L : ℝ} {k : ℕ} (h : sqCoeff lam L k ≠ 0) :
    k ≤ polyLength L := by
  rw [sqCoeff_apply] at h
  split_ifs at h with hk
  · have h1 : k ≤ k ^ 2 := Nat.le_self_pow (by norm_num) k
    omega
  · exact absurd rfl h

/-! ### The split -/

theorem cpow_neg_eq_term {n : ℕ} (hn : 1 ≤ n) (s : ℂ) :
    ((n : ℝ) : ℂ) ^ (-s) = 1 / (n : ℂ) ^ s := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [Complex.ofReal_natCast, Complex.cpow_neg, one_div]

theorem polyTerm_prime {lam : ℕ → ℝ} {L : ℝ} {s : ℂ} {p : ℕ} (hp : p.Prime)
    (hpN : p < polyLength L) :
    polyTerm lam L s p = primeCoeff lam L p * ((p : ℝ) : ℂ) ^ (-s) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : p ≠ 0 := by omega
  rw [primeCoeff_apply, if_pos ⟨hp, hpN⟩, cpow_neg_eq_term (by omega)]
  unfold polyTerm
  rw [LSeries.term_of_ne_zero hp0]
  unfold lamC
  rw [if_pos hp2]
  push_cast
  ring

theorem polyTerm_sq {lam : ℕ → ℝ} {L : ℝ} {s : ℂ} {p : ℕ} (hp : p.Prime)
    (hpN : p ^ 2 < polyLength L) :
    polyTerm lam L s (p ^ 2) = sqCoeff lam L p * ((p : ℝ) : ℂ) ^ (-(2 * s)) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ p ^ 2 := le_trans hp2 (Nat.le_self_pow (by norm_num) p)
  have hq0 : p ^ 2 ≠ 0 := by omega
  have hpC : ((p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  rw [sqCoeff_apply, if_pos ⟨hp, hpN⟩]
  unfold polyTerm
  rw [LSeries.term_of_ne_zero hq0]
  unfold lamC
  rw [if_pos hq2]
  have hpow : ((p ^ 2 : ℕ) : ℂ) ^ s = ((p : ℝ) : ℂ) ^ (2 * s) := by
    have hppos : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    have hq : ((p ^ 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hq0
    rw [Complex.cpow_def_of_ne_zero hq, Complex.cpow_def_of_ne_zero hpC]
    congr 1
    have hl : Complex.log ((p ^ 2 : ℕ) : ℂ) = 2 * Complex.log ((p : ℝ) : ℂ) := by
      rw [show ((p ^ 2 : ℕ) : ℂ) = (((p : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_log (by positivity), ← Complex.ofReal_log hppos.le, Real.log_pow]
      push_cast; ring
    rw [hl]; ring
  rw [hpow, Complex.cpow_neg]
  push_cast
  ring

/-- The rest polynomial: `n` neither prime nor a prime square. -/
def restPoly (lam : ℕ → ℝ) (L : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ (Finset.range (polyLength L)).filter (fun n => ¬ n.Prime ∧ ¬ IsPrimeSq n),
    polyTerm lam L s n

theorem edPoly_primeCoeff_eq (lam : ℕ → ℝ) (L : ℝ) (s : ℂ) :
    edPoly (⇑(primeCoeff lam L)) (Finset.Icc 1 (polyLength L)) s =
      ∑ n ∈ (Finset.range (polyLength L)).filter (fun n => n.Prime), polyTerm lam L s n := by
  unfold edPoly
  rw [Finset.sum_filter]
  have hN0 := polyLength_pos L
  have h1 : Finset.Icc 1 (polyLength L) = insert (polyLength L) (Finset.Ico 1 (polyLength L)) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
  have hN : primeCoeff lam L (polyLength L) = 0 := by
    rw [primeCoeff_apply, if_neg (fun h => lt_irrefl _ h.2)]
  rw [h1, Finset.sum_insert (by simp), hN, zero_mul, zero_add]
  have h2 : Finset.range (polyLength L) = insert 0 (Finset.Ico 1 (polyLength L)) := by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
  rw [h2, Finset.sum_insert (by simp), if_neg Nat.not_prime_zero, zero_add]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Ico] at hn
  split_ifs with hp
  · rw [polyTerm_prime hp hn.2]
  · rw [primeCoeff_apply, if_neg (fun h => hp h.1), zero_mul]

theorem edPoly_sqCoeff_eq (lam : ℕ → ℝ) (L : ℝ) (s : ℂ) :
    edPoly (⇑(sqCoeff lam L)) (Finset.Icc 1 (polyLength L)) (2 * s) =
      ∑ n ∈ (Finset.range (polyLength L)).filter (fun n => IsPrimeSq n), polyTerm lam L s n := by
  unfold edPoly
  set N := polyLength L
  -- both sides are sums over the primes `p` with `p² < N`
  set P := (Finset.Icc 1 N).filter (fun p => p.Prime ∧ p ^ 2 < N) with hP
  have hl : ∑ n ∈ Finset.Icc 1 N, sqCoeff lam L n * ((n : ℝ) : ℂ) ^ (-(2 * s)) =
      ∑ p ∈ P, sqCoeff lam L p * ((p : ℝ) : ℂ) ^ (-(2 * s)) := by
    rw [hP, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs with h
    · rfl
    · rw [sqCoeff_apply, if_neg h, zero_mul]
  have himg : (Finset.range N).filter (fun n => IsPrimeSq n) = P.image (fun p => p ^ 2) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, hP, Finset.mem_Icc]
    constructor
    · rintro ⟨hn, hsq⟩
      refine ⟨Nat.sqrt n, ⟨⟨hsq.1.one_lt.le, ?_⟩, hsq.1, by rw [hsq.2]; exact hn⟩, hsq.2⟩
      have := Nat.sqrt_le_self n
      omega
    · rintro ⟨p, ⟨⟨_, _⟩, hp, hpN⟩, rfl⟩
      exact ⟨hpN, isPrimeSq_sq hp⟩
  have hinj : Set.InjOn (fun p : ℕ => p ^ 2) P := fun a _ b _ h =>
    Nat.pow_left_injective (by norm_num) h
  rw [hl, himg, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [hP, Finset.mem_filter] at hp
  rw [polyTerm_sq hp.2.1 hp.2.2]

theorem producerPoly_div_eq_split (lam : ℕ → ℝ) (L : ℝ) (s : ℂ) :
    producerPoly lam L s / L =
      edPoly (⇑(primeCoeff lam L)) (Finset.Icc 1 (polyLength L)) s +
        edPoly (⇑(sqCoeff lam L)) (Finset.Icc 1 (polyLength L)) (2 * s) + restPoly lam L s := by
  rw [producerPoly_div_eq, edPoly_primeCoeff_eq, edPoly_sqCoeff_eq, restPoly]
  set R := Finset.range (polyLength L)
  rw [← Finset.sum_filter_add_sum_filter_not R (fun n => n.Prime)]
  have hnot : R.filter (fun n => ¬ n.Prime) = (R.filter (fun n => IsPrimeSq n)) ∪
      R.filter (fun n => ¬ n.Prime ∧ ¬ IsPrimeSq n) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hn, hp⟩
      by_cases hq : IsPrimeSq n
      · exact Or.inl ⟨hn, hq⟩
      · exact Or.inr ⟨hn, hp, hq⟩
    · rintro (⟨hn, hq⟩ | ⟨hn, hp, _⟩)
      · exact ⟨hn, not_prime_of_isPrimeSq hq⟩
      · exact ⟨hn, hp⟩
  have hdisj : Disjoint (R.filter (fun n => IsPrimeSq n))
      (R.filter (fun n => ¬ n.Prime ∧ ¬ IsPrimeSq n)) := by
    rw [Finset.disjoint_filter]
    intro n _ h1 h2
    exact h2.2 h1
  rw [hnot, Finset.sum_union hdisj, add_assoc]

/-- **The rest is bounded by `A_c`** on `Re s ≥ ½`. -/
theorem norm_restPoly_div_le (lam : ℕ → ℝ) {L : ℝ} (hL : 0 < L) {s : ℂ} (hs : 1 / 2 ≤ s.re)
    (hA : Summable (restWeight lam)) :
    ‖restPoly lam L s‖ ≤ ∑' n, restWeight lam n := by
  unfold restPoly
  refine (norm_sum_le _ _).trans ?_
  refine le_trans ?_ (hA.sum_le_tsum ((Finset.range (polyLength L)).filter
    (fun n => ¬ n.Prime ∧ ¬ IsPrimeSq n)) (fun n _ => restWeight_nonneg lam n))
  refine Finset.sum_le_sum fun n hn => ?_
  rw [Finset.mem_filter, Finset.mem_range] at hn
  obtain ⟨_, hp, hq⟩ := hn
  rcases lt_or_ge n 2 with hn2 | hn2
  · unfold polyTerm
    rw [term_lamC_eq_zero_of_lt lam _ hn2]
    simp only [zero_mul, zero_div, norm_zero]
    exact restWeight_nonneg lam n
  · have hn0 : n ≠ 0 := by omega
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    unfold restWeight
    rw [if_pos ⟨hn2, hp, hq⟩]
    unfold polyTerm
    rw [norm_div, norm_div, norm_mul, LSeries.norm_term_eq, if_neg hn0, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hl, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
    have hlamC : ‖lamC lam n‖ = |lam n| := by
      unfold lamC
      rw [Complex.norm_real, Real.norm_eq_abs, if_pos hn2]
    rw [hlamC]
    have hpow : Real.sqrt n ≤ (n : ℝ) ^ s.re := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hn1 hs
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
    have hmax : max (L - Real.log n) 0 ≤ L := max_le (by linarith) hL.le
    have hmax0 : 0 ≤ max (L - Real.log n) 0 := le_max_right _ _
    calc |lam n| / (n : ℝ) ^ s.re * max (L - Real.log n) 0 / Real.log n / L
        ≤ |lam n| / Real.sqrt n * L / Real.log n / L := by gcongr
      _ = |lam n| / (Real.sqrt n * Real.log n) := by field_simp


/-! ### The split Soundararajan inequality -/

theorem displacedLinePt_eq (σ t : ℝ) : ((σ : ℂ) + t * I) = displacedLinePt (1 / 2 - σ) t := by
  unfold displacedLinePt; push_cast; ring

theorem two_mul_displacedLinePt_eq (σ t : ℝ) :
    2 * ((σ : ℂ) + t * I) = displacedLinePt (1 / 2 - 2 * σ) (2 * t) := by
  unfold displacedLinePt; push_cast; ring

/-- **Soundararajan's inequality, split.**  For `½ < σ ≤ ½ + 1/L`, `L ≥ 2`, `|t| ≥ max(4, e^L)`:
`log|F_lam(σ+it)| ≤ Re S_p + Re S_{p²} + A_c + (log|t| + 6)/L + M₂ + 2`, where
`S_p = Σ_p a_p p^{−σ₀−it}`, `S_{p²} = Σ_p b_p p^{−2σ₀−2it}`, `σ₀ = ½ + 1/L`, and
`M₂ = Σ |lam(n)| n^{−2}`. -/
theorem re_producerLogZeta_le_split {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hA : Summable (restWeight lam)) {σ L t : ℝ} (hσ : 1 / 2 < σ) (hσL : σ ≤ 1 / 2 + 1 / L)
    (hL2 : 2 ≤ L) (ht4 : 4 ≤ |t|) (hexp : Real.exp L ≤ |t|) :
    (producerLogZeta hW σ t).re ≤
      (edPoly (⇑(primeCoeff lam L)) (Finset.Icc 1 (polyLength L))
        (displacedLinePt (1 / 2 - (1 / 2 + 1 / L)) t)).re +
      (edPoly (⇑(sqCoeff lam L)) (Finset.Icc 1 (polyLength L))
        (displacedLinePt (1 / 2 - 2 * (1 / 2 + 1 / L)) (2 * t))).re +
      (∑' n, restWeight lam n) + (Real.log |t| + 6) / L +
        ((∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ)) + 2) := by
  set M₂ : ℝ := ∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ) with hM₂
  have hM₂0 : 0 ≤ M₂ := tsum_nonneg fun n => by positivity
  have hLpos : 0 < L := by linarith
  set σ₀ : ℝ := 1 / 2 + 1 / L with hσ₀
  have hσ₀2 : σ₀ ≤ 2 := by
    have : 1 / L ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hL2
    rw [hσ₀]; linarith
  have ht0 : t ≠ 0 := fun h => by rw [h, abs_zero] at ht4; linarith
  have hlamb : Real.exp (-((σ₀ - 1 / 2) * L)) ≤ (σ₀ - 1 / 2) * L := by
    have h1 : (σ₀ - 1 / 2) * L = 1 := by rw [hσ₀]; field_simp; ring
    rw [h1]
    have : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    exact this
  have hmain := re_producerLogZeta_le hW hσ hσL hσ₀2 ht0 hLpos hlamb
  -- the polynomial
  have hsplit := producerPoly_div_eq_split lam L ((σ₀ : ℂ) + t * I)
  have hpoly : (producerPoly lam L ((σ₀ : ℂ) + t * I)).re / L ≤
      (edPoly (⇑(primeCoeff lam L)) (Finset.Icc 1 (polyLength L))
        (displacedLinePt (1 / 2 - σ₀) t)).re +
      (edPoly (⇑(sqCoeff lam L)) (Finset.Icc 1 (polyLength L))
        (displacedLinePt (1 / 2 - 2 * σ₀) (2 * t))).re + ∑' n, restWeight lam n := by
    have e1 : (producerPoly lam L ((σ₀ : ℂ) + t * I)).re / L =
        (producerPoly lam L ((σ₀ : ℂ) + t * I) / L).re := by
      rw [Complex.div_ofReal_re]
    rw [e1, hsplit, Complex.add_re, Complex.add_re, ← displacedLinePt_eq,
      ← two_mul_displacedLinePt_eq]
    have hrest := norm_restPoly_div_le lam hLpos (s := (σ₀ : ℂ) + t * I)
      (by simp [hσ₀]; positivity) hA
    have := (Complex.re_le_norm _).trans hrest
    linarith
  -- archimedean terms
  have hU : ∀ u : ℝ, 1 / 2 < u → u ≤ 2 → (archU ((u : ℂ) + t * I)).re ≤ Real.log |t| / 2 + 3 :=
    fun u hu hu2 => re_archU_le (by linarith) hu2 ht4
  have hσ₀gt : 1 / 2 < σ₀ := by
    have : 0 < 1 / L := by positivity
    rw [hσ₀]; linarith
  have hP2 : (archU ((σ₀ : ℂ) + t * I)).re / L ≤ (Real.log |t| / 2 + 3) / L :=
    div_le_div_of_nonneg_right (hU σ₀ hσ₀gt hσ₀2) hLpos.le
  have hdiff : σ₀ - σ ≤ 1 / L := by rw [hσ₀]; linarith
  have hP3 : (∫ u in σ..σ₀, (archU ((u : ℂ) + t * I)).re) ≤ (Real.log |t| / 2 + 3) / L := by
    have hc := continuousOn_archU_horizontal hW hσ hσ₀gt ht0
    have hint := (Complex.continuous_re.comp_continuousOn hc).intervalIntegrable (μ := volume)
    have h1 := intervalIntegral.integral_mono_on hσL hint
      (intervalIntegrable_const (c := Real.log |t| / 2 + 3)) fun u hu =>
        hU u (by linarith [hu.1]) (hu.2.trans hσ₀2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    have hy3 : 0 ≤ Real.log |t| / 2 + 3 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ |t| by linarith); linarith
    calc _ ≤ (σ₀ - σ) * (Real.log |t| / 2 + 3) := h1
      _ ≤ 1 / L * (Real.log |t| / 2 + 3) := mul_le_mul_of_nonneg_right hdiff hy3
      _ = (Real.log |t| / 2 + 3) / L := by ring
  have hP4 := residual_div_le_littlewood hM₂0 (le_of_eq rfl : 1 / 2 + 1 / L ≤ σ₀) hL2 ht4 hexp
  have e2 : (Real.log |t| / 2 + 3) / L + (Real.log |t| / 2 + 3) / L = (Real.log |t| + 6) / L := by
    ring
  linarith

end RHTower.WeilSpectral
