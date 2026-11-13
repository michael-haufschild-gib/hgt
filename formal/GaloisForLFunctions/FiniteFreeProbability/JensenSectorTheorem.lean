import GaloisForLFunctions.FiniteFreeProbability.EulerFactorStability
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The sector theorem for Jensen polynomials

`R_d(h) = h(D) X^d` is the reversed Jensen polynomial of degree `d` of a symbol `h`.

**Theorem** (`splits_diffOp_X_pow_of_sector`). Let `h` be a real polynomial with `h(0) ≠ 0` all of whose
complex roots `ρ` lie in the double sector `(d − 1)(Im ρ)² ≤ (Re ρ)²`. Then `R_d(h)` is real-rooted.

**Exactness** (`splits_diffOp_pairSymbol_iff`). For `d ≥ 2` and `ρ ≠ 0`, the symbol `(w − ρ)(w − ρ̄)` has a
real-rooted `R_d` iff `ρ` lies in the sector: no larger conjugation-invariant region of roots is
admissible in degree `d`.

Mechanism. `R_d(fg) = R_d(f) ⊞_d R_d(g)`, and Walsh's theorem keeps real-rootedness under `⊞_d`. So
the symbols with real-rooted `R_d` and nonzero constant term are closed under products, and each real
irreducible factor is tested alone. A factor `c + bw + aw²` gives
`R_d = X^{d−2}(cX² + bdX + ad(d−1))`, with discriminant `d(db² − 4ac(d−1))`; for the roots
`γ ± iδ` this is nonnegative iff `(d − 1)δ² ≤ γ²`.
-/

open Polynomial

namespace FiniteFreeProbability

noncomputable section

/-- The Jensen sector of degree `d`: `(d − 1)(Im ρ)² ≤ (Re ρ)²`. -/
def InJensenSector (d : ℕ) (ρ : ℂ) : Prop := ((d : ℝ) - 1) * ρ.im ^ 2 ≤ ρ.re ^ 2

/-! ## Polynomial symbols -/

/-- For a polynomial symbol, `R_d(h) = h(D) X^d`. -/
theorem jensenRev_coe {K : Type*} [Field K] (d : ℕ) (h : K[X]) :
    jensenRev d (h : PowerSeries K) = diffOp h (X ^ d) := by
  rw [jensenRev]
  refine diffOp_congr (natDegree_X_pow_le d) fun i hi => ?_
  rw [PowerSeries.coeff_trunc, if_pos (Nat.lt_succ_of_le hi), Polynomial.coeff_coe]

/-- `h(D) X^d` has degree `d` when `h(0) ≠ 0`. -/
theorem natDegree_diffOp_X_pow {K : Type*} [Field K] {h : K[X]} (h0 : h.coeff 0 ≠ 0) (d : ℕ) :
    (diffOp h (X ^ d)).natDegree = d := by
  rw [← jensenRev_coe]
  refine natDegree_jensenRev ?_
  rwa [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]

/-- **Product closure.** If `R_d(f)` and `R_d(g)` are real-rooted and `f(0), g(0) ≠ 0`, then
`R_d(fg)` is real-rooted. -/
theorem splits_diffOp_mul_X_pow {f g : ℝ[X]} {d : ℕ} (hf0 : f.coeff 0 ≠ 0) (hg0 : g.coeff 0 ≠ 0)
    (hf : (diffOp f (X ^ d)).Splits) (hg : (diffOp g (X ^ d)).Splits) :
    (diffOp (f * g) (X ^ d)).Splits := by
  have hgd := natDegree_diffOp_X_pow hg0 d
  have hfd := natDegree_diffOp_X_pow hf0 d
  have hne : ∀ {p : ℝ[X]}, p.coeff 0 ≠ 0 → diffOp p (X ^ d) ≠ 0 := fun {p} hp h => by
    have hc : (diffOp p (X ^ d)).coeff d = p.coeff 0 := by
      rw [← jensenRev_coe, coeff_jensenRev_self, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        Polynomial.coeff_coe]
    rw [h, coeff_zero] at hc
    exact hp hc.symm
  rw [diffOp_mul, ← ffConv_diffOp_X_pow_right hgd.le f]
  exact splits_ffConv hg hf (hne hg0) hgd (hne hf0) hfd.le

/-! ## Quadratics -/

/-- A real quadratic splits iff its discriminant is nonnegative. -/
theorem splits_quadratic_iff {a b c : ℝ} (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Splits ↔ 0 ≤ b ^ 2 - 4 * a * c := by
  constructor
  · intro hs
    have hdeg : (C a * X ^ 2 + C b * X + C c).degree ≠ 0 := by
      rw [degree_quadratic ha]
      norm_num
    obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero hdeg
    have hq : a * (x * x) + b * x + c = 0 := by
      simpa [sq] using hx
    have := discrim_eq_sq_of_quadratic_eq_zero hq
    rw [discrim] at this
    rw [this]
    positivity
  · intro hD
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s ^ 2 = b ^ 2 - 4 * a * c := ⟨_, Real.sq_sqrt hD⟩
    obtain ⟨r₁, hr₁⟩ : ∃ r : ℝ, r = (-b + s) / (2 * a) := ⟨_, rfl⟩
    obtain ⟨r₂, hr₂⟩ : ∃ r : ℝ, r = (-b - s) / (2 * a) := ⟨_, rfl⟩
    have hsum : b = -(a * (r₁ + r₂)) := by
      rw [hr₁, hr₂]
      field_simp
      ring
    have hprod : c = a * (r₁ * r₂) := by
      rw [hr₁, hr₂]
      field_simp
      linear_combination hs
    have hfac : C a * X ^ 2 + C b * X + C c = C a * ((X - C r₁) * (X - C r₂)) := by
      rw [hsum, hprod]
      simp only [map_neg, map_mul, map_add]
      ring
    rw [hfac]
    exact ((Splits.X_sub_C r₁).mul (Splits.X_sub_C r₂)).C_mul a

/-- A symbol of degree at most two acts on `X^{k+2}` through one quadratic factor. -/
theorem diffOp_X_pow_of_natDegree_le_two {q : ℝ[X]} (hq : q.natDegree ≤ 2) (k : ℕ) :
    diffOp q (X ^ (k + 2)) =
      X ^ k * (C (q.coeff 0) * X ^ 2 + C (q.coeff 1 * ((k : ℝ) + 2)) * X +
        C (q.coeff 2 * (((k : ℝ) + 2) * ((k : ℝ) + 1)))) := by
  have h1 : derivative ((X : ℝ[X]) ^ (k + 2)) = C ((k : ℝ) + 2) * X ^ (k + 1) := by
    rw [derivative_X_pow]
    push_cast
    rfl
  have h2 : derivative (C ((k : ℝ) + 2) * (X : ℝ[X]) ^ (k + 1)) =
      C (((k : ℝ) + 2) * ((k : ℝ) + 1)) * X ^ k := by
    rw [derivative_C_mul, derivative_X_pow, ← mul_assoc, ← C_mul]
    push_cast
    rfl
  rw [diffOp_eq_sum q _ (n := 3) (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Function.iterate_succ,
    Function.iterate_zero, Function.comp_apply, id_eq, h1, h2, map_mul]
  ring

/-- **The pair test.** For `deg q ≤ 2` and `q(0) ≠ 0`, `R_{k+2}(q)` is real-rooted iff
`4 q₀ q₂ (k+1) ≤ (k+2) q₁²`. -/
theorem splits_diffOp_X_pow_iff_of_natDegree_le_two {q : ℝ[X]} (hq : q.natDegree ≤ 2)
    (h0 : q.coeff 0 ≠ 0) (k : ℕ) :
    (diffOp q (X ^ (k + 2))).Splits ↔
      4 * q.coeff 0 * q.coeff 2 * ((k : ℝ) + 1) ≤ ((k : ℝ) + 2) * q.coeff 1 ^ 2 := by
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hQ0 : C (q.coeff 0) * X ^ 2 + C (q.coeff 1 * ((k : ℝ) + 2)) * X +
      C (q.coeff 2 * (((k : ℝ) + 2) * ((k : ℝ) + 1))) ≠ 0 := fun h => by
    have := natDegree_quadratic (b := q.coeff 1 * ((k : ℝ) + 2))
      (c := q.coeff 2 * (((k : ℝ) + 2) * ((k : ℝ) + 1))) h0
    rw [h, natDegree_zero] at this
    omega
  rw [diffOp_X_pow_of_natDegree_le_two hq, splits_mul (pow_ne_zero k X_ne_zero) hQ0,
    splits_quadratic_iff h0]
  have hdisc : (q.coeff 1 * ((k : ℝ) + 2)) ^ 2 -
      4 * q.coeff 0 * (q.coeff 2 * (((k : ℝ) + 2) * ((k : ℝ) + 1))) =
      ((k : ℝ) + 2) * (((k : ℝ) + 2) * q.coeff 1 ^ 2 -
        4 * q.coeff 0 * q.coeff 2 * ((k : ℝ) + 1)) := by ring
  rw [hdisc]
  constructor
  · rintro ⟨-, h⟩
    have := nonneg_of_mul_nonneg_right h hk2
    linarith only [this]
  · intro h
    exact ⟨Splits.X_pow k, mul_nonneg hk2.le (by linarith only [h])⟩

/-- A real symbol of degree at most two with roots in the sector `n (Im ρ)² ≤ (Re ρ)²`, `n ≥ 0`,
satisfies `4 q₀ q₂ n ≤ (n + 1) q₁²`. -/
theorem pair_discriminant_of_sector {q : ℝ[X]} (hq : q.natDegree ≤ 2) {n : ℝ} (hn : 0 ≤ n)
    (hsec : ∀ ρ : ℂ, (q.map (algebraMap ℝ ℂ)).IsRoot ρ → n * ρ.im ^ 2 ≤ ρ.re ^ 2) :
    4 * q.coeff 0 * q.coeff 2 * n ≤ (n + 1) * q.coeff 1 ^ 2 := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = q.coeff 0 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = q.coeff 1 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = q.coeff 2 := ⟨_, rfl⟩
  rw [← hc, ← hb, ← ha]
  rcases le_or_gt (4 * c * a) (b ^ 2) with hD | hD
  · -- real roots: no constraint is needed
    nlinarith only [mul_le_mul_of_nonneg_right hD hn, sq_nonneg b]
  · -- a conjugate pair `(−b ± i s)/(2a)`
    have ha0 : a ≠ 0 := fun h => by
      rw [h, mul_zero] at hD
      linarith only [hD, sq_nonneg b]
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s ^ 2 = 4 * c * a - b ^ 2 :=
      ⟨_, Real.sq_sqrt (by linarith only [hD])⟩
    have hroot : (q.map (algebraMap ℝ ℂ)).IsRoot ⟨-b / (2 * a), s / (2 * a)⟩ := by
      rw [IsRoot, eval_eq_sum_range' (n := 3) (lt_of_le_of_lt natDegree_map_le (by omega))]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, coeff_map, ← hc, ← hb,
        ← ha, pow_zero, mul_one, pow_one]
      apply Complex.ext
      · simp only [Complex.add_re, Complex.mul_re, Complex.coe_algebraMap, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, sq, Complex.zero_re]
        field_simp
        linear_combination -hs
      · simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.coe_algebraMap,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sq, Complex.zero_im]
        field_simp
        ring
    have h := hsec _ hroot
    simp only [div_pow] at h
    rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity), hs, neg_sq] at h
    linarith only [h]

/-- **The sector test for one factor.** A real symbol of degree at most two with `q(0) ≠ 0` and
roots in the Jensen sector of degree `d` has a real-rooted `R_d`. -/
theorem splits_diffOp_X_pow_of_natDegree_le_two {q : ℝ[X]} (hq : q.natDegree ≤ 2)
    (h0 : q.coeff 0 ≠ 0) (d : ℕ)
    (hsec : ∀ ρ : ℂ, (q.map (algebraMap ℝ ℂ)).IsRoot ρ → InJensenSector d ρ) :
    (diffOp q (X ^ d)).Splits := by
  rcases Nat.lt_or_ge d 2 with hd | hd
  · exact Splits.of_natDegree_le_one
      ((natDegree_diffOp_le _ _).trans ((natDegree_X_pow_le d).trans (by omega)))
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hd
    rw [splits_diffOp_X_pow_iff_of_natDegree_le_two hq h0]
    have h := pair_discriminant_of_sector hq (n := (k : ℝ) + 1) (by positivity) fun ρ hρ => by
      have := hsec ρ hρ
      rw [InJensenSector] at this
      push_cast at this
      linarith only [this]
    linarith only [h]

/-! ## The sector theorem -/

/-- **Sector theorem.** A real polynomial symbol with `h(0) ≠ 0` whose complex roots lie in the
Jensen sector of degree `d` has a real-rooted Jensen polynomial `h(D) X^d`. -/
theorem splits_diffOp_X_pow_of_sector (d : ℕ) (h : ℝ[X]) (h0 : h.coeff 0 ≠ 0)
    (hsec : ∀ ρ : ℂ, (h.map (algebraMap ℝ ℂ)).IsRoot ρ → InJensenSector d ρ) :
    (diffOp h (X ^ d)).Splits := by
  induction h using WfDvdMonoid.induction_on_irreducible with
  | zero => simp at h0
  | unit u hu =>
    obtain ⟨r, -, rfl⟩ := Polynomial.isUnit_iff.1 hu
    have : diffOp (C r) (X ^ d) = C r * X ^ d := by
      simpa [diffOp] using diffOp_C_mul_left r 1 ((X : ℝ[X]) ^ d)
    rw [this]
    exact (Splits.X_pow d).C_mul r
  | mul a i _ hi ih =>
    rw [mul_coeff_zero] at h0
    have hi0 : i.coeff 0 ≠ 0 := left_ne_zero_of_mul h0
    have ha0 : a.coeff 0 ≠ 0 := right_ne_zero_of_mul h0
    have hroot : ∀ {p : ℝ[X]} (ρ : ℂ), p ∣ i * a → (p.map (algebraMap ℝ ℂ)).IsRoot ρ →
        InJensenSector d ρ := fun {p} ρ hp hρ =>
      hsec ρ ((Polynomial.map_dvd (algebraMap ℝ ℂ) hp).trans (dvd_refl _) |>.elim fun c hc => by
        rw [IsRoot, hc, eval_mul, hρ.eq_zero, zero_mul])
    exact splits_diffOp_mul_X_pow hi0 ha0
      (splits_diffOp_X_pow_of_natDegree_le_two hi.natDegree_le_two hi0 d
        fun ρ hρ => hroot ρ (dvd_mul_right i a) hρ)
      (ih ha0 fun ρ hρ => hroot ρ (dvd_mul_left a i) hρ)

/-! ## Exactness of the sector -/

/-- The real quadratic symbol with roots `ρ` and `conj ρ`. -/
def pairSymbol (ρ : ℂ) : ℝ[X] := X ^ 2 - C (2 * ρ.re) * X + C (Complex.normSq ρ)

/-- **The sector is exact.** For `d ≥ 2` and `ρ ≠ 0`, the pair `ρ, conj ρ` alone has a real-rooted
Jensen polynomial of degree `d` iff `(d − 1)(Im ρ)² ≤ (Re ρ)²`. -/
theorem splits_diffOp_pairSymbol_iff {d : ℕ} (hd : 2 ≤ d) {ρ : ℂ} (hρ : ρ ≠ 0) :
    (diffOp (pairSymbol ρ) (X ^ d)).Splits ↔ InJensenSector d ρ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hd
  have hform : pairSymbol ρ = C 1 * X ^ 2 + C (-(2 * ρ.re)) * X + C (Complex.normSq ρ) := by
    rw [pairSymbol, C_1, C_neg]
    ring
  have hdeg : (pairSymbol ρ).natDegree ≤ 2 := by
    rw [hform]
    exact (natDegree_quadratic one_ne_zero).le
  have hc0 : (pairSymbol ρ).coeff 0 = Complex.normSq ρ := by
    simp [pairSymbol]
  have hc1 : (pairSymbol ρ).coeff 1 = -(2 * ρ.re) := by
    simp [pairSymbol]
  have hc2 : (pairSymbol ρ).coeff 2 = 1 := by
    simp [pairSymbol]
  have hN : 0 < Complex.normSq ρ := Complex.normSq_pos.2 hρ
  rw [splits_diffOp_X_pow_iff_of_natDegree_le_two hdeg (by rw [hc0]; exact hN.ne'), hc0, hc1, hc2,
    InJensenSector, Complex.normSq_apply]
  push_cast
  constructor <;> intro h <;> nlinarith only [h]

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.splits_diffOp_X_pow_of_sector
#print axioms FiniteFreeProbability.splits_diffOp_pairSymbol_iff
