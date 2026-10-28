import GaloisForLFunctions.ArithmeticLorentzianGeometry.LorentzianPolynomialsAndTheTuranLayer
import Mathlib.NumberTheory.Real.Irrational

/-!
# Ramanujan and Lorentzian meet only at the Weil bound

Is the local factor at a prime Lorentzian *because of* the Riemann hypothesis over `𝔽_p`? No: the
two properties pull in opposite directions and meet only at the boundary.

Write a local factor of degree `d` as `P(T) = Σ_k a_k T^k`, `a_0 = 1`, sign-normalized to positive
coefficients, and homogenize it to `Σ_k a_k x^k y^{d−k}` (`bivariateCoeff`). The Riemann hypothesis
over `𝔽_q` (every inverse root has modulus `√q`) gives `a_d = (√q)^d` and `a_1 ≤ d √q`.

* **Lorentzian forces the opposite bound** (`le_pow_of_logConcave`, `sqrt_le_of_isLorentzianPoly`):
  the normalized coefficients `b_k = a_k / C(d, k)` of a Lorentzian bivariate form are
  log-concave, so `b_k ≤ b_1^k`; with `a_d = (√q)^d` this is `a_1 ≥ d √q`.
* **Rigidity** (`ramanujan_lorentzian_rigid`): a Ramanujan local factor with Lorentzian
  homogenization has `a_1 = d √q`, the trace of the maximal factor `(1 + √q T)^d`, which is
  Lorentzian (`isLorentzianPoly_maximal`).
* **At a prime they never meet** (`not_isLorentzianPoly_at_prime`): for `q = p` prime and an
  integral trace, `d √p ∈ ℤ` contradicts the irrationality of `√p`. For elliptic curves:
  `1 + a T + p T²` is Lorentzian iff `a² ≥ 4p` (`isLorentzianPoly_quadFactor_iff`), the reverse
  of the Hasse bound, and no prime reaches the boundary (`not_isLorentzianPoly_of_hasse`).

The local factors of a curve over a prime field are therefore never Lorentzian. Positivity at a
prime is the trickle-down of the Frobenius ladder (`TheTrickleDownInequalityIsTheSquareRootCount`),
a statement about a Gram matrix rather than about the local polynomial, and the Lorentzian inputs
of the Euler product closure (`TheEulerProductOfLorentzianLocalFactorsIsLorentzian`) cannot be the
local L-factors themselves.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

/-! ### Log-concave sequences -/

/-- A positive log-concave sequence with `b_0 = 1` satisfies `b_k ≤ b_1^k`. -/
theorem le_pow_of_logConcave {d : ℕ} {b : ℕ → ℝ} (hb0 : b 0 = 1) (hpos : ∀ k ≤ d, 0 < b k)
    (hlc : ∀ i, i + 2 ≤ d → b i * b (i + 2) ≤ b (i + 1) ^ 2) : ∀ k ≤ d, b k ≤ b 1 ^ k := by
  -- the ratios `b_{k+1} / b_k` decrease from `b_1`
  have hratio : ∀ k, k + 1 ≤ d → b (k + 1) ≤ b 1 * b k := by
    intro k
    induction k with
    | zero => intro _; rw [hb0, mul_one]
    | succ k ih =>
      intro hk
      show b (k + 2) ≤ b 1 * b (k + 1)
      have h1 := hlc k (by omega)
      have h2 := ih (by omega)
      have hbk := hpos k (by omega)
      have hbk1 := hpos (k + 1) (by omega)
      have : b k * b (k + 2) ≤ b k * (b 1 * b (k + 1)) := by
        nlinarith [mul_le_mul_of_nonneg_left h2 hbk1.le]
      exact le_of_mul_le_mul_left this hbk
  intro k
  induction k with
  | zero => intro _; rw [hb0, pow_zero]
  | succ k ih =>
    intro hk
    calc b (k + 1) ≤ b 1 * b k := hratio k hk
      _ ≤ b 1 * b 1 ^ k := mul_le_mul_of_nonneg_left (ih (by omega)) (hpos 1 (by omega)).le
      _ = b 1 ^ (k + 1) := by ring

/-! ### Lorentzian local factors -/

/-- **A Lorentzian local factor has trace at least `d √q`**: if `Σ_k a_k x^k y^{d−k}` is
Lorentzian with positive coefficients, `a_0 = 1` and `a_d = (√q)^d`, then `a_1 ≥ d √q`. -/
theorem sqrt_le_of_isLorentzianPoly {d : ℕ} (hd : 1 ≤ d) {a : ℕ → ℝ} {q : ℝ}
    (ha : ∀ k, 0 ≤ a k) (hpos : ∀ k ≤ d, 0 < a k) (h0 : a 0 = 1) (hD : a d = √q ^ d)
    (hL : IsLorentzianPoly d (bivariateCoeff d a)) : d * √q ≤ a 1 := by
  have hulc := ((isLorentzianPoly_bivariate_iff ha).mp hL).2
  have hb := le_pow_of_logConcave (b := fun k => a k / d.choose k) (d := d) (by simp [h0])
    (fun k hk => div_pos (hpos k hk) (by exact_mod_cast Nat.choose_pos hk)) hulc d le_rfl
  simp only [Nat.choose_self, Nat.choose_one_right, Nat.cast_one, div_one] at hb
  rw [hD] at hb
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h : √q ≤ a 1 / d := by
    by_contra h
    push Not at h
    exact absurd hb (not_le.mpr (pow_lt_pow_left₀ h (div_pos (hpos 1 hd) hd0).le (by omega)))
  rw [le_div_iff₀ hd0] at h
  linarith

/-- **Ramanujan and Lorentzian are rigid together**: a local factor with `a_d = (√q)^d` and the
Ramanujan trace bound `a_1 ≤ d √q` has Lorentzian homogenization only if `a_1 = d √q`. -/
theorem ramanujan_lorentzian_rigid {d : ℕ} (hd : 1 ≤ d) {a : ℕ → ℝ} {q : ℝ}
    (ha : ∀ k, 0 ≤ a k) (hpos : ∀ k ≤ d, 0 < a k) (h0 : a 0 = 1) (hD : a d = √q ^ d)
    (hR : a 1 ≤ d * √q) (hL : IsLorentzianPoly d (bivariateCoeff d a)) : a 1 = d * √q :=
  le_antisymm hR (sqrt_le_of_isLorentzianPoly hd ha hpos h0 hD hL)

/-- **At a prime, Ramanujan local factors with integral trace are never Lorentzian.** -/
theorem not_isLorentzianPoly_at_prime {d : ℕ} (hd : 1 ≤ d) {p : ℕ} (hp : p.Prime)
    {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hpos : ∀ k ≤ d, 0 < a k) (h0 : a 0 = 1)
    (hD : a d = √(p : ℝ) ^ d) (hR : a 1 ≤ d * √(p : ℝ)) {n : ℤ} (hn : a 1 = n) :
    ¬ IsLorentzianPoly d (bivariateCoeff d a) := fun hL => by
  have h := ramanujan_lorentzian_rigid hd ha hpos h0 hD hR hL
  rw [hn] at h
  exact (hp.irrational_sqrt.natCast_mul (by omega : d ≠ 0)).ne_int n h.symm

/-- **The maximal local factor `(1 + s T)^d` is Lorentzian.** -/
theorem isLorentzianPoly_maximal (d : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    IsLorentzianPoly d (bivariateCoeff d fun k => (d.choose k : ℝ) * s ^ k) := by
  rw [isLorentzianPoly_bivariate_iff fun k => by positivity]
  refine ⟨fun l m k hlm hmk hkd _ hk => ?_, fun i hi => ?_⟩
  · have hs0 : s ≠ 0 := fun h => hk (by simp only [h, zero_pow (by omega : k ≠ 0), mul_zero])
    exact mul_ne_zero (by exact_mod_cast (Nat.choose_pos (by omega)).ne') (pow_ne_zero _ hs0)
  · have c : ∀ k ≤ d, (d.choose k : ℝ) * s ^ k / d.choose k = s ^ k := fun k hk =>
      mul_div_cancel_left₀ _ (by exact_mod_cast (Nat.choose_pos hk).ne')
    rw [c i (by omega), c (i + 2) hi, c (i + 1) (by omega)]
    exact le_of_eq (by ring)

/-! ### Elliptic curves -/

/-- The sign-normalized local factor `1 + t T + q T²` of a genus-one curve. -/
def quadFactor (t q : ℝ) : ℕ → ℝ := fun k => if k = 0 then 1 else if k = 1 then t else
  if k = 2 then q else 0

/-- **`1 + t T + q T²` is Lorentzian iff `4q ≤ t²`**: the reverse of the Hasse bound. -/
theorem isLorentzianPoly_quadFactor_iff {t q : ℝ} (ht : 0 ≤ t) (hq : 0 < q) :
    IsLorentzianPoly 2 (bivariateCoeff 2 (quadFactor t q)) ↔ 4 * q ≤ t ^ 2 := by
  have ha : ∀ k, 0 ≤ quadFactor t q k := fun k => by
    unfold quadFactor; split_ifs <;> linarith
  rw [isLorentzianPoly_bivariate_iff ha]
  have h2 : (Nat.choose 2 1 : ℝ) = 2 := by norm_num [Nat.choose]
  constructor
  · rintro ⟨-, hU⟩
    have := hU 0 le_rfl
    simp only [quadFactor, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, div_one,
      zero_add, if_true, one_ne_zero, if_false, h2] at this
    norm_num at this
    nlinarith
  · intro h
    refine ⟨fun l m k hlm hmk hkd _ _ => ?_, fun i hi => ?_⟩
    · have hm : m = 1 := by omega
      subst hm
      simp only [quadFactor, one_ne_zero, if_false, if_true]
      intro h0
      rw [h0] at h
      linarith
    · have hi0 : i = 0 := by omega
      subst hi0
      simp only [quadFactor, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, div_one,
        zero_add, if_true, one_ne_zero, if_false, h2]
      norm_num
      nlinarith

/-- **Elliptic curves over a prime field never have Lorentzian local factors**: under the Hasse
bound `a² ≤ 4p` the factor `1 + |a| T + p T²` is not Lorentzian, since `a² = 4p` is impossible
for `p` prime. -/
theorem not_isLorentzianPoly_of_hasse {p : ℕ} (hp : p.Prime) {a : ℤ}
    (hasse : (a : ℝ) ^ 2 ≤ 4 * p) :
    ¬ IsLorentzianPoly 2 (bivariateCoeff 2 (quadFactor |(a : ℝ)| p)) := fun hL => by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have h := (isLorentzianPoly_quadFactor_iff (abs_nonneg _) hp0).mp hL
  rw [sq_abs] at h
  -- `|a| = 2 √p`, an integer
  have hsq : |(a : ℝ)| ^ 2 = (2 * √(p : ℝ)) ^ 2 := by
    rw [sq_abs, mul_pow, Real.sq_sqrt hp0.le]; linarith
  have heq := (pow_left_inj₀ (abs_nonneg _) (by positivity) two_ne_zero).mp hsq
  have hint : |(a : ℝ)| = ((|a| : ℤ) : ℝ) := by push_cast; rfl
  rw [hint] at heq
  exact (hp.irrational_sqrt.natCast_mul two_ne_zero).ne_int |a| (by exact_mod_cast heq.symm)

end GaloisForLFunctions.ArithmeticLorentzianGeometry
