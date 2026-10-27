import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The Mertens budget of an elliptic curve is the strict Hasse bound

The `𝔽_q` calibration of `TheMertensBudgetForcesASimpleCriticalSpectrum` (P45) in genus one. For
`Z_E(u) = (1 − a u + q u²)/((1 − u)(1 − q u))` the Mertens row `μ_E(m)` is the coefficient sequence
of `1/Z_E` (`ellipticMertens`, `ellipticMertens_mul_eq`). With `t = a/√q`,
`μ_E(m + 1)/q^{(m+1)/2} = ((a − 1 − q)/√q) U_m`, where `U_0 = 1`, `U_1 = t`,
`U_{m+2} = t U_{m+1} − U_m` is the Chebyshev row of the second kind (`chebRow`).

* **Strict Hasse gives the budget** (`abs_ellipticMertens_energy_sub_le`). If `a² < 4q`, then
  `Σ_{m ≤ M} μ_E(m)²/q^m = 2(q + 1 − a)² M/(4q − a²) + O(1)`: writing `t = 2 cos θ`,
  `U_m sin θ = sin((m + 1)θ)` and the oscillating part is a Dirichlet sum bounded by `1/|sin θ|`.
* **The Hasse boundary has no budget** (`not_ellipticMertens_budget`). If `a² ≥ 4q` and
  `a ≠ q + 1`, then `|U_m| ≥ m + 1` and the energy grows at least quadratically.

So in genus one a Mertens budget exists exactly under the *strict* Hasse bound, with slope
`2 #E(𝔽_q)²/(4q − a²)`, while the prime-error budget exists under `a² ≤ 4q` (P42). The curves
with `a² = 4q` are pure with a double Frobenius eigenvalue and have no Mertens budget: the
Mertens budget is purity together with a simple spectrum, as over `ℤ` (P45), and its slope
`∝ 1/|α − β|²` is a repulsion energy that diverges when the eigenvalues collide.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-! ### The Chebyshev row -/

/-- The Chebyshev row `U_0 = 1`, `U_1 = t`, `U_{m+2} = t U_{m+1} − U_m` (`U_m(t/2)`). -/
def chebRow (t : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => t
  | m + 2 => t * chebRow t (m + 1) - chebRow t m

/-- `U_m(cos θ) sin θ = sin((m + 1)θ)`. -/
theorem chebRow_mul_sin (θ : ℝ) (m : ℕ) :
    chebRow (2 * Real.cos θ) m * Real.sin θ = Real.sin ((m + 1) * θ) := by
  have key : ∀ m : ℕ, chebRow (2 * Real.cos θ) m * Real.sin θ = Real.sin ((m + 1) * θ) ∧
      chebRow (2 * Real.cos θ) (m + 1) * Real.sin θ = Real.sin ((m + 2) * θ) := by
    intro m
    induction m with
    | zero =>
      refine ⟨by simp [chebRow], ?_⟩
      simp only [chebRow, Nat.cast_zero, zero_add]
      rw [show (2 : ℝ) * θ = 2 * θ from rfl, Real.sin_two_mul]
      ring
    | succ n ih =>
      refine ⟨?_, ?_⟩
      · rw [ih.2]; congr 1; push_cast; ring
      · have hx : (((n + 1 : ℕ) : ℝ) + 2) * θ = ((n : ℝ) + 2) * θ + θ := by push_cast; ring
        have hy : ((n : ℝ) + 1) * θ = ((n : ℝ) + 2) * θ - θ := by ring
        rw [hx]
        show (2 * Real.cos θ * chebRow (2 * Real.cos θ) (n + 1) - chebRow (2 * Real.cos θ) n) *
          Real.sin θ = _
        rw [sub_mul, mul_assoc, ih.2, ih.1, hy, Real.sin_add, Real.sin_sub]
        ring
  exact (key m).1

/-- `2 sin θ Σ_{k<M} cos(2(k + 1)θ) = sin((2M + 1)θ) − sin θ`. -/
theorem two_sin_mul_sum_cos (θ : ℝ) (M : ℕ) :
    2 * Real.sin θ * ∑ k ∈ range M, Real.cos (2 * (k + 1) * θ) =
      Real.sin ((2 * M + 1) * θ) - Real.sin θ := by
  induction M with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    have e1 : (2 * ((n + 1 : ℕ) : ℝ) + 1) * θ = (2 * n + 1) * θ + 2 * θ := by push_cast; ring
    have e2 : 2 * ((n : ℝ) + 1) * θ = (2 * n + 1) * θ + θ := by ring
    rw [e1, e2, Real.sin_add, Real.cos_add, Real.sin_two_mul, Real.cos_two_mul]
    linear_combination (-2 * Real.sin ((2 * n + 1) * θ)) * Real.sin_sq_add_cos_sq θ

/-- The Dirichlet bound `|Σ_{k<M} cos(2(k + 1)θ)| ≤ 1/|sin θ|`. -/
theorem abs_sum_cos_le {θ : ℝ} (hs : Real.sin θ ≠ 0) (M : ℕ) :
    |∑ k ∈ range M, Real.cos (2 * (k + 1) * θ)| ≤ 1 / |Real.sin θ| := by
  have hb : |Real.sin ((2 * M + 1) * θ) - Real.sin θ| ≤ 2 := by
    have h1 := Real.abs_sin_le_one ((2 * M + 1) * θ)
    have h2 := Real.abs_sin_le_one θ
    linarith [abs_sub (Real.sin ((2 * M + 1) * θ)) (Real.sin θ)]
  have h2 := congrArg abs (two_sin_mul_sum_cos θ M)
  rw [abs_mul, abs_mul, abs_two] at h2
  rw [le_div_iff₀ (abs_pos.mpr hs)]
  linarith

/-- `(Σ_{m<M} U_m²) sin²θ = M/2 − ½ Σ_{k<M} cos(2(k + 1)θ)` at `t = 2 cos θ`. -/
theorem sum_chebRow_sq_mul_sin_sq (θ : ℝ) (M : ℕ) :
    (∑ m ∈ range M, chebRow (2 * Real.cos θ) m ^ 2) * Real.sin θ ^ 2 =
      M / 2 - (∑ k ∈ range M, Real.cos (2 * (k + 1) * θ)) / 2 := by
  induction M with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, add_mul, ih, sum_range_succ, ← mul_pow, chebRow_mul_sin,
      Real.sin_sq_eq_half_sub, show 2 * (((n : ℝ) + 1) * θ) = 2 * ((n : ℝ) + 1) * θ by ring]
    push_cast
    ring

/-- At `t = 2 cos θ`, `sin θ ≠ 0`: `|Σ_{m<M} U_m² − M/(2 sin²θ)| ≤ 1/(2|sin θ|³)`. -/
theorem abs_sum_chebRow_sq_sub_le {θ : ℝ} (hs : Real.sin θ ≠ 0) (M : ℕ) :
    |∑ m ∈ range M, chebRow (2 * Real.cos θ) m ^ 2 - M / (2 * Real.sin θ ^ 2)| ≤
      1 / (2 * |Real.sin θ| ^ 3) := by
  have hs2 : 0 < Real.sin θ ^ 2 := by positivity
  have habs : 0 < |Real.sin θ| := abs_pos.mpr hs
  have h := sum_chebRow_sq_mul_sin_sq θ M
  have hE : ∑ m ∈ range M, chebRow (2 * Real.cos θ) m ^ 2 - M / (2 * Real.sin θ ^ 2) =
      -(∑ k ∈ range M, Real.cos (2 * (k + 1) * θ)) / (2 * Real.sin θ ^ 2) := by
    field_simp
    linear_combination 2 * h
  rw [hE, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.sin θ ^ 2),
    div_le_div_iff₀ (by positivity) (by positivity)]
  have hc := abs_sum_cos_le hs M
  rw [le_div_iff₀ habs] at hc
  have hsq : Real.sin θ ^ 2 = |Real.sin θ| ^ 2 := (sq_abs _).symm
  rw [hsq]
  nlinarith [pow_pos habs 2]

/-- **The strict Hasse range.** For `t² < 4`, `Σ_{m<M} U_m² = 2M/(4 − t²) + O(1)`. -/
theorem exists_abs_sum_chebRow_sq_sub_le {t : ℝ} (ht : t ^ 2 < 4) :
    ∃ C : ℝ, ∀ M : ℕ, |∑ m ∈ range M, chebRow t m ^ 2 - 2 * M / (4 - t ^ 2)| ≤ C := by
  have h1 : -1 ≤ t / 2 := by nlinarith
  have h2 : t / 2 ≤ 1 := by nlinarith
  have hc : Real.cos (Real.arccos (t / 2)) = t / 2 := Real.cos_arccos h1 h2
  have hs2 : Real.sin (Real.arccos (t / 2)) ^ 2 = 1 - t ^ 2 / 4 := by
    rw [Real.sin_arccos, Real.sq_sqrt (by nlinarith)]; ring
  have hs : Real.sin (Real.arccos (t / 2)) ≠ 0 := fun h => by rw [h] at hs2; nlinarith
  refine ⟨1 / (2 * |Real.sin (Real.arccos (t / 2))| ^ 3), fun M => ?_⟩
  have h := abs_sum_chebRow_sq_sub_le hs M
  rw [hc, show 2 * (t / 2) = t by ring, hs2] at h
  convert h using 3
  field_simp
  ring

/-! ### The Hasse boundary and beyond -/

/-- `U_m(−t) = (−1)^m U_m(t)`. -/
theorem chebRow_neg (t : ℝ) (m : ℕ) : chebRow (-t) m = (-1) ^ m * chebRow t m := by
  have key : ∀ m : ℕ, chebRow (-t) m = (-1) ^ m * chebRow t m ∧
      chebRow (-t) (m + 1) = (-1) ^ (m + 1) * chebRow t (m + 1) := by
    intro m
    induction m with
    | zero => exact ⟨by simp [chebRow], by simp [chebRow]⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      show -t * chebRow (-t) (n + 1) - chebRow (-t) n = _
      rw [ih.1, ih.2]
      simp only [chebRow, pow_succ]
      ring
  exact (key m).1

/-- For `t ≥ 2`, `U_m ≥ m + 1` and `U_{m+1} ≥ U_m + 1`. -/
theorem le_chebRow_of_two_le {t : ℝ} (ht : 2 ≤ t) (m : ℕ) :
    (m + 1 : ℝ) ≤ chebRow t m ∧ chebRow t m + 1 ≤ chebRow t (m + 1) := by
  induction m with
  | zero => exact ⟨by simp [chebRow], by simp [chebRow]; linarith⟩
  | succ n ih =>
    refine ⟨by push_cast; linarith [ih.1, ih.2], ?_⟩
    show chebRow t (n + 1) + 1 ≤ t * chebRow t (n + 1) - chebRow t n
    have h0 : 0 ≤ chebRow t (n + 1) := by linarith [ih.1, ih.2]
    nlinarith [ih.1, ih.2]

/-- On and beyond the Hasse boundary, `|U_m| ≥ m + 1`. -/
theorem le_abs_chebRow {t : ℝ} (ht : 4 ≤ t ^ 2) (m : ℕ) : (m + 1 : ℝ) ≤ |chebRow t m| := by
  rcases le_or_gt 0 t with h | h
  · have h2 : 2 ≤ t := by nlinarith
    exact (le_chebRow_of_two_le h2 m).1.trans (le_abs_self _)
  · have h2 : 2 ≤ -t := by nlinarith
    have := (le_chebRow_of_two_le h2 m).1
    rw [chebRow_neg] at this
    calc (m + 1 : ℝ) ≤ (-1) ^ m * chebRow t m := this
      _ ≤ |(-1) ^ m * chebRow t m| := le_abs_self _
      _ = |chebRow t m| := by rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- **No budget at or beyond the Hasse boundary.** For `t² ≥ 4` the Chebyshev energy is not
bounded by `S M + B`. -/
theorem not_chebRow_budget {t : ℝ} (ht : 4 ≤ t ^ 2) {S B : ℝ} :
    ¬ ∀ M : ℕ, ∑ m ∈ range M, chebRow t m ^ 2 ≤ S * M + B := by
  intro h
  set N := ⌈|S| + |B|⌉₊ with hN
  have hN' : |S| + |B| ≤ N := Nat.le_ceil _
  have hterm : ((N : ℝ) + 1) ^ 2 ≤ ∑ m ∈ range (N + 1), chebRow t m ^ 2 := by
    have h1 := le_abs_chebRow ht N
    have h2 : ((N : ℝ) + 1) ^ 2 ≤ chebRow t N ^ 2 := by
      rw [← sq_abs (chebRow t N)]; exact pow_le_pow_left₀ (by positivity) h1 2
    exact h2.trans (single_le_sum (fun m _ => sq_nonneg (chebRow t m))
      (mem_range.mpr (Nat.lt_succ_self N)))
  have hb := h (N + 1)
  push_cast at hb
  nlinarith [le_abs_self S, le_abs_self B, abs_nonneg S, abs_nonneg B]

/-! ### The Mertens row of an elliptic curve -/

/-- The `H¹` row of `1/(1 − a u + q u²)`: `c_0 = 1`, `c_1 = a`, `c_{m+2} = a c_{m+1} − q c_m`. -/
def h1Row (a q : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => a
  | m + 2 => a * h1Row a q (m + 1) - q * h1Row a q m

/-- `c_m = q^{m/2} U_m(a/√q)`. -/
theorem h1Row_eq {q : ℝ} (hq : 0 < q) (a : ℝ) (m : ℕ) :
    h1Row a q m = Real.sqrt q ^ m * chebRow (a / Real.sqrt q) m := by
  have hr2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  have hr : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  generalize Real.sqrt q = r at hr2 hr ⊢
  subst hr2
  have key : ∀ m : ℕ, h1Row a (r ^ 2) m = r ^ m * chebRow (a / r) m ∧
      h1Row a (r ^ 2) (m + 1) = r ^ (m + 1) * chebRow (a / r) (m + 1) := by
    intro m
    induction m with
    | zero => exact ⟨by simp [h1Row, chebRow], by simp [h1Row, chebRow]; field_simp⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      show a * h1Row a (r ^ 2) (n + 1) - r ^ 2 * h1Row a (r ^ 2) n = _
      rw [ih.1, ih.2]
      simp only [chebRow]
      field_simp
      ring
  exact (key m).1

/-- The Mertens row of an elliptic curve: `μ_E(0) = 1`, `μ_E(m + 1) = (a − 1 − q) c_m`, the
coefficients of `1/Z_E(u) = (1 − u)(1 − q u)/(1 − a u + q u²)` (`ellipticMertens_mul_eq`). -/
def ellipticMertens (a q : ℝ) : ℕ → ℝ
  | 0 => 1
  | m + 1 => (a - 1 - q) * h1Row a q m

open PowerSeries in
/-- `(Σ_m μ_E(m) u^m)(1 − a u + q u²) = (1 − u)(1 − q u)`: `μ_E` is the coefficient sequence of
`1/Z_E`. -/
theorem ellipticMertens_mul_eq (a q : ℝ) :
    mk (ellipticMertens a q) * (1 - C a * X + C q * X ^ 2) = (1 - X) * (1 - C q * X) := by
  have hR : ((1 - X) * (1 - C q * X) : PowerSeries ℝ) = 1 - C (1 + q) * X + C q * X ^ 2 := by
    simp only [map_add, map_one]; ring
  have hL : mk (ellipticMertens a q) * (1 - C a * X + C q * X ^ 2) =
      mk (ellipticMertens a q) - C a * (mk (ellipticMertens a q) * X) +
        C q * (mk (ellipticMertens a q) * X ^ 2) := by ring
  rw [hR, hL]
  ext n
  rcases n with _ | _ | _ | n
  · simp [ellipticMertens]
  · simp [coeff_mul_X_pow', coeff_succ_mul_X, ellipticMertens, h1Row]; ring
  · simp [coeff_mul_X_pow', coeff_succ_mul_X, ellipticMertens, h1Row]; ring
  · simp [coeff_mul_X_pow', coeff_succ_mul_X, ellipticMertens, h1Row]
    ring

/-- The normalized Mertens energy `Σ_{m=1}^{M} μ_E(m)²/q^m`. -/
def ellipticMertensEnergy (a q : ℝ) (M : ℕ) : ℝ :=
  ∑ m ∈ range M, ellipticMertens a q (m + 1) ^ 2 / q ^ (m + 1)

/-- The Mertens energy is `(q + 1 − a)²/q` times the Chebyshev energy at `t = a/√q`. -/
theorem ellipticMertensEnergy_eq {q : ℝ} (hq : 0 < q) (a : ℝ) (M : ℕ) :
    ellipticMertensEnergy a q M =
      (q + 1 - a) ^ 2 / q * ∑ m ∈ range M, chebRow (a / Real.sqrt q) m ^ 2 := by
  rw [ellipticMertensEnergy, mul_sum]
  refine sum_congr rfl fun m _ => ?_
  have hr2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  simp only [ellipticMertens]
  rw [h1Row_eq hq, mul_pow, mul_pow, ← pow_mul, show m * 2 = 2 * m by ring, pow_mul, hr2]
  field_simp
  ring

/-- **Strict Hasse gives the Mertens budget.** If `a² < 4q`, the Mertens energy of `E` is
`2(q + 1 − a)² M/(4q − a²) + O(1)`. -/
theorem abs_ellipticMertensEnergy_sub_le {a q : ℝ} (hq : 0 < q) (ha : a ^ 2 < 4 * q) :
    ∃ C : ℝ, ∀ M : ℕ,
      |ellipticMertensEnergy a q M - 2 * (q + 1 - a) ^ 2 * M / (4 * q - a ^ 2)| ≤ C := by
  have hr2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  have hr : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have ht : (a / Real.sqrt q) ^ 2 < 4 := by
    rw [div_pow, hr2, div_lt_iff₀ hq]; linarith
  obtain ⟨C, hC⟩ := exists_abs_sum_chebRow_sq_sub_le ht
  refine ⟨(q + 1 - a) ^ 2 / q * C, fun M => ?_⟩
  have hK : 0 ≤ (q + 1 - a) ^ 2 / q := by positivity
  have hslope : 2 * (q + 1 - a) ^ 2 * M / (4 * q - a ^ 2) =
      (q + 1 - a) ^ 2 / q * (2 * M / (4 - (a / Real.sqrt q) ^ 2)) := by
    rw [div_pow, hr2]
    have : 4 * q - a ^ 2 ≠ 0 := by linarith
    have : 4 - a ^ 2 / q ≠ 0 := by
      rw [sub_ne_zero]; intro h; rw [eq_div_iff hq.ne'] at h; linarith
    field_simp
  rw [ellipticMertensEnergy_eq hq, hslope, ← mul_sub, abs_mul, abs_of_nonneg hK]
  exact mul_le_mul_of_nonneg_left (hC M) hK

/-- **The Hasse boundary has no Mertens budget.** If `a² ≥ 4q` and `a ≠ q + 1`, the Mertens energy
of `E` is not bounded by `S M + B`. -/
theorem not_ellipticMertens_budget {a q : ℝ} (hq : 0 < q) (ha : 4 * q ≤ a ^ 2) (h1 : a ≠ q + 1)
    {S B : ℝ} : ¬ ∀ M : ℕ, ellipticMertensEnergy a q M ≤ S * M + B := by
  intro h
  have hr2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  have ht : 4 ≤ (a / Real.sqrt q) ^ 2 := by
    rw [div_pow, hr2, le_div_iff₀ hq]; linarith
  have hK : 0 < (q + 1 - a) ^ 2 / q := by
    have : q + 1 - a ≠ 0 := fun h' => h1 (by linarith)
    positivity
  refine not_chebRow_budget ht (S := S / ((q + 1 - a) ^ 2 / q)) (B := B / ((q + 1 - a) ^ 2 / q))
    fun M => ?_
  have hM := h M
  rw [ellipticMertensEnergy_eq hq] at hM
  rw [div_mul_eq_mul_div, ← add_div, le_div_iff₀ hK, mul_comm]
  exact hM

/-- **The genus-one Mertens budget law.** For `q > 0` and `a ≠ q + 1`, the Mertens row of
`Z_E(u) = (1 − a u + q u²)/((1 − u)(1 − q u))` has a linear energy budget exactly under the strict
Hasse bound `a² < 4q`. -/
theorem ellipticMertens_budget_iff {a q : ℝ} (hq : 0 < q) (h1 : a ≠ q + 1) :
    (∃ S B : ℝ, ∀ M : ℕ, ellipticMertensEnergy a q M ≤ S * M + B) ↔ a ^ 2 < 4 * q := by
  constructor
  · rintro ⟨S, B, h⟩
    by_contra ha
    exact not_ellipticMertens_budget hq (not_lt.mp ha) h1 h
  · intro ha
    obtain ⟨C, hC⟩ := abs_ellipticMertensEnergy_sub_le hq ha
    refine ⟨2 * (q + 1 - a) ^ 2 / (4 * q - a ^ 2), C, fun M => ?_⟩
    have := (abs_le.mp (hC M)).2
    have e : 2 * (q + 1 - a) ^ 2 * (M : ℝ) / (4 * q - a ^ 2) =
        2 * (q + 1 - a) ^ 2 / (4 * q - a ^ 2) * M := by ring
    linarith

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
