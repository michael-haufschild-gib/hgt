import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FrobeniusSpanHodgeIndexIsRH
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FakeCurvesAndTheWindowLaw
import GaloisForLFunctions.RHTower.FractionalPartZeta

/-!
# Kernel counts are blind to complex quartets

A ring element `P(F)` of a curve has two quadratic-type invariants. Its **degree**, the number of
points in its kernel on the Jacobian, is the determinant `Π_i P(α_i)` over the Frobenius
eigenvalues; it pairs each eigenvalue with its complex conjugate. Its **Rosati degree**
`Tr(P(F) P(F)′) = Σ_i P(α_i) P(q/α_i)` pairs each eigenvalue with its reflection under the
functional equation. Over `𝔽_q` both are nonnegative, the first because it counts points, the second
because of a polarization. They carry very different information.

* **The determinant degree** (`detDeg`) is multiplicative (`detDeg_mul`) and real
  (`conj_detDeg`). On every curve datum without real eigenvalues it is a nonnegative real for every
  real polynomial (`detDeg_nonneg_of_im_ne_zero`): conjugation pairs the factors into `|·|²`.
* **The Rosati degree** (`rosatiDeg`) is the Toeplitz form of the power sums in the coefficients
  `c_k q^{k/2}` (`rosatiDeg_sum_monomials`), and its nonnegativity on all of `ℝ[F]` is exactly
  unitarity (`rosatiDeg_nonneg_iff_unitary`): Weil's theorem in ring form.
* **Calibration.** The golden datum has a real off-line pair and a ring element of degree `−1`
  (`goldenDatum_detDeg_two_sub_X`).
* **A complex fake** (`complexFake`): `q = 16`, Frobenius roots `±8i, ±2i` of the integral Weil-type
  polynomial `X⁴ + 68X² + 256` (`complexFake_eigenvalue_root`). It has nonnegative point counts at
  every level (`complexFake_pointCount_nonneg`), a nonnegative kernel count for every ring element
  (`complexFake_detDeg_nonneg`), and violates Hasse–Weil (`complexFake_not_hasseWeil`): it is not
  unitary, and the Rosati degree of `F² + q` is `−2304` (`complexFake_rosatiDeg_neg`).
* **`ζ`.** Zeros of `ζ` in the critical strip are not real (`zeta_strip_zero_im_ne_zero`): every
  off-line candidate of `ζ` is of the complex type that the determinant pairing cannot see.

So effectivity by counting kernels forces purity only in genus one (Hasse); from genus two on it
is blind to complex off-line quartets, which are the only off-line candidates of `ζ`. The sign of
Weil's argument is of trace (Rosati) type: it pairs `ρ` with `1 − ρ̄`, not with `ρ̄`.
-/

open Complex Polynomial Finset
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open ArithmeticCastelnuovoSeveri

section CurveData

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The Frobenius eigenvalue `α_i = √q β_i`. -/
def eigenvalue (i : ι) : ℂ := (D.sqrtq : ℂ) * D.β i

theorem eigenvalue_conjPerm (i : ι) : eigenvalue D (D.conjPerm i) = conj (eigenvalue D i) := by
  rw [eigenvalue, eigenvalue, D.β_conjPerm, map_mul, Complex.conj_ofReal]

/-- Real polynomials commute with complex conjugation. -/
theorem aeval_conj (z : ℂ) (P : ℝ[X]) : aeval (conj z) P = conj (aeval z P) := by
  have h := Polynomial.aeval_algHom_apply Complex.conjAe z P
  simpa using h

/-- The **determinant degree** `deg P(F) = Π_i P(α_i)`: over `𝔽_q` the number of points in the
kernel of `P(F)` on the Jacobian. -/
def detDeg (P : ℝ[X]) : ℂ := ∏ i, aeval (eigenvalue D i) P

/-- The **Rosati degree** `Tr(P(F) P(F)′) = Σ_i P(α_i) P(q/α_i)`. -/
def rosatiDeg (P : ℝ[X]) : ℂ :=
  ∑ i, aeval (eigenvalue D i) P * aeval (eigenvalue D (D.fePerm i)) P

/-- The degree is multiplicative. -/
theorem detDeg_mul (P Q : ℝ[X]) : detDeg D (P * Q) = detDeg D P * detDeg D Q := by
  simp only [detDeg, map_mul, prod_mul_distrib]

/-- The degree is real. -/
theorem conj_detDeg (P : ℝ[X]) : conj (detDeg D P) = detDeg D P := by
  rw [detDeg, map_prod]
  simp_rw [← aeval_conj, ← eigenvalue_conjPerm]
  exact Equiv.prod_comp D.conjPerm (fun i => aeval (eigenvalue D i) P)

/-- **Without real eigenvalues every degree is a nonnegative real.** Conjugation maps the
eigenvalues of positive imaginary part bijectively onto those of negative imaginary part, so the
degree is `A · conj A`. -/
theorem detDeg_nonneg_of_im_ne_zero (hD : ∀ i, (D.β i).im ≠ 0) (P : ℝ[X]) :
    ∃ r : ℝ, 0 ≤ r ∧ detDeg D P = r := by
  classical
  set F : ι → ℂ := fun i => aeval (eigenvalue D i) P
  have him : ∀ i, (D.β (D.conjPerm i)).im = -(D.β i).im := fun i => by
    rw [D.β_conjPerm, Complex.conj_im]
  set T := univ.filter fun i => 0 < (D.β i).im
  have hsplit : detDeg D P = (∏ i ∈ T, F i) * ∏ i ∈ univ.filter (fun i => ¬ 0 < (D.β i).im), F i :=
    (prod_filter_mul_prod_filter_not univ _ F).symm
  have hneg : ∏ i ∈ univ.filter (fun i => ¬ 0 < (D.β i).im), F i = ∏ i ∈ T, conj (F i) := by
    refine prod_nbij' (fun a => D.conjPerm.symm a) (fun a => D.conjPerm a) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, T] at ha ⊢
      have h1 := him (D.conjPerm.symm a)
      rw [Equiv.apply_symm_apply] at h1
      rcases lt_or_gt_of_ne (hD (D.conjPerm.symm a)) with h | h
      · linarith
      · exact h
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, T] at ha ⊢
      rw [him]; linarith
    · intro a _; simp
    · intro a _; simp
    · intro a _
      simp only [F]
      rw [← aeval_conj, ← eigenvalue_conjPerm, Equiv.apply_symm_apply]
  refine ⟨Complex.normSq (∏ i ∈ T, F i), Complex.normSq_nonneg _, ?_⟩
  rw [hsplit, hneg, ← map_prod, Complex.mul_conj]

/-! ### The Rosati degree is the Toeplitz form -/

/-- `Σ_i β_i^k β_{fe(i)}^l` is the power sum at `|k − l|`. -/
theorem sum_pow_mul_pow_fePerm (k l : ℕ) :
    ∑ i, D.β i ^ k * D.β (D.fePerm i) ^ l = D.powerSum (Nat.dist k l) := by
  rcases le_total l k with h | h
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h, CurveDatum.powerSum]
    refine sum_congr rfl fun i _ => ?_
    rw [show k = (k - l) + l by omega, pow_add, mul_assoc, ← mul_pow, mul_comm (D.β i),
      D.β_fePerm, one_pow, mul_one, Nat.add_sub_cancel]
  · rw [Nat.dist_eq_sub_of_le h, CurveDatum.powerSum,
      ← Equiv.sum_comp D.fePerm (fun i => D.β i ^ (l - k))]
    refine sum_congr rfl fun i _ => ?_
    rw [show l = (l - k) + k by omega, pow_add, mul_comm, mul_assoc, ← mul_pow, D.β_fePerm,
      one_pow, mul_one, Nat.add_sub_cancel]

theorem aeval_sum_monomials (S : Finset ℕ) (c : ℕ → ℝ) (z : ℂ) :
    aeval z (∑ k ∈ S, C (c k) * X ^ k) = ∑ k ∈ S, (c k : ℂ) * z ^ k := by
  simp [map_sum]

/-- **The Rosati degree is the Toeplitz form of the power sums** in the normalized coefficients
`c_k q^{k/2}`. -/
theorem rosatiDeg_sum_monomials (S : Finset ℕ) (c : ℕ → ℝ) :
    rosatiDeg D (∑ k ∈ S, C (c k) * X ^ k) = (D.toeplitz S (fun k => c k * D.sqrtq ^ k) : ℝ) := by
  simp only [rosatiDeg, aeval_sum_monomials, sum_mul_sum, eigenvalue, CurveDatum.toeplitz]
  rw [sum_comm]
  push_cast
  refine sum_congr rfl fun k _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun l _ => ?_
  rw [← D.powerSum_eq_trace, ← sum_pow_mul_pow_fePerm, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  ring

/-- **Weil's theorem in ring form.** The Rosati degree is nonnegative on every real polynomial in
`F` iff the datum is unitary. -/
theorem rosatiDeg_nonneg_iff_unitary :
    (∀ P : ℝ[X], ∃ r : ℝ, 0 ≤ r ∧ rosatiDeg D P = r) ↔ ∀ i, ‖D.β i‖ = 1 := by
  rw [← D.hodgeIndexOnSpan_iff_unitary]
  constructor
  · intro h S d
    obtain ⟨r, hr, hP⟩ := h (∑ k ∈ S, C (d k) * X ^ k)
    rw [rosatiDeg_sum_monomials] at hP
    rw [D.spanDefect_eq_toeplitz, Complex.ofReal_injective hP]
    exact hr
  · intro h P
    have hsq : ∀ k, D.sqrtq ^ k ≠ 0 := fun k => pow_ne_zero _ D.sqrtq_pos.ne'
    refine ⟨D.toeplitz P.support (fun k => P.coeff k * D.sqrtq ^ k), ?_, ?_⟩
    · have := h P.support (fun k => P.coeff k)
      rwa [D.spanDefect_eq_toeplitz] at this
    · conv_lhs => rw [P.as_sum_support_C_mul_X_pow]
      rw [rosatiDeg_sum_monomials]

end CurveData

/-! ### The golden datum: a real pair and a ring element of degree `−1` -/

open Real in
/-- **`deg(2 − F) = −1` on the golden curve**: `(2 − √5 φ)(2 − √5 φ⁻¹) = 9 − 2√5 · √5`. -/
theorem goldenDatum_detDeg_two_sub_X : detDeg goldenDatum (C 2 - X) = -1 := by
  have hφ : goldenRatio + goldenRatio⁻¹ = Real.sqrt 5 := by
    rw [inv_goldenRatio]; simp only [goldenRatio, goldenConj]; ring
  have hs : goldenDatum.sqrtq = Real.sqrt 5 := by simp [CurveDatum.sqrtq, goldenDatum]
  have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hinv : goldenRatio * goldenRatio⁻¹ = 1 := mul_inv_cancel₀ goldenRatio_ne_zero
  have key : (2 - Real.sqrt 5 * goldenRatio) * (2 - Real.sqrt 5 * goldenRatio⁻¹) = -1 := by
    have : (2 - Real.sqrt 5 * goldenRatio) * (2 - Real.sqrt 5 * goldenRatio⁻¹) =
        4 - 2 * Real.sqrt 5 * (goldenRatio + goldenRatio⁻¹) +
          Real.sqrt 5 * Real.sqrt 5 * (goldenRatio * goldenRatio⁻¹) := by ring
    rw [this, hφ, hinv]
    linear_combination (-1 : ℝ) * h5
  have hval : ∀ i, aeval (eigenvalue goldenDatum i) (C 2 - X : ℝ[X]) =
      2 - eigenvalue goldenDatum i := fun i => by simp
  have e0 : eigenvalue goldenDatum 0 = ((Real.sqrt 5 * goldenRatio : ℝ) : ℂ) := by
    rw [eigenvalue, hs]; simp [goldenDatum]
  have e1 : eigenvalue goldenDatum 1 = ((Real.sqrt 5 * goldenRatio⁻¹ : ℝ) : ℂ) := by
    rw [eigenvalue, hs]; simp [goldenDatum]
  rw [detDeg, Fin.prod_univ_two, hval, hval, e0, e1]
  exact_mod_cast key

/-! ### A complex fake of genus two -/

/-- The **complex fake**: `q = 16`, normalized eigenvalues `2i, −2i, i/2, −i/2`, i.e. Frobenius roots
`±8i, ±2i`. Conjugation swaps `0 ↔ 1`, `2 ↔ 3`; the functional equation swaps `0 ↔ 3`, `1 ↔ 2`. -/
def complexFake : CurveDatum (Fin 4) where
  q := 16
  one_lt_q := by norm_num
  β := ![2 * I, -(2 * I), I / 2, -(I / 2)]
  conjPerm := ⟨![1, 0, 3, 2], ![1, 0, 3, 2], by decide, by decide⟩
  β_conjPerm i := by
    have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
    fin_cases i <;> simp [map_div₀, h2] <;> ring
  fePerm := ⟨![3, 2, 1, 0], ![3, 2, 1, 0], by decide, by decide⟩
  β_fePerm i := by
    fin_cases i <;> simp <;> ring_nf <;> simp [Complex.I_sq]

theorem complexFake_sqrtq : complexFake.sqrtq = 4 := by
  rw [CurveDatum.sqrtq, show complexFake.q = 4 ^ 2 by norm_num [complexFake]]
  exact Real.sqrt_sq (by norm_num)

theorem complexFake_eigenvalue :
    eigenvalue complexFake = ![8 * I, -(8 * I), 2 * I, -(2 * I)] := by
  funext i
  rw [eigenvalue, complexFake_sqrtq]
  fin_cases i <;> simp [complexFake] <;> ring

/-- The Frobenius roots of the complex fake are the roots of `X⁴ + 68X² + 256`, an integral
Weil-type polynomial for `q = 16`. -/
theorem complexFake_eigenvalue_root (i : Fin 4) :
    eigenvalue complexFake i ^ 4 + 68 * eigenvalue complexFake i ^ 2 + 256 = 0 := by
  rw [complexFake_eigenvalue]
  fin_cases i <;> simp <;> ring_nf <;> simp [Complex.I_sq, Complex.I_pow_four] <;> norm_num

theorem complexFake_norm_β (i : Fin 4) : ‖complexFake.β i‖ = if i.val < 2 then 2 else 1 / 2 := by
  fin_cases i <;> simp [complexFake]

/-- The complex fake has no real eigenvalue. -/
theorem complexFake_im_ne_zero (i : Fin 4) : (complexFake.β i).im ≠ 0 := by
  fin_cases i <;> simp [complexFake]

/-- **Every kernel count of the complex fake is nonnegative.** -/
theorem complexFake_detDeg_nonneg (P : ℝ[X]) : ∃ r : ℝ, 0 ≤ r ∧ detDeg complexFake P = r :=
  detDeg_nonneg_of_im_ne_zero complexFake complexFake_im_ne_zero P

theorem complexFake_trace_one : complexFake.trace 1 = 0 := by
  simp [CurveDatum.trace, CurveDatum.powerSum, Fin.sum_univ_four, complexFake]

theorem complexFake_trace_two : complexFake.trace 2 = -(17 / 2) := by
  simp [CurveDatum.trace, CurveDatum.powerSum, Fin.sum_univ_four, complexFake]
  ring_nf
  simp [Complex.I_sq]
  norm_num

theorem complexFake_abs_trace_le (j : ℕ) : |complexFake.trace j| ≤ 2 * 2 ^ j + 2 * (1 / 2) ^ j := by
  have h1 : |complexFake.trace j| ≤ ‖complexFake.powerSum j‖ := Complex.abs_re_le_norm _
  have h2 : ‖complexFake.powerSum j‖ ≤ ∑ i, ‖complexFake.β i‖ ^ j := by
    rw [CurveDatum.powerSum]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [norm_pow]
  have h3 : ∑ i, ‖complexFake.β i‖ ^ j = 2 * 2 ^ j + 2 * (1 / 2) ^ j := by
    simp [Fin.sum_univ_four, complexFake]; ring
  linarith

/-- **The complex fake has nonnegative point counts at every level `m ≥ 1`.** -/
theorem complexFake_pointCount_nonneg {m : ℕ} (hm : 1 ≤ m) : 0 ≤ complexFake.pointCount m := by
  rw [CurveDatum.pointCount, complexFake_sqrtq, show complexFake.q = 16 by rfl]
  rcases Nat.lt_or_ge m 2 with h | h
  · obtain rfl : m = 1 := by omega
    rw [complexFake_trace_one]; norm_num
  · have hb := complexFake_abs_trace_le m
    have htr : (4 : ℝ) ^ m * complexFake.trace m ≤ 2 * 8 ^ m + 2 * 2 ^ m := by
      have h4 : (4 : ℝ) ^ m * complexFake.trace m ≤ 4 ^ m * (2 * 2 ^ m + 2 * (1 / 2) ^ m) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans hb) (by positivity)
      have e1 : (4 : ℝ) ^ m * (2 * 2 ^ m + 2 * (1 / 2) ^ m) = 2 * 8 ^ m + 2 * 2 ^ m := by
        have a1 : (4 : ℝ) ^ m * 2 ^ m = 8 ^ m := by rw [← mul_pow]; norm_num
        have a2 : (4 : ℝ) ^ m * (1 / 2) ^ m = 2 ^ m := by rw [← mul_pow]; norm_num
        linear_combination 2 * a1 + 2 * a2
      linarith
    have h16 : (16 : ℝ) ^ m = 2 ^ m * 8 ^ m := by rw [← mul_pow]; norm_num
    have h2m : (4 : ℝ) ≤ 2 ^ m := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) h
    have h8 : (2 : ℝ) ^ m ≤ 8 ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 8) m]

/-- The complex fake is not unitary. -/
theorem complexFake_not_unitary : ¬ ∀ i, ‖complexFake.β i‖ = 1 := by
  intro h
  have := h 0
  rw [complexFake_norm_β] at this
  norm_num at this

/-- **The complex fake violates Hasse–Weil**: `|Σ β_i²| = 17/2 > 4 = 2g`. -/
theorem complexFake_not_hasseWeil : (Fintype.card (Fin 4) : ℝ) < |complexFake.trace 2| := by
  rw [complexFake_trace_two]; norm_num

/-- **The Rosati degree sees the complex fake**: `Tr((F² + q)(F² + q)′) = −2304`. -/
theorem complexFake_rosatiDeg_neg : rosatiDeg complexFake (X ^ 2 + C 16) = -2304 := by
  have hfe : ∀ i, complexFake.fePerm i = ![3, 2, 1, 0] i := fun i => rfl
  simp only [rosatiDeg, hfe, complexFake_eigenvalue, map_add, map_pow, aeval_X, aeval_C]
  simp [Fin.sum_univ_four]
  ring_nf
  simp [Complex.I_sq]
  norm_num

/-- **Point counts and kernel counts do not certify purity.** The complex fake has nonnegative
point counts at every level and a nonnegative kernel count for every ring element, and is not
unitary. -/
theorem counts_do_not_force_purity :
    ∃ D : CurveDatum (Fin 4), (∀ m, 1 ≤ m → 0 ≤ D.pointCount m) ∧
      (∀ P : ℝ[X], ∃ r : ℝ, 0 ≤ r ∧ detDeg D P = r) ∧ ¬ ∀ i, ‖D.β i‖ = 1 :=
  ⟨complexFake, fun _ hm => complexFake_pointCount_nonneg hm, complexFake_detDeg_nonneg,
    complexFake_not_unitary⟩

/-! ### `ζ`: its off-line candidates are complex -/

/-- **Zeros of `ζ` in the critical strip are not real.** -/
theorem zeta_strip_zero_im_ne_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) : ρ.im ≠ 0 := by
  intro him
  have hρr : ρ = ((ρ.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  exact RHTower.riemannZeta_ne_zero_of_ofReal_mem_Ioo h0 h1 (hρr ▸ hρ)

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
