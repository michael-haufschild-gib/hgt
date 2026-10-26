import GaloisForLFunctions.ArithmeticEffectivityTheory.TatesLimitLaw
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheThetaSurface
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.KernelCountsAreBlindToComplexQuartets

/-!
# Naive heights are traces, not kernel orders

On a curve datum of any genus the integral Frobenius ring `ℤ[F]` carries two quadratic-type
invariants of a ring element `P(F)`: the **kernel count** `deg P(F) = Π_i P(α_i)`, the order of a
finite group over `𝔽_q`, and the **Rosati form** `Tr(P(F) P(F)′) = Σ_i P(α_i) P(q/α_i)` (ACP).

* **Weil's theorem as a naive height** (`exists_naiveHeight_iff_unitary`). The integral Rosati form
  on `ℤ[F]` has a naive height — a function bounded below at bounded distance — iff the datum is
  unitary. The integral form decides the real one by the rounding principle
  (`intRosatiDeg_nonneg_iff_unitary`).
* **Kernel orders do not supply it** (`complexFake_kernelCounts_nonneg_no_naiveHeight`). On the
  complex fake (`q = 16`, Frobenius roots `±8i, ±2i`) every kernel count is a nonnegative real,
  while the integral Rosati form takes the value `−2304` at `F² + 16` and has no naive height.

* **The positive example** (`tateLimit_log_thetaChar`). The theta count with exponential
  characteristic is a naive height from counting: Tate's limit of `J ↦ log ϑ(J, t)` is exactly the
  polarization `π J²/t`. It is a trace-type form — and soft (`TheThetaSurface`).

The positivity a naive height needs pairs an eigenvalue with its reflection `q/α` (a trace), not
with its conjugate (a determinant). Over `𝔽_q` it comes from a polarization; orders of finite
kernels are determinants and are blind to complex quartets, which are the only off-line candidates
of `ζ`.
-/

noncomputable section

open Polynomial Finset

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

open ArithmeticCastelnuovoSeveri ArithmeticCorrespondencePositivity

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The **integral Rosati form** on `ℤ[F]`: `Tr(P(F) P(F)′)` for `P ∈ ℤ[X]`. -/
def intRosatiDeg (P : ℤ[X]) : ℝ := (rosatiDeg D (P.map (Int.castRingHom ℝ))).re

/-- The Rosati degree is quadratic under real scaling. -/
theorem rosatiDeg_smul (c : ℝ) (P : ℝ[X]) : rosatiDeg D (c • P) = (c : ℂ) ^ 2 * rosatiDeg D P := by
  simp only [rosatiDeg, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  ring

theorem intRosatiDeg_nsmul (m : ℕ) (P : ℤ[X]) :
    intRosatiDeg D (m • P) = (m : ℝ) ^ 2 * intRosatiDeg D P := by
  have hmap : (m • P).map (Int.castRingHom ℝ) = (m : ℝ) • P.map (Int.castRingHom ℝ) := by
    ext k
    simp [Polynomial.coeff_map]
  rw [intRosatiDeg, intRosatiDeg, hmap, rosatiDeg_smul, ← Complex.ofReal_pow,
    Complex.re_ofReal_mul]

/-- The Rosati degree of `Σ_{k ∈ S} c_k X^k` as a double sum with real weights. -/
theorem rosatiDeg_sum_monomials_eq (S : Finset ℕ) (c : ℕ → ℝ) :
    rosatiDeg D (∑ k ∈ S, C (c k) * X ^ k) =
      ((∑ k ∈ S, ∑ l ∈ S, c k * c l * (D.sqrtq ^ k * D.sqrtq ^ l * D.trace (Nat.dist k l)) : ℝ) : ℂ) := by
  rw [rosatiDeg_sum_monomials, CurveDatum.toeplitz]
  congr 1
  refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  ring

/-- **The integral Rosati form decides unitarity.** -/
theorem intRosatiDeg_nonneg_iff_unitary :
    (∀ P : ℤ[X], 0 ≤ intRosatiDeg D P) ↔ ∀ i, ‖D.β i‖ = 1 := by
  rw [← rosatiDeg_nonneg_iff_unitary]
  constructor
  · intro hI P
    have hint : ∀ m : ℕ → ℤ, 0 ≤ ∑ k ∈ P.support, ∑ l ∈ P.support,
        (m k : ℝ) * m l * (D.sqrtq ^ k * D.sqrtq ^ l * D.trace (Nat.dist k l)) := by
      intro m
      have h := hI (∑ k ∈ P.support, C (m k) * X ^ k)
      have hmap : (∑ k ∈ P.support, C (m k) * X ^ k : ℤ[X]).map (Int.castRingHom ℝ) =
          ∑ k ∈ P.support, C ((m k : ℝ)) * X ^ k := by
        simp [Polynomial.map_sum]
      rw [intRosatiDeg, hmap, rosatiDeg_sum_monomials_eq, Complex.ofReal_re] at h
      exact h
    refine ⟨_, sum_sum_nonneg_of_int P.support _ hint (fun k => P.coeff k), ?_⟩
    conv_lhs => rw [P.as_sum_support_C_mul_X_pow]
    exact rosatiDeg_sum_monomials_eq D P.support (fun k => P.coeff k)
  · intro h P
    obtain ⟨r, hr, hP⟩ := h (P.map (Int.castRingHom ℝ))
    rw [intRosatiDeg, hP, Complex.ofReal_re]
    exact hr

/-- **Weil's theorem as a naive height.** The integral Rosati form of a curve datum has a naive
height iff the datum is unitary. -/
theorem exists_naiveHeight_iff_unitary :
    (∃ h : ℤ[X] → ℝ, ∃ K B : ℝ, (∀ P, -K ≤ h P) ∧ ∀ P, |h P - intRosatiDeg D P| ≤ B) ↔
      ∀ i, ‖D.β i‖ = 1 := by
  rw [exists_naiveHeight_iff_nonneg (intRosatiDeg_nsmul D), intRosatiDeg_nonneg_iff_unitary]

/-- **Kernel counts are nonnegative, yet there is no naive height.** On the complex fake every
kernel count `deg P(F)` is a nonnegative real, and the integral Rosati form, whose value at
`F² + 16` is `−2304`, has no naive height. -/
theorem complexFake_kernelCounts_nonneg_no_naiveHeight :
    (∀ P : ℝ[X], ∃ r : ℝ, 0 ≤ r ∧ detDeg complexFake P = r) ∧
      intRosatiDeg complexFake (X ^ 2 + C 16) = -2304 ∧
      ¬ ∃ h : ℤ[X] → ℝ, ∃ K B : ℝ, (∀ P, -K ≤ h P) ∧
        ∀ P, |h P - intRosatiDeg complexFake P| ≤ B := by
  refine ⟨complexFake_detDeg_nonneg, ?_, fun hex =>
    complexFake_not_unitary ((exists_naiveHeight_iff_unitary complexFake).mp hex)⟩
  have hmap : (X ^ 2 + C 16 : ℤ[X]).map (Int.castRingHom ℝ) = X ^ 2 + C 16 := by
    rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, map_ofNat]
  rw [intRosatiDeg, hmap, complexFake_rosatiDeg_neg]
  norm_num

/-- **The Tate limit of the theta count is the free polarization**: Tate's machine applied to
`J ↦ log ϑ(J, t)` returns `π J²/t`. -/
theorem tateLimit_log_thetaChar {t : ℝ} (ht : 0 < t) :
    tateLimit (fun J => Real.log (thetaChar J t)) = fun J => Real.pi * J ^ 2 / t := by
  set h : ℝ → ℝ := fun J => Real.log (thetaChar J t)
  set q : ℝ → ℝ := fun J => Real.pi * J ^ 2 / t
  set B := max (Real.pi * t / 4) (Real.log (HurwitzZeta.evenKernel 0 t))
  have hB : ∀ J, |h J - q J| ≤ B := fun J => abs_log_thetaChar_sub_le J ht
  have hq2 : ∀ J : ℝ, q (2 • J) = 4 * q J := fun J => by
    simp only [q, nsmul_eq_mul, Nat.cast_ofNat]; ring
  have hC : ∀ J : ℝ, |h (2 • J) - 4 * h J| ≤ 5 * B := fun J => by
    have h1 := hB (2 • J)
    have h2 := hB J
    rw [hq2] at h1
    calc |h (2 • J) - 4 * h J| = |(h (2 • J) - 4 * q J) - 4 * (h J - q J)| := by ring_nf
      _ ≤ |h (2 • J) - 4 * q J| + |4 * (h J - q J)| := abs_sub _ _
      _ ≤ B + 4 * B := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]; linarith
      _ = 5 * B := by ring
  exact eq_of_two_nsmul_of_bounded (tateLimit_two_nsmul hC) hq2 (abs_tateLimit_sub_le hC)
    (fun J => by rw [abs_sub_comm]; exact hB J)

end GaloisForLFunctions.ArithmeticEffectivityTheory
