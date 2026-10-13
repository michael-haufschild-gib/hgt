import GaloisForLFunctions.RHTower.FamilySeamAssembly
import GaloisForLFunctions.RHTower.FamilyClassMass

/-!
# The Frobenius norms of the characters modulo `q`, summed, with an explicit majorant

Summed over all characters modulo `q`, `tr G̃²(μ₀ + P_χ)` is the main term `φ(q) (TL/2π)(ℓ₁² + L²/3)` up to
`φ(q) K M(q)`, with the explicit majorant (`famMaj`)

`M = (1+log q)² l² log L + TLℓ₁²/l² + (1+log q) l √X + (1 + log²(log q + 8)) TL²
     + L³(1 + log L)(X/q + L) + L l log l ((1+log q)² l² + q l² + (X/q + 1) L²)`

(`family_frob_all_le`).  The six terms come from the archimedean diagonal, the archimedean–prime cross terms,
the prime diagonal (Mertens), the `∫Φ²|x|` correction, the residue-class Montgomery–Vaughan off-diagonal
term and the end effects (residue-class masses, `FamilyClassMass`).  Each is `o(T l L²)` as soon as
`q ≤ T^{1−δ}` and `X ≤ q T^{1−δ}`.

Over the nontrivial characters (`family_frob_nontriv`), an odd character is compared with the even
archimedean factor at the cost `(1+η)·(even part) + (1+1/η)·(parity shift)`, and the trivial character only
adds a nonnegative term.
-/

open MeasureTheory Real Set Zeta23 Zeta23.ThmE Zeta23.PrimeSide
open scoped ArithmeticFunction

noncomputable section

namespace RHTower

/-- The explicit majorant of the per-character Frobenius error of the family. -/
def famMaj (q : ℕ) (T L l X : ℝ) : ℝ :=
  (1 + Real.log q) ^ 2 * l ^ 2 * Real.log L
  + T * L * ell1q q T ^ 2 / l ^ 2
  + (1 + Real.log q) * l * Real.sqrt X
  + (1 + Real.log (Real.log q + 8) ^ 2) * T * L ^ 2
  + L ^ 3 * (1 + Real.log L) * (X / q + L)
  + L * l * Real.log l * ((1 + Real.log q) ^ 2 * l ^ 2 + q * l ^ 2 + (X / q + 1) * L ^ 2)

theorem trGt2Nu_nonneg (ν : ℝ → ℝ) (p : Setting) (F : LocalFun) : 0 ≤ trGt2Nu ν p F := by
  unfold trGt2Nu
  exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _)

variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem log_X_eq (p : Setting) : Real.log p.X = p.L := Real.log_exp _

/-- `∑_{n ≤ X} a_n² ≤ (1/2 + |C|) L²`. -/
theorem sum_acoef_sq_le_of_cheb {C : ℝ}
    (hC : ∀ x : ℝ, 2 ≤ x → |∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Λ n : ℝ) ^ 2 / n - Real.log x ^ 2 / 2|
      ≤ C * Real.log x)
    (hF : LocalHypsCoreW cϱ p F) :
    ∑ n ∈ primeRange p.X, acoef n ^ 2 ≤ (1 / 2 + |C|) * p.L ^ 2 := by
  have hX2 := two_le_X_of_coreW hF
  have h := (abs_le.mp (hC p.X hX2)).2
  rw [log_X_eq] at h
  have hL1 : 1 ≤ p.L := by have := hF.eight_le_L; linarith
  have e : ∑ n ∈ primeRange p.X, acoef n ^ 2 = ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, (Λ n : ℝ) ^ 2 / n := by
    unfold primeRange; exact Finset.sum_congr rfl fun n _ => acoef_sq n
  rw [e]
  have h1 : C * p.L ≤ |C| * p.L ^ 2 := by
    calc C * p.L ≤ |C| * p.L := mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
      _ ≤ |C| * p.L ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg C)
  nlinarith

/-- `∑_{n ≤ X} a_n² (n + q) ≤ |C'| X L + q (1/2 + |C|) L²`. -/
theorem sum_acoef_sq_mul_le_of_cheb {C C' : ℝ}
    (hC : ∀ x : ℝ, 2 ≤ x → |∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Λ n : ℝ) ^ 2 / n - Real.log x ^ 2 / 2|
      ≤ C * Real.log x)
    (hC' : ∀ x : ℝ, 2 ≤ x → ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Λ n : ℝ) ^ 2 ≤ C' * x * Real.log x)
    (hF : LocalHypsCoreW cϱ p F) (q : ℕ) :
    ∑ n ∈ primeRange p.X, acoef n ^ 2 * ((n : ℝ) + q)
      ≤ |C'| * p.X * p.L + q * ((1 / 2 + |C|) * p.L ^ 2) := by
  have hX2 := two_le_X_of_coreW hF
  have hS2 := sum_acoef_sq_le_of_cheb hC hF
  have h1 : ∑ n ∈ primeRange p.X, acoef n ^ 2 * (n : ℝ)
      = ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, (Λ n : ℝ) ^ 2 := by
    unfold primeRange
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℝ) ≠ 0 := by
      have := (Finset.mem_Ioc.mp hn).1; positivity
    rw [acoef_sq]; field_simp
  have h2 := hC' p.X hX2
  rw [log_X_eq] at h2
  have hXL : 0 ≤ p.X * p.L := by
    have := hF.eight_le_L; have : 0 < p.X := Real.exp_pos _; positivity
  have h3 : C' * p.X * p.L ≤ |C'| * p.X * p.L := by
    rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self C') hXL
  have e : ∑ n ∈ primeRange p.X, acoef n ^ 2 * ((n : ℝ) + q)
      = ∑ n ∈ primeRange p.X, acoef n ^ 2 * (n : ℝ) + q * ∑ n ∈ primeRange p.X, acoef n ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [e, h1]
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have := mul_le_mul_of_nonneg_left hS2 hq
  linarith

/-- `∫ Φ² |x| ≤ (8 + 8 log(c_ϱ/4)) (1 + log L)`. -/
theorem integral_Phi_sq_mul_abs_le' (hF : LocalHypsCoreW cϱ p F) :
    ∫ x, F.Phi x ^ 2 * |x| ≤ (8 + 8 * Real.log (cϱ / 4)) * (1 + Real.log p.L) := by
  have h := hF.integral_Phi_sq_mul_abs_le
  have hc4 : 1 ≤ cϱ / 4 := by have := hF.four_le_cϱ; linarith
  have hL8 := hF.eight_le_L
  have hw1 := hF.one_le_w
  have hlogc : 0 ≤ Real.log (cϱ / 4) := Real.log_nonneg hc4
  have hlogL : 0 ≤ Real.log p.L := Real.log_nonneg (by linarith)
  have hc0 : 0 < cϱ := by have := hF.four_le_cϱ; linarith
  have hL0 : 0 < p.L := by linarith
  have hw0 : 0 < p.w := by linarith
  have hle : Real.log (cϱ * p.L / (4 * p.w)) ≤ Real.log (cϱ / 4) + Real.log p.L := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ (by positivity)]
    have : cϱ / 4 * p.L * (4 * p.w) = cϱ * p.L * p.w := by ring
    rw [this]
    have hcL : 0 ≤ cϱ * p.L := by positivity
    nlinarith
  nlinarith

/-- `∫ Φ² ≤ 2π L`. -/
theorem integral_Phi_sq_le_L (hF : LocalHypsCoreW cϱ p F) : ∫ x, F.Phi x ^ 2 ≤ 2 * π * p.L := by
  rw [hF.Phi_sq_integral]
  have hb := hF.b_le_a.trans hF.a_le_one
  have hL : 0 ≤ p.L := by have := hF.eight_le_L; linarith
  have : 2 * π * F.b * p.L ≤ 2 * π * 1 * p.L := by gcongr
  linarith

/-- `log(⌊X⌋ + 1) ≤ L + 1`. -/
theorem log_floor_X_add_one_le (hF : LocalHypsCoreW cϱ p F) :
    Real.log ((⌊p.X⌋₊ : ℝ) + 1) ≤ p.L + 1 := by
  have hX2 := two_le_X_of_coreW hF
  have hfl : (⌊p.X⌋₊ : ℝ) ≤ p.X := Nat.floor_le (by linarith)
  have h1 : Real.log ((⌊p.X⌋₊ : ℝ) + 1) ≤ Real.log (2 * p.X) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_mul (by norm_num) (by linarith), log_X_eq] at h1
  have : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  linarith

theorem one_div_two_pi_sq_le_one : (1 : ℝ) / (2 * π ^ 2) ≤ 1 := by
  rw [div_le_one (by positivity)]; nlinarith only [Real.pi_gt_three]

theorem one_div_two_pi_le_one : (1 : ℝ) / (2 * π) ≤ 1 := by
  rw [div_le_one (by positivity)]; linarith only [Real.pi_gt_three]

theorem one_div_pi_le_one : (1 : ℝ) / π ≤ 1 := by
  rw [div_le_one (by positivity)]; linarith only [Real.pi_gt_three]

/-- The archimedean, prime-diagonal and cross errors against the first four majorant terms. -/
theorem frob_arch_le {Cm CΓ Cx B K lq l logL T L ell sX y f1 f2 f3 f4 : ℝ} (hCm : 0 ≤ Cm)
    (hCx : 0 ≤ Cx) (hB : 0 ≤ B) (hK : 0 ≤ K) (hlq : 0 ≤ lq) (hl : 0 < l) (hlogL : 0 ≤ logL) (hT : 0 ≤ T)
    (hL : 0 ≤ L) (hsX : 0 ≤ sX) (hy : 0 ≤ y) (hf1 : f1 = (1 + lq) ^ 2 * l ^ 2 * logL)
    (hf2 : f2 = T * L * ell ^ 2 / l ^ 2) (hf3 : f3 = (1 + lq) * l * sX) (hf4 : f4 = (1 + y) * T * L ^ 2) :
    Cm * (1 + lq) ^ 2 * (l ^ 2 * logL) + |CΓ| / (2 * π) * (T * L * ell ^ 2 / l ^ 2)
      + 2 * (Cx * (1 + lq) * (l * sX)) + (B + K * y) / π * (T * L ^ 2)
      ≤ (Cm + |CΓ| + 2 * Cx + B + K) * (f1 + f2 + f3 + f4) := by
  have hf10 : 0 ≤ f1 := by rw [hf1]; positivity
  have hf20 : 0 ≤ f2 := by rw [hf2]; positivity
  have hf30 : 0 ≤ f3 := by rw [hf3]; positivity
  have hf40 : 0 ≤ f4 := by rw [hf4]; positivity
  have e1 : Cm * (1 + lq) ^ 2 * (l ^ 2 * logL) = Cm * f1 := by rw [hf1]; ring
  have e2 : |CΓ| / (2 * π) * (T * L * ell ^ 2 / l ^ 2) = |CΓ| * (1 / (2 * π)) * f2 := by
    rw [hf2]; ring
  have e3 : 2 * (Cx * (1 + lq) * (l * sX)) = 2 * Cx * f3 := by rw [hf3]; ring
  have e4 : (B + K * y) / π * (T * L ^ 2) = (B + K * y) * (1 / π) * (T * L ^ 2) := by ring
  rw [e1, e2, e3, e4]
  have hTL : 0 ≤ T * L ^ 2 := by positivity
  have b2 : |CΓ| * (1 / (2 * π)) * f2 ≤ |CΓ| * 1 * f2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left one_div_two_pi_le_one (abs_nonneg _)) hf20
  have hBK : 0 ≤ B + K * y := by positivity
  have h1 : (B + K * y) * (1 / π) ≤ (B + K * y) * 1 := mul_le_mul_of_nonneg_left one_div_pi_le_one hBK
  have h2 : B + K * y ≤ (B + K) * (1 + y) := by linarith only [mul_nonneg hB hy, hK]
  have b4 : (B + K * y) * (1 / π) * (T * L ^ 2) ≤ (B + K) * f4 := by
    rw [hf4]
    calc (B + K * y) * (1 / π) * (T * L ^ 2) ≤ (B + K) * (1 + y) * (T * L ^ 2) := by
          rw [mul_one] at h1; exact mul_le_mul_of_nonneg_right (h1.trans h2) hTL
      _ = (B + K) * ((1 + y) * T * L ^ 2) := by ring
  have hCΓ := abs_nonneg CΓ
  have hCx2 : 0 ≤ 2 * Cx := by linarith
  linarith only [b2, b4, mul_nonneg hCm hf20, mul_nonneg hCm hf30, mul_nonneg hCm hf40,
    mul_nonneg hCΓ hf10, mul_nonneg hCΓ hf30, mul_nonneg hCΓ hf40,
    mul_nonneg hCx2 hf10, mul_nonneg hCx2 hf20, mul_nonneg hCx2 hf40,
    mul_nonneg hB hf10, mul_nonneg hB hf20, mul_nonneg hB hf30,
    mul_nonneg hK hf10, mul_nonneg hK hf20, mul_nonneg hK hf30]

/-- The diagonal `∫Φ²|x|` term against the fifth majorant term. -/
theorem frob_diag_le {S I KS KI L logL Xq : ℝ} (hS0 : 0 ≤ S) (hS : S ≤ KS * L ^ 2) (hI0 : 0 ≤ I)
    (hI : I ≤ KI * (1 + logL)) (hKS : 0 ≤ KS) (hL : 1 ≤ L) (hlogL : 0 ≤ logL) (hXq : 0 ≤ Xq) :
    1 / (2 * π ^ 2) * (S * I) ≤ KS * KI * (L ^ 3 * (1 + logL) * (Xq + L)) := by
  have hKI : 0 ≤ KI := by
    by_contra h
    have : KI * (1 + logL) < 0 := mul_neg_of_neg_of_pos (not_le.mp h) (by linarith)
    linarith
  have h1 : 1 / (2 * π ^ 2) * (S * I) ≤ S * I := by
    have := mul_le_mul_of_nonneg_right one_div_two_pi_sq_le_one (mul_nonneg hS0 hI0)
    linarith only [this]
  have h2 : S * I ≤ (KS * L ^ 2) * (KI * (1 + logL)) := mul_le_mul hS hI hI0 (by positivity)
  have h3 : L ^ 2 ≤ L ^ 3 * (Xq + L) := by
    have : L ^ 2 * 1 ≤ L ^ 2 * (L * (Xq + L)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    nlinarith
  have h4 : (KS * L ^ 2) * (KI * (1 + logL)) ≤ KS * KI * (L ^ 3 * (1 + logL) * (Xq + L)) := by
    have := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ KS * KI * (1 + logL))
    nlinarith
  linarith

/-- The Montgomery–Vaughan off-diagonal term against the fifth majorant term. -/
theorem frob_mv_le {I2 LF S3 Cmv C1 KS L logL X q : ℝ} (hI0 : 0 ≤ I2) (hI : I2 ≤ 2 * π * L)
    (hLF0 : 0 ≤ LF) (hLF : LF ≤ L + 1) (hS0 : 0 ≤ S3) (hS : S3 ≤ |C1| * X * L + q * (KS * L ^ 2))
    (hCmv : 0 ≤ Cmv) (hKS : 0 ≤ KS) (hL : 1 ≤ L) (hlogL : 0 ≤ logL) (hX : 0 ≤ X) (hq : 0 < q) :
    1 / (2 * π ^ 2) * (I2 / q * (8 * Cmv + 2 + 2 * LF) * S3)
      ≤ (8 * Cmv + 6) * (|C1| + KS) * (L ^ 3 * (1 + logL) * (X / q + L)) := by
  have hpi : 0 < π := Real.pi_pos
  have hA0 : 0 ≤ 8 * Cmv + 2 + 2 * LF := by positivity
  have hA : 8 * Cmv + 2 + 2 * LF ≤ (8 * Cmv + 6) * L := by nlinarith
  have hS' : S3 / q ≤ |C1| * (X / q) * L + KS * L ^ 2 := by
    rw [div_le_iff₀ hq]
    have e : (|C1| * (X / q) * L + KS * L ^ 2) * q = |C1| * X * L + q * (KS * L ^ 2) := by
      field_simp
    rw [e]; exact hS
  have hS'' : |C1| * (X / q) * L + KS * L ^ 2 ≤ (|C1| + KS) * L * (X / q + L) := by
    have h1 : 0 ≤ X / q := by positivity
    linarith only [mul_nonneg (abs_nonneg C1) (sq_nonneg L),
      mul_nonneg (mul_nonneg hKS (by linarith : (0:ℝ) ≤ L)) h1]
  have e : 1 / (2 * π ^ 2) * (I2 / q * (8 * Cmv + 2 + 2 * LF) * S3)
      = (I2 / (2 * π)) * (1 / π) * (8 * Cmv + 2 + 2 * LF) * (S3 / q) := by
    field_simp
  rw [e]
  have hI' : I2 / (2 * π) ≤ L := (div_le_iff₀ (by positivity)).mpr (by rw [mul_comm]; exact hI)
  have hI0' : 0 ≤ I2 / (2 * π) := by positivity
  have hSq0 : 0 ≤ S3 / q := by positivity
  calc I2 / (2 * π) * (1 / π) * (8 * Cmv + 2 + 2 * LF) * (S3 / q)
      ≤ L * 1 * ((8 * Cmv + 6) * L) * ((|C1| + KS) * L * (X / q + L)) := by
        apply mul_le_mul _ (hS'.trans hS'') hSq0 (by positivity)
        apply mul_le_mul _ hA hA0 (by positivity)
        exact mul_le_mul hI' one_div_pi_le_one (by positivity) (by linarith)
    _ = (8 * Cmv + 6) * (|C1| + KS) * (L ^ 3 * 1 * (X / q + L)) := by ring
    _ ≤ (8 * Cmv + 6) * (|C1| + KS) * (L ^ 3 * (1 + logL) * (X / q + L)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- The end-effect bracket against the sixth majorant term. -/
theorem frob_ends_le {C₀ lq l ocm U KS S2 Xq q L : ℝ} (hC₀ : 1 ≤ C₀) (hlq : 0 ≤ lq) (hl : 0 ≤ l)
    (hocm : ocm ^ 2 ≤ (Xq + 1) * S2) (hU0 : 0 ≤ U) (hU : U ≤ 7 * q * l ^ 2 + 10 * ((Xq + 1) * S2))
    (hS2 : S2 ≤ KS * L ^ 2) (hKS : 0 ≤ KS) (hXq : 0 ≤ Xq) (hq : 0 ≤ q) :
    ((C₀ + lq) * l) ^ 2 + ((C₀ + lq) * l + ocm) ^ 2 + 1 / (2 * π ^ 2) * U
      ≤ (3 * C₀ ^ 2 + 7 + 12 * KS) * ((1 + lq) ^ 2 * l ^ 2 + q * l ^ 2 + (Xq + 1) * L ^ 2) := by
  have hB : (C₀ + lq) * l ≤ C₀ * (1 + lq) * l := by
    apply mul_le_mul_of_nonneg_right _ hl; nlinarith
  have hB0 : 0 ≤ (C₀ + lq) * l := by positivity
  have hB2 : ((C₀ + lq) * l) ^ 2 ≤ C₀ ^ 2 * ((1 + lq) ^ 2 * l ^ 2) := by
    have := pow_le_pow_left₀ hB0 hB 2
    nlinarith
  have hsq : ((C₀ + lq) * l + ocm) ^ 2 ≤ 2 * ((C₀ + lq) * l) ^ 2 + 2 * ocm ^ 2 := by
    nlinarith [sq_nonneg ((C₀ + lq) * l - ocm)]
  have hU' : 1 / (2 * π ^ 2) * U ≤ U := by
    have := mul_le_mul_of_nonneg_right one_div_two_pi_sq_le_one hU0
    linarith
  have hXS : (Xq + 1) * S2 ≤ KS * ((Xq + 1) * L ^ 2) := by
    have := mul_le_mul_of_nonneg_left hS2 (by positivity : (0:ℝ) ≤ Xq + 1)
    linarith
  have hg : 0 ≤ (1 + lq) ^ 2 * l ^ 2 := by positivity
  have hql : 0 ≤ q * l ^ 2 := by positivity
  have hXL : 0 ≤ (Xq + 1) * L ^ 2 := by positivity
  have hC0 : 0 ≤ C₀ ^ 2 := sq_nonneg _
  nlinarith

/-- **The family Frobenius sum over all characters, with an explicit majorant.** -/
theorem family_frob_all_le (cϱ lam : ℝ) (hlam : 0 < lam) :
    ∃ K T₀ : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q], 1 ≤ q → ∀ (p : Setting) (F : LocalFun), p.lam = lam →
      T₀ ≤ p.T → LocalHypsCoreW cϱ p F → p.L ≤ 2 * p.l →
      ∑ χ : DirichletCharacter ℂ q, trGt2Nu (muq 0 q + PXc (fun n => χ n) p.X) p F
        ≤ (q.totient : ℝ) * (p.T * p.L / (2 * π) * (ell1q q p.T ^ 2 + p.L ^ 2 / 3)
          + K * famMaj q p.T p.L p.l p.X) := by
  obtain ⟨Cm, Cx, B, K, Cmv, Ce, C₀, CΓ, T₀, hCm, hCx, hB, hK, hCmv, hCe, hC₀, h⟩ :=
    family_frob_le cϱ lam hlam
  obtain ⟨C2, hC2⟩ := Zeta23.Cheb.chebyshevMertens.cheb2a
  obtain ⟨C1, hC1⟩ := Zeta23.Cheb.chebyshevMertens.cheb1d
  obtain ⟨KS, hKS⟩ : ∃ x : ℝ, x = 1 / 2 + |C2| := ⟨_, rfl⟩
  obtain ⟨KI, hKI⟩ : ∃ x : ℝ, x = 8 + 8 * |Real.log (cϱ / 4)| := ⟨_, rfl⟩
  obtain ⟨K₁, hK₁⟩ : ∃ x : ℝ, x = Cm + |CΓ| + 2 * Cx + B + K := ⟨_, rfl⟩
  obtain ⟨K₃, hK₃⟩ : ∃ x : ℝ, x = (8 * Cmv + 6) * (|C1| + KS) := ⟨_, rfl⟩
  obtain ⟨K₄, hK₄⟩ : ∃ x : ℝ, x = Ce * (3 * C₀ ^ 2 + 7 + 12 * KS) := ⟨_, rfl⟩
  have hKS0 : 0 ≤ KS := by rw [hKS]; positivity
  have hKI0 : 0 ≤ KI := by rw [hKI]; positivity
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  have hK₃0 : 0 ≤ K₃ := by rw [hK₃]; positivity
  have hK₄0 : 0 ≤ K₄ := by rw [hK₄]; positivity
  refine ⟨K₁ + KS * KI + K₃ + K₄, max T₀ 1, by positivity, fun q _ hq p F hp hT hF hL2 => ?_⟩
  have H := h q hq p F hp ((le_max_left T₀ 1).trans hT) hF hL2
  -- basic facts
  have hL8 := hF.eight_le_L
  have hl1 : 1 ≤ p.l := hF.one_le_l
  have hL1 : 1 ≤ p.L := by linarith
  have hT0 : 0 ≤ p.T := by have := (le_max_right T₀ 1).trans hT; linarith
  have hX0 : 0 < p.X := Real.exp_pos _
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlogL : 0 ≤ Real.log p.L := Real.log_nonneg hL1
  have hlogl : 0 ≤ Real.log p.l := Real.log_nonneg hl1
  have hφ : (0 : ℝ) ≤ q.totient := Nat.cast_nonneg _
  have hXq : 0 ≤ p.X / q := by positivity
  -- the majorant
  obtain ⟨f1, hf1⟩ : ∃ x : ℝ, x = (1 + Real.log q) ^ 2 * Zeta23.l p.T ^ 2 * Real.log p.L := ⟨_, rfl⟩
  obtain ⟨f2, hf2⟩ : ∃ x : ℝ, x = p.T * p.L * ell1q q p.T ^ 2 / Zeta23.l p.T ^ 2 := ⟨_, rfl⟩
  obtain ⟨f3, hf3⟩ : ∃ x : ℝ, x = (1 + Real.log q) * Zeta23.l p.T * Real.sqrt p.X := ⟨_, rfl⟩
  obtain ⟨f4, hf4⟩ : ∃ x : ℝ, x = (1 + Real.log (Real.log q + 8) ^ 2) * p.T * p.L ^ 2 := ⟨_, rfl⟩
  obtain ⟨f5, hf5⟩ : ∃ x : ℝ, x = p.L ^ 3 * (1 + Real.log p.L) * (p.X / q + p.L) := ⟨_, rfl⟩
  obtain ⟨g6, hg6⟩ : ∃ x : ℝ, x = (1 + Real.log q) ^ 2 * p.l ^ 2 + q * p.l ^ 2
      + (p.X / q + 1) * p.L ^ 2 := ⟨_, rfl⟩
  obtain ⟨Λe, hΛedef⟩ : ∃ x : ℝ, x = p.L * p.l * Real.log p.l := ⟨_, rfl⟩
  have hfam : famMaj q p.T p.L p.l p.X = f1 + f2 + f3 + f4 + f5 + Λe * g6 := by
    rw [hf1, hf2, hf3, hf4, hf5, hg6, hΛedef]; unfold famMaj; ring
  have hf10 : 0 ≤ f1 := by rw [hf1]; positivity
  have hf20 : 0 ≤ f2 := by rw [hf2]; positivity
  have hf30 : 0 ≤ f3 := by rw [hf3]; positivity
  have hf40 : 0 ≤ f4 := by rw [hf4]; positivity
  have hf50 : 0 ≤ f5 := by rw [hf5]; positivity
  have hg60 : 0 ≤ g6 := by rw [hg6]; positivity
  have hΛe0 : 0 ≤ Λe := by rw [hΛedef]; positivity
  -- the four pieces
  have a1 := frob_arch_le (CΓ := CΓ) (ell := ell1q q p.T) (lq := Real.log q) (l := Zeta23.l p.T)
    (logL := Real.log p.L) (T := p.T) (L := p.L) (sX := Real.sqrt p.X)
    (y := Real.log (Real.log q + 8) ^ 2) hCm hCx hB hK hlq
    (lt_of_lt_of_le one_pos hl1 : (0:ℝ) < Zeta23.l p.T)
    hlogL hT0 (by linarith) (Real.sqrt_nonneg p.X) (sq_nonneg (Real.log (Real.log q + 8))) hf1 hf2 hf3 hf4
  have hS2 := sum_acoef_sq_le_of_cheb hC2 hF
  rw [← hKS] at hS2
  have hS20 : 0 ≤ ∑ n ∈ primeRange p.X, acoef n ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hI0 : 0 ≤ ∫ x, F.Phi x ^ 2 * |x| := MeasureTheory.integral_nonneg fun x => by positivity
  have hI : ∫ x, F.Phi x ^ 2 * |x| ≤ KI * (1 + Real.log p.L) := by
    refine (integral_Phi_sq_mul_abs_le' hF).trans ?_
    rw [hKI]
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    linarith only [le_abs_self (Real.log (cϱ / 4))]
  have a2 := frob_diag_le hS20 hS2 hI0 hI hKS0 hL1 hlogL hXq
  rw [← hf5] at a2
  have hI20 : 0 ≤ ∫ x, F.Phi x ^ 2 := MeasureTheory.integral_nonneg fun x => by positivity
  have hLF0 : 0 ≤ Real.log ((⌊p.X⌋₊ : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) ⌊p.X⌋₊])
  have hS3 := sum_acoef_sq_mul_le_of_cheb hC2 hC1 hF q
  rw [← hKS] at hS3
  have hS30 : 0 ≤ ∑ n ∈ primeRange p.X, acoef n ^ 2 * ((n : ℝ) + q) :=
    Finset.sum_nonneg fun n _ => by positivity
  have a3 := frob_mv_le hI20 (integral_Phi_sq_le_L hF) hLF0 (log_floor_X_add_one_le hF) hS30 hS3
    hCmv hKS0 hL1 hlogL hX0.le hq0
  rw [← hK₃, ← hf5] at a3
  have hU0 : 0 ≤ ∑ r ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
      (2 * (p.l + classMass q p.X r) ^ 2 + (p.l + classMass q p.X r + classMass q p.X r⁻¹) ^ 2) :=
    Finset.sum_nonneg fun r _ => by positivity
  have a4 := frob_ends_le hC₀ hlq (by linarith : (0:ℝ) ≤ p.l) (oneClassMass_sq_le hX0.le) hU0
    (sum_units_classMass_bracket_le hX0.le p.l) hS2 hKS0 hXq hq0.le
  rw [← hg6] at a4
  -- multiply through by `φ(q)` and the end-effect weight
  have a1' := mul_le_mul_of_nonneg_left a1 hφ
  rw [← hK₁] at a1'
  have a2' : (q.totient : ℝ) / (2 * π ^ 2) * ((∑ n ∈ primeRange p.X, acoef n ^ 2) * ∫ x, F.Phi x ^ 2 * |x|)
      ≤ (q.totient : ℝ) * (KS * KI * f5) := by
    have := mul_le_mul_of_nonneg_left a2 hφ
    calc _ = (q.totient : ℝ) * (1 / (2 * π ^ 2)
          * ((∑ n ∈ primeRange p.X, acoef n ^ 2) * ∫ x, F.Phi x ^ 2 * |x|)) := by ring
      _ ≤ _ := this
  have a3' : (q.totient : ℝ) / (2 * π ^ 2) * ((∫ x, F.Phi x ^ 2) / q
        * (8 * Cmv + 2 + 2 * Real.log ((⌊p.X⌋₊ : ℝ) + 1))
        * ∑ n ∈ primeRange p.X, acoef n ^ 2 * ((n : ℝ) + q))
      ≤ (q.totient : ℝ) * (K₃ * f5) := by
    have := mul_le_mul_of_nonneg_left a3 hφ
    calc _ = (q.totient : ℝ) * (1 / (2 * π ^ 2) * ((∫ x, F.Phi x ^ 2) / q
          * (8 * Cmv + 2 + 2 * Real.log ((⌊p.X⌋₊ : ℝ) + 1))
          * ∑ n ∈ primeRange p.X, acoef n ^ 2 * ((n : ℝ) + q))) := by ring
      _ ≤ _ := this
  have hΛw : 0 ≤ Ce * (p.L * p.l * Real.log p.l) * q.totient := by positivity
  have a4' := mul_le_mul_of_nonneg_left a4 hΛw
  have a4'' : Ce * (p.L * p.l * Real.log p.l) * q.totient * ((3 * C₀ ^ 2 + 7 + 12 * KS) * g6)
      = (q.totient : ℝ) * (K₄ * (Λe * g6)) := by rw [hK₄, hΛedef]; ring
  rw [a4''] at a4'
  have hrest : K₁ * (f1 + f2 + f3 + f4) + KS * KI * f5 + K₃ * f5 + K₄ * (Λe * g6)
      ≤ (K₁ + KS * KI + K₃ + K₄) * (f1 + f2 + f3 + f4 + f5 + Λe * g6) := by
    have hKSKI : 0 ≤ KS * KI := mul_nonneg hKS0 hKI0
    have hΛg : 0 ≤ Λe * g6 := mul_nonneg hΛe0 hg60
    have e : (K₁ + KS * KI + K₃ + K₄) * (f1 + f2 + f3 + f4 + f5 + Λe * g6)
        - (K₁ * (f1 + f2 + f3 + f4) + KS * KI * f5 + K₃ * f5 + K₄ * (Λe * g6))
        = K₁ * (f5 + Λe * g6) + KS * KI * (f1 + f2 + f3 + f4 + Λe * g6)
          + K₃ * (f1 + f2 + f3 + f4 + Λe * g6) + K₄ * (f1 + f2 + f3 + f4 + f5) := by ring
    have : 0 ≤ K₁ * (f5 + Λe * g6) + KS * KI * (f1 + f2 + f3 + f4 + Λe * g6)
          + K₃ * (f1 + f2 + f3 + f4 + Λe * g6) + K₄ * (f1 + f2 + f3 + f4 + f5) := by positivity
    linarith only [e, this]
  have hrest' := mul_le_mul_of_nonneg_left hrest hφ
  rw [hfam]
  have hmain : (q.totient : ℝ) * (p.T * p.L / (2 * π) * (ell1q q p.T ^ 2 + p.L ^ 2 / 3)
        + (K₁ + KS * KI + K₃ + K₄) * (f1 + f2 + f3 + f4 + f5 + Λe * g6))
      = (q.totient : ℝ) * (p.T * p.L / (2 * π) * (ell1q q p.T ^ 2 + p.L ^ 2 / 3))
        + (q.totient : ℝ) * ((K₁ + KS * KI + K₃ + K₄) * (f1 + f2 + f3 + f4 + f5 + Λe * g6)) := by ring
  rw [hmain]
  have e1 : (q.totient : ℝ) * (K₁ * (f1 + f2 + f3 + f4) + KS * KI * f5 + K₃ * f5 + K₄ * (Λe * g6))
      = (q.totient : ℝ) * (K₁ * (f1 + f2 + f3 + f4)) + (q.totient : ℝ) * (KS * KI * f5)
        + (q.totient : ℝ) * (K₃ * f5) + (q.totient : ℝ) * (K₄ * (Λe * g6)) := by ring
  linarith only [H, a1', a2', a3', a4', hrest', e1]

/-- **The Frobenius norms of the nontrivial characters, summed.**  Odd characters are compared with the
even archimedean factor at the cost `(1+η, 1+1/η)`; the trivial character adds a nonnegative term. -/
theorem family_frob_nontriv (cϱ lam : ℝ) (hlam : 0 < lam) :
    ∃ K M CP T₀ : ℝ, 0 ≤ K ∧ 0 ≤ M ∧ 0 ≤ CP ∧ ∀ (q : ℕ) [NeZero q], 1 ≤ q → ∀ (p : Setting)
      (F : LocalFun), p.lam = lam → T₀ ≤ p.T → LocalHypsCoreW cϱ p F → p.L ≤ 2 * p.l →
      ∀ η : ℝ, 0 < η →
      ∑ χ ∈ nontrivChars q, trGt2ChiA (parity χ) q (coeff χ) p F
        ≤ (1 + η) * ((q.totient : ℝ) * (p.T * p.L / (2 * π) * (ell1q q p.T ^ 2 + p.L ^ 2 / 3)
            + K * famMaj q p.T p.L p.l p.X))
          + (nontrivChars q).card * ((1 + 1 / η) * (M ^ 2 * (p.T * (2 * π * p.L))
            + CP * (p.L * p.l * Real.log p.l * (p.l + M) ^ 2))) := by
  obtain ⟨K, T₁, hK, hall⟩ := family_frob_all_le cϱ lam hlam
  obtain ⟨T₂, hodd⟩ := trGt2_odd_le
  obtain ⟨CP, T₃, M, hCP, hM, hpar⟩ := trGt2_parityShift_le cϱ lam
  refine ⟨K, M, CP, max (max T₁ T₂) (max T₃ 1), hK, hM, hCP,
    fun q _ hq p F hp hT hF hL2 η hη => ?_⟩
  have hT₁ : T₁ ≤ p.T := (le_max_left _ _).trans ((le_max_left _ _).trans hT)
  have hT₂ : T₂ ≤ p.T := (le_max_right _ _).trans ((le_max_left _ _).trans hT)
  have hT₃ : T₃ ≤ p.T := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hT0 : 0 ≤ p.T := by
    have := (le_max_right T₃ 1).trans ((le_max_right _ _).trans hT); linarith
  obtain ⟨PS, hPS⟩ : ∃ x : ℝ, x = trGt2Nu parityShift p F := ⟨_, rfl⟩
  have hPS0 : 0 ≤ PS := by rw [hPS]; exact trGt2Nu_nonneg _ _ _
  have hη1 : 0 ≤ 1 + 1 / η := by positivity
  -- one character at a time
  have hpt : ∀ χ ∈ nontrivChars q, trGt2ChiA (parity χ) q (coeff χ) p F
      ≤ (1 + η) * trGt2Nu (muq 0 q + PXc (fun n => χ n) p.X) p F + (1 + 1 / η) * PS := by
    intro χ _
    have e : trGt2ChiA 0 q (coeff χ) p F = trGt2Nu (muq 0 q + PXc (fun n => χ n) p.X) p F := rfl
    unfold parity
    split_ifs
    · rw [e]
      have h0 := trGt2Nu_nonneg (muq 0 q + PXc (fun n => χ n) p.X) p F
      nlinarith
    · have := hodd q hq (coeff χ) (fun n => DirichletCharacter.norm_le_one χ _) p F hT₂ hF hη
      rw [e, ← hPS] at this
      exact this
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  have hsub : ∑ χ ∈ nontrivChars q, trGt2Nu (muq 0 q + PXc (fun n => χ n) p.X) p F
      ≤ ∑ χ : DirichletCharacter ℂ q, trGt2Nu (muq 0 q + PXc (fun n => χ n) p.X) p F :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun χ _ _ => trGt2Nu_nonneg _ _ _
  have hA := hall q hq p F hp hT₁ hF hL2
  have hP := hpar p F hp hT₃ hF hL2
  rw [← hPS] at hP
  have hP' : PS ≤ M ^ 2 * (p.T * (2 * π * p.L)) + CP * (p.L * p.l * Real.log p.l * (p.l + M) ^ 2) := by
    have h1 : M ^ 2 * (p.T * ∫ x, F.Phi x ^ 2) ≤ M ^ 2 * (p.T * (2 * π * p.L)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (integral_Phi_sq_le_L hF) hT0)
        (sq_nonneg M)
    linarith only [hP, h1]
  have hc0 : (0 : ℝ) ≤ (nontrivChars q).card := Nat.cast_nonneg _
  have h1 := mul_le_mul_of_nonneg_left (hsub.trans hA) (by linarith : (0:ℝ) ≤ 1 + η)
  have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP' hη1) hc0
  have e2 : (nontrivChars q).card * ((1 + 1 / η) * PS)
      = ((nontrivChars q).card : ℝ) * (1 + 1 / η) * PS := by ring
  linarith only [hsum, h1, h2, e2]

end RHTower
