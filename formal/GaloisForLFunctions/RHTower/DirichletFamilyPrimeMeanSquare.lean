import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Zeta23.ThmE.Hypotheses
import Zeta23.PrimeSideB.PPKernel
import GaloisForLFunctions.RHTower.MVResidueClass

/-!
# The mean square of the prime polynomials over all Dirichlet characters modulo `q`

For a Dirichlet character `χ` modulo `q` let
`P_χ(τ) = −(1/π) Re ∑_{n ≤ X} Λ(n) χ(n) n^{−1/2−iτ}` (Alpöge–Furman's `PXc`), and let
`𝓜[u, v] = ∬_{[T,2T]²} Φ(τ − τ')² u(τ) v(τ') dτ dτ'` be their bilinear form.  With
`a_n = Λ(n)/√n`, `y_n = log n`, and the difference/sum kernels `A^∓(y, y')` of the two-thirds
argument, orthogonality of characters gives the exact identity

`∑_χ 𝓜[P_χ, P_χ] = φ(q)/(2π²) · ( ∑_{n ≡ m, (m,q)=1} a_n a_m A⁻(y_n, y_m)
                                 + ∑_{nm ≡ 1} a_n a_m A⁺(y_n, y_m) )`

(`sum_Mform_PXc_dirichlet`).  The single-character mean square has the full double sum over
`n, m ≤ X` in the `A⁻` term; the character average keeps only pairs in one residue class.
Combined with the Montgomery–Vaughan inequality on residue classes, the off-diagonal part
`n ≠ m` is bounded by `8 C W ∑_{n ≤ X} a_n² (n + q)/q` (`offDiag_residueClass_bound`), where
`W = ∫ Φ²`: a factor `q` smaller than the single-character bound.  This is what lets the family
mean square be evaluated for polynomial lengths `X` up to `q T^{1−ε}`.
-/

open Complex ComplexConjugate MeasureTheory Set

noncomputable section

namespace RHTower

open Zeta23 Zeta23.PrimeSide Zeta23.ThmE

/-! ## Orthogonality of Dirichlet characters -/

lemma conj_dirichletChar_of_isUnit {q : ℕ} (χ : DirichletCharacter ℂ q) {b : ZMod q}
    (hb : IsUnit b) : conj (χ b) = χ b⁻¹ := by
  have h1 : conj (χ b) = χ⁻¹ b := by rw [← Complex.star_def]; exact MulChar.star_apply' χ b
  have hu : χ b ≠ 0 := by
    intro h0
    have := congrArg (fun z => z * χ b⁻¹) h0
    simp only [zero_mul, ← map_mul, mul_comm b, ZMod.inv_mul_of_unit b hb, map_one] at this
    exact one_ne_zero this
  have h2 : χ⁻¹ b * χ b = 1 := by
    rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply hb]
  have h3 : χ b⁻¹ * χ b = 1 := by
    rw [← map_mul, ZMod.inv_mul_of_unit b hb, map_one]
  rw [h1]
  exact mul_right_cancel₀ hu (h2.trans h3.symm)

/-- `∑_χ χ(a) χ̄(b) = φ(q)` if `b` is a unit and `a = b`, and `0` otherwise. -/
theorem sum_dirichletChar_mul_conj {q : ℕ} [NeZero q] (a b : ZMod q) :
    ∑ χ : DirichletCharacter ℂ q, χ a * conj (χ b)
      = if IsUnit b ∧ a = b then (q.totient : ℂ) else 0 := by
  by_cases hb : IsUnit b
  · have e : ∀ χ : DirichletCharacter ℂ q, χ a * conj (χ b) = χ b⁻¹ * χ a := fun χ => by
      rw [conj_dirichletChar_of_isUnit χ hb, mul_comm]
    simp_rw [e]
    rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb a]
    simp only [hb, true_and, eq_comm]
  · simp [MulChar.map_nonunit _ hb, hb]

/-- `∑_χ χ(a) χ(b) = φ(q)` if `ab = 1`, and `0` otherwise. -/
theorem sum_dirichletChar_mul {q : ℕ} [NeZero q] (a b : ZMod q) :
    ∑ χ : DirichletCharacter ℂ q, χ a * χ b = if a * b = 1 then (q.totient : ℂ) else 0 := by
  simp_rw [← map_mul]
  exact DirichletCharacter.sum_characters_eq ℂ (a * b)

/-! ## The difference and sum kernels as integrals over the square -/

section Kernels

variable {Φ : ℝ → ℝ} {T : ℝ}

lemma setIntegral_Ix_cos_linear (hT : 0 ≤ T) {x : ℝ} (hx : |x| ≤ T) (θ c : ℝ) :
    ∫ τ' in Ix T x, Real.cos (θ * τ' + c) = Jker θ c (max (T - x) T) (min (2 * T - x) (2 * T)) := by
  unfold Ix
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (Ix_le hT hx)]
  exact intervalIntegral_cos_linear_eq_Jker θ c _ _

/-- `∬_{[T,2T]²} Φ(τ − τ')² cos(τ y − τ' y') = A⁻(y, y')`. -/
theorem integral_square_cos_sub (hT : 0 ≤ T) (hΦ : Continuous Φ) (y y' : ℝ) :
    ∫ p in Icc T (2 * T) ×ˢ Icc T (2 * T), Φ (p.1 - p.2) ^ 2 * Real.cos (p.1 * y - p.2 * y')
      = Aminus Φ T y y' := by
  rw [sqIntegral_shear hΦ (G := fun p : ℝ × ℝ => Real.cos (p.1 * y - p.2 * y')) (by fun_prop)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-T) T) ?zero]
  case zero =>
    intro x hx
    rw [Ix_eq_empty hT (not_mem_Icc_neg hx)]; simp
  unfold Aminus
  refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
  have hx' : |x| ≤ T := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  have e : ∀ τ' : ℝ, Real.cos ((x + τ') * y - τ' * y') = Real.cos ((y - y') * τ' + x * y) :=
    fun τ' => by ring_nf
  simp only [e, setIntegral_Ix_cos_linear hT hx']
  rfl

/-- `∬_{[T,2T]²} Φ(τ − τ')² cos(τ y + τ' y') = A⁺(y, y')`. -/
theorem integral_square_cos_add (hT : 0 ≤ T) (hΦ : Continuous Φ) (y y' : ℝ) :
    ∫ p in Icc T (2 * T) ×ˢ Icc T (2 * T), Φ (p.1 - p.2) ^ 2 * Real.cos (p.1 * y + p.2 * y')
      = Aplus Φ T y y' := by
  rw [sqIntegral_shear hΦ (G := fun p : ℝ × ℝ => Real.cos (p.1 * y + p.2 * y')) (by fun_prop)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-T) T) ?zero]
  case zero =>
    intro x hx
    rw [Ix_eq_empty hT (not_mem_Icc_neg hx)]; simp
  unfold Aplus
  refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
  have hx' : |x| ≤ T := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  have e : ∀ τ' : ℝ, Real.cos ((x + τ') * y + τ' * y') = Real.cos ((y + y') * τ' + x * y) :=
    fun τ' => by ring_nf
  simp only [e, setIntegral_Ix_cos_linear hT hx']
  rfl

end Kernels

/-! ## The prime polynomial of a character as a real part -/

/-- The phase `n^{−iτ} = e^{−iτ log n}`. -/
def phaseExp (τ : ℝ) (n : ℕ) : ℂ := Complex.exp ((-(τ * Real.log n) : ℝ) * I)

/-- `D_c(τ) = ∑_{n ≤ X} a_n c(n) n^{−iτ}`. -/
def primeDirPoly (c : ℕ → ℂ) (X τ : ℝ) : ℂ :=
  ∑ n ∈ primeRange X, ((acoef n : ℝ) : ℂ) * c n * phaseExp τ n

lemma natCast_cpow_neg_half_sub_I_mul {n : ℕ} (hn : 1 ≤ n) (τ : ℝ) :
    (n : ℂ) ^ (-(1 / 2 : ℂ) - I * τ)
      = (((Real.sqrt n)⁻¹ : ℝ) : ℂ) * Complex.exp ((-(τ * Real.log n) : ℝ) * I) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [show ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) by push_cast; rfl]
    exact (Complex.ofReal_log hn0.le).symm
  rw [Complex.cpow_def_of_ne_zero hnC, hlog]
  have harg : ((Real.log n : ℝ) : ℂ) * (-(1 / 2 : ℂ) - I * τ)
      = ((-(Real.log n / 2) : ℝ) : ℂ) + ((-(τ * Real.log n) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [harg, Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_exp]
  congr 1
  rw [Real.exp_neg]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0]
  congr 1
  ring

/-- `P_c(τ) = −(1/π) Re D_c(τ)`. -/
lemma PXc_eq_re_primeDirPoly (c : ℕ → ℂ) (X τ : ℝ) :
    PXc c X τ = -(1 / Real.pi) * (primeDirPoly c X τ).re := by
  unfold PXc primeDirPoly
  congr 2
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [natCast_cpow_neg_half_sub_I_mul (one_le_of_mem_primeRange hn)]
  unfold acoef phaseExp
  push_cast
  ring

/-! ## The pointwise character average -/

open Classical in
/-- The indicator of `n ≡ m (mod q)` with `(m, q) = 1`. -/
def sameUnitClass (q n m : ℕ) : ℝ := if IsUnit (m : ZMod q) ∧ (n : ZMod q) = m then 1 else 0

open Classical in
/-- The indicator of `nm ≡ 1 (mod q)`. -/
def inverseClass (q n m : ℕ) : ℝ := if (n : ZMod q) * m = 1 then 1 else 0

private lemma re_mul_re (z w : ℂ) : z.re * w.re = ((z * conj w).re + (z * w).re) / 2 := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring

/-- **Pointwise orthogonality.**  For all real `τ, τ'`,
`∑_χ P_χ(τ) P_χ(τ') = φ(q)/(2π²) ∑_{n,m ≤ X} a_n a_m ([n ≡ m] cos(τ y_n − τ' y_m)
+ [nm ≡ 1] cos(τ y_n + τ' y_m))`. -/
theorem sum_PXc_mul_PXc_dirichlet {q : ℕ} [NeZero q] (X τ τ' : ℝ) :
    ∑ χ : DirichletCharacter ℂ q,
        PXc (fun n => χ n) X τ * PXc (fun n => χ n) X τ'
      = (q.totient : ℝ) / (2 * Real.pi ^ 2) *
        ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, acoef n * acoef m *
          (sameUnitClass q n m * Real.cos (τ * Real.log n - τ' * Real.log m)
            + inverseClass q n m * Real.cos (τ * Real.log n + τ' * Real.log m)) := by
  -- the two complex character sums
  have hconj : ∑ χ : DirichletCharacter ℂ q,
      primeDirPoly (fun n => χ n) X τ * conj (primeDirPoly (fun n => χ n) X τ')
      = ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, ((acoef n * acoef m : ℝ) : ℂ)
          * (phaseExp τ n * conj (phaseExp τ' m)) * (sameUnitClass q n m * q.totient : ℝ) := by
    unfold primeDirPoly
    simp_rw [map_sum, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    have e : ∀ χ : DirichletCharacter ℂ q,
        ((acoef n : ℝ) : ℂ) * χ n * phaseExp τ n * conj (((acoef m : ℝ) : ℂ) * χ m * phaseExp τ' m)
          = ((acoef n * acoef m : ℝ) : ℂ) * (phaseExp τ n * conj (phaseExp τ' m)) * (χ n * conj (χ m)) := by
      intro χ
      simp only [map_mul, Complex.conj_ofReal]
      push_cast; ring
    rw [Finset.sum_congr rfl fun χ _ => e χ, ← Finset.mul_sum, sum_dirichletChar_mul_conj]
    unfold sameUnitClass
    split_ifs <;> push_cast <;> ring
  have hmul : ∑ χ : DirichletCharacter ℂ q,
      primeDirPoly (fun n => χ n) X τ * primeDirPoly (fun n => χ n) X τ'
      = ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, ((acoef n * acoef m : ℝ) : ℂ)
          * (phaseExp τ n * phaseExp τ' m) * (inverseClass q n m * q.totient : ℝ) := by
    unfold primeDirPoly
    simp_rw [Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    have e : ∀ χ : DirichletCharacter ℂ q,
        ((acoef n : ℝ) : ℂ) * χ n * phaseExp τ n * (((acoef m : ℝ) : ℂ) * χ m * phaseExp τ' m)
          = ((acoef n * acoef m : ℝ) : ℂ) * (phaseExp τ n * phaseExp τ' m) * (χ n * χ m) := by
      intro χ; push_cast; ring
    rw [Finset.sum_congr rfl fun χ _ => e χ, ← Finset.mul_sum, sum_dirichletChar_mul]
    unfold inverseClass
    push_cast
    split_ifs <;> push_cast <;> ring
  -- real parts of the phase factors
  have hEc : ∀ n m : ℕ, (phaseExp τ n * conj (phaseExp τ' m)).re = Real.cos (τ * Real.log n - τ' * Real.log m) := by
    intro n m
    have hc : conj (((-(τ' * Real.log m) : ℝ) : ℂ) * I) = ((τ' * Real.log m : ℝ) : ℂ) * I := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
    unfold phaseExp
    rw [← Complex.exp_conj, hc, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add,
      Complex.exp_ofReal_mul_I_re, ← Real.cos_neg]
    congr 1; ring
  have hEm : ∀ n m : ℕ, (phaseExp τ n * phaseExp τ' m).re = Real.cos (τ * Real.log n + τ' * Real.log m) := by
    intro n m
    unfold phaseExp
    rw [← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, Complex.exp_ofReal_mul_I_re,
      ← Real.cos_neg]
    congr 1; ring
  -- assemble
  have hpt : ∀ χ : DirichletCharacter ℂ q,
      PXc (fun n => χ n) X τ * PXc (fun n => χ n) X τ'
        = 1 / (2 * Real.pi ^ 2) *
          ((primeDirPoly (fun n => χ n) X τ * conj (primeDirPoly (fun n => χ n) X τ')).re
            + (primeDirPoly (fun n => χ n) X τ * primeDirPoly (fun n => χ n) X τ').re) := by
    intro χ
    rw [PXc_eq_re_primeDirPoly, PXc_eq_re_primeDirPoly]
    have := re_mul_re (primeDirPoly (fun n => χ n) X τ) (primeDirPoly (fun n => χ n) X τ')
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    linear_combination (2 : ℝ) * this
  simp_rw [hpt]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Complex.re_sum, ← Complex.re_sum, hconj, hmul,
    Complex.re_sum, Complex.re_sum]
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.re_sum, Complex.re_sum, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.re_mul_ofReal, Complex.re_mul_ofReal, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
    hEc, hEm]
  ring

lemma continuous_PXc (c : ℕ → ℂ) (X : ℝ) : Continuous (PXc c X) := by
  have e : PXc c X = fun τ => -(1 / Real.pi) * (primeDirPoly c X τ).re :=
    funext (PXc_eq_re_primeDirPoly c X)
  rw [e]
  unfold primeDirPoly phaseExp
  fun_prop

/-! ## The character average of the mean square -/

section FamilyMeanSquare

variable {Φ : ℝ → ℝ} {T : ℝ}

lemma integrableOn_square_of_continuous (hΦ : Continuous Φ) {G : ℝ × ℝ → ℝ} (hG : Continuous G) :
    Integrable (fun p : ℝ × ℝ => Φ (p.1 - p.2) ^ 2 * G p)
      (volume.restrict (Icc T (2 * T) ×ˢ Icc T (2 * T))) :=
  ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    (Continuous.continuousOn (by fun_prop))

/-- The `(n, m)` term of the averaged integrand. -/
def familyPairIntegrand (Φ : ℝ → ℝ) (q n m : ℕ) (p : ℝ × ℝ) : ℝ :=
  acoef n * acoef m *
    (sameUnitClass q n m * (Φ (p.1 - p.2) ^ 2 * Real.cos (p.1 * Real.log n - p.2 * Real.log m))
      + inverseClass q n m * (Φ (p.1 - p.2) ^ 2 * Real.cos (p.1 * Real.log n + p.2 * Real.log m)))

lemma integrable_familyPairIntegrand (hΦ : Continuous Φ) (q n m : ℕ) :
    Integrable (familyPairIntegrand Φ q n m) (volume.restrict (Icc T (2 * T) ×ˢ Icc T (2 * T))) := by
  have h1 := integrableOn_square_of_continuous (T := T) hΦ
    (G := fun p : ℝ × ℝ => Real.cos (p.1 * Real.log n - p.2 * Real.log m)) (by fun_prop)
  have h2 := integrableOn_square_of_continuous (T := T) hΦ
    (G := fun p : ℝ × ℝ => Real.cos (p.1 * Real.log n + p.2 * Real.log m)) (by fun_prop)
  exact ((h1.const_mul _).add (h2.const_mul _)).const_mul _

lemma integral_familyPairIntegrand (hT : 0 ≤ T) (hΦ : Continuous Φ) (q n m : ℕ) :
    ∫ p in Icc T (2 * T) ×ˢ Icc T (2 * T), familyPairIntegrand Φ q n m p
      = acoef n * acoef m * (sameUnitClass q n m * Aminus Φ T (Real.log n) (Real.log m)
          + inverseClass q n m * Aplus Φ T (Real.log n) (Real.log m)) := by
  have h1 := integrableOn_square_of_continuous (T := T) hΦ
    (G := fun p : ℝ × ℝ => Real.cos (p.1 * Real.log n - p.2 * Real.log m)) (by fun_prop)
  have h2 := integrableOn_square_of_continuous (T := T) hΦ
    (G := fun p : ℝ × ℝ => Real.cos (p.1 * Real.log n + p.2 * Real.log m)) (by fun_prop)
  unfold familyPairIntegrand
  rw [integral_const_mul, integral_add (h1.const_mul _) (h2.const_mul _), integral_const_mul,
    integral_const_mul, integral_square_cos_sub hT hΦ, integral_square_cos_add hT hΦ]

lemma sum_square_integrand_dirichlet {q : ℕ} [NeZero q] (X : ℝ) (p : ℝ × ℝ) :
    ∑ χ : DirichletCharacter ℂ q,
        Φ (p.1 - p.2) ^ 2 * PXc (fun n => χ n) X p.1 * PXc (fun n => χ n) X p.2
      = (q.totient : ℝ) / (2 * Real.pi ^ 2) *
        ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, familyPairIntegrand Φ q n m p := by
  simp_rw [mul_assoc (Φ (p.1 - p.2) ^ 2)]
  rw [← Finset.mul_sum, sum_PXc_mul_PXc_dirichlet, mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold familyPairIntegrand
  ring

/-- **Mean square over the characters modulo `q`.**  For `T ≥ 0` and continuous `Φ`,
`∑_χ 𝓜[P_χ, P_χ] = φ(q)/(2π²) ∑_{n,m ≤ X} a_n a_m ([n ≡ m, (m,q)=1] A⁻(y_n, y_m)
+ [nm ≡ 1] A⁺(y_n, y_m))`. -/
theorem sum_Mform_PXc_dirichlet {q : ℕ} [NeZero q] (hT : 0 ≤ T) (hΦ : Continuous Φ) (X : ℝ) :
    ∑ χ : DirichletCharacter ℂ q,
        Mform Φ T (PXc (fun n => χ n) X) (PXc (fun n => χ n) X)
      = (q.totient : ℝ) / (2 * Real.pi ^ 2) *
        ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, acoef n * acoef m *
          (sameUnitClass q n m * Aminus Φ T (Real.log n) (Real.log m)
            + inverseClass q n m * Aplus Φ T (Real.log n) (Real.log m)) := by
  have hχint : ∀ χ : DirichletCharacter ℂ q, Integrable
      (fun p : ℝ × ℝ => Φ (p.1 - p.2) ^ 2 * PXc (fun n => χ n) X p.1 * PXc (fun n => χ n) X p.2)
      (volume.restrict (Icc T (2 * T) ×ˢ Icc T (2 * T))) := fun χ =>
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      (Continuous.continuousOn (by
        have := continuous_PXc (fun n => χ n) X
        fun_prop))
  unfold Mform
  rw [← integral_finsetSum _ fun χ _ => hχint χ]
  simp_rw [sum_square_integrand_dirichlet]
  rw [integral_const_mul, integral_finsetSum _ fun n _ =>
    integrable_finsetSum _ fun m _ => integrable_familyPairIntegrand hΦ q n m]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_finsetSum _ fun m _ => integrable_familyPairIntegrand hΦ q n m]
  exact Finset.sum_congr rfl fun m _ => integral_familyPairIntegrand hT hΦ q n m

end FamilyMeanSquare

/-! ## The off-diagonal on one residue class -/

section OffDiagonal

variable {Φ : ℝ → ℝ} {T C : ℝ}

/-- With `u = a`, `v = a·M` (or the reverse), `|M| ≤ W` and weights `w ≥ 0`,
`C (∑ u² w)^{1/2} (∑ v² w)^{1/2} ≤ C W ∑ a² w`. -/
lemma mv_size_le_weighted (hC : 0 ≤ C) (S : Finset ℕ) {w M : ℕ → ℝ} {W : ℝ} (hW : 0 ≤ W)
    (hw : ∀ n ∈ S, 0 ≤ w n) (hM : ∀ n ∈ S, |M n| ≤ W) :
    C * Real.sqrt (∑ n ∈ S, acoef n ^ 2 * w n)
        * Real.sqrt (∑ n ∈ S, (acoef n * M n) ^ 2 * w n)
      ≤ C * W * ∑ n ∈ S, acoef n ^ 2 * w n ∧
    C * Real.sqrt (∑ n ∈ S, (acoef n * M n) ^ 2 * w n)
        * Real.sqrt (∑ n ∈ S, acoef n ^ 2 * w n)
      ≤ C * W * ∑ n ∈ S, acoef n ^ 2 * w n := by
  set A := ∑ n ∈ S, acoef n ^ 2 * w n with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun n hn => mul_nonneg (sq_nonneg _) (hw n hn)
  have h2 : ∑ n ∈ S, (acoef n * M n) ^ 2 * w n ≤ W ^ 2 * A := by
    rw [hA, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hM2 : M n ^ 2 ≤ W ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hM n hn) 2
    have := mul_le_mul_of_nonneg_right hM2 (mul_nonneg (sq_nonneg (acoef n)) (hw n hn))
    nlinarith
  have hs2 : Real.sqrt (∑ n ∈ S, (acoef n * M n) ^ 2 * w n) ≤ W * Real.sqrt A := by
    calc Real.sqrt (∑ n ∈ S, (acoef n * M n) ^ 2 * w n) ≤ Real.sqrt (W ^ 2 * A) :=
          Real.sqrt_le_sqrt h2
      _ = W * Real.sqrt A := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hW]
  have hsq : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA0
  have hsA : 0 ≤ Real.sqrt A := Real.sqrt_nonneg _
  constructor
  · calc C * Real.sqrt A * Real.sqrt (∑ n ∈ S, (acoef n * M n) ^ 2 * w n)
        ≤ C * Real.sqrt A * (W * Real.sqrt A) :=
          mul_le_mul_of_nonneg_left hs2 (mul_nonneg hC hsA)
      _ = C * W * A := by
          rw [show C * Real.sqrt A * (W * Real.sqrt A) = C * W * (Real.sqrt A * Real.sqrt A) by ring,
            hsq]
  · calc C * Real.sqrt (∑ n ∈ S, (acoef n * M n) ^ 2 * w n) * Real.sqrt A
        ≤ C * (W * Real.sqrt A) * Real.sqrt A :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs2 hC) hsA
      _ = C * W * A := by
          rw [show C * (W * Real.sqrt A) * Real.sqrt A = C * W * (Real.sqrt A * Real.sqrt A) by ring,
            hsq]

/-- **The difference-frequency off-diagonal on a well-spaced set.**  Let `S` be a finite set of
positive integers on which the real Montgomery–Vaughan inequality holds with constant `C` and
weights `w ≥ 0`.  Then for `T ≥ 0` and continuous `Φ` with `Φ²` integrable,
`|∑_{n ≠ m ∈ S} a_n a_m A⁻(y_n, y_m)| ≤ 8 C (∫Φ²) ∑_{n ∈ S} a_n² w_n`. -/
theorem offDiag_Aminus_le_of_mvReal (hC : 0 ≤ C) (hT : 0 ≤ T) (hΦ : Continuous Φ)
    (hΦ2 : Integrable fun x => Φ x ^ 2) (S : Finset ℕ) (hpos : ∀ n ∈ S, 1 ≤ n) (w : ℕ → ℝ)
    (hw : ∀ n ∈ S, 0 ≤ w n)
    (hmv : ∀ (c : ℝ) (u v : ℕ → ℝ),
      |∑ n ∈ S, ∑ m ∈ S, (if n = m then (0:ℝ) else
          u n * v m * Real.cos (c * (Real.log n - Real.log m)) / (Real.log n - Real.log m))|
        ≤ C * Real.sqrt (∑ n ∈ S, u n ^ 2 * w n) * Real.sqrt (∑ n ∈ S, v n ^ 2 * w n) ∧
      |∑ n ∈ S, ∑ m ∈ S, (if n = m then (0:ℝ) else
          u n * v m * Real.sin (c * (Real.log n - Real.log m)) / (Real.log n - Real.log m))|
        ≤ C * Real.sqrt (∑ n ∈ S, u n ^ 2 * w n) * Real.sqrt (∑ n ∈ S, v n ^ 2 * w n)) :
    |∑ n ∈ S, ∑ m ∈ S,
        (if n = m then (0:ℝ) else acoef n * acoef m * Aminus Φ T (Real.log n) (Real.log m))|
      ≤ 8 * C * (∫ x, Φ x ^ 2) * ∑ n ∈ S, acoef n ^ 2 * w n := by
  set W : ℝ := ∫ x, Φ x ^ 2 with hW
  have hW0 : 0 ≤ W := MeasureTheory.integral_nonneg fun x => sq_nonneg _
  set A : ℝ := ∑ n ∈ S, acoef n ^ 2 * w n with hA
  set S1 : ℝ := ∑ n ∈ S, ∑ m ∈ S, (if n = m then (0:ℝ) else
    (fun k => acoef k * Cm Φ T (Real.log k)) n * acoef m
      * Real.sin ((2 * T) * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) with hS1
  set S2 : ℝ := ∑ n ∈ S, ∑ m ∈ S, (if n = m then (0:ℝ) else
    (fun k => acoef k * Sm Φ T (Real.log k)) n * acoef m
      * Real.cos ((2 * T) * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) with hS2
  set S3 : ℝ := ∑ n ∈ S, ∑ m ∈ S, (if n = m then (0:ℝ) else
    acoef n * (fun k => acoef k * Cm Φ T (Real.log k)) m
      * Real.sin (T * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) with hS3
  set S4 : ℝ := ∑ n ∈ S, ∑ m ∈ S, (if n = m then (0:ℝ) else
    acoef n * (fun k => acoef k * Sm Φ T (Real.log k)) m
      * Real.cos (T * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) with hS4
  set S5 : ℝ := ∑ n ∈ S, ∑ m ∈ S, (if n = m then (0:ℝ) else
    acoef n * (fun k => acoef k * Cp Φ T (Real.log k)) m
      * Real.sin ((2 * T) * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) with hS5
  set S6 : ℝ := ∑ n ∈ S, ∑ m ∈ S, (if n = m then (0:ℝ) else
    acoef n * (fun k => acoef k * Sp Φ T (Real.log k)) m
      * Real.cos ((2 * T) * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) with hS6
  set S7 : ℝ := ∑ n ∈ S, ∑ m ∈ S, (if n = m then (0:ℝ) else
    (fun k => acoef k * Cp Φ T (Real.log k)) n * acoef m
      * Real.sin (T * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) with hS7
  set S8 : ℝ := ∑ n ∈ S, ∑ m ∈ S, (if n = m then (0:ℝ) else
    (fun k => acoef k * Sp Φ T (Real.log k)) n * acoef m
      * Real.cos (T * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) with hS8
  have hsplit : ∑ n ∈ S, ∑ m ∈ S,
      (if n = m then (0:ℝ) else acoef n * acoef m * Aminus Φ T (Real.log n) (Real.log m))
      = S1 + S2 - S3 - S4 + S5 + S6 - S7 - S8 := by
    rw [hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => ?_
    by_cases hnm : n = m
    · simp [hnm]
    · simp only [if_neg hnm]
      have hθ : Real.log n - Real.log m ≠ 0 := by
        have hn1 := hpos n hn
        have hm1 := hpos m hm
        have hinj : Real.log n ≠ Real.log m := by
          rcases lt_or_gt_of_ne hnm with hlt | hgt
          · exact ne_of_lt (Real.log_lt_log (by exact_mod_cast hn1) (by exact_mod_cast hlt))
          · exact ne_of_gt (Real.log_lt_log (by exact_mod_cast hm1) (by exact_mod_cast hgt))
        exact sub_ne_zero.mpr hinj
      have hAm : Aminus Φ T (Real.log n) (Real.log m)
          = ((Real.sin ((Real.log n - Real.log m) * (2 * T)) * Cm Φ T (Real.log n)
              + Real.cos ((Real.log n - Real.log m) * (2 * T)) * Sm Φ T (Real.log n)
              - (Real.sin ((Real.log n - Real.log m) * T) * Cm Φ T (Real.log m)
                + Real.cos ((Real.log n - Real.log m) * T) * Sm Φ T (Real.log m)))
            + (Real.sin ((Real.log n - Real.log m) * (2 * T)) * Cp Φ T (Real.log m)
              + Real.cos ((Real.log n - Real.log m) * (2 * T)) * Sp Φ T (Real.log m)
              - (Real.sin ((Real.log n - Real.log m) * T) * Cp Φ T (Real.log n)
                + Real.cos ((Real.log n - Real.log m) * T) * Sp Φ T (Real.log n))))
            / (Real.log n - Real.log m) := by
        rw [eq_div_iff hθ, mul_comm]
        exact sub_mul_Aminus_eq (Φ := Φ) hT hΦ hθ
      rw [hAm, mul_comm ((2 : ℝ) * T) (Real.log n - Real.log m),
        mul_comm T (Real.log n - Real.log m)]
      field_simp
      ring
  have hw_Cm : ∀ n ∈ S, |Cm Φ T (Real.log n)| ≤ W := fun n _ => abs_Cm_le hT hΦ hΦ2 _
  have hw_Sm : ∀ n ∈ S, |Sm Φ T (Real.log n)| ≤ W := fun n _ => abs_Sm_le hT hΦ hΦ2 _
  have hw_Cp : ∀ n ∈ S, |Cp Φ T (Real.log n)| ≤ W := fun n _ => abs_Cp_le hT hΦ hΦ2 _
  have hw_Sp : ∀ n ∈ S, |Sp Φ T (Real.log n)| ≤ W := fun n _ => abs_Sp_le hT hΦ hΦ2 _
  have hb1 : |S1| ≤ C * W * A :=
    ((hmv (2 * T) (fun k => acoef k * Cm Φ T (Real.log k)) acoef).2).trans
      (mv_size_le_weighted hC S hW0 hw hw_Cm).2
  have hb2 : |S2| ≤ C * W * A :=
    ((hmv (2 * T) (fun k => acoef k * Sm Φ T (Real.log k)) acoef).1).trans
      (mv_size_le_weighted hC S hW0 hw hw_Sm).2
  have hb3 : |S3| ≤ C * W * A :=
    ((hmv T acoef (fun k => acoef k * Cm Φ T (Real.log k))).2).trans
      (mv_size_le_weighted hC S hW0 hw hw_Cm).1
  have hb4 : |S4| ≤ C * W * A :=
    ((hmv T acoef (fun k => acoef k * Sm Φ T (Real.log k))).1).trans
      (mv_size_le_weighted hC S hW0 hw hw_Sm).1
  have hb5 : |S5| ≤ C * W * A :=
    ((hmv (2 * T) acoef (fun k => acoef k * Cp Φ T (Real.log k))).2).trans
      (mv_size_le_weighted hC S hW0 hw hw_Cp).1
  have hb6 : |S6| ≤ C * W * A :=
    ((hmv (2 * T) acoef (fun k => acoef k * Sp Φ T (Real.log k))).1).trans
      (mv_size_le_weighted hC S hW0 hw hw_Sp).1
  have hb7 : |S7| ≤ C * W * A :=
    ((hmv T (fun k => acoef k * Cp Φ T (Real.log k)) acoef).2).trans
      (mv_size_le_weighted hC S hW0 hw hw_Cp).2
  have hb8 : |S8| ≤ C * W * A :=
    ((hmv T (fun k => acoef k * Sp Φ T (Real.log k)) acoef).1).trans
      (mv_size_le_weighted hC S hW0 hw hw_Sp).2
  rw [hsplit]
  have t1 := abs_add_le S1 S2
  have t2 := abs_sub (S1 + S2) S3
  have t3 := abs_sub (S1 + S2 - S3) S4
  have t4 := abs_add_le (S1 + S2 - S3 - S4) S5
  have t5 := abs_add_le (S1 + S2 - S3 - S4 + S5) S6
  have t6 := abs_sub (S1 + S2 - S3 - S4 + S5 + S6) S7
  have t7 := abs_sub (S1 + S2 - S3 - S4 + S5 + S6 - S7) S8
  linarith

end OffDiagonal

/-! ## Splitting the character-averaged double sum into residue classes -/

section ResidueClasses

open Classical in
/-- A double sum weighted by `[n ≡ m, (m, q) = 1]` is the sum over reduced residue classes `r` of
the full double sums over the class `r`. -/
theorem sum_sameUnitClass_eq_sum_classes {q : ℕ} [NeZero q] (R : Finset ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ n ∈ R, ∑ m ∈ R, sameUnitClass q n m * g n m
      = ∑ r ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
          ∑ n ∈ R.filter (fun n : ℕ => (n : ZMod q) = r),
            ∑ m ∈ R.filter (fun m : ℕ => (m : ZMod q) = r), g n m := by
  have h1 : ∀ r : ZMod q, ∑ n ∈ R.filter (fun n : ℕ => (n : ZMod q) = r),
      ∑ m ∈ R.filter (fun m : ℕ => (m : ZMod q) = r), g n m
        = ∑ n ∈ R, if (n : ZMod q) = r then
            ∑ m ∈ R, (if (m : ZMod q) = r then g n m else 0) else 0 := by
    intro r
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_filter]
  conv_rhs => rw [Finset.sum_congr rfl fun r _ => h1 r, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_ite_eq]
  unfold sameUnitClass
  split_ifs with hU
  · refine Finset.sum_congr rfl fun m _ => ?_
    have hU' : IsUnit (n : ZMod q) := (Finset.mem_filter.mp hU).2
    by_cases hnm : (n : ZMod q) = m
    · rw [if_pos ⟨hnm ▸ hU', hnm⟩, if_pos hnm.symm, one_mul]
    · rw [if_neg (fun h => hnm h.2), if_neg (fun h => hnm h.symm), zero_mul]
  · refine Finset.sum_eq_zero fun m _ => ?_
    rw [if_neg, zero_mul]
    rintro ⟨hm, hnm⟩
    exact hU (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnm ▸ hm⟩)

/-- **The character-averaged off-diagonal.**  With the Montgomery–Vaughan constant `C`, for
`T ≥ 0`, continuous `Φ` with `Φ²` integrable and any `X`,
`|∑_{n ≠ m ≤ X} [n ≡ m, (m,q)=1] a_n a_m A⁻(y_n, y_m)| ≤ 8 C (∫ Φ²) ∑_{n ≤ X} a_n² (n + q)/q`. -/
theorem offDiag_residueClass_bound {C : ℝ} (hMV : Zeta23.MVHilbert C) (hC : 0 ≤ C) {q : ℕ}
    [NeZero q] {Φ : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hΦ : Continuous Φ)
    (hΦ2 : Integrable fun x => Φ x ^ 2) (X : ℝ) :
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X, sameUnitClass q n m *
        (if n = m then (0:ℝ) else acoef n * acoef m * Aminus Φ T (Real.log n) (Real.log m))|
      ≤ 8 * C * (∫ x, Φ x ^ 2) * ∑ n ∈ primeRange X, acoef n ^ 2 * ((n + q) / q) := by
  classical
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  set W : ℝ := ∫ x, Φ x ^ 2 with hW
  have hW0 : 0 ≤ W := MeasureTheory.integral_nonneg fun x => sq_nonneg _
  set w : ℕ → ℝ := fun n => ((n : ℝ) + q) / q with hw
  have hw0 : ∀ n, 0 ≤ w n := fun n => by simp only [hw]; positivity
  rw [sum_sameUnitClass_eq_sum_classes]
  -- each residue class is well spaced
  have hclass : ∀ r : ZMod q,
      |∑ n ∈ (primeRange X).filter (fun n : ℕ => (n : ZMod q) = r),
          ∑ m ∈ (primeRange X).filter (fun m : ℕ => (m : ZMod q) = r),
          (if n = m then (0:ℝ) else acoef n * acoef m * Aminus Φ T (Real.log n) (Real.log m))|
        ≤ 8 * C * W * ∑ n ∈ (primeRange X).filter (fun n : ℕ => (n : ZMod q) = r),
            acoef n ^ 2 * w n := by
    intro r
    have hpos : ∀ n ∈ (primeRange X).filter (fun n : ℕ => (n : ZMod q) = r), 1 ≤ n :=
      fun n hn => one_le_of_mem_primeRange (Finset.mem_filter.mp hn).1
    have hcong : ∀ n ∈ (primeRange X).filter (fun n : ℕ => (n : ZMod q) = r),
        ∀ m ∈ (primeRange X).filter (fun m : ℕ => (m : ZMod q) = r), n ≡ m [MOD q] := by
      intro n hn m hm
      exact (ZMod.natCast_eq_natCast_iff n m q).mp
        ((Finset.mem_filter.mp hn).2.trans (Finset.mem_filter.mp hm).2.symm)
    exact offDiag_Aminus_le_of_mvReal hC hT hΦ hΦ2 _ hpos w (fun n _ => hw0 n)
      (fun c u v => mv_real_residueClass hMV hq _ hpos hcong c u v)
  calc |∑ r ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
          ∑ n ∈ (primeRange X).filter (fun n : ℕ => (n : ZMod q) = r),
            ∑ m ∈ (primeRange X).filter (fun m : ℕ => (m : ZMod q) = r),
              (if n = m then (0:ℝ) else acoef n * acoef m * Aminus Φ T (Real.log n) (Real.log m))|
      ≤ ∑ r ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
          8 * C * W * ∑ n ∈ (primeRange X).filter (fun n : ℕ => (n : ZMod q) = r),
            acoef n ^ 2 * w n :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => hclass r)
    _ = 8 * C * W * ∑ n ∈ (primeRange X).filter
          (fun n : ℕ => (n : ZMod q) ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit),
            acoef n ^ 2 * w n := by
        rw [← Finset.mul_sum, Finset.sum_fiberwise_eq_sum_filter]
    _ ≤ 8 * C * W * ∑ n ∈ primeRange X, acoef n ^ 2 * w n := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun n _ _ => mul_nonneg (sq_nonneg _) (hw0 n)

end ResidueClasses

/-! ## The sum-frequency term -/

section SumFrequency

open Classical in
/-- A double sum weighted by `[nm ≡ 1 (mod q)]` pairs the class `r` with the class `r⁻¹`. -/
theorem sum_inverseClass_eq_sum_classes {q : ℕ} [NeZero q] (R : Finset ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ n ∈ R, ∑ m ∈ R, inverseClass q n m * g n m
      = ∑ r ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
          ∑ n ∈ R.filter (fun n : ℕ => (n : ZMod q) = r),
            ∑ m ∈ R.filter (fun m : ℕ => (m : ZMod q) = r⁻¹), g n m := by
  have h1 : ∀ r : ZMod q, ∑ n ∈ R.filter (fun n : ℕ => (n : ZMod q) = r),
      ∑ m ∈ R.filter (fun m : ℕ => (m : ZMod q) = r⁻¹), g n m
        = ∑ n ∈ R, if (n : ZMod q) = r then
            ∑ m ∈ R, (if (m : ZMod q) = r⁻¹ then g n m else 0) else 0 := by
    intro r
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_filter]
  conv_rhs => rw [Finset.sum_congr rfl fun r _ => h1 r, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_ite_eq]
  unfold inverseClass
  split_ifs with hU
  · refine Finset.sum_congr rfl fun m _ => ?_
    have hU' : IsUnit (n : ZMod q) := (Finset.mem_filter.mp hU).2
    have hiff : (n : ZMod q) * m = 1 ↔ (m : ZMod q) = (n : ZMod q)⁻¹ := by
      constructor
      · intro h
        calc (m : ZMod q) = (n : ZMod q)⁻¹ * ((n : ZMod q) * m) := by
              rw [← mul_assoc, ZMod.inv_mul_of_unit _ hU', one_mul]
          _ = (n : ZMod q)⁻¹ := by rw [h, mul_one]
      · intro h; rw [h, ZMod.mul_inv_of_unit _ hU']
    by_cases hm : (m : ZMod q) = (n : ZMod q)⁻¹
    · rw [if_pos (hiff.mpr hm), if_pos hm, one_mul]
    · rw [if_neg (fun h => hm (hiff.mp h)), if_neg hm, zero_mul]
  · refine Finset.sum_eq_zero fun m _ => ?_
    rw [if_neg, zero_mul]
    intro h
    exact hU (Finset.mem_filter.mpr ⟨Finset.mem_univ _, IsUnit.of_mul_eq_one _ h⟩)

/-- **Harmonic count on a residue class.**  For `q > 0` and any class `r`,
`∑_{n ≤ X, n ≡ r} 1/(n + q) ≤ (1 + log(⌊X⌋ + 1))/q`. -/
theorem sum_inv_add_le_of_residueClass {q : ℕ} (hq : 0 < q) (X : ℝ) (r : ZMod q) :
    ∑ n ∈ (primeRange X).filter (fun n : ℕ => (n : ZMod q) = r), 1 / ((n : ℝ) + q)
      ≤ (1 + Real.log ((⌊X⌋₊ : ℝ) + 1)) / q := by
  set Rr := (primeRange X).filter (fun n : ℕ => (n : ZMod q) = r) with hRr
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  -- the block index `k(n) = (n − 1)/q` is injective on a residue class
  have hinj : Set.InjOn (fun n : ℕ => (n - 1) / q) Rr := by
    intro n hn m hm hnm
    have hn1 := one_le_of_mem_primeRange (Finset.mem_filter.mp hn).1
    have hm1 := one_le_of_mem_primeRange (Finset.mem_filter.mp hm).1
    have hcong : n ≡ m [MOD q] := (ZMod.natCast_eq_natCast_iff n m q).mp
      ((Finset.mem_filter.mp hn).2.trans (Finset.mem_filter.mp hm).2.symm)
    have hmod : (n - 1) % q = (m - 1) % q := by
      have : n - 1 + 1 ≡ m - 1 + 1 [MOD q] := by
        rwa [Nat.sub_add_cancel hn1, Nat.sub_add_cancel hm1]
      exact Nat.ModEq.add_right_cancel' 1 this
    simp only at hnm
    have e1 := Nat.div_add_mod (n - 1) q
    have e2 := Nat.div_add_mod (m - 1) q
    rw [hnm] at e1
    omega
  have hmaps : ∀ n ∈ Rr, (n - 1) / q ∈ Finset.range (⌊X⌋₊ + 1) := by
    intro n hn
    have hnX : n ≤ ⌊X⌋₊ := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le ((Nat.div_le_self _ _).trans (by omega))
  have hterm : ∀ n ∈ Rr, 1 / ((n : ℝ) + q) ≤ 1 / (q * (((n - 1) / q : ℕ) + 1 : ℝ)) := by
    intro n hn
    have hn1 := one_le_of_mem_primeRange (Finset.mem_filter.mp hn).1
    apply one_div_le_one_div_of_le (by positivity)
    have h1 : q * ((n - 1) / q) ≤ n - 1 := Nat.mul_div_le (n - 1) q
    have h2 : ((q * ((n - 1) / q) : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast [Nat.cast_sub hn1] at h2
    nlinarith
  calc ∑ n ∈ Rr, 1 / ((n : ℝ) + q)
      ≤ ∑ n ∈ Rr, 1 / (q * (((n - 1) / q : ℕ) + 1 : ℝ)) := Finset.sum_le_sum hterm
    _ = ∑ k ∈ Rr.image (fun n : ℕ => (n - 1) / q), 1 / (q * ((k : ℝ) + 1)) :=
        (Finset.sum_image (f := fun k : ℕ => 1 / ((q : ℝ) * ((k : ℝ) + 1))) hinj).symm
    _ ≤ ∑ k ∈ Finset.range (⌊X⌋₊ + 1), 1 / (q * ((k : ℝ) + 1)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
          exact hmaps n hn
        · intro k _ _; positivity
    _ = (harmonic (⌊X⌋₊ + 1) : ℝ) / q := by
        rw [harmonic]
        push_cast
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun k _ => ?_
        field_simp
    _ ≤ (1 + Real.log ((⌊X⌋₊ : ℝ) + 1)) / q := by
        apply div_le_div_of_nonneg_right _ hq0.le
        have := harmonic_le_one_add_log (⌊X⌋₊ + 1)
        push_cast at this
        exact this

/-- `(∑_{n ≤ X, n ≡ r} a_n)² ≤ (1 + log(⌊X⌋ + 1))/q · ∑_{n ≤ X, n ≡ r} a_n² (n + q)`. -/
theorem sq_classSum_acoef_le {q : ℕ} (hq : 0 < q) (X : ℝ) (r : ZMod q) :
    (∑ n ∈ (primeRange X).filter (fun n : ℕ => (n : ZMod q) = r), acoef n) ^ 2
      ≤ (1 + Real.log ((⌊X⌋₊ : ℝ) + 1)) / q *
        ∑ n ∈ (primeRange X).filter (fun n : ℕ => (n : ZMod q) = r), acoef n ^ 2 * ((n : ℝ) + q) := by
  set Rr := (primeRange X).filter (fun n : ℕ => (n : ZMod q) = r) with hRr
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hg : ∀ n ∈ Rr, (0 : ℝ) < 1 / ((n : ℝ) + q) := fun n _ => by positivity
  have hH := sum_inv_add_le_of_residueClass hq X r
  have hsed := Finset.sq_sum_div_le_sum_sq_div Rr acoef hg
  have he : ∀ n ∈ Rr, acoef n ^ 2 / (1 / ((n : ℝ) + q)) = acoef n ^ 2 * ((n : ℝ) + q) :=
    fun n _ => by rw [div_div_eq_mul_div, div_one]
  rw [Finset.sum_congr rfl he] at hsed
  have hB0 : 0 ≤ ∑ n ∈ Rr, acoef n ^ 2 * ((n : ℝ) + q) :=
    Finset.sum_nonneg fun n _ => by positivity
  rcases Rr.eq_empty_or_nonempty with hE | hNE
  · rw [hE]; simp
  · have hG : 0 < ∑ n ∈ Rr, 1 / ((n : ℝ) + q) := Finset.sum_pos hg hNE
    rw [div_le_iff₀ hG] at hsed
    calc (∑ n ∈ Rr, acoef n) ^ 2 ≤ (∑ n ∈ Rr, acoef n ^ 2 * ((n : ℝ) + q))
          * ∑ n ∈ Rr, 1 / ((n : ℝ) + q) := hsed
      _ ≤ (∑ n ∈ Rr, acoef n ^ 2 * ((n : ℝ) + q)) * ((1 + Real.log ((⌊X⌋₊ : ℝ) + 1)) / q) :=
          mul_le_mul_of_nonneg_left hH hB0
      _ = _ := by ring

/-- **The paired class sums.**  `∑_{n,m ≤ X, nm ≡ 1} a_n a_m ≤ (1 + log(⌊X⌋ + 1))/q ·
∑_{n ≤ X} a_n² (n + q)`. -/
theorem sum_inverseClass_acoef_le {q : ℕ} [NeZero q] (X : ℝ) :
    ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, inverseClass q n m * (acoef n * acoef m)
      ≤ (1 + Real.log ((⌊X⌋₊ : ℝ) + 1)) / q * ∑ n ∈ primeRange X, acoef n ^ 2 * ((n : ℝ) + q) := by
  classical
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  set U := (Finset.univ : Finset (ZMod q)).filter IsUnit with hU
  set A : ZMod q → ℝ := fun r =>
    ∑ n ∈ (primeRange X).filter (fun n : ℕ => (n : ZMod q) = r), acoef n with hA
  set H : ℝ := (1 + Real.log ((⌊X⌋₊ : ℝ) + 1)) / q with hH
  rw [sum_inverseClass_eq_sum_classes]
  have hprod : ∀ r ∈ U, ∑ n ∈ (primeRange X).filter (fun n : ℕ => (n : ZMod q) = r),
      ∑ m ∈ (primeRange X).filter (fun m : ℕ => (m : ZMod q) = r⁻¹), acoef n * acoef m
        = A r * A r⁻¹ := fun r _ => by rw [hA]; simp only; rw [Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl hprod]
  -- r ↦ r⁻¹ permutes the units
  have hunit_inv : ∀ r ∈ U, r⁻¹ ∈ U := by
    intro r hr
    have hr' : IsUnit r := (Finset.mem_filter.mp hr).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      IsUnit.of_mul_eq_one r (ZMod.inv_mul_of_unit r hr')⟩
  have hinv_inv : ∀ r ∈ U, r⁻¹⁻¹ = r := by
    intro r hr
    have hr' : IsUnit r := (Finset.mem_filter.mp hr).2
    have hr'' : IsUnit r⁻¹ := (Finset.mem_filter.mp (hunit_inv r hr)).2
    calc r⁻¹⁻¹ = r⁻¹⁻¹ * (r⁻¹ * r) := by rw [ZMod.inv_mul_of_unit r hr', mul_one]
      _ = (r⁻¹⁻¹ * r⁻¹) * r := by rw [mul_assoc]
      _ = r := by rw [ZMod.inv_mul_of_unit _ hr'', one_mul]
  have hperm : ∑ r ∈ U, A r⁻¹ ^ 2 = ∑ r ∈ U, A r ^ 2 := by
    refine Finset.sum_nbij' (fun r => r⁻¹) (fun r => r⁻¹) hunit_inv hunit_inv hinv_inv hinv_inv ?_
    intro r _; rfl
  have hamgm : ∑ r ∈ U, A r * A r⁻¹ ≤ ∑ r ∈ U, A r ^ 2 := by
    have : ∑ r ∈ U, A r * A r⁻¹ ≤ ∑ r ∈ U, (A r ^ 2 + A r⁻¹ ^ 2) / 2 :=
      Finset.sum_le_sum fun r _ => by nlinarith [sq_nonneg (A r - A r⁻¹)]
    rw [← Finset.sum_div, Finset.sum_add_distrib, hperm] at this
    linarith
  have hclass : ∀ r ∈ U, A r ^ 2 ≤ H * ∑ n ∈ (primeRange X).filter (fun n : ℕ => (n : ZMod q) = r),
      acoef n ^ 2 * ((n : ℝ) + q) := fun r _ => sq_classSum_acoef_le hq X r
  have hH0 : 0 ≤ H := by
    rw [hH]
    have : 0 ≤ Real.log ((⌊X⌋₊ : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) ⌊X⌋₊])
    positivity
  calc ∑ r ∈ U, A r * A r⁻¹ ≤ ∑ r ∈ U, A r ^ 2 := hamgm
    _ ≤ ∑ r ∈ U, H * ∑ n ∈ (primeRange X).filter (fun n : ℕ => (n : ZMod q) = r),
          acoef n ^ 2 * ((n : ℝ) + q) := Finset.sum_le_sum hclass
    _ = H * ∑ n ∈ (primeRange X).filter (fun n : ℕ => (n : ZMod q) ∈ U),
          acoef n ^ 2 * ((n : ℝ) + q) := by
        rw [← Finset.mul_sum, Finset.sum_fiberwise_eq_sum_filter]
    _ ≤ H * ∑ n ∈ primeRange X, acoef n ^ 2 * ((n : ℝ) + q) := by
        apply mul_le_mul_of_nonneg_left _ hH0
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun n _ _ => by positivity

/-- **The character-averaged sum-frequency term.**  For continuous `Φ` with `Φ²` integrable,
`|∑_{n,m ≤ X} [nm ≡ 1] a_n a_m A⁺(y_n, y_m)| ≤ 2 (∫ Φ²) (1 + log(⌊X⌋ + 1))/q ·
∑_{n ≤ X} a_n² (n + q)`. -/
theorem sumFreq_inverseClass_bound {q : ℕ} [NeZero q] {Φ : ℝ → ℝ} {T : ℝ} (hΦ : Continuous Φ)
    (hΦ2 : Integrable fun x => Φ x ^ 2) (X : ℝ) :
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        acoef n * acoef m * (inverseClass q n m * Aplus Φ T (Real.log n) (Real.log m))|
      ≤ 2 * (∫ x, Φ x ^ 2) * ((1 + Real.log ((⌊X⌋₊ : ℝ) + 1)) / q *
          ∑ n ∈ primeRange X, acoef n ^ 2 * ((n : ℝ) + q)) := by
  set W : ℝ := ∫ x, Φ x ^ 2 with hW
  have hW0 : 0 ≤ W := MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have hic0 : ∀ n m, 0 ≤ inverseClass q n m := fun n m => by
    unfold inverseClass; split_ifs <;> norm_num
  have hterm : ∀ n ∈ primeRange X, ∀ m ∈ primeRange X,
      |acoef n * acoef m * (inverseClass q n m * Aplus Φ T (Real.log n) (Real.log m))|
        ≤ 2 * W * (inverseClass q n m * (acoef n * acoef m)) := by
    intro n hn m hm
    rcases acoef_eq_zero_or_two_le hn with h0 | hn2
    · rw [h0]; simp
    rcases acoef_eq_zero_or_two_le hm with h0 | hm2
    · rw [h0]; simp
    have hl2 : (1 : ℝ) / 2 < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
    have hlm : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast hm2)
    have hsum : 1 ≤ Real.log n + Real.log m := by linarith
    have hA := abs_Aplus_le (T := T) hΦ hΦ2 (lt_of_lt_of_le one_pos hsum)
    have hA' : |Aplus Φ T (Real.log n) (Real.log m)| ≤ 2 * W := by
      refine hA.trans ?_
      rw [← hW]
      have : 2 / (Real.log n + Real.log m) ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      exact mul_le_mul_of_nonneg_right this hW0
    simp only [abs_mul, abs_of_nonneg (acoef_nonneg n), abs_of_nonneg (acoef_nonneg m),
      abs_of_nonneg (hic0 n m)]
    have := mul_le_mul_of_nonneg_left hA' (hic0 n m)
    have hab := mul_nonneg (acoef_nonneg n) (acoef_nonneg m)
    nlinarith
  calc |∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
          acoef n * acoef m * (inverseClass q n m * Aplus Φ T (Real.log n) (Real.log m))|
      ≤ ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
          2 * W * (inverseClass q n m * (acoef n * acoef m)) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun m hm => hterm n hn m hm)
    _ = 2 * W * ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
          inverseClass q n m * (acoef n * acoef m) := by
        rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]
    _ ≤ 2 * W * ((1 + Real.log ((⌊X⌋₊ : ℝ) + 1)) / q *
          ∑ n ∈ primeRange X, acoef n ^ 2 * ((n : ℝ) + q)) :=
        mul_le_mul_of_nonneg_left (sum_inverseClass_acoef_le X) (by positivity)

end SumFrequency

/-! ## The character-averaged mean square up to its diagonal -/

/-- **Family mean square.**  With the Montgomery–Vaughan constant `C`, for `T ≥ 0`, continuous `Φ`
with `Φ²` integrable, and any `X`,
`|∑_χ 𝓜[P_χ, P_χ] − φ(q)/(2π²) ∑_{n ≤ X, (n,q)=1} a_n² A⁻(y_n, y_n)|
  ≤ φ(q)/(2π²) · (∫Φ²)/q · (8C + 2 + 2 log(⌊X⌋ + 1)) · ∑_{n ≤ X} a_n² (n + q)`.
Since `∑_{n ≤ X} a_n² (n + q) = ∑ Λ(n)² + q ∑ Λ(n)²/n`, the error is
`≪ φ(q) (∫Φ²) log X (X log X / q + log² X)`. -/
theorem sum_Mform_PXc_dirichlet_sub_diag_le {C : ℝ} (hMV : Zeta23.MVHilbert C) (hC : 0 ≤ C)
    {q : ℕ} [NeZero q] {Φ : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hΦ : Continuous Φ)
    (hΦ2 : Integrable fun x => Φ x ^ 2) (X : ℝ) :
    |∑ χ : DirichletCharacter ℂ q, Mform Φ T (PXc (fun n => χ n) X) (PXc (fun n => χ n) X)
        - (q.totient : ℝ) / (2 * Real.pi ^ 2) *
          ∑ n ∈ primeRange X, sameUnitClass q n n * acoef n ^ 2 * Aminus Φ T (Real.log n) (Real.log n)|
      ≤ (q.totient : ℝ) / (2 * Real.pi ^ 2) * ((∫ x, Φ x ^ 2) / q
          * (8 * C + 2 + 2 * Real.log ((⌊X⌋₊ : ℝ) + 1))
          * ∑ n ∈ primeRange X, acoef n ^ 2 * ((n : ℝ) + q)) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set W : ℝ := ∫ x, Φ x ^ 2 with hW
  set K : ℝ := (q.totient : ℝ) / (2 * Real.pi ^ 2) with hK
  have hK0 : 0 ≤ K := by positivity
  set R := primeRange X with hR
  set D : ℝ := ∑ n ∈ R, sameUnitClass q n n * acoef n ^ 2 * Aminus Φ T (Real.log n) (Real.log n)
    with hD
  set O1 : ℝ := ∑ n ∈ R, ∑ m ∈ R, sameUnitClass q n m *
      (if n = m then (0:ℝ) else acoef n * acoef m * Aminus Φ T (Real.log n) (Real.log m)) with hO1
  set O2 : ℝ := ∑ n ∈ R, ∑ m ∈ R,
      acoef n * acoef m * (inverseClass q n m * Aplus Φ T (Real.log n) (Real.log m)) with hO2
  have hsplit : ∑ n ∈ R, ∑ m ∈ R, acoef n * acoef m *
      (sameUnitClass q n m * Aminus Φ T (Real.log n) (Real.log m)
        + inverseClass q n m * Aplus Φ T (Real.log n) (Real.log m)) = D + O1 + O2 := by
    rw [hD, hO1, hO2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have e : ∀ m ∈ R, acoef n * acoef m *
        (sameUnitClass q n m * Aminus Φ T (Real.log n) (Real.log m)
          + inverseClass q n m * Aplus Φ T (Real.log n) (Real.log m))
        = (if n = m then sameUnitClass q n m * acoef n * acoef m *
              Aminus Φ T (Real.log n) (Real.log m) else 0)
          + (sameUnitClass q n m * (if n = m then (0:ℝ) else
              acoef n * acoef m * Aminus Φ T (Real.log n) (Real.log m))
            + acoef n * acoef m * (inverseClass q n m * Aplus Φ T (Real.log n) (Real.log m))) := by
      intro m _
      split_ifs <;> ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq,
      if_pos hn]
    ring
  rw [sum_Mform_PXc_dirichlet hT hΦ X, ← hR, hsplit]
  have hb1 := offDiag_residueClass_bound (q := q) hMV hC hT hΦ hΦ2 X
  have hb2 := sumFreq_inverseClass_bound (q := q) (T := T) hΦ hΦ2 X
  rw [← hR, ← hO1] at hb1
  rw [← hR, ← hO2] at hb2
  have hw : ∑ n ∈ R, acoef n ^ 2 * (((n : ℝ) + q) / q)
      = (∑ n ∈ R, acoef n ^ 2 * ((n : ℝ) + q)) / q := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hw] at hb1
  have e : K * (D + O1 + O2) - K * D = K * (O1 + O2) := by ring
  rw [e, abs_mul, abs_of_nonneg hK0]
  apply mul_le_mul_of_nonneg_left _ hK0
  calc |O1 + O2| ≤ |O1| + |O2| := abs_add_le _ _
    _ ≤ 8 * C * W * ((∑ n ∈ R, acoef n ^ 2 * ((n : ℝ) + q)) / q)
        + 2 * W * ((1 + Real.log ((⌊X⌋₊ : ℝ) + 1)) / q *
          ∑ n ∈ R, acoef n ^ 2 * ((n : ℝ) + q)) := add_le_add hb1 hb2
    _ = W / q * (8 * C + 2 + 2 * Real.log ((⌊X⌋₊ : ℝ) + 1))
          * ∑ n ∈ R, acoef n ^ 2 * ((n : ℝ) + q) := by
        field_simp
        ring

end RHTower
