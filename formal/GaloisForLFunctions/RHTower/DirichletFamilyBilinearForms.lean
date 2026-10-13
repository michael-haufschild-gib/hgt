import GaloisForLFunctions.RHTower.DirichletFamilyPrimeMeanSquare
import Zeta23.PrimeSideA.Basic

/-!
# Character averages of bilinear forms in the prime polynomials

Let `β` be a real form on functions `ℝ → ℝ` that is bilinear on the trigonometric polynomials
`τ ↦ ∑_{n ≤ X} (x_n cos(τ log n) + x'_n sin(τ log n))`.  For the prime polynomials
`P_χ(τ) = −(1/π) Re ∑_{n ≤ X} Λ(n) χ(n) n^{−1/2−iτ}` of the Dirichlet characters modulo `q`,
orthogonality of characters gives

`∑_χ β(P_χ, P_χ) = φ(q)/(2π²) ∑_{r ∈ (ℤ/q)^×} (β(C_r, C_r) + β(S_r, S_r) + β(C_r, C_{r⁻¹}) − β(S_r, S_{r⁻¹}))`

(`sum_bilin_PXc_dirichlet`), where `C_r(τ) = ∑_{n ≤ X, n ≡ r} a_n cos(τ log n)` and
`S_r(τ) = ∑_{n ≤ X, n ≡ r} a_n sin(τ log n)` are the prime polynomials of one residue class.
The character average of a quadratic quantity therefore splits into quadratic quantities of the
residue-class polynomials, each of which is bounded pointwise by `∑_{n ≤ X, n ≡ r} a_n` rather than
by `∑_{n ≤ X} a_n`.
-/

open Complex ComplexConjugate

noncomputable section

namespace RHTower

open Zeta23 Zeta23.PrimeSide Zeta23.ThmE

/-! ## Real and imaginary parts of character values -/

section CharacterParts

variable {q : ℕ} [NeZero q]

private lemma re_mul_re' (z w : ℂ) : z.re * w.re = ((z * conj w).re + (z * w).re) / 2 := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring

private lemma im_mul_im' (z w : ℂ) : z.im * w.im = ((z * conj w).re - (z * w).re) / 2 := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring

private lemma re_mul_im' (z w : ℂ) : z.re * w.im = ((z * w).im - (z * conj w).im) / 2 := by
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring

private lemma im_mul_re' (z w : ℂ) : z.im * w.re = ((z * w).im + (z * conj w).im) / 2 := by
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring

private lemma sum_conj_eq (n m : ℕ) :
    ∑ χ : DirichletCharacter ℂ q, χ n * conj (χ m)
      = ((sameUnitClass q n m * q.totient : ℝ) : ℂ) := by
  rw [sum_dirichletChar_mul_conj]
  unfold sameUnitClass
  by_cases h : IsUnit (m : ZMod q) ∧ (n : ZMod q) = m
  · rw [if_pos h, if_pos h]; push_cast; ring
  · rw [if_neg h, if_neg h]; push_cast; ring

private lemma sum_mul_eq (n m : ℕ) :
    ∑ χ : DirichletCharacter ℂ q, χ n * χ m = ((inverseClass q n m * q.totient : ℝ) : ℂ) := by
  rw [sum_dirichletChar_mul]
  unfold inverseClass
  by_cases h : (n : ZMod q) * m = 1
  · rw [if_pos h, if_pos h]; push_cast; ring
  · rw [if_neg h, if_neg h]; push_cast; ring

lemma sum_dirichletChar_re_mul_re (n m : ℕ) :
    ∑ χ : DirichletCharacter ℂ q, (χ n).re * (χ m).re
      = q.totient / 2 * (sameUnitClass q n m + inverseClass q n m) := by
  simp_rw [re_mul_re']
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Complex.re_sum, ← Complex.re_sum, sum_conj_eq,
    sum_mul_eq, Complex.ofReal_re, Complex.ofReal_re]
  ring

lemma sum_dirichletChar_im_mul_im (n m : ℕ) :
    ∑ χ : DirichletCharacter ℂ q, (χ n).im * (χ m).im
      = q.totient / 2 * (sameUnitClass q n m - inverseClass q n m) := by
  simp_rw [im_mul_im']
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Complex.re_sum, ← Complex.re_sum, sum_conj_eq,
    sum_mul_eq, Complex.ofReal_re, Complex.ofReal_re]
  ring

lemma sum_dirichletChar_re_mul_im (n m : ℕ) :
    ∑ χ : DirichletCharacter ℂ q, (χ n).re * (χ m).im = 0 := by
  simp_rw [re_mul_im']
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Complex.im_sum, ← Complex.im_sum, sum_conj_eq,
    sum_mul_eq, Complex.ofReal_im, Complex.ofReal_im]
  ring

lemma sum_dirichletChar_im_mul_re (n m : ℕ) :
    ∑ χ : DirichletCharacter ℂ q, (χ n).im * (χ m).re = 0 := by
  simp_rw [im_mul_re']
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Complex.im_sum, ← Complex.im_sum, sum_conj_eq,
    sum_mul_eq, Complex.ofReal_im, Complex.ofReal_im]
  ring

end CharacterParts

/-! ## Trigonometric polynomials over the prime range -/

/-- `τ ↦ ∑_{n ∈ R} (x_n cos(τ log n) + x'_n sin(τ log n))`. -/
def trigPoly (R : Finset ℕ) (x x' : ℕ → ℝ) (τ : ℝ) : ℝ :=
  ∑ n ∈ R, (x n * Real.cos (τ * Real.log n) + x' n * Real.sin (τ * Real.log n))

/-- `τ ↦ cos(τ log n)`. -/
def cosFreq (n : ℕ) (τ : ℝ) : ℝ := Real.cos (τ * Real.log n)

/-- `τ ↦ sin(τ log n)`. -/
def sinFreq (n : ℕ) (τ : ℝ) : ℝ := Real.sin (τ * Real.log n)

/-- `β` is bilinear on the trigonometric polynomials over `R`. -/
def IsTrigBilin (β : (ℝ → ℝ) → (ℝ → ℝ) → ℝ) (R : Finset ℕ) : Prop :=
  ∀ x x' y y' : ℕ → ℝ, β (trigPoly R x x') (trigPoly R y y')
    = ∑ n ∈ R, ∑ m ∈ R,
        (x n * y m * β (cosFreq n) (cosFreq m) + x n * y' m * β (cosFreq n) (sinFreq m)
          + x' n * y m * β (sinFreq n) (cosFreq m) + x' n * y' m * β (sinFreq n) (sinFreq m))

open Classical in
/-- The coefficients `a_n` restricted to the residue class `r`. -/
def classCoef (q : ℕ) (r : ZMod q) (n : ℕ) : ℝ := if (n : ZMod q) = r then acoef n else 0

/-- `C_r(τ) = ∑_{n ≤ X, n ≡ r} a_n cos(τ log n)`. -/
def classCos (q : ℕ) (X : ℝ) (r : ZMod q) : ℝ → ℝ := trigPoly (primeRange X) (classCoef q r) 0

/-- `S_r(τ) = ∑_{n ≤ X, n ≡ r} a_n sin(τ log n)`. -/
def classSin (q : ℕ) (X : ℝ) (r : ZMod q) : ℝ → ℝ := trigPoly (primeRange X) 0 (classCoef q r)

lemma PXc_dirichlet_eq_trigPoly {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℝ) :
    PXc (fun n => χ n) X = trigPoly (primeRange X)
      (fun n => -(1 / Real.pi) * acoef n * (χ n).re) (fun n => -(1 / Real.pi) * acoef n * (χ n).im) := by
  funext τ
  rw [PXc_eq_sum_cos_sin]
  unfold trigPoly
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (one_le_of_mem_primeRange hn)
  have ha : (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) = acoef n := by
    unfold acoef
    rw [Real.rpow_neg hn0.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  rw [ha]
  ring

open Classical in
/-- The `[n ≡ m, (m,q)=1]`-weighted double sum of a product of class coefficients. -/
private lemma sum_classes_same {q : ℕ} [NeZero q] (R : Finset ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ r ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit, ∑ n ∈ R, ∑ m ∈ R,
        classCoef q r n * classCoef q r m * g n m
      = ∑ n ∈ R, ∑ m ∈ R, sameUnitClass q n m * (acoef n * acoef m * g n m) := by
  rw [sum_sameUnitClass_eq_sum_classes]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_filter]
  unfold classCoef
  split_ifs with h1
  · refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> ring
  · simp

open Classical in
private lemma sum_classes_inv {q : ℕ} [NeZero q] (R : Finset ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ r ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit, ∑ n ∈ R, ∑ m ∈ R,
        classCoef q r n * classCoef q r⁻¹ m * g n m
      = ∑ n ∈ R, ∑ m ∈ R, inverseClass q n m * (acoef n * acoef m * g n m) := by
  rw [sum_inverseClass_eq_sum_classes]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_filter]
  unfold classCoef
  split_ifs with h1
  · refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> ring
  · simp

/-- **Character average of a bilinear form.**  If `β` is bilinear on the trigonometric polynomials
over `n ≤ X`, then
`∑_χ β(P_χ, P_χ) = φ(q)/(2π²) ∑_{r unit} (β(C_r, C_r) + β(S_r, S_r) + β(C_r, C_{r⁻¹}) − β(S_r, S_{r⁻¹}))`. -/
theorem sum_bilin_PXc_dirichlet {q : ℕ} [NeZero q] (X : ℝ) (β : (ℝ → ℝ) → (ℝ → ℝ) → ℝ)
    (hβ : IsTrigBilin β (primeRange X)) :
    ∑ χ : DirichletCharacter ℂ q, β (PXc (fun n => χ n) X) (PXc (fun n => χ n) X)
      = (q.totient : ℝ) / (2 * Real.pi ^ 2) *
        ∑ r ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
          (β (classCos q X r) (classCos q X r) + β (classSin q X r) (classSin q X r)
            + β (classCos q X r) (classCos q X r⁻¹) - β (classSin q X r) (classSin q X r⁻¹)) := by
  classical
  unfold IsTrigBilin at hβ
  set cc : ℕ → ℕ → ℝ := fun n m => β (cosFreq n) (cosFreq m) with hcc
  set ss : ℕ → ℕ → ℝ := fun n m => β (sinFreq n) (sinFreq m) with hss
  -- left side
  have hL : ∑ χ : DirichletCharacter ℂ q, β (PXc (fun n => χ n) X) (PXc (fun n => χ n) X)
      = (q.totient : ℝ) / (2 * Real.pi ^ 2) * ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
          (sameUnitClass q n m * (acoef n * acoef m * (cc n m + ss n m))
            + inverseClass q n m * (acoef n * acoef m * (cc n m - ss n m))) := by
    simp_rw [PXc_dirichlet_eq_trigPoly, hβ]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have e : ∀ χ : DirichletCharacter ℂ q,
        -(1 / Real.pi) * acoef n * (χ n).re * (-(1 / Real.pi) * acoef m * (χ m).re) * cc n m
          + -(1 / Real.pi) * acoef n * (χ n).re * (-(1 / Real.pi) * acoef m * (χ m).im)
            * β (cosFreq n) (sinFreq m)
          + -(1 / Real.pi) * acoef n * (χ n).im * (-(1 / Real.pi) * acoef m * (χ m).re)
            * β (sinFreq n) (cosFreq m)
          + -(1 / Real.pi) * acoef n * (χ n).im * (-(1 / Real.pi) * acoef m * (χ m).im) * ss n m
        = (acoef n * acoef m / Real.pi ^ 2) *
          ((χ n).re * (χ m).re * cc n m + (χ n).re * (χ m).im * β (cosFreq n) (sinFreq m)
            + (χ n).im * (χ m).re * β (sinFreq n) (cosFreq m) + (χ n).im * (χ m).im * ss n m) := by
      intro χ; field_simp
    rw [Finset.sum_congr rfl fun χ _ => e χ, ← Finset.mul_sum]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [sum_dirichletChar_re_mul_re, sum_dirichletChar_re_mul_im, sum_dirichletChar_im_mul_re,
      sum_dirichletChar_im_mul_im]
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  -- right side, expanded through bilinearity
  have hC : ∀ r r' : ZMod q, β (classCos q X r) (classCos q X r')
      = ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, classCoef q r n * classCoef q r' m * cc n m := by
    intro r r'
    unfold classCos
    rw [hβ]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    simp only [Pi.zero_apply, hcc]; ring
  have hS : ∀ r r' : ZMod q, β (classSin q X r) (classSin q X r')
      = ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, classCoef q r n * classCoef q r' m * ss n m := by
    intro r r'
    unfold classSin
    rw [hβ]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    simp only [Pi.zero_apply, hss]; ring
  rw [hL]
  congr 1
  simp_rw [hC, hS]
  conv_rhs => rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_classes_same, sum_classes_same, sum_classes_inv, sum_classes_inv]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-! ## Forms that are bilinear on trigonometric polynomials -/

section Closure

variable {R : Finset ℕ}

/-- `ℓ` is linear on the trigonometric polynomials over `R`. -/
def IsTrigLinear (ℓ : (ℝ → ℝ) → ℝ) (R : Finset ℕ) : Prop :=
  ∀ x x' : ℕ → ℝ, ℓ (trigPoly R x x') = ∑ n ∈ R, (x n * ℓ (cosFreq n) + x' n * ℓ (sinFreq n))

lemma IsTrigBilin.add {β₁ β₂ : (ℝ → ℝ) → (ℝ → ℝ) → ℝ} (h₁ : IsTrigBilin β₁ R)
    (h₂ : IsTrigBilin β₂ R) : IsTrigBilin (fun u v => β₁ u v + β₂ u v) R := by
  intro x x' y y'
  simp only
  rw [h₁, h₂, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

lemma IsTrigBilin.sub {β₁ β₂ : (ℝ → ℝ) → (ℝ → ℝ) → ℝ} (h₁ : IsTrigBilin β₁ R)
    (h₂ : IsTrigBilin β₂ R) : IsTrigBilin (fun u v => β₁ u v - β₂ u v) R := by
  intro x x' y y'
  simp only
  rw [h₁, h₂, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

lemma IsTrigBilin.const_mul {β : (ℝ → ℝ) → (ℝ → ℝ) → ℝ} (h : IsTrigBilin β R) (c : ℝ) :
    IsTrigBilin (fun u v => c * β u v) R := by
  intro x x' y y'
  simp only
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

lemma IsTrigBilin.sum {ι : Type*} (s : Finset ι) {β : ι → (ℝ → ℝ) → (ℝ → ℝ) → ℝ}
    (h : ∀ i ∈ s, IsTrigBilin (β i) R) : IsTrigBilin (fun u v => ∑ i ∈ s, β i u v) R := by
  intro x x' y y'
  simp only
  rw [Finset.sum_congr rfl fun i hi => h i hi x x' y y', Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

lemma isTrigBilin_mul {ℓ ℓ' : (ℝ → ℝ) → ℝ} (h : IsTrigLinear ℓ R) (h' : IsTrigLinear ℓ' R) :
    IsTrigBilin (fun u v => ℓ u * ℓ' v) R := by
  intro x x' y y'
  simp only
  rw [h, h', Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  ring

lemma continuous_trigPoly (R : Finset ℕ) (x x' : ℕ → ℝ) : Continuous (trigPoly R x x') := by
  unfold trigPoly; fun_prop

lemma continuous_cosFreq (n : ℕ) : Continuous (cosFreq n) := by unfold cosFreq; fun_prop

lemma continuous_sinFreq (n : ℕ) : Continuous (sinFreq n) := by unfold sinFreq; fun_prop

lemma abs_trigPoly_le (R : Finset ℕ) (x x' : ℕ → ℝ) (τ : ℝ) :
    |trigPoly R x x' τ| ≤ ∑ n ∈ R, (|x n| + |x' n|) := by
  unfold trigPoly
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  · rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

/-- `𝓜` is bilinear on trigonometric polynomials. -/
lemma isTrigBilin_Mform {Φ : ℝ → ℝ} (hΦ : Continuous Φ) (T : ℝ) (R : Finset ℕ) :
    IsTrigBilin (Mform Φ T) R := by
  intro x x' y y'
  set S := Set.Icc T (2 * T) ×ˢ Set.Icc T (2 * T)
  have hint : ∀ u v : ℝ → ℝ, Continuous u → Continuous v →
      MeasureTheory.Integrable (fun q : ℝ × ℝ => Φ (q.1 - q.2) ^ 2 * u q.1 * v q.2)
        (MeasureTheory.volume.restrict S) := fun u v hu hv => Mform_integrableOn hΦ hu hv
  have hpt : ∀ q : ℝ × ℝ, Φ (q.1 - q.2) ^ 2 * trigPoly R x x' q.1 * trigPoly R y y' q.2
      = ∑ n ∈ R, ∑ m ∈ R,
          (x n * y m * (Φ (q.1 - q.2) ^ 2 * cosFreq n q.1 * cosFreq m q.2)
            + x n * y' m * (Φ (q.1 - q.2) ^ 2 * cosFreq n q.1 * sinFreq m q.2)
            + x' n * y m * (Φ (q.1 - q.2) ^ 2 * sinFreq n q.1 * cosFreq m q.2)
            + x' n * y' m * (Φ (q.1 - q.2) ^ 2 * sinFreq n q.1 * sinFreq m q.2)) := by
    intro q
    unfold trigPoly cosFreq sinFreq
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  have hterm : ∀ n m : ℕ, MeasureTheory.Integrable (fun q : ℝ × ℝ =>
      x n * y m * (Φ (q.1 - q.2) ^ 2 * cosFreq n q.1 * cosFreq m q.2)
        + x n * y' m * (Φ (q.1 - q.2) ^ 2 * cosFreq n q.1 * sinFreq m q.2)
        + x' n * y m * (Φ (q.1 - q.2) ^ 2 * sinFreq n q.1 * cosFreq m q.2)
        + x' n * y' m * (Φ (q.1 - q.2) ^ 2 * sinFreq n q.1 * sinFreq m q.2))
      (MeasureTheory.volume.restrict S) := fun n m =>
    ((((hint _ _ (continuous_cosFreq n) (continuous_cosFreq m)).const_mul _).add
      ((hint _ _ (continuous_cosFreq n) (continuous_sinFreq m)).const_mul _)).add
      ((hint _ _ (continuous_sinFreq n) (continuous_cosFreq m)).const_mul _)).add
      ((hint _ _ (continuous_sinFreq n) (continuous_sinFreq m)).const_mul _)
  unfold Mform
  simp_rw [hpt]
  rw [MeasureTheory.integral_finsetSum _ fun n _ =>
    MeasureTheory.integrable_finsetSum _ fun m _ => hterm n m]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MeasureTheory.integral_finsetSum _ fun m _ => hterm n m]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h1 := hint _ _ (continuous_cosFreq n) (continuous_cosFreq m)
  have h2 := hint _ _ (continuous_cosFreq n) (continuous_sinFreq m)
  have h3 := hint _ _ (continuous_sinFreq n) (continuous_cosFreq m)
  have h4 := hint _ _ (continuous_sinFreq n) (continuous_sinFreq m)
  rw [MeasureTheory.integral_add, MeasureTheory.integral_add, MeasureTheory.integral_add,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  all_goals first
    | rfl
    | exact ((h1.const_mul _).add (h2.const_mul _)).add (h3.const_mul _)
    | exact (h1.const_mul _).add (h2.const_mul _)
    | exact h1.const_mul _ | exact h2.const_mul _ | exact h3.const_mul _ | exact h4.const_mul _

end Closure

/-! ## Polarisation on trigonometric polynomials -/

section Polarisation

variable {R : Finset ℕ} {β : (ℝ → ℝ) → (ℝ → ℝ) → ℝ}

lemma IsTrigBilin.expand_add (hβ : IsTrigBilin β R) (x x' y y' : ℕ → ℝ) :
    β (trigPoly R (x + y) (x' + y')) (trigPoly R (x + y) (x' + y'))
      = β (trigPoly R x x') (trigPoly R x x') + β (trigPoly R x x') (trigPoly R y y')
        + β (trigPoly R y y') (trigPoly R x x') + β (trigPoly R y y') (trigPoly R y y') := by
  rw [hβ, hβ, hβ, hβ, hβ, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Pi.add_apply]
  ring

lemma IsTrigBilin.expand_sub (hβ : IsTrigBilin β R) (x x' y y' : ℕ → ℝ) :
    β (trigPoly R (x - y) (x' - y')) (trigPoly R (x - y) (x' - y'))
      = β (trigPoly R x x') (trigPoly R x x') - β (trigPoly R x x') (trigPoly R y y')
        - β (trigPoly R y y') (trigPoly R x x') + β (trigPoly R y y') (trigPoly R y y') := by
  rw [hβ, hβ, hβ, hβ, hβ, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Pi.sub_apply]
  ring

/-- **Polarisation.**  For a symmetric form bilinear on trigonometric polynomials,
`4 β(A, B) = β(A + B, A + B) − β(A − B, A − B)`. -/
lemma IsTrigBilin.polarization (hβ : IsTrigBilin β R) (hsymm : ∀ u v, β u v = β v u)
    (x x' y y' : ℕ → ℝ) :
    4 * β (trigPoly R x x') (trigPoly R y y')
      = β (trigPoly R (x + y) (x' + y')) (trigPoly R (x + y) (x' + y'))
        - β (trigPoly R (x - y) (x' - y')) (trigPoly R (x - y) (x' - y')) := by
  rw [hβ.expand_add, hβ.expand_sub, hsymm (trigPoly R y y') (trigPoly R x x')]
  ring

end Polarisation

end RHTower
