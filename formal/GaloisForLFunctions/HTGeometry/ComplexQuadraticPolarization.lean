import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Polarization of bounded semidefinite complex quadratic functions

A nonnegative complex-homogeneous function satisfying the parallelogram identity polarizes to a
Hermitian sesquilinear form.  The only analytic input needed to exclude pathological additive
maps is a quadratic norm bound.  This is the semidefinite Jordan--von Neumann bridge used by the
matrix-valued spectral-law construction.
-/

open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Real polarization of a real-valued quadratic function. -/
def realQuadraticPolarization (q : V → ℝ) (x y : V) : ℝ :=
  (q (x + y) - q (x - y)) / 4

theorem quadratic_zero
    (q : V → ℝ) (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x) :
    q 0 = 0 := by
  have h := hsmul 0 0
  simpa using h

theorem quadratic_neg
    (q : V → ℝ) (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (x : V) : q (-x) = q x := by
  have h := hsmul (-1) x
  simpa using h

theorem realQuadraticPolarization_zero_left
    (q : V → ℝ) (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (y : V) : realQuadraticPolarization q 0 y = 0 := by
  rw [realQuadraticPolarization, zero_add, zero_sub, quadratic_neg q hsmul]
  ring

theorem realQuadraticPolarization_symm
    (q : V → ℝ) (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (x y : V) : realQuadraticPolarization q x y = realQuadraticPolarization q y x := by
  rw [realQuadraticPolarization, realQuadraticPolarization]
  have hsum : y + x = x + y := add_comm _ _
  have hsub : y - x = -(x - y) := by abel
  rw [hsum, hsub, quadratic_neg q hsmul]

theorem realQuadraticPolarization_jensen
    (q : V → ℝ)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (x z y : V) :
    realQuadraticPolarization q (x + z) y +
        realQuadraticPolarization q (x - z) y =
      2 * realQuadraticPolarization q x y := by
  have hplus := hpar (x + y) z
  have hminus := hpar (x - y) z
  simp only [realQuadraticPolarization]
  rw [show x + z + y = x + y + z by abel,
    show x + z - y = x - y + z by abel,
    show x - z + y = x + y - z by abel,
    show x - z - y = x - y - z by abel]
  linarith

theorem realQuadraticPolarization_two_smul
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (x y : V) :
    realQuadraticPolarization q ((2 : ℝ) • x) y =
      2 * realQuadraticPolarization q x y := by
  have h := realQuadraticPolarization_jensen q hpar x x y
  rw [sub_self, realQuadraticPolarization_zero_left q hsmul] at h
  simpa [two_smul ℝ] using h

theorem realQuadraticPolarization_add_left
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (x z y : V) :
    realQuadraticPolarization q (x + z) y =
      realQuadraticPolarization q x y + realQuadraticPolarization q z y := by
  let u : V := (2 : ℝ)⁻¹ • (x + z)
  let v : V := (2 : ℝ)⁻¹ • (x - z)
  have huv : u + v = x := by
    dsimp only [u, v]
    module
  have huv' : u - v = z := by
    dsimp only [u, v]
    module
  have hsum := realQuadraticPolarization_jensen q hpar u v y
  rw [huv, huv'] at hsum
  have htwo := realQuadraticPolarization_two_smul q hsmul hpar u y
  have h2u : (2 : ℝ) • u = x + z := by
    dsimp only [u]
    module
  rw [h2u] at htwo
  linarith

theorem realQuadraticPolarization_add_right
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (x y z : V) :
    realQuadraticPolarization q x (y + z) =
      realQuadraticPolarization q x y + realQuadraticPolarization q x z := by
  rw [realQuadraticPolarization_symm q hsmul,
    realQuadraticPolarization_add_left q hsmul hpar,
    realQuadraticPolarization_symm q hsmul y,
    realQuadraticPolarization_symm q hsmul z]

/-- Additive real polarization in the first variable. -/
def realQuadraticPolarizationAddHom
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (y : V) : V →+ ℝ where
  toFun x := realQuadraticPolarization q x y
  map_zero' := realQuadraticPolarization_zero_left q hsmul y
  map_add' := fun x z ↦ realQuadraticPolarization_add_left q hsmul hpar x z y

theorem quadratic_add_eq_polarization
    (q : V → ℝ)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (x y : V) :
    q (x + y) = q x + q y + 2 * realQuadraticPolarization q x y := by
  have h := hpar x y
  rw [realQuadraticPolarization]
  linarith

theorem realQuadraticPolarization_self
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (x : V) : realQuadraticPolarization q x x = q x := by
  rw [realQuadraticPolarization, sub_self, quadratic_zero q hsmul]
  have h := hsmul 2 x
  rw [show x + x = (2 : ℂ) • x by module, h]
  norm_num [Complex.normSq_apply]

theorem quadratic_real_smul
    (q : V → ℝ) (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (t : ℝ) (x : V) : q (t • x) = t ^ 2 * q x := by
  have h := hsmul (t : ℂ) x
  rw [show (t : ℂ) • x = t • x by rfl] at h
  simpa [Complex.normSq_apply, pow_two] using h

theorem realQuadraticPolarization_rat_smul_left
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (t : ℚ) (x y : V) :
    realQuadraticPolarization q ((t : ℝ) • x) y =
      (t : ℝ) * realQuadraticPolarization q x y := by
  have h := map_ratCast_smul
    (realQuadraticPolarizationAddHom q hsmul hpar y) ℝ ℝ t x
  simpa [realQuadraticPolarizationAddHom] using h

theorem realQuadraticPolarization_sq_le
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (hnonneg : ∀ x, 0 ≤ q x) (x y : V) :
    realQuadraticPolarization q x y ^ 2 ≤ q x * q y := by
  let b := realQuadraticPolarization q x y
  let P : ℝ → ℝ := fun t ↦ q x * t ^ 2 + 2 * b * t + q y
  have hrat (t : ℚ) : 0 ≤ P (t : ℝ) := by
    have hq := hnonneg ((t : ℝ) • x + y)
    rw [quadratic_add_eq_polarization q hpar,
      quadratic_real_smul q hsmul,
      realQuadraticPolarization_rat_smul_left q hsmul hpar] at hq
    dsimp only [P, b]
    linarith
  have hclosed : IsClosed {t : ℝ | 0 ≤ P t} := by
    exact isClosed_le continuous_const (by fun_prop)
  have hrange : Set.range (Rat.cast : ℚ → ℝ) ⊆ {t : ℝ | 0 ≤ P t} := by
    rintro _ ⟨t, rfl⟩
    exact hrat t
  have hall (t : ℝ) : 0 ≤ P t := by
    have hsub := hclosed.closure_subset_iff.mpr hrange
    apply hsub
    rw [Rat.denseRange_cast.closure_eq]
    exact Set.mem_univ t
  have hqx := hnonneg x
  have hqy := hnonneg y
  rcases hqx.eq_or_lt with hqx0 | hqxpos
  · have hb : b = 0 := by
      by_contra hb0
      let t : ℝ := -(q y + 1) / (2 * b)
      have ht := hall t
      have hP : P t = -1 := by
        dsimp only [P, t]
        rw [← hqx0, zero_mul, zero_add]
        field_simp [hb0]
        ring
      rw [hP] at ht
      linarith
    simp [b, ← hqx0, hb]
  · let t : ℝ := -b / q x
    have ht := hall t
    have hP : P t = q y - b ^ 2 / q x := by
      dsimp only [P, t]
      field_simp [ne_of_gt hqxpos]
      ring
    rw [hP] at ht
    have hdiv : b ^ 2 / q x ≤ q y := by linarith
    have hmul := (div_le_iff₀ hqxpos).mp hdiv
    simpa [b, mul_comm] using hmul

theorem abs_realQuadraticPolarization_le
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (hnonneg : ∀ x, 0 ≤ q x) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, q x ≤ C * ‖x‖ ^ 2) (x y : V) :
    |realQuadraticPolarization q x y| ≤
      Real.sqrt (C * q y) * ‖x‖ := by
  have hsq0 : 0 ≤ C * q y := mul_nonneg hC (hnonneg y)
  have hsq := realQuadraticPolarization_sq_le q hsmul hpar hnonneg x y
  have hsq' : realQuadraticPolarization q x y ^ 2 ≤
      (C * q y) * ‖x‖ ^ 2 := by
    calc
      realQuadraticPolarization q x y ^ 2 ≤ q x * q y := hsq
      _ ≤ (C * ‖x‖ ^ 2) * q y := by
        exact mul_le_mul_of_nonneg_right (hbound x) (hnonneg y)
      _ = (C * q y) * ‖x‖ ^ 2 := by ring
  calc
    |realQuadraticPolarization q x y| =
        Real.sqrt (realQuadraticPolarization q x y ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt ((C * q y) * ‖x‖ ^ 2) := Real.sqrt_le_sqrt hsq'
    _ = Real.sqrt (C * q y) * ‖x‖ := by
      rw [Real.sqrt_mul hsq0, Real.sqrt_sq (norm_nonneg x)]

theorem realQuadraticPolarization_lipschitz
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (hnonneg : ∀ x, 0 ≤ q x) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, q x ≤ C * ‖x‖ ^ 2) (y : V) :
    LipschitzWith (NNReal.mk (Real.sqrt (C * q y)) (Real.sqrt_nonneg _))
      (realQuadraticPolarizationAddHom q hsmul hpar y) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x z
  change |realQuadraticPolarization q x y - realQuadraticPolarization q z y| ≤
    Real.sqrt (C * q y) * ‖x - z‖
  have hmap := map_sub (realQuadraticPolarizationAddHom q hsmul hpar y) x z
  change realQuadraticPolarization q (x - z) y =
      realQuadraticPolarization q x y - realQuadraticPolarization q z y at hmap
  rw [← hmap]
  exact abs_realQuadraticPolarization_le q hsmul hpar hnonneg C hC hbound (x - z) y

/-- Continuous real-linear polarization in the first variable. -/
def realQuadraticPolarizationCLM
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (hnonneg : ∀ x, 0 ≤ q x) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, q x ≤ C * ‖x‖ ^ 2) (y : V) : V →L[ℝ] ℝ :=
  (realQuadraticPolarizationAddHom q hsmul hpar y).toRealLinearMap
    (realQuadraticPolarization_lipschitz q hsmul hpar hnonneg C hC hbound y).continuous

@[simp]
theorem realQuadraticPolarizationCLM_apply
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (hnonneg : ∀ x, 0 ≤ q x) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, q x ≤ C * ‖x‖ ^ 2) (y x : V) :
    realQuadraticPolarizationCLM q hsmul hpar hnonneg C hC hbound y x =
      realQuadraticPolarization q x y := rfl

theorem realQuadraticPolarization_real_smul_left
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (hnonneg : ∀ x, 0 ≤ q x) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, q x ≤ C * ‖x‖ ^ 2) (t : ℝ) (x y : V) :
    realQuadraticPolarization q (t • x) y =
      t * realQuadraticPolarization q x y := by
  exact map_smul (realQuadraticPolarizationCLM q hsmul hpar hnonneg C hC hbound y) t x

theorem realQuadraticPolarization_real_smul_right
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (hnonneg : ∀ x, 0 ≤ q x) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, q x ≤ C * ‖x‖ ^ 2) (t : ℝ) (x y : V) :
    realQuadraticPolarization q x (t • y) =
      t * realQuadraticPolarization q x y := by
  rw [realQuadraticPolarization_symm q hsmul,
    realQuadraticPolarization_real_smul_left q hsmul hpar hnonneg C hC hbound,
    realQuadraticPolarization_symm q hsmul]

theorem realQuadraticPolarization_I_I
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (x y : V) :
    realQuadraticPolarization q (Complex.I • x) (Complex.I • y) =
      realQuadraticPolarization q x y := by
  simp only [realQuadraticPolarization, ← smul_add, ← smul_sub]
  rw [hsmul, hsmul]
  norm_num [Complex.normSq_apply]

theorem realQuadraticPolarization_I_left
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (x y : V) :
    realQuadraticPolarization q (Complex.I • x) y =
      -realQuadraticPolarization q x (Complex.I • y) := by
  have h := realQuadraticPolarization_I_I q hsmul x ((-Complex.I) • y)
  have hIy : Complex.I • ((-Complex.I) • y) = y := by
    rw [smul_smul]
    simp
  rw [hIy] at h
  have hscale : realQuadraticPolarization q x ((-Complex.I) • y) =
      -realQuadraticPolarization q x (Complex.I • y) := by
    rw [show (-Complex.I) • y = -(Complex.I • y) by module]
    have hz := realQuadraticPolarization_add_right q hsmul hpar x
      (Complex.I • y) (-(Complex.I • y))
    have hzero : realQuadraticPolarization q x 0 = 0 := by
      rw [realQuadraticPolarization_symm q hsmul]
      exact realQuadraticPolarization_zero_left q hsmul x
    rw [add_neg_cancel, hzero] at hz
    linarith
  calc
    realQuadraticPolarization q (Complex.I • x) y =
        realQuadraticPolarization q x ((-Complex.I) • y) := h
    _ = -realQuadraticPolarization q x (Complex.I • y) := hscale

/-- Complex polarization, conjugate-linear in the first variable and linear in the second. -/
def complexQuadraticPolarization (q : V → ℝ) (x y : V) : ℂ :=
  (realQuadraticPolarization q x y : ℂ) -
    Complex.I * (realQuadraticPolarization q x (Complex.I • y) : ℂ)

theorem complexQuadraticPolarization_add_left
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (x y z : V) :
    complexQuadraticPolarization q (x + y) z =
      complexQuadraticPolarization q x z + complexQuadraticPolarization q y z := by
  simp only [complexQuadraticPolarization,
    realQuadraticPolarization_add_left q hsmul hpar]
  push_cast
  ring

theorem complexQuadraticPolarization_add_right
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (x y z : V) :
    complexQuadraticPolarization q x (y + z) =
      complexQuadraticPolarization q x y + complexQuadraticPolarization q x z := by
  simp only [complexQuadraticPolarization, smul_add,
    realQuadraticPolarization_add_right q hsmul hpar]
  push_cast
  ring

theorem complexQuadraticPolarization_real_smul_left
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (hnonneg : ∀ x, 0 ≤ q x) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, q x ≤ C * ‖x‖ ^ 2) (t : ℝ) (x y : V) :
    complexQuadraticPolarization q (t • x) y =
      (t : ℂ) * complexQuadraticPolarization q x y := by
  simp only [complexQuadraticPolarization,
    realQuadraticPolarization_real_smul_left q hsmul hpar hnonneg C hC hbound]
  push_cast
  ring

theorem complexQuadraticPolarization_real_smul_right
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (hnonneg : ∀ x, 0 ≤ q x) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, q x ≤ C * ‖x‖ ^ 2) (t : ℝ) (x y : V) :
    complexQuadraticPolarization q x (t • y) =
      (t : ℂ) * complexQuadraticPolarization q x y := by
  have hIt : Complex.I • (t • y) = t • (Complex.I • y) := by module
  simp only [complexQuadraticPolarization, hIt,
    realQuadraticPolarization_real_smul_right q hsmul hpar hnonneg C hC hbound]
  push_cast
  ring

theorem complexQuadraticPolarization_I_smul_right
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (hnonneg : ∀ x, 0 ≤ q x) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, q x ≤ C * ‖x‖ ^ 2) (x y : V) :
    complexQuadraticPolarization q x (Complex.I • y) =
      Complex.I * complexQuadraticPolarization q x y := by
  have hII : Complex.I • (Complex.I • y) = (-1 : ℝ) • y := by
    rw [smul_smul, Complex.I_mul_I]
    norm_num
  simp only [complexQuadraticPolarization, hII,
    realQuadraticPolarization_real_smul_right q hsmul hpar hnonneg C hC hbound]
  push_cast
  simp only [mul_sub, ← mul_assoc, Complex.I_mul_I, neg_mul, one_mul]
  ring

theorem complexQuadraticPolarization_I_smul_left
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (x y : V) :
    complexQuadraticPolarization q (Complex.I • x) y =
      -Complex.I * complexQuadraticPolarization q x y := by
  unfold complexQuadraticPolarization
  rw [realQuadraticPolarization_I_I q hsmul x y,
    realQuadraticPolarization_I_left q hsmul hpar x y]
  push_cast
  simp only [mul_sub, ← mul_assoc, Complex.I_mul_I, neg_mul, one_mul]
  ring

theorem complexQuadraticPolarization_smul_left
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (hnonneg : ∀ x, 0 ≤ q x) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, q x ≤ C * ‖x‖ ^ 2) (c : ℂ) (x y : V) :
    complexQuadraticPolarization q (c • x) y =
      star c * complexQuadraticPolarization q x y := by
  have hcx : c • x = c.re • x + c.im • (Complex.I • x) := by
    conv_lhs => rw [← Complex.re_add_im c]
    module
  have hstar : star c = (c.re : ℂ) - (c.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hcx, complexQuadraticPolarization_add_left q hsmul hpar,
    complexQuadraticPolarization_real_smul_left q hsmul hpar hnonneg C hC hbound,
    complexQuadraticPolarization_real_smul_left q hsmul hpar hnonneg C hC hbound,
    complexQuadraticPolarization_I_smul_left q hsmul hpar, hstar]
  ring

theorem complexQuadraticPolarization_smul_right
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (hnonneg : ∀ x, 0 ≤ q x) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, q x ≤ C * ‖x‖ ^ 2) (c : ℂ) (x y : V) :
    complexQuadraticPolarization q x (c • y) =
      c * complexQuadraticPolarization q x y := by
  have hcy : c • y = c.re • y + c.im • (Complex.I • y) := by
    conv_lhs => rw [← Complex.re_add_im c]
    module
  rw [hcy, complexQuadraticPolarization_add_right q hsmul hpar,
    complexQuadraticPolarization_real_smul_right q hsmul hpar hnonneg C hC hbound,
    complexQuadraticPolarization_real_smul_right q hsmul hpar hnonneg C hC hbound,
    complexQuadraticPolarization_I_smul_right q hsmul hpar hnonneg C hC hbound]
  conv_rhs => rw [← Complex.re_add_im c]
  ring

theorem complexQuadraticPolarization_conj_symm
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (x y : V) :
    complexQuadraticPolarization q y x =
      star (complexQuadraticPolarization q x y) := by
  have hcross : realQuadraticPolarization q y (Complex.I • x) =
      -realQuadraticPolarization q x (Complex.I • y) := by
    rw [realQuadraticPolarization_symm q hsmul,
      realQuadraticPolarization_I_left q hsmul hpar]
  unfold complexQuadraticPolarization
  rw [realQuadraticPolarization_symm q hsmul y x, hcross]
  apply Complex.ext <;> simp

@[simp]
theorem complexQuadraticPolarization_self
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (x : V) :
    complexQuadraticPolarization q x x = q x := by
  have hcross : realQuadraticPolarization q x (Complex.I • x) = 0 := by
    have h := realQuadraticPolarization_I_left q hsmul hpar x x
    rw [realQuadraticPolarization_symm q hsmul] at h
    linarith
  unfold complexQuadraticPolarization
  rw [realQuadraticPolarization_self q hsmul, hcross]
  simp

theorem complexQuadraticPolarization_zero_left
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (hnonneg : ∀ x, 0 ≤ q x) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, q x ≤ C * ‖x‖ ^ 2) (y : V) :
    complexQuadraticPolarization q 0 y = 0 := by
  have h := complexQuadraticPolarization_smul_left
    q hsmul hpar hnonneg C hC hbound (0 : ℂ) (0 : V) y
  simpa using h

theorem complexQuadraticPolarization_zero_right
    (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (hnonneg : ∀ x, 0 ≤ q x) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, q x ≤ C * ‖x‖ ^ 2) (x : V) :
    complexQuadraticPolarization q x 0 = 0 := by
  have h := complexQuadraticPolarization_smul_right
    q hsmul hpar hnonneg C hC hbound (0 : ℂ) x (0 : V)
  simpa using h

theorem complexQuadraticPolarization_sum_left
    {J : Type*} (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (hnonneg : ∀ x, 0 ≤ q x) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, q x ≤ C * ‖x‖ ^ 2)
    (s : Finset J) (f : J → V) (y : V) :
    complexQuadraticPolarization q (∑ j ∈ s, f j) y =
      ∑ j ∈ s, complexQuadraticPolarization q (f j) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [complexQuadraticPolarization_zero_left q hsmul hpar hnonneg C hC hbound]
  | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      rw [complexQuadraticPolarization_add_left q hsmul hpar, ih]

theorem complexQuadraticPolarization_sum_right
    {J : Type*} (q : V → ℝ)
    (hsmul : ∀ (c : ℂ) x, q (c • x) = Complex.normSq c * q x)
    (hpar : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (hnonneg : ∀ x, 0 ≤ q x) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, q x ≤ C * ‖x‖ ^ 2)
    (x : V) (s : Finset J) (f : J → V) :
    complexQuadraticPolarization q x (∑ j ∈ s, f j) =
      ∑ j ∈ s, complexQuadraticPolarization q x (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [complexQuadraticPolarization_zero_right q hsmul hpar hnonneg C hC hbound]
  | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      rw [complexQuadraticPolarization_add_right q hsmul hpar, ih]

end

end GaloisForLFunctions.HTGeometry
