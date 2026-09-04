import GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearDefect
import GaloisForLFunctions.HTGeometry.DiagonalEllTwoIndexed
import GaloisForLFunctions.HTGeometry.LikelihoodJuliaLift
import GaloisForLFunctions.HTGeometry.TraceClassQuantumCorner
import GaloisForLFunctions.HTGeometry.TanhSubstitution

/-!
# Prime--Hodge Poisson two-channel integral split

The literal prime--history trace-one source is polarized by the theta visibility and contrast
symbols.  Both marginals remain positive Schatten-one operators, while their traces add exactly
to the integral source charge.  The combined Kraus map is realized on the doubled Hilbert carrier
and is completely positive and trace preserving.

No divisor, zero, ordinate, or RH hypothesis occurs in any definition or theorem below.
-/

open scoped InnerProductSpace BigOperators

namespace RHTower

open ContinuousLinearMap

noncomputable section

/-- Prime rapidity at horizontal grade `a`. -/
def primeHodgeRapidity (a : ℝ) (p : Nat.Primes) : ℝ :=
  a * Real.log (p : ℝ) / 2

/-- Theta visibility amplitude `sech(a log(p)/2)`. -/
def primeHodgeVisibility (a : ℝ) (p : Nat.Primes) : ℝ :=
  1 / Real.cosh (primeHodgeRapidity a p)

/-- Signed theta contrast amplitude `tanh(a log(p)/2)`. -/
def primeHodgeContrast (a : ℝ) (p : Nat.Primes) : ℝ :=
  Real.tanh (primeHodgeRapidity a p)

theorem primeHodgeVisibility_pos (a : ℝ) (p : Nat.Primes) :
    0 < primeHodgeVisibility a p := by
  rw [primeHodgeVisibility]
  exact one_div_pos.mpr (Real.cosh_pos _)

theorem primeHodgeVisibility_le_one (a : ℝ) (p : Nat.Primes) :
    primeHodgeVisibility a p ≤ 1 := by
  rw [primeHodgeVisibility, div_le_one (Real.cosh_pos _)]
  exact Real.one_le_cosh _

theorem abs_primeHodgeContrast_lt_one (a : ℝ) (p : Nat.Primes) :
    |primeHodgeContrast a p| < 1 := by
  rw [abs_lt]
  exact ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩

theorem primeHodgeVisibility_sq_add_contrast_sq (a : ℝ) (p : Nat.Primes) :
    primeHodgeVisibility a p ^ 2 + primeHodgeContrast a p ^ 2 = 1 := by
  have h := HTGeometry.one_sub_tanh_sq (primeHodgeRapidity a p)
  rw [primeHodgeVisibility, primeHodgeContrast]
  calc
    (1 / Real.cosh (primeHodgeRapidity a p)) ^ 2 +
          Real.tanh (primeHodgeRapidity a p) ^ 2 =
        1 / Real.cosh (primeHodgeRapidity a p) ^ 2 +
          Real.tanh (primeHodgeRapidity a p) ^ 2 := by ring
    _ = (1 - Real.tanh (primeHodgeRapidity a p) ^ 2) +
          Real.tanh (primeHodgeRapidity a p) ^ 2 := by rw [h]
    _ = 1 := by ring

theorem primeHodgeRapidity_neg (a : ℝ) (p : Nat.Primes) :
    primeHodgeRapidity (-a) p = -primeHodgeRapidity a p := by
  rw [primeHodgeRapidity, primeHodgeRapidity]
  ring

theorem primeHodgeVisibility_neg (a : ℝ) (p : Nat.Primes) :
    primeHodgeVisibility (-a) p = primeHodgeVisibility a p := by
  rw [primeHodgeVisibility, primeHodgeVisibility, primeHodgeRapidity_neg, Real.cosh_neg]

theorem primeHodgeContrast_neg (a : ℝ) (p : Nat.Primes) :
    primeHodgeContrast (-a) p = -primeHodgeContrast a p := by
  rw [primeHodgeContrast, primeHodgeContrast, primeHodgeRapidity_neg, Real.tanh_neg]

theorem primeHodgeVisibility_zero (p : Nat.Primes) : primeHodgeVisibility 0 p = 1 := by
  simp [primeHodgeVisibility, primeHodgeRapidity]

theorem primeHodgeContrast_zero (p : Nat.Primes) : primeHodgeContrast 0 p = 0 := by
  simp [primeHodgeContrast, primeHodgeRapidity]

theorem primeHodgeRapidity_ne_zero {a : ℝ} (ha : a ≠ 0) (p : Nat.Primes) :
    primeHodgeRapidity a p ≠ 0 := by
  have hp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.property.one_lt)
  rw [primeHodgeRapidity]
  exact div_ne_zero (mul_ne_zero ha hp.ne') (by norm_num)

theorem primeHodgeContrast_ne_zero {a : ℝ} (ha : a ≠ 0) (p : Nat.Primes) :
    primeHodgeContrast a p ≠ 0 := by
  rw [primeHodgeContrast]
  intro h
  have ht : Real.tanh (primeHodgeRapidity a p) = Real.tanh 0 := by
    simpa using h
  exact primeHodgeRapidity_ne_zero ha p (HTGeometry.tanh_strictMono.injective ht)

theorem norm_primeHodgeVisibility_le_one (a : ℝ) (np : PrimeHodgeHistoryIndex) :
    ‖((primeHodgeVisibility a np.2 : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (primeHodgeVisibility_pos a np.2)]
  exact primeHodgeVisibility_le_one a np.2

theorem norm_primeHodgeContrast_le_one (a : ℝ) (np : PrimeHodgeHistoryIndex) :
    ‖((primeHodgeContrast a np.2 : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (abs_primeHodgeContrast_lt_one a np.2).le

/-- Visibility multiplier on the literal history--prime carrier. -/
def primeHodgeVisibilityOp (a : ℝ) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  HTGeometry.ellTwoDiagonal
    (fun np : PrimeHodgeHistoryIndex => (primeHodgeVisibility a np.2 : ℂ))
    (norm_primeHodgeVisibility_le_one a)

/-- Signed contrast multiplier on the literal history--prime carrier. -/
def primeHodgeContrastOp (a : ℝ) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  HTGeometry.ellTwoDiagonal
    (fun np : PrimeHodgeHistoryIndex => (primeHodgeContrast a np.2 : ℂ))
    (norm_primeHodgeContrast_le_one a)

@[simp] theorem primeHodgeVisibilityOp_apply (a : ℝ) (f : PrimeHodgeHistoryHilbert)
    (np : PrimeHodgeHistoryIndex) :
    primeHodgeVisibilityOp a f np = (primeHodgeVisibility a np.2 : ℂ) * f np := by
  rw [primeHodgeVisibilityOp, HTGeometry.ellTwoDiagonal_apply]

@[simp] theorem primeHodgeContrastOp_apply (a : ℝ) (f : PrimeHodgeHistoryHilbert)
    (np : PrimeHodgeHistoryIndex) :
    primeHodgeContrastOp a f np = (primeHodgeContrast a np.2 : ℂ) * f np := by
  rw [primeHodgeContrastOp, HTGeometry.ellTwoDiagonal_apply]

theorem primeHodgeVisibilityOp_isSelfAdjoint (a : ℝ) :
    IsSelfAdjoint (primeHodgeVisibilityOp a) := by
  change ContinuousLinearMap.adjoint (primeHodgeVisibilityOp a) =
    primeHodgeVisibilityOp a
  rw [primeHodgeVisibilityOp, HTGeometry.adjoint_ellTwoDiagonal]
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext np
  simp [HTGeometry.ellTwoDiagonal_apply]

theorem primeHodgeContrastOp_isSelfAdjoint (a : ℝ) :
    IsSelfAdjoint (primeHodgeContrastOp a) := by
  change ContinuousLinearMap.adjoint (primeHodgeContrastOp a) =
    primeHodgeContrastOp a
  rw [primeHodgeContrastOp, HTGeometry.adjoint_ellTwoDiagonal]
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext np
  simp [HTGeometry.ellTwoDiagonal_apply]

theorem adjoint_primeHodgeVisibilityOp (a : ℝ) :
    ContinuousLinearMap.adjoint (primeHodgeVisibilityOp a) = primeHodgeVisibilityOp a :=
  primeHodgeVisibilityOp_isSelfAdjoint a

theorem adjoint_primeHodgeContrastOp (a : ℝ) :
    ContinuousLinearMap.adjoint (primeHodgeContrastOp a) = primeHodgeContrastOp a :=
  primeHodgeContrastOp_isSelfAdjoint a

/-- Operator Pythagorean identity `V_a^2 + C_a^2 = I`. -/
theorem primeHodgeVisibilityOp_sq_add_contrastOp_sq (a : ℝ) :
    primeHodgeVisibilityOp a ∘L primeHodgeVisibilityOp a +
        primeHodgeContrastOp a ∘L primeHodgeContrastOp a =
      ContinuousLinearMap.id ℂ PrimeHodgeHistoryHilbert := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext np
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    primeHodgeVisibilityOp_apply, primeHodgeContrastOp_apply,
    ContinuousLinearMap.id_apply, lp.coeFn_add, Pi.add_apply]
  rw [show (primeHodgeVisibility a np.2 : ℂ) *
        ((primeHodgeVisibility a np.2 : ℂ) * f np) +
      (primeHodgeContrast a np.2 : ℂ) *
        ((primeHodgeContrast a np.2 : ℂ) * f np) =
      (((primeHodgeVisibility a np.2 ^ 2 + primeHodgeContrast a np.2 ^ 2 : ℝ) : ℂ)) *
        f np by push_cast; ring,
    primeHodgeVisibility_sq_add_contrast_sq, Complex.ofReal_one, one_mul]

theorem primeHodgeVisibilityOp_contrastOp_comm (a : ℝ) :
    primeHodgeVisibilityOp a ∘L primeHodgeContrastOp a =
      primeHodgeContrastOp a ∘L primeHodgeVisibilityOp a := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext np
  simp only [ContinuousLinearMap.comp_apply, primeHodgeVisibilityOp_apply,
    primeHodgeContrastOp_apply]
  ring

theorem primeHodgeVisibilityOp_zero :
    primeHodgeVisibilityOp 0 = ContinuousLinearMap.id ℂ PrimeHodgeHistoryHilbert := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext np
  simp [primeHodgeVisibilityOp_apply, primeHodgeVisibility_zero]

theorem primeHodgeContrastOp_zero :
    primeHodgeContrastOp 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext np
  simp [primeHodgeContrastOp_apply, primeHodgeContrast_zero]

theorem primeHodgeVisibilityOp_neg (a : ℝ) :
    primeHodgeVisibilityOp (-a) = primeHodgeVisibilityOp a := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext np
  rw [primeHodgeVisibilityOp_apply, primeHodgeVisibilityOp_apply,
    primeHodgeVisibility_neg]

theorem primeHodgeContrastOp_neg (a : ℝ) :
    primeHodgeContrastOp (-a) = -primeHodgeContrastOp a := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext np
  simp only [primeHodgeContrastOp_apply, ContinuousLinearMap.neg_apply, lp.coeFn_neg,
    Pi.neg_apply]
  rw [primeHodgeContrast_neg]
  push_cast
  ring

/-- Visible positive trace-class marginal. -/
def primeHodgeVisibleMarginal (a : ℝ) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  (primeHodgeVisibilityOp a ∘L primeHodgeHistoryIntegralNuclearDefectT) ∘L
    ContinuousLinearMap.adjoint (primeHodgeVisibilityOp a)

/-- Contrast positive trace-class marginal. -/
def primeHodgeContrastMarginal (a : ℝ) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  (primeHodgeContrastOp a ∘L primeHodgeHistoryIntegralNuclearDefectT) ∘L
    ContinuousLinearMap.adjoint (primeHodgeContrastOp a)

theorem primeHodgeVisibleMarginal_memSchattenClass_one (a : ℝ) :
    MemSchattenClass 1 (primeHodgeVisibleMarginal a) := by
  exact GaloisForLFunctions.HTGeometry.memSchattenClass_one_sandwich
    (primeHodgeVisibilityOp a) primeHodgeHistoryIntegralNuclearDefect_closed.2.1

theorem primeHodgeContrastMarginal_memSchattenClass_one (a : ℝ) :
    MemSchattenClass 1 (primeHodgeContrastMarginal a) := by
  exact GaloisForLFunctions.HTGeometry.memSchattenClass_one_sandwich
    (primeHodgeContrastOp a) primeHodgeHistoryIntegralNuclearDefect_closed.2.1

theorem primeHodgeVisibleMarginal_isPositive (a : ℝ) :
    (primeHodgeVisibleMarginal a).IsPositive := by
  have hT : 0 ≤ primeHodgeHistoryIntegralNuclearDefectT := by
    rw [ContinuousLinearMap.le_def, sub_zero]
    exact primeHodgeHistoryIntegralNuclearDefect_closed.1
  have h := GaloisForLFunctions.HTGeometry.traceClassSandwich_nonneg
    (primeHodgeVisibilityOp a) primeHodgeHistoryIntegralNuclearDefectT hT
  rw [ContinuousLinearMap.le_def, sub_zero] at h
  exact h

theorem primeHodgeContrastMarginal_isPositive (a : ℝ) :
    (primeHodgeContrastMarginal a).IsPositive := by
  have hT : 0 ≤ primeHodgeHistoryIntegralNuclearDefectT := by
    rw [ContinuousLinearMap.le_def, sub_zero]
    exact primeHodgeHistoryIntegralNuclearDefect_closed.1
  have h := GaloisForLFunctions.HTGeometry.traceClassSandwich_nonneg
    (primeHodgeContrastOp a) primeHodgeHistoryIntegralNuclearDefectT hT
  rw [ContinuousLinearMap.le_def, sub_zero] at h
  exact h

/-- Exact conservation of the integral trace charge between visibility and contrast. -/
theorem opTrace_primeHodgeMarginals_add (a : ℝ) :
    ContinuousLinearMap.opTrace (primeHodgeVisibleMarginal a) +
      ContinuousLinearMap.opTrace (primeHodgeContrastMarginal a) = 1 := by
  let T := primeHodgeHistoryIntegralNuclearDefectT
  let V := primeHodgeVisibilityOp a
  let C := primeHodgeContrastOp a
  have hT : MemSchattenClass 1 T := primeHodgeHistoryIntegralNuclearDefect_closed.2.1
  have hTV : MemSchattenClass 1 (T ∘L (ContinuousLinearMap.adjoint V ∘L V)) :=
    memSchattenClass_one_comp_right hT _
  have hTC : MemSchattenClass 1 (T ∘L (ContinuousLinearMap.adjoint C ∘L C)) :=
    memSchattenClass_one_comp_right hT _
  rw [show primeHodgeVisibleMarginal a =
      (V ∘L T) ∘L ContinuousLinearMap.adjoint V by rfl,
    show primeHodgeContrastMarginal a = (C ∘L T) ∘L ContinuousLinearMap.adjoint C by rfl]
  rw [GaloisForLFunctions.HTGeometry.opTrace_sandwich V T hT,
    GaloisForLFunctions.HTGeometry.opTrace_sandwich C T hT]
  rw [← opTrace_add_of_memSchattenClass_one hTV hTC]
  have hsum : ContinuousLinearMap.adjoint V ∘L V +
      ContinuousLinearMap.adjoint C ∘L C =
      ContinuousLinearMap.id ℂ PrimeHodgeHistoryHilbert := by
    rw [adjoint_primeHodgeVisibilityOp, adjoint_primeHodgeContrastOp]
    exact primeHodgeVisibilityOp_sq_add_contrastOp_sq a
  have hop : T ∘L (ContinuousLinearMap.adjoint V ∘L V) +
      T ∘L (ContinuousLinearMap.adjoint C ∘L C) = T := by
    rw [← ContinuousLinearMap.comp_add, hsum]
    ext f
    rfl
  rw [hop]
  exact primeHodgeHistoryIntegralNuclearDefect_closed.2.2.1

@[simp] theorem primeHodgeVisibilityOp_lpBasis (a : ℝ) (np : PrimeHodgeHistoryIndex) :
    primeHodgeVisibilityOp a (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np) =
      (primeHodgeVisibility a np.2 : ℂ) •
        HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np := by
  exact HTGeometry.ellTwoDiagonal_coordinateBasis
    (fun kp : PrimeHodgeHistoryIndex => (primeHodgeVisibility a kp.2 : ℂ))
    (norm_primeHodgeVisibility_le_one a) np

@[simp] theorem primeHodgeContrastOp_lpBasis (a : ℝ) (np : PrimeHodgeHistoryIndex) :
    primeHodgeContrastOp a (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np) =
      (primeHodgeContrast a np.2 : ℂ) •
        HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np := by
  exact HTGeometry.ellTwoDiagonal_coordinateBasis
    (fun kp : PrimeHodgeHistoryIndex => (primeHodgeContrast a kp.2 : ℂ))
    (norm_primeHodgeContrast_le_one a) np

/-- Every matrix entry of the fixed unit-aperture source is its literal prime--history kernel. -/
theorem inner_lpBasis_primeHodgeHistoryIntegralNuclearDefectT
    (i j : PrimeHodgeHistoryIndex) :
    inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex i)
      (primeHodgeHistoryIntegralNuclearDefectT
        (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex j)) =
      primeHodgeHistoryDefectKernel 1 (i, j) := by
  change inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex i)
    (HilbertSchmidt.toOperator (primeHodgeHistoryDefectKernel_isHS zero_lt_one)
      (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex j)) = _
  rw [HilbertSchmidt.lpBasis_apply, HilbertSchmidt.lpBasis_apply,
    lp.inner_single_left]
  simp only [RCLike.inner_apply, map_one, mul_one]
  rw [HilbertSchmidt.toOperator_single]

/-- `(PTC.9)`: the visible marginal has the pointwise visibility-square diagonal. -/
theorem inner_lpBasis_primeHodgeVisibleMarginal (a : ℝ)
    (np : PrimeHodgeHistoryIndex) :
    inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np)
      (primeHodgeVisibleMarginal a
        (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np)) =
      ((primeHodgeHistoryDiagonalWeight 1 np * primeHodgeVisibility a np.2 ^ 2 : ℝ) : ℂ) := by
  let b := HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np
  let v : ℂ := (primeHodgeVisibility a np.2 : ℂ)
  have hVb : primeHodgeVisibilityOp a b = v • b :=
    primeHodgeVisibilityOp_lpBasis a np
  have hsymm : inner ℂ b (primeHodgeVisibilityOp a
      (primeHodgeHistoryIntegralNuclearDefectT b)) =
      inner ℂ (primeHodgeVisibilityOp a b)
        (primeHodgeHistoryIntegralNuclearDefectT b) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (primeHodgeVisibilityOp_isSelfAdjoint a) b
      (primeHodgeHistoryIntegralNuclearDefectT b)).symm
  rw [primeHodgeVisibleMarginal, adjoint_primeHodgeVisibilityOp]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hVb, map_smul, map_smul, inner_smul_right, hsymm, hVb,
    inner_smul_left, inner_lpBasis_primeHodgeHistoryIntegralNuclearDefectT]
  rw [primeHodgeHistoryDefectKernel_diagonal zero_lt_one]
  simp [v]
  push_cast
  ring

/-- `(PTC.9)`: the contrast marginal has the pointwise contrast-square diagonal. -/
theorem inner_lpBasis_primeHodgeContrastMarginal (a : ℝ)
    (np : PrimeHodgeHistoryIndex) :
    inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np)
      (primeHodgeContrastMarginal a
        (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np)) =
      ((primeHodgeHistoryDiagonalWeight 1 np * primeHodgeContrast a np.2 ^ 2 : ℝ) : ℂ) := by
  let b := HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np
  let c : ℂ := (primeHodgeContrast a np.2 : ℂ)
  have hCb : primeHodgeContrastOp a b = c • b :=
    primeHodgeContrastOp_lpBasis a np
  have hsymm : inner ℂ b (primeHodgeContrastOp a
      (primeHodgeHistoryIntegralNuclearDefectT b)) =
      inner ℂ (primeHodgeContrastOp a b)
        (primeHodgeHistoryIntegralNuclearDefectT b) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (primeHodgeContrastOp_isSelfAdjoint a) b
      (primeHodgeHistoryIntegralNuclearDefectT b)).symm
  rw [primeHodgeContrastMarginal, adjoint_primeHodgeContrastOp]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hCb, map_smul, map_smul, inner_smul_right, hsymm, hCb,
    inner_smul_left, inner_lpBasis_primeHodgeHistoryIntegralNuclearDefectT]
  rw [primeHodgeHistoryDefectKernel_diagonal zero_lt_one]
  simp [c]
  push_cast
  ring

/-- Exact visible trace-series formula in `(PTC.9)`. -/
theorem opTrace_primeHodgeVisibleMarginal_eq_tsum (a : ℝ) :
    ContinuousLinearMap.opTrace (primeHodgeVisibleMarginal a) =
      ∑' np : PrimeHodgeHistoryIndex,
        ((primeHodgeHistoryDiagonalWeight 1 np * primeHodgeVisibility a np.2 ^ 2 : ℝ) : ℂ) := by
  rw [opTrace_eq_tsum_basis_of_memSchattenClass_one
    (primeHodgeVisibleMarginal_memSchattenClass_one a)
    (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex)]
  exact tsum_congr (inner_lpBasis_primeHodgeVisibleMarginal a)

/-- Exact contrast trace-series formula in `(PTC.9)`. -/
theorem opTrace_primeHodgeContrastMarginal_eq_tsum (a : ℝ) :
    ContinuousLinearMap.opTrace (primeHodgeContrastMarginal a) =
      ∑' np : PrimeHodgeHistoryIndex,
        ((primeHodgeHistoryDiagonalWeight 1 np * primeHodgeContrast a np.2 ^ 2 : ℝ) : ℂ) := by
  rw [opTrace_eq_tsum_basis_of_memSchattenClass_one
    (primeHodgeContrastMarginal_memSchattenClass_one a)
    (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex)]
  exact tsum_congr (inner_lpBasis_primeHodgeContrastMarginal a)

/-- Real visible charge. -/
def primeHodgeVisibleCharge (a : ℝ) : ℝ :=
  (ContinuousLinearMap.opTrace (primeHodgeVisibleMarginal a)).re

/-- Real contrast charge. -/
def primeHodgeContrastCharge (a : ℝ) : ℝ :=
  (ContinuousLinearMap.opTrace (primeHodgeContrastMarginal a)).re

theorem primeHodgeVisibleMarginal_ne_zero (a : ℝ) :
    primeHodgeVisibleMarginal a ≠ 0 := by
  intro hzero
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  let np : PrimeHodgeHistoryIndex := (0, p)
  have hdiag := inner_lpBasis_primeHodgeVisibleMarginal a np
  rw [hzero] at hdiag
  simp only [ContinuousLinearMap.zero_apply, inner_zero_right] at hdiag
  have hweight : primeHodgeHistoryDiagonalWeight 1 np ≠ 0 :=
    (primeHodgeHistoryDiagonalWeight_pos zero_lt_one np).ne'
  have hvis : primeHodgeVisibility a np.2 ^ 2 ≠ 0 :=
    pow_ne_zero 2 (primeHodgeVisibility_pos a np.2).ne'
  exact Complex.ofReal_ne_zero.mpr (mul_ne_zero hweight hvis) hdiag.symm

theorem primeHodgeContrastMarginal_ne_zero {a : ℝ} (ha : a ≠ 0) :
    primeHodgeContrastMarginal a ≠ 0 := by
  intro hzero
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  let np : PrimeHodgeHistoryIndex := (0, p)
  have hdiag := inner_lpBasis_primeHodgeContrastMarginal a np
  rw [hzero] at hdiag
  simp only [ContinuousLinearMap.zero_apply, inner_zero_right] at hdiag
  have hweight : primeHodgeHistoryDiagonalWeight 1 np ≠ 0 :=
    (primeHodgeHistoryDiagonalWeight_pos zero_lt_one np).ne'
  have hcon : primeHodgeContrast a np.2 ^ 2 ≠ 0 :=
    pow_ne_zero 2 (primeHodgeContrast_ne_zero ha np.2)
  exact Complex.ofReal_ne_zero.mpr (mul_ne_zero hweight hcon) hdiag.symm

theorem primeHodgeVisibleCharge_pos (a : ℝ) : 0 < primeHodgeVisibleCharge a := by
  rw [primeHodgeVisibleCharge,
    ← traceNorm_eq_re_opTrace_of_isPositive
      (primeHodgeVisibleMarginal_memSchattenClass_one a)
      (primeHodgeVisibleMarginal_isPositive a)]
  have hn : traceNorm PrimeHodgeHistoryHilbert (primeHodgeVisibleMarginal a) ≠ 0 := by
    intro hzero
    exact primeHodgeVisibleMarginal_ne_zero a
      ((traceNorm_eq_zero_iff
        (primeHodgeVisibleMarginal_memSchattenClass_one a).one_summable_approxNumber).mp hzero)
  exact lt_of_le_of_ne (traceNorm_nonneg _) hn.symm

theorem primeHodgeContrastCharge_pos {a : ℝ} (ha : a ≠ 0) :
    0 < primeHodgeContrastCharge a := by
  rw [primeHodgeContrastCharge,
    ← traceNorm_eq_re_opTrace_of_isPositive
      (primeHodgeContrastMarginal_memSchattenClass_one a)
      (primeHodgeContrastMarginal_isPositive a)]
  have hn : traceNorm PrimeHodgeHistoryHilbert (primeHodgeContrastMarginal a) ≠ 0 := by
    intro hzero
    exact primeHodgeContrastMarginal_ne_zero ha
      ((traceNorm_eq_zero_iff
        (primeHodgeContrastMarginal_memSchattenClass_one a).one_summable_approxNumber).mp hzero)
  exact lt_of_le_of_ne (traceNorm_nonneg _) hn.symm

theorem primeHodgeVisibleCharge_add_contrastCharge (a : ℝ) :
    primeHodgeVisibleCharge a + primeHodgeContrastCharge a = 1 := by
  have h := congrArg Complex.re (opTrace_primeHodgeMarginals_add a)
  simpa [primeHodgeVisibleCharge, primeHodgeContrastCharge] using h

theorem primeHodgeVisibleCharge_lt_one {a : ℝ} (ha : a ≠ 0) :
    primeHodgeVisibleCharge a < 1 := by
  nlinarith [primeHodgeContrastCharge_pos ha,
    primeHodgeVisibleCharge_add_contrastCharge a]

theorem primeHodgeContrastCharge_lt_one {a : ℝ} (ha : a ≠ 0) :
    primeHodgeContrastCharge a < 1 := by
  nlinarith [primeHodgeVisibleCharge_pos a,
    primeHodgeVisibleCharge_add_contrastCharge a]

theorem primeHodgeVisibleMarginal_zero :
    primeHodgeVisibleMarginal 0 = primeHodgeHistoryIntegralNuclearDefectT := by
  rw [primeHodgeVisibleMarginal, primeHodgeVisibilityOp_zero]
  ext f
  simp

theorem primeHodgeContrastMarginal_zero : primeHodgeContrastMarginal 0 = 0 := by
  rw [primeHodgeContrastMarginal, primeHodgeContrastOp_zero]
  ext f
  simp

theorem primeHodgeVisibleCharge_zero : primeHodgeVisibleCharge 0 = 1 := by
  rw [primeHodgeVisibleCharge, primeHodgeVisibleMarginal_zero,
    primeHodgeHistoryIntegralNuclearDefect_closed.2.2.1]
  rfl

theorem primeHodgeContrastCharge_zero : primeHodgeContrastCharge 0 = 0 := by
  rw [primeHodgeContrastCharge, primeHodgeContrastMarginal_zero]
  simp

theorem primeHodgeVisibleMarginal_neg (a : ℝ) :
    primeHodgeVisibleMarginal (-a) = primeHodgeVisibleMarginal a := by
  rw [primeHodgeVisibleMarginal, primeHodgeVisibleMarginal,
    primeHodgeVisibilityOp_neg]

theorem primeHodgeContrastMarginal_neg (a : ℝ) :
    primeHodgeContrastMarginal (-a) = primeHodgeContrastMarginal a := by
  rw [primeHodgeContrastMarginal, primeHodgeContrastMarginal,
    primeHodgeContrastOp_neg]
  ext f
  simp [ContinuousLinearMap.comp_apply]

theorem primeHodgeVisibleCharge_neg (a : ℝ) :
    primeHodgeVisibleCharge (-a) = primeHodgeVisibleCharge a := by
  rw [primeHodgeVisibleCharge, primeHodgeVisibleCharge, primeHodgeVisibleMarginal_neg]

theorem primeHodgeContrastCharge_neg (a : ℝ) :
    primeHodgeContrastCharge (-a) = primeHodgeContrastCharge a := by
  rw [primeHodgeContrastCharge, primeHodgeContrastCharge, primeHodgeContrastMarginal_neg]

/-- Every visible same-history cross-prime entry survives. -/
theorem inner_lpBasis_primeHodgeVisibleMarginal_sameHistory_ne_zero
    (a : ℝ) (n : ℕ) (p q : Nat.Primes) :
    inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
      (primeHodgeVisibleMarginal a
        (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, q))) ≠ 0 := by
  let bp := HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p)
  let bq := HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, q)
  have hVp := primeHodgeVisibilityOp_lpBasis a (n, p)
  have hVq := primeHodgeVisibilityOp_lpBasis a (n, q)
  have hsymm : inner ℂ bp (primeHodgeVisibilityOp a
      (primeHodgeHistoryIntegralNuclearDefectT bq)) =
      inner ℂ (primeHodgeVisibilityOp a bp)
        (primeHodgeHistoryIntegralNuclearDefectT bq) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (primeHodgeVisibilityOp_isSelfAdjoint a) bp
      (primeHodgeHistoryIntegralNuclearDefectT bq)).symm
  rw [primeHodgeVisibleMarginal, adjoint_primeHodgeVisibilityOp]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hVq, map_smul, map_smul, inner_smul_right, hsymm, hVp,
    inner_smul_left, inner_lpBasis_primeHodgeHistoryIntegralNuclearDefectT]
  apply mul_ne_zero
  · simpa using Complex.ofReal_ne_zero.mpr (primeHodgeVisibility_pos a q).ne'
  apply mul_ne_zero
  · simpa using Complex.ofReal_ne_zero.mpr (primeHodgeVisibility_pos a p).ne'
  · exact primeHodgeHistoryDefectKernel_sameHistory_ne_zero zero_lt_one n p q

/-- For nonzero grade every contrast same-history cross-prime entry survives. -/
theorem inner_lpBasis_primeHodgeContrastMarginal_sameHistory_ne_zero
    {a : ℝ} (ha : a ≠ 0) (n : ℕ) (p q : Nat.Primes) :
    inner ℂ (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p))
      (primeHodgeContrastMarginal a
        (HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, q))) ≠ 0 := by
  let bp := HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, p)
  let bq := HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex (n, q)
  have hCp := primeHodgeContrastOp_lpBasis a (n, p)
  have hCq := primeHodgeContrastOp_lpBasis a (n, q)
  have hsymm : inner ℂ bp (primeHodgeContrastOp a
      (primeHodgeHistoryIntegralNuclearDefectT bq)) =
      inner ℂ (primeHodgeContrastOp a bp)
        (primeHodgeHistoryIntegralNuclearDefectT bq) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (primeHodgeContrastOp_isSelfAdjoint a) bp
      (primeHodgeHistoryIntegralNuclearDefectT bq)).symm
  rw [primeHodgeContrastMarginal, adjoint_primeHodgeContrastOp]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hCq, map_smul, map_smul, inner_smul_right, hsymm, hCp,
    inner_smul_left, inner_lpBasis_primeHodgeHistoryIntegralNuclearDefectT]
  apply mul_ne_zero
  · simpa using Complex.ofReal_ne_zero.mpr (primeHodgeContrast_ne_zero ha q)
  apply mul_ne_zero
  · simpa using Complex.ofReal_ne_zero.mpr (primeHodgeContrast_ne_zero ha p)
  · exact primeHodgeHistoryDefectKernel_sameHistory_ne_zero zero_lt_one n p q

/-- Doubled-carrier Kraus isometry `x |-> (V_a x,C_a x)`. -/
def primeHodgeSplitDilation (a : ℝ) :
    PrimeHodgeHistoryHilbert →L[ℂ]
      WithLp 2 (PrimeHodgeHistoryHilbert × PrimeHodgeHistoryHilbert) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ PrimeHodgeHistoryHilbert
      PrimeHodgeHistoryHilbert).symm.toContinuousLinearMap ∘L
    ((primeHodgeVisibilityOp a).prod (primeHodgeContrastOp a))

@[simp] theorem primeHodgeSplitDilation_fst (a : ℝ) (f : PrimeHodgeHistoryHilbert) :
    (primeHodgeSplitDilation a f).fst = primeHodgeVisibilityOp a f := rfl

@[simp] theorem primeHodgeSplitDilation_snd (a : ℝ) (f : PrimeHodgeHistoryHilbert) :
    (primeHodgeSplitDilation a f).snd = primeHodgeContrastOp a f := rfl

theorem norm_primeHodgeSplitDilation (a : ℝ) (f : PrimeHodgeHistoryHilbert) :
    ‖primeHodgeSplitDilation a f‖ = ‖f‖ := by
  have hv := primeHodgeVisibilityOp_isSelfAdjoint a
  have hc := primeHodgeContrastOp_isSelfAdjoint a
  apply GaloisForLFunctions.HTGeometry.norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _)
  rw [WithLp.prod_norm_sq_eq_of_L2, primeHodgeSplitDilation_fst,
    primeHodgeSplitDilation_snd]
  have h1 : inner ℂ (primeHodgeVisibilityOp a f) (primeHodgeVisibilityOp a f) =
      inner ℂ f (primeHodgeVisibilityOp a (primeHodgeVisibilityOp a f)) := by
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hv f
      (primeHodgeVisibilityOp a f))
  have h2 : inner ℂ (primeHodgeContrastOp a f) (primeHodgeContrastOp a f) =
      inner ℂ f (primeHodgeContrastOp a (primeHodgeContrastOp a f)) := by
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hc f
      (primeHodgeContrastOp a f))
  have hsum := congrArg (fun A : PrimeHodgeHistoryHilbert →L[ℂ]
      PrimeHodgeHistoryHilbert => A f) (primeHodgeVisibilityOp_sq_add_contrastOp_sq a)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hsum
  have hinner : inner ℂ (primeHodgeVisibilityOp a f) (primeHodgeVisibilityOp a f) +
      inner ℂ (primeHodgeContrastOp a f) (primeHodgeContrastOp a f) = inner ℂ f f := by
    rw [h1, h2, ← inner_add_right, hsum]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K] at hinner
  exact_mod_cast hinner

theorem adjoint_primeHodgeSplitDilation_comp_self (a : ℝ) :
    ContinuousLinearMap.adjoint (primeHodgeSplitDilation a) ∘L
      primeHodgeSplitDilation a =
      ContinuousLinearMap.id ℂ PrimeHodgeHistoryHilbert := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro g
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
  have hprod : inner ℂ (primeHodgeSplitDilation a f) (primeHodgeSplitDilation a g) =
      inner ℂ (primeHodgeVisibilityOp a f) (primeHodgeVisibilityOp a g) +
        inner ℂ (primeHodgeContrastOp a f) (primeHodgeContrastOp a g) :=
    WithLp.prod_inner_apply _ _
  rw [hprod]
  have h1 : inner ℂ (primeHodgeVisibilityOp a f) (primeHodgeVisibilityOp a g) =
      inner ℂ f (primeHodgeVisibilityOp a (primeHodgeVisibilityOp a g)) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (primeHodgeVisibilityOp_isSelfAdjoint a) f (primeHodgeVisibilityOp a g)
  have h2 : inner ℂ (primeHodgeContrastOp a f) (primeHodgeContrastOp a g) =
      inner ℂ f (primeHodgeContrastOp a (primeHodgeContrastOp a g)) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (primeHodgeContrastOp_isSelfAdjoint a) f (primeHodgeContrastOp a g)
  rw [h1, h2, ← inner_add_right]
  have hsum := congrArg (fun A : PrimeHodgeHistoryHilbert →L[ℂ]
      PrimeHodgeHistoryHilbert => A g) (primeHodgeVisibilityOp_sq_add_contrastOp_sq a)
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using congrArg (fun x => inner ℂ f x) hsum

/-- Literal two-Kraus trace-class instrument on the doubled carrier. -/
def primeHodgeTwoChannelInstrument (a : ℝ) :=
  GaloisForLFunctions.HTGeometry.traceClassSandwich (primeHodgeSplitDilation a)

theorem primeHodgeTwoChannelInstrument_completelyPositive (a : ℝ) :
    GaloisForLFunctions.HTGeometry.IsCompletelyPositive
      (GaloisForLFunctions.HTGeometry.traceClassMatrixCone PrimeHodgeHistoryHilbert)
      (GaloisForLFunctions.HTGeometry.traceClassMatrixCone
        (WithLp 2 (PrimeHodgeHistoryHilbert × PrimeHodgeHistoryHilbert)))
      (primeHodgeTwoChannelInstrument a) :=
  GaloisForLFunctions.HTGeometry.traceClassSandwich_completelyPositive _

theorem primeHodgeTwoChannelInstrument_tracePreserving (a : ℝ) :
    ∀ ρ, GaloisForLFunctions.HTGeometry.traceClassPositive ρ →
      GaloisForLFunctions.HTGeometry.traceClassTrace
          (primeHodgeTwoChannelInstrument a ρ) =
        GaloisForLFunctions.HTGeometry.traceClassTrace ρ :=
  GaloisForLFunctions.HTGeometry.traceClassSandwich_tracePreserving
    (primeHodgeSplitDilation a) (adjoint_primeHodgeSplitDilation_comp_self a)

/-- Closed capstone: the concrete prime--Hodge source admits a lossless two-channel split. -/
theorem primeHodgePoissonTwoChannelIntegralSplit_closed :
    ∀ a : ℝ,
      (primeHodgeVisibleMarginal a).IsPositive ∧
      MemSchattenClass 1 (primeHodgeVisibleMarginal a) ∧
      (primeHodgeContrastMarginal a).IsPositive ∧
      MemSchattenClass 1 (primeHodgeContrastMarginal a) ∧
      ContinuousLinearMap.opTrace (primeHodgeVisibleMarginal a) +
          ContinuousLinearMap.opTrace (primeHodgeContrastMarginal a) = 1 ∧
      GaloisForLFunctions.HTGeometry.IsCompletelyPositive
        (GaloisForLFunctions.HTGeometry.traceClassMatrixCone PrimeHodgeHistoryHilbert)
        (GaloisForLFunctions.HTGeometry.traceClassMatrixCone
          (WithLp 2 (PrimeHodgeHistoryHilbert × PrimeHodgeHistoryHilbert)))
        (primeHodgeTwoChannelInstrument a) := by
  intro a
  exact ⟨primeHodgeVisibleMarginal_isPositive a,
    primeHodgeVisibleMarginal_memSchattenClass_one a,
    primeHodgeContrastMarginal_isPositive a,
    primeHodgeContrastMarginal_memSchattenClass_one a,
    opTrace_primeHodgeMarginals_add a,
    primeHodgeTwoChannelInstrument_completelyPositive a⟩

end
end RHTower
