import GaloisForLFunctions.RHTower.XiRationalHurwitzDyadicRefinement

/-!
# The reflected rational-Hurwitz seam is a Lorentz boost

After removing the common phase and the critical normalization, the two inverse reflected
rational-Hurwitz responses at modulus `n` are the light-cone coordinates of the boost of rapidity
`(Re ρ − 1/2)·log n`.  The boost matrix

```text
B(u) = [[cosh u, sinh u], [sinh u, cosh u]]
```

preserves the Krein form `diag(1,−1)`, has determinant one, inverse `B(−u)`, and turns
multiplicative refinement of the modulus into the additive group law of `SO⁺(1,1)`.  Its
off-diagonal transfer squared is exactly the normalized seam energy, and its rapidity is the
inverse hyperbolic sine of the square root of that energy.

The colligation is conservative in the *indefinite* Krein metric for every horizontal
displacement, so functional-equation self-duality alone permits every off-line point.  What it
forbids is a *positive* metric: a boost and its inverse are simultaneously contractive for one
positive-definite form exactly when the rapidity vanishes, i.e. exactly on the critical line.
-/

namespace RHTower

open Matrix

noncomputable section

/-! ## The boost -/

/-- The Lorentz boost of rapidity `u` in even/odd coordinates. -/
def lorentzBoost (u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh u, Real.sinh u; Real.sinh u, Real.cosh u]

/-- The Krein form of signature `(1,1)`. -/
def kreinMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

@[simp] theorem lorentzBoost_zero : lorentzBoost 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lorentzBoost]

/-- **Krein conservation.** -/
theorem lorentzBoost_krein (u : ℝ) :
    (lorentzBoost u)ᵀ * kreinMatrix * lorentzBoost u = kreinMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzBoost, kreinMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [Real.cosh_sq_sub_sinh_sq u]

/-- **Unimodularity.** -/
theorem det_lorentzBoost (u : ℝ) : (lorentzBoost u).det = 1 := by
  rw [lorentzBoost, Matrix.det_fin_two_of]
  nlinarith [Real.cosh_sq_sub_sinh_sq u]

/-- **The rapidity is additive.** -/
theorem lorentzBoost_mul (u v : ℝ) :
    lorentzBoost u * lorentzBoost v = lorentzBoost (u + v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzBoost, Matrix.mul_apply, Fin.sum_univ_two, Real.cosh_add, Real.sinh_add] <;>
    ring

theorem lorentzBoost_mul_neg (u : ℝ) : lorentzBoost u * lorentzBoost (-u) = 1 := by
  rw [lorentzBoost_mul, add_neg_cancel, lorentzBoost_zero]

theorem lorentzBoost_neg_mul (u : ℝ) : lorentzBoost (-u) * lorentzBoost u = 1 := by
  rw [lorentzBoost_mul, neg_add_cancel, lorentzBoost_zero]

theorem lorentzBoost_pow (u : ℝ) : ∀ k : ℕ, (lorentzBoost u) ^ k = lorentzBoost (k * u)
  | 0 => by simp
  | (k + 1) => by
      rw [pow_succ, lorentzBoost_pow u k, lorentzBoost_mul]
      congr 1
      push_cast
      ring

/-! ## Light-cone eigenvectors -/

theorem lorentzBoost_mulVec_plus (u : ℝ) :
    (lorentzBoost u).mulVec ![1, 1] = Real.exp u • ![1, 1] := by
  funext i
  fin_cases i <;>
    simp [lorentzBoost, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Real.cosh_eq, Real.sinh_eq] <;>
    ring

theorem lorentzBoost_mulVec_minus (u : ℝ) :
    (lorentzBoost u).mulVec ![1, -1] = Real.exp (-u) • ![1, -1] := by
  funext i
  fin_cases i <;>
    simp [lorentzBoost, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Real.cosh_eq, Real.sinh_eq] <;>
    ring

/-- The light-cone change of basis. -/
def lightConeChart : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, -1]

theorem lorentzBoost_mulVec_e0 (u : ℝ) :
    (lorentzBoost u).mulVec ![1, 0] = ![Real.cosh u, Real.sinh u] := by
  funext i
  fin_cases i <;> simp [lorentzBoost, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **The light-cone coordinates of the reflected pair.**  The boost applied to the even generator
has light-cone components `exp (±u)`. -/
theorem lightConeChart_mulVec_boost (u : ℝ) :
    lightConeChart.mulVec ((lorentzBoost u).mulVec ![1, 0])
      = ![Real.exp u, Real.exp (-u)] := by
  rw [lorentzBoost_mulVec_e0]
  funext i
  fin_cases i <;>
    simp [lightConeChart, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Real.cosh_eq,
      Real.sinh_eq] <;>
    ring

/-! ## The seam boost -/

/-- The boost attached to a strip point and an integer modulus. -/
def hurwitzBoost (rho : ℂ) (n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  lorentzBoost ((rho.re - 1 / 2) * Real.log n)

theorem hurwitzBoost_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (rho : ℂ) :
    hurwitzBoost rho (m * n) = hurwitzBoost rho m * hurwitzBoost rho n := by
  rw [hurwitzBoost, hurwitzBoost, hurwitzBoost, lorentzBoost_mul]
  congr 1
  rw [Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hm) (Nat.cast_ne_zero.mpr hn)]
  ring

theorem hurwitzBoost_pow (n : ℕ) (rho : ℂ) (k : ℕ) :
    hurwitzBoost rho (n ^ k) = (hurwitzBoost rho n) ^ k := by
  rw [hurwitzBoost, hurwitzBoost, lorentzBoost_pow]
  congr 1
  rw [Nat.cast_pow, Real.log_pow]
  ring

/-- **Equation `(4)`.**  The light-cone components of the seam boost are the two inverse reflected
rational-Hurwitz responses after removal of their common scalar. -/
theorem hurwitzBoost_lightCone (rho : ℂ) {n : ℕ} (hn : n ≠ 0) :
    lightConeChart.mulVec ((hurwitzBoost rho n).mulVec ![1, 0])
      = ![(n : ℝ) ^ (rho.re - 1 / 2), (n : ℝ) ^ (-(rho.re - 1 / 2))] := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [hurwitzBoost, lightConeChart_mulVec_boost]
  funext i
  fin_cases i <;>
    simp [Real.rpow_def_of_pos hnpos] <;>
    ring_nf

/-- **The seam energy is the squared off-diagonal transfer of the boost.** -/
theorem normalizedScaleSeamEnergy_eq_boost_offDiagonal_sq (rho : ℂ) (n : ℕ) :
    normalizedScaleSeamEnergy n rho = (hurwitzBoost rho n 0 1) ^ 2 := by
  rw [normalizedScaleSeamEnergy_eq_sinh, hurwitzBoost, lorentzBoost]
  simp

/-- **The rapidity coordinate of the seam energy.** -/
theorem arsinh_sqrt_normalizedScaleSeamEnergy (rho : ℂ) (n : ℕ) :
    Real.arsinh (Real.sqrt (normalizedScaleSeamEnergy n rho))
      = |(rho.re - 1 / 2) * Real.log n| := by
  rw [normalizedScaleSeamEnergy_eq_sinh, Real.sqrt_sq_eq_abs]
  set x : ℝ := (rho.re - 1 / 2) * Real.log n with hx
  rcases le_or_gt 0 x with hpos | hneg
  · rw [abs_of_nonneg (Real.sinh_nonneg_iff.mpr hpos), Real.arsinh_sinh, abs_of_nonneg hpos]
  · rw [abs_of_neg (Real.sinh_neg_iff.mpr hneg), ← Real.sinh_neg, Real.arsinh_sinh,
      abs_of_neg hneg]

/-! ## Positive-metric rigidity -/

/-- The quadratic form of a symmetric matrix. -/
def metricForm (P : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) : ℝ := v ⬝ᵥ P.mulVec v

theorem metricForm_smul (P : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ) (v : Fin 2 → ℝ) :
    metricForm P (c • v) = c ^ 2 * metricForm P v := by
  simp only [metricForm, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- Positive definiteness of the metric. -/
def IsPositiveMetric (P : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ v : Fin 2 → ℝ, v ≠ 0 → 0 < metricForm P v

/-- Contractivity of a matrix in a metric. -/
def IsContractionIn (P B : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ v : Fin 2 → ℝ, metricForm P (B.mulVec v) ≤ metricForm P v

theorem lightConePlus_ne_zero : (![1, 1] : Fin 2 → ℝ) ≠ 0 := by
  intro hc
  have := congrFun hc 0
  simp at this

/-- **Positive-metric rigidity.**  A boost and its inverse are simultaneously contractive for one
positive-definite metric exactly when the rapidity vanishes. -/
theorem rapidity_eq_zero_of_contraction_pair {P : Matrix (Fin 2) (Fin 2) ℝ}
    (hP : IsPositiveMetric P) {u : ℝ}
    (h₁ : IsContractionIn P (lorentzBoost u)) (h₂ : IsContractionIn P (lorentzBoost (-u))) :
    u = 0 := by
  have hq : 0 < metricForm P ![1, 1] := hP _ lightConePlus_ne_zero
  have hc₁ := h₁ ![1, 1]
  have hc₂ := h₂ ![1, 1]
  rw [lorentzBoost_mulVec_plus, metricForm_smul] at hc₁
  rw [lorentzBoost_mulVec_plus, metricForm_smul] at hc₂
  have he₁ : Real.exp u ^ 2 ≤ 1 := by nlinarith
  have he₂ : Real.exp (-u) ^ 2 ≤ 1 := by nlinarith
  have hu₁ : u ≤ 0 := by
    by_contra hcon
    have hpos : 0 < u := not_le.mp hcon
    have hgt : (1 : ℝ) < Real.exp u := by
      calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ < Real.exp u := Real.exp_lt_exp.mpr hpos
    nlinarith
  have hu₂ : 0 ≤ u := by
    by_contra hcon
    have hneg : u < 0 := not_le.mp hcon
    have hgt : (1 : ℝ) < Real.exp (-u) := by
      calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ < Real.exp (-u) := Real.exp_lt_exp.mpr (by linarith)
    nlinarith
  linarith

/-- **The exact critical-line selector.**  For a modulus `n ≥ 2`, simultaneous contractivity of the
seam boost and its inverse in one positive metric is equivalent to `Re ρ = 1/2`. -/
theorem re_eq_half_of_contraction_pair {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : IsPositiveMetric P)
    {n : ℕ} (hn : 2 ≤ n) {rho : ℂ}
    (h₁ : IsContractionIn P (hurwitzBoost rho n))
    (h₂ : IsContractionIn P (lorentzBoost (-((rho.re - 1 / 2) * Real.log n)))) :
    rho.re = 1 / 2 := by
  have hu := rapidity_eq_zero_of_contraction_pair hP h₁ h₂
  have hlog : Real.log n ≠ 0 := by
    refine ne_of_gt (Real.log_pos ?_)
    exact_mod_cast lt_of_lt_of_le one_lt_two (by exact_mod_cast hn)
  rcases mul_eq_zero.mp hu with h | h
  · linarith
  · exact absurd h hlog

/-- **The critical line is exactly the identity boost.** -/
theorem hurwitzBoost_eq_one_iff {n : ℕ} (hn : 2 ≤ n) (rho : ℂ) :
    hurwitzBoost rho n = 1 ↔ rho.re = 1 / 2 := by
  have hlog : Real.log n ≠ 0 := by
    refine ne_of_gt (Real.log_pos ?_)
    exact_mod_cast lt_of_lt_of_le one_lt_two (by exact_mod_cast hn)
  constructor
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    simp [hurwitzBoost, lorentzBoost] at h01
    rcases h01 with hc | hc | hc | hc
    · linarith
    · omega
    · omega
    · exfalso
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
  · intro h
    rw [hurwitzBoost, h]
    simp

end

end RHTower
