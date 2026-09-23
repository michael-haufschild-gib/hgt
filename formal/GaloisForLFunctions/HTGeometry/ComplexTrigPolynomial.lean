import GaloisForLFunctions.RHTower.CosinePhaseParseval

/-!
# Complex trigonometric polynomials and the `L²` Bernstein inequality

A complex trigonometric polynomial of degree at most `D` is a finite combination of the exponential
monomials `e^{ikθ}` with `|k| ≤ D`.  In this description every operation the Cayley transport needs
is a clean index shift:

* multiplication by `e^{±iθ}` raises the degree by one and preserves the `L²` norm;
* differentiation preserves the degree and multiplies the `k`-th coefficient by `ik`.

Orthogonality of the monomials on the full period gives Parseval, and the frequency bound `|k| ≤ D`
then gives the `L²` Bernstein inequality `‖G'‖₂ ≤ D‖G‖₂`.
-/

open Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The exponential monomial of integer frequency. -/
def expMon (k : ℤ) (θ : ℝ) : ℂ := Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I)

theorem expMon_mul (j k : ℤ) (θ : ℝ) : expMon j θ * expMon k θ = expMon (j + k) θ := by
  rw [expMon, expMon, expMon, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_expMon (k : ℤ) (θ : ℝ) : ‖expMon k θ‖ = 1 := by
  rw [expMon, Complex.norm_exp]
  have hre : (((k : ℂ) * (θ : ℂ) * Complex.I)).re = 0 := by
    simp [Complex.mul_re]
  rw [hre, Real.exp_zero]

theorem conj_expMon (k : ℤ) (θ : ℝ) :
    (starRingEnd ℂ) (expMon k θ) = expMon (-k) θ := by
  rw [expMon, expMon, ← Complex.exp_conj]
  congr 1
  simp

theorem continuous_expMon (k : ℤ) : Continuous (expMon k) := by
  unfold expMon
  fun_prop

/-- The full-period integral of an exponential monomial. -/
theorem integral_expMon (k : ℤ) :
    (∫ θ in (-Real.pi)..Real.pi, expMon k θ) = if k = 0 then (2 * Real.pi : ℂ) else 0 := by
  have hsplit : ∀ θ : ℝ, expMon k θ
      = ((Real.cos ((k : ℝ) * θ) : ℝ) : ℂ) + ((Real.sin ((k : ℝ) * θ) : ℝ) : ℂ) * Complex.I := by
    intro θ
    rw [expMon, show ((k : ℂ) * (θ : ℂ) * Complex.I) = (((k : ℝ) * θ : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [intervalIntegral.integral_congr (g := fun θ : ℝ =>
    ((Real.cos ((k : ℝ) * θ) : ℝ) : ℂ) + ((Real.sin ((k : ℝ) * θ) : ℝ) : ℂ) * Complex.I)
    (fun θ _ => hsplit θ)]
  have hc : IntervalIntegrable (fun θ : ℝ => ((Real.cos ((k : ℝ) * θ) : ℝ) : ℂ))
      volume (-Real.pi) Real.pi :=
    (Complex.continuous_ofReal.comp
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hs : IntervalIntegrable
      (fun θ : ℝ => ((Real.sin ((k : ℝ) * θ) : ℝ) : ℂ) * Complex.I)
      volume (-Real.pi) Real.pi :=
    ((Complex.continuous_ofReal.comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).mul
      continuous_const).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hc hs, intervalIntegral.integral_mul_const]
  have hcr : (∫ θ in (-Real.pi)..Real.pi, ((Real.cos ((k : ℝ) * θ) : ℝ) : ℂ))
      = (((∫ θ in (-Real.pi)..Real.pi, Real.cos ((k : ℝ) * θ)) : ℝ) : ℂ) :=
    intervalIntegral.integral_ofReal
  have hsr : (∫ θ in (-Real.pi)..Real.pi, ((Real.sin ((k : ℝ) * θ) : ℝ) : ℂ))
      = (((∫ θ in (-Real.pi)..Real.pi, Real.sin ((k : ℝ) * θ)) : ℝ) : ℂ) :=
    intervalIntegral.integral_ofReal
  rw [hcr, hsr, RHTower.integral_cos_int_mul, RHTower.integral_sin_int_mul]
  rcases eq_or_ne k 0 with rfl | hk
  · rw [if_pos rfl, if_pos rfl]
    push_cast
    ring
  · rw [if_neg hk, if_neg hk]
    push_cast
    ring_nf

/-- **Orthogonality of the exponential monomials on the full period.** -/
theorem integral_expMon_mul_conj (j k : ℤ) :
    (∫ θ in (-Real.pi)..Real.pi, expMon j θ * (starRingEnd ℂ) (expMon k θ))
      = if j = k then (2 * Real.pi : ℂ) else 0 := by
  have hprod : ∀ θ : ℝ, expMon j θ * (starRingEnd ℂ) (expMon k θ) = expMon (j - k) θ := by
    intro θ
    rw [conj_expMon, expMon_mul, show j + -k = j - k by ring]
  rw [intervalIntegral.integral_congr (g := fun θ : ℝ => expMon (j - k) θ)
    (fun θ _ => hprod θ), integral_expMon]
  rcases eq_or_ne j k with rfl | hjk
  · rw [if_pos rfl, if_pos (by omega : j - j = 0)]
  · rw [if_neg hjk, if_neg (by omega : ¬ j - k = 0)]


/-! ## Trigonometric polynomials and Parseval -/

/-- The trigonometric polynomial with coefficient family `f` and degree bound `D`. -/
def trigExp (D : ℕ) (f : ℤ → ℂ) (θ : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(D : ℤ)) (D : ℤ), f k * expMon k θ

theorem continuous_trigExp (D : ℕ) (f : ℤ → ℂ) : Continuous (trigExp D f) := by
  unfold trigExp
  refine continuous_finsetSum _ fun k _ => ?_
  exact continuous_const.mul (continuous_expMon k)

/-- **Parseval for trigonometric polynomials.** -/
theorem integral_normSq_trigExp (D : ℕ) (f : ℤ → ℂ) :
    (∫ θ in (-Real.pi)..Real.pi, ‖trigExp D f θ‖ ^ (2 : ℕ))
      = 2 * Real.pi * ∑ k ∈ Finset.Icc (-(D : ℤ)) (D : ℤ), ‖f k‖ ^ (2 : ℕ) := by
  have hcast : ∀ θ : ℝ, ((‖trigExp D f θ‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = ∑ j ∈ Finset.Icc (-(D : ℤ)) (D : ℤ), ∑ k ∈ Finset.Icc (-(D : ℤ)) (D : ℤ),
        (f j * (starRingEnd ℂ) (f k)) * (expMon j θ * (starRingEnd ℂ) (expMon k θ)) := by
    intro θ
    have h1 : ((‖trigExp D f θ‖ ^ (2 : ℕ) : ℝ) : ℂ)
        = trigExp D f θ * (starRingEnd ℂ) (trigExp D f θ) := by
      rw [Complex.mul_conj]
      norm_cast
      rw [Complex.normSq_eq_norm_sq]
    rw [h1, trigExp, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    ring
  have hcastInt : (((∫ θ in (-Real.pi)..Real.pi, ‖trigExp D f θ‖ ^ (2 : ℕ) : ℝ)) : ℂ)
      = ∫ θ in (-Real.pi)..Real.pi, ((‖trigExp D f θ‖ ^ (2 : ℕ) : ℝ) : ℂ) :=
    intervalIntegral.integral_ofReal.symm
  have hgoal : (((∫ θ in (-Real.pi)..Real.pi, ‖trigExp D f θ‖ ^ (2 : ℕ) : ℝ)) : ℂ)
      = ((2 * Real.pi * ∑ k ∈ Finset.Icc (-(D : ℤ)) (D : ℤ), ‖f k‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [hcastInt, intervalIntegral.integral_congr (fun θ _ => hcast θ)]
    have hintj : ∀ j ∈ Finset.Icc (-(D : ℤ)) (D : ℤ), IntervalIntegrable
        (fun θ : ℝ => ∑ k ∈ Finset.Icc (-(D : ℤ)) (D : ℤ),
          (f j * (starRingEnd ℂ) (f k)) * (expMon j θ * (starRingEnd ℂ) (expMon k θ)))
        volume (-Real.pi) Real.pi := by
      intro j _
      refine Continuous.intervalIntegrable ?_ _ _
      refine continuous_finsetSum _ fun k _ => ?_
      exact continuous_const.mul ((continuous_expMon j).mul
        (Complex.continuous_conj.comp (continuous_expMon k)))
    rw [intervalIntegral.integral_finsetSum hintj]
    have hinner : ∀ j ∈ Finset.Icc (-(D : ℤ)) (D : ℤ),
        (∫ θ in (-Real.pi)..Real.pi, ∑ k ∈ Finset.Icc (-(D : ℤ)) (D : ℤ),
          (f j * (starRingEnd ℂ) (f k)) * (expMon j θ * (starRingEnd ℂ) (expMon k θ)))
          = (2 * Real.pi : ℂ) * ((‖f j‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      intro j hj
      have hintk : ∀ k ∈ Finset.Icc (-(D : ℤ)) (D : ℤ), IntervalIntegrable
          (fun θ : ℝ => (f j * (starRingEnd ℂ) (f k))
            * (expMon j θ * (starRingEnd ℂ) (expMon k θ))) volume (-Real.pi) Real.pi := by
        intro k _
        refine Continuous.intervalIntegrable ?_ _ _
        exact continuous_const.mul ((continuous_expMon j).mul
          (Complex.continuous_conj.comp (continuous_expMon k)))
      rw [intervalIntegral.integral_finsetSum hintk]
      have hterm : ∀ k ∈ Finset.Icc (-(D : ℤ)) (D : ℤ),
          (∫ θ in (-Real.pi)..Real.pi, (f j * (starRingEnd ℂ) (f k))
            * (expMon j θ * (starRingEnd ℂ) (expMon k θ)))
            = (f j * (starRingEnd ℂ) (f k)) * (if j = k then (2 * Real.pi : ℂ) else 0) := by
        intro k _
        rw [intervalIntegral.integral_const_mul, integral_expMon_mul_conj]
      rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single j]
      · rw [if_pos rfl, Complex.mul_conj]
        rw [show ((Complex.normSq (f j) : ℝ) : ℂ) = ((‖f j‖ ^ (2 : ℕ) : ℝ) : ℂ) by
          norm_cast
          rw [Complex.normSq_eq_norm_sq]]
        ring
      · intro k _ hkj
        rw [if_neg (fun h => hkj h.symm), mul_zero]
      · intro hjnot
        exact absurd hj hjnot
    rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
    push_cast
    ring
  exact_mod_cast hgoal

/-- The derivative of a trigonometric polynomial. -/
theorem hasDerivAt_trigExp (D : ℕ) (f : ℤ → ℂ) (θ : ℝ) :
    HasDerivAt (trigExp D f) (trigExp D (fun k => f k * ((k : ℂ) * Complex.I)) θ) θ := by
  unfold trigExp
  refine HasDerivAt.fun_sum fun k _ => ?_
  have hlin : HasDerivAt (fun u : ℝ => (k : ℂ) * (u : ℂ) * Complex.I) ((k : ℂ) * Complex.I) θ := by
    have h1 : HasDerivAt (fun u : ℝ => (u : ℂ)) (1 : ℂ) θ := Complex.ofRealCLM.hasDerivAt
    have h2 := (h1.const_mul ((k : ℂ))).mul_const Complex.I
    simpa using h2
  have hexp : HasDerivAt (fun u : ℝ => Complex.exp ((k : ℂ) * (u : ℂ) * Complex.I))
      (Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I) * ((k : ℂ) * Complex.I)) θ :=
    hlin.cexp
  have hres := hexp.const_mul (f k)
  refine hres.congr_deriv ?_
  rw [expMon]
  ring

/-- **The `L²` Bernstein inequality for trigonometric polynomials.** -/
theorem integral_normSq_trigExp_deriv_le (D : ℕ) (f : ℤ → ℂ) :
    (∫ θ in (-Real.pi)..Real.pi,
        ‖trigExp D (fun k => f k * ((k : ℂ) * Complex.I)) θ‖ ^ (2 : ℕ))
      ≤ (D : ℝ) ^ (2 : ℕ) * ∫ θ in (-Real.pi)..Real.pi, ‖trigExp D f θ‖ ^ (2 : ℕ) := by
  rw [integral_normSq_trigExp, integral_normSq_trigExp]
  have hterm : ∀ k ∈ Finset.Icc (-(D : ℤ)) (D : ℤ),
      ‖f k * ((k : ℂ) * Complex.I)‖ ^ (2 : ℕ) ≤ (D : ℝ) ^ (2 : ℕ) * ‖f k‖ ^ (2 : ℕ) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have habs : |(k : ℝ)| ≤ (D : ℝ) := by
      rw [abs_le]
      constructor
      · exact_mod_cast hk.1
      · exact_mod_cast hk.2
    have hnorm : ‖f k * ((k : ℂ) * Complex.I)‖ = ‖f k‖ * |(k : ℝ)| := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one]
      congr 1
      rw [Complex.norm_intCast]
    rw [hnorm, mul_pow]
    have hk0 : (0 : ℝ) ≤ |(k : ℝ)| := abs_nonneg _
    have hfn : (0 : ℝ) ≤ ‖f k‖ ^ (2 : ℕ) := sq_nonneg _
    nlinarith [pow_le_pow_left₀ hk0 habs 2]
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  nlinarith [hsum, Real.pi_pos]


/-! ## Degree filtration and the shift -/

/-- A coefficient family supported in the frequency window of radius `D`. -/
def TrigSupp (D : ℕ) (f : ℤ → ℂ) : Prop := ∀ k : ℤ, (D : ℤ) < |k| → f k = 0

theorem trigExp_eq_of_supp {D E : ℕ} (hDE : D ≤ E) {f : ℤ → ℂ} (hf : TrigSupp D f) (θ : ℝ) :
    trigExp E f θ = trigExp D f θ := by
  have hDEZ : (D : ℤ) ≤ (E : ℤ) := by exact_mod_cast hDE
  rw [trigExp, trigExp]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro k _ hknot
    simp only [Finset.mem_Icc, not_and, not_le] at hknot
    have habs : (D : ℤ) < |k| := by
      rcases le_or_gt (-(D : ℤ)) k with hlow | hlow
      · have := hknot hlow
        rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ k)]
        omega
      · rw [abs_of_neg (by omega : k < 0)]
        omega
    rw [hf k habs, zero_mul]

theorem trigSupp_deriv {D : ℕ} {f : ℤ → ℂ} (hf : TrigSupp D f) :
    TrigSupp D (fun k => f k * ((k : ℂ) * Complex.I)) := by
  intro k hk
  show f k * ((k : ℂ) * Complex.I) = 0
  rw [hf k hk, zero_mul]

theorem trigSupp_shift_succ {D : ℕ} {f : ℤ → ℂ} (hf : TrigSupp D f) :
    TrigSupp (D + 1) (fun l => f (l - 1)) := by
  intro l hl
  refine hf (l - 1) ?_
  push_cast at hl ⊢
  rcases abs_cases l with ⟨he, _⟩ | ⟨he, _⟩ <;>
    rcases abs_cases (l - 1) with ⟨he2, _⟩ | ⟨he2, _⟩ <;> omega

theorem trigSupp_shift_pred {D : ℕ} {f : ℤ → ℂ} (hf : TrigSupp D f) :
    TrigSupp (D + 1) (fun l => f (l + 1)) := by
  intro l hl
  refine hf (l + 1) ?_
  push_cast at hl ⊢
  rcases abs_cases l with ⟨he, _⟩ | ⟨he, _⟩ <;>
    rcases abs_cases (l + 1) with ⟨he2, _⟩ | ⟨he2, _⟩ <;> omega

theorem trigSupp_add {D : ℕ} {f g : ℤ → ℂ} (hf : TrigSupp D f) (hg : TrigSupp D g) :
    TrigSupp D (fun k => f k + g k) := by
  intro k hk
  show f k + g k = 0
  rw [hf k hk, hg k hk, add_zero]

theorem trigSupp_smul {D : ℕ} {f : ℤ → ℂ} (hf : TrigSupp D f) (c : ℂ) :
    TrigSupp D (fun k => c * f k) := by
  intro k hk
  show c * f k = 0
  rw [hf k hk, mul_zero]

theorem trigExp_add (D : ℕ) (f g : ℤ → ℂ) (θ : ℝ) :
    trigExp D (fun k => f k + g k) θ = trigExp D f θ + trigExp D g θ := by
  rw [trigExp, trigExp, trigExp, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem trigExp_smul (D : ℕ) (f : ℤ → ℂ) (c : ℂ) (θ : ℝ) :
    trigExp D (fun k => c * f k) θ = c * trigExp D f θ := by
  rw [trigExp, trigExp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Multiplication by `e^{iθ}` is the coefficient shift.** -/
theorem expMon_one_mul_trigExp {D : ℕ} {f : ℤ → ℂ} (hf : TrigSupp D f) (θ : ℝ) :
    expMon 1 θ * trigExp D f θ = trigExp (D + 1) (fun l => f (l - 1)) θ := by
  have hLHS : expMon 1 θ * trigExp D f θ
      = ∑ k ∈ Finset.Icc (-(D : ℤ)) (D : ℤ), f k * expMon (k + 1) θ := by
    rw [trigExp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show k + 1 = 1 + k by ring, ← expMon_mul]
    ring
  have hmid : ∑ k ∈ Finset.Icc (-(D : ℤ)) (D : ℤ), f k * expMon (k + 1) θ
      = ∑ l ∈ Finset.Icc (-(D : ℤ) + 1) ((D : ℤ) + 1), f (l - 1) * expMon l θ := by
    refine Finset.sum_nbij' (fun k => k + 1) (fun l => l - 1) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    · intro l hl
      simp only [Finset.mem_Icc] at hl ⊢
      omega
    · intro k _
      omega
    · intro l _
      omega
    · intro k _
      congr 2
      omega
  have hext : ∑ l ∈ Finset.Icc (-(D : ℤ) + 1) ((D : ℤ) + 1), f (l - 1) * expMon l θ
      = trigExp (D + 1) (fun l => f (l - 1)) θ := by
    rw [trigExp]
    refine Finset.sum_subset ?_ ?_
    · intro l hl
      simp only [Finset.mem_Icc] at hl ⊢
      push_cast
      omega
    · intro l _ hlnot
      simp only [Finset.mem_Icc, not_and, not_le] at hlnot
      have hzero : f (l - 1) = 0 := by
        refine hf (l - 1) ?_
        rcases le_or_gt (-(D : ℤ) + 1) l with hlow | hlow
        · have := hlnot hlow
          rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ l - 1)]
          omega
        · rw [abs_of_neg (by omega : l - 1 < 0)]
          omega
      rw [hzero, zero_mul]
  rw [hLHS, hmid, hext]

/-- **Multiplication by `e^{-iθ}` is the opposite coefficient shift.** -/
theorem expMon_neg_one_mul_trigExp {D : ℕ} {f : ℤ → ℂ} (hf : TrigSupp D f) (θ : ℝ) :
    expMon (-1) θ * trigExp D f θ = trigExp (D + 1) (fun l => f (l + 1)) θ := by
  have hLHS : expMon (-1) θ * trigExp D f θ
      = ∑ k ∈ Finset.Icc (-(D : ℤ)) (D : ℤ), f k * expMon (k - 1) θ := by
    rw [trigExp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show k - 1 = -1 + k by ring, ← expMon_mul]
    ring
  have hmid : ∑ k ∈ Finset.Icc (-(D : ℤ)) (D : ℤ), f k * expMon (k - 1) θ
      = ∑ l ∈ Finset.Icc (-(D : ℤ) - 1) ((D : ℤ) - 1), f (l + 1) * expMon l θ := by
    refine Finset.sum_nbij' (fun k => k - 1) (fun l => l + 1) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    · intro l hl
      simp only [Finset.mem_Icc] at hl ⊢
      omega
    · intro k _
      omega
    · intro l _
      omega
    · intro k _
      congr 2
      omega
  have hext : ∑ l ∈ Finset.Icc (-(D : ℤ) - 1) ((D : ℤ) - 1), f (l + 1) * expMon l θ
      = trigExp (D + 1) (fun l => f (l + 1)) θ := by
    rw [trigExp]
    refine Finset.sum_subset ?_ ?_
    · intro l hl
      simp only [Finset.mem_Icc] at hl ⊢
      push_cast
      omega
    · intro l _ hlnot
      simp only [Finset.mem_Icc, not_and, not_le] at hlnot
      have hzero : f (l + 1) = 0 := by
        refine hf (l + 1) ?_
        rcases le_or_gt (-(D : ℤ) - 1) l with hlow | hlow
        · have := hlnot hlow
          rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ l + 1)]
          omega
        · rw [abs_of_neg (by omega : l + 1 < 0)]
          omega
      rw [hzero, zero_mul]
  rw [hLHS, hmid, hext]

end GaloisForLFunctions.HTGeometry

end
