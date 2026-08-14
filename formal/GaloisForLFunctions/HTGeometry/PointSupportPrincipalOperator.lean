import GaloisForLFunctions.HTGeometry.PointSupportStructure

/-!
# The principal Gamma operator has no point-supported kernel

The principal part of the frequency equation is `2η ∂ + 1`.  On a distribution supported at the
origin it acts diagonally in the jet coefficients: since `(η φ')^{(j)}(0) = j φ^{(j)}(0)`, the
coefficient of `δ^{(j)}` is multiplied by `2j + 1`, which never vanishes.  Hence no nonzero
distribution supported at the origin solves the principal equation.
-/

open Set SchwartzMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Multiplication by the coordinate on Schwartz space. -/
def coordMulCLM : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) Complex.ofRealCLM.hasTemperateGrowth

@[simp] theorem coordMulCLM_apply (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    (coordMulCLM φ : ℝ → ℂ) x = φ x * (x : ℂ) := rfl

/-- The Leibniz rule for multiplication by the coordinate. -/
theorem iteratedDeriv_mul_coord {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (fun y : ℝ => g y * (y : ℂ)) x
      = iteratedDeriv j g x * (x : ℂ) + (j : ℂ) * iteratedDeriv (j - 1) g x := by
  induction j generalizing x with
  | zero => simp [iteratedDeriv_zero]
  | succ j ih =>
    have hstep : ∀ k : ℕ, ∀ y : ℝ,
        HasDerivAt (iteratedDeriv k g) (iteratedDeriv (k+1) g y) y := by
      intro k y
      have hd : Differentiable ℝ (iteratedDeriv k g) :=
        hg.differentiable_iteratedDeriv k (by exact_mod_cast lt_top_iff_ne_top.mpr (by simp))
      have h := (hd y).hasDerivAt
      rwa [← iteratedDeriv_succ] at h
    have hfun : iteratedDeriv j (fun y : ℝ => g y * (y : ℂ))
        = fun y : ℝ => iteratedDeriv j g y * (y : ℂ) + (j : ℂ) * iteratedDeriv (j - 1) g y := by
      funext y
      exact ih y
    rw [iteratedDeriv_succ, hfun]
    have hofReal : HasDerivAt (fun y : ℝ => ((y : ℂ))) 1 x := by
      have h0 := (hasDerivAt_id x).ofReal_comp
      rw [Complex.ofReal_one] at h0
      exact h0
    have h1 : HasDerivAt (fun y : ℝ => iteratedDeriv j g y * (y : ℂ))
        (iteratedDeriv (j+1) g x * (x : ℂ) + iteratedDeriv j g x * 1) x :=
      (hstep j x).mul hofReal
    have h2 : HasDerivAt (fun y : ℝ => (j : ℂ) * iteratedDeriv (j - 1) g y)
        ((j : ℂ) * iteratedDeriv (j - 1 + 1) g x) x :=
      (hstep (j - 1) x).const_mul (j : ℂ)
    have hsum : HasDerivAt (fun y : ℝ => iteratedDeriv j g y * (y : ℂ)
        + (j : ℂ) * iteratedDeriv (j - 1) g y)
        (iteratedDeriv (j+1) g x * (x : ℂ) + iteratedDeriv j g x * 1
          + (j : ℂ) * iteratedDeriv (j - 1 + 1) g x) x := h1.add h2
    rw [hsum.deriv]
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      simp
    · have hj1 : j - 1 + 1 = j := by omega
      rw [hj1]
      have hjs : (j + 1 : ℕ) - 1 = j := by omega
      rw [hjs]
      push_cast
      ring

/-- The jet coefficients of the coordinate multiple of a derivative. -/
theorem iteratedDeriv_coordMul_deriv_zero (φ : SchwartzMap ℝ ℂ) (j : ℕ) :
    iteratedDeriv j ((coordMulCLM (SchwartzMap.derivCLM ℂ ℂ φ) : SchwartzMap ℝ ℂ) : ℝ → ℂ) 0
      = (j : ℂ) * iteratedDeriv j (φ : ℝ → ℂ) 0 := by
  have hfun : ((coordMulCLM (SchwartzMap.derivCLM ℂ ℂ φ) : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      = fun y : ℝ => (deriv (φ : ℝ → ℂ)) y * (y : ℂ) := rfl
  have hgc : ContDiff ℝ (⊤ : ℕ∞) (deriv (φ : ℝ → ℂ)) := by
    have hcoe : (deriv (φ : ℝ → ℂ))
        = ((SchwartzMap.derivCLM ℂ ℂ φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) := rfl
    rw [hcoe]
    exact (SchwartzMap.derivCLM ℂ ℂ φ).smooth'
  rw [hfun, iteratedDeriv_mul_coord hgc j 0]
  have hzero : ((0:ℝ) : ℂ) = 0 := by norm_num
  rw [hzero, mul_zero, zero_add]
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    simp
  · have hj1 : j - 1 + 1 = j := by omega
    have hsucc := iteratedDeriv_succ' (n := j - 1) (f := (φ : ℝ → ℂ))
    rw [hj1] at hsucc
    rw [← hsucc]

/-- **The principal Gamma operator kills no point-supported distribution.** -/
theorem coeff_eq_zero_of_principal {u : SchwartzMap ℝ ℂ →L[ℂ] X} {N : ℕ} {c : ℕ → X}
    (hrep : ∀ φ : SchwartzMap ℝ ℂ,
      u φ = ∑ j ∈ Finset.range (N+1), (iteratedDeriv j (φ : ℝ → ℂ) 0) • c j)
    (hEq : ∀ φ : SchwartzMap ℝ ℂ,
      u φ + (2 : ℂ) • u (coordMulCLM (SchwartzMap.derivCLM ℂ ℂ φ)) = 0) :
    ∀ j, j ≤ N → c j = 0 := by
  intro i hi
  have hmem : i ∈ Finset.range (N+1) := Finset.mem_range.mpr (by omega)
  have hu1 : u (jetTest i) = c i := by
    rw [hrep]
    have hcongr : ∀ j ∈ Finset.range (N+1),
        (iteratedDeriv j (jetTest i : ℝ → ℂ) 0) • c j = if j = i then c j else 0 := by
      intro j _
      rw [iteratedDeriv_jetTest_zero]
      by_cases h : j = i
      · rw [if_pos h, if_pos h, one_smul]
      · rw [if_neg h, if_neg h, zero_smul]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq' (Finset.range (N+1)) i c, if_pos hmem]
  have hu2 : u (coordMulCLM (SchwartzMap.derivCLM ℂ ℂ (jetTest i))) = (i : ℂ) • c i := by
    rw [hrep]
    have hcongr : ∀ j ∈ Finset.range (N+1),
        (iteratedDeriv j ((coordMulCLM (SchwartzMap.derivCLM ℂ ℂ (jetTest i)) :
            SchwartzMap ℝ ℂ) : ℝ → ℂ) 0) • c j = if j = i then (i : ℂ) • c i else 0 := by
      intro j _
      rw [iteratedDeriv_coordMul_deriv_zero, iteratedDeriv_jetTest_zero]
      by_cases h : j = i
      · rw [if_pos h, if_pos h, h, mul_one]
      · rw [if_neg h, if_neg h, mul_zero, zero_smul]
    rw [Finset.sum_congr rfl hcongr,
      Finset.sum_ite_eq' (Finset.range (N+1)) i (fun _ => (i : ℂ) • c i), if_pos hmem]
  have h := hEq (jetTest i)
  rw [hu1, hu2, smul_smul] at h
  have hfac : c i + ((2 : ℂ) * (i : ℂ)) • c i = ((1 : ℂ) + 2 * (i : ℂ)) • c i := by
    rw [add_smul, one_smul]
  rw [hfac] at h
  have hne : ((1 : ℂ) + 2 * (i : ℂ)) ≠ 0 := by
    intro hcon
    have hre : ((1 : ℂ) + 2 * (i : ℂ)).re = 1 + 2 * (i : ℝ) := by
      simp
    rw [hcon] at hre
    have : (0:ℝ) = 1 + 2 * (i : ℝ) := by simpa using hre
    have hipos : (0:ℝ) ≤ (i : ℝ) := by positivity
    linarith
  exact (smul_eq_zero.mp h).resolve_left hne

/-- **No nonzero distribution supported at the origin solves the principal Gamma equation.** -/
theorem eq_zero_of_pointSupport_principal {u : SchwartzMap ℝ ℂ →L[ℂ] X}
    (hu : ∀ ψ : SchwartzMap ℝ ℂ, (∃ δ > 0, ∀ x : ℝ, |x| ≤ δ → (ψ : ℝ → ℂ) x = 0) → u ψ = 0)
    (hEq : ∀ φ : SchwartzMap ℝ ℂ,
      u φ + (2 : ℂ) • u (coordMulCLM (SchwartzMap.derivCLM ℂ ℂ φ)) = 0) :
    ∀ φ : SchwartzMap ℝ ℂ, u φ = 0 := by
  obtain ⟨N, c, hrep⟩ := exists_delta_representation u hu
  have hzero := coeff_eq_zero_of_principal hrep hEq
  intro φ
  rw [hrep]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [hzero j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)), smul_zero]

end

end GaloisForLFunctions.HTGeometry
