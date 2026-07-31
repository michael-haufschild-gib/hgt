import GaloisForLFunctions.HTGeometry.BohrDerivativeSpectrum

/-!
# Finite Bohr rank for almost-periodic solutions of a linear autonomous equation

This is eq. (9) in the linear autonomous case, unconditionally.

Differentiating multiplies the Bohr coefficient at `λ` by `iλ`, so applying the coefficient
functional to a relation `∑_j d_j f⁽ʲ⁾ = 0` with constant `d_j` produces

`(∑_j d_j (iλ)^j) · a_f(λ) = 0`.

Every frequency in the spectrum therefore makes the characteristic polynomial vanish at `iλ`.  A
nonzero polynomial has finitely many roots, and `λ ↦ iλ` is injective, so the spectrum is **finite**
and the Bohr frequency module is finitely generated: a nonconstant almost-periodic solution of a
nontrivial constant-coefficient linear differential equation has finite rational frequency rank.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-! ### Linearity of the Bohr coefficient -/

theorem bohrCoefficient_finsetSum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℂ)
    (hc : ∀ i ∈ s, Continuous (F i)) (ha : ∀ i ∈ s, HTGeometry.IsBohrAlmostPeriodic (F i))
    (lam : ℝ) :
    bohrCoefficient (fun t => ∑ i ∈ s, F i t) lam = ∑ i ∈ s, bohrCoefficient (F i) lam := by
  have hfun : (fun t : ℝ => (∑ i ∈ s, F i t) * bohrChar lam t)
      = fun t : ℝ => ∑ i ∈ s, F i t * bohrChar lam t := by
    funext t
    rw [Finset.sum_mul]
  rw [bohrCoefficient, hfun,
    bohrMean_sum (F := fun i => fun t => F i t * bohrChar lam t) s
      (fun i hi => (hc i hi).mul (continuous_bohrChar lam))
      (fun i hi => isBohrAlmostPeriodic_mul_bohrChar (hc i hi) (ha i hi) lam)]
  rfl

theorem bohrCoefficient_const_mul (c : ℂ) {F : ℝ → ℂ} (hc : Continuous F)
    (ha : HTGeometry.IsBohrAlmostPeriodic F) (lam : ℝ) :
    bohrCoefficient (fun t => c * F t) lam = c * bohrCoefficient F lam := by
  have hfun : (fun t : ℝ => (c * F t) * bohrChar lam t)
      = fun t : ℝ => c * (F t * bohrChar lam t) := funext fun t => by ring
  rw [bohrCoefficient, hfun,
    bohrMean_const_mul (f := fun t => F t * bohrChar lam t) c
      (hc.mul (continuous_bohrChar lam)) (isBohrAlmostPeriodic_mul_bohrChar hc ha lam)]
  rfl

theorem bohrCoefficient_of_eq_zero {F : ℝ → ℂ} (h : ∀ t, F t = 0) (lam : ℝ) :
    bohrCoefficient F lam = 0 := by
  have hfun : (fun t : ℝ => F t * bohrChar lam t) = fun _ : ℝ => (0 : ℂ) := by
    funext t
    rw [h t, zero_mul]
  rw [bohrCoefficient, hfun, bohrMean_zero]

/-- Iterated differentiation multiplies the Bohr coefficient by `(iλ)^j`. -/
theorem bohrCoefficient_iterate {f : ℕ → ℝ → ℂ}
    (hderiv : ∀ j t, HasDerivAt (f j) (f (j + 1) t) t)
    (hcont : ∀ j, Continuous (f j)) (hap : ∀ j, HTGeometry.IsBohrAlmostPeriodic (f j))
    (lam : ℝ) (j : ℕ) :
    bohrCoefficient (f j) lam = ((lam : ℂ) * Complex.I) ^ j * bohrCoefficient (f 0) lam := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [bohrCoefficient_deriv (hderiv j) (hcont j) (hcont (j + 1)) (hap j) (hap (j + 1)) lam,
        ih, pow_succ]
      ring

/-! ### The characteristic equation on the spectrum -/

/-- **Every Bohr frequency of a solution is a characteristic root.** -/
theorem linearOde_char_eq_zero {n : ℕ} {f : ℕ → ℝ → ℂ}
    (hderiv : ∀ j t, HasDerivAt (f j) (f (j + 1) t) t)
    (hcont : ∀ j, Continuous (f j)) (hap : ∀ j, HTGeometry.IsBohrAlmostPeriodic (f j))
    (d : ℕ → ℂ)
    (hrel : ∀ t, ∑ j ∈ Finset.range (n + 1), d j * f j t = 0)
    {lam : ℝ} (hlam : bohrCoefficient (f 0) lam ≠ 0) :
    ∑ j ∈ Finset.range (n + 1), d j * ((lam : ℂ) * Complex.I) ^ j = 0 := by
  have h0 : bohrCoefficient (fun t => ∑ j ∈ Finset.range (n + 1), d j * f j t) lam = 0 :=
    bohrCoefficient_of_eq_zero hrel lam
  rw [bohrCoefficient_finsetSum (s := Finset.range (n + 1))
    (F := fun j => fun t => d j * f j t)
    (fun j _ => (continuous_const.mul (hcont j) : Continuous fun t : ℝ => d j * f j t))
    (fun j _ => isBohrAlmostPeriodic_const_mul (d j) (hap j)) lam] at h0
  have hterm : ∀ j ∈ Finset.range (n + 1),
      bohrCoefficient (fun t => d j * f j t) lam
        = (d j * ((lam : ℂ) * Complex.I) ^ j) * bohrCoefficient (f 0) lam := by
    intro j _
    rw [bohrCoefficient_const_mul (d j) (hcont j) (hap j) lam,
      bohrCoefficient_iterate hderiv hcont hap lam j]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exact absurd h hlam

/-! ### Finiteness of the spectrum -/

/-- **Finite Bohr spectrum (eq. 9, linear autonomous case).**  An almost-periodic solution of a
nontrivial constant-coefficient linear differential equation has finite Bohr spectrum. -/
theorem bohrSpectrum_finite_of_linearOde {n : ℕ} {f : ℕ → ℝ → ℂ}
    (hderiv : ∀ j t, HasDerivAt (f j) (f (j + 1) t) t)
    (hcont : ∀ j, Continuous (f j)) (hap : ∀ j, HTGeometry.IsBohrAlmostPeriodic (f j))
    (d : ℕ → ℂ)
    (hrel : ∀ t, ∑ j ∈ Finset.range (n + 1), d j * f j t = 0)
    {j₀ : ℕ} (hj₀ : j₀ ∈ Finset.range (n + 1)) (hd : d j₀ ≠ 0) :
    (bohrSpectrum (f 0)).Finite := by
  classical
  set P : Polynomial ℂ :=
    ∑ j ∈ Finset.range (n + 1), Polynomial.C (d j) * Polynomial.X ^ j with hP
  have hPeval : ∀ z : ℂ, P.eval z = ∑ j ∈ Finset.range (n + 1), d j * z ^ j := by
    intro z
    rw [hP, Polynomial.eval_finsetSum]
    simp
  have hPcoeff : P.coeff j₀ = d j₀ := by
    rw [hP, Polynomial.finsetSum_coeff]
    have hstep : ∀ j ∈ Finset.range (n + 1),
        (Polynomial.C (d j) * Polynomial.X ^ j).coeff j₀ = if j₀ = j then d j else 0 := by
      intro j _
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases h : j₀ = j <;> simp [h]
    rw [Finset.sum_congr rfl hstep, Finset.sum_ite_eq (Finset.range (n + 1)) j₀ d, if_pos hj₀]
  have hPne : P ≠ 0 := by
    intro h
    apply hd
    rw [← hPcoeff, h, Polynomial.coeff_zero]
  have hroots := Polynomial.finite_setOf_isRoot hPne
  have hsub : bohrSpectrum (f 0) ⊆
      (fun lam : ℝ => (lam : ℂ) * Complex.I) ⁻¹' {z : ℂ | P.IsRoot z} := by
    intro lam hlam
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Polynomial.IsRoot, hPeval]
    exact linearOde_char_eq_zero hderiv hcont hap d hrel hlam
  refine Set.Finite.subset ?_ hsub
  refine Set.Finite.preimage ?_ hroots
  intro a _ b _ hab
  have hIne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have : ((a : ℝ) : ℂ) = ((b : ℝ) : ℂ) := mul_right_cancel₀ hIne hab
  exact_mod_cast this

/-- **Finitely generated frequency module (eq. 9, linear autonomous case).** -/
theorem bohrFrequencyModule_fg_of_linearOde {n : ℕ} {f : ℕ → ℝ → ℂ}
    (hderiv : ∀ j t, HasDerivAt (f j) (f (j + 1) t) t)
    (hcont : ∀ j, Continuous (f j)) (hap : ∀ j, HTGeometry.IsBohrAlmostPeriodic (f j))
    (d : ℕ → ℂ)
    (hrel : ∀ t, ∑ j ∈ Finset.range (n + 1), d j * f j t = 0)
    {j₀ : ℕ} (hj₀ : j₀ ∈ Finset.range (n + 1)) (hd : d j₀ ≠ 0) :
    (bohrFrequencyModule (f 0)).FG :=
  Submodule.fg_span
    (bohrSpectrum_finite_of_linearOde hderiv hcont hap d hrel hj₀ hd)

end

end GaloisForLFunctions
