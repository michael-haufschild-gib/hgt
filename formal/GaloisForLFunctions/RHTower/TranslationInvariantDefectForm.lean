import GaloisForLFunctions.RHTower.XiEntireReal

/-!
# Translation-invariant defect forms are hyperbolic on every off-real orbit

On a semisimple divisor module real translation acts by the character `e_ρ ↦ exp(-i a ρ) e_ρ`.
A Hermitian form invariant under every real translation can pair `e_ρ` with `e_σ` only when
`ρ = conj σ`: otherwise the character identity `exp(i a (conj σ - ρ)) = 1` would hold for every real
`a`, forcing `conj σ = ρ` by differentiating at `a = 0`.

Hence the diagonal entry at a nonreal frequency vanishes, so each nonreal conjugate pair spans an
isotropic plane whose form is `2 Re(x conj(y) c)`: with `c ≠ 0` it takes both signs, i.e. it is a
hyperbolic plane.  A form that is nonzero on the diagonal at every frequency therefore has real
support only.
-/

noncomputable section

namespace RHTower

open Complex

variable {ι : Type*}

/-- A real translation acts on the semisimple divisor module by the character `exp(-i a ρ)`. -/
def divisorTranslationChar (rho : ι → ℂ) (a : ℝ) (i : ι) : ℂ :=
  Complex.exp (-(a : ℂ) * I * rho i)

/-- A character identity holding for every real translation forces the frequencies to be
conjugate. -/
theorem eq_zero_of_exp_eq_one {c : ℂ} (h : ∀ a : ℝ, Complex.exp ((a : ℂ) * (I * c)) = 1) :
    c = 0 := by
  have hfun : (fun a : ℝ => Complex.exp ((a : ℂ) * (I * c))) = fun _ : ℝ => (1 : ℂ) := funext h
  have hlin : HasDerivAt (fun a : ℝ => ((a : ℂ) * (I * c))) (I * c) 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (I * c)
  have hcomp : HasDerivAt (fun a : ℝ => Complex.exp ((a : ℂ) * (I * c)))
      (Complex.exp (((0 : ℝ) : ℂ) * (I * c)) * (I * c)) 0 :=
    (Complex.hasDerivAt_exp _).comp 0 hlin
  rw [hfun] at hcomp
  have hzero : Complex.exp (((0 : ℝ) : ℂ) * (I * c)) * (I * c) = 0 :=
    ((hasDerivAt_const (0 : ℝ) (1 : ℂ)).unique hcomp).symm
  have hexp : Complex.exp (((0 : ℝ) : ℂ) * (I * c)) ≠ 0 := Complex.exp_ne_zero _
  have hIc : I * c = 0 := (mul_eq_zero.mp hzero).resolve_left hexp
  exact (mul_eq_zero.mp hIc).resolve_left Complex.I_ne_zero

/-- **Invariant forms pair only conjugate frequencies.**  A translation-invariant Hermitian form
can pair `e_ρ` with `e_σ` only when `ρ = conj σ`. -/
theorem eq_conj_of_invariant_ne_zero {rho : ι → ℂ} {H : ι → ι → ℂ}
    (hinv : ∀ (a : ℝ) (i j : ι),
      divisorTranslationChar rho a i * (starRingEnd ℂ) (divisorTranslationChar rho a j) * H i j = H i j)
    {i j : ι} (hij : H i j ≠ 0) : rho i = (starRingEnd ℂ) (rho j) := by
  have hchar : ∀ a : ℝ,
      divisorTranslationChar rho a i * (starRingEnd ℂ) (divisorTranslationChar rho a j) = 1 := by
    intro a
    have h := hinv a i j
    have hfac : (divisorTranslationChar rho a i * (starRingEnd ℂ) (divisorTranslationChar rho a j) - 1) *
        H i j = 0 := by linear_combination h
    rcases mul_eq_zero.mp hfac with hc | hc
    · linear_combination hc
    · exact absurd hc hij
  have hkey : ∀ a : ℝ,
      Complex.exp ((a : ℂ) * (I * ((starRingEnd ℂ) (rho j) - rho i))) = 1 := by
    intro a
    have h := hchar a
    rw [divisorTranslationChar, divisorTranslationChar, ← Complex.exp_conj, ← Complex.exp_add] at h
    rw [← h]
    congr 1
    simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
    ring
  have := eq_zero_of_exp_eq_one hkey
  linear_combination -this

/-- **Off-real orbits are isotropic.**  A translation-invariant form vanishes on the diagonal at
every nonreal frequency. -/
theorem diag_eq_zero_of_not_conj_self {rho : ι → ℂ} {H : ι → ι → ℂ}
    (hinv : ∀ (a : ℝ) (i j : ι),
      divisorTranslationChar rho a i * (starRingEnd ℂ) (divisorTranslationChar rho a j) * H i j = H i j)
    {i : ι} (hi : rho i ≠ (starRingEnd ℂ) (rho i)) : H i i = 0 := by
  by_contra hne
  exact hi (eq_conj_of_invariant_ne_zero hinv hne)

/-- The quadratic value of a two-dimensional isotropic pair with off-diagonal entry `c`. -/
def hyperbolicValue (c x y : ℂ) : ℂ :=
  x * (starRingEnd ℂ) y * c + y * (starRingEnd ℂ) x * (starRingEnd ℂ) c

/-- **Every nonreal conjugate pair is a hyperbolic plane.**  With a nonzero off-diagonal entry the
restricted form takes both strictly positive and strictly negative values. -/
theorem hyperbolicValue_pos_neg {c : ℂ} (hc : c ≠ 0) :
    0 < (hyperbolicValue c ((starRingEnd ℂ) c) 1).re ∧
      (hyperbolicValue c (-(starRingEnd ℂ) c) 1).re < 0 := by
  have hnorm : (0 : ℝ) < Complex.normSq c := Complex.normSq_pos.mpr hc
  have h1 : (hyperbolicValue c ((starRingEnd ℂ) c) 1).re = 2 * Complex.normSq c := by
    simp [hyperbolicValue, Complex.normSq_apply, Complex.mul_re]
    ring
  have h2 : (hyperbolicValue c (-(starRingEnd ℂ) c) 1).re = -(2 * Complex.normSq c) := by
    simp [hyperbolicValue, Complex.normSq_apply, Complex.mul_re]
    ring
  refine ⟨?_, ?_⟩
  · rw [h1]; linarith
  · rw [h2]; linarith

/-- **A positive invariant form is faithful only on real support.**  If the form is nondegenerate on
the diagonal then every frequency is fixed by conjugation. -/
theorem rho_eq_conj_of_posDef {rho : ι → ℂ} {H : ι → ι → ℂ}
    (hinv : ∀ (a : ℝ) (i j : ι),
      divisorTranslationChar rho a i * (starRingEnd ℂ) (divisorTranslationChar rho a j) * H i j = H i j)
    (hpos : ∀ i : ι, H i i ≠ 0) (i : ι) : rho i = (starRingEnd ℂ) (rho i) :=
  eq_conj_of_invariant_ne_zero hinv (hpos i)

end RHTower
