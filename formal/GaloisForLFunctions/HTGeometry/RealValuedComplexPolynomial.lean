/-
# A complex polynomial with real values on the real points has real coefficients

Splitting a complex polynomial into the real and imaginary parts of its coefficients writes it as
a real polynomial plus `i` times a real polynomial.  Evaluating at a real point separates the two,
so reality of every real value forces the imaginary part to vanish identically -- hence, over an
infinite field, to be the zero polynomial.

Main results:
* `imagCoeffPart`, `split_realCoeffPart` — the coefficientwise real/imaginary split.
* `map_conj_of_real_valued` — **real values force conjugation-invariant coefficients**.
* `exists_realPoly_of_real_valued` — **hence a real polynomial representing the same function**.
* `exists_realShellPoly_of_isSymmetric` — **the real shell polynomial of a symmetric spectral
  function**.
-/
import GaloisForLFunctions.HTGeometry.ShellSymmetricPolynomial
import Mathlib.Algebra.MvPolynomial.Funext

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {σ : Type*}

/-- The real polynomial whose coefficients are the imaginary parts of a complex one. -/
def imagCoeffPart (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ :=
  realCoeffPart ((-Complex.I) • p)

theorem coeff_imagCoeffPart (p : MvPolynomial σ ℂ) (t : σ →₀ ℕ) :
    (imagCoeffPart p).coeff t = (p.coeff t).im := by
  rw [imagCoeffPart, coeff_realCoeffPart, MvPolynomial.coeff_smul, smul_eq_mul]
  simp [Complex.mul_re]

/-- **The coefficientwise real/imaginary split.** -/
theorem split_realCoeffPart (p : MvPolynomial σ ℂ) :
    p = MvPolynomial.map (algebraMap ℝ ℂ) (realCoeffPart p)
      + Complex.I • MvPolynomial.map (algebraMap ℝ ℂ) (imagCoeffPart p) := by
  ext t
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, smul_eq_mul, MvPolynomial.coeff_map,
    MvPolynomial.coeff_map, coeff_realCoeffPart, coeff_imagCoeffPart]
  simp only [Complex.coe_algebraMap]
  conv_lhs => rw [← Complex.re_add_im (p.coeff t)]
  ring

variable {N : ℕ}

private theorem eval_split (G : MvPolynomial (Fin N) ℂ) (θ : Fin N → ℝ) :
    MvPolynomial.eval (fun i => ((θ i : ℝ) : ℂ)) G
      = ((MvPolynomial.eval θ (realCoeffPart G) : ℝ) : ℂ)
        + Complex.I * ((MvPolynomial.eval θ (imagCoeffPart G) : ℝ) : ℂ) := by
  conv_lhs => rw [split_realCoeffPart G]
  rw [map_add, ofReal_eval_eq_eval_map, ofReal_eval_eq_eval_map]
  congr 1
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]

/-- **Real values force conjugation-invariant coefficients.** -/
theorem map_conj_of_real_valued {G : MvPolynomial (Fin N) ℂ}
    (hreal : ∀ θ : Fin N → ℝ, (MvPolynomial.eval (fun i => ((θ i : ℝ) : ℂ)) G).im = 0) :
    MvPolynomial.map (starRingEnd ℂ) G = G := by
  have hB : imagCoeffPart G = 0 := by
    refine MvPolynomial.funext fun θ => ?_
    have h := hreal θ
    rw [eval_split G θ] at h
    simpa using h
  ext t
  rw [MvPolynomial.coeff_map]
  have him : (G.coeff t).im = 0 := by
    have := congrArg (fun q => MvPolynomial.coeff t q) hB
    rw [coeff_imagCoeffPart] at this
    simpa using this
  exact Complex.conj_eq_iff_im.mpr him

/-- **A complex polynomial with real values on the real points is a real polynomial.** -/
theorem exists_realPoly_of_real_valued {G : MvPolynomial (Fin N) ℂ}
    (hreal : ∀ θ : Fin N → ℝ, (MvPolynomial.eval (fun i => ((θ i : ℝ) : ℂ)) G).im = 0) :
    ∃ G' : MvPolynomial (Fin N) ℝ, ∀ θ : Fin N → ℝ,
      ((MvPolynomial.eval θ G' : ℝ) : ℂ)
        = MvPolynomial.eval (fun i => ((θ i : ℝ) : ℂ)) G := by
  refine ⟨realCoeffPart G, fun θ => ?_⟩
  rw [ofReal_eval_eq_eval_map, map_realCoeffPart (map_conj_of_real_valued hreal)]

/-- **The real shell polynomial of a symmetric spectral function.**  A real symmetric function of
the spectrum of a Hermitian interaction family equals a fixed real polynomial in the coordinates. -/
theorem exists_realShellPoly_of_isSymmetric {D : ℕ} {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (p : MvPolynomial (Fin D) ℝ) (hp : p.IsSymmetric) :
    ∃ G : MvPolynomial (Fin N) ℝ, ∀ θ : Fin N → ℝ,
      MvPolynomial.eval
          (fun i => (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i) p
        = MvPolynomial.eval θ G := by
  have hpC : (MvPolynomial.map (algebraMap ℝ ℂ) p).IsSymmetric := by
    intro e
    rw [← MvPolynomial.map_rename, hp e]
  obtain ⟨Gc, hGc⟩ := exists_shellPoly_of_isSymmetric hP _ hpC
  have hval : ∀ θ : Fin N → ℝ,
      MvPolynomial.eval (fun a => ((θ a : ℝ) : ℂ)) Gc
        = ((MvPolynomial.eval
            (fun i => (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i) p : ℝ) : ℂ) := by
    intro θ
    rw [← hGc θ, ofReal_eval_eq_eval_map]
  have hreal : ∀ θ : Fin N → ℝ,
      (MvPolynomial.eval (fun a => ((θ a : ℝ) : ℂ)) Gc).im = 0 := by
    intro θ
    rw [hval θ]
    exact Complex.ofReal_im _
  obtain ⟨G, hG⟩ := exists_realPoly_of_real_valued hreal
  refine ⟨G, fun θ => ?_⟩
  have := (hG θ).trans (hval θ)
  exact (Complex.ofReal_inj.mp this).symm

end

end GaloisForLFunctions.HTGeometry
