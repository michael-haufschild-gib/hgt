import GaloisForLFunctions.HTGeometry.DigammaJetGerm
import GaloisForLFunctions.HTGeometry.RationalShiftHypertranscendence

/-!
# No differential polynomial in the digamma jets is flat

Evaluating a jet polynomial over `ℂ(s)` at the digamma jets is a ring homomorphism into the germ
ring of the upper right half-plane, and it intertwines the jet substitution `X_j ↦ X_j + polePart j`
with the unit translation.  The flat values therefore form a set closed under differences, under
`ℂ(s)`-multiples and under the jet substitution, containing no nonzero constant — and no such set
contains a nonzero element.

So a nonzero differential polynomial in `ψ, ψ′, …` with rational coefficients never has a value that
beats every power of the modulus: there is no flat cancellation.  This is the analytic form of the
injectivity of the formal Stirling expansion.
-/

open Filter Topology Complex Polynomial

namespace GaloisForLFunctions

/-- Evaluation of a jet polynomial at the digamma jet germs. -/
noncomputable def digammaJetEval (σ₀ : ℝ) (m : ℕ) :
    MvPolynomial (Fin m) (RatFunc ℂ) →+* HalfPlaneGerm σ₀ :=
  MvPolynomial.eval₂Hom (ratGerm σ₀) (fun j : Fin m => digammaJetGerm σ₀ (j : ℕ))

@[simp] theorem digammaJetEval_C (σ₀ : ℝ) (m : ℕ) (k : RatFunc ℂ) :
    digammaJetEval σ₀ m (MvPolynomial.C k) = ratGerm σ₀ k := by
  simp [digammaJetEval]

@[simp] theorem digammaJetEval_X (σ₀ : ℝ) (m : ℕ) (j : Fin m) :
    digammaJetEval σ₀ m (MvPolynomial.X j) = digammaJetGerm σ₀ (j : ℕ) := by
  simp [digammaJetEval]

/-- **The jet substitution is the translation.**  Substituting `X_j ↦ X_j + polePart j` and shifting
the coefficients is, after evaluation at the digamma jets, the unit translation of the value. -/
theorem digammaJetEval_jetTranslate (σ₀ : ℝ) (m : ℕ)
    (G : MvPolynomial (Fin m) (RatFunc ℂ)) :
    digammaJetEval σ₀ m (RationalIncrementHolder.jetTranslateWith (fun j => polePart j) m G)
      = shiftGerm σ₀ (digammaJetEval σ₀ m G) := by
  have hext : (digammaJetEval σ₀ m).comp
        (RationalIncrementHolder.jetTranslateWith (fun j => polePart j) m)
      = (shiftGerm σ₀).comp (digammaJetEval σ₀ m) := by
    refine MvPolynomial.ringHom_ext (fun k => ?_) (fun j => ?_)
    · show digammaJetEval σ₀ m
          (RationalIncrementHolder.jetTranslateWith (fun j => polePart j) m (MvPolynomial.C k))
        = shiftGerm σ₀ (digammaJetEval σ₀ m (MvPolynomial.C k))
      rw [RationalIncrementHolder.jetTranslate_CWith, digammaJetEval_C, digammaJetEval_C,
        shiftGerm_ratGerm]
    · show digammaJetEval σ₀ m
          (RationalIncrementHolder.jetTranslateWith (fun j => polePart j) m (MvPolynomial.X j))
        = shiftGerm σ₀ (digammaJetEval σ₀ m (MvPolynomial.X j))
      rw [RationalIncrementHolder.jetTranslate_XWith, digammaJetEval_X, shiftGerm_digammaJetGerm,
        map_add, digammaJetEval_X, digammaJetEval_C]
  exact RingHom.congr_fun hext G

/-- **No nonzero differential polynomial in the digamma jets has a flat value.**  The flat values
form a shift-stable annihilator space with no nonzero constants, and no such space contains a
nonzero element. -/
theorem not_isFlatGerm_digammaJetEval {σ₀ : ℝ} {m : ℕ} {G : MvPolynomial (Fin m) (RatFunc ℂ)}
    (hG : G ≠ 0) : ¬ IsFlatGerm σ₀ (digammaJetEval σ₀ m G) := by
  intro hflat
  refine RationalIncrementHolder.no_shift_stable_annihilatorWith (fun j => polePart j)
    {H | IsFlatGerm σ₀ (digammaJetEval σ₀ m H)} ?_ ?_ ?_ ?_ ?_ ⟨G, hflat, hG⟩
  · intro H K hH hK
    show IsFlatGerm σ₀ (digammaJetEval σ₀ m (H - K))
    rw [map_sub]
    exact IsFlatGerm.sub hH hK
  · intro k H hH
    show IsFlatGerm σ₀ (digammaJetEval σ₀ m (MvPolynomial.C k * H))
    rw [map_mul, digammaJetEval_C]
    exact IsFlatGerm.mul_ratGerm k hH
  · intro H hH
    show IsFlatGerm σ₀ (digammaJetEval σ₀ m
      (RationalIncrementHolder.jetTranslateWith (fun j => polePart j) m H))
    rw [digammaJetEval_jetTranslate]
    exact IsFlatGerm.shiftGerm hH
  · intro k hk
    by_contra hk0
    exact not_isFlatGerm_ratGerm hk0 (by simpa using hk)
  · intro w δ h
    exact ratShift_sub_polePart_combination h

end GaloisForLFunctions
