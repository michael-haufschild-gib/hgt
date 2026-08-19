import GaloisForLFunctions.HTGeometry.JetNonNegligible
import GaloisForLFunctions.HTGeometry.ShiftedJetFieldDatum

/-!
# Jet polynomial germs have a representative of polynomial tube growth

Every evaluation of a jet polynomial at the upper end is the germ of a function with polynomial
growth on tubes.  Consequently multiplying a negligible germ by a jet polynomial germ leaves it
negligible — the closure property the shift elimination needs beyond rational multiples.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

local instance jetGrowthRatFuncAlgebra : Algebra (RatFunc ℂ) (Germ upperEndFilter ℂ) :=
  ratFuncGerm.toAlgebra

variable {r : ℕ}

theorem exists_polyGrowth_rep_shiftedJetEval (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    {M : ℕ} (idx : Fin M → Fin r × ℕ) (P : MvPolynomial (Fin M) (RatFunc ℂ)) :
    ∃ f : ℂ → ℂ, (f : Germ upperEndFilter ℂ) = shiftedJetEval lam idx P
      ∧ HasTubePolyGrowth f := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
      refine ⟨ratFuncFun a, ?_, hasTubePolyGrowth_ratFuncFun a⟩
      rw [shiftedJetEval, MvPolynomial.eval₂_C]
      rfl
  | add p q hp hq =>
      obtain ⟨f, hf, hfg⟩ := hp
      obtain ⟨g, hg, hgg⟩ := hq
      refine ⟨fun z => f z + g z, ?_, hfg.add hgg⟩
      rw [shiftedJetEval, MvPolynomial.eval₂_add, ← shiftedJetEval, ← shiftedJetEval, ← hf, ← hg]
      rfl
  | mul_X p k hp =>
      obtain ⟨f, hf, hfg⟩ := hp
      refine ⟨fun z => f z * jetFieldFun lam (idx k) z, ?_,
        hfg.mul ((hasLogRatApprox_jetFieldFun lam hlam (idx k)).hasTubePolyGrowth)⟩
      rw [shiftedJetEval, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, ← shiftedJetEval, ← hf]
      have hjet : jetGerm lam (idx k)
          = ((jetFieldFun lam (idx k) : ℂ → ℂ) : Germ upperEndFilter ℂ) := rfl
      rw [hjet]
      rfl

/-- Multiplying a negligible germ by a jet polynomial germ keeps it negligible. -/
theorem IsGermNegligible.mul_shiftedJetEval {g : Germ upperEndFilter ℂ} (hg : IsGermNegligible g)
    (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i) {M : ℕ} (idx : Fin M → Fin r × ℕ)
    (P : MvPolynomial (Fin M) (RatFunc ℂ)) :
    IsGermNegligible (shiftedJetEval lam idx P * g) := by
  obtain ⟨f, hf, hfg⟩ := exists_polyGrowth_rep_shiftedJetEval lam hlam idx P
  obtain ⟨u, hu, huneg⟩ := hg
  refine ⟨fun z => f z * u z, ?_, huneg.mul_polyGrowth hfg⟩
  rw [← hu, ← hf]
  rfl

/-- Multiplying a negligible germ by the germ of a function of polynomial growth. -/
theorem IsGermNegligible.mul_coe {g : Germ upperEndFilter ℂ} (hg : IsGermNegligible g)
    {f : ℂ → ℂ} (hf : HasTubePolyGrowth f) :
    IsGermNegligible ((f : Germ upperEndFilter ℂ) * g) := by
  obtain ⟨u, hu, huneg⟩ := hg
  refine ⟨fun z => f z * u z, ?_, huneg.mul_polyGrowth hf⟩
  rw [← hu]
  rfl

end

end GaloisForLFunctions.HTGeometry
