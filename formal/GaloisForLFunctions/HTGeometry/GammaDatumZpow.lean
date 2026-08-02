import GaloisForLFunctions.HTGeometry.UniformGammaDatumHom

/-!
# The monomial normal form of a Gamma-field element

Every power of `Γ` has datum `(n, 0, 0)` with residue `1`, so dividing an element by the power of `Γ`
its datum prescribes leaves an element of `Γ`-exponent zero.  That is the group-level form of eq. (3):
a nonzero element of `K_Γ` is `Γ^k` times something with no exponential direction left.
-/

open Filter Set Topology Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance gammaZpowDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance gammaZpowIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance gammaZpowDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance gammaZpowComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance gammaZpowRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance gammaZpowRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance gammaZpowRatFuncDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

/-- A natural power of `Γ` has datum `(n, 0, 0)` and residue `1`. -/
theorem hasGammaTubeDatum_gammaPow {M : ℝ} (n : ℕ) :
    HasGammaTubeDatum M (gammaUpperMero ^ n) (n : ℤ) 0 0 1 := by
  induction n with
  | zero =>
      simpa using (hasGammaTubeDatum_one (M := M))
  | succ n ih =>
      have hstep := ih.mul (hasGammaTubeDatum_gammaUpperMero (M := M))
      have hcast : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hcast] at hstep
      simpa [pow_succ] using hstep

/-- An integer power of `Γ` has datum `(n, 0, 0)` and residue `1`. -/
theorem hasGammaTubeDatum_gammaZpow {M : ℝ} (hM : 0 < M) (n : ℤ) :
    HasGammaTubeDatum M (gammaUpperMero ^ n) n 0 0 1 := by
  obtain ⟨m, hm | hm⟩ := n.eq_nat_or_neg
  · subst hm
    rw [zpow_natCast]
    exact hasGammaTubeDatum_gammaPow m
  · subst hm
    have hinv := (hasGammaTubeDatum_gammaPow (M := M) m).inv hM
    rw [zpow_neg, zpow_natCast]
    simpa using hinv

/-- **The monomial normal form.**  A nonzero element of the Gamma field is an integer power of `Γ`
times an element whose datum has `Γ`-exponent zero. -/
theorem exists_gammaZpow_normal_form {M : ℝ} (hM : 0 < M) {x : upperEndMeroField}
    (hx : x ∈ differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
    (hx0 : x ≠ 0) :
    ∃ (k a b : ℤ) (c : ℂ) (y : upperEndMeroField),
      y ∈ differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField)
        ∧ x = gammaUpperMero ^ k * y ∧ HasGammaTubeDatum M y 0 a b c := by
  classical
  obtain ⟨k, a, b, c, hdat⟩ := exists_hasGammaTubeDatum hM hx hx0
  have hΓmem : gammaUpperMero ∈ differentialAdjoin (RatFunc ℂ)
      ({gammaUpperMero} : Set upperEndMeroField) :=
    subset_differentialAdjoin (RatFunc ℂ) _ (Set.mem_singleton _)
  have hΓ0 : gammaUpperMero ≠ 0 := gammaUpperMero_ne_zero
  refine ⟨k, a, b, c, gammaUpperMero ^ (-k) * x, mul_mem (zpow_mem hΓmem _) hx, ?_, ?_⟩
  · rw [← mul_assoc, ← zpow_add₀ hΓ0]
    simp
  · have hmul := (hasGammaTubeDatum_gammaZpow hM (-k)).mul hdat
    simpa using hmul

end

end GaloisForLFunctions.HTGeometry
