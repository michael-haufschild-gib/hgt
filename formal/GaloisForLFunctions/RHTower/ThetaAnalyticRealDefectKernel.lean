import GaloisForLFunctions.RHTower.SlabMassSquareCertificate
import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# The analytic-to-real theta-defect comparison has the off-real divisor as kernel

The semisimplification of the analytic cokernel of multiplication by the centered completed zeta
function has algebraic core the direct sum of one complex line per distinct zero.  The comparison
to the positive real-boundary defect is restriction to the real spectral axis.

Its kernel is exactly the sum of the nonreal zero fibers, its range is exactly the real fibers, and
it is faithful precisely when every centered zero is real — that is, precisely under the Riemann
hypothesis.  The comparison therefore supplies no intermediate localization law: its missing
injectivity *is* the absence of off-line zeros.
-/

noncomputable section

namespace RHTower

/-- The distinct complex zero set of the centered completed zeta function. -/
private def xiZeroSet : Set ℂ := {z : ℂ | XiC z = 0}

instance : DecidablePred (fun ρ : xiZeroSet => (ρ : ℂ).im = 0) :=
  fun _ => Classical.dec _

/-- Algebraic core of the analytic semisimple defect: one complex line per distinct zero. -/
abbrev analyticDefectCore : Type := xiZeroSet →₀ ℂ

/-- The canonical comparison to the real-boundary defect: restriction to the real spectral axis. -/
def realBoundaryComparison : analyticDefectCore →ₗ[ℂ] analyticDefectCore where
  toFun f := Finsupp.filter (fun ρ : xiZeroSet => (ρ : ℂ).im = 0) f
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

@[simp]
theorem realBoundaryComparison_apply (f : analyticDefectCore) (ρ : xiZeroSet) :
    realBoundaryComparison f ρ = if (ρ : ℂ).im = 0 then f ρ else 0 :=
  Finsupp.filter_apply _ _ _

/-- A real zero fiber is preserved exactly. -/
theorem realBoundaryComparison_single_real {ρ : xiZeroSet} (hρ : (ρ : ℂ).im = 0) (c : ℂ) :
    realBoundaryComparison (Finsupp.single ρ c) = Finsupp.single ρ c :=
  Finsupp.filter_single_of_pos _ hρ

/-- A nonreal zero fiber is annihilated. -/
theorem realBoundaryComparison_single_nonreal {ρ : xiZeroSet} (hρ : ¬ (ρ : ℂ).im = 0) (c : ℂ) :
    realBoundaryComparison (Finsupp.single ρ c) = 0 :=
  Finsupp.filter_single_of_neg _ hρ

/-- **Kernel.**  The comparison kills exactly the elements supported on nonreal zeros. -/
theorem mem_ker_realBoundaryComparison_iff (f : analyticDefectCore) :
    f ∈ LinearMap.ker realBoundaryComparison ↔ ∀ ρ ∈ f.support, ¬ (ρ : ℂ).im = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h ρ hρ hreal
    have := congrArg (fun g : analyticDefectCore => g ρ) h
    simp only [realBoundaryComparison_apply, if_pos hreal, Finsupp.coe_zero,
      Pi.zero_apply] at this
    exact (Finsupp.mem_support_iff.mp hρ) this
  · intro h
    refine Finsupp.ext fun ρ => ?_
    simp only [realBoundaryComparison_apply, Finsupp.coe_zero, Pi.zero_apply]
    by_cases hreal : (ρ : ℂ).im = 0
    · rw [if_pos hreal]
      by_contra hne
      exact h ρ (Finsupp.mem_support_iff.mpr hne) hreal
    · rw [if_neg hreal]

/-- **Range.**  The image is exactly the real-boundary defect core. -/
theorem mem_range_realBoundaryComparison_iff (f : analyticDefectCore) :
    f ∈ LinearMap.range realBoundaryComparison ↔ ∀ ρ ∈ f.support, (ρ : ℂ).im = 0 := by
  constructor
  · rintro ⟨g, rfl⟩ ρ hρ
    by_contra hreal
    have hzero : realBoundaryComparison g ρ = 0 := by
      simp [realBoundaryComparison_apply, if_neg hreal]
    exact (Finsupp.mem_support_iff.mp hρ) hzero
  · intro h
    refine ⟨f, ?_⟩
    refine Finsupp.ext fun ρ => ?_
    simp only [realBoundaryComparison_apply]
    by_cases hreal : (ρ : ℂ).im = 0
    · rw [if_pos hreal]
    · rw [if_neg hreal]
      by_contra hne
      exact hreal (h ρ (Finsupp.mem_support_iff.mpr fun hzero => hne hzero.symm))

/-- **Faithfulness is reality of the divisor.** -/
theorem injective_realBoundaryComparison_iff :
    Function.Injective realBoundaryComparison ↔ ∀ z : ℂ, XiC z = 0 → z.im = 0 := by
  constructor
  · intro hinj z hz
    by_contra hne
    have hmem : z ∈ xiZeroSet := hz
    have hzero : realBoundaryComparison (Finsupp.single (⟨z, hmem⟩ : xiZeroSet) 1) = 0 :=
      realBoundaryComparison_single_nonreal hne 1
    have hzero' : realBoundaryComparison (0 : analyticDefectCore) = 0 := map_zero _
    have := hinj (hzero.trans hzero'.symm)
    exact (Finsupp.single_ne_zero.mpr one_ne_zero) this
  · intro hreal
    have hid : realBoundaryComparison = LinearMap.id := by
      refine LinearMap.ext fun f => ?_
      refine Finsupp.ext fun ρ => ?_
      simp only [realBoundaryComparison_apply, LinearMap.id_coe, id_eq]
      rw [if_pos (hreal (ρ : ℂ) ρ.2)]
    rw [hid]
    exact fun _ _ h => h

/-- **RH equivalence.**  The analytic-to-real defect comparison is faithful exactly under the
Riemann hypothesis. -/
theorem injective_realBoundaryComparison_iff_riemannHypothesis :
    Function.Injective realBoundaryComparison ↔ RiemannHypothesis := by
  rw [injective_realBoundaryComparison_iff,
    SlabMassSquareCertificate.riemannHypothesis_iff_xiC_zero_im_eq_zero]

end RHTower
