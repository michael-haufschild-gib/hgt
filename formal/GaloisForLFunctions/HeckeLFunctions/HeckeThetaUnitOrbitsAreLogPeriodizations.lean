import GaloisForLFunctions.HeckeLFunctions.HeckeThetaAveragesOverTheUnitDomain
import GaloisForLFunctions.HeckeLFunctions.NonzeroIdealElementsAreGlobalUnitOrbits
import GaloisForLFunctions.HTGeometry.NumberFieldUnitsAreTorsionTimesLogLattice

/-!
# Hecke theta unit orbits are logarithmic periodizations

The actual ideal Gaussian series gives absolute convergence on every nonzero unit orbit.
The exact torsion/lattice equivalence and unit covariance turn each orbit into a logarithmic
lattice periodization with coefficient equal to the torsion order. Removing the zero term and
using the inverse-class generator equivalence expresses the entire nonzero ideal theta as
an absolutely convergent sum of these periodizations.
-/

noncomputable section
open NumberField NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open MeasureTheory Set
open scoped Classical nonZeroDivisors
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry
variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-- Multiplication by a nonzero ideal element embeds the actual unit group in that ideal. -/
def unitOrbitInIdeal {b : Ideal (𝓞 K)} (a : nonzeroIdealElements b)
    (u : (𝓞 K)ˣ) : b :=
  ⟨(u : 𝓞 K) * a.1, b.mul_mem_left _ a.2.1⟩

omit [NumberField K] in
/-- Nonzero cancellation makes the unit-orbit embedding injective. -/
theorem unitOrbitInIdeal_injective {b : Ideal (𝓞 K)} (a : nonzeroIdealElements b) :
    Function.Injective (unitOrbitInIdeal a) := by
  intro u v h
  apply Units.ext
  exact mul_right_cancel₀ a.2.2 (congrArg Subtype.val h)

/-- Absolute convergence of the ideal series restricts to each nonzero unit orbit. -/
theorem summable_norm_heckeThetaUnitOrbit (ψ : HeckeCharacter 𝔪)
    {b : Ideal (𝓞 K)} (a : nonzeroIdealElements b)
    (y : InfinitePlace K → ℝ) {t : ℝ} (ht : 0 < t) :
    Summable (fun u : (𝓞 K)ˣ => ‖heckeThetaKernel 𝔪 ψ y t ((u : 𝓞 K) * a.1)‖) := by
  have hs := (summable_norm_heckeThetaKernel 𝔪 ψ b y ht).comp_injective
    (i := unitOrbitInIdeal a) (unitOrbitInIdeal_injective a)
  simpa only [Function.comp_def, unitOrbitInIdeal] using hs

/-- Multiplying the argument by a unit translates the logarithmic kernel by its negative logarithm. -/
theorem heckeThetaKernel_unit_as_logTranslate (ψ : HeckeCharacter 𝔪)
    (x : logSpace K) (u : (𝓞 K)ˣ) (t : ℝ) (a : 𝓞 K) :
    heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile x) t ((u : 𝓞 K) * a) =
      heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile
        (x - Units.logEmbedding K (Additive.ofMul u))) t a := by
  simpa only [sub_add_cancel] using
    heckeThetaKernel_unitLog 𝔪 ψ (x - Units.logEmbedding K (Additive.ofMul u)) u t a

/-- Under the actual torsion/lattice equivalence, the kernel depends only on the lattice coordinate. -/
theorem heckeThetaKernel_torsionLogLattice (ψ : HeckeCharacter 𝔪)
    (x : logSpace K) (t : ℝ) (a : 𝓞 K)
    (ζ : Units.torsion K) (l : Units.unitLattice K) :
    heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile x) t
      (((numberFieldUnitsEquivTorsionLogLattice (K := K)).symm (ζ, l) : 𝓞 K) * a) =
      heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile (x - (l : logSpace K))) t a := by
  rw [heckeThetaKernel_unit_as_logTranslate,
    logEmbedding_numberFieldUnitsEquivTorsionLogLattice_symm]

/-- The actual logarithmic-lattice periodization converges absolutely at every positive parameter. -/
theorem summable_norm_heckeThetaLogPeriodization (ψ : HeckeCharacter 𝔪)
    {b : Ideal (𝓞 K)} (a : nonzeroIdealElements b) (x : logSpace K)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun l : Units.unitLattice K =>
      ‖heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile (x - (l : logSpace K))) t a.1‖) := by
  let g : Units.unitLattice K → (𝓞 K)ˣ :=
    fun l => (numberFieldUnitsEquivTorsionLogLattice (K := K)).symm (1, l)
  have hg : Function.Injective g := by
    intro l m h
    exact congrArg Prod.snd ((numberFieldUnitsEquivTorsionLogLattice (K := K)).symm.injective h)
  have hs := (summable_norm_heckeThetaUnitOrbit 𝔪 ψ a
    (numberFieldWeightedLogProfile x) ht).comp_injective (i := g) hg
  simpa only [g, Function.comp_def, heckeThetaKernel_torsionLogLattice] using hs

/-- A unit orbit is the logarithmic-lattice periodization times the exact torsion order. -/
theorem tsum_heckeThetaUnitOrbit_eq_logPeriodization (ψ : HeckeCharacter 𝔪)
    {b : Ideal (𝓞 K)} (a : nonzeroIdealElements b) (x : logSpace K)
    {t : ℝ} (ht : 0 < t) :
    (∑' u : (𝓞 K)ˣ, heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile x) t
      ((u : 𝓞 K) * a.1)) =
      (Units.torsionOrder K : ℂ) * ∑' l : Units.unitLattice K,
        heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile (x - (l : logSpace K))) t a.1 := by
  let e := numberFieldUnitsEquivTorsionLogLattice (K := K)
  have hs := (summable_norm_heckeThetaUnitOrbit 𝔪 ψ a
    (numberFieldWeightedLogProfile x) ht).of_norm.comp_injective
      (i := e.symm) e.symm.injective
  simp only [Function.comp_def] at hs
  rw [← e.symm.tsum_eq]
  rw [hs.tsum_prod]
  dsimp only [e]
  simp_rw [heckeThetaKernel_torsionLogLattice]
  letI := Fintype.ofFinite (Units.torsion K)
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Units.torsionOrder, Nat.card_eq_fintype_card]

/-- The exact class/unit reindexing preserves the absolute convergence of the ideal kernel. -/
theorem summable_norm_heckeThetaClassUnitKernels (ψ : HeckeCharacter 𝔪)
    (b : (Ideal (𝓞 K))⁰) (y : InfinitePlace K → ℝ) {t : ℝ} (ht : 0 < t) :
    Summable (fun p : inverseClassIntegralIdeals b × (𝓞 K)ˣ =>
      ‖heckeThetaKernel 𝔪 ψ y t ((p.2 : 𝓞 K) * inverseClassGenerator b p.1)‖) := by
  let e := nonzeroIdealElementsEquivClassUnits b
  let f : inverseClassIntegralIdeals b × (𝓞 K)ˣ → (b : Ideal (𝓞 K)) :=
    fun p => ⟨(e.symm p).1, (e.symm p).2.1⟩
  have hf : Function.Injective f := by
    intro p q h
    apply e.symm.injective
    exact Subtype.ext (congrArg (fun z : (b : Ideal (𝓞 K)) => (z : 𝓞 K)) h)
  have hs := (summable_norm_heckeThetaKernel 𝔪 ψ (b : Ideal (𝓞 K)) y ht).comp_injective
    (i := f) hf
  apply hs.congr
  rintro ⟨I, u⟩
  simp only [Function.comp_def, f, e, nonzeroIdealElementsEquivClassUnits_symm_apply]

/-- Removing the actual zero term leaves exactly the sum over nonzero ideal elements. -/
theorem heckeIdealTheta_sub_constant_eq_tsum_nonzero (ψ : HeckeCharacter 𝔪)
    (b : Ideal (𝓞 K)) (y : InfinitePlace K → ℝ) {t : ℝ} (ht : 0 < t) :
    heckeIdealTheta 𝔪 ψ b y t - heckeThetaConstant 𝔪 ψ =
      ∑' a : nonzeroIdealElements b, heckeThetaKernel 𝔪 ψ y t a.1 := by
  let e : ↥{a : b | (a : 𝓞 K) ≠ 0} ≃ nonzeroIdealElements b :=
    { toFun := fun a => ⟨a.1.1, a.1.2, a.2⟩
      invFun := fun a => ⟨⟨a.1, a.2.1⟩, a.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he : (∑' a : nonzeroIdealElements b, heckeThetaKernel 𝔪 ψ y t a.1) =
      ∑' a : b, if (a : 𝓞 K) = 0 then 0 else heckeThetaKernel 𝔪 ψ y t (a : 𝓞 K) := by
    rw [← e.tsum_eq]
    change (∑' a : ↥{a : b | (a : 𝓞 K) ≠ 0},
      heckeThetaKernel 𝔪 ψ y t (a.1 : 𝓞 K)) = _
    simpa only [Set.indicator, Set.mem_setOf_eq, ne_eq, ite_not] using
      (tsum_subtype {a : b | (a : 𝓞 K) ≠ 0}
        (fun a : b => heckeThetaKernel 𝔪 ψ y t (a : 𝓞 K)))
  have hs := (summable_norm_heckeThetaKernel 𝔪 ψ b y ht).of_norm.tsum_eq_add_tsum_ite (0 : b)
  simp only [ZeroMemClass.coe_zero, Subtype.ext_iff, heckeThetaKernel_zero] at hs
  rw [heckeIdealTheta, he]
  exact sub_eq_iff_eq_add.mpr (hs.trans (add_comm _ _))

/-- The nonzero theta series is exactly the absolutely convergent sum of its ideal-class unit orbits. -/
theorem heckeIdealTheta_sub_constant_eq_classUnitSum (ψ : HeckeCharacter 𝔪)
    (b : (Ideal (𝓞 K))⁰) (y : InfinitePlace K → ℝ) {t : ℝ} (ht : 0 < t) :
    heckeIdealTheta 𝔪 ψ (b : Ideal (𝓞 K)) y t - heckeThetaConstant 𝔪 ψ =
      ∑' I : inverseClassIntegralIdeals b, ∑' u : (𝓞 K)ˣ,
        heckeThetaKernel 𝔪 ψ y t ((u : 𝓞 K) * inverseClassGenerator b I) := by
  rw [heckeIdealTheta_sub_constant_eq_tsum_nonzero 𝔪 ψ _ y ht,
    ← (nonzeroIdealElementsEquivClassUnits b).symm.tsum_eq]
  change (∑' p : inverseClassIntegralIdeals b × (𝓞 K)ˣ,
    heckeThetaKernel 𝔪 ψ y t ((p.2 : 𝓞 K) * inverseClassGenerator b p.1)) = _
  exact (summable_norm_heckeThetaClassUnitKernels 𝔪 ψ b y ht).of_norm.tsum_prod

/-- The actual nonzero ideal theta is the torsion-weighted sum of logarithmic periodizations. -/
theorem heckeIdealTheta_sub_constant_eq_classLogPeriodizations (ψ : HeckeCharacter 𝔪)
    (b : (Ideal (𝓞 K))⁰) (x : logSpace K) {t : ℝ} (ht : 0 < t) :
    heckeIdealTheta 𝔪 ψ (b : Ideal (𝓞 K)) (numberFieldWeightedLogProfile x) t -
        heckeThetaConstant 𝔪 ψ =
      (Units.torsionOrder K : ℂ) * ∑' I : inverseClassIntegralIdeals b,
        ∑' l : Units.unitLattice K, heckeThetaKernel 𝔪 ψ
          (numberFieldWeightedLogProfile (x - (l : logSpace K))) t (inverseClassGenerator b I) := by
  rw [heckeIdealTheta_sub_constant_eq_classUnitSum 𝔪 ψ b _ ht, ← tsum_mul_left]
  apply tsum_congr
  intro I
  exact tsum_heckeThetaUnitOrbit_eq_logPeriodization 𝔪 ψ
    ⟨inverseClassGenerator b I, inverseClassGenerator_mem_ne_zero b I⟩ x ht

end GaloisForLFunctions.HeckeLFunctions
