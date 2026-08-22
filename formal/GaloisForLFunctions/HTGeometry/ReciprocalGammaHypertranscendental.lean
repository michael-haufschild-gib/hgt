import GaloisForLFunctions.HTGeometry.GammaHypertranscendental
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicPropagation
import GaloisForLFunctions.HTGeometry.ReciprocalSubstitutionInjective
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles
import GaloisForLFunctions.HTGeometry.GammaDifferentialFE
import GaloisForLFunctions.HTGeometry.AnalyticJetFieldBridge

/-!
# Hypertranscendence of the reciprocal Gamma function, and additive closure on a domain

`1/Γ` is entire, so a differential relation for it on any nonempty open set already holds on the
whole plane.  Inverting such a relation on the right half plane gives one for `Γ`, which propagates
across the connected pole complement; multiplying by the `Γ`-slot variable extends it over the
poles, where `Γ` vanishes.  Hölder's theorem then forbids it.

The same file records the additive and subtractive closure of differential algebraicity on an
arbitrary domain, which the corpus previously had only for entire functions.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set
open GaloisForLFunctions Bottcher
open scoped Differential

noncomputable section

/-- The pole set of `Γ`. -/
def gammaPoleSet : Set ℂ := Set.range fun m : ℕ => -(m : ℂ)

theorem mem_gammaPoleSet_compl_iff {z : ℂ} :
    z ∈ (gammaPoleSet)ᶜ ↔ ∀ m : ℕ, z ≠ -(m : ℂ) := by
  simp only [gammaPoleSet, Set.mem_compl_iff, Set.mem_range, not_exists]
  exact ⟨fun h m hm => h m hm.symm, fun h m hm => h m hm.symm⟩

theorem isOpen_gammaPoleSet_compl : IsOpen (gammaPoleSet)ᶜ := by
  have h : (gammaPoleSet)ᶜ = {z : ℂ | ∀ n : ℕ, z ≠ -(n : ℂ)} := by
    ext z
    exact mem_gammaPoleSet_compl_iff
  rw [h]
  exact GaloisForLFunctions.offPoles_isOpen

theorem isPreconnected_gammaPoleSet_compl : IsPreconnected (gammaPoleSet)ᶜ := by
  refine (Set.Countable.isPathConnected_compl_of_one_lt_rank ?_
    (Set.countable_range _)).isConnected.isPreconnected
  rw [Complex.rank_real_complex]
  norm_num

theorem analyticOnNhd_gamma_off_poles : AnalyticOnNhd ℂ Complex.Gamma (gammaPoleSet)ᶜ :=
  fun _ hz => HTGeometry.analyticAt_Gamma_off_poles (mem_gammaPoleSet_compl_iff.1 hz)

/-- **The reciprocal Gamma function is hypertranscendental.**  A relation for `1/Γ` inverts to a
relation for `Γ` on the right half plane, propagates across the connected pole complement, and the
extra factor `X₁` extends it over the poles, where `Γ` vanishes.  Hölder's theorem then applies. -/
theorem hypertranscendental_invGamma :
    Hypertranscendental (fun z => (Complex.Gamma z)⁻¹) := by
  intro hDA
  obtain ⟨n, P, hP0, hPv⟩ := hDA
  set W : Set ℂ := {z : ℂ | 0 < z.re} with hW
  have hWopen : IsOpen W := isOpen_lt continuous_const Complex.continuous_re
  have hWne : W.Nonempty := ⟨1, by simp [hW]⟩
  have hWsub : W ⊆ (gammaPoleSet)ᶜ := fun z hz =>
    mem_gammaPoleSet_compl_iff.2 (HTGeometry.ne_neg_natCast_of_re_pos hz)
  have hinvan : AnalyticOnNhd ℂ (fun z => (Complex.Gamma z)⁻¹) W := fun z _ =>
    (Complex.differentiable_one_div_Gamma.differentiableOn.analyticOnNhd isOpen_univ) z
      (Set.mem_univ z)
  have hne : ∀ z ∈ W, (Complex.Gamma z)⁻¹ ≠ 0 := fun z hz =>
    inv_ne_zero (Complex.Gamma_ne_zero (HTGeometry.ne_neg_natCast_of_re_pos hz))
  have hDAW : DifferentiallyAlgebraicOn (fun z => (Complex.Gamma z)⁻¹) W :=
    ⟨n, P, hP0, fun z _ => hPv z⟩
  have hGammaW : DifferentiallyAlgebraicOn Complex.Gamma W := by
    have h := differentiallyAlgebraicOn_inv hWopen hinvan hne hDAW
    have heq : (fun z => ((Complex.Gamma z)⁻¹)⁻¹) = Complex.Gamma := by
      funext z
      rw [inv_inv]
    rwa [heq] at h
  obtain ⟨m, Q, hQ0, hQv⟩ := differentiallyAlgebraicOn_mono_of_isPreconnected
    isPreconnected_gammaPoleSet_compl analyticOnNhd_gamma_off_poles hWopen hWne hWsub hGammaW
  refine hypertranscendental_gamma ⟨m, Q * MvPolynomial.X 1, mul_ne_zero hQ0
    (MvPolynomial.X_ne_zero _), ?_⟩
  intro z
  rw [map_mul, MvPolynomial.eval_X]
  by_cases hz : z ∈ (gammaPoleSet)ᶜ
  · rw [hQv z hz, zero_mul]
  · have hpole : ∃ mm : ℕ, z = -(mm : ℂ) := by
      by_contra hcon
      exact hz (mem_gammaPoleSet_compl_iff.2 fun mm hmm => hcon ⟨mm, hmm⟩)
    obtain ⟨mm, rfl⟩ := hpole
    have : (Fin.cons (-(mm : ℂ)) (fun j : Fin (m + 1) =>
        iteratedDeriv (j : ℕ) Complex.Gamma (-(mm : ℂ))) : Fin (m + 2) → ℂ) 1 = 0 := by
      rw [show (1 : Fin (m + 2)) = (0 : Fin (m + 1)).succ from rfl, Fin.cons_succ]
      simpa using Complex.Gamma_neg_nat_eq_zero mm
    rw [this, mul_zero]

/-- **The reciprocal Gamma function satisfies no algebraic differential equation on any nonempty
open set.**  Its jet evaluation is entire, so a local relation propagates to the whole plane. -/
theorem not_differentiallyAlgebraicOn_invGamma {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) :
    ¬ DifferentiallyAlgebraicOn (fun z => (Complex.Gamma z)⁻¹) U := by
  intro hDA
  have hinvan : AnalyticOnNhd ℂ (fun z => (Complex.Gamma z)⁻¹) Set.univ := fun z _ =>
    (Complex.differentiable_one_div_Gamma.differentiableOn.analyticOnNhd isOpen_univ) z
      (Set.mem_univ z)
  obtain ⟨n, P, hP0, hPv⟩ := differentiallyAlgebraicOn_mono_of_isPreconnected
    isPreconnected_univ hinvan hU hUne (Set.subset_univ U) hDA
  exact hypertranscendental_invGamma ⟨n, P, hP0, fun z => hPv z (Set.mem_univ z)⟩

/-! ### Additive closure of domain differential algebraicity -/

theorem differentiallyAlgebraicOn_add {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hfDA : DifferentiallyAlgebraicOn f U) (hgDA : DifferentiallyAlgebraicOn g U) :
    DifferentiallyAlgebraicOn (fun z => f z + g z) U := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  letI : Differential (RatFunc ℂ) := ratFuncCoordinateDifferential
  letI := meroFieldDifferential (U := U) hUo hUc hUne
  letI : DifferentialAlgebra (RatFunc ℂ) (meroField U) :=
    meroFieldRatFuncDifferentialAlgebra hUo hUc hUne hUinf
  letI : CharZero (meroField U) :=
    charZero_of_injective_algebraMap (algebraMap (RatFunc ℂ) (meroField U)).injective
  have hadd : AnalyticOnNhd ℂ (fun z => f z + g z) U := hf.add hg
  refine (differentialAlgebraicOver_analyticMeroElement_iff hUo hUc hUne hUinf hadd).1 ?_
  rw [analyticMeroElement_add hf hg]
  exact differentialAlgebraicOver_add
    ((differentialAlgebraicOver_analyticMeroElement_iff hUo hUc hUne hUinf hf).2 hfDA)
    ((differentialAlgebraicOver_analyticMeroElement_iff hUo hUc hUne hUinf hg).2 hgDA)

theorem differentiallyAlgebraicOn_sub {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hfDA : DifferentiallyAlgebraicOn f U) (hgDA : DifferentiallyAlgebraicOn g U) :
    DifferentiallyAlgebraicOn (fun z => f z - g z) U := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  letI : Differential (RatFunc ℂ) := ratFuncCoordinateDifferential
  letI := meroFieldDifferential (U := U) hUo hUc hUne
  letI : DifferentialAlgebra (RatFunc ℂ) (meroField U) :=
    meroFieldRatFuncDifferentialAlgebra hUo hUc hUne hUinf
  letI : CharZero (meroField U) :=
    charZero_of_injective_algebraMap (algebraMap (RatFunc ℂ) (meroField U)).injective
  have hsub : AnalyticOnNhd ℂ (fun z => f z - g z) U := hf.sub hg
  refine (differentialAlgebraicOver_analyticMeroElement_iff hUo hUc hUne hUinf hsub).1 ?_
  rw [analyticMeroElement_sub hf hg]
  exact differentialAlgebraicOver_sub
    ((differentialAlgebraicOver_analyticMeroElement_iff hUo hUc hUne hUinf hf).2 hfDA)
    ((differentialAlgebraicOver_analyticMeroElement_iff hUo hUc hUne hUinf hg).2 hgDA)

end

end GaloisForLFunctions.HTGeometry
