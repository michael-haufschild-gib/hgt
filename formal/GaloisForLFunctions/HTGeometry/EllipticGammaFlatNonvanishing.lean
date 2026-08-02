import GaloisForLFunctions.HTGeometry.ZeroNomeBoundaryDifferentialAlgebraic
import GaloisForLFunctions.HTGeometry.EllipticGammaReciprocalNome

/-!
# The flat difference does not vanish

If the multiple elliptic Gamma product agreed with its zero-nome boundary on the disk, the identity
theorem would make the two entire objects equal, and the boundary is differentially algebraic while
the reciprocal fibre is hypertranscendental.

So the flat section of the bornological Krull radical is genuinely nonzero: at every scaling
parameter there is a point of the disk where the fibre differs from its boundary.
-/

open Filter Topology Set Function Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

/-- The polynomial embedding sends a constant to the constant germ. -/
theorem polyToAnalytic_C (c : ℂ) :
    polyToAnalytic (Set.univ : Set ℂ) (Polynomial.C c) = constToAnalytic Set.univ c := by
  apply Subtype.ext
  change ((fun z : ℂ => (Polynomial.C c).eval z : ℂ → ℂ) : Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
    = ((fun _ : ℂ => c : ℂ → ℂ) : Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
  rw [Germ.coe_eq]
  refine eventually_principal.mpr fun z _ => ?_
  simp

/-- The two constant embeddings into the meromorphic field agree. -/
theorem ratfunc_algebraMap_complex (c : ℂ) :
    algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (algebraMap ℂ (RatFunc ℂ) c)
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) c := by
  have hC : algebraMap ℂ (RatFunc ℂ) c
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) := by
    simp
  change ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
      Set.infinite_univ (algebraMap ℂ (RatFunc ℂ) c) = _
  rw [hC, ratfuncToMero_algebraMap_polynomial]
  change (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ))
      (polyToAnalytic Set.univ (Polynomial.C c)) = _
  rw [polyToAnalytic_C]
  rfl

local instance zeroNomeScalarTower :
    IsScalarTower ℂ (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  IsScalarTower.of_algebraMap_eq fun c => (ratfunc_algebraMap_complex c).symm

/-- Differential algebraicity over the constants upgrades to the rational coordinate field. -/
theorem differentialAlgebraicOver_ratFunc_of_complex {y : meroField (Set.univ : Set ℂ)}
    (h : DifferentialAlgebraicOver ℂ y) : DifferentialAlgebraicOver (RatFunc ℂ) y := by
  intro hindep
  exact h (hindep.restrictScalars (algebraMap ℂ (RatFunc ℂ)).injective)

/-- **The zero-nome boundary is differentially algebraic over the coordinate field.** -/
theorem differentialAlgebraicOver_ratFunc_zeroNomeMero :
    DifferentialAlgebraicOver (RatFunc ℂ) zeroNomeMero :=
  differentialAlgebraicOver_ratFunc_of_complex differentialAlgebraicOver_zeroNomeMero

/-- The zero-nome boundary is a nonzero analytic germ. -/
theorem zeroNomeAnalytic_ne_zero : zeroNomeAnalytic ≠ 0 := by
  intro hzero
  have hv := congrArg Subtype.val hzero
  change ((fun z : ℂ => 1 - multipleEllipticGammaCoordinate z : ℂ → ℂ)
      : Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
    = ((fun _ : ℂ => 0 : ℂ → ℂ) : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) at hv
  rw [Germ.coe_eq] at hv
  have hval := eventually_principal.mp hv (1 / 2 : ℂ) (Set.mem_univ _)
  have hexp : multipleEllipticGammaCoordinate (1 / 2 : ℂ) = -1 := by
    show Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (1 / 2 : ℂ)) = -1
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (1 / 2 : ℂ) = (Real.pi : ℂ) * Complex.I by ring]
    exact Complex.exp_pi_mul_I
  have hval' : 1 - multipleEllipticGammaCoordinate (1 / 2 : ℂ) = 0 := hval
  rw [hexp] at hval'
  norm_num at hval'

theorem zeroNomeMero_ne_zero : zeroNomeMero ≠ 0 := by
  rw [zeroNomeMero]
  intro hzero
  exact zeroNomeAnalytic_ne_zero
    ((meroField_algebraMap_eq_zero_iff Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty _).mp hzero)

/-- **The inverse boundary is differentially algebraic.** -/
theorem differentialAlgebraicOver_zeroNomeMeroInv :
    DifferentialAlgebraicOver ℂ zeroNomeMero⁻¹ := by
  refine differentialAlgebraicOver_of_deriv_quadratic
    (c₂ := 2 * (Real.pi : ℂ) * Complex.I) (c₁ := -(2 * (Real.pi : ℂ) * Complex.I))
    (c₀ := 0) ?_
  have hne := zeroNomeMero_ne_zero
  have hinv : (zeroNomeMero⁻¹)′ = -zeroNomeMero⁻¹ ^ 2 * (zeroNomeMero)′ := by
    letI : Algebra ℤ (meroField (Set.univ : Set ℂ)) := Ring.toIntAlgebra _
    simpa [smul_eq_mul] using Differential.deriv.leibniz_inv zeroNomeMero
  rw [hinv, deriv_zeroNomeMero, map_zero, map_neg, add_zero]
  have hmul : zeroNomeMero⁻¹ * zeroNomeMero = 1 := inv_mul_cancel₀ hne
  field_simp
  ring

theorem differentialAlgebraicOver_ratFunc_zeroNomeMeroInv :
    DifferentialAlgebraicOver (RatFunc ℂ) zeroNomeMero⁻¹ :=
  differentialAlgebraicOver_ratFunc_of_complex differentialAlgebraicOver_zeroNomeMeroInv

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Two entire functions agreeing on the flat disk agree everywhere. -/
theorem eq_of_eqOn_flatDisk {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : ∀ z ∈ flatDisk, f z = g z) : f = g := by
  have hfa : AnalyticOnNhd ℂ f Set.univ :=
    (Complex.analyticOnNhd_univ_iff_differentiable).mpr hf
  have hga : AnalyticOnNhd ℂ g Set.univ :=
    (Complex.analyticOnNhd_univ_iff_differentiable).mpr hg
  have hnhds : f =ᶠ[nhds Complex.I] g := by
    refine Filter.eventually_of_mem
      (Metric.closedBall_mem_nhds Complex.I (ε := 1 / 4) (by norm_num)) ?_
    intro z hz
    exact h z hz
  have hEq := hfa.eqOn_of_preconnected_of_eventuallyEq hga isPreconnected_univ
    (Set.mem_univ Complex.I) hnhds
  funext z
  exact hEq (Set.mem_univ z)

omit [DecidableEq ι] in
/-- **The odd-parity identity transfer.**  If the product agrees with its boundary on the disk, the
two meromorphic-field elements are equal. -/
theorem multipleEllipticGammaMero_eq_zeroNomeMero_of_odd {τ : ι → ℂ} (hτ : ∀ i, 0 < (τ i).im)
    (hodd : ¬ Even (Fintype.card ι))
    (heq : ∀ z ∈ flatDisk, multipleEllipticGammaProduct τ z = zeroNomeBoundary ι z) :
    multipleEllipticGammaMero τ hτ = zeroNomeMero := by
  have hfun : (fun z : ℂ => multipleEllipticGammaForwardProduct τ z
      * multipleEllipticGammaBackwardProduct τ z)
      = fun z : ℂ => 1 - multipleEllipticGammaCoordinate z := by
    refine eq_of_eqOn_flatDisk ?_ ?_ ?_
    · exact (differentiable_multipleEllipticGammaForwardProduct hτ).mul
        (differentiable_multipleEllipticGammaBackwardProduct hτ)
    · exact (differentiable_const 1).sub
        ((differentiable_const _).mul differentiable_id).cexp
    · intro z hz
      have h := heq z hz
      rw [multipleEllipticGammaProduct, if_neg hodd, zeroNomeBoundary, if_neg hodd] at h
      exact h
  have hanalytic : multipleEllipticGammaForwardAnalytic τ hτ
      * multipleEllipticGammaBackwardAnalytic τ hτ = zeroNomeAnalytic := by
    apply Subtype.ext
    change ((fun z : ℂ => multipleEllipticGammaForwardProduct τ z
        * multipleEllipticGammaBackwardProduct τ z : ℂ → ℂ)
      : Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
      = ((fun z : ℂ => 1 - multipleEllipticGammaCoordinate z : ℂ → ℂ)
        : Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
    rw [hfun]
  rw [multipleEllipticGammaMero, if_neg hodd, zeroNomeMero, ← hanalytic, map_mul]

omit [DecidableEq ι] in
/-- **The flat difference is nonzero at odd nome count.**  A hypertranscendental fibre cannot agree
with its differentially algebraic boundary on the disk. -/
theorem exists_flat_difference_ne_zero_odd {τ : ι → ℂ} (hτ : ∀ i, 0 < (τ i).im)
    (hodd : ¬ Even (Fintype.card ι))
    (hHT : HypertranscendentalOver (RatFunc ℂ) (multipleEllipticGammaMero τ hτ)) :
    ∃ z ∈ flatDisk, multipleEllipticGammaProduct τ z ≠ zeroNomeBoundary ι z := by
  by_contra hcontra
  have hall : ∀ z ∈ flatDisk, multipleEllipticGammaProduct τ z = zeroNomeBoundary ι z := by
    intro z hz
    by_contra hne
    exact hcontra ⟨z, hz, hne⟩
  have heq := multipleEllipticGammaMero_eq_zeroNomeMero_of_odd hτ hodd hall
  refine hHT ?_
  rw [heq]
  exact differentialAlgebraicOver_ratFunc_zeroNomeMero

omit [DecidableEq ι] in
/-- **The even-parity identity transfer.**  If the quotient agrees with the inverse boundary on the
disk, the two meromorphic-field elements are equal. -/
theorem multipleEllipticGammaMero_eq_zeroNomeMeroInv_of_even {τ : ι → ℂ}
    (hτ : ∀ i, 0 < (τ i).im) (heven : Even (Fintype.card ι))
    (heq : ∀ z ∈ flatDisk, multipleEllipticGammaProduct τ z = zeroNomeBoundary ι z) :
    multipleEllipticGammaMero τ hτ = zeroNomeMero⁻¹ := by
  have hfun : (fun z : ℂ => multipleEllipticGammaForwardProduct τ z
      * (1 - multipleEllipticGammaCoordinate z))
      = fun z : ℂ => multipleEllipticGammaBackwardProduct τ z := by
    refine eq_of_eqOn_flatDisk ?_ ?_ ?_
    · exact (differentiable_multipleEllipticGammaForwardProduct hτ).mul
        ((differentiable_const 1).sub ((differentiable_const _).mul differentiable_id).cexp)
    · exact differentiable_multipleEllipticGammaBackwardProduct hτ
    · intro z hz
      have h := heq z hz
      rw [multipleEllipticGammaProduct, if_pos heven, zeroNomeBoundary, if_pos heven] at h
      have hx : (1 : ℂ) - multipleEllipticGammaCoordinate z ≠ 0 :=
        one_sub_coordinate_ne_zero_of_mem hz
      have hB : multipleEllipticGammaBackwardProduct τ z ≠ 0 := by
        intro h0
        rw [h0, div_zero] at h
        exact (inv_ne_zero hx) h.symm
      field_simp at h
      linear_combination h
  have hanalytic : multipleEllipticGammaForwardAnalytic τ hτ * zeroNomeAnalytic
      = multipleEllipticGammaBackwardAnalytic τ hτ := by
    apply Subtype.ext
    change ((fun z : ℂ => multipleEllipticGammaForwardProduct τ z
        * (1 - multipleEllipticGammaCoordinate z) : ℂ → ℂ)
      : Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
      = ((fun z : ℂ => multipleEllipticGammaBackwardProduct τ z : ℂ → ℂ)
        : Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
    rw [hfun]
  have hBne : algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
      (multipleEllipticGammaBackwardAnalytic τ hτ) ≠ 0 := by
    intro h0
    exact multipleEllipticGammaBackwardAnalytic_ne_zero τ hτ
      ((meroField_algebraMap_eq_zero_iff Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty _).mp h0)
  rw [multipleEllipticGammaMero, if_pos heven]
  rw [div_eq_iff hBne, inv_mul_eq_div, eq_div_iff zeroNomeMero_ne_zero, zeroNomeMero,
    ← map_mul, hanalytic]

omit [DecidableEq ι] in
/-- **The flat difference is nonzero at even nome count.** -/
theorem exists_flat_difference_ne_zero_even {τ : ι → ℂ} (hτ : ∀ i, 0 < (τ i).im)
    (heven : Even (Fintype.card ι))
    (hHT : HypertranscendentalOver (RatFunc ℂ) (multipleEllipticGammaMero τ hτ)) :
    ∃ z ∈ flatDisk, multipleEllipticGammaProduct τ z ≠ zeroNomeBoundary ι z := by
  by_contra hcontra
  have hall : ∀ z ∈ flatDisk, multipleEllipticGammaProduct τ z = zeroNomeBoundary ι z := by
    intro z hz
    by_contra hne
    exact hcontra ⟨z, hz, hne⟩
  have heq := multipleEllipticGammaMero_eq_zeroNomeMeroInv_of_even hτ heven hall
  refine hHT ?_
  rw [heq]
  exact differentialAlgebraicOver_ratFunc_zeroNomeMeroInv

omit [DecidableEq ι] in
/-- **The flat difference never vanishes on the disk.**  Whatever the parity, a hypertranscendental
fibre differs from its zero-nome boundary somewhere on the disk. -/
theorem exists_flat_difference_ne_zero {τ : ι → ℂ} (hτ : ∀ i, 0 < (τ i).im)
    (hHT : HypertranscendentalOver (RatFunc ℂ) (multipleEllipticGammaMero τ hτ)) :
    ∃ z ∈ flatDisk, multipleEllipticGammaProduct τ z ≠ zeroNomeBoundary ι z := by
  by_cases heven : Even (Fintype.card ι)
  · exact exists_flat_difference_ne_zero_even hτ heven hHT
  · exact exists_flat_difference_ne_zero_odd hτ heven hHT

/-- **Equation (9): every coordinate of the flat section is nonzero.**  For a reciprocalized packet
of pairwise distinct integer shifts of a transcendental period, at every scaling parameter the
multiple elliptic Gamma fibre differs from its zero-nome boundary somewhere on the disk. -/
theorem exists_reciprocal_flat_difference_ne_zero {N : ℕ} {omega : ℂ}
    (homega : Transcendental ℚ omega) (himω : 0 < omega.im) {n : Fin N → ℤ}
    (hn : Function.Injective n) (hN : 2 ≤ N) {m : ℕ} (hm : 0 < m) :
    ∃ z ∈ flatDisk, multipleEllipticGammaProduct (inversePeriod omega n m) z
      ≠ zeroNomeBoundary (Fin N) z := by
  obtain ⟨-, hHT, -⟩ := inversePeriod_hypertranscendental homega himω hn hm hN
  exact exists_flat_difference_ne_zero (inversePeriod_im_pos homega himω n hm) hHT

end

end GaloisForLFunctions.HTGeometry
