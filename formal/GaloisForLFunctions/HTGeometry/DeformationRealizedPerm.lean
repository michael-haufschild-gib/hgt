import GaloisForLFunctions.HTGeometry.PowerSeriesRootFamilyTransfer

/-!
# A realized permutation survives one deformation variable

If the coefficients of the deformed polynomial come from the base, a base automorphism of the
residue field extends coefficientwise to the power series ring, still fixes the deformed base, and
permutes the lifted roots exactly as it permuted the residue roots.  So every permutation realized
before the deformation is realized after it, in the labelling carried along by the lift.

## Main results

* `map_eq_self_of_coeffMem` — a coefficientwise automorphism fixing the base fixes the polynomial.
* `realized_of_deformation` — the transported permutation.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F L : Type*} [Field F] [Field L]

theorem map_eq_self_of_coeffMem (ψ : F →+* L) (φ : L ≃+* L) (hfix : ∀ a, φ (ψ a) = ψ a)
    {G : Polynomial (PowerSeries L)}
    (hcoeff : ∀ j, ∃ c : PowerSeries F, G.coeff j = PowerSeries.map ψ c) :
    G.map (PowerSeries.map (φ : L →+* L)) = G := by
  refine Polynomial.ext fun j => ?_
  rw [Polynomial.coeff_map]
  obtain ⟨c, hc⟩ := hcoeff j
  rw [hc]
  ext n
  simp [PowerSeries.coeff_map, hfix]

/-- **A realized permutation survives one deformation variable.** -/
theorem realized_of_deformation (ψ : F →+* L)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {θ : ι → L} (hinj : Function.Injective θ)
    {G : Polynomial (PowerSeries L)}
    (hcoeff : ∀ j, ∃ c : PowerSeries F, G.coeff j = PowerSeries.map ψ c)
    (hres : G.map (PowerSeries.constantCoeff (R := L))
      = ∏ i, (Polynomial.X - Polynomial.C (θ i)))
    {y : ι → PowerSeries L}
    (hy : ∀ i, G.IsRoot (y i))
    (hyc : ∀ i, (PowerSeries.X : PowerSeries L) ∣ (y i - PowerSeries.C (θ i)))
    (φ : L ≃+* L) (hfix : ∀ a, φ (ψ a) = ψ a) (π : Equiv.Perm ι)
    (hπ : ∀ i, φ (θ i) = θ (π i)) :
    ∀ i, PowerSeries.map (φ : L →+* L) (y i) = y (π i) := by
  classical
  obtain ⟨y', hy', hyc', hequiv⟩ := exists_powerSeriesRootFamily G θ hinj hres
  have hsep : (G.map (PowerSeries.constantCoeff (R := L))).Separable := by
    rw [hres]
    exact Polynomial.separable_prod_X_sub_C_iff.mpr hinj
  have hrootres : ∀ k, (G.map (PowerSeries.constantCoeff (R := L))).IsRoot (θ k) := by
    intro k
    rw [hres]
    show Polynomial.eval (θ k) (∏ j, (Polynomial.X - Polynomial.C (θ j))) = 0
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  have hconstC : ∀ k, PowerSeries.constantCoeff (R := L) (PowerSeries.C (θ k)) = θ k := by
    intro k
    simp
  have hv : ∀ k, (PowerSeries.X : PowerSeries L) ∣
      Polynomial.eval (PowerSeries.C (θ k)) G := by
    intro k
    rw [PowerSeries.X_dvd_iff]
    have hmap := Polynomial.eval_map_apply (PowerSeries.constantCoeff (R := L))
      (PowerSeries.C (θ k)) (p := G)
    rw [hconstC k] at hmap
    rw [← hmap]
    exact hrootres k
  have hdu : ∀ k, IsUnit
      (Polynomial.eval (PowerSeries.C (θ k)) (Polynomial.derivative G)) := by
    intro k
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have hmap := Polynomial.eval_map_apply (PowerSeries.constantCoeff (R := L))
      (PowerSeries.C (θ k)) (p := Polynomial.derivative G)
    rw [hconstC k] at hmap
    rw [← hmap, ← Polynomial.derivative_map]
    exact (eval_derivative_ne_zero_of_separable hsep (hrootres k)).isUnit
  have hsame : ∀ i, y i = y' i := fun i =>
    (existsUnique_isRoot_powerSeries_of_isUnit_deriv (hdu i) (hv i)).unique
      ⟨hy i, hyc i⟩ ⟨hy' i, hyc' i⟩
  intro i
  rw [hsame i, hsame (π i)]
  exact hequiv φ π (map_eq_self_of_coeffMem ψ φ hfix hcoeff) hπ i

end

end GaloisForLFunctions.HTGeometry
