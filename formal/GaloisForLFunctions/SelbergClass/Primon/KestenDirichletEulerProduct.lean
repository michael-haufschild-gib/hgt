import GaloisForLFunctions.SelbergClass.Primon.KestenDirichletDeterminant
import GaloisForLFunctions.RHTower.PrimeZetaLogAsymptotic
import GaloisForLFunctions.RHTower.RiemannXiZerosInfinite

/-!
# The Euler product of finite Green determinant ratios

At depth `N`, the exact local ratio is
`(1-p⁻²)/(1-p⁻(2N+3))`. Multiplying over all primes therefore gives
`ζ(2N+3)/ζ(2)`. The limiting boundary factor has product `1/ζ(2)`;
finite-prime depth limits and the full arithmetic product have this
same limit. Logarithms give the corresponding additive identity.
-/

open _root_.RHTower Filter Topology
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

private theorem gap_pos (p : Nat.Primes) : 0 < 1 - primeReciprocal p ^ 2 :=
  sub_pos.mpr (pow_lt_one₀ (primeReciprocal_pos p).le (primeReciprocal_lt_one p) (by decide))

private theorem prime_rpow_neg_nat (p : Nat.Primes) (k : ℕ) :
    (p : ℝ) ^ (-(k : ℝ)) = primeReciprocal p ^ k := by
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  simp only [primeReciprocal, inv_pow]

private theorem hasProd_inverse_gap (k : ℕ) (hk : 1 < k) :
    HasProd (fun p : Nat.Primes => (1 - primeReciprocal p ^ k)⁻¹) (riemannZeta (k : ℂ)).re := by
  have h := _root_.RHTower.hasProd_primeEulerFactor (s := (k : ℝ)) (by exact_mod_cast hk)
  simpa only [prime_rpow_neg_nat, Complex.ofReal_natCast] using h

private theorem zeta_two_pos : 0 < (riemannZeta (2 : ℂ)).re := by
  simpa using riemannZeta_re_pos_of_one_lt (x := (2 : ℝ)) (by norm_num)

private theorem zeta_odd_pos (n : ℕ) : 0 < (riemannZeta ((2 * n + 3 : ℕ) : ℂ)).re := by
  have hn : (1 : ℝ) < ((2 * n + 3 : ℕ) : ℝ) := by exact_mod_cast (show 1 < 2 * n + 3 by omega)
  simpa only [Complex.ofReal_natCast] using riemannZeta_re_pos_of_one_lt hn

/-- The product of the limiting local boundary factors is the reciprocal zeta value at two. -/
theorem hasProd_kestenDirichletBoundaryFactors :
    HasProd (fun p : Nat.Primes => 1 - primeReciprocal p ^ 2) (riemannZeta (2 : ℂ)).re⁻¹ := by
  have h := Filter.Tendsto.inv₀ (hasProd_inverse_gap 2 (by omega)) zeta_two_pos.ne'
  refine h.congr fun s => ?_
  rw [← Finset.prod_inv_distrib]
  simp only [inv_inv]

theorem tprod_kestenDirichletBoundaryFactors :
    (∏' p : Nat.Primes, 1 - primeReciprocal p ^ 2) = (riemannZeta (2 : ℂ)).re⁻¹ :=
  hasProd_kestenDirichletBoundaryFactors.tprod_eq

/-- At each finite depth, the product of the actual matrix determinant ratios is an odd zeta ratio. -/
theorem hasProd_kestenDirichletGreen_det_ratio (n : ℕ) :
    HasProd (fun p : Nat.Primes => (kestenDirichletGreen p n).det / (kestenFiniteGreen p n).det)
      ((riemannZeta ((2 * n + 3 : ℕ) : ℂ)).re / (riemannZeta (2 : ℂ)).re) := by
  have h := Filter.Tendsto.div (hasProd_inverse_gap (2 * n + 3) (by omega))
    (hasProd_inverse_gap 2 (by omega)) zeta_two_pos.ne'
  refine h.congr fun s => ?_
  change (∏ p ∈ s, (1 - primeReciprocal p ^ (2 * n + 3))⁻¹) /
    (∏ p ∈ s, (1 - primeReciprocal p ^ 2)⁻¹) = _
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p _
  rw [inv_div_inv, kestenDirichletGreen_det_ratio]

theorem tprod_kestenDirichletGreen_det_ratio (n : ℕ) :
    (∏' p : Nat.Primes, (kestenDirichletGreen p n).det / (kestenFiniteGreen p n).det) =
      (riemannZeta ((2 * n + 3 : ℕ) : ℂ)).re / (riemannZeta (2 : ℂ)).re :=
  (hasProd_kestenDirichletGreen_det_ratio n).tprod_eq

/-- The prime sum of logarithmic determinant ratios is the difference of two zeta logarithms. -/
theorem hasSum_log_kestenDirichletGreen_det_ratio (n : ℕ) :
    HasSum (fun p : Nat.Primes => Real.log ((kestenDirichletGreen p n).det / (kestenFiniteGreen p n).det))
      (Real.log (riemannZeta ((2 * n + 3 : ℕ) : ℂ)).re - Real.log (riemannZeta (2 : ℂ)).re) := by
  have h := _root_.RHTower.hasSum_log_of_hasProd
    (fun p => (gap_pos p).trans (kestenDirichletGreen_det_ratio_lower p n))
    (div_pos (zeta_odd_pos n) zeta_two_pos) (hasProd_kestenDirichletGreen_det_ratio n)
  rwa [Real.log_div (zeta_odd_pos n).ne' zeta_two_pos.ne'] at h

/-- The limiting boundary logarithms sum to minus the logarithm of zeta at two. -/
theorem hasSum_log_kestenDirichletBoundaryFactors :
    HasSum (fun p : Nat.Primes => Real.log (1 - primeReciprocal p ^ 2))
      (-Real.log (riemannZeta (2 : ℂ)).re) := by
  have h := _root_.RHTower.hasSum_log_of_hasProd gap_pos (inv_pos.mpr zeta_two_pos)
    hasProd_kestenDirichletBoundaryFactors
  rwa [Real.log_inv] at h

/-- Depth limits commute with each fixed finite prime product. -/
theorem tendsto_finset_kestenDirichletGreen_det_ratio (s : Finset Nat.Primes) :
    Tendsto (fun n => ∏ p ∈ s, (kestenDirichletGreen p n).det / (kestenFiniteGreen p n).det)
      atTop (𝓝 (∏ p ∈ s, 1 - primeReciprocal p ^ 2)) :=
  tendsto_finset_prod s (fun p _ => tendsto_kestenDirichletGreen_det_ratio p)

/-- The full arithmetic determinant product converges to the product of the local boundary limits. -/
theorem tendsto_tprod_kestenDirichletGreen_det_ratio :
    Tendsto (fun n => ∏' p : Nat.Primes, (kestenDirichletGreen p n).det / (kestenFiniteGreen p n).det)
      atTop (𝓝 (riemannZeta (2 : ℂ)).re⁻¹) := by
  have hn : Tendsto (fun n : ℕ => 2 * n + 3) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact ⟨b, fun n hn => by omega⟩
  have hr : Tendsto (fun n : ℕ => ((2 * n + 3 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hz := (Complex.continuous_re.tendsto (1 : ℂ)).comp
    (_root_.RHTower.tendsto_riemannZeta_atTop.comp hr)
  have h := hz.div_const (riemannZeta (2 : ℂ)).re
  simpa only [Function.comp_apply, Complex.ofReal_natCast, Complex.one_re, one_div,
    tprod_kestenDirichletGreen_det_ratio] using h

end
end GaloisForLFunctions.SelbergClass.Primon

#print axioms GaloisForLFunctions.SelbergClass.Primon.hasProd_kestenDirichletBoundaryFactors
#print axioms GaloisForLFunctions.SelbergClass.Primon.tprod_kestenDirichletBoundaryFactors
#print axioms GaloisForLFunctions.SelbergClass.Primon.hasProd_kestenDirichletGreen_det_ratio
#print axioms GaloisForLFunctions.SelbergClass.Primon.tprod_kestenDirichletGreen_det_ratio
#print axioms GaloisForLFunctions.SelbergClass.Primon.hasSum_log_kestenDirichletGreen_det_ratio
#print axioms GaloisForLFunctions.SelbergClass.Primon.hasSum_log_kestenDirichletBoundaryFactors
#print axioms GaloisForLFunctions.SelbergClass.Primon.tendsto_finset_kestenDirichletGreen_det_ratio
#print axioms GaloisForLFunctions.SelbergClass.Primon.tendsto_tprod_kestenDirichletGreen_det_ratio
