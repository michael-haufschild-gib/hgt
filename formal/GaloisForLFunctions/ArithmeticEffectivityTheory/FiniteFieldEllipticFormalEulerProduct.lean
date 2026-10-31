import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticClosedPointDegrees
import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittGhost
import Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# The formal Euler product over the actual elliptic places

Residue-degree cutoffs give coefficientwise stable products. Their logarithmic
ghost counts actual residue-field embeddings, so inversion gives the existing
point-count zeta series, including its degree-one infinity factor.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open IsDedekindDomain _root_.RHTower PowerSeries
open ArithmeticCastelnuovoSeveri
open scoped PowerSeries.WithPiTopology Topology
noncomputable section

/-- The inverse local factor of an actual affine prime. -/
def affineEulerFactor (v : HeightOneSpectrum A) : PowerSeries ℂ :=
  deningerBigWittFactor 1 (affinePlaceDegree v)

theorem affineEulerFactor_constantCoeff (v : HeightOneSpectrum A) :
    PowerSeries.constantCoeff (affineEulerFactor v) = 1 :=
  deningerBigWittFactor_constantCoeff _ _ (affinePlaceDegree_pos v).ne'

/-- Finite inverse Euler product, with the actual degree-one infinity factor. -/
def ellipticEulerPartial (N : ℕ) : PowerSeries ℂ :=
  deningerBigWittFactor 1 1 * ∏ v ∈ affinePlacesDegreeLe N, affineEulerFactor v

theorem ellipticEulerPartial_constantCoeff (N : ℕ) :
    PowerSeries.constantCoeff (ellipticEulerPartial N) = 1 := by
  simp only [ellipticEulerPartial, map_mul, map_prod, affineEulerFactor_constantCoeff,
    deningerBigWittFactor_constantCoeff (1 : ℂ) 1 (by omega), Finset.prod_const_one, one_mul]

private theorem coeff_mul_affineEulerFactors_of_lt (f : PowerSeries ℂ)
    (S : Finset (HeightOneSpectrum A)) (k : ℕ)
    (hS : ∀ v ∈ S, k < affinePlaceDegree v) :
    PowerSeries.coeff k (f * ∏ v ∈ S, affineEulerFactor v) = PowerSeries.coeff k f := by
  classical
  induction S using Finset.induction_on generalizing f with
  | empty => simp only [Finset.prod_empty, mul_one]
  | @insert v S hv ih =>
    rw [Finset.prod_insert hv, ← mul_assoc]
    rw [ih (f * affineEulerFactor v) (fun w hw => hS w (Finset.mem_insert_of_mem hw))]
    exact coeff_mul_deningerBigWittFactor_of_lt f 1 (hS v (Finset.mem_insert_self _ _))

/-- Every coefficient stabilizes once the cutoff reaches its degree. -/
theorem ellipticEulerPartial_coeff_stable {k N M : ℕ} (hk : k ≤ N) (hNM : N ≤ M) :
    PowerSeries.coeff k (ellipticEulerPartial M) =
      PowerSeries.coeff k (ellipticEulerPartial N) := by
  classical
  have hsub := affinePlacesDegreeLe_mono hNM
  have hprod : (∏ v ∈ affinePlacesDegreeLe N, affineEulerFactor v) *
      (∏ v ∈ affinePlacesDegreeLe M \ affinePlacesDegreeLe N, affineEulerFactor v) =
      ∏ v ∈ affinePlacesDegreeLe M, affineEulerFactor v :=
    (mul_comm _ _).trans (Finset.prod_sdiff hsub)
  unfold ellipticEulerPartial
  rw [← hprod, ← mul_assoc]
  apply coeff_mul_affineEulerFactors_of_lt
  intro v hv
  have hn : ¬ affinePlaceDegree v ≤ N := by
    simpa only [mem_affinePlacesDegreeLe] using (Finset.mem_sdiff.mp hv).2
  exact hk.trans_lt (lt_of_not_ge hn)

/-- The literal coefficientwise product of all inverse local factors. -/
def ellipticEulerProduct : PowerSeries ℂ :=
  PowerSeries.mk fun n => PowerSeries.coeff n (ellipticEulerPartial n)

theorem ellipticEulerProduct_coeff (n : ℕ) :
    PowerSeries.coeff n ellipticEulerProduct = PowerSeries.coeff n (ellipticEulerPartial n) :=
  PowerSeries.coeff_mk _ _

theorem ellipticEulerProduct_constantCoeff :
    PowerSeries.constantCoeff ellipticEulerProduct = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, ellipticEulerProduct_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, ellipticEulerPartial_constantCoeff]

/-- The inverse local-factor products converge in the coefficient topology. -/
theorem tendsto_ellipticEulerPartial :
    Filter.Tendsto ellipticEulerPartial Filter.atTop (𝓝 ellipticEulerProduct) := by
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_ge_atTop n] with N hN
  simp only [ellipticEulerProduct_coeff,
    ellipticEulerPartial_coeff_stable (k := n) le_rfl hN]

/-- The positive-degree logarithmic ghost of the partial product is the literal degree sum. -/
theorem ellipticEulerPartial_ghost_coeff (N : ℕ) {k : ℕ} (hk : 0 < k) :
    PowerSeries.coeff k (deningerBigWittLogGhost (ellipticEulerPartial N)
      (ellipticEulerPartial_constantCoeff N)) =
      1 + ∑ v ∈ affinePlacesDegreeLe N,
        if affinePlaceDegree v ∣ k then (affinePlaceDegree v : ℂ) else 0 := by
  unfold ellipticEulerPartial
  rw [deningerBigWittLogGhost_mul _ _
    (deningerBigWittFactor_constantCoeff 1 1 (by omega))
    (by simp only [map_prod, affineEulerFactor_constantCoeff, Finset.prod_const_one])]
  rw [map_add, deningerBigWittLogGhost_factor_coeff 1 (by omega) hk,
    deningerBigWittLogGhost_finset_prod _ _ affineEulerFactor_constantCoeff, map_sum]
  simp only [one_dvd, if_true, Nat.cast_one, one_pow, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  simpa only [affineEulerFactor, one_pow, mul_one] using
    deningerBigWittLogGhost_factor_coeff (1 : ℂ) (affinePlaceDegree_pos v) hk

/-- The logarithmic ghost is exactly the already constructed projective point-count ghost. -/
theorem ellipticEulerProduct_logGhost :
    deningerBigWittLogGhost ellipticEulerProduct ellipticEulerProduct_constantCoeff =
      pointCountGhost := by
  apply PowerSeries.ext
  intro k
  by_cases hk : k = 0
  · subst k
    rw [PowerSeries.coeff_zero_eq_constantCoeff, deningerBigWittLogGhost_constantCoeff]
    change 0 = (extensionPointCount 0 : ℂ)
    rw [extensionPointCount_zero, Nat.cast_zero]
  · letI : NeZero k := ⟨hk⟩
    rw [deningerBigWittLogGhost_coeff_congr ellipticEulerProduct_constantCoeff
      (ellipticEulerPartial_constantCoeff k)
      (fun n hn => by
        rw [ellipticEulerProduct_coeff]
        exact (ellipticEulerPartial_coeff_stable (k := n) le_rfl hn).symm)]
    rw [ellipticEulerPartial_ghost_coeff k (Nat.pos_of_ne_zero hk)]
    simp only [pointCountGhost, PowerSeries.coeff_mk, extensionPointCount_eq_closed_degree_sum]
    push_cast
    rfl

/-- Inversion of the actual local-factor product gives the point-count zeta series. -/
theorem ellipticEulerProduct_inv_eq_zeta :
    PowerSeries.invOfUnit ellipticEulerProduct 1 = zeta := by
  let P := ellipticEulerProduct
  let Z := PowerSeries.invOfUnit P 1
  have hP : PowerSeries.constantCoeff P = 1 := ellipticEulerProduct_constantCoeff
  have hZP : Z * P = 1 := PowerSeries.invOfUnit_mul P 1 hP
  have hZ : PowerSeries.constantCoeff Z = 1 := by
    have h := congrArg PowerSeries.constantCoeff hZP
    simpa only [map_mul, hP, mul_one, map_one] using h
  have hG := deningerBigWittLogGhost_mul Z P hZ hP
  have hleft : deningerBigWittLogGhost (Z * P) (by simp only [map_mul, hZ, hP, mul_one]) = 0 := by
    have he := deningerBigWittLogGhost_congr
      (by simp only [map_mul, hZ, hP, mul_one]) (by exact map_one _) hZP
    exact he.trans (by simp only [deningerBigWittLogGhost, Derivation.map_one_eq_zero,
      mul_zero, zero_mul, neg_zero])
  have hGZ : deningerBigWittLogGhost Z hZ = -pointCountGhost := by
    rw [hleft, ellipticEulerProduct_logGhost] at hG
    exact eq_neg_of_add_eq_zero_left hG.symm
  apply zeta_unique Z hZ
  have hself := deningerBigWittLogGhost_mul_self Z hZ
  rw [hGZ, neg_mul] at hself
  unfold HasGhost
  exact (neg_injective hself).symm.trans (mul_comm _ _)

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ellipticEulerProduct_logGhost
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ellipticEulerProduct_inv_eq_zeta
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.tendsto_ellipticEulerPartial
