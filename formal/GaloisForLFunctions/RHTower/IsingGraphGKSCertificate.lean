import GaloisForLFunctions.RHTower.PrimeIsingArbitraryGraphGKSNoGo
import GaloisForLFunctions.HTGeometry.LeeYangFirstZeroBudget

/-!
# Ferromagnetic Ising graphs carry the GKS certificate

`FiniteGKSPrimeSpinModel` asks for a nonnegative spin weight table whose two-point correlations
`Σ_σ w(σ) σ_i σ_j` are nonnegative. This file shows that the zero-field Ising model on any finite
graph with nonnegative couplings supplies one.

* `boolDownSetEquiv`: Boolean configurations correspond to down-sets `{k : σ_k = −1}`, and the
  spin of a site is the same in both pictures (`spin_boolDownSet`).
* `isingGKSModel`: the Ising weight table `exp(Σ_{(i,j)∈E} J_ij σ_i σ_j)` with arbitrary site
  masses `≥ log 2` is a `FiniteGKSPrimeSpinModel`. Off the diagonal, its pair correlations are
  nonnegative by the first Griffiths inequality (`corrA_nonneg`). On the diagonal, they equal the
  partition function.

**Corollaries.** For every sequence of finite ferromagnetic Ising graphs, of arbitrary topology,
couplings and size, with site masses `≥ log 2`:
* the normalized characteristic partitions never converge locally uniformly to the pointed
  completed `Ξ` (`not_tendstoLocallyUniformly_isingGKS_unitCentralXiC`);
* if the graphs grow and converge after a common argument rescaling `a_k`, then `a_k → 0`
  (`tendsto_scale_zero_of_isingGKS_tendstoLocallyUniformly`).
-/

open Complex Filter Topology Finset
open GaloisForLFunctions.HTGeometry.LeeYang

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The down-set `{k : σ_k = −1}` of a Boolean configuration. -/
def boolDownSet {n : ℕ} (σ : Fin n → Bool) : Finset (Fin n) := univ.filter fun k => σ k = false

/-- Boolean configurations are down-sets. -/
def boolDownSetEquiv (n : ℕ) : (Fin n → Bool) ≃ Finset (Fin n) where
  toFun := boolDownSet
  invFun D := fun k => decide (k ∉ D)
  left_inv σ := by
    funext k
    cases h : σ k <;> simp [boolDownSet, h]
  right_inv D := by
    ext k
    simp [boolDownSet]

theorem spin_boolDownSet {n : ℕ} (σ : Fin n → Bool) (k : Fin n) :
    spin (boolDownSet σ) k = boolSpin (σ k) := by
  cases h : σ k <;> simp [spin, boolSpin, boolDownSet, h]

/-- **The zero-field ferromagnetic Ising model on any finite graph is a GKS weight table.** -/
def isingGKSModel {n : ℕ} (J : Fin n → Fin n → ℝ) (E : Finset (Fin n × Fin n))
    (hJ : ∀ p ∈ E, 0 ≤ J p.1 p.2) (mass : Fin n → ℝ) (hmass : ∀ i, Real.log 2 ≤ mass i) :
    FiniteGKSPrimeSpinModel n where
  mass := mass
  weight σ := isingWeight J E (boolDownSet σ)
  mass_floor := hmass
  weight_nonneg σ := (isingWeight_pos J E _).le
  totalWeight_pos := Finset.sum_pos (fun σ _ => isingWeight_pos J E _) ⟨fun _ => true, mem_univ _⟩
  pairNumerator_nonneg i j := by
    rw [Fintype.sum_equiv (boolDownSetEquiv n) _
      (fun D => isingWeight J E D * spin D i * spin D j)
      (fun σ => by simp only [boolDownSetEquiv, Equiv.coe_fn_mk, spin_boolDownSet])]
    by_cases hij : i = j
    · subst hij
      exact Finset.sum_nonneg fun D _ => by
        rw [mul_assoc, spin_mul_self, mul_one]
        exact (isingWeight_pos J E D).le
    · have h := corrA_nonneg J E hJ {i, j}
      rw [corrA] at h
      simpa only [Finset.prod_pair hij, mul_assoc] using h

/-- **No ferromagnetic Ising graph sequence produces `Ξ`.** For arbitrary graphs, nonnegative
couplings and site masses `≥ log 2`, the normalized characteristic partitions never converge
locally uniformly to the pointed completed `Ξ`. -/
theorem not_tendstoLocallyUniformly_isingGKS_unitCentralXiC (vertexCount : ℕ → ℕ)
    (J : ∀ k, Fin (vertexCount k) → Fin (vertexCount k) → ℝ)
    (E : ∀ k, Finset (Fin (vertexCount k) × Fin (vertexCount k)))
    (hJ : ∀ k, ∀ p ∈ E k, 0 ≤ J k p.1 p.2) (mass : ∀ k, Fin (vertexCount k) → ℝ)
    (hmass : ∀ k i, Real.log 2 ≤ mass k i) :
    ¬ TendstoLocallyUniformly
      (fun k => (isingGKSModel (J k) (E k) (hJ k) (mass k) (hmass k)).partition)
      unitCentralXiC atTop :=
  not_tendstoLocallyUniformly_finiteGKSPrimeSpinPartition_unitCentralXiC vertexCount
    (fun k => isingGKSModel (J k) (E k) (hJ k) (mass k) (hmass k))

/-- **Growing ferromagnetic Ising producers of `Ξ` must collapse their scale.** If the graphs grow
and the rescaled partitions converge to the pointed completed `Ξ`, then the scales tend to zero. -/
theorem tendsto_scale_zero_of_isingGKS_tendstoLocallyUniformly (vertexCount : ℕ → ℕ)
    (J : ∀ k, Fin (vertexCount k) → Fin (vertexCount k) → ℝ)
    (E : ∀ k, Finset (Fin (vertexCount k) × Fin (vertexCount k)))
    (hJ : ∀ k, ∀ p ∈ E k, 0 ≤ J k p.1 p.2) (mass : ∀ k, Fin (vertexCount k) → ℝ)
    (hmass : ∀ k i, Real.log 2 ≤ mass k i) (a : ℕ → ℝ)
    (hvertices : Tendsto (fun k => (vertexCount k : ℝ)) atTop atTop)
    (hconv : TendstoLocallyUniformly
      (fun k => (isingGKSModel (J k) (E k) (hJ k) (mass k) (hmass k)).rescaledPartition (a k))
      unitCentralXiC atTop) :
    Tendsto a atTop (nhds 0) :=
  tendsto_scale_zero_of_vertexCount_tendsto_atTop_of_rescaled_gksPrimeSpin_tendstoLocallyUniformly
    vertexCount (fun k => isingGKSModel (J k) (E k) (hJ k) (mass k) (hmass k)) a hvertices hconv

end

end GaloisForLFunctions.RHTower
