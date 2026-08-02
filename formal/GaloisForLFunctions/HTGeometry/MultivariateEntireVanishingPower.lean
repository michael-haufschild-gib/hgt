import GaloisForLFunctions.HTGeometry.MultivariateMultiIndexJet
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Powers of a multivariate entire zero kill all lower mixed jets

Abe's all-order separator argument raises one order-one entire separator to the packet order.
The source space is defined by entire affine-line restrictions, so the precise proof reduces each
polarized directional jet to one-variable analytic order.  This file supplies multiplication and
powers inside that source space and proves the full mixed-jet vanishing statement.
-/

open Filter Function Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Product of two compact-open line-entire sources. -/
def multivariateEntireMul {d : ℕ}
    (f g : MultivariateEntire d) : MultivariateEntire d :=
  ⟨⟨fun x => f.1 x * g.1 x, f.1.continuous.mul g.1.continuous⟩,
    fun x v => (f.property x v).mul (g.property x v)⟩

@[simp]
theorem multivariateEntireMul_apply {d : ℕ}
    (f g : MultivariateEntire d) (x : Fin d → ℂ) :
    (multivariateEntireMul f g).1 x = f.1 x * g.1 x :=
  rfl

/-- A finite power of a compact-open line-entire source. -/
def multivariateEntirePow {d : ℕ}
    (f : MultivariateEntire d) (m : ℕ) : MultivariateEntire d :=
  ⟨⟨fun x => f.1 x ^ m, f.1.continuous.pow m⟩,
    fun x v => (f.property x v).pow m⟩

@[simp]
theorem multivariateEntirePow_apply {d : ℕ}
    (f : MultivariateEntire d) (m : ℕ) (x : Fin d → ℂ) :
    (multivariateEntirePow f m).1 x = f.1 x ^ m :=
  rfl

/-- Finite product of compact-open line-entire sources. -/
def multivariateEntireFinsetProd {d : ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → MultivariateEntire d) : MultivariateEntire d :=
  ⟨⟨fun x => ∏ i ∈ s, (f i).1 x,
      continuous_finsetProd s fun i _ => (f i).1.continuous⟩,
    fun x v => by
      change Differentiable ℂ (fun z : ℂ => ∏ i ∈ s, (f i).1 (x + z • v))
      rw [show (fun z : ℂ => ∏ i ∈ s, (f i).1 (x + z • v)) =
          ∏ i ∈ s, (fun z : ℂ => (f i).1 (x + z • v)) by
        funext z
        simp only [Finset.prod_apply]]
      exact Differentiable.finsetProd fun i _ => (f i).property x v⟩

@[simp]
theorem multivariateEntireFinsetProd_apply {d : ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → MultivariateEntire d) (x : Fin d → ℂ) :
    (multivariateEntireFinsetProd s f).1 x = ∏ i ∈ s, (f i).1 x :=
  rfl

/-- If `h` vanishes at `x`, then `h^m g` has every directional jet of order `< m` equal to
zero at `x`.  The proof factors every affine-line restriction by `z^m` using the removable
singularity `dslope`. -/
theorem directionalJetEval_mul_pow_eq_zero_of_lt
    {d m n : ℕ} (h g : MultivariateEntire d) (x v : Fin d → ℂ)
    (hh : h.1 x = 0) (hnm : n < m) :
    directionalJetEval n x v
      (multivariateEntireMul (multivariateEntirePow h m) g) = 0 := by
  let u : ℂ → ℂ := affineLineRestriction x v h
  let q : ℂ → ℂ := affineLineRestriction x v g
  have hu : Differentiable ℂ u := h.property x v
  have hq : Differentiable ℂ q := g.property x v
  have hu0 : u 0 = 0 := by simpa [u, affineLineRestriction] using hh
  have hds : Differentiable ℂ (dslope u 0) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope univ_mem).mpr hu.differentiableOn
  have hw : AnalyticAt ℂ (u ^ m * q) 0 :=
    ((hu.analyticAt 0).pow m).mul (hq.analyticAt 0)
  have horder : (m : ℕ∞) ≤ analyticOrderAt (u ^ m * q) 0 := by
    rw [natCast_le_analyticOrderAt hw]
    refine ⟨(dslope u 0) ^ m * q,
      ((hds.analyticAt 0).pow m).mul (hq.analyticAt 0), ?_⟩
    filter_upwards [] with z
    have huz : u z = z * dslope u 0 z := by
      simpa only [sub_zero, smul_eq_mul] using (sub_smul_dslope_of_zero hu0 z).symm
    rw [Pi.mul_apply, Pi.pow_apply, huz, mul_pow]
    simp only [sub_zero, smul_eq_mul, Pi.mul_apply, Pi.pow_apply]
    ring
  have hderiv : iteratedDeriv n (u ^ m * q) 0 = 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hw).mp horder n hnm
  change iteratedDeriv n (fun z : ℂ => u z ^ m * q z) 0 = 0 at hderiv
  change iteratedDeriv n
    (fun z : ℂ => h.1 (x + z • v) ^ m * g.1 (x + z • v)) 0 = 0
  simpa only [u, q, affineLineRestriction] using hderiv

/-- Cardinality of the canonical word of a multi-index is its total degree. -/
theorem card_multiIndexSlot {d : ℕ} (a : Fin d →₀ ℕ) :
    Fintype.card (MultiIndexSlot a) = Finsupp.degree a := by
  classical
  simp [MultiIndexSlot, Finsupp.degree_eq_sum]

/-- **All lower mixed jets vanish.** If `h(x)=0`, every multi-index jet of `h^m g` whose total
degree is `< m` is zero at `x`. -/
theorem multiIndexJetEvalCLM_mul_pow_eq_zero_of_degree_lt
    {d m : ℕ} (h g : MultivariateEntire d) (x : Fin d → ℂ)
    (hh : h.1 x = 0) (a : Fin d →₀ ℕ) (ha : Finsupp.degree a < m) :
    multiIndexJetEvalCLM x a
      (multivariateEntireMul (multivariateEntirePow h m) g) = 0 := by
  rw [multiIndexJetEvalCLM, orderedPartialJetEvalCLM_apply,
    polarizedJetEvalCLM_apply]
  apply Finset.sum_eq_zero
  intro s hs
  rw [smul_eq_mul, mul_eq_zero]
  exact Or.inr (directionalJetEval_mul_pow_eq_zero_of_lt h g x
    (jetSubsetDirection (fun j => coordinateJetDirection (multiIndexWord a j)) s)
    hh (by simpa only [card_multiIndexSlot] using ha))

end

end GaloisForLFunctions.HTGeometry
