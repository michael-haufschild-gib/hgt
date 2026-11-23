import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechCupLeibniz
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveTopCechResidue
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RegularChartFormProduct
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverRationalForms

/-! The traced top residue of a cup product with a complementary
cocycle depends only on the cohomology class of the other factor. -/

noncomputable section

open GlobalTheory.CechDR
open scoped GlobalTheory.CechDR

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

private theorem integralClosure_restrictScalars_mono {A B : Subalgebra k F} (h : A ≤ B) :
    (integralClosure A E).restrictScalars k ≤ (integralClosure B E).restrictScalars k := by
  letI : Algebra A B := (Subalgebra.inclusion h).toRingHom.toAlgebra
  letI : IsScalarTower A B E := .of_algebraMap_eq fun _ => rfl
  intro z hz
  exact (show IsIntegral A z from hz).tower_top (A := B)

/-- Normalized chart rings are monotone in the set of indices. -/
theorem rB_mono {I J : Finset (Fin (d + 1))} (h : I ⊆ J) :
    rB k E x I ≤ rB k E x J :=
  integralClosure_restrictScalars_mono (rA_mono (k := k) (x := x) h)

/-- Pair with a fixed left cochain by the top Čech cup product and residue. -/
def cupResidueFunctional (τ : DR k E →ₗ[E] E) (ρ : F →ₗ[k] k)
    (a : Finset (Fin (d + 1)) → DR k E) : (Finset (Fin (d + 1)) → DR k E) →ₗ[k] k :=
  ∑ i : Fin (d + 1), topResidue τ ρ ∘ₗ
    LinearMap.mul k (DR k E) (a (Finset.univ.filter (· ≤ i))) ∘ₗ
    LinearMap.proj (Finset.univ.filter (i ≤ ·))

theorem cupResidueFunctional_apply (τ : DR k E →ₗ[E] E) (ρ : F →ₗ[k] k)
    (a b : Finset (Fin (d + 1)) → DR k E) :
    cupResidueFunctional τ ρ a b = topResidue τ ρ (cechCup (LinearMap.mul k (DR k E)) a b Finset.univ) := by
  simp only [cupResidueFunctional, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    cechCup_apply, map_sum]

/-- Cup with a complementary cocycle followed by residue kills boundaries. -/
theorem IsFinCover.cupResidueFunctional_eq_zero_of_boundary [CharZero k] (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (ρ : F →ₗ[k] k) (hρ : IsRes x ρ)
    {p q : ℕ} (hpq : p + q = d) {a b : Finset (Fin (d + 1)) → DR k E}
    (ha : a ∈ (cech fun I => omB k E (rB k E x I) p).Z p)
    (hb : b ∈ (cech fun I => omB k E (rB k E x I) q).B q) :
    cupResidueFunctional τ ρ a b = 0 := by
  let A (n : ℕ) (I : Finset (Fin (d + 1))) := omB k E (rB k E x I) n
  let μ := LinearMap.mul k (DR k E)
  have hm {I J W : Finset (Fin (d + 1))} (_ : I.Nonempty) (_ : J.Nonempty)
      (hI : I ⊆ W) (hJ : J ⊆ W) {v w : DR k E} (hv : v ∈ A p I) (hw : w ∈ A q J) :
      μ v w ∈ A d W := by
    rw [← hpq]
    exact mul_mem_omB (omB_mono (rB_mono hI) p hv) (omB_mono (rB_mono hJ) q hw)
  have hbd : cechCup μ a b ∈ (cech (A d)).B ((p : ℤ) + q) :=
    cechCup_boundary_right μ (A p) (A q) (A d) hm ha hb
  rw [show (p : ℤ) + q = d by exact_mod_cast hpq] at hbd
  rw [cupResidueFunctional_apply]
  exact h.topResidue_cech_boundary τ hτ ρ hρ hbd

end GlobalTheory.PD
