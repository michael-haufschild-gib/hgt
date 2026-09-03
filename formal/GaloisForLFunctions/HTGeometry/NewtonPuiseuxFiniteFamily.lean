import GaloisForLFunctions.HTGeometry.NewtonPuiseuxRoot
import GaloisForLFunctions.HTGeometry.PowerSeriesSimpleRootLift

/-!
# One common Newton--Puiseux cover for a finite polynomial family

Individual Newton--Puiseux ramifications are multiplied.  Expanding each selected root by the
product of the other ramifications gives a root of every polynomial after one common nonzero
ramification.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial PowerSeries

variable {K ι : Type} [Field K] [IsAlgClosed K] [CharZero K] [Fintype ι]

/-- Every finite family of positive-degree monic power-series polynomials acquires a selected root
on one common finite ramified cover. -/
theorem exists_isRoot_map_expand_finite_family
    (f : ι → (PowerSeries K)[X])
    (hf : ∀ i, (f i).Monic) (hpos : ∀ i, 0 < (f i).natDegree) :
    ∃ (N : ℕ) (hN : N ≠ 0) (y : ι → PowerSeries K),
      ∀ i, ((f i).map (PowerSeries.expand (R := K) N hN).toRingHom).IsRoot (y i) := by
  classical
  have hex : ∀ i, ∃ (N : ℕ) (hN : N ≠ 0) (y : PowerSeries K),
      ((f i).map (PowerSeries.expand (R := K) N hN).toRingHom).IsRoot y := by
    intro i
    exact exists_isRoot_map_expand (K := K) (f i).natDegree (f i) (hf i) rfl (hpos i)
  let Ni : ι → ℕ := fun i => (hex i).choose
  have hNi : ∀ i, Ni i ≠ 0 := fun i => (hex i).choose_spec.choose
  let yi : ∀ i, PowerSeries K := fun i => (hex i).choose_spec.choose_spec.choose
  have hyi : ∀ i,
      ((f i).map (PowerSeries.expand (R := K) (Ni i) (hNi i)).toRingHom).IsRoot
        (yi i) := fun i => (hex i).choose_spec.choose_spec.choose_spec
  let N : ℕ := ∏ i, Ni i
  have hN : N ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hNi i
  refine ⟨N, hN, fun i =>
    PowerSeries.expand (R := K) (∏ j ∈ Finset.univ.erase i, Ni j)
      (Finset.prod_ne_zero_iff.mpr fun j _ => hNi j) (yi i), ?_⟩
  intro i
  let M : ℕ := ∏ j ∈ Finset.univ.erase i, Ni j
  have hM : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hNi j
  have hprod : N = M * Ni i := by
    change (∏ j, Ni j) = (∏ j ∈ Finset.univ.erase i, Ni j) * Ni i
    exact (Finset.prod_erase_mul (s := Finset.univ) (f := Ni) (Finset.mem_univ i)).symm
  have hroot := isRoot_map_powerSeries
    (PowerSeries.expand (R := K) M hM).toRingHom (hyi i)
  rw [Polynomial.map_map] at hroot
  have hcomp :
      (PowerSeries.expand (R := K) M hM).toRingHom.comp
          (PowerSeries.expand (R := K) (Ni i) (hNi i)).toRingHom =
        (PowerSeries.expand (R := K) N hN).toRingHom := by
    apply RingHom.ext
    intro φ
    change PowerSeries.expand (R := K) M hM
        (PowerSeries.expand (R := K) (Ni i) (hNi i) φ) =
      PowerSeries.expand (R := K) N hN φ
    simpa only [hprod] using
      (PowerSeries.expand_mul M hM (Ni i) (hNi i) φ).symm
  rw [hcomp] at hroot
  exact hroot

end GaloisForLFunctions.HTGeometry
