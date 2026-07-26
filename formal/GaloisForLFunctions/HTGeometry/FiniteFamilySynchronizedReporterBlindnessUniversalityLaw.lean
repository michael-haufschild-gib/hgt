import GaloisForLFunctions.HTGeometry.FiniteReporterBlindness

/-!
# Finite-family synchronized reporter blindness

One coefficient vector simultaneously synthesizes a nonzero derivative packet for every member
of a finite constant-coefficient differentially transcendental source family while every
source-specific finite-dimensional reporter annihilates its packet.
-/

open scoped BigOperators

namespace HTGeometry

open GaloisForLFunctions Module

noncomputable section

/-- **Finite-family synchronized reporter-blindness universality.**

At one coefficient resolution beyond the rank of the complete product reporter, one common
nonzero coefficient vector is invisible after reporting for every source and remains a nonzero
function before reporting for every source. -/
theorem exists_common_nonzero_finiteDerivativeReporterPacket_ker
    {ι Y : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
    (f : ι → ℂ → ℂ)
    (hf : ∀ i, ConstantCoefficientDifferentiallyTranscendental (f i))
    (report : ι → (ℂ → ℂ) →ₗ[ℂ] Y) :
    ∃ c : Fin (finrank ℂ (ι → Y) + 1) → ℂ,
      (∃ j, c j ≠ 0) ∧
      ∀ i,
        finiteDerivativeReporterPacket c (f i) ≠ 0 ∧
          report i (finiteDerivativeReporterPacket c (f i)) = 0 := by
  let n : ℕ := finrank ℂ (ι → Y) + 1
  let v : Fin n → (ι → Y) :=
    fun j i => report i (iteratedDeriv (j : ℕ) (f i))
  have hv : ¬ LinearIndependent ℂ v := by
    intro hlinear
    have hbound := hlinear.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hbound
    omega
  obtain ⟨c, hsum, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hv
  refine ⟨c, ⟨j, hj⟩, ?_⟩
  intro i
  constructor
  · intro hpacket
    have hall :
        LinearIndependent ℂ (fun m : ℕ => iteratedDeriv m (f i)) :=
      (constantCoefficientDifferentiallyTranscendental_iff_linearIndependent_iteratedDeriv
        (f i)).mp (hf i)
    have hinitial :
        LinearIndependent ℂ
          (fun k : Fin n => iteratedDeriv (k : ℕ) (f i)) :=
      hall.comp (fun k : Fin n => (k : ℕ)) Fin.val_injective
    have hcoeff := Fintype.linearIndependent_iff.mp hinitial c
    exact hj (hcoeff (by
      simpa only [finiteDerivativeReporterPacket] using hpacket) j)
  · have hi := congrFun hsum i
    rw [finiteDerivativeReporterPacket, map_sum]
    simpa only [map_smul, v, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply]
      using hi

end

end HTGeometry
