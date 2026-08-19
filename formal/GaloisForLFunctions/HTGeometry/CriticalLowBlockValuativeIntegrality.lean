import GaloisForLFunctions.HTGeometry.ValuationSubringResidueAlgebraic
import Mathlib.RingTheory.Polynomial.Subring
import GaloisForLFunctions.HTGeometry.CriticalBiprojectiveBoundary

/-!
# Valuative integrality of the critical low blocks

A critical state is a pair of truncations inverse to one another modulo the horizon.  Its two low
blocks are integral wherever the two tails are and their marked coefficients are units:

```text
coeffs_mem_of_criticalRelation :
    tails in O, marked tail coefficients units of O,  X^{m+n} ∣ (Alow + U)(Blow + W) − 1
      ⟹  every coefficient of Alow and of Blow lies in O
```

The proof is the valuative criterion made explicit.  Scale each low block by the inverse of a
coefficient of minimal value — `exists_scaling`, which exists because in a valuation ring one of
any finitely many elements divides all the others — lift the scaled relation to `O[X]`, and reduce
it modulo the maximal ideal.  A failure of integrality makes the reduced homogenizing coordinate
zero while the reduced low block is nonzero, which
`critical_biprojective_boundary_exclusion_of_marked_coefficients` forbids.  The marked coefficients
survive the reduction precisely because they were assumed invertible.

This is the ring-theoretic form of "the critical map is finite on the chart".
-/

namespace GaloisForLFunctions.HTGeometry

open IsLocalRing Polynomial

set_option maxHeartbeats 2000000

variable {E : Type*} [Field E]

/-- A scaling that pulls a finite family into a valuation subring, normalized so that either the
scaling is trivial or one of the scaled elements is one. -/
theorem exists_scaling (O : ValuationSubring E) (s : Finset E) :
    ∃ α : E, α ≠ 0 ∧ α ∈ O ∧ (∀ x ∈ s, α * x ∈ O) ∧ (α = 1 ∨ ∃ x ∈ s, α * x = 1) := by
  classical
  obtain ⟨c, hcs, hmax⟩ := (insert (1 : E) s).exists_max_image (fun x => O.valuation x)
    ⟨1, Finset.mem_insert_self _ _⟩
  have hone := hmax 1 (Finset.mem_insert_self _ _)
  rw [map_one] at hone
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hone
    exact absurd hone (by simp)
  refine ⟨c⁻¹, inv_ne_zero hc0, ?_, ?_, ?_⟩
  · rw [← ValuationSubring.valuation_le_one_iff, map_inv₀]
    exact inv_le_one_of_one_le₀ hone
  · intro x hx
    rw [← ValuationSubring.valuation_le_one_iff, map_mul, map_inv₀]
    rw [inv_mul_le_iff₀ (lt_of_lt_of_le zero_lt_one hone), mul_one]
    exact hmax x (Finset.mem_insert_of_mem hx)
  · rcases Finset.mem_insert.mp hcs with h | h
    · exact Or.inl (by rw [h, inv_one])
    · exact Or.inr ⟨c, h, inv_mul_cancel₀ hc0⟩

/-- Lift a polynomial whose coefficients lie in a valuation subring. -/
noncomputable def valLift (O : ValuationSubring E) (p : E[X]) (hp : ∀ i, p.coeff i ∈ O) :
    O[X] :=
  p.toSubring O.toSubring (by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp (by simpa using hy)
    exact hp i)

@[simp] theorem valLift_map (O : ValuationSubring E) (p : E[X]) (hp : ∀ i, p.coeff i ∈ O) :
    (valLift O p hp).map (Subring.subtype O.toSubring) = p :=
  Polynomial.map_toSubring _ _ _

@[simp] theorem valLift_coeff (O : ValuationSubring E) (p : E[X]) (hp : ∀ i, p.coeff i ∈ O)
    (i : ℕ) : (((valLift O p hp).coeff i : O) : E) = p.coeff i :=
  Polynomial.coeff_toSubring _ _ _ (n := i)

theorem valLift_natDegree_le (O : ValuationSubring E) (p : E[X]) (hp : ∀ i, p.coeff i ∈ O) :
    (valLift O p hp).natDegree = p.natDegree :=
  Polynomial.natDegree_toSubring _ _ _

/-- **Valuative integrality of the critical low blocks.**  If the two tails have coefficients in a
valuation subring and their marked coefficients are units there, then the two low blocks of any
critical state have coefficients in that subring. -/
theorem coeffs_mem_of_criticalRelation (O : ValuationSubring E) {m n : ℕ}
    {Alow Blow U W : E[X]}
    (hAdeg : Alow.natDegree < m) (hBdeg : Blow.natDegree < n)
    (hU : ∀ i, U.coeff i ∈ O) (hW : ∀ i, W.coeff i ∈ O)
    (hUm0 : U.coeff m ≠ 0) (hWn0 : W.coeff n ≠ 0)
    (hUm : (U.coeff m)⁻¹ ∈ O) (hWn : (W.coeff n)⁻¹ ∈ O)
    (hdvd : (X : E[X]) ^ (m + n) ∣ (Alow + U) * (Blow + W) - 1) :
    (∀ i, Alow.coeff i ∈ O) ∧ (∀ i, Blow.coeff i ∈ O) := by
  classical
  obtain ⟨α, hα0, hαO, hαs, hαcase⟩ := exists_scaling O ((Finset.range m).image Alow.coeff)
  obtain ⟨β, hβ0, hβO, hβs, hβcase⟩ := exists_scaling O ((Finset.range n).image Blow.coeff)
  have hAmem : ∀ i, (C α * Alow).coeff i ∈ O := by
    intro i
    rw [Polynomial.coeff_C_mul]
    by_cases hi : i < m
    · exact hαs _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
      exact O.zero_mem
  have hBmem : ∀ i, (C β * Blow).coeff i ∈ O := by
    intro i
    rw [Polynomial.coeff_C_mul]
    by_cases hi : i < n
    · exact hβs _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
      exact O.zero_mem
  set AO := valLift O (C α * Alow) hAmem with hAO
  set BO := valLift O (C β * Blow) hBmem with hBO
  set UO := valLift O U hU with hUO
  set WO := valLift O W hW with hWO
  set αO : O := ⟨α, hαO⟩ with hαOdef
  set βO : O := ⟨β, hβO⟩ with hβOdef
  set Q : O[X] := (AO + C αO * UO) * (BO + C βO * WO) - C (αO * βO) with hQ
  have hAOmap : AO.map (Subring.subtype O.toSubring) = C α * Alow := valLift_map _ _ _
  have hBOmap : BO.map (Subring.subtype O.toSubring) = C β * Blow := valLift_map _ _ _
  have hUOmap : UO.map (Subring.subtype O.toSubring) = U := valLift_map _ _ _
  have hWOmap : WO.map (Subring.subtype O.toSubring) = W := valLift_map _ _ _
  have hQmap : Q.map (Subring.subtype O.toSubring) = C (α * β) * ((Alow + U) * (Blow + W) - 1) := by
    rw [hQ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
      Polynomial.map_C, hAOmap, hBOmap, hUOmap, hWOmap]
    show (C α * Alow + C α * U) * (C β * Blow + C β * W) - C (α * β) = _
    rw [Polynomial.C_mul]
    ring
  have hQdvd : (X : O[X]) ^ (m + n) ∣ Q := by
    rw [Polynomial.X_pow_dvd_iff]
    intro j hj
    apply Subtype.val_injective
    have hc : ((Q.coeff j : O) : E) = (Q.map (Subring.subtype O.toSubring)).coeff j := by
      rw [Polynomial.coeff_map]; rfl
    show ((Q.coeff j : O) : E) = ((0 : O) : E)
    rw [hc, hQmap, Polynomial.coeff_C_mul,
      Polynomial.X_pow_dvd_iff.mp hdvd j hj, mul_zero]
    rfl
  -- reduce to the residue field
  have hred := Polynomial.map_dvd (IsLocalRing.residue O) hQdvd
  rw [Polynomial.map_pow, Polynomial.map_X] at hred
  have hQred : Q.map (IsLocalRing.residue O)
      = (AO.map (IsLocalRing.residue O)
          + C (IsLocalRing.residue O αO) * UO.map (IsLocalRing.residue O))
        * (BO.map (IsLocalRing.residue O)
          + C (IsLocalRing.residue O βO) * WO.map (IsLocalRing.residue O))
        - C (IsLocalRing.residue O αO * IsLocalRing.residue O βO) := by
    rw [hQ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
      Polynomial.map_C, map_mul]
  rw [hQred] at hred
  have hUunit : IsUnit (UO.coeff m) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨(U.coeff m)⁻¹, hUm⟩, ?_⟩
    apply Subtype.val_injective
    show ((UO.coeff m : O) : E) * (U.coeff m)⁻¹ = 1
    rw [valLift_coeff]
    exact mul_inv_cancel₀ hUm0
  have hWunit : IsUnit (WO.coeff n) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨(W.coeff n)⁻¹, hWn⟩, ?_⟩
    apply Subtype.val_injective
    show ((WO.coeff n : O) : E) * (W.coeff n)⁻¹ = 1
    rw [valLift_coeff]
    exact mul_inv_cancel₀ hWn0
  have hAdeg' : (AO.map (IsLocalRing.residue O)).natDegree < m := by
    refine lt_of_le_of_lt (Polynomial.natDegree_map_le) ?_
    rw [hAO, valLift_natDegree_le]
    exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) hAdeg
  have hBdeg' : (BO.map (IsLocalRing.residue O)).natDegree < n := by
    refine lt_of_le_of_lt (Polynomial.natDegree_map_le) ?_
    rw [hBO, valLift_natDegree_le]
    exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) hBdeg
  have hleft : AO.map (IsLocalRing.residue O) ≠ 0 ∨ IsLocalRing.residue O αO ≠ 0 := by
    rcases hαcase with h1 | ⟨x, hx, hx1⟩
    · refine Or.inr ?_
      have : αO = 1 := Subtype.ext h1
      rw [this, map_one]
      exact one_ne_zero
    · refine Or.inl ?_
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      intro hzero
      have hcoeff : (AO.map (IsLocalRing.residue O)).coeff i = 0 := by rw [hzero]; simp
      rw [Polynomial.coeff_map] at hcoeff
      have hone : AO.coeff i = 1 := by
        apply Subtype.val_injective
        rw [hAO, valLift_coeff, Polynomial.coeff_C_mul]
        exact hx1
      rw [hone, map_one] at hcoeff
      exact one_ne_zero hcoeff
  have hright : BO.map (IsLocalRing.residue O) ≠ 0 ∨ IsLocalRing.residue O βO ≠ 0 := by
    rcases hβcase with h1 | ⟨x, hx, hx1⟩
    · refine Or.inr ?_
      have : βO = 1 := Subtype.ext h1
      rw [this, map_one]
      exact one_ne_zero
    · refine Or.inl ?_
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      intro hzero
      have hcoeff : (BO.map (IsLocalRing.residue O)).coeff i = 0 := by rw [hzero]; simp
      rw [Polynomial.coeff_map] at hcoeff
      have hone : BO.coeff i = 1 := by
        apply Subtype.val_injective
        rw [hBO, valLift_coeff, Polynomial.coeff_C_mul]
        exact hx1
      rw [hone, map_one] at hcoeff
      exact one_ne_zero hcoeff
  have hUcoeff : (UO.map (IsLocalRing.residue O)).coeff m ≠ 0 := by
    rw [Polynomial.coeff_map]
    intro h
    rw [IsLocalRing.residue_eq_zero_iff] at h
    exact (IsLocalRing.notMem_maximalIdeal.mpr hUunit) h
  have hWcoeff : (WO.map (IsLocalRing.residue O)).coeff n ≠ 0 := by
    rw [Polynomial.coeff_map]
    intro h
    rw [IsLocalRing.residue_eq_zero_iff] at h
    exact (IsLocalRing.notMem_maximalIdeal.mpr hWunit) h
  obtain ⟨hαne, hβne⟩ := critical_biprojective_boundary_exclusion_of_marked_coefficients
    hAdeg' hBdeg' hUcoeff hWcoeff hleft hright hred
  have hαunit : IsUnit αO := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff]
    exact hαne
  have hβunit : IsUnit βO := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff]
    exact hβne
  obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp hαunit
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hβunit
  constructor
  · intro i
    have hmem := hAmem i
    rw [Polynomial.coeff_C_mul] at hmem
    have : Alow.coeff i = (u : E) * (α * Alow.coeff i) := by
      have hone : (α : E) * (u : E) = 1 := congrArg Subtype.val hu
      rw [← mul_assoc, mul_comm (u : E) α, hone, one_mul]
    rw [this]
    exact O.mul_mem _ _ u.property hmem
  · intro i
    have hmem := hBmem i
    rw [Polynomial.coeff_C_mul] at hmem
    have : Blow.coeff i = (w : E) * (β * Blow.coeff i) := by
      have hone : (β : E) * (w : E) = 1 := congrArg Subtype.val hw
      rw [← mul_assoc, mul_comm (w : E) β, hone, one_mul]
    rw [this]
    exact O.mul_mem _ _ w.property hmem

end GaloisForLFunctions.HTGeometry
