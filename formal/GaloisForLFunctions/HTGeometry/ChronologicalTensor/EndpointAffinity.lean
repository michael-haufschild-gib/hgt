import GaloisForLFunctions.HTGeometry.ChronologicalTensor.TwoGap

/-!
# Endpoint affinity and the complete gap bridge

Each endpoint belongs to exactly one chord. Isolating that factor proves
that every perfect-pairing response is affine in each endpoint coordinate.
The identities hold for every real interpolation parameter.

Summing endpoint pulses also identifies the interval-window response with
the endpoint-pairing response for arbitrary gaps, including reversed gaps.
These identities are the algebraic basis for monotone coalescence.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

def endpointPositions {n : ℕ} (g : Fin n → ℝ) (q : Fin n) : ℝ :=
  ∑ cut, endpointPulse cut (g cut) q

theorem endpointPositions_difference {n : ℕ} (g : Fin n → ℝ) (a b : Fin n) :
    endpointPositions g b-endpointPositions g a = endpointOrderSign a b*
      windowValue (Finset.Ico (min a b) (max a b)) g := by
  classical
  simp only [endpointPositions,← Finset.sum_sub_distrib,endpointPulse_difference,
    ← Finset.mul_sum]
  congr 1
  simp only [Finset.sum_ite_mem,Finset.univ_inter,windowValue]

theorem enumeratedPairing_gap_value {d : ℕ}
    (e : (Fin d ⊕ Fin d) ≃ Fin (2*d)) (g : Fin (2*d) → ℝ) :
    enumeratedPairingValue e (endpointPositions g) = enumeratedPairingSign e*
      diagramValue (enumeratedPairingWindows e) g := by
  simp only [enumeratedPairingValue,endpointPositions_difference,Finset.prod_mul_distrib,
    enumeratedPairingSign,diagramValue,enumeratedPairingWindows]

theorem enumeratedFamily_gap_value {d m : ℕ}
    (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) (c : Fin m → ℝ)
    (g : Fin (2*d) → ℝ) :
    familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c) g =
      enumeratedPairingFamilyValue E c (endpointPositions g) := by
  simp only [familyValue,enumeratedFamilyWindows,enumeratedFamilyCoefficients,
    enumeratedPairingFamilyValue,enumeratedPairing_gap_value,mul_assoc]

theorem enumeratedPairing_update_left {d : ℕ}
    (e : (Fin d ⊕ Fin d) ≃ Fin (2*d)) (x : Fin (2*d) → ℝ) (j : Fin d) (t : ℝ) :
    enumeratedPairingValue e (Function.update x (e (Sum.inl j)) t) =
      (x (e (Sum.inr j))-t)*
        ∏ i ∈ Finset.univ.erase j, (x (e (Sum.inr i))-x (e (Sum.inl i))) := by
  classical
  unfold enumeratedPairingValue
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  have hrl (i : Fin d) : e (Sum.inr i) ≠ e (Sum.inl j) := by
    intro h
    have := e.injective h
    cases this
  simp only [Function.update_self,Function.update_of_ne (hrl j)]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hij := (Finset.mem_erase.mp hi).1
  have hll : e (Sum.inl i) ≠ e (Sum.inl j) := by
    intro h
    exact hij (Sum.inl.inj (e.injective h))
  simp only [Function.update_of_ne (hrl i),Function.update_of_ne hll]

theorem enumeratedPairing_update_right {d : ℕ}
    (e : (Fin d ⊕ Fin d) ≃ Fin (2*d)) (x : Fin (2*d) → ℝ) (j : Fin d) (t : ℝ) :
    enumeratedPairingValue e (Function.update x (e (Sum.inr j)) t) =
      (t-x (e (Sum.inl j)))*
        ∏ i ∈ Finset.univ.erase j, (x (e (Sum.inr i))-x (e (Sum.inl i))) := by
  classical
  unfold enumeratedPairingValue
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  have hlr (i : Fin d) : e (Sum.inl i) ≠ e (Sum.inr j) := by
    intro h
    have := e.injective h
    cases this
  simp only [Function.update_self,Function.update_of_ne (hlr j)]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hij := (Finset.mem_erase.mp hi).1
  have hrr : e (Sum.inr i) ≠ e (Sum.inr j) := by
    intro h
    exact hij (Sum.inr.inj (e.injective h))
  simp only [Function.update_of_ne (hlr i),Function.update_of_ne hrr]

theorem enumeratedPairing_endpoint_affine {d : ℕ}
    (e : (Fin d ⊕ Fin d) ≃ Fin (2*d)) (x : Fin (2*d) → ℝ)
    (q : Fin (2*d)) (s t u : ℝ) :
    enumeratedPairingValue e (Function.update x q ((1-u)*s+u*t)) =
      (1-u)*enumeratedPairingValue e (Function.update x q s)+
        u*enumeratedPairingValue e (Function.update x q t) := by
  have hq := e.apply_symm_apply q
  cases h : e.symm q with
  | inl j =>
    rw [h] at hq
    rw [← hq,enumeratedPairing_update_left,enumeratedPairing_update_left,
      enumeratedPairing_update_left]
    ring
  | inr j =>
    rw [h] at hq
    rw [← hq,enumeratedPairing_update_right,enumeratedPairing_update_right,
      enumeratedPairing_update_right]
    ring

theorem enumeratedFamily_endpoint_affine {d m : ℕ}
    (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) (c : Fin m → ℝ)
    (x : Fin (2*d) → ℝ) (q : Fin (2*d)) (s t u : ℝ) :
    enumeratedPairingFamilyValue E c (Function.update x q ((1-u)*s+u*t)) =
      (1-u)*enumeratedPairingFamilyValue E c (Function.update x q s)+
        u*enumeratedPairingFamilyValue E c (Function.update x q t) := by
  simp only [enumeratedPairingFamilyValue,enumeratedPairing_endpoint_affine]
  simp only [mul_add,Finset.sum_add_distrib]
  rw [Finset.mul_sum,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;> ring

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
