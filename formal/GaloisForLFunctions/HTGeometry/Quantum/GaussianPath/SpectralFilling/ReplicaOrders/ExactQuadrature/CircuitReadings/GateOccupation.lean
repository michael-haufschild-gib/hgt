import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.CircuitReadings.PositiveMoments
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.FiniteCircuitWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.Spacing.PhysicalRecords

/-! # Gate occupation at the individual binary-clock dates -/
open Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
open SharpOccupation ReplicaOrders
noncomputable section

/-- The observed event is a fit at the specified physical error and budget. -/
def gateIndicator {K : ℕ} (H : selfAdjoint (Register K)) (s : ℕ) (ε t : ℝ) : ℝ := by
  classical
  exact if HasProjectiveCircuitApproximation K ε s (unitaryEvolution H.val t) then 1 else 0

/-- At any origin the fraction of binary readings admitting a short
circuit is bounded by the circuit net size times the permutation floor.
No asymptotic time average or minimum detuning enters this estimate. -/
theorem sampled_gate_occupation {K : ℕ} (H : selfAdjoint (Register K))
    (hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues)
    (s q : ℕ) (a ε δ ρ : ℝ) (hδ : 0<δ) (he : ε+δ≤ρ) (hρ : 0≤ρ) (hsmall : ρ^2<2) :
    let D : ℕ := 2^K
    let E := H.2.isHermitian.eigenvalues ∘ (qubitConfigFin K).symm
    let N := ((s:ℝ)+1)*((((K:ℝ)+1)^2)*(1+4*(s:ℝ)/δ)^32)^s
    reading (frequencies E q).toList (gateIndicator H s ε) a ≤
      N*(((q.factorial:ℝ)/(D:ℝ)^q)/(1-ρ^2/2)^(2*q)) := by
  classical
  intro D E N
  let τ := 1-ρ^2/2
  have hτ : 0<τ := by dsimp only [τ]; linarith only [hsmall]
  let w := microcanonicalWeight (Fin D)
  have hw (i : Fin D) : 0<w i := by dsimp only [w,microcanonicalWeight]; positivity
  obtain ⟨F,hcover,hcard⟩ := exists_budget_net K s δ hδ
  choose v hv htest using fun i : F => target_twist H i.val 0
  let f (i : F) (t : ℝ) := ‖twistedFiniteSpectralAmplitude w E (v i) t‖^(2*q)
  have hnon (i : F) (t : ℝ) : 0≤f i t := pow_nonneg (norm_nonneg _) _
  have hdom (t : ℝ) : τ^(2*q)*gateIndicator H s ε t≤∑ i:F, f i t := by
    by_cases h : HasProjectiveCircuitApproximation K ε s (unitaryEvolution H.val t)
    · rw [gateIndicator,if_pos h,mul_one]
      obtain ⟨c,hc,C,hC,hfit⟩ := h
      obtain ⟨W,hW,hnear⟩ := hcover C hC
      let i : F := ⟨W,hW⟩
      have hd := norm_sub_le_norm_sub_add_norm_sub (unitaryEvolution H.val t)
        (c • (C.eval:Register K)) (c • (W:Register K))
      rw [←smul_sub,norm_smul,hc,one_mul] at hd
      have ht := htest i t c hc ρ hρ hsmall (hd.trans ((add_le_add hfit hnear).trans he))
      have hh : τ≤‖twistedFiniteSpectralAmplitude w E (v i) t‖ := by simpa only [sub_zero] using ht
      exact (pow_le_pow_left₀ hτ.le hh _).trans (single_le_sum (fun j _ => hnon j t) (mem_univ i))
    · rw [gateIndicator,if_neg h,mul_zero]
      exact sum_nonneg fun j _ => hnon j t
  let ws := (frequencies E q).toList
  have hh := reading_mono ws hdom a
  rw [reading_mul,reading_sum] at hh
  let M := (q.factorial:ℝ)/(D:ℝ)^q
  have hM : 0≤M := div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
  have hprice (i : F) : reading ws (f i) a≤M := by
    apply (reading_trace_floor w E hw (hmax.comp_equiv _) (v i) (hv i) q a).trans
    simpa only [M,w,Fintype.card_fin] using fidelityReplicaPermutationFloor_microcanonical_le (I:=Fin D) q
  have h := hh.trans (sum_le_sum fun i _ => hprice i)
  rw [sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul,mul_comm (τ^(2*q))] at h
  have hpow := pow_pos hτ (2*q)
  exact ((le_div_iff₀ hpow).mpr h).trans
    ((le_of_eq (mul_div_assoc ..)).trans (mul_le_mul_of_nonneg_right hcard (div_nonneg hM hpow.le)))

#print axioms sampled_gate_occupation
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
