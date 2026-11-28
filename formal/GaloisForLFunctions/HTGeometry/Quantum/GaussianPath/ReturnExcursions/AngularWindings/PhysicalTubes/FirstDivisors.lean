import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.Laboratory
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.Subdivision
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ElapsedWindow.Reflection
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.PrefixProbability

/-! # Winding divisors at the first affordable visit of the frozen chain -/

open Matrix Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
open PrescribedTimes ShortWindows SharpOccupation
noncomputable section

/-- At the first affordable date, a divisor of all relative winding increments
from an earlier fit of the same circuit must put the last intermediate
subdivision strictly before the original robust crossing. -/
theorem first_visit_winding_divisors (ω : PathPauliDisorder) (k s : ℕ) :
    let K := k+3
    let X := prefixPoint k ω
    let P := nearHilbertContinuousCircuitBudget K
    let H := prefixGenerator (k+1) X
    let V := H.2.isHermitian.eigenvectorUnitary
    let A (i : Fin K → Bool) := -H.2.isHermitian.eigenvalues i/(2*π)
    let σ := crossingOrigin (k+1) P (9/80) X
    let Δ := crossingWait (k+1) P s X
    let v := σ+Δ
    let x := physicalArc (1/10)
    (∃ C : TwoQubitCircuit K, C.gateCount ≤ s ∧ v∈laboratoryDates H C.eval (1/10)) ∧
      ∀ C : TwoQubitCircuit K, C.gateCount ≤ s → let W := V⁻¹*C.eval*V
        ∀ u < v, ∀ m n : (Fin K → Bool) → ℤ,
        u∈wordDates W A (circuitTurns W) m x (1/10) →
        v∈wordDates W A (circuitTurns W) n x (1/10) →
        ∀ i₀, ∀ d : ℕ, 2 ≤ d → (∀ i, (d:ℤ) ∣ n i-m i-(n i₀-m i₀)) →
          (d:ℝ)*Δ<v-u := by
  intro K X P H V A σ Δ v x
  have he : (1/10:ℝ)∈Ioo 0 (sqrt 2) := ⟨by norm_num,
    (by norm_num : (1/10:ℝ)<1).trans_le (one_le_sqrt.mpr (by norm_num))⟩
  constructor
  · have hh := ElapsedWindow.first_wait_fit (k+1) P s X
    obtain ⟨z,hz,C,hC,hfit⟩ := (hasProjectiveCircuitApproximation_iff_infDist ..).mpr hh.2
    exact ⟨C,hC,z,hz,hfit⟩
  · intro C hC W u huv m n hu hv i₀ d hd hdiv
    let t := u+((d-1:ℕ):ℝ)/d*(v-u)
    have hd₀ : 0<(d:ℝ) := by exact_mod_cast (by omega : 0<d)
    have hm : t∈laboratoryDates H C.eval (1/10) := by
      rw [laboratoryDates_eq]
      exact subdivision_fit W A m n i₀ he hu hv (by omega) hdiv (d-1) (Nat.sub_le ..)
    have htime : (d:ℝ)*t=(d:ℝ)*v-(v-u) := by
      dsimp only [t]
      rw [Nat.cast_sub (by omega : 1≤d),Nat.cast_one]
      field_simp [hd₀.ne']
      ring
    have htv : t<v := (mul_lt_mul_iff_right₀ hd₀).mp (by linarith only [htime,huv])
    have hbefore : t<σ := by
      by_contra! hσ
      obtain ⟨z,hz,hclose⟩ := hm
      have hfreq : pathGateDistance (k+1) s X t≤1/10 :=
        (hasProjectiveCircuitApproximation_iff_infDist ..).mp ⟨z,hz,C,hC,hclose⟩
      have hmin := (crossingWait_le_iff (k+1) P s X (t-σ)).mpr
        ⟨t,⟨hσ,by change t≤σ+(t-σ); linarith⟩,hfreq⟩
      change Δ≤t-σ at hmin
      change t<σ+Δ at htv
      linarith only [htv,hmin]
    change (d:ℝ)*t=(d:ℝ)*(σ+Δ)-(v-u) at htime
    nlinarith only [htime,mul_lt_mul_of_pos_left hbefore hd₀]

#print axioms first_visit_winding_divisors
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
