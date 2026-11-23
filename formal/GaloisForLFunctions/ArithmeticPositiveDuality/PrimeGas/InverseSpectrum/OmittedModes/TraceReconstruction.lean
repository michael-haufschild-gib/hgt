import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.FiniteRange
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.BoundaryArithmetic

/-! # Reconstructing the gas from fourth traces and omitted dimensions

Adjacent lower trace endpoints determine the energy of every occupation.
Their positive fourth-root amplitudes give the multiplicative prime-mode monoid.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap Set

/-- The directly measured fourth traces at each finite omitted dimension. -/
def measuredTraces (r : ℕ) : Set ℝ := {y | ∃ P : Projection, MissingDimension P r ∧
  Conserving (projected P) ∧ (opTrace ((projected P)^4)).re = y}

theorem measuredTraces_iff (r : ℕ) (y : ℝ) :
    y ∈ measuredTraces r ↔ (riemannZeta 2).re-y ∈ lossesAtRank r := by
  constructor
  · rintro ⟨P,hd,hc,rfl⟩
    exact ⟨P,hd,hc,rfl⟩
  · rintro ⟨P,hd,hc,he⟩
    exact ⟨P,hd,hc,sub_right_inj.mp he⟩

theorem measuredTraces_succ (r : ℕ) :
    measuredTraces (r+1) = Ioo ((riemannZeta 2).re-traceCeiling (r+1)) (riemannZeta 2).re := by
  ext y
  rw [measuredTraces_iff,lossesAtRank_succ,mem_Ioo,mem_Ioo]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith only [h₁,h₂]

theorem measuredTraces_zero : measuredTraces 0 = {(riemannZeta 2).re} := by
  ext y
  rw [measuredTraces_iff,lossesAtRank_zero,mem_singleton_iff,mem_singleton_iff,sub_eq_zero,eq_comm]

/-- A calibration-free increment obtained from two consecutive infimal raw traces. -/
def traceIncrement (r : ℕ) : ℝ := sInf (measuredTraces r)-sInf (measuredTraces (r+1))

theorem traceIncrement_eq (r : ℕ) : traceIncrement r = (((r:ℝ)+1)⁻¹)^2 := by
  have h (k : ℕ) : sInf (measuredTraces k) = (riemannZeta 2).re-traceCeiling k := by
    cases k with
    | zero => simp [measuredTraces_zero,traceCeiling]
    | succ k =>
      rw [measuredTraces_succ,csInf_Ioo (sub_lt_self _ (traceCeiling_pos (Nat.succ_pos k)))]
  rw [traceIncrement,h,h,← traceCeiling_succ r]
  abel

/-- The positive fourth roots of the observed increments are exactly the multiplicative modes. -/
theorem measured_modes (x : ℝ) :
    (0 < x ∧ ∃ r, x^4 = traceIncrement r) ↔ x ∈ boundaryModes := by
  have hin (r : ℕ) : attenuation (number r)^4 = traceIncrement r := by
    rw [traceIncrement_eq,← occupationWeight_eq,occupationWeight]
    ring
  constructor
  · rintro ⟨hx,r,he⟩
    have h := he.trans (hin r).symm
    have eqn : x = attenuation (number r) := by
      rcases lt_trichotomy x (attenuation (number r)) with hl | heq | hg
      · exact ((pow_lt_pow_left₀ hl hx.le (by decide : (4:ℕ) ≠ 0)).ne h).elim
      · exact heq
      · exact ((pow_lt_pow_left₀ hg (attenuation_pos _).le (by decide : (4:ℕ) ≠ 0)).ne h.symm).elim
    rw [eqn]
    exact (boundaryModeEquiv (number r)).property
  · intro hx
    obtain ⟨n,hn⟩ := boundaryModeEquiv.surjective (⟨x,hx⟩ : boundaryModes)
    obtain ⟨k,rfl⟩ := number_surjective n
    have he : attenuation (number k) = x := congrArg Subtype.val hn
    exact he ▸ ⟨attenuation_pos _,k,hin k⟩

def traceEnergy (r : ℕ) : ℝ := -(Real.log (traceIncrement r))/2

theorem traceEnergy_eq (r : ℕ) : traceEnergy r = energy (number r) := by
  rw [traceEnergy,traceIncrement_eq,Real.log_pow,Real.log_inv]
  change _ = Real.log ((↑(r+1):ℝ))
  rw [Nat.cast_add,Nat.cast_one]
  ring

/-- A sum over omitted dimensions alone, with energies from two trace infima, recovers the partition. -/
theorem partition_from_traces (s : {z : ℂ // 1 < z.re}) :
    ∑' r : ℕ, Complex.exp (-s.val*(traceEnergy r:ℂ)) = riemannZeta s.val := by
  let e : ℕ ≃ ℕ+ := Equiv.ofBijective number ⟨number_injective,number_surjective⟩
  rw [← insertedPartition_one s,insertedPartition_eq_series,← e.tsum_eq]
  apply tsum_congr
  intro k
  change Complex.exp (-s.val*(traceEnergy k:ℂ)) = (↑(1:Circle):ℂ)*heat s.val (number k)
  rw [traceEnergy_eq,Circle.coe_one,one_mul]
  rfl

#print axioms measuredTraces_succ
#print axioms traceIncrement_eq
#print axioms measured_modes
#print axioms traceEnergy_eq
#print axioms partition_from_traces

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
