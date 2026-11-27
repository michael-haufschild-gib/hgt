import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.ExtremePair.ArcPacking.Clock
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateOccupation

/-! # A volume deadline for a clock synchronizing two energies -/
open Finset Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PassageMoments.ExtremePair.ArcPacking
noncomputable section
open private mem_relativeEnclosingUnitArc_clock from GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateOccupation

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- A synchronized pair acts as one phase for the packing estimate.
The hitting radius is the exact chord of the doubled arc. -/
theorem synchronized_tick {n : ℕ} (H : selfAdjoint (Reg n)) (a b : Fin n → Bool)
    (hab : a≠b) (τ : ℝ) (z : ℤ)
    (hs : τ*(H.2.isHermitian.eigenvalues b-H.2.isHermitian.eigenvalues a)/(2*π)=z)
    (r : ℝ) (hr : 0<r) (hr' : r≤1/4) :
    let d : ℕ := 2^n-1
    ∃ q : ℕ, 0<q ∧ (q:ℝ)≤1/((d:ℝ)*r^(d-1)) ∧
      HasProjectiveCircuitApproximation n (2*sin (π*r)) 0 (unitaryEvolution H.val ((q:ℝ)*τ)) := by
  classical
  intro d
  let E := H.2.isHermitian.eigenvalues
  let v (i : Fin n → Bool) : UnitAddCircle := ((-(τ*E i)/(2*π):ℝ):UnitAddCircle)
  have hba : v b=v a := by
    apply sub_eq_zero.mp
    have he : -(τ*E b)/(2*π)- -(τ*E a)/(2*π) = -(z:ℝ) := by rw [←hs]; ring
    change ((-(τ*E b)/(2*π):ℝ):UnitAddCircle)-((-(τ*E a)/(2*π):ℝ):UnitAddCircle)=0
    rw [←AddCircle.coe_sub,he]
    apply (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr
    exact ⟨-z,by simp [zsmul_eq_mul]⟩
  let S := univ.erase b
  have ha : a∈S := mem_erase.mpr ⟨hab,mem_univ _⟩
  letI : Nonempty S := ⟨⟨a,ha⟩⟩
  let θ (i : S) := v i.val
  have hc : Fintype.card S=d := by
    rw [Fintype.card_coe,show S=univ.erase b from rfl,card_erase_of_mem (mem_univ _),card_univ]
    simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,d]
  let μ := (d:ℝ)*r^(d-1)
  have hd : 0<d := hc ▸ Fintype.card_pos
  have hμ : 0<μ := mul_pos (Nat.cast_pos.mpr hd) (pow_pos hr _)
  let N := ⌊1/μ⌋₊
  have hN : 1<((N:ℝ)+1)*μ := (div_lt_iff₀ hμ).mp (Nat.lt_floor_add_one _)
  obtain ⟨q,hq,hbound,hfit⟩ := packed_tick θ ⟨r,hr.le,by linarith only [hr']⟩ N (by simpa only [hc] using hN)
  have hq' : (q:ℝ)≤1/μ := (Nat.cast_le.mpr hbound).trans (Nat.floor_le (by positivity))
  refine ⟨q,hq,hq',?_⟩
  let e (i : Fin n → Bool) : S := if hi : i=b then ⟨a,ha⟩ else ⟨i,mem_erase.mpr ⟨hi,mem_univ _⟩⟩
  have hv (i : Fin n → Bool) : θ (e i)=v i := by
    by_cases he : i=b <;> simp [e,θ,he,hba]
  let t := (q:ℝ)*τ
  let R : Icc (0:ℝ) (1/2) := ⟨2*r,by positivity,by linarith only [hr']⟩
  have he : (q • θ) ∘ e = fun i => ((-(t*E i)/(2*π):ℝ):UnitAddCircle) := by
    funext i
    change q • θ (e i)=_
    rw [hv]
    dsimp only [v]
    rw [←AddCircle.coe_nsmul]
    congr 1
    rw [nsmul_eq_mul]
    dsimp only [t]
    ring
  have hphase := arc_pullback e (mul_nonneg (by norm_num) hr.le) hfit
  rw [he] at hphase
  have hL := (mem_enclosingUnitArc_iff_spectralEnclosingArcLength (fun j => -(t*E j)) R).mp hphase
  have hphysical := (zeroGateApproximation_iff_clock_shortArc H a t R).mpr
    ((mem_relativeEnclosingUnitArc_clock E a t R).mpr hL)
  simpa only [show π*(R:ℝ)/2=π*r by dsimp only [R]; ring] using hphysical

#print axioms synchronized_tick
end
end GaloisForLFunctions.HTGeometry.PassageMoments.ExtremePair.ArcPacking
