import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! # Fixed density and wire scales for longitudinal packet tests -/

open Real
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section

/-- The energy discarded on packets with excessive norm, the mass on weak
packets, and the remaining mass on too few regular packets together
account for less than half the original longitudinal field. -/
theorem exists_mass_scales {u v : ℝ} (hu : 0<u) (hv : 0<v) :
    ∃ C>0, ∃ γ>0, γ≤1 ∧ ∀ {L q b g a : ℝ}, 0<L → 0<q → b≤2*q → g≤γ*q →
      0≤a → a≤1 →
      b*(u*L/16)+g*(sqrt L*(C*sqrt L))+sqrt L/(C*sqrt L)*(v*(q*L)) <
        u*(q*L)/(1+a) := by
  let C := 16*v/u
  let γ := min 1 (u/(16*C))
  have hC : 0<C := by dsimp only [C]; positivity
  have hγ : 0<γ := lt_min zero_lt_one (by positivity)
  have hγC : γ*C≤u/16 := by
    have h := (le_div_iff₀ (show 0<16*C by positivity)).mp (min_le_right 1 (u/(16*C)))
    change min 1 (u/(16*C))*C≤u/16
    linarith only [h]
  have hCv : v/C=u/16 := by dsimp only [C]; field_simp; ring
  refine ⟨C,hC,γ,hγ,min_le_left ..,?_⟩
  intro L q b g a hL hq hb hg ha ha₁
  have hs := sqrt_pos.mpr hL
  have h₁ := mul_le_mul_of_nonneg_right hb (show 0≤u*L/16 by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hg (mul_nonneg hC.le hL.le)
  have h₃ := mul_le_mul_of_nonneg_right hγC (mul_nonneg hq.le hL.le)
  have he : sqrt L*(C*sqrt L)=C*L := by nlinarith only [congrArg (C*·) (sq_sqrt hL.le)]
  have hf : sqrt L/(C*sqrt L)*(v*(q*L))=(v/C)*(q*L) := by field_simp; ring
  have hhalf : u*(q*L)/2≤u*(q*L)/(1+a) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only [ha₁])
  rw [he,hf,hCv]
  apply lt_of_lt_of_le _ hhalf
  nlinarith only [h₁,h₂,h₃,mul_pos hu (mul_pos hq hL)]

/-- Taking the integer gate budget proportional to the total wire count
and the wire threshold proportional to the packet length bounds the
number of exceptional packet choices, with no rounding loss. -/
theorem packet_bit_budget {α τ L q : ℝ} (hα : 0<α) (hL : 0<L)
    (hτ : 0≤τ) (hq : 0≤q) {s r : ℕ} (hs : (s:ℝ)≤τ*(q*L))
    (hr : α*L≤(r:ℝ)+1) :
    ((2*s/(r+1):ℕ):ℝ)≤(2*τ/α)*q := by
  have h₀ : ((2*s/(r+1):ℕ):ℝ)≤((2*s:ℕ):ℝ)/((r+1:ℕ):ℝ) := Nat.cast_div_le
  push_cast at h₀
  apply h₀.trans
  apply (div_le_iff₀ (by positivity)).mpr
  calc 2*(s:ℝ) ≤ 2*(τ*(q*L)) := mul_le_mul_of_nonneg_left hs zero_le_two
       _ = (2*τ/α)*q*(α*L) := by field_simp; ring
       _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)

#print axioms exists_mass_scales
#print axioms packet_bit_budget
end
end GaloisForLFunctions.HTGeometry.BlockDilations
