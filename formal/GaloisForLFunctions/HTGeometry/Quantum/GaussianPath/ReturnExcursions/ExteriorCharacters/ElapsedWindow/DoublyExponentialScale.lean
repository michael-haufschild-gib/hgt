import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.Supports.HammingPrice

/-! # Positive signed threshold on a doubly exponential horizon -/

open Filter
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.ElapsedWindow
noncomputable section

private theorem growth_room (C : ℝ) :
    let c := 1-(9/80:ℝ)^2/2
    ∀ᶠ n : ℕ in atTop, 320*(1+C*(4*n))*((9/10:ℝ)*(11/10))^(4*n)≤c^(4*n) := by
  intro c
  let z := (((9/10:ℝ)*(11/10))/c)^4
  have hz : 0≤z := by norm_num [z,c]
  have hz' : z<1 := by norm_num [z,c]
  have h₁ := tendsto_pow_atTop_nhds_zero_of_lt_one hz hz'
  have h₂ := tendsto_self_mul_const_pow_of_lt_one hz hz'
  have hlim : Tendsto (fun n : ℕ => 320*z^n+(1280*C)*((n:ℝ)*z^n)) atTop (nhds 0) := by
    simpa only [mul_zero,add_zero] using (h₁.const_mul 320).add (h₂.const_mul (1280*C))
  filter_upwards [hlim.eventually_lt_const zero_lt_one] with n hn
  have hc : 0<c^(4*n) := pow_pos (by norm_num [c]) _
  apply (div_le_one hc).mp
  rw [mul_div_assoc,←div_pow,pow_mul]
  calc
    _ = 320*z^n+(1280*C)*((n:ℝ)*z^n) := by dsimp only [z]; ring
    _ ≤ 1 := hn.le

/-- Even after the small-support subtraction and the duration of a fit,
the normalized threshold exceeds $(9/10)^D$ at horizon $(11/10)^D$
for every Hamiltonian with a linear bound on its norm. -/
theorem positive_window_price (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ h : ℝ, 0≤h → h≤C*(4*n) →
      let D := 4*n
      let B : ℝ := D.choose (2*n)
      let δ := (1/80)/(1+h)
      let L := (11/10:ℝ)^D
      B^2*(9/10)^D ≤ δ/(L+δ)*(B*(1-(9/80:ℝ)^2/2)^(2*n))^2-B*(2^n*(3/2)^D) := by
  filter_upwards [growth_room C,quarter_price_of_base (c:=9/10) (by norm_num)] with n hroom hnear
  intro h hh hC D B δ L
  let c : ℝ := 1-(9/80)^2/2
  let p : ℝ := 9/10
  have hp : 0≤p^D := pow_nonneg (by norm_num [p]) _
  have hL : 1≤L := one_le_pow₀ (by norm_num : (1:ℝ)≤11/10)
  have hden : 0<1+h := by linarith only [hh]
  have hδ : 0<δ := div_pos (by norm_num) hden
  have hδ₁ : δ≤1 := (div_le_one hden).mpr (by linarith only [hh])
  have hw : 0<L+δ := by linarith only [hL,hδ]
  have hsmall : 4*(p^D*L)≤δ*c^D := by
    dsimp only [δ]
    rw [div_mul_eq_mul_div,le_div_iff₀ hden]
    have hcoef : 320*(1+h)≤320*(1+C*(4*n)) := by linarith only [hC]
    have hbound := (mul_le_mul_of_nonneg_right hcoef (mul_nonneg hp (zero_le_one.trans hL))).trans
      (show 320*(1+C*(4*n))*(p^D*L)≤c^D by simpa only [p,c,D,L,mul_pow] using hroom)
    calc
      _ = (1/80:ℝ)*(320*(1+h)*(p^D*L)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by norm_num)
  have hratio : 2*p^D≤δ/(L+δ)*c^D := by
    rw [div_mul_eq_mul_div,le_div_iff₀ hw]
    calc
      _ ≤ 2*p^D*(2*L) := mul_le_mul_of_nonneg_left (by linarith only [hL,hδ₁]) (by positivity)
      _ ≤ _ := by nlinarith only [hsmall]
  have hB : 0≤B := Nat.cast_nonneg _
  have hleft := mul_le_mul_of_nonneg_left hratio (sq_nonneg B)
  have hright := mul_le_mul_of_nonneg_left hnear hB
  change B*(2^n*(3/2)^D) ≤ B*(1/2*B*p^D) at hright
  change B^2*p^D≤δ/(L+δ)*(B*c^(2*n))^2-B*(2^n*(3/2)^D)
  rw [mul_pow,←pow_mul,show 2*n*2=D by dsimp [D]; omega]
  nlinarith only [hleft,hright,mul_nonneg (sq_nonneg B) hp]

#print axioms positive_window_price
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.ElapsedWindow
