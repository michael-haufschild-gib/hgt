import GaloisForLFunctions.RHTower.ChiRamanujanDampedSquarePerron
import GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareResidues
import GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareTails
import GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareEdges

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology
open GaloisForLFunctions.RHTower
namespace RHTower.BAGTrace

private theorem rectangle_solve (r l b u p : ℂ)
    (h : b-u+I*r-I*l = 2*Real.pi*I*p) :
    r-(2*Real.pi : ℂ)*p = l+I*(b-u) := by
  linear_combination (norm := (ring_nf; simp [I_sq])) -I*h

private theorem source_normalization (S P e x L : ℂ)
    (he : e ≠ 0) (hx : x ≠ 0) (hL : L ≠ 0) :
    S/(x*e^2*L)-P/(x*L) = ((2*Real.pi : ℂ)*S/e^2-(2*Real.pi : ℂ)*P) /
      ((2*Real.pi : ℂ)*x*L) := by
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- The actual physical square energy at the joint damping-height normalization. -/
def dampedSquareWindowEnergy (ε X : ℝ) : ℂ :=
  (∑' n : ℕ,(pmPowerDampedDivisorCoeff ε n : ℂ)^2*
    (bagPhysicalHeightWindow (n/X) : ℂ))/((X : ℂ)*(ε : ℂ)^2*Real.log X)

/-- Exact transfer error: both original tails, left edge and both horizontal edges. -/
theorem exists_dampedSquareWindowEnergy_transfer :
    ∃ d ∈ Ioc (0 : ℝ) (1/128), ∀ {T δ ε b X : ℝ},
      0 < T → 0 < δ → δ ≤ d/(1+T)^9 → 0 < ε → ε < δ/4 →
      0 < b → b ≤ δ → 1 < X →
      dampedSquareWindowEnergy ε X-dampedSquareResiduePacket ε X =
        (((∫ t : ℝ,dampedSquareContourIntegrand ε X ((1+b : ℝ)+t*I)) -
           ∫ t in (-T)..T,dampedSquareContourIntegrand ε X ((1+b : ℝ)+t*I)) +
         (∫ t in (-T)..T,dampedSquareContourIntegrand ε X ((1-δ : ℝ)+t*I)) +
         I*((∫ x in (1-δ)..(1+b),dampedSquareContourIntegrand ε X ((x : ℂ)+(-T)*I)) -
             ∫ x in (1-δ)..(1+b),dampedSquareContourIntegrand ε X ((x : ℂ)+T*I))) /
          ((2*Real.pi*X*Real.log X : ℝ) : ℂ) := by
  obtain ⟨d,hd,hrect⟩ := exists_dampedSquareContour_rectangle
  refine ⟨d,hd,?_⟩
  intro T δ ε b X hT hδ hδd hε hεδ hb hbδ hX
  have hδsmall : δ ≤ d := hδd.trans (div_le_self hd.1.le (one_le_pow₀ (by linarith)))
  have hε1 : ε < 1/16 := by linarith [hd.2]
  have he := hrect hT hδ hδd hε hεδ hb hbδ (by linarith : 0 < X)
  simp only [rectIntegral,sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,
    mul_zero,sub_zero,add_zero,sub_im,add_im,mul_im,mul_one,zero_sub,
    zero_add,smul_eq_mul,ofReal_neg] at he
  have hper := dampedSquare_weighted_sum_normalized_eq_integral hε.le hε1 hX.le
    (show 1 < 1+b by linarith)
  let P := dampedSquareMellinNumerator ε X 1/(2*ε)+
    dampedSquareMellinNumerator ε X (1-2*ε)/(-2*ε)
  have hline :
      (∫ t in (-T)..T,dampedSquareContourIntegrand ε X ((1+b : ℝ)+t*I)) -
        (2*Real.pi : ℂ)*P =
      (∫ t in (-T)..T,dampedSquareContourIntegrand ε X ((1-δ : ℝ)+t*I)) +
        I*((∫ x in (1-δ)..(1+b),dampedSquareContourIntegrand ε X ((x : ℂ)+(-T)*I)) -
           ∫ x in (1-δ)..(1+b),dampedSquareContourIntegrand ε X ((x : ℂ)+T*I)) := by
    exact rectangle_solve _ _ _ _ P he
  have hX0 : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have he0 : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
  have hL0 : (Real.log X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hX).ne'
  rw [add_assoc,← hline,← hper,sub_add_sub_cancel]
  simpa only [dampedSquareWindowEnergy,dampedSquareResiduePacket,P,ofReal_mul,
    ofReal_ofNat] using source_normalization
      (∑' n : ℕ,(pmPowerDampedDivisorCoeff ε n : ℂ)^2*(bagPhysicalHeightWindow (n/X) : ℂ))
      P ε X (Real.log X) he0 hX0 hL0

private theorem transfer_numerator_norm_le (r l b u : ℂ) :
    ‖r+l+I*(b-u)‖ ≤ ‖r‖+‖l‖+‖b‖+‖u‖ := by
  calc _ ≤ ‖r+l‖+‖I*(b-u)‖ := norm_add_le _ _
    _ ≤ (‖r‖+‖l‖)+(‖b‖+‖u‖) := by
      rw [norm_mul,norm_I,one_mul]
      exact add_le_add (norm_add_le _ _) (norm_sub_le _ _)
    _ = _ := by ring

/-- Complete actual transfer error, uniform in damping and retaining every edge/tail. -/
theorem exists_dampedSquareWindowEnergy_remainder_bound :
    ∃ d ∈ Ioc (0 : ℝ) (1/128), ∀ j : ℕ, 2 ≤ j → ∃ K > 0,
    ∀ {T δ ε b X : ℝ}, 1 ≤ T → 0 < δ → δ ≤ d/(1+T)^9 →
      0 < ε → ε < δ/4 → 0 < b → b ≤ δ → 1 < X →
      ‖dampedSquareWindowEnergy ε X-dampedSquareResiduePacket ε X‖ ≤
        K*(X^(1+b)/b^3*(T^(1-(j : ℝ))/((j : ℝ)-1)) +
          X^(1-δ)*(1+T)^55*(1+2/δ^2) +
          X^(1+b)*(1+T)^54/(1+T)^j)/(X*Real.log X) := by
  obtain ⟨d₁,hd₁,htransfer⟩ := exists_dampedSquareWindowEnergy_transfer
  obtain ⟨d₂,hd₂,C,hC,hedges⟩ := exists_dampedSquareContour_edge_bounds
  let d := min d₁ d₂
  have hd : d ∈ Ioc (0 : ℝ) (1/128) :=
    ⟨lt_min hd₁.1 hd₂.1,(min_le_left _ _).trans hd₁.2⟩
  refine ⟨d,hd,?_⟩
  intro j hj
  obtain ⟨A,hA,horiz⟩ := hedges j
  obtain ⟨B,hB,htails⟩ := exists_dampedSquareContour_two_tail_bound j hj
  let K := B+C+2*A
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K/(2*Real.pi),by positivity,?_⟩
  intro T δ ε b X hT hδ hδd hε hεδ hb hbδ hX
  have hX0 : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hδ₁ : δ ≤ d₁/(1+T)^9 := hδd.trans
    (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity))
  have hδ₂ : δ ≤ d₂/(1+T)^9 := hδd.trans
    (div_le_div_of_nonneg_right (min_le_right _ _) (by positivity))
  have hδsmall : δ ≤ d := hδd.trans (div_le_self hd.1.le (one_le_pow₀ (by linarith)))
  have hε1 : ε < 1/16 := by linarith [hd.2]
  have hb1 : b ≤ 1 := by linarith [hd.2]
  have hT0 : 0 < T := by linarith
  have hjR : (1 : ℝ) < j := by exact_mod_cast (show 1 < j by omega)
  let D := X^(1+b)/b^3*(T^(1-(j : ℝ))/((j : ℝ)-1))
  let L := X^(1-δ)*(1+T)^55*(1+2/δ^2)
  let H := X^(1+b)*(1+T)^54/(1+T)^j
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have htail : ‖(∫ t : ℝ,dampedSquareContourIntegrand ε X ((1+b : ℝ)+t*I)) -
      ∫ t in (-T)..T,dampedSquareContourIntegrand ε X ((1+b : ℝ)+t*I)‖ ≤ B*D := by
    convert htails hε hε1 hb hb1 hX0 hT0 using 1
    dsimp [D]
    ring
  obtain ⟨hl,hh⟩ := horiz hT hδ hδ₂ hε hεδ hb hbδ hX.le
  have hleft : ‖∫ t in (-T)..T,dampedSquareContourIntegrand ε X ((1-δ : ℝ)+t*I)‖ ≤ C*L := by
    convert hl using 1
    dsimp [L]
    ring
  have hbottom : ‖∫ x in (1-δ)..(1+b),dampedSquareContourIntegrand ε X ((x : ℂ)+(-T)*I)‖ ≤ A*H := by
    simpa only [H,ofReal_neg,mul_div_assoc,mul_assoc] using hh (-T) (by rw [abs_neg,abs_of_pos hT0])
  have htop : ‖∫ x in (1-δ)..(1+b),dampedSquareContourIntegrand ε X ((x : ℂ)+T*I)‖ ≤ A*H := by
    convert hh T (abs_of_pos hT0) using 1
    dsimp [H]
    ring
  rw [htransfer hT0 hδ hδ₁ hε hεδ hb hbδ hX,norm_div,Complex.norm_real,
    Real.norm_of_nonneg (by positivity : 0 ≤ 2*Real.pi*X*Real.log X)]
  have htriangle := transfer_numerator_norm_le
    ((∫ t : ℝ,dampedSquareContourIntegrand ε X ((1+b : ℝ)+t*I)) -
      ∫ t in (-T)..T,dampedSquareContourIntegrand ε X ((1+b : ℝ)+t*I))
    (∫ t in (-T)..T,dampedSquareContourIntegrand ε X ((1-δ : ℝ)+t*I))
    (∫ x in (1-δ)..(1+b),dampedSquareContourIntegrand ε X ((x : ℂ)+(-T)*I))
    (∫ x in (1-δ)..(1+b),dampedSquareContourIntegrand ε X ((x : ℂ)+T*I))
  have hnum : B*D+C*L+A*H+A*H ≤ K*(D+L+H) := by
    have hBK : B ≤ K := by dsimp [K]; linarith
    have hCK : C ≤ K := by dsimp [K]; linarith
    have hAK : 2*A ≤ K := by dsimp [K]; linarith
    calc _ = B*D+C*L+(2*A)*H := by ring
      _ ≤ K*D+K*L+K*H := by gcongr
      _ = _ := by ring
  calc _ ≤ (B*D+C*L+A*H+A*H)/(2*Real.pi*X*Real.log X) := by
        gcongr
        exact htriangle.trans (by gcongr)
    _ ≤ K*(D+L+H)/(2*Real.pi*X*Real.log X) := by gcongr
    _ = _ := by dsimp [D,L,H]; ring

end RHTower.BAGTrace
