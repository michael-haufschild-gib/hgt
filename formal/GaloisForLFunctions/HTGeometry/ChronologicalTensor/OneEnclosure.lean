import GaloisForLFunctions.HTGeometry.ChronologicalTensor.Reversal

/-!
# One enclosure suppresses the cubic reversal advantage

The separated-minus-rainbow form has signed capacity greater than its monotone
capacity. Multiplication by net displacement restores the unit upper bound.
A rational cubic envelope handles small displacement; the remaining sign cases
reduce to an exact quartic comparison. All bounds include arbitrary signs and
the zero probe, without external assumptions or numerical certificates.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

theorem cubic_rational_envelope (a b c d e : ℝ) :
    |reversalResponse a b c d e| ≤ (8/7 : ℝ) * sixCost a b c d e ^ 3 := by
  have h := weightedSix_majorant 27 (-1) a b c d e
  simp only [weightedSixResponse, neg_one_mul, ← sub_eq_add_neg,
    abs_neg, abs_one,
    abs_of_nonneg (show (0 : ℝ) ≤ 27 by positivity), one_mul] at h
  let x := |b|+|c|+|d|
  let y := |a|+|e|
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have he : x+y = sixCost a b c d e := by dsimp [x,y,sixCost]; ring
  have hid : (8/7 : ℝ)*(x+y)^3 - (27/4*x*y^2+(x+y)*x^2) =
      (3*x-2*y)^2*(x+21*y)/75 + (x-y/2)^2*(x+4*y)/81 +
      149/14175*(x+y)^3 := by ring
  have hn : 0 ≤ (3*x-2*y)^2*(x+21*y)/75 + (x-y/2)^2*(x+4*y)/81 +
      (149/14175 : ℝ)*(x+y)^3 := by positivity
  rw [← hid, he] at hn
  exact h.trans (by dsimp [x,y] at hn ⊢; linarith)

theorem one_enclosure_reversal_bound (a b c d e : ℝ) :
    |(a+b+c+d+e)*reversalResponse a b c d e| ≤ sixCost a b c d e ^ 4 := by
  have quartic : ∀ T z L : ℝ, 0 ≤ T → 0 ≤ z → z ≤ T → 7*T/8 ≤ z →
      0 ≤ L → 2*L ≤ T+z →
      (27/4 : ℝ)*L*z*(T^2-z^2) - L^2*z*(27*T-29*z)/2 ≤ T^4 := by
    intro T z L hT hz hzT hhigh hL hLmax
    let H := (T+z)/2
    have hH : 0 ≤ H := by dsimp [H]; positivity
    have hLH : L ≤ H := by dsimp [H]; linarith
    have hgap : 0 ≤ T^2-z^2 := by nlinarith
    have hslope : 0 ≤ (27/4 : ℝ)*(T^2-z^2) - (27*T-29*z)*(H+L)/2 := by
      by_cases hc : 0 ≤ 27*T-29*z
      · have hprod := mul_le_mul_of_nonneg_left (show H+L ≤ T+z by dsimp [H] at *; linarith) hc
        have hpos := mul_nonneg (show 0 ≤ T+z by positivity) (show 0 ≤ 31*z-27*T by linarith)
        nlinarith
      · have hprod := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) (show 0 ≤ H+L by positivity)
        nlinarith
    have hdiff := mul_nonneg (mul_nonneg (sub_nonneg.mpr hLH) hz) hslope
    have hid : z^2*(T+z)^2/4 - ((27/4 : ℝ)*L*z*(T^2-z^2)-L^2*z*(27*T-29*z)/2) =
        (H-L)*z*((27/4 : ℝ)*(T^2-z^2)-(27*T-29*z)*(H+L)/2) := by dsimp [H]; ring
    rw [← hid] at hdiff
    have hlast : z^2*(T+z)^2/4 ≤ T^4 := by
      have h1 : z^2 ≤ T^2 := by nlinarith
      have h2 : (T+z)^2 ≤ 4*T^2 := by nlinarith
      have hh := mul_le_mul h1 h2 (sq_nonneg (T+z)) (sq_nonneg T)
      nlinarith
    linarith
  have core : ∀ a b c d e : ℝ, 0 ≤ a+b+c+d+e →
      |(a+b+c+d+e)*reversalResponse a b c d e| ≤ sixCost a b c d e ^ 4 := by
    intro a b c d e hS0
    let S := a+b+c+d+e
    let M := b+c+d
    let L := |b|+|c|+|d|
    let w := |a|+|e|
    let u := a+e
    let T := sixCost a b c d e
    have hS : 0 ≤ S := hS0
    have hL : 0 ≤ L := by dsimp [L]; positivity
    have hw : 0 ≤ w := by dsimp [w]; positivity
    have hT : 0 ≤ T := by dsimp [T,sixCost]; positivity
    have hTw : T = w+L := by dsimp [T,w,L,sixCost]; ring
    have hSu : S = u+M := by dsimp [S,u,M]; ring
    have hu : |u| ≤ w := abs_add_le a e
    have hM : |M| ≤ L := (abs_add_le (b+c) d).trans (add_le_add (abs_add_le b c) le_rfl)
    have hc : |c| ≤ L := by dsimp [L]; linarith [abs_nonneg b, abs_nonneg d]
    have hST : S ≤ T := by
      have hsum := (abs_add_le u M).trans (add_le_add hu hM)
      rw [← hSu, abs_of_nonneg hS, ← hTw] at hsum
      exact hsum
    have hP : reversalResponse a b c d e = c*(27*a*e-S*M) := by
      dsimp [reversalResponse,separatedThree,rainbowThree,S,M]; ring
    have hD := normalized_separated_bound a b c d e
    have hR := rainbow_bound a b c d e
    have hDr : |c*(27*a*e)| ≤ T^3 := by
      convert hD using 1
      dsimp [separatedThree,T]
      congr 1
      ring
    have hRr : |c*(S*M)| ≤ T^3 := by
      convert hR using 1
      dsimp [rainbowThree,T,S,M]
      congr 1
      ring
    change |S*reversalResponse a b c d e| ≤ T^4
    by_cases hlo : S ≤ 7*T/8
    · have hp := cubic_rational_envelope a b c d e
      change |reversalResponse a b c d e| ≤ (8/7 : ℝ)*T^3 at hp
      rw [abs_mul,abs_of_nonneg hS]
      calc
        S * |reversalResponse a b c d e| ≤ (7*T/8)*((8/7 : ℝ)*T^3) :=
          mul_le_mul hlo hp (abs_nonneg _) (by positivity)
        _ = T^4 := by ring
    have hhigh : 7*T/8 ≤ S := le_of_not_ge hlo
    rw [hP, abs_mul, abs_of_nonneg hS, abs_mul]
    by_cases hae : 0 ≤ a*e
    · by_cases hm : 0 ≤ M
      · have hd0 : 0 ≤ 27*a*e := by nlinarith only [hae]
        have hr0 : 0 ≤ S*M := mul_nonneg hS hm
        have hd : |c| *(27*a*e) ≤ T^3 := by simpa [abs_mul,abs_of_nonneg hd0] using hDr
        have hr : |c| *(S*M) ≤ T^3 := by simpa [abs_mul,abs_of_nonneg hr0] using hRr
        have hh : |c| * |27*a*e-S*M| ≤ T^3 := by
          have heq : |c| * |27*a*e-S*M| = |(|c|)*(27*a*e-S*M)| := by rw [abs_mul,abs_abs]
          rw [heq]
          apply abs_le.mpr
          constructor <;> nlinarith only [hd, hr, mul_nonneg (abs_nonneg c) hd0, mul_nonneg (abs_nonneg c) hr0]
        calc
          S*(|c| * |27*a*e-S*M|) ≤ T*T^3 := mul_le_mul hST hh (by positivity) hT
          _ = T^4 := by ring
      · have hm0 : M ≤ 0 := le_of_not_ge hm
        have hu0 : 0 ≤ u := by linarith only [hSu,hS,hm0]
        have haesq : w^2 = u^2 := by
          dsimp [w,u]
          nlinarith only [sq_abs a,sq_abs e,show |a| *|e| = a*e by rw [← abs_mul,abs_of_nonneg hae]]
        have hwu : w = u := by nlinarith only [haesq,hw,hu0]
        have htri : |c| ≤ -M+|b|+|d| := by
          have ht := (abs_add_le M (-b-d)).trans (add_le_add le_rfl (abs_add_le (-b) (-d)))
          have hid : M+(-b-d) = c := by dsimp [M]; ring
          rw [hid,abs_of_nonpos hm0,abs_neg,abs_neg] at ht
          linarith only [ht]
        have hcS : 2*|c| ≤ T-S := by dsimp [L] at hTw; rw [hwu] at hTw; linarith only [hTw,hSu,htri]
        have hSc : S*|c| ≤ T^2/8 := by
          have hh := mul_le_mul_of_nonneg_left hcS hS
          nlinarith only [hh,sq_nonneg (S-T/2)]
        have hAE : 4*(a*e) ≤ u^2 := by dsimp [u]; nlinarith only [sq_nonneg (a-e)]
        have huT : u ≤ T := by linarith only [hwu,hTw,hL]
        have huSq : u^2 ≤ T^2 := by nlinarith only [huT,hu0,hT]
        have hSM : 4*(S*(-M)) ≤ u^2 := by
          rw [show u = S-M by linarith only [hSu]]
          nlinarith only [sq_nonneg (S+M)]
        have hb0 : 0 ≤ 27*a*e-S*M := by nlinarith only [hae,mul_nonpos_of_nonneg_of_nonpos hS hm0]
        have hb : 27*a*e-S*M ≤ 7*T^2 := by nlinarith only [hAE,huSq,hSM]
        rw [abs_of_nonneg hb0]
        calc
          S*(|c| *(27*a*e-S*M)) = (S*|c|)*(27*a*e-S*M) := by ring
          _ ≤ (T^2/8)*(7*T^2) := mul_le_mul hSc hb hb0 (by positivity)
          _ ≤ T^4 := by nlinarith only [sq_nonneg (T^2)]
    · have hae0 : a*e ≤ 0 := le_of_not_ge hae
      by_cases hm : M ≤ 0
      · have hd0 : 27*a*e ≤ 0 := by nlinarith only [hae0]
        have hr0 : S*M ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hS hm
        have hd : -(|c| *(27*a*e)) ≤ T^3 := by simpa [abs_mul,abs_of_nonpos hd0] using hDr
        have hr : -(|c| *(S*M)) ≤ T^3 := by simpa [abs_mul,abs_of_nonpos hr0] using hRr
        have hh : |c| * |27*a*e-S*M| ≤ T^3 := by
          have heq : |c| * |27*a*e-S*M| = |(|c|)*(27*a*e-S*M)| := by rw [abs_mul,abs_abs]
          rw [heq]
          apply abs_le.mpr
          constructor <;> nlinarith only [hd, hr, mul_nonpos_of_nonneg_of_nonpos (abs_nonneg c) hd0,
            mul_nonpos_of_nonneg_of_nonpos (abs_nonneg c) hr0]
        calc
          S*(|c| * |27*a*e-S*M|) ≤ T*T^3 := mul_le_mul hST hh (by positivity) hT
          _ = T^4 := by ring
      · have hm0 : 0 ≤ M := le_of_not_ge hm
        let z := u+L
        have hML : M ≤ L := (le_abs_self M).trans hM
        have hSz : S ≤ z := by dsimp [z]; linarith
        have hz : 0 ≤ z := hS.trans hSz
        have hzT : z ≤ T := by dsimp [z]; linarith [(abs_le.mp hu).2]
        have hzm : 2*L ≤ T+z := by dsimp [z]; linarith [(abs_le.mp hu).1]
        have haesq : w^2-u^2 = -4*(a*e) := by
          dsimp [w,u]
          nlinarith only [sq_abs a,sq_abs e,show |a| *|e| = -(a*e) by rw [← abs_mul,abs_of_nonpos hae0]]
        have hb0 : 0 ≤ -27*a*e+S*M := by nlinarith only [hae0,mul_nonneg hS hm0]
        have hzL : S*M ≤ z*L := mul_le_mul hSz hML hm0 hz
        have hb : -27*a*e+S*M ≤ -27*a*e+z*L := by linarith only [hzL]
        have hn : 0 ≤ -27*a*e+z*L := hb0.trans hb
        have hprod := mul_le_mul (mul_le_mul hSz hc (abs_nonneg c) hz) hb hb0 (by positivity : 0 ≤ z*L)
        have habs : |27*a*e-S*M| = -27*a*e+S*M := by rw [abs_of_nonpos (by linarith only [hb0])]; ring
        rw [habs]
        calc
          S*(|c| *(-27*a*e+S*M)) = (S*|c|)*(-27*a*e+S*M) := by ring
          _ ≤ (z*L)*(-27*a*e+z*L) := hprod
          _ = (27/4 : ℝ)*L*z*(T^2-z^2)-L^2*z*(27*T-29*z)/2 := by
            have hid : (z*L)*(-27*a*e+z*L) =
                (z*L)*((27/4 : ℝ)*(w^2-u^2)+z*L) := by rw [haesq]; ring
            rw [hid,hTw]
            dsimp [z]
            ring
          _ ≤ T^4 := quartic T z L hT hz hzT (hhigh.trans hSz) hL hzm
  by_cases h : 0 ≤ a+b+c+d+e
  · exact core a b c d e h
  · have hn := core (-a) (-b) (-c) (-d) (-e) (by linarith)
    have hcost : sixCost (-a) (-b) (-c) (-d) (-e) = sixCost a b c d e := by simp [sixCost]
    have hid : (-a+-b+-c+-d+-e)*reversalResponse (-a) (-b) (-c) (-d) (-e) =
        (a+b+c+d+e)*reversalResponse a b c d e := by
      unfold reversalResponse separatedThree rainbowThree; ring
    rw [hcost,hid] at hn
    exact hn

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
