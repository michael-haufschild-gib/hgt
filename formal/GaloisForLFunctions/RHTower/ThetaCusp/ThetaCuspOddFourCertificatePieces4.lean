import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourPieceSetup

/-!
# Piece certificates 15–19 on `q ∈ [21/5, 47/10]`

Each piece proves that the piece matrix `W(q)` of its compensation matrix is positive
semidefinite on its interval: every entry is affine in `t = q − q_*` up to an explicit radius
(Taylor shift of the polynomial numerators, linearized `e^{-3q}`, crude higher pairs and tail),
and both endpoint matrices with the row radii removed have an exact `LDLᵀ` factorization with
nonnegative pivots.
-/

namespace RHTower.ThetaCuspOddFourPieces
noncomputable section
open ThetaCuspOddCentralTail ThetaCuspOddFourCentralEntries ThetaCuspOddFourCentralBound
open ThetaCuspOddFourCertificateTools

/-! #### Piece 15 (seam), `q ∈ [21/5, 43/10]` -/

/-- The compensation matrix of piece 15. -/
def pieceX_15 : Fin 4 → Fin 4 → ℝ :=
  sym4 ((55310771321:ℝ)/5000000000000) ((-92982048037:ℝ)/125000000000000) ((224052875687:ℝ)/100000000000000) ((-161981029799:ℝ)/10000000000000) ((24949647159:ℝ)/1250000000000) ((-269302576627:ℝ)/10000000000000) ((195042349853:ℝ)/1000000000000) ((460001673167:ℝ)/5000000000000) ((-58630167601:ℝ)/100000000000) ((42569079329:ℝ)/10000000000)

theorem piece15_L3 : ((344551455396940947292714505003:ℝ)/1000000000000000000000000) ≤ Real.exp ((3:ℝ)*((17:ℝ)/4)) := by
  have h := le_exp_nat_add 12 (f := ((3:ℝ)/4)) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((17:ℝ)/4) = ((12:ℕ):ℝ) + ((3:ℝ)/4) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece15_U3 : Real.exp ((3:ℝ)*((17:ℝ)/4)) ≤ ((172275955240474463017463468103:ℝ)/500000000000000000000000) := by
  have h := exp_nat_add_le 12 (f := ((3:ℝ)/4)) (by norm_num) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((17:ℝ)/4) = ((12:ℕ):ℝ) + ((3:ℝ)/4) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem piece15_L8_at : ((391106005602355390279146778221:ℝ)/1000000000000000) ≤ Real.exp ((8:ℝ)*((21:ℝ)/5)) := by
  have h := le_exp_nat_add 33 (f := ((3:ℝ)/5)) (by norm_num)
  rw [show ((8:ℝ):ℝ)*((21:ℝ)/5) = ((33:ℕ):ℝ) + ((3:ℝ)/5) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece15_E8 {q : ℝ} (h0 : ((21:ℝ)/5) ≤ q) : Real.exp (-((8:ℝ))*q) ≤ 1/((391106005602355390279146778221:ℝ)/1000000000000000) := by
  have hm : Real.exp (-((8:ℝ))*q) ≤ Real.exp (-((8:ℝ)*((21:ℝ)/5))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece15_L8_at (le_refl _)).2

theorem piece15_L11_at : ((5799293210154367748248128699:ℝ)/50000000) ≤ Real.exp ((11:ℝ)*((21:ℝ)/5)) := by
  have h := le_exp_nat_add 46 (f := ((1:ℝ)/5)) (by norm_num)
  rw [show ((11:ℝ):ℝ)*((21:ℝ)/5) = ((46:ℕ):ℝ) + ((1:ℝ)/5) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece15_E11 {q : ℝ} (h0 : ((21:ℝ)/5) ≤ q) : Real.exp (-((11:ℝ))*q) ≤ 1/((5799293210154367748248128699:ℝ)/50000000) := by
  have hm : Real.exp (-((11:ℝ))*q) ≤ Real.exp (-((11:ℝ)*((21:ℝ)/5))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece15_L11_at (le_refl _)).2

theorem piece15_Lt_at : ((99375560574937156562341070943:ℝ)/5000000000) ≤ Real.exp (((529:ℝ)/50)*((21:ℝ)/5)) := by
  have h := le_exp_nat_add 44 (f := ((109:ℝ)/250)) (by norm_num)
  rw [show (((529:ℝ)/50):ℝ)*((21:ℝ)/5) = ((44:ℕ):ℝ) + ((109:ℝ)/250) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece15_Et {q : ℝ} (h0 : ((21:ℝ)/5) ≤ q) : Real.exp (-(((529:ℝ)/50))*q) ≤ 1/((99375560574937156562341070943:ℝ)/5000000000) := by
  have hm : Real.exp (-(((529:ℝ)/50))*q) ≤ Real.exp (-(((529:ℝ)/50)*((21:ℝ)/5))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece15_Lt_at (le_refl _)).2

theorem piece15_e00 {q : ℝ} (h0 : ((21:ℝ)/5) ≤ q) (h1 : q ≤ ((43:ℝ)/10)) :
    |pieceW q pieceX_15 0 0 - (((365796843547401301:ℝ)/50000000000) + (q - ((17:ℝ)/4)) * ((82685047305684533:ℝ)/5000000000))| ≤ ((436833273365836533:ℝ)/10000000000000) := by
  set t := q - ((17:ℝ)/4) with htd
  have hq : q = ((17:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece15_L3 piece15_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((17:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_00 q = ∑ e ∈ Finset.range 10, ([((59499107585:ℝ)/8192), ((33527083341:ℝ)/2048), ((132046701:ℝ)/8), ((156100749:ℝ)/16), ((59530821:ℝ)/16), ((3793125:ℝ)/4), (161364:ℝ), (17664:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_00; ring
  have h12 : centralNum12_00 q = ∑ e ∈ Finset.range 11, ([((-20018372162305:ℝ)/32768), ((-12483298972437:ℝ)/8192), ((-1752783649503:ℝ)/1024), ((-145916114739:ℝ)/128), ((-31896448815:ℝ)/64), ((-2390864343:ℝ)/16), (-31112907:ℝ), (-4441494:ℝ), (-415986:ℝ), (-23080:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_00; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((59499107585:ℝ)/8192), ((33527083341:ℝ)/2048), ((132046701:ℝ)/8), ((156100749:ℝ)/16), ((59530821:ℝ)/16), ((3793125:ℝ)/4), (161364:ℝ), (17664:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-20018372162305:ℝ)/32768), ((-12483298972437:ℝ)/8192), ((-1752783649503:ℝ)/1024), ((-145916114739:ℝ)/128), ((-31896448815:ℝ)/64), ((-2390864343:ℝ)/16), (-31112907:ℝ), (-4441494:ℝ), (-415986:ℝ), (-23080:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 9 ht
  have m12 := abs_poly_le (fun e => ([((-20018372162305:ℝ)/32768), ((-12483298972437:ℝ)/8192), ((-1752783649503:ℝ)/1024), ((-145916114739:ℝ)/128), ((-31896448815:ℝ)/64), ((-2390864343:ℝ)/16), (-31112907:ℝ), (-4441494:ℝ), (-415986:ℝ), (-23080:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 11 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((59499107585:ℝ)/8192), ((33527083341:ℝ)/2048), ((132046701:ℝ)/8), ((156100749:ℝ)/16), ((59530821:ℝ)/16), ((3793125:ℝ)/4), (161364:ℝ), (17664:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - (((59499107585:ℝ)/8192) + ((33527083341:ℝ)/2048)*t)| ≤ ((340061474112503:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 11, ([((-20018372162305:ℝ)/32768), ((-12483298972437:ℝ)/8192), ((-1752783649503:ℝ)/1024), ((-145916114739:ℝ)/128), ((-31896448815:ℝ)/64), ((-2390864343:ℝ)/16), (-31112907:ℝ), (-4441494:ℝ), (-415986:ℝ), (-23080:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e) - ((-20018372162305:ℝ)/32768) - ((-12483298972437:ℝ)/8192)*t| ≤ ((707986437818945759:ℝ)/160000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 11, ([((-20018372162305:ℝ)/32768), ((-12483298972437:ℝ)/8192), ((-1752783649503:ℝ)/1024), ((-145916114739:ℝ)/128), ((-31896448815:ℝ)/64), ((-2390864343:ℝ)/16), (-31112907:ℝ), (-4441494:ℝ), (-415986:ℝ), (-23080:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((108051431556976891:ℝ)/156250000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((49650979433:ℝ)/8192) - ((29471971749:ℝ)/2048)*t| ≤ ((311553438853703:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((43:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (600:ℝ), (-7776:ℝ), (16800:ℝ), (-9216:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m13' : |centralNum13_00 q| ≤ ((2287959496149562503:ℝ)/78125000) := by
    rw [centralNum13_00_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((43:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (780:ℝ), (-6156:ℝ), (15288:ℝ), (-14400:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m23' : |centralNum23_00 q| ≤ ((2471556115198452369:ℝ)/62500000) := by
    rw [centralNum23_00_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((172275955240474463017463468103:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece15_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece15_E11 h0) m23'
  have c5 := scaled_affine (X := ((55310771321:ℝ)/5000000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0))| ≤ ((11855195064968959047680000000:ℝ)/838289639484209165407096842587601) := by
    rw [abs_neg, tailWeight_0, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((43:ℝ)/10)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((43:ℝ)/10)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece15_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((10465499600:ℝ)/59049)) ≤ ((43:ℝ)/10)^6*(8000*(2*((43:ℝ)/10)-3)^2*(1/((99375560574937156562341070943:ℝ)/5000000000))*((10465499600:ℝ)/59049)) := by
          gcongr
      _ ≤ ((11855195064968959047680000000:ℝ)/838289639484209165407096842587601) := by norm_num
  have c7 := affine_round (α := ((59499107585:ℝ)/8192) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((-20018372162305:ℝ)/32768) + ((49650979433:ℝ)/8192)*((55310771321:ℝ)/5000000000000) - ((365796843547401301:ℝ)/50000000000)) (β := ((33527083341:ℝ)/2048) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((-12483298972437:ℝ)/8192) - 3*((-20018372162305:ℝ)/32768)) + ((29471971749:ℝ)/2048)*((55310771321:ℝ)/5000000000000) - ((82685047305684533:ℝ)/5000000000)) ht
  have hW : pieceW q pieceX_15 0 0 = centralNum11_00 q + 8*(Real.exp (-(3*((17:ℝ)/4)))*Real.exp (-3*t))*centralNum12_00 q + 18*Real.exp (-8*q)*centralNum13_00 q + 72*Real.exp (-11*q)*centralNum23_00 q + 8*q^7*(2*q-3)^2*((55310771321:ℝ)/5000000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0)) := by
    rw [pieceW_00, pieceX_15, sym4_00, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((32038630423409959813466485657404556405897739896311447025216461373:ℝ)/6078252145459582155972807207509773588964163824783905220537241600000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((59499107585:ℝ)/8192) + ((33527083341:ℝ)/2048)*t) + (8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((-20018372162305:ℝ)/32768) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((-12483298972437:ℝ)/8192) - 3*((-20018372162305:ℝ)/32768))*t) + (((49650979433:ℝ)/8192) + ((29471971749:ℝ)/2048)*t)*((55310771321:ℝ)/5000000000000) - (((365796843547401301:ℝ)/50000000000) + t * ((82685047305684533:ℝ)/5000000000)) = (((59499107585:ℝ)/8192) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((-20018372162305:ℝ)/32768) + ((49650979433:ℝ)/8192)*((55310771321:ℝ)/5000000000000) - ((365796843547401301:ℝ)/50000000000)) + t*(((33527083341:ℝ)/2048) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((-12483298972437:ℝ)/8192) - 3*((-20018372162305:ℝ)/32768)) + ((29471971749:ℝ)/2048)*((55310771321:ℝ)/5000000000000) - ((82685047305684533:ℝ)/5000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece15_e01 {q : ℝ} (h0 : ((21:ℝ)/5) ≤ q) (h1 : q ≤ ((43:ℝ)/10)) :
    |pieceW q pieceX_15 0 1 - (((-125453697356078433:ℝ)/100000000000) + (q - ((17:ℝ)/4)) * ((-24841793999561663:ℝ)/12500000000))| ≤ ((644639573445928807:ℝ)/100000000000000) := by
  set t := q - ((17:ℝ)/4) with htd
  have hq : q = ((17:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece15_L3 piece15_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((17:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_01 q = ∑ e ∈ Finset.range 8, ([((-1231016019:ℝ)/1024), ((-506888949:ℝ)/256), ((-89450991:ℝ)/64), ((-8769705:ℝ)/16), ((-515865:ℝ)/4), (-18207:ℝ), (-1428:ℝ), (-48:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_01; ring
  have h12 : centralNum12_01 q = ∑ e ∈ Finset.range 12, ([((-540402491164791:ℝ)/262144), ((-197858235812883:ℝ)/32768), ((-131296586287329:ℝ)/16384), ((-13033869571479:ℝ)/2048), ((-1721081652315:ℝ)/512), ((-79371031383:ℝ)/64), ((-10437162393:ℝ)/32), ((-244615863:ℝ)/4), ((-32045859:ℝ)/4), (-698430:ℝ), (-36468:ℝ), (-864:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_01; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-1231016019:ℝ)/1024), ((-506888949:ℝ)/256), ((-89450991:ℝ)/64), ((-8769705:ℝ)/16), ((-515865:ℝ)/4), (-18207:ℝ), (-1428:ℝ), (-48:ℝ)] : List ℝ).getD e 0) 6 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-540402491164791:ℝ)/262144), ((-197858235812883:ℝ)/32768), ((-131296586287329:ℝ)/16384), ((-13033869571479:ℝ)/2048), ((-1721081652315:ℝ)/512), ((-79371031383:ℝ)/64), ((-10437162393:ℝ)/32), ((-244615863:ℝ)/4), ((-32045859:ℝ)/4), (-698430:ℝ), (-36468:ℝ), (-864:ℝ)] : List ℝ).getD e 0) 10 ht
  have m12 := abs_poly_le (fun e => ([((-540402491164791:ℝ)/262144), ((-197858235812883:ℝ)/32768), ((-131296586287329:ℝ)/16384), ((-13033869571479:ℝ)/2048), ((-1721081652315:ℝ)/512), ((-79371031383:ℝ)/64), ((-10437162393:ℝ)/32), ((-244615863:ℝ)/4), ((-32045859:ℝ)/4), (-698430:ℝ), (-36468:ℝ), (-864:ℝ)] : List ℝ).getD e 0) 12 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 8, ([((-1231016019:ℝ)/1024), ((-506888949:ℝ)/256), ((-89450991:ℝ)/64), ((-8769705:ℝ)/16), ((-515865:ℝ)/4), (-18207:ℝ), (-1428:ℝ), (-48:ℝ)] : List ℝ).getD e 0 * t^e) - (((-1231016019:ℝ)/1024) + ((-506888949:ℝ)/256)*t)| ≤ ((71270088147:ℝ)/20000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 12, ([((-540402491164791:ℝ)/262144), ((-197858235812883:ℝ)/32768), ((-131296586287329:ℝ)/16384), ((-13033869571479:ℝ)/2048), ((-1721081652315:ℝ)/512), ((-79371031383:ℝ)/64), ((-10437162393:ℝ)/32), ((-244615863:ℝ)/4), ((-32045859:ℝ)/4), (-698430:ℝ), (-36468:ℝ), (-864:ℝ)] : List ℝ).getD e 0 * t^e) - ((-540402491164791:ℝ)/262144) - ((-197858235812883:ℝ)/32768)*t| ≤ ((266895301240620930639:ℝ)/12800000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 12, ([((-540402491164791:ℝ)/262144), ((-197858235812883:ℝ)/32768), ((-131296586287329:ℝ)/16384), ((-13033869571479:ℝ)/2048), ((-1721081652315:ℝ)/512), ((-79371031383:ℝ)/64), ((-10437162393:ℝ)/32), ((-244615863:ℝ)/4), ((-32045859:ℝ)/4), (-698430:ℝ), (-36468:ℝ), (-864:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((7450721278898145159:ℝ)/3125000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((49650979433:ℝ)/8192) - ((29471971749:ℝ)/2048)*t| ≤ ((311553438853703:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((43:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-6288:ℝ), (81024:ℝ), (-238720:ℝ), (246784:ℝ), (-98304:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m13' : |centralNum13_01 q| ≤ ((615816327354334162973:ℝ)/390625000) := by
    rw [centralNum13_01_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((43:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-7368:ℝ), (59208:ℝ), (-155734:ℝ), (205300:ℝ), (-60000:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m23' : |centralNum23_01 q| ≤ ((271662839743714300403:ℝ)/250000000) := by
    rw [centralNum23_01_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((172275955240474463017463468103:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece15_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece15_E11 h0) m23'
  have c5 := scaled_affine (X := ((-92982048037:ℝ)/125000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-1231016019:ℝ)/1024) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((-540402491164791:ℝ)/262144) + ((49650979433:ℝ)/8192)*((-92982048037:ℝ)/125000000000000) - ((-125453697356078433:ℝ)/100000000000)) (β := ((-506888949:ℝ)/256) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((-197858235812883:ℝ)/32768) - 3*((-540402491164791:ℝ)/262144)) + ((29471971749:ℝ)/2048)*((-92982048037:ℝ)/125000000000000) - ((-24841793999561663:ℝ)/12500000000)) ht
  have hW : pieceW q pieceX_15 0 1 = centralNum11_01 q + 8*(Real.exp (-(3*((17:ℝ)/4)))*Real.exp (-3*t))*centralNum12_01 q + 18*Real.exp (-8*q)*centralNum13_01 q + 72*Real.exp (-11*q)*centralNum23_01 q + 8*q^7*(2*q-3)^2*((-92982048037:ℝ)/125000000000000) + (0:ℝ) := by
    rw [pieceW_01, pieceX_15, sym4_01, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((43764023386415711490458361828835393291538081070561361729998399953:ℝ)/12663025303040796158276681682312028310342007968299802542785920000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-1231016019:ℝ)/1024) + ((-506888949:ℝ)/256)*t) + (8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((-540402491164791:ℝ)/262144) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((-197858235812883:ℝ)/32768) - 3*((-540402491164791:ℝ)/262144))*t) + (((49650979433:ℝ)/8192) + ((29471971749:ℝ)/2048)*t)*((-92982048037:ℝ)/125000000000000) - (((-125453697356078433:ℝ)/100000000000) + t * ((-24841793999561663:ℝ)/12500000000)) = (((-1231016019:ℝ)/1024) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((-540402491164791:ℝ)/262144) + ((49650979433:ℝ)/8192)*((-92982048037:ℝ)/125000000000000) - ((-125453697356078433:ℝ)/100000000000)) + t*(((-506888949:ℝ)/256) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((-197858235812883:ℝ)/32768) - 3*((-540402491164791:ℝ)/262144)) + ((29471971749:ℝ)/2048)*((-92982048037:ℝ)/125000000000000) - ((-24841793999561663:ℝ)/12500000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece15_e02 {q : ℝ} (h0 : ((21:ℝ)/5) ≤ q) (h1 : q ≤ ((43:ℝ)/10)) :
    |pieceW q pieceX_15 0 2 - (((-210250518139271027:ℝ)/250000000000000) + (q - ((17:ℝ)/4)) * ((-24023002815871681:ℝ)/625000000000))| ≤ ((219656311303091647:ℝ)/100000000000000) := by
  set t := q - ((17:ℝ)/4) with htd
  have hq : q = ((17:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece15_L3 piece15_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((17:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_02 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_02; ring
  have h12 : centralNum12_02 q = ∑ e ∈ Finset.range 13, ([((-5210015556037491:ℝ)/8388608), ((-10291425927204861:ℝ)/2097152), ((-5801641036931259:ℝ)/524288), ((-1697936502510495:ℝ)/131072), ((-77623019332155:ℝ)/8192), ((-19277910856233:ℝ)/4096), ((-1693029831003:ℝ)/1024), ((-106895766807:ℝ)/256), ((-9684433035:ℝ)/128), ((-308043585:ℝ)/32), ((-6546879:ℝ)/8), ((-83619:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_02; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-5210015556037491:ℝ)/8388608), ((-10291425927204861:ℝ)/2097152), ((-5801641036931259:ℝ)/524288), ((-1697936502510495:ℝ)/131072), ((-77623019332155:ℝ)/8192), ((-19277910856233:ℝ)/4096), ((-1693029831003:ℝ)/1024), ((-106895766807:ℝ)/256), ((-9684433035:ℝ)/128), ((-308043585:ℝ)/32), ((-6546879:ℝ)/8), ((-83619:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((-5210015556037491:ℝ)/8388608), ((-10291425927204861:ℝ)/2097152), ((-5801641036931259:ℝ)/524288), ((-1697936502510495:ℝ)/131072), ((-77623019332155:ℝ)/8192), ((-19277910856233:ℝ)/4096), ((-1693029831003:ℝ)/1024), ((-106895766807:ℝ)/256), ((-9684433035:ℝ)/128), ((-308043585:ℝ)/32), ((-6546879:ℝ)/8), ((-83619:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((-5210015556037491:ℝ)/8388608), ((-10291425927204861:ℝ)/2097152), ((-5801641036931259:ℝ)/524288), ((-1697936502510495:ℝ)/131072), ((-77623019332155:ℝ)/8192), ((-19277910856233:ℝ)/4096), ((-1693029831003:ℝ)/1024), ((-106895766807:ℝ)/256), ((-9684433035:ℝ)/128), ((-308043585:ℝ)/32), ((-6546879:ℝ)/8), ((-83619:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0 * t^e) - ((-5210015556037491:ℝ)/8388608) - ((-10291425927204861:ℝ)/2097152)*t| ≤ ((15024321176349404221389:ℝ)/512000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((-5210015556037491:ℝ)/8388608), ((-10291425927204861:ℝ)/2097152), ((-5801641036931259:ℝ)/524288), ((-1697936502510495:ℝ)/131072), ((-77623019332155:ℝ)/8192), ((-19277910856233:ℝ)/4096), ((-1693029831003:ℝ)/1024), ((-106895766807:ℝ)/256), ((-9684433035:ℝ)/128), ((-308043585:ℝ)/32), ((-6546879:ℝ)/8), ((-83619:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((223948336232655401193:ℝ)/250000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((49650979433:ℝ)/8192) - ((29471971749:ℝ)/2048)*t| ≤ ((311553438853703:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((43:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82080:ℝ), (-967680:ℝ), (3257600:ℝ), (-4474880:ℝ), (2908160:ℝ), (-786432:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_02 q| ≤ ((68236661459587666158393:ℝ)/976562500) := by
    rw [centralNum13_02_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((43:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (87660:ℝ), (-702180:ℝ), ((7421435:ℝ)/4), ((-10854125:ℝ)/4), ((2828125:ℝ)/2), (-187500:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_02 q| ≤ ((22011610310148400333611:ℝ)/800000000) := by
    rw [centralNum23_02_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((172275955240474463017463468103:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece15_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece15_E11 h0) m23'
  have c5 := scaled_affine (X := ((224052875687:ℝ)/100000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((-5210015556037491:ℝ)/8388608) + ((49650979433:ℝ)/8192)*((224052875687:ℝ)/100000000000000) - ((-210250518139271027:ℝ)/250000000000000)) (β := (0:ℝ) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((-10291425927204861:ℝ)/2097152) - 3*((-5210015556037491:ℝ)/8388608)) + ((29471971749:ℝ)/2048)*((224052875687:ℝ)/100000000000000) - ((-24023002815871681:ℝ)/625000000000)) ht
  have hW : pieceW q pieceX_15 0 2 = centralNum11_02 q + 8*(Real.exp (-(3*((17:ℝ)/4)))*Real.exp (-3*t))*centralNum12_02 q + 18*Real.exp (-8*q)*centralNum13_02 q + 72*Real.exp (-11*q)*centralNum23_02 q + 8*q^7*(2*q-3)^2*((224052875687:ℝ)/100000000000000) + (0:ℝ) := by
    rw [pieceW_02, pieceX_15, sym4_02, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((99244053705953175029595852279322269730739945525228451680477151:ℝ)/40521680969730547706485381383398490593094425498559368136914944000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((-5210015556037491:ℝ)/8388608) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((-10291425927204861:ℝ)/2097152) - 3*((-5210015556037491:ℝ)/8388608))*t) + (((49650979433:ℝ)/8192) + ((29471971749:ℝ)/2048)*t)*((224052875687:ℝ)/100000000000000) - (((-210250518139271027:ℝ)/250000000000000) + t * ((-24023002815871681:ℝ)/625000000000)) = ((0:ℝ) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((-5210015556037491:ℝ)/8388608) + ((49650979433:ℝ)/8192)*((224052875687:ℝ)/100000000000000) - ((-210250518139271027:ℝ)/250000000000000)) + t*((0:ℝ) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((-10291425927204861:ℝ)/2097152) - 3*((-5210015556037491:ℝ)/8388608)) + ((29471971749:ℝ)/2048)*((224052875687:ℝ)/100000000000000) - ((-24023002815871681:ℝ)/625000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece15_e03 {q : ℝ} (h0 : ((21:ℝ)/5) ≤ q) (h1 : q ≤ ((43:ℝ)/10)) :
    |pieceW q pieceX_15 0 3 - (((143243281901315867:ℝ)/5000000000000) + (q - ((17:ℝ)/4)) * ((-248829675392603407:ℝ)/1000000000000))| ≤ ((20048663721643673:ℝ)/2500000000000) := by
  set t := q - ((17:ℝ)/4) with htd
  have hq : q = ((17:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece15_L3 piece15_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((17:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_03 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_03; ring
  have h12 : centralNum12_03 q = ∑ e ∈ Finset.range 14, ([((2565922023523536129:ℝ)/469762048), ((461220806156831145:ℝ)/29360128), ((19473432986649519:ℝ)/1048576), ((39040047003723417:ℝ)/3670016), ((2706760790192925:ℝ)/1835008), ((-73069544125269:ℝ)/32768), ((-13698608643225:ℝ)/7168), ((-5913387477027:ℝ)/7168), ((-1656585310581:ℝ)/7168), ((-1421947575:ℝ)/32), ((-656970021:ℝ)/112), ((-28612035:ℝ)/56), ((-106191:ℝ)/4), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_03; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((2565922023523536129:ℝ)/469762048), ((461220806156831145:ℝ)/29360128), ((19473432986649519:ℝ)/1048576), ((39040047003723417:ℝ)/3670016), ((2706760790192925:ℝ)/1835008), ((-73069544125269:ℝ)/32768), ((-13698608643225:ℝ)/7168), ((-5913387477027:ℝ)/7168), ((-1656585310581:ℝ)/7168), ((-1421947575:ℝ)/32), ((-656970021:ℝ)/112), ((-28612035:ℝ)/56), ((-106191:ℝ)/4), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((2565922023523536129:ℝ)/469762048), ((461220806156831145:ℝ)/29360128), ((19473432986649519:ℝ)/1048576), ((39040047003723417:ℝ)/3670016), ((2706760790192925:ℝ)/1835008), ((-73069544125269:ℝ)/32768), ((-13698608643225:ℝ)/7168), ((-5913387477027:ℝ)/7168), ((-1656585310581:ℝ)/7168), ((-1421947575:ℝ)/32), ((-656970021:ℝ)/112), ((-28612035:ℝ)/56), ((-106191:ℝ)/4), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((2565922023523536129:ℝ)/469762048), ((461220806156831145:ℝ)/29360128), ((19473432986649519:ℝ)/1048576), ((39040047003723417:ℝ)/3670016), ((2706760790192925:ℝ)/1835008), ((-73069544125269:ℝ)/32768), ((-13698608643225:ℝ)/7168), ((-5913387477027:ℝ)/7168), ((-1656585310581:ℝ)/7168), ((-1421947575:ℝ)/32), ((-656970021:ℝ)/112), ((-28612035:ℝ)/56), ((-106191:ℝ)/4), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((2565922023523536129:ℝ)/469762048) - ((461220806156831145:ℝ)/29360128)*t| ≤ ((3913148402684084484719937:ℝ)/81920000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((2565922023523536129:ℝ)/469762048), ((461220806156831145:ℝ)/29360128), ((19473432986649519:ℝ)/1048576), ((39040047003723417:ℝ)/3670016), ((2706760790192925:ℝ)/1835008), ((-73069544125269:ℝ)/32768), ((-13698608643225:ℝ)/7168), ((-5913387477027:ℝ)/7168), ((-1656585310581:ℝ)/7168), ((-1421947575:ℝ)/32), ((-656970021:ℝ)/112), ((-28612035:ℝ)/56), ((-106191:ℝ)/4), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((56406750233637860471137581:ℝ)/8960000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((49650979433:ℝ)/8192) - ((29471971749:ℝ)/2048)*t| ≤ ((311553438853703:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((43:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-812160:ℝ), (8985600:ℝ), (-32225280:ℝ), (52019200:ℝ), ((-305233920:ℝ)/7), ((135528448:ℝ)/7), ((-25165824:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_03 q| ≤ ((16460165713238625514233061:ℝ)/8544921875) := by
    rw [centralNum13_03_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((43:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-833220:ℝ), (6469740:ℝ), ((-68603955:ℝ)/4), ((104396875:ℝ)/4), ((-1001334375:ℝ)/56), ((125828125:ℝ)/28), ((-2343750:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_03 q| ≤ ((10507258602565695272042899:ℝ)/22400000000) := by
    rw [centralNum23_03_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((172275955240474463017463468103:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece15_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece15_E11 h0) m23'
  have c5 := scaled_affine (X := ((-161981029799:ℝ)/10000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((2565922023523536129:ℝ)/469762048) + ((49650979433:ℝ)/8192)*((-161981029799:ℝ)/10000000000000) - ((143243281901315867:ℝ)/5000000000000)) (β := (0:ℝ) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((461220806156831145:ℝ)/29360128) - 3*((2565922023523536129:ℝ)/469762048)) + ((29471971749:ℝ)/2048)*((-161981029799:ℝ)/10000000000000) - ((-248829675392603407:ℝ)/1000000000000)) ht
  have hW : pieceW q pieceX_15 0 3 = centralNum11_03 q + 8*(Real.exp (-(3*((17:ℝ)/4)))*Real.exp (-3*t))*centralNum12_03 q + 18*Real.exp (-8*q)*centralNum13_03 q + 72*Real.exp (-11*q)*centralNum23_03 q + 8*q^7*(2*q-3)^2*((-161981029799:ℝ)/10000000000000) + (0:ℝ) := by
    rw [pieceW_03, pieceX_15, sym4_03, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((2006299214859409902151625576183760760100942205819185191584754457:ℝ)/28365176678811383394539766968378943415166097848991557695840460800000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((2565922023523536129:ℝ)/469762048) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((461220806156831145:ℝ)/29360128) - 3*((2565922023523536129:ℝ)/469762048))*t) + (((49650979433:ℝ)/8192) + ((29471971749:ℝ)/2048)*t)*((-161981029799:ℝ)/10000000000000) - (((143243281901315867:ℝ)/5000000000000) + t * ((-248829675392603407:ℝ)/1000000000000)) = ((0:ℝ) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((2565922023523536129:ℝ)/469762048) + ((49650979433:ℝ)/8192)*((-161981029799:ℝ)/10000000000000) - ((143243281901315867:ℝ)/5000000000000)) + t*((0:ℝ) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((461220806156831145:ℝ)/29360128) - 3*((2565922023523536129:ℝ)/469762048)) + ((29471971749:ℝ)/2048)*((-161981029799:ℝ)/10000000000000) - ((-248829675392603407:ℝ)/1000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece15_e11 {q : ℝ} (h0 : ((21:ℝ)/5) ≤ q) (h1 : q ≤ ((43:ℝ)/10)) :
    |pieceW q pieceX_15 1 1 - (((560117188173585927:ℝ)/100000000000) + (q - ((17:ℝ)/4)) * ((1477871724186003:ℝ)/125000000))| ≤ ((307677860950553273:ℝ)/10000000000000) := by
  set t := q - ((17:ℝ)/4) with htd
  have hq : q = ((17:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece15_L3 piece15_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((17:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_11 q = ∑ e ∈ Finset.range 10, ([((33478808203:ℝ)/6144), ((11908340659:ℝ)/1024), ((717695953:ℝ)/64), ((102588353:ℝ)/16), (2393209:ℝ), ((1207493:ℝ)/2), (102732:ℝ), (11344:ℝ), (736:ℝ), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_11; ring
  have h12 : centralNum12_11 q = ∑ e ∈ Finset.range 13, ([((8446849897073437:ℝ)/6291456), ((484706523089:ℝ)/524288), ((-764991816712873:ℝ)/131072), ((-328139923099829:ℝ)/32768), ((-17840329997185:ℝ)/2048), ((-4911471403571:ℝ)/1024), ((-462695552361:ℝ)/256), ((-30772785149:ℝ)/64), ((-2903810857:ℝ)/32), ((-286449745:ℝ)/24), ((-2086677:ℝ)/2), (-54594:ℝ), (-1296:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_11; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((33478808203:ℝ)/6144), ((11908340659:ℝ)/1024), ((717695953:ℝ)/64), ((102588353:ℝ)/16), (2393209:ℝ), ((1207493:ℝ)/2), (102732:ℝ), (11344:ℝ), (736:ℝ), ((64:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((8446849897073437:ℝ)/6291456), ((484706523089:ℝ)/524288), ((-764991816712873:ℝ)/131072), ((-328139923099829:ℝ)/32768), ((-17840329997185:ℝ)/2048), ((-4911471403571:ℝ)/1024), ((-462695552361:ℝ)/256), ((-30772785149:ℝ)/64), ((-2903810857:ℝ)/32), ((-286449745:ℝ)/24), ((-2086677:ℝ)/2), (-54594:ℝ), (-1296:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((8446849897073437:ℝ)/6291456), ((484706523089:ℝ)/524288), ((-764991816712873:ℝ)/131072), ((-328139923099829:ℝ)/32768), ((-17840329997185:ℝ)/2048), ((-4911471403571:ℝ)/1024), ((-462695552361:ℝ)/256), ((-30772785149:ℝ)/64), ((-2903810857:ℝ)/32), ((-286449745:ℝ)/24), ((-2086677:ℝ)/2), (-54594:ℝ), (-1296:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((33478808203:ℝ)/6144), ((11908340659:ℝ)/1024), ((717695953:ℝ)/64), ((102588353:ℝ)/16), (2393209:ℝ), ((1207493:ℝ)/2), (102732:ℝ), (11344:ℝ), (736:ℝ), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((33478808203:ℝ)/6144) + ((11908340659:ℝ)/1024)*t)| ≤ ((692438820311641:ℝ)/24000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((8446849897073437:ℝ)/6291456), ((484706523089:ℝ)/524288), ((-764991816712873:ℝ)/131072), ((-328139923099829:ℝ)/32768), ((-17840329997185:ℝ)/2048), ((-4911471403571:ℝ)/1024), ((-462695552361:ℝ)/256), ((-30772785149:ℝ)/64), ((-2903810857:ℝ)/32), ((-286449745:ℝ)/24), ((-2086677:ℝ)/2), (-54594:ℝ), (-1296:ℝ)] : List ℝ).getD e 0 * t^e) - ((8446849897073437:ℝ)/6291456) - ((484706523089:ℝ)/524288)*t| ≤ ((6105134312858401046429:ℝ)/384000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((8446849897073437:ℝ)/6291456), ((484706523089:ℝ)/524288), ((-764991816712873:ℝ)/131072), ((-328139923099829:ℝ)/32768), ((-17840329997185:ℝ)/2048), ((-4911471403571:ℝ)/1024), ((-462695552361:ℝ)/256), ((-30772785149:ℝ)/64), ((-2903810857:ℝ)/32), ((-286449745:ℝ)/24), ((-2086677:ℝ)/2), (-54594:ℝ), (-1296:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((86946281347342554145759:ℝ)/64000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((49650979433:ℝ)/8192) - ((29471971749:ℝ)/2048)*t| ≤ ((311553438853703:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((43:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-3444:ℝ), (162624:ℝ), (-1531216:ℝ), (4800960:ℝ), (-6350848:ℝ), ((12025856:ℝ)/3), (-1048576:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_11 q| ≤ ((279709033789560898211477:ℝ)/2929687500) := by
    rw [centralNum13_11_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((43:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-4074:ℝ), (159906:ℝ), (-1104799:ℝ), (2801499:ℝ), (-3931375:ℝ), ((5896250:ℝ)/3), (-250000:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_11 q| ≤ ((114876605941682908545491:ℝ)/3000000000) := by
    rw [centralNum23_11_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((172275955240474463017463468103:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece15_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece15_E11 h0) m23'
  have c5 := scaled_affine (X := ((24949647159:ℝ)/1250000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1))| ≤ ((5454085624821724958341120000000:ℝ)/7544606755357882488663871583288409) := by
    rw [abs_neg, tailWeight_1, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((43:ℝ)/10)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((43:ℝ)/10)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece15_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((4814744136400:ℝ)/531441)) ≤ ((43:ℝ)/10)^6*(8000*(2*((43:ℝ)/10)-3)^2*(1/((99375560574937156562341070943:ℝ)/5000000000))*((4814744136400:ℝ)/531441)) := by
          gcongr
      _ ≤ ((5454085624821724958341120000000:ℝ)/7544606755357882488663871583288409) := by norm_num
  have c7 := affine_round (α := ((33478808203:ℝ)/6144) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((8446849897073437:ℝ)/6291456) + ((49650979433:ℝ)/8192)*((24949647159:ℝ)/1250000000000) - ((560117188173585927:ℝ)/100000000000)) (β := ((11908340659:ℝ)/1024) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((484706523089:ℝ)/524288) - 3*((8446849897073437:ℝ)/6291456)) + ((29471971749:ℝ)/2048)*((24949647159:ℝ)/1250000000000) - ((1477871724186003:ℝ)/125000000)) ht
  have hW : pieceW q pieceX_15 1 1 = centralNum11_11 q + 8*(Real.exp (-(3*((17:ℝ)/4)))*Real.exp (-3*t))*centralNum12_11 q + 18*Real.exp (-8*q)*centralNum13_11 q + 72*Real.exp (-11*q)*centralNum23_11 q + 8*q^7*(2*q-3)^2*((24949647159:ℝ)/1250000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1)) := by
    rw [pieceW_11, pieceX_15, sym4_11, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((11155617043197433949485271764022157752641552992271472923224919399:ℝ)/4558689109094686616979605405632330191723122868587928915402931200000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((33478808203:ℝ)/6144) + ((11908340659:ℝ)/1024)*t) + (8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((8446849897073437:ℝ)/6291456) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((484706523089:ℝ)/524288) - 3*((8446849897073437:ℝ)/6291456))*t) + (((49650979433:ℝ)/8192) + ((29471971749:ℝ)/2048)*t)*((24949647159:ℝ)/1250000000000) - (((560117188173585927:ℝ)/100000000000) + t * ((1477871724186003:ℝ)/125000000)) = (((33478808203:ℝ)/6144) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((8446849897073437:ℝ)/6291456) + ((49650979433:ℝ)/8192)*((24949647159:ℝ)/1250000000000) - ((560117188173585927:ℝ)/100000000000)) + t*(((11908340659:ℝ)/1024) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((484706523089:ℝ)/524288) - 3*((8446849897073437:ℝ)/6291456)) + ((29471971749:ℝ)/2048)*((24949647159:ℝ)/1250000000000) - ((1477871724186003:ℝ)/125000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece15_e12 {q : ℝ} (h0 : ((21:ℝ)/5) ≤ q) (h1 : q ≤ ((43:ℝ)/10)) :
    |pieceW q pieceX_15 1 2 - (((-296657392725368321:ℝ)/500000000000) + (q - ((17:ℝ)/4)) * ((-64403031746487319:ℝ)/50000000000))| ≤ ((105919561666455747:ℝ)/5000000000000) := by
  set t := q - ((17:ℝ)/4) with htd
  have hq : q = ((17:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece15_L3 piece15_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((17:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_12 q = ∑ e ∈ Finset.range 9, ([((-17258361835:ℝ)/24576), ((-1583140555:ℝ)/1536), ((-215066575:ℝ)/384), ((-10047085:ℝ)/96), ((1090975:ℝ)/48), ((93755:ℝ)/6), ((9970:ℝ)/3), ((1000:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_12; ring
  have h12 : centralNum12_12 q = ∑ e ∈ Finset.range 14, ([((2359806996380171329:ℝ)/201326592), ((513008684664271993:ℝ)/12582912), ((187224993885505177:ℝ)/3145728), ((75017793742385657:ℝ)/1572864), ((17288717448133405:ℝ)/786432), ((458267162747117:ℝ)/98304), ((-2488594514033:ℝ)/3072), ((-2961208529603:ℝ)/3072), ((-1102219980341:ℝ)/3072), ((-2559583315:ℝ)/32), ((-185820807:ℝ)/16), ((-8667297:ℝ)/8), ((-237411:ℝ)/4), (-1458:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_12; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-17258361835:ℝ)/24576), ((-1583140555:ℝ)/1536), ((-215066575:ℝ)/384), ((-10047085:ℝ)/96), ((1090975:ℝ)/48), ((93755:ℝ)/6), ((9970:ℝ)/3), ((1000:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((2359806996380171329:ℝ)/201326592), ((513008684664271993:ℝ)/12582912), ((187224993885505177:ℝ)/3145728), ((75017793742385657:ℝ)/1572864), ((17288717448133405:ℝ)/786432), ((458267162747117:ℝ)/98304), ((-2488594514033:ℝ)/3072), ((-2961208529603:ℝ)/3072), ((-1102219980341:ℝ)/3072), ((-2559583315:ℝ)/32), ((-185820807:ℝ)/16), ((-8667297:ℝ)/8), ((-237411:ℝ)/4), (-1458:ℝ)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((2359806996380171329:ℝ)/201326592), ((513008684664271993:ℝ)/12582912), ((187224993885505177:ℝ)/3145728), ((75017793742385657:ℝ)/1572864), ((17288717448133405:ℝ)/786432), ((458267162747117:ℝ)/98304), ((-2488594514033:ℝ)/3072), ((-2961208529603:ℝ)/3072), ((-1102219980341:ℝ)/3072), ((-2559583315:ℝ)/32), ((-185820807:ℝ)/16), ((-8667297:ℝ)/8), ((-237411:ℝ)/4), (-1458:ℝ)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((-17258361835:ℝ)/24576), ((-1583140555:ℝ)/1536), ((-215066575:ℝ)/384), ((-10047085:ℝ)/96), ((1090975:ℝ)/48), ((93755:ℝ)/6), ((9970:ℝ)/3), ((1000:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((-17258361835:ℝ)/24576) + ((-1583140555:ℝ)/1536)*t)| ≤ ((2713732119451:ℝ)/1920000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((2359806996380171329:ℝ)/201326592), ((513008684664271993:ℝ)/12582912), ((187224993885505177:ℝ)/3145728), ((75017793742385657:ℝ)/1572864), ((17288717448133405:ℝ)/786432), ((458267162747117:ℝ)/98304), ((-2488594514033:ℝ)/3072), ((-2961208529603:ℝ)/3072), ((-1102219980341:ℝ)/3072), ((-2559583315:ℝ)/32), ((-185820807:ℝ)/16), ((-8667297:ℝ)/8), ((-237411:ℝ)/4), (-1458:ℝ)] : List ℝ).getD e 0 * t^e) - ((2359806996380171329:ℝ)/201326592) - ((513008684664271993:ℝ)/12582912)*t| ≤ ((38066701249082268352489339:ℝ)/245760000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((2359806996380171329:ℝ)/201326592), ((513008684664271993:ℝ)/12582912), ((187224993885505177:ℝ)/3145728), ((75017793742385657:ℝ)/1572864), ((17288717448133405:ℝ)/786432), ((458267162747117:ℝ)/98304), ((-2488594514033:ℝ)/3072), ((-2961208529603:ℝ)/3072), ((-1102219980341:ℝ)/3072), ((-2559583315:ℝ)/32), ((-185820807:ℝ)/16), ((-8667297:ℝ)/8), ((-237411:ℝ)/4), (-1458:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((854918879936168553965563741:ℝ)/61440000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((49650979433:ℝ)/8192) - ((29471971749:ℝ)/2048)*t| ≤ ((311553438853703:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((43:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (122790:ℝ), (-3586680:ℝ), (28529720:ℝ), (-90761600:ℝ), (137804800:ℝ), ((-332136448:ℝ)/3), ((141819904:ℝ)/3), (-8388608:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_12 q| ≤ ((137874455489921796323056703:ℝ)/29296875000) := by
    rw [centralNum13_12_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((43:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (132555:ℝ), (-3252375:ℝ), ((39743695:ℝ)/2), ((-197111615:ℝ)/4), ((281947375:ℝ)/4), ((-1100234375:ℝ)/24), ((131828125:ℝ)/12), (-781250:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_12 q| ≤ ((11316011198823168367786483:ℝ)/9600000000) := by
    rw [centralNum23_12_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((172275955240474463017463468103:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece15_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece15_E11 h0) m23'
  have c5 := scaled_affine (X := ((-269302576627:ℝ)/10000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-17258361835:ℝ)/24576) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((2359806996380171329:ℝ)/201326592) + ((49650979433:ℝ)/8192)*((-269302576627:ℝ)/10000000000000) - ((-296657392725368321:ℝ)/500000000000)) (β := ((-1583140555:ℝ)/1536) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((513008684664271993:ℝ)/12582912) - 3*((2359806996380171329:ℝ)/201326592)) + ((29471971749:ℝ)/2048)*((-269302576627:ℝ)/10000000000000) - ((-64403031746487319:ℝ)/50000000000)) ht
  have hW : pieceW q pieceX_15 1 2 = centralNum11_12 q + 8*(Real.exp (-(3*((17:ℝ)/4)))*Real.exp (-3*t))*centralNum12_12 q + 18*Real.exp (-8*q)*centralNum13_12 q + 72*Real.exp (-11*q)*centralNum23_12 q + 8*q^7*(2*q-3)^2*((-269302576627:ℝ)/10000000000000) + (0:ℝ) := by
    rw [pieceW_12, pieceX_15, sym4_12, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((3286301680556609377920430634239159317147795624890954334283423649:ℝ)/12156504290919164311945614415019547177928327649567810441074483200000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-17258361835:ℝ)/24576) + ((-1583140555:ℝ)/1536)*t) + (8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((2359806996380171329:ℝ)/201326592) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((513008684664271993:ℝ)/12582912) - 3*((2359806996380171329:ℝ)/201326592))*t) + (((49650979433:ℝ)/8192) + ((29471971749:ℝ)/2048)*t)*((-269302576627:ℝ)/10000000000000) - (((-296657392725368321:ℝ)/500000000000) + t * ((-64403031746487319:ℝ)/50000000000)) = (((-17258361835:ℝ)/24576) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((2359806996380171329:ℝ)/201326592) + ((49650979433:ℝ)/8192)*((-269302576627:ℝ)/10000000000000) - ((-296657392725368321:ℝ)/500000000000)) + t*(((-1583140555:ℝ)/1536) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((513008684664271993:ℝ)/12582912) - 3*((2359806996380171329:ℝ)/201326592)) + ((29471971749:ℝ)/2048)*((-269302576627:ℝ)/10000000000000) - ((-64403031746487319:ℝ)/50000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece15_e13 {q : ℝ} (h0 : ((21:ℝ)/5) ≤ q) (h1 : q ≤ ((43:ℝ)/10)) :
    |pieceW q pieceX_15 1 3 - (((16471448384060823:ℝ)/50000000000) + (q - ((17:ℝ)/4)) * ((13760979503664453:ℝ)/5000000000))| ≤ ((368981067969698989:ℝ)/10000000000000) := by
  set t := q - ((17:ℝ)/4) with htd
  have hq : q = ((17:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece15_L3 piece15_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((17:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_13 q = ∑ e ∈ Finset.range 7, ([((-362063535:ℝ)/1024), ((-63893565:ℝ)/128), ((-18792225:ℝ)/64), ((-368475:ℝ)/4), ((-65025:ℝ)/4), (-1530:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_13; ring
  have h12 : centralNum12_13 q = ∑ e ∈ Finset.range 15, ([((-80787448166283125241:ℝ)/3758096384), ((-42600723298863954753:ℝ)/939524096), ((-678738134082009273:ℝ)/29360128), ((733138624640413581:ℝ)/29360128), ((666489414487958097:ℝ)/14680064), ((120137564528474109:ℝ)/3670016), ((6335713206162591:ℝ)/458752), ((201837358706919:ℝ)/57344), ((24618567787017:ℝ)/57344), ((-542525640183:ℝ)/14336), ((-23878844901:ℝ)/896), ((-2393023851:ℝ)/448), ((-131459841:ℝ)/224), ((-1992357:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_13; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-362063535:ℝ)/1024), ((-63893565:ℝ)/128), ((-18792225:ℝ)/64), ((-368475:ℝ)/4), ((-65025:ℝ)/4), (-1530:ℝ), (-60:ℝ)] : List ℝ).getD e 0) 5 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-80787448166283125241:ℝ)/3758096384), ((-42600723298863954753:ℝ)/939524096), ((-678738134082009273:ℝ)/29360128), ((733138624640413581:ℝ)/29360128), ((666489414487958097:ℝ)/14680064), ((120137564528474109:ℝ)/3670016), ((6335713206162591:ℝ)/458752), ((201837358706919:ℝ)/57344), ((24618567787017:ℝ)/57344), ((-542525640183:ℝ)/14336), ((-23878844901:ℝ)/896), ((-2393023851:ℝ)/448), ((-131459841:ℝ)/224), ((-1992357:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-80787448166283125241:ℝ)/3758096384), ((-42600723298863954753:ℝ)/939524096), ((-678738134082009273:ℝ)/29360128), ((733138624640413581:ℝ)/29360128), ((666489414487958097:ℝ)/14680064), ((120137564528474109:ℝ)/3670016), ((6335713206162591:ℝ)/458752), ((201837358706919:ℝ)/57344), ((24618567787017:ℝ)/57344), ((-542525640183:ℝ)/14336), ((-23878844901:ℝ)/896), ((-2393023851:ℝ)/448), ((-131459841:ℝ)/224), ((-1992357:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 7, ([((-362063535:ℝ)/1024), ((-63893565:ℝ)/128), ((-18792225:ℝ)/64), ((-368475:ℝ)/4), ((-65025:ℝ)/4), (-1530:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e) - (((-362063535:ℝ)/1024) + ((-63893565:ℝ)/128)*t)| ≤ ((2386202283:ℝ)/3200000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-80787448166283125241:ℝ)/3758096384), ((-42600723298863954753:ℝ)/939524096), ((-678738134082009273:ℝ)/29360128), ((733138624640413581:ℝ)/29360128), ((666489414487958097:ℝ)/14680064), ((120137564528474109:ℝ)/3670016), ((6335713206162591:ℝ)/458752), ((201837358706919:ℝ)/57344), ((24618567787017:ℝ)/57344), ((-542525640183:ℝ)/14336), ((-23878844901:ℝ)/896), ((-2393023851:ℝ)/448), ((-131459841:ℝ)/224), ((-1992357:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((-80787448166283125241:ℝ)/3758096384) - ((-42600723298863954753:ℝ)/939524096)*t| ≤ ((175500541193385139410202179:ℝ)/2867200000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-80787448166283125241:ℝ)/3758096384), ((-42600723298863954753:ℝ)/939524096), ((-678738134082009273:ℝ)/29360128), ((733138624640413581:ℝ)/29360128), ((666489414487958097:ℝ)/14680064), ((120137564528474109:ℝ)/3670016), ((6335713206162591:ℝ)/458752), ((201837358706919:ℝ)/57344), ((24618567787017:ℝ)/57344), ((-542525640183:ℝ)/14336), ((-23878844901:ℝ)/896), ((-2393023851:ℝ)/448), ((-131459841:ℝ)/224), ((-1992357:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((273247146287258636357201355591:ℝ)/11468800000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((49650979433:ℝ)/8192) - ((29471971749:ℝ)/2048)*t| ≤ ((311553438853703:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((43:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2325540:ℝ), (52589280:ℝ), (-375655200:ℝ), (1192958720:ℝ), (-1965096960:ℝ), ((12857851904:ℝ)/7), ((-21171273728:ℝ)/21), ((914358272:ℝ)/3), ((-268435456:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_13 q| ≤ ((293160673775072631875798393323:ℝ)/2050781250000) := by
    rw [centralNum13_13_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((43:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2399070:ℝ), (45666930:ℝ), (-251781675:ℝ), ((2452738385:ℝ)/4), ((-14104310625:ℝ)/16), ((74345740625:ℝ)/112), ((-74899765625:ℝ)/336), ((5161328125:ℝ)/168), ((-9765625:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_13 q| ≤ ((6351721241587263884828123171:ℝ)/268800000000) := by
    rw [centralNum23_13_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((172275955240474463017463468103:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece15_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece15_E11 h0) m23'
  have c5 := scaled_affine (X := ((195042349853:ℝ)/1000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-362063535:ℝ)/1024) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((-80787448166283125241:ℝ)/3758096384) + ((49650979433:ℝ)/8192)*((195042349853:ℝ)/1000000000000) - ((16471448384060823:ℝ)/50000000000)) (β := ((-63893565:ℝ)/128) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((-42600723298863954753:ℝ)/939524096) - 3*((-80787448166283125241:ℝ)/3758096384)) + ((29471971749:ℝ)/2048)*((195042349853:ℝ)/1000000000000) - ((13760979503664453:ℝ)/5000000000)) ht
  have hW : pieceW q pieceX_15 1 3 = centralNum11_13 q + 8*(Real.exp (-(3*((17:ℝ)/4)))*Real.exp (-3*t))*centralNum12_13 q + 18*Real.exp (-8*q)*centralNum13_13 q + 72*Real.exp (-11*q)*centralNum23_13 q + 8*q^7*(2*q-3)^2*((195042349853:ℝ)/1000000000000) + (0:ℝ) := by
    rw [pieceW_13, pieceX_15, sym4_13, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((491932576458113707577524438841588345992706968633844979345067741:ℝ)/2836517667881138339453976696837894341516609784899155769584046080000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-362063535:ℝ)/1024) + ((-63893565:ℝ)/128)*t) + (8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((-80787448166283125241:ℝ)/3758096384) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((-42600723298863954753:ℝ)/939524096) - 3*((-80787448166283125241:ℝ)/3758096384))*t) + (((49650979433:ℝ)/8192) + ((29471971749:ℝ)/2048)*t)*((195042349853:ℝ)/1000000000000) - (((16471448384060823:ℝ)/50000000000) + t * ((13760979503664453:ℝ)/5000000000)) = (((-362063535:ℝ)/1024) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((-80787448166283125241:ℝ)/3758096384) + ((49650979433:ℝ)/8192)*((195042349853:ℝ)/1000000000000) - ((16471448384060823:ℝ)/50000000000)) + t*(((-63893565:ℝ)/128) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((-42600723298863954753:ℝ)/939524096) - 3*((-80787448166283125241:ℝ)/3758096384)) + ((29471971749:ℝ)/2048)*((195042349853:ℝ)/1000000000000) - ((13760979503664453:ℝ)/5000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece15_e22 {q : ℝ} (h0 : ((21:ℝ)/5) ≤ q) (h1 : q ≤ ((43:ℝ)/10)) :
    |pieceW q pieceX_15 2 2 - (((418170823237198201:ℝ)/100000000000) + (q - ((17:ℝ)/4)) * ((125697412065724601:ℝ)/10000000000))| ≤ ((12013702830690817:ℝ)/125000000000) := by
  set t := q - ((17:ℝ)/4) with htd
  have hq : q = ((17:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece15_L3 piece15_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((17:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_22 q = ∑ e ∈ Finset.range 10, ([((231003634615:ℝ)/49152), ((130714123445:ℝ)/12288), ((8225418295:ℝ)/768), ((405393305:ℝ)/64), ((233897305:ℝ)/96), ((15214535:ℝ)/24), (111705:ℝ), ((38540:ℝ)/3), ((2620:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_22; ring
  have h12 : centralNum12_22 q = ∑ e ∈ Finset.range 15, ([((-298468165251830336443:ℝ)/6442450944), ((-181657868542086405587:ℝ)/1610612736), ((-4708566348159763409:ℝ)/50331648), ((-48288989343702747:ℝ)/16777216), ((1383735586207291411:ℝ)/25165824), ((314960048965492247:ℝ)/6291456), ((6204383621989903:ℝ)/262144), ((658279002640957:ℝ)/98304), ((99880966565003:ℝ)/98304), ((-6859095989:ℝ)/24576), ((-18633318681:ℝ)/512), ((-2135868723:ℝ)/256), ((-124124481:ℝ)/128), ((-1945701:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_22; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((231003634615:ℝ)/49152), ((130714123445:ℝ)/12288), ((8225418295:ℝ)/768), ((405393305:ℝ)/64), ((233897305:ℝ)/96), ((15214535:ℝ)/24), (111705:ℝ), ((38540:ℝ)/3), ((2620:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-298468165251830336443:ℝ)/6442450944), ((-181657868542086405587:ℝ)/1610612736), ((-4708566348159763409:ℝ)/50331648), ((-48288989343702747:ℝ)/16777216), ((1383735586207291411:ℝ)/25165824), ((314960048965492247:ℝ)/6291456), ((6204383621989903:ℝ)/262144), ((658279002640957:ℝ)/98304), ((99880966565003:ℝ)/98304), ((-6859095989:ℝ)/24576), ((-18633318681:ℝ)/512), ((-2135868723:ℝ)/256), ((-124124481:ℝ)/128), ((-1945701:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-298468165251830336443:ℝ)/6442450944), ((-181657868542086405587:ℝ)/1610612736), ((-4708566348159763409:ℝ)/50331648), ((-48288989343702747:ℝ)/16777216), ((1383735586207291411:ℝ)/25165824), ((314960048965492247:ℝ)/6291456), ((6204383621989903:ℝ)/262144), ((658279002640957:ℝ)/98304), ((99880966565003:ℝ)/98304), ((-6859095989:ℝ)/24576), ((-18633318681:ℝ)/512), ((-2135868723:ℝ)/256), ((-124124481:ℝ)/128), ((-1945701:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((231003634615:ℝ)/49152), ((130714123445:ℝ)/12288), ((8225418295:ℝ)/768), ((405393305:ℝ)/64), ((233897305:ℝ)/96), ((15214535:ℝ)/24), (111705:ℝ), ((38540:ℝ)/3), ((2620:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((231003634615:ℝ)/49152) + ((130714123445:ℝ)/12288)*t)| ≤ ((66198387668107:ℝ)/2400000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-298468165251830336443:ℝ)/6442450944), ((-181657868542086405587:ℝ)/1610612736), ((-4708566348159763409:ℝ)/50331648), ((-48288989343702747:ℝ)/16777216), ((1383735586207291411:ℝ)/25165824), ((314960048965492247:ℝ)/6291456), ((6204383621989903:ℝ)/262144), ((658279002640957:ℝ)/98304), ((99880966565003:ℝ)/98304), ((-6859095989:ℝ)/24576), ((-18633318681:ℝ)/512), ((-2135868723:ℝ)/256), ((-124124481:ℝ)/128), ((-1945701:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e) - ((-298468165251830336443:ℝ)/6442450944) - ((-181657868542086405587:ℝ)/1610612736)*t| ≤ ((2306177190393280598027829239:ℝ)/9830400000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-298468165251830336443:ℝ)/6442450944), ((-181657868542086405587:ℝ)/1610612736), ((-4708566348159763409:ℝ)/50331648), ((-48288989343702747:ℝ)/16777216), ((1383735586207291411:ℝ)/25165824), ((314960048965492247:ℝ)/6291456), ((6204383621989903:ℝ)/262144), ((658279002640957:ℝ)/98304), ((99880966565003:ℝ)/98304), ((-6859095989:ℝ)/24576), ((-18633318681:ℝ)/512), ((-2135868723:ℝ)/256), ((-124124481:ℝ)/128), ((-1945701:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e)| ≤ ((1026340073375682855020518549103:ℝ)/19660800000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((49650979433:ℝ)/8192) - ((29471971749:ℝ)/2048)*t| ≤ ((311553438853703:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((43:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82125:ℝ), (-6663750:ℝ), (115666200:ℝ), (-750437000:ℝ), (2277262000:ℝ), (-3656824320:ℝ), (3359621120:ℝ), (-1817706496:ℝ), ((1625292800:ℝ)/3), (-67108864:ℝ)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_22 q| ≤ ((74902452196318446889181974817:ℝ)/292968750000) := by
    rw [centralNum13_22_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((43:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((178425:ℝ)/2), ((-13176075:ℝ)/2), ((777815145:ℝ)/8), ((-3968389015:ℝ)/8), ((9393350195:ℝ)/8), ((-26366634375:ℝ)/16), ((77851609375:ℝ)/64), ((-25714921875:ℝ)/64), ((5236328125:ℝ)/96), ((-9765625:ℝ)/4)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_22 q| ≤ ((6566113516816245811609722247:ℝ)/153600000000) := by
    rw [centralNum23_22_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((172275955240474463017463468103:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece15_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece15_E11 h0) m23'
  have c5 := scaled_affine (X := ((460001673167:ℝ)/5000000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2))| ≤ ((2911753989209149726923097600000000:ℝ)/67901460798220942397974844249595681) := by
    rw [abs_neg, tailWeight_2, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((43:ℝ)/10)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((43:ℝ)/10)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece15_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((2570430941234500:ℝ)/4782969)) ≤ ((43:ℝ)/10)^6*(8000*(2*((43:ℝ)/10)-3)^2*(1/((99375560574937156562341070943:ℝ)/5000000000))*((2570430941234500:ℝ)/4782969)) := by
          gcongr
      _ ≤ ((2911753989209149726923097600000000:ℝ)/67901460798220942397974844249595681) := by norm_num
  have c7 := affine_round (α := ((231003634615:ℝ)/49152) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((-298468165251830336443:ℝ)/6442450944) + ((49650979433:ℝ)/8192)*((460001673167:ℝ)/5000000000000) - ((418170823237198201:ℝ)/100000000000)) (β := ((130714123445:ℝ)/12288) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((-181657868542086405587:ℝ)/1610612736) - 3*((-298468165251830336443:ℝ)/6442450944)) + ((29471971749:ℝ)/2048)*((460001673167:ℝ)/5000000000000) - ((125697412065724601:ℝ)/10000000000)) ht
  have hW : pieceW q pieceX_15 2 2 = centralNum11_22 q + 8*(Real.exp (-(3*((17:ℝ)/4)))*Real.exp (-3*t))*centralNum12_22 q + 18*Real.exp (-8*q)*centralNum13_22 q + 72*Real.exp (-11*q)*centralNum23_22 q + 8*q^7*(2*q-3)^2*((460001673167:ℝ)/5000000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2)) := by
    rw [pieceW_22, pieceX_15, sym4_22, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((31952002144055478093073997693110919752099342721193529831531011713:ℝ)/18234756436378746467918421622529320766892491474351715661611724800000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((231003634615:ℝ)/49152) + ((130714123445:ℝ)/12288)*t) + (8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((-298468165251830336443:ℝ)/6442450944) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((-181657868542086405587:ℝ)/1610612736) - 3*((-298468165251830336443:ℝ)/6442450944))*t) + (((49650979433:ℝ)/8192) + ((29471971749:ℝ)/2048)*t)*((460001673167:ℝ)/5000000000000) - (((418170823237198201:ℝ)/100000000000) + t * ((125697412065724601:ℝ)/10000000000)) = (((231003634615:ℝ)/49152) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((-298468165251830336443:ℝ)/6442450944) + ((49650979433:ℝ)/8192)*((460001673167:ℝ)/5000000000000) - ((418170823237198201:ℝ)/100000000000)) + t*(((130714123445:ℝ)/12288) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((-181657868542086405587:ℝ)/1610612736) - 3*((-298468165251830336443:ℝ)/6442450944)) + ((29471971749:ℝ)/2048)*((460001673167:ℝ)/5000000000000) - ((125697412065724601:ℝ)/10000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece15_e23 {q : ℝ} (h0 : ((21:ℝ)/5) ≤ q) (h1 : q ≤ ((43:ℝ)/10)) :
    |pieceW q pieceX_15 2 3 - (((-149260318859369123:ℝ)/100000000000) + (q - ((17:ℝ)/4)) * ((-968099743662044473:ℝ)/100000000000))| ≤ ((11610829567817957:ℝ)/25000000000) := by
  set t := q - ((17:ℝ)/4) with htd
  have hq : q = ((17:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece15_L3 piece15_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((17:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_23 q = ∑ e ∈ Finset.range 9, ([((149084985:ℝ)/128), ((4346850445:ℝ)/2048), ((939439295:ℝ)/512), ((125762685:ℝ)/128), ((11199175:ℝ)/32), ((662495:ℝ)/8), ((24885:ℝ)/2), (1070:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_23; ring
  have h12 : centralNum12_23 q = ∑ e ∈ Finset.range 16, ([((4641769121390344843539:ℝ)/120259084288), ((-438740996348751998387:ℝ)/15032385536), ((-290350280571305795351:ℝ)/1073741824), ((-397858847481370948131:ℝ)/939524096), ((-155939211712631309329:ℝ)/469762048), ((-8636783793370414699:ℝ)/58720256), ((-923014580434924629:ℝ)/29360128), ((9622915730792029:ℝ)/3670016), ((7273738565987833:ℝ)/1835008), ((41081450131929:ℝ)/32768), ((22670650476189:ℝ)/114688), ((149340518127:ℝ)/14336), ((-13592360763:ℝ)/7168), ((-376835409:ℝ)/896), ((-15162471:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_23; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((149084985:ℝ)/128), ((4346850445:ℝ)/2048), ((939439295:ℝ)/512), ((125762685:ℝ)/128), ((11199175:ℝ)/32), ((662495:ℝ)/8), ((24885:ℝ)/2), (1070:ℝ), (40:ℝ)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((4641769121390344843539:ℝ)/120259084288), ((-438740996348751998387:ℝ)/15032385536), ((-290350280571305795351:ℝ)/1073741824), ((-397858847481370948131:ℝ)/939524096), ((-155939211712631309329:ℝ)/469762048), ((-8636783793370414699:ℝ)/58720256), ((-923014580434924629:ℝ)/29360128), ((9622915730792029:ℝ)/3670016), ((7273738565987833:ℝ)/1835008), ((41081450131929:ℝ)/32768), ((22670650476189:ℝ)/114688), ((149340518127:ℝ)/14336), ((-13592360763:ℝ)/7168), ((-376835409:ℝ)/896), ((-15162471:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 14 ht
  have m12 := abs_poly_le (fun e => ([((4641769121390344843539:ℝ)/120259084288), ((-438740996348751998387:ℝ)/15032385536), ((-290350280571305795351:ℝ)/1073741824), ((-397858847481370948131:ℝ)/939524096), ((-155939211712631309329:ℝ)/469762048), ((-8636783793370414699:ℝ)/58720256), ((-923014580434924629:ℝ)/29360128), ((9622915730792029:ℝ)/3670016), ((7273738565987833:ℝ)/1835008), ((41081450131929:ℝ)/32768), ((22670650476189:ℝ)/114688), ((149340518127:ℝ)/14336), ((-13592360763:ℝ)/7168), ((-376835409:ℝ)/896), ((-15162471:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 16 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((149084985:ℝ)/128), ((4346850445:ℝ)/2048), ((939439295:ℝ)/512), ((125762685:ℝ)/128), ((11199175:ℝ)/32), ((662495:ℝ)/8), ((24885:ℝ)/2), (1070:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e) - (((149084985:ℝ)/128) + ((4346850445:ℝ)/2048)*t)| ≤ ((3015766059211:ℝ)/640000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 16, ([((4641769121390344843539:ℝ)/120259084288), ((-438740996348751998387:ℝ)/15032385536), ((-290350280571305795351:ℝ)/1073741824), ((-397858847481370948131:ℝ)/939524096), ((-155939211712631309329:ℝ)/469762048), ((-8636783793370414699:ℝ)/58720256), ((-923014580434924629:ℝ)/29360128), ((9622915730792029:ℝ)/3670016), ((7273738565987833:ℝ)/1835008), ((41081450131929:ℝ)/32768), ((22670650476189:ℝ)/114688), ((149340518127:ℝ)/14336), ((-13592360763:ℝ)/7168), ((-376835409:ℝ)/896), ((-15162471:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e) - ((4641769121390344843539:ℝ)/120259084288) - ((-438740996348751998387:ℝ)/15032385536)*t| ≤ ((2683072196601345391342989108153:ℝ)/3670016000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 16, ([((4641769121390344843539:ℝ)/120259084288), ((-438740996348751998387:ℝ)/15032385536), ((-290350280571305795351:ℝ)/1073741824), ((-397858847481370948131:ℝ)/939524096), ((-155939211712631309329:ℝ)/469762048), ((-8636783793370414699:ℝ)/58720256), ((-923014580434924629:ℝ)/29360128), ((9622915730792029:ℝ)/3670016), ((7273738565987833:ℝ)/1835008), ((41081450131929:ℝ)/32768), ((22670650476189:ℝ)/114688), ((149340518127:ℝ)/14336), ((-13592360763:ℝ)/7168), ((-376835409:ℝ)/896), ((-15162471:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e)| ≤ ((74847174524964577158772690843139:ℝ)/1835008000000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((49650979433:ℝ)/8192) - ((29471971749:ℝ)/2048)*t| ≤ ((311553438853703:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((43:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-7627725:ℝ)/2), (173988600:ℝ), (-2299614450:ℝ), (13088188200:ℝ), (-38221499200:ℝ), (63366115840:ℝ), ((-445610508288:ℝ)/7), ((841540698112:ℝ)/21), ((-326820167680:ℝ)/21), ((10133438464:ℝ)/3), ((-2147483648:ℝ)/7)] : List ℝ).getD e 0) 16 hq1'
  have m13' : |centralNum13_23 q| ≤ ((4148013799521727824806872204041:ℝ)/488281250000) := by
    rw [centralNum13_23_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((43:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-15801525:ℝ)/4), ((655493865:ℝ)/4), ((-7334421225:ℝ)/4), ((16442962485:ℝ)/2), ((-598626108395:ℝ)/32), ((414013307125:ℝ)/16), ((-4611984703125:ℝ)/224), ((399923828125:ℝ)/48), ((-4353201171875:ℝ)/2688), ((189736328125:ℝ)/1344), ((-244140625:ℝ)/56)] : List ℝ).getD e 0) 16 hq1'
  have m23' : |centralNum23_23 q| ≤ ((1415009240276457436228246340693:ℝ)/1433600000000) := by
    rw [centralNum23_23_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((172275955240474463017463468103:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece15_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece15_E11 h0) m23'
  have c5 := scaled_affine (X := ((-58630167601:ℝ)/100000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((149084985:ℝ)/128) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((4641769121390344843539:ℝ)/120259084288) + ((49650979433:ℝ)/8192)*((-58630167601:ℝ)/100000000000) - ((-149260318859369123:ℝ)/100000000000)) (β := ((4346850445:ℝ)/2048) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((-438740996348751998387:ℝ)/15032385536) - 3*((4641769121390344843539:ℝ)/120259084288)) + ((29471971749:ℝ)/2048)*((-58630167601:ℝ)/100000000000) - ((-968099743662044473:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_15 2 3 = centralNum11_23 q + 8*(Real.exp (-(3*((17:ℝ)/4)))*Real.exp (-3*t))*centralNum12_23 q + 18*Real.exp (-8*q)*centralNum13_23 q + 72*Real.exp (-11*q)*centralNum23_23 q + 8*q^7*(2*q-3)^2*((-58630167601:ℝ)/100000000000) + (0:ℝ) := by
    rw [pieceW_23, pieceX_15, sym4_23, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((433993906554978772553120696084808964789879160080690276111351561:ℝ)/170191060072868300367238601810273660490996587093949346175042764800000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((149084985:ℝ)/128) + ((4346850445:ℝ)/2048)*t) + (8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((4641769121390344843539:ℝ)/120259084288) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((-438740996348751998387:ℝ)/15032385536) - 3*((4641769121390344843539:ℝ)/120259084288))*t) + (((49650979433:ℝ)/8192) + ((29471971749:ℝ)/2048)*t)*((-58630167601:ℝ)/100000000000) - (((-149260318859369123:ℝ)/100000000000) + t * ((-968099743662044473:ℝ)/100000000000)) = (((149084985:ℝ)/128) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((4641769121390344843539:ℝ)/120259084288) + ((49650979433:ℝ)/8192)*((-58630167601:ℝ)/100000000000) - ((-149260318859369123:ℝ)/100000000000)) + t*(((4346850445:ℝ)/2048) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((-438740996348751998387:ℝ)/15032385536) - 3*((4641769121390344843539:ℝ)/120259084288)) + ((29471971749:ℝ)/2048)*((-58630167601:ℝ)/100000000000) - ((-968099743662044473:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece15_e33 {q : ℝ} (h0 : ((21:ℝ)/5) ≤ q) (h1 : q ≤ ((43:ℝ)/10)) :
    |pieceW q pieceX_15 3 3 - (((36584281062583551:ℝ)/1250000000) + (q - ((17:ℝ)/4)) * ((74829221954250799:ℝ)/1000000000))| ≤ ((29201761920732719:ℝ)/2000000000) := by
  set t := q - ((17:ℝ)/4) with htd
  have hq : q = ((17:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece15_L3 piece15_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((17:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_33 q = ∑ e ∈ Finset.range 10, ([((67914683545:ℝ)/57344), ((27298765155:ℝ)/7168), ((17135990565:ℝ)/3584), ((420123975:ℝ)/128), ((44934405:ℝ)/32), ((3174855:ℝ)/8), ((150465:ℝ)/2), ((65190:ℝ)/7), ((4800:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_33; ring
  have h12 : centralNum12_33 q = ∑ e ∈ Finset.range 17, ([((661991263030803738070063:ℝ)/6734508720128), ((1204305065443213239650829:ℝ)/1683627180032), ((619402468857517355753445:ℝ)/420906795008), ((21481036840672195251183:ℝ)/15032385536), ((2606009094258744692211:ℝ)/3758096384), ((74996497035929288895:ℝ)/939524096), ((-24286945653598032537:ℝ)/234881024), ((-28289676983942109675:ℝ)/411041792), ((-2092441953675444969:ℝ)/102760448), ((-68510093547579913:ℝ)/25690112), ((167111492228937:ℝ)/917504), ((30164518683549:ℝ)/229376), ((1192708831185:ℝ)/57344), ((14690234277:ℝ)/14336), ((-2674506357:ℝ)/25088), ((-105874857:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_33; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((67914683545:ℝ)/57344), ((27298765155:ℝ)/7168), ((17135990565:ℝ)/3584), ((420123975:ℝ)/128), ((44934405:ℝ)/32), ((3174855:ℝ)/8), ((150465:ℝ)/2), ((65190:ℝ)/7), ((4800:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((661991263030803738070063:ℝ)/6734508720128), ((1204305065443213239650829:ℝ)/1683627180032), ((619402468857517355753445:ℝ)/420906795008), ((21481036840672195251183:ℝ)/15032385536), ((2606009094258744692211:ℝ)/3758096384), ((74996497035929288895:ℝ)/939524096), ((-24286945653598032537:ℝ)/234881024), ((-28289676983942109675:ℝ)/411041792), ((-2092441953675444969:ℝ)/102760448), ((-68510093547579913:ℝ)/25690112), ((167111492228937:ℝ)/917504), ((30164518683549:ℝ)/229376), ((1192708831185:ℝ)/57344), ((14690234277:ℝ)/14336), ((-2674506357:ℝ)/25088), ((-105874857:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 15 ht
  have m12 := abs_poly_le (fun e => ([((661991263030803738070063:ℝ)/6734508720128), ((1204305065443213239650829:ℝ)/1683627180032), ((619402468857517355753445:ℝ)/420906795008), ((21481036840672195251183:ℝ)/15032385536), ((2606009094258744692211:ℝ)/3758096384), ((74996497035929288895:ℝ)/939524096), ((-24286945653598032537:ℝ)/234881024), ((-28289676983942109675:ℝ)/411041792), ((-2092441953675444969:ℝ)/102760448), ((-68510093547579913:ℝ)/25690112), ((167111492228937:ℝ)/917504), ((30164518683549:ℝ)/229376), ((1192708831185:ℝ)/57344), ((14690234277:ℝ)/14336), ((-2674506357:ℝ)/25088), ((-105874857:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 17 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((67914683545:ℝ)/57344), ((27298765155:ℝ)/7168), ((17135990565:ℝ)/3584), ((420123975:ℝ)/128), ((44934405:ℝ)/32), ((3174855:ℝ)/8), ((150465:ℝ)/2), ((65190:ℝ)/7), ((4800:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e) - (((67914683545:ℝ)/57344) + ((27298765155:ℝ)/7168)*t)| ≤ ((277139457046201:ℝ)/22400000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 17, ([((661991263030803738070063:ℝ)/6734508720128), ((1204305065443213239650829:ℝ)/1683627180032), ((619402468857517355753445:ℝ)/420906795008), ((21481036840672195251183:ℝ)/15032385536), ((2606009094258744692211:ℝ)/3758096384), ((74996497035929288895:ℝ)/939524096), ((-24286945653598032537:ℝ)/234881024), ((-28289676983942109675:ℝ)/411041792), ((-2092441953675444969:ℝ)/102760448), ((-68510093547579913:ℝ)/25690112), ((167111492228937:ℝ)/917504), ((30164518683549:ℝ)/229376), ((1192708831185:ℝ)/57344), ((14690234277:ℝ)/14336), ((-2674506357:ℝ)/25088), ((-105874857:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e) - ((661991263030803738070063:ℝ)/6734508720128) - ((1204305065443213239650829:ℝ)/1683627180032)*t| ≤ ((496070925892615633129731628080199:ℝ)/128450560000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 17, ([((661991263030803738070063:ℝ)/6734508720128), ((1204305065443213239650829:ℝ)/1683627180032), ((619402468857517355753445:ℝ)/420906795008), ((21481036840672195251183:ℝ)/15032385536), ((2606009094258744692211:ℝ)/3758096384), ((74996497035929288895:ℝ)/939524096), ((-24286945653598032537:ℝ)/234881024), ((-28289676983942109675:ℝ)/411041792), ((-2092441953675444969:ℝ)/102760448), ((-68510093547579913:ℝ)/25690112), ((167111492228937:ℝ)/917504), ((30164518683549:ℝ)/229376), ((1192708831185:ℝ)/57344), ((14690234277:ℝ)/14336), ((-2674506357:ℝ)/25088), ((-105874857:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e)| ≤ ((1265472247912386693282074074857291:ℝ)/9175040000000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((49650979433:ℝ)/8192), ((29471971749:ℝ)/2048), ((966922617:ℝ)/64), ((36832761:ℝ)/4), ((57467361:ℝ)/16), ((3720297:ℝ)/4), (159936:ℝ), (17616:ℝ), (1128:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((49650979433:ℝ)/8192) - ((29471971749:ℝ)/2048)*t| ≤ ((311553438853703:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((43:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-8120475:ℝ)/4), ((464861025:ℝ)/2), (-5906535975:ℝ), ((411904731750:ℝ)/7), ((-2024051769000:ℝ)/7), ((5554394637600:ℝ)/7), (-1314913862656:ℝ), ((9709155336192:ℝ)/7), ((-6724555112448:ℝ)/7), ((1313173667840:ℝ)/3), ((-6168244125696:ℝ)/49), ((3004329623552:ℝ)/147), ((-68719476736:ℝ)/49)] : List ℝ).getD e 0) 17 hq1'
  have m13' : |centralNum13_33 q| ≤ ((220259643087107712537299937850037201:ℝ)/717773437500000) := by
    rw [centralNum13_33_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((43:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-16872075:ℝ)/8), ((1833754545:ℝ)/8), ((-83998007145:ℝ)/16), ((4929124002765:ℝ)/112), ((-76723155584685:ℝ)/448), ((164888745653055:ℝ)/448), ((-63358359907625:ℝ)/128), ((364713160040625:ℝ)/896), ((-334937462578125:ℝ)/1792), ((245466998046875:ℝ)/5376), ((-72144521484375:ℝ)/12544), ((6518798828125:ℝ)/18816), ((-6103515625:ℝ)/784)] : List ℝ).getD e 0) 17 hq1'
  have m23' : |centralNum23_33 q| ≤ ((3110432030987595602319839965946207:ℝ)/120422400000000) := by
    rw [centralNum23_33_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((172275955240474463017463468103:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece15_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece15_E11 h0) m23'
  have c5 := scaled_affine (X := ((42569079329:ℝ)/10000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3))| ≤ ((3747911301442165604649879155200000000:ℝ)/1833339441551965444745320794739083387) := by
    rw [abs_neg, tailWeight_3, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((43:ℝ)/10)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((43:ℝ)/10)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece15_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((3308571812705231500:ℝ)/129140163)) ≤ ((43:ℝ)/10)^6*(8000*(2*((43:ℝ)/10)-3)^2*(1/((99375560574937156562341070943:ℝ)/5000000000))*((3308571812705231500:ℝ)/129140163)) := by
          gcongr
      _ ≤ ((3747911301442165604649879155200000000:ℝ)/1833339441551965444745320794739083387) := by norm_num
  have c7 := affine_round (α := ((67914683545:ℝ)/57344) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((661991263030803738070063:ℝ)/6734508720128) + ((49650979433:ℝ)/8192)*((42569079329:ℝ)/10000000000) - ((36584281062583551:ℝ)/1250000000)) (β := ((27298765155:ℝ)/7168) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((1204305065443213239650829:ℝ)/1683627180032) - 3*((661991263030803738070063:ℝ)/6734508720128)) + ((29471971749:ℝ)/2048)*((42569079329:ℝ)/10000000000) - ((74829221954250799:ℝ)/1000000000)) ht
  have hW : pieceW q pieceX_15 3 3 = centralNum11_33 q + 8*(Real.exp (-(3*((17:ℝ)/4)))*Real.exp (-3*t))*centralNum12_33 q + 18*Real.exp (-8*q)*centralNum13_33 q + 72*Real.exp (-11*q)*centralNum23_33 q + 8*q^7*(2*q-3)^2*((42569079329:ℝ)/10000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3)) := by
    rw [pieceW_33, pieceX_15, sym4_33, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((20633764669662834993807964211383343825062664824084184017013645173:ℝ)/595668710255039051285335106335957811718488054828822711612649676800000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((67914683545:ℝ)/57344) + ((27298765155:ℝ)/7168)*t) + (8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((661991263030803738070063:ℝ)/6734508720128) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((1204305065443213239650829:ℝ)/1683627180032) - 3*((661991263030803738070063:ℝ)/6734508720128))*t) + (((49650979433:ℝ)/8192) + ((29471971749:ℝ)/2048)*t)*((42569079329:ℝ)/10000000000) - (((36584281062583551:ℝ)/1250000000) + t * ((74829221954250799:ℝ)/1000000000)) = (((67914683545:ℝ)/57344) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*((661991263030803738070063:ℝ)/6734508720128) + ((49650979433:ℝ)/8192)*((42569079329:ℝ)/10000000000) - ((36584281062583551:ℝ)/1250000000)) + t*(((27298765155:ℝ)/7168) + 8*(((1/((172275955240474463017463468103:ℝ)/500000000000000000000000))+(1/((344551455396940947292714505003:ℝ)/1000000000000000000000000)))/2)*(((1204305065443213239650829:ℝ)/1683627180032) - 3*((661991263030803738070063:ℝ)/6734508720128)) + ((29471971749:ℝ)/2048)*((42569079329:ℝ)/10000000000) - ((74829221954250799:ℝ)/1000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece15_plus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((365796843547401301:ℝ)/50000000000) + ((1:ℝ)/20)*((82685047305684533:ℝ)/5000000000) - (((436833273365836533:ℝ)/10000000000000) + ((644639573445928807:ℝ)/100000000000000) + ((219656311303091647:ℝ)/100000000000000) + ((20048663721643673:ℝ)/2500000000000)))
      (((-125453697356078433:ℝ)/100000000000) + ((1:ℝ)/20)*((-24841793999561663:ℝ)/12500000000))
      (((-210250518139271027:ℝ)/250000000000000) + ((1:ℝ)/20)*((-24023002815871681:ℝ)/625000000000))
      (((143243281901315867:ℝ)/5000000000000) + ((1:ℝ)/20)*((-248829675392603407:ℝ)/1000000000000))
      (((560117188173585927:ℝ)/100000000000) + ((1:ℝ)/20)*((1477871724186003:ℝ)/125000000) - (((644639573445928807:ℝ)/100000000000000) + ((307677860950553273:ℝ)/10000000000000) + ((105919561666455747:ℝ)/5000000000000) + ((368981067969698989:ℝ)/10000000000000)))
      (((-296657392725368321:ℝ)/500000000000) + ((1:ℝ)/20)*((-64403031746487319:ℝ)/50000000000))
      (((16471448384060823:ℝ)/50000000000) + ((1:ℝ)/20)*((13760979503664453:ℝ)/5000000000))
      (((418170823237198201:ℝ)/100000000000) + ((1:ℝ)/20)*((125697412065724601:ℝ)/10000000000) - (((219656311303091647:ℝ)/100000000000000) + ((105919561666455747:ℝ)/5000000000000) + ((12013702830690817:ℝ)/125000000000) + ((11610829567817957:ℝ)/25000000000)))
      (((-149260318859369123:ℝ)/100000000000) + ((1:ℝ)/20)*((-968099743662044473:ℝ)/100000000000))
      (((36584281062583551:ℝ)/1250000000) + ((1:ℝ)/20)*((74829221954250799:ℝ)/1000000000) - (((20048663721643673:ℝ)/2500000000000) + ((368981067969698989:ℝ)/10000000000000) + ((11610829567817957:ℝ)/25000000000) + ((29201761920732719:ℝ)/2000000000))) i j :=
  quadForm_nonneg_of_ldl ((101030519904151750287:ℝ)/12500000000000) ((59307233643748146320529445214552116286671:ℝ)/10103051990415175028700000000000000) ((1231358929884216181251239066634923978791754398802153395692243653:ℝ)/296536168218740731602647226072760581433355000000000000000) ((1671652343183899827809035074679435684039566227545753866430729454816617979376828616131:ℝ)/98508714390737294500099125330793918303340351904172271655379492240000000000000) ((-16923801869487887275:ℝ)/101030519904151750287) ((-690710574456704647:ℝ)/2020610398083035005740) ((1620717261063300305:ℝ)/808244159233214002296) ((-6649633081730443947553877182159984547470:ℝ)/59307233643748146320529445214552116286671) ((4745945599090420485235383433759173531875:ℝ)/59307233643748146320529445214552116286671) ((-1141058068723202662680663900540059917588668188728718204649599725:ℝ)/2462717859768432362502478133269847957583508797604306791384487306)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece15_minus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((365796843547401301:ℝ)/50000000000) - ((1:ℝ)/20)*((82685047305684533:ℝ)/5000000000) - (((436833273365836533:ℝ)/10000000000000) + ((644639573445928807:ℝ)/100000000000000) + ((219656311303091647:ℝ)/100000000000000) + ((20048663721643673:ℝ)/2500000000000)))
      (((-125453697356078433:ℝ)/100000000000) - ((1:ℝ)/20)*((-24841793999561663:ℝ)/12500000000))
      (((-210250518139271027:ℝ)/250000000000000) - ((1:ℝ)/20)*((-24023002815871681:ℝ)/625000000000))
      (((143243281901315867:ℝ)/5000000000000) - ((1:ℝ)/20)*((-248829675392603407:ℝ)/1000000000000))
      (((560117188173585927:ℝ)/100000000000) - ((1:ℝ)/20)*((1477871724186003:ℝ)/125000000) - (((644639573445928807:ℝ)/100000000000000) + ((307677860950553273:ℝ)/10000000000000) + ((105919561666455747:ℝ)/5000000000000) + ((368981067969698989:ℝ)/10000000000000)))
      (((-296657392725368321:ℝ)/500000000000) - ((1:ℝ)/20)*((-64403031746487319:ℝ)/50000000000))
      (((16471448384060823:ℝ)/50000000000) - ((1:ℝ)/20)*((13760979503664453:ℝ)/5000000000))
      (((418170823237198201:ℝ)/100000000000) - ((1:ℝ)/20)*((125697412065724601:ℝ)/10000000000) - (((219656311303091647:ℝ)/100000000000000) + ((105919561666455747:ℝ)/5000000000000) + ((12013702830690817:ℝ)/125000000000) + ((11610829567817957:ℝ)/25000000000)))
      (((-149260318859369123:ℝ)/100000000000) - ((1:ℝ)/20)*((-968099743662044473:ℝ)/100000000000))
      (((36584281062583551:ℝ)/1250000000) - ((1:ℝ)/20)*((74829221954250799:ℝ)/1000000000) - (((20048663721643673:ℝ)/2500000000000) + ((368981067969698989:ℝ)/10000000000000) + ((11610829567817957:ℝ)/25000000000) + ((29201761920732719:ℝ)/2000000000))) i j :=
  quadForm_nonneg_of_ldl ((80359258077730617037:ℝ)/12500000000000) ((37826359889452013381210709285321745859421:ℝ)/8035925807773061703700000000000000) ((20383582056391116327656471737249894590814793461179484969712179:ℝ)/7004881461009632107631612830615138122115000000000000000) ((49276814746143873771544728308276953492042724339300001818106030251570321943462922499:ℝ)/4892059693533867918637553216939974701795550430683076392730922960000000000000) ((-14439622469531720975:ℝ)/80359258077730617037) ((270209538178162593:ℝ)/1607185161554612340740) ((4109014014989334375:ℝ)/642874064621844936296) ((-157360552671811212121877608547632896290:ℝ)/1400976292201926421526322566123027624423) ((533592416992884270512225862042157718875:ℝ)/12608786629817337793736903095107248619807) ((-13816223346078703583174855557930696941257090568115139724395625:ℝ)/40767164112782232655312943474499789181629586922358969939424358)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

/-- **Piece 15.** The piece matrix is positive semidefinite on `q ∈ [21/5, 43/10]`. -/
theorem piece_15 {q : ℝ} (h0 : ((21:ℝ)/5) ≤ q) (h1 : q ≤ ((43:ℝ)/10)) (y : Fin 4 → ℝ) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceW q pieceX_15 i j :=
  pieceForm_nonneg (pieceW_symm (sym4_symm _ _ _ _ _ _ _ _ _ _) q) (by norm_num : (0:ℝ) < ((1:ℝ)/20))
    (abs_le.mpr ⟨by linarith, by linarith⟩)
    (piece15_e00 h0 h1) (piece15_e01 h0 h1) (piece15_e02 h0 h1) (piece15_e03 h0 h1) (piece15_e11 h0 h1) (piece15_e12 h0 h1) (piece15_e13 h0 h1) (piece15_e22 h0 h1) (piece15_e23 h0 h1) (piece15_e33 h0 h1)
    piece15_plus piece15_minus y

/-! #### Piece 16 (seam), `q ∈ [43/10, 22/5]` -/

/-- The compensation matrix of piece 16. -/
def pieceX_16 : Fin 4 → Fin 4 → ℝ :=
  sym4 ((110104789471:ℝ)/10000000000000) ((-15057506059:ℝ)/62500000000000) ((384514158423:ℝ)/500000000000000) ((-374809743411:ℝ)/100000000000000) ((167843206691:ℝ)/10000000000000) ((-184069901641:ℝ)/10000000000000) ((901328149831:ℝ)/10000000000000) ((695877282219:ℝ)/10000000000000) ((-7169768159:ℝ)/25000000000) ((35388847709:ℝ)/25000000000)

theorem piece16_L3 : ((465096411314890046271789904047:ℝ)/1000000000000000000000000) ≤ Real.exp ((3:ℝ)*((87:ℝ)/20)) := by
  have h := le_exp_nat_add 13 (f := ((1:ℝ)/20)) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((87:ℝ)/20) = ((13:ℕ):ℝ) + ((1:ℝ)/20) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece16_U3 : Real.exp ((3:ℝ)*((87:ℝ)/20)) ≤ ((465096411982178219697953578871:ℝ)/1000000000000000000000000) := by
  have h := exp_nat_add_le 13 (f := ((1:ℝ)/20)) (by norm_num) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((87:ℝ)/20) = ((13:ℕ):ℝ) + ((1:ℝ)/20) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem piece16_L8_at : ((870422625977163737937519556989:ℝ)/1000000000000000) ≤ Real.exp ((8:ℝ)*((43:ℝ)/10)) := by
  have h := le_exp_nat_add 34 (f := ((2:ℝ)/5)) (by norm_num)
  rw [show ((8:ℝ):ℝ)*((43:ℝ)/10) = ((34:ℕ):ℝ) + ((2:ℝ)/5) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece16_E8 {q : ℝ} (h0 : ((43:ℝ)/10) ≤ q) : Real.exp (-((8:ℝ))*q) ≤ 1/((870422625977163737937519556989:ℝ)/1000000000000000) := by
  have hm : Real.exp (-((8:ℝ))*q) ≤ Real.exp (-((8:ℝ)*((43:ℝ)/10))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece16_L8_at (le_refl _)).2

theorem piece16_L11_at : ((348440792060643818291210141533:ℝ)/1000000000) ≤ Real.exp ((11:ℝ)*((43:ℝ)/10)) := by
  have h := le_exp_nat_add 47 (f := ((3:ℝ)/10)) (by norm_num)
  rw [show ((11:ℝ):ℝ)*((43:ℝ)/10) = ((47:ℕ):ℝ) + ((3:ℝ)/10) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece16_E11 {q : ℝ} (h0 : ((43:ℝ)/10) ≤ q) : Real.exp (-((11:ℝ))*q) ≤ 1/((348440792060643818291210141533:ℝ)/1000000000) := by
  have hm : Real.exp (-((11:ℝ))*q) ≤ Real.exp (-((11:ℝ)*((43:ℝ)/10))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece16_L11_at (le_refl _)).2

theorem piece16_Lt_at : ((114504651573259954108771412367:ℝ)/2000000000) ≤ Real.exp (((529:ℝ)/50)*((43:ℝ)/10)) := by
  have h := le_exp_nat_add 45 (f := ((247:ℝ)/500)) (by norm_num)
  rw [show (((529:ℝ)/50):ℝ)*((43:ℝ)/10) = ((45:ℕ):ℝ) + ((247:ℝ)/500) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece16_Et {q : ℝ} (h0 : ((43:ℝ)/10) ≤ q) : Real.exp (-(((529:ℝ)/50))*q) ≤ 1/((114504651573259954108771412367:ℝ)/2000000000) := by
  have hm : Real.exp (-(((529:ℝ)/50))*q) ≤ Real.exp (-(((529:ℝ)/50)*((43:ℝ)/10))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece16_Lt_at (le_refl _)).2

theorem piece16_e00 {q : ℝ} (h0 : ((43:ℝ)/10) ≤ q) (h1 : q ≤ ((22:ℝ)/5)) :
    |pieceW q pieceX_16 0 0 - (((914623869287462287:ℝ)/100000000000) + (q - ((87:ℝ)/20)) * ((100912001942736407:ℝ)/5000000000))| ≤ ((518153597132078979:ℝ)/10000000000000) := by
  set t := q - ((87:ℝ)/20) with htd
  have hq : q = ((87:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece16_L3 piece16_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((87:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_00 q = ∑ e ∈ Finset.range 10, ([((145205370548476767:ℝ)/16000000000), ((15983895395392749:ℝ)/800000000), ((6145529952231:ℝ)/312500), ((2835671300217:ℝ)/250000), ((210982385691:ℝ)/50000), ((2622181653:ℝ)/2500), ((21755916:ℝ)/125), ((464448:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_00; ring
  have h12 : centralNum12_00 q = ∑ e ∈ Finset.range 11, ([((-250113477947008879107:ℝ)/320000000000), ((-6087839978538327357:ℝ)/3200000000), ((-166811080113674991:ℝ)/80000000), ((-2709806783805459:ℝ)/2000000), ((-115584370579377:ℝ)/200000), ((-8452653342651:ℝ)/50000), ((-4292547462:ℝ)/125), ((-119566518:ℝ)/25), ((-2185086:ℝ)/5), (-23656:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_00; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((145205370548476767:ℝ)/16000000000), ((15983895395392749:ℝ)/800000000), ((6145529952231:ℝ)/312500), ((2835671300217:ℝ)/250000), ((210982385691:ℝ)/50000), ((2622181653:ℝ)/2500), ((21755916:ℝ)/125), ((464448:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-250113477947008879107:ℝ)/320000000000), ((-6087839978538327357:ℝ)/3200000000), ((-166811080113674991:ℝ)/80000000), ((-2709806783805459:ℝ)/2000000), ((-115584370579377:ℝ)/200000), ((-8452653342651:ℝ)/50000), ((-4292547462:ℝ)/125), ((-119566518:ℝ)/25), ((-2185086:ℝ)/5), (-23656:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 9 ht
  have m12 := abs_poly_le (fun e => ([((-250113477947008879107:ℝ)/320000000000), ((-6087839978538327357:ℝ)/3200000000), ((-166811080113674991:ℝ)/80000000), ((-2709806783805459:ℝ)/2000000), ((-115584370579377:ℝ)/200000), ((-8452653342651:ℝ)/50000), ((-4292547462:ℝ)/125), ((-119566518:ℝ)/25), ((-2185086:ℝ)/5), (-23656:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 11 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((145205370548476767:ℝ)/16000000000), ((15983895395392749:ℝ)/800000000), ((6145529952231:ℝ)/312500), ((2835671300217:ℝ)/250000), ((210982385691:ℝ)/50000), ((2622181653:ℝ)/2500), ((21755916:ℝ)/125), ((464448:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - (((145205370548476767:ℝ)/16000000000) + ((15983895395392749:ℝ)/800000000)*t)| ≤ ((202435114291693:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 11, ([((-250113477947008879107:ℝ)/320000000000), ((-6087839978538327357:ℝ)/3200000000), ((-166811080113674991:ℝ)/80000000), ((-2709806783805459:ℝ)/2000000), ((-115584370579377:ℝ)/200000), ((-8452653342651:ℝ)/50000), ((-4292547462:ℝ)/125), ((-119566518:ℝ)/25), ((-2185086:ℝ)/5), (-23656:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e) - ((-250113477947008879107:ℝ)/320000000000) - ((-6087839978538327357:ℝ)/3200000000)*t| ≤ ((86173992936418967:ℝ)/16000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 11, ([((-250113477947008879107:ℝ)/320000000000), ((-6087839978538327357:ℝ)/3200000000), ((-166811080113674991:ℝ)/80000000), ((-2709806783805459:ℝ)/2000000), ((-115584370579377:ℝ)/200000), ((-8452653342651:ℝ)/50000), ((-4292547462:ℝ)/125), ((-119566518:ℝ)/25), ((-2185086:ℝ)/5), (-23656:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((8614384695386624:ℝ)/9765625) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((122570082855806967:ℝ)/16000000000) - ((14162665351154949:ℝ)/800000000)*t| ≤ ((186430602969793:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((22:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (600:ℝ), (-7776:ℝ), (16800:ℝ), (-9216:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m13' : |centralNum13_00 q| ≤ ((357041809397289984:ℝ)/9765625) := by
    rw [centralNum13_00_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((22:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (780:ℝ), (-6156:ℝ), (15288:ℝ), (-14400:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m23' : |centralNum23_00 q| ≤ ((96687028807159296:ℝ)/1953125) := by
    rw [centralNum23_00_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece16_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece16_E11 h0) m23'
  have c5 := scaled_affine (X := ((110104789471:ℝ)/10000000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0))| ≤ ((40874456797445828378624000000:ℝ)/6761385170749427030168843128858983) := by
    rw [abs_neg, tailWeight_0, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((22:ℝ)/5)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((22:ℝ)/5)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece16_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((10465499600:ℝ)/59049)) ≤ ((22:ℝ)/5)^6*(8000*(2*((22:ℝ)/5)-3)^2*(1/((114504651573259954108771412367:ℝ)/2000000000))*((10465499600:ℝ)/59049)) := by
          gcongr
      _ ≤ ((40874456797445828378624000000:ℝ)/6761385170749427030168843128858983) := by norm_num
  have c7 := affine_round (α := ((145205370548476767:ℝ)/16000000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((-250113477947008879107:ℝ)/320000000000) + ((122570082855806967:ℝ)/16000000000)*((110104789471:ℝ)/10000000000000) - ((914623869287462287:ℝ)/100000000000)) (β := ((15983895395392749:ℝ)/800000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((-6087839978538327357:ℝ)/3200000000) - 3*((-250113477947008879107:ℝ)/320000000000)) + ((14162665351154949:ℝ)/800000000)*((110104789471:ℝ)/10000000000000) - ((100912001942736407:ℝ)/5000000000)) ht
  have hW : pieceW q pieceX_16 0 0 = centralNum11_00 q + 8*(Real.exp (-(3*((87:ℝ)/20)))*Real.exp (-3*t))*centralNum12_00 q + 18*Real.exp (-8*q)*centralNum13_00 q + 72*Real.exp (-11*q)*centralNum23_00 q + 8*q^7*(2*q-3)^2*((110104789471:ℝ)/10000000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0)) := by
    rw [pieceW_00, pieceX_16, sym4_00, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((36938507854126020916920306678936654945643413966166670031881125506406981:ℝ)/5768391256755805776901313961163585065155037509056248975758320000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((145205370548476767:ℝ)/16000000000) + ((15983895395392749:ℝ)/800000000)*t) + (8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((-250113477947008879107:ℝ)/320000000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((-6087839978538327357:ℝ)/3200000000) - 3*((-250113477947008879107:ℝ)/320000000000))*t) + (((122570082855806967:ℝ)/16000000000) + ((14162665351154949:ℝ)/800000000)*t)*((110104789471:ℝ)/10000000000000) - (((914623869287462287:ℝ)/100000000000) + t * ((100912001942736407:ℝ)/5000000000)) = (((145205370548476767:ℝ)/16000000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((-250113477947008879107:ℝ)/320000000000) + ((122570082855806967:ℝ)/16000000000)*((110104789471:ℝ)/10000000000000) - ((914623869287462287:ℝ)/100000000000)) + t*(((15983895395392749:ℝ)/800000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((-6087839978538327357:ℝ)/3200000000) - 3*((-250113477947008879107:ℝ)/320000000000)) + ((14162665351154949:ℝ)/800000000)*((110104789471:ℝ)/10000000000000) - ((100912001942736407:ℝ)/5000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece16_e01 {q : ℝ} (h0 : ((43:ℝ)/10) ≤ q) (h1 : q ≤ ((22:ℝ)/5)) :
    |pieceW q pieceX_16 0 1 - (((-146388986721594643:ℝ)/100000000000) + (q - ((87:ℝ)/20)) * ((-113687082922384783:ℝ)/50000000000))| ≤ ((27091723328696237:ℝ)/4000000000000) := by
  set t := q - ((87:ℝ)/20) with htd
  have hq : q = ((87:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece16_L3 piece16_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((87:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_01 q = ∑ e ∈ Finset.range 8, ([((-113176438463349:ℝ)/80000000), ((-9106150221189:ℝ)/4000000), ((-314005180041:ℝ)/200000), ((-1203084981:ℝ)/2000), ((-13828563:ℝ)/100), ((-476847:ℝ)/25), ((-7308:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_01; ring
  have h12 : centralNum12_01 q = ∑ e ∈ Finset.range 12, ([((-35227359690908095338507:ℝ)/12800000000000), ((-2510690420974103107353:ℝ)/320000000000), ((-64880378803868213493:ℝ)/6400000000), ((-1254327714401429331:ℝ)/160000000), ((-32261562722701611:ℝ)/8000000), ((-1449169027578153:ℝ)/1000000), ((-37127174887593:ℝ)/100000), ((-33909488511:ℝ)/500), ((-865660491:ℝ)/100), ((-3676866:ℝ)/5), ((-187092:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_01; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-113176438463349:ℝ)/80000000), ((-9106150221189:ℝ)/4000000), ((-314005180041:ℝ)/200000), ((-1203084981:ℝ)/2000), ((-13828563:ℝ)/100), ((-476847:ℝ)/25), ((-7308:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0) 6 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-35227359690908095338507:ℝ)/12800000000000), ((-2510690420974103107353:ℝ)/320000000000), ((-64880378803868213493:ℝ)/6400000000), ((-1254327714401429331:ℝ)/160000000), ((-32261562722701611:ℝ)/8000000), ((-1449169027578153:ℝ)/1000000), ((-37127174887593:ℝ)/100000), ((-33909488511:ℝ)/500), ((-865660491:ℝ)/100), ((-3676866:ℝ)/5), ((-187092:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0) 10 ht
  have m12 := abs_poly_le (fun e => ([((-35227359690908095338507:ℝ)/12800000000000), ((-2510690420974103107353:ℝ)/320000000000), ((-64880378803868213493:ℝ)/6400000000), ((-1254327714401429331:ℝ)/160000000), ((-32261562722701611:ℝ)/8000000), ((-1449169027578153:ℝ)/1000000), ((-37127174887593:ℝ)/100000), ((-33909488511:ℝ)/500), ((-865660491:ℝ)/100), ((-3676866:ℝ)/5), ((-187092:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0) 12 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 8, ([((-113176438463349:ℝ)/80000000), ((-9106150221189:ℝ)/4000000), ((-314005180041:ℝ)/200000), ((-1203084981:ℝ)/2000), ((-13828563:ℝ)/100), ((-476847:ℝ)/25), ((-7308:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0 * t^e) - (((-113176438463349:ℝ)/80000000) + ((-9106150221189:ℝ)/4000000)*t)| ≤ ((160045113219:ℝ)/40000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 12, ([((-35227359690908095338507:ℝ)/12800000000000), ((-2510690420974103107353:ℝ)/320000000000), ((-64880378803868213493:ℝ)/6400000000), ((-1254327714401429331:ℝ)/160000000), ((-32261562722701611:ℝ)/8000000), ((-1449169027578153:ℝ)/1000000), ((-37127174887593:ℝ)/100000), ((-33909488511:ℝ)/500), ((-865660491:ℝ)/100), ((-3676866:ℝ)/5), ((-187092:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e) - ((-35227359690908095338507:ℝ)/12800000000000) - ((-2510690420974103107353:ℝ)/320000000000)*t| ≤ ((67454731680715793703:ℝ)/2560000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 12, ([((-35227359690908095338507:ℝ)/12800000000000), ((-2510690420974103107353:ℝ)/320000000000), ((-64880378803868213493:ℝ)/6400000000), ((-1254327714401429331:ℝ)/160000000), ((-32261562722701611:ℝ)/8000000), ((-1449169027578153:ℝ)/1000000), ((-37127174887593:ℝ)/100000), ((-33909488511:ℝ)/500), ((-865660491:ℝ)/100), ((-3676866:ℝ)/5), ((-187092:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((154823357358016512:ℝ)/48828125) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((122570082855806967:ℝ)/16000000000) - ((14162665351154949:ℝ)/800000000)*t| ≤ ((186430602969793:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((22:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-6288:ℝ), (81024:ℝ), (-238720:ℝ), (246784:ℝ), (-98304:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m13' : |centralNum13_01 q| ≤ ((97984214598188193792:ℝ)/48828125) := by
    rw [centralNum13_01_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((22:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-7368:ℝ), (59208:ℝ), (-155734:ℝ), (205300:ℝ), (-60000:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m23' : |centralNum23_01 q| ≤ ((2697632131891243008:ℝ)/1953125) := by
    rw [centralNum23_01_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece16_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece16_E11 h0) m23'
  have c5 := scaled_affine (X := ((-15057506059:ℝ)/62500000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-113176438463349:ℝ)/80000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((-35227359690908095338507:ℝ)/12800000000000) + ((122570082855806967:ℝ)/16000000000)*((-15057506059:ℝ)/62500000000000) - ((-146388986721594643:ℝ)/100000000000)) (β := ((-9106150221189:ℝ)/4000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((-2510690420974103107353:ℝ)/320000000000) - 3*((-35227359690908095338507:ℝ)/12800000000000)) + ((14162665351154949:ℝ)/800000000)*((-15057506059:ℝ)/62500000000000) - ((-113687082922384783:ℝ)/50000000000)) ht
  have hW : pieceW q pieceX_16 0 1 = centralNum11_01 q + 8*(Real.exp (-(3*((87:ℝ)/20)))*Real.exp (-3*t))*centralNum12_01 q + 18*Real.exp (-8*q)*centralNum13_01 q + 72*Real.exp (-11*q)*centralNum23_01 q + 8*q^7*(2*q-3)^2*((-15057506059:ℝ)/62500000000000) + (0:ℝ) := by
    rw [pieceW_01, pieceX_16, sym4_01, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((65669816418591572847181609817315773014183353463154995189241755736047849:ℝ)/36052445354723786105633212257272406657218984431601556098489500000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-113176438463349:ℝ)/80000000) + ((-9106150221189:ℝ)/4000000)*t) + (8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((-35227359690908095338507:ℝ)/12800000000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((-2510690420974103107353:ℝ)/320000000000) - 3*((-35227359690908095338507:ℝ)/12800000000000))*t) + (((122570082855806967:ℝ)/16000000000) + ((14162665351154949:ℝ)/800000000)*t)*((-15057506059:ℝ)/62500000000000) - (((-146388986721594643:ℝ)/100000000000) + t * ((-113687082922384783:ℝ)/50000000000)) = (((-113176438463349:ℝ)/80000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((-35227359690908095338507:ℝ)/12800000000000) + ((122570082855806967:ℝ)/16000000000)*((-15057506059:ℝ)/62500000000000) - ((-146388986721594643:ℝ)/100000000000)) + t*(((-9106150221189:ℝ)/4000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((-2510690420974103107353:ℝ)/320000000000) - 3*((-35227359690908095338507:ℝ)/12800000000000)) + ((14162665351154949:ℝ)/800000000)*((-15057506059:ℝ)/62500000000000) - ((-113687082922384783:ℝ)/50000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece16_e02 {q : ℝ} (h0 : ((43:ℝ)/10) ≤ q) (h1 : q ≤ ((22:ℝ)/5)) :
    |pieceW q pieceX_16 0 2 - (((-153761552051803023:ℝ)/10000000000000) + (q - ((87:ℝ)/20)) * ((-262199287045914349:ℝ)/5000000000000))| ≤ ((246633584566337933:ℝ)/100000000000000) := by
  set t := q - ((87:ℝ)/20) with htd
  have hq : q = ((87:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece16_L3 piece16_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((87:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_02 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_02; ring
  have h12 : centralNum12_02 q = ∑ e ∈ Finset.range 13, ([((-2532195816354422097257241:ℝ)/2048000000000000), ((-773065610011557041623641:ℝ)/102400000000000), ((-79719338962583938066149:ℝ)/5120000000000), ((-883181451282009745743:ℝ)/51200000000), ((-3869403462974093193:ℝ)/320000000), ((-1852985317990867173:ℝ)/320000000), ((-31482451967869413:ℝ)/16000000), ((-385323501189267:ℝ)/800000), ((-1355177080629:ℝ)/16000), ((-8374344777:ℝ)/800), ((-172998369:ℝ)/200), ((-429759:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_02; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-2532195816354422097257241:ℝ)/2048000000000000), ((-773065610011557041623641:ℝ)/102400000000000), ((-79719338962583938066149:ℝ)/5120000000000), ((-883181451282009745743:ℝ)/51200000000), ((-3869403462974093193:ℝ)/320000000), ((-1852985317990867173:ℝ)/320000000), ((-31482451967869413:ℝ)/16000000), ((-385323501189267:ℝ)/800000), ((-1355177080629:ℝ)/16000), ((-8374344777:ℝ)/800), ((-172998369:ℝ)/200), ((-429759:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((-2532195816354422097257241:ℝ)/2048000000000000), ((-773065610011557041623641:ℝ)/102400000000000), ((-79719338962583938066149:ℝ)/5120000000000), ((-883181451282009745743:ℝ)/51200000000), ((-3869403462974093193:ℝ)/320000000), ((-1852985317990867173:ℝ)/320000000), ((-31482451967869413:ℝ)/16000000), ((-385323501189267:ℝ)/800000), ((-1355177080629:ℝ)/16000), ((-8374344777:ℝ)/800), ((-172998369:ℝ)/200), ((-429759:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((-2532195816354422097257241:ℝ)/2048000000000000), ((-773065610011557041623641:ℝ)/102400000000000), ((-79719338962583938066149:ℝ)/5120000000000), ((-883181451282009745743:ℝ)/51200000000), ((-3869403462974093193:ℝ)/320000000), ((-1852985317990867173:ℝ)/320000000), ((-31482451967869413:ℝ)/16000000), ((-385323501189267:ℝ)/800000), ((-1355177080629:ℝ)/16000), ((-8374344777:ℝ)/800), ((-172998369:ℝ)/200), ((-429759:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e) - ((-2532195816354422097257241:ℝ)/2048000000000000) - ((-773065610011557041623641:ℝ)/102400000000000)*t| ≤ ((42146896035258900464967:ℝ)/1024000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((-2532195816354422097257241:ℝ)/2048000000000000), ((-773065610011557041623641:ℝ)/102400000000000), ((-79719338962583938066149:ℝ)/5120000000000), ((-883181451282009745743:ℝ)/51200000000), ((-3869403462974093193:ℝ)/320000000), ((-1852985317990867173:ℝ)/320000000), ((-31482451967869413:ℝ)/16000000), ((-385323501189267:ℝ)/800000), ((-1355177080629:ℝ)/16000), ((-8374344777:ℝ)/800), ((-172998369:ℝ)/200), ((-429759:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((404066469482957952:ℝ)/244140625) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((122570082855806967:ℝ)/16000000000) - ((14162665351154949:ℝ)/800000000)*t| ≤ ((186430602969793:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((22:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82080:ℝ), (-967680:ℝ), (3257600:ℝ), (-4474880:ℝ), (2908160:ℝ), (-786432:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_02 q| ≤ ((22102781425423068147712:ℝ)/244140625) := by
    rw [centralNum13_02_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((22:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (87660:ℝ), (-702180:ℝ), ((7421435:ℝ)/4), ((-10854125:ℝ)/4), ((2828125:ℝ)/2), (-187500:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_02 q| ≤ ((13837058313024090496:ℝ)/390625) := by
    rw [centralNum23_02_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece16_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece16_E11 h0) m23'
  have c5 := scaled_affine (X := ((384514158423:ℝ)/500000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((-2532195816354422097257241:ℝ)/2048000000000000) + ((122570082855806967:ℝ)/16000000000)*((384514158423:ℝ)/500000000000000) - ((-153761552051803023:ℝ)/10000000000000)) (β := (0:ℝ) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((-773065610011557041623641:ℝ)/102400000000000) - 3*((-2532195816354422097257241:ℝ)/2048000000000000)) + ((14162665351154949:ℝ)/800000000)*((384514158423:ℝ)/500000000000000) - ((-262199287045914349:ℝ)/5000000000000)) ht
  have hW : pieceW q pieceX_16 0 2 = centralNum11_02 q + 8*(Real.exp (-(3*((87:ℝ)/20)))*Real.exp (-3*t))*centralNum12_02 q + 18*Real.exp (-8*q)*centralNum13_02 q + 72*Real.exp (-11*q)*centralNum23_02 q + 8*q^7*(2*q-3)^2*((384514158423:ℝ)/500000000000000) + (0:ℝ) := by
    rw [pieceW_02, pieceX_16, sym4_02, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((3409944319646112899997304077091854103518281376220554783459777581820947:ℝ)/288419562837790288845065698058179253257751875452812448787916000000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((-2532195816354422097257241:ℝ)/2048000000000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((-773065610011557041623641:ℝ)/102400000000000) - 3*((-2532195816354422097257241:ℝ)/2048000000000000))*t) + (((122570082855806967:ℝ)/16000000000) + ((14162665351154949:ℝ)/800000000)*t)*((384514158423:ℝ)/500000000000000) - (((-153761552051803023:ℝ)/10000000000000) + t * ((-262199287045914349:ℝ)/5000000000000)) = ((0:ℝ) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((-2532195816354422097257241:ℝ)/2048000000000000) + ((122570082855806967:ℝ)/16000000000)*((384514158423:ℝ)/500000000000000) - ((-153761552051803023:ℝ)/10000000000000)) + t*((0:ℝ) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((-773065610011557041623641:ℝ)/102400000000000) - 3*((-2532195816354422097257241:ℝ)/2048000000000000)) + ((14162665351154949:ℝ)/800000000)*((384514158423:ℝ)/500000000000000) - ((-262199287045914349:ℝ)/5000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece16_e03 {q : ℝ} (h0 : ((43:ℝ)/10) ≤ q) (h1 : q ≤ ((22:ℝ)/5)) :
    |pieceW q pieceX_16 0 3 - (((478204482056410431:ℝ)/5000000000000) + (q - ((87:ℝ)/20)) * ((-498747630188075017:ℝ)/5000000000000))| ≤ ((141656869163727507:ℝ)/20000000000000) := by
  set t := q - ((87:ℝ)/20) with htd
  have hq : q = ((87:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece16_L3 piece16_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((87:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_03 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_03; ring
  have h12 : centralNum12_03 q = ∑ e ∈ Finset.range 14, ([((4145716918194227704560268557:ℝ)/573440000000000000), ((141547509285059818591364547:ℝ)/7168000000000000), ((558738994665501493256709:ℝ)/25600000000000), ((392926926391360314735357:ℝ)/35840000000000), ((4393381581042988743:ℝ)/102400000000), ((-319272863487458989419:ℝ)/89600000000), ((-2863981124062425189:ℝ)/1120000000), ((-114976398121148079:ℝ)/112000000), ((-6133701380299641:ℝ)/22400000), ((-25294280859:ℝ)/500), ((-22559341347:ℝ)/3500), ((-108654777:ℝ)/200), ((-3830409:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_03; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((4145716918194227704560268557:ℝ)/573440000000000000), ((141547509285059818591364547:ℝ)/7168000000000000), ((558738994665501493256709:ℝ)/25600000000000), ((392926926391360314735357:ℝ)/35840000000000), ((4393381581042988743:ℝ)/102400000000), ((-319272863487458989419:ℝ)/89600000000), ((-2863981124062425189:ℝ)/1120000000), ((-114976398121148079:ℝ)/112000000), ((-6133701380299641:ℝ)/22400000), ((-25294280859:ℝ)/500), ((-22559341347:ℝ)/3500), ((-108654777:ℝ)/200), ((-3830409:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((4145716918194227704560268557:ℝ)/573440000000000000), ((141547509285059818591364547:ℝ)/7168000000000000), ((558738994665501493256709:ℝ)/25600000000000), ((392926926391360314735357:ℝ)/35840000000000), ((4393381581042988743:ℝ)/102400000000), ((-319272863487458989419:ℝ)/89600000000), ((-2863981124062425189:ℝ)/1120000000), ((-114976398121148079:ℝ)/112000000), ((-6133701380299641:ℝ)/22400000), ((-25294280859:ℝ)/500), ((-22559341347:ℝ)/3500), ((-108654777:ℝ)/200), ((-3830409:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((4145716918194227704560268557:ℝ)/573440000000000000), ((141547509285059818591364547:ℝ)/7168000000000000), ((558738994665501493256709:ℝ)/25600000000000), ((392926926391360314735357:ℝ)/35840000000000), ((4393381581042988743:ℝ)/102400000000), ((-319272863487458989419:ℝ)/89600000000), ((-2863981124062425189:ℝ)/1120000000), ((-114976398121148079:ℝ)/112000000), ((-6133701380299641:ℝ)/22400000), ((-25294280859:ℝ)/500), ((-22559341347:ℝ)/3500), ((-108654777:ℝ)/200), ((-3830409:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((4145716918194227704560268557:ℝ)/573440000000000000) - ((141547509285059818591364547:ℝ)/7168000000000000)*t| ≤ ((32076053246078423702312103:ℝ)/573440000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((4145716918194227704560268557:ℝ)/573440000000000000), ((141547509285059818591364547:ℝ)/7168000000000000), ((558738994665501493256709:ℝ)/25600000000000), ((392926926391360314735357:ℝ)/35840000000000), ((4393381581042988743:ℝ)/102400000000), ((-319272863487458989419:ℝ)/89600000000), ((-2863981124062425189:ℝ)/1120000000), ((-114976398121148079:ℝ)/112000000), ((-6133701380299641:ℝ)/22400000), ((-25294280859:ℝ)/500), ((-22559341347:ℝ)/3500), ((-108654777:ℝ)/200), ((-3830409:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((74124734509071021916063107:ℝ)/8960000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((122570082855806967:ℝ)/16000000000) - ((14162665351154949:ℝ)/800000000)*t| ≤ ((186430602969793:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((22:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-812160:ℝ), (8985600:ℝ), (-32225280:ℝ), (52019200:ℝ), ((-305233920:ℝ)/7), ((135528448:ℝ)/7), ((-25165824:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_03 q| ≤ ((21677223306171637759295488:ℝ)/8544921875) := by
    rw [centralNum13_03_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((22:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-833220:ℝ), (6469740:ℝ), ((-68603955:ℝ)/4), ((104396875:ℝ)/4), ((-1001334375:ℝ)/56), ((125828125:ℝ)/28), ((-2343750:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_03 q| ≤ ((1669854177238434256256:ℝ)/2734375) := by
    rw [centralNum23_03_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece16_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece16_E11 h0) m23'
  have c5 := scaled_affine (X := ((-374809743411:ℝ)/100000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((4145716918194227704560268557:ℝ)/573440000000000000) + ((122570082855806967:ℝ)/16000000000)*((-374809743411:ℝ)/100000000000000) - ((478204482056410431:ℝ)/5000000000000)) (β := (0:ℝ) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((141547509285059818591364547:ℝ)/7168000000000000) - 3*((4145716918194227704560268557:ℝ)/573440000000000000)) + ((14162665351154949:ℝ)/800000000)*((-374809743411:ℝ)/100000000000000) - ((-498747630188075017:ℝ)/5000000000000)) ht
  have hW : pieceW q pieceX_16 0 3 = centralNum11_03 q + 8*(Real.exp (-(3*((87:ℝ)/20)))*Real.exp (-3*t))*centralNum12_03 q + 18*Real.exp (-8*q)*centralNum13_03 q + 72*Real.exp (-11*q)*centralNum23_03 q + 8*q^7*(2*q-3)^2*((-374809743411:ℝ)/100000000000000) + (0:ℝ) := by
    rw [pieceW_03, pieceX_16, sym4_03, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((4348552682052672026903084509622906831626375896947409420439070822972257:ℝ)/201893693986453202191545988640725477280426312816968714151541200000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((4145716918194227704560268557:ℝ)/573440000000000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((141547509285059818591364547:ℝ)/7168000000000000) - 3*((4145716918194227704560268557:ℝ)/573440000000000000))*t) + (((122570082855806967:ℝ)/16000000000) + ((14162665351154949:ℝ)/800000000)*t)*((-374809743411:ℝ)/100000000000000) - (((478204482056410431:ℝ)/5000000000000) + t * ((-498747630188075017:ℝ)/5000000000000)) = ((0:ℝ) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((4145716918194227704560268557:ℝ)/573440000000000000) + ((122570082855806967:ℝ)/16000000000)*((-374809743411:ℝ)/100000000000000) - ((478204482056410431:ℝ)/5000000000000)) + t*((0:ℝ) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((141547509285059818591364547:ℝ)/7168000000000000) - 3*((4145716918194227704560268557:ℝ)/573440000000000000)) + ((14162665351154949:ℝ)/800000000)*((-374809743411:ℝ)/100000000000000) - ((-498747630188075017:ℝ)/5000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece16_e11 {q : ℝ} (h0 : ((43:ℝ)/10) ≤ q) (h1 : q ≤ ((22:ℝ)/5)) :
    |pieceW q pieceX_16 1 1 - (((688122750373900493:ℝ)/100000000000) + (q - ((87:ℝ)/20)) * ((14279829631602213:ℝ)/1000000000))| ≤ ((361766913029551263:ℝ)/10000000000000) := by
  set t := q - ((87:ℝ)/20) with htd
  have hq : q = ((87:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece16_L3 piece16_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((87:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_11 q = ∑ e ∈ Finset.range 10, ([((3365372946030849:ℝ)/500000000), ((5629709157189363:ℝ)/400000000), ((66436586951499:ℝ)/5000000), ((1857881267613:ℝ)/250000), ((33886178361:ℝ)/12500), ((834761781:ℝ)/1250), ((13860084:ℝ)/125), ((298512:ℝ)/25), ((3776:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_11; ring
  have h12 : centralNum12_11 q = ∑ e ∈ Finset.range 13, ([((651972543779790821832093:ℝ)/512000000000000), ((-38505879093024369376227:ℝ)/25600000000000), ((-12050021471563508006583:ℝ)/1280000000000), ((-179404721658256265541:ℝ)/12800000000), ((-911829443035876551:ℝ)/80000000), ((-478960752345601671:ℝ)/80000000), ((-8681659686455511:ℝ)/4000000), ((-111568759607889:ℝ)/200000), ((-407858116823:ℝ)/4000), ((-7805433817:ℝ)/600), ((-55212363:ℝ)/50), ((-280746:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_11; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((3365372946030849:ℝ)/500000000), ((5629709157189363:ℝ)/400000000), ((66436586951499:ℝ)/5000000), ((1857881267613:ℝ)/250000), ((33886178361:ℝ)/12500), ((834761781:ℝ)/1250), ((13860084:ℝ)/125), ((298512:ℝ)/25), ((3776:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((651972543779790821832093:ℝ)/512000000000000), ((-38505879093024369376227:ℝ)/25600000000000), ((-12050021471563508006583:ℝ)/1280000000000), ((-179404721658256265541:ℝ)/12800000000), ((-911829443035876551:ℝ)/80000000), ((-478960752345601671:ℝ)/80000000), ((-8681659686455511:ℝ)/4000000), ((-111568759607889:ℝ)/200000), ((-407858116823:ℝ)/4000), ((-7805433817:ℝ)/600), ((-55212363:ℝ)/50), ((-280746:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((651972543779790821832093:ℝ)/512000000000000), ((-38505879093024369376227:ℝ)/25600000000000), ((-12050021471563508006583:ℝ)/1280000000000), ((-179404721658256265541:ℝ)/12800000000), ((-911829443035876551:ℝ)/80000000), ((-478960752345601671:ℝ)/80000000), ((-8681659686455511:ℝ)/4000000), ((-111568759607889:ℝ)/200000), ((-407858116823:ℝ)/4000), ((-7805433817:ℝ)/600), ((-55212363:ℝ)/50), ((-280746:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((3365372946030849:ℝ)/500000000), ((5629709157189363:ℝ)/400000000), ((66436586951499:ℝ)/5000000), ((1857881267613:ℝ)/250000), ((33886178361:ℝ)/12500), ((834761781:ℝ)/1250), ((13860084:ℝ)/125), ((298512:ℝ)/25), ((3776:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((3365372946030849:ℝ)/500000000) + ((5629709157189363:ℝ)/400000000)*t)| ≤ ((819945303145207:ℝ)/24000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((651972543779790821832093:ℝ)/512000000000000), ((-38505879093024369376227:ℝ)/25600000000000), ((-12050021471563508006583:ℝ)/1280000000000), ((-179404721658256265541:ℝ)/12800000000), ((-911829443035876551:ℝ)/80000000), ((-478960752345601671:ℝ)/80000000), ((-8681659686455511:ℝ)/4000000), ((-111568759607889:ℝ)/200000), ((-407858116823:ℝ)/4000), ((-7805433817:ℝ)/600), ((-55212363:ℝ)/50), ((-280746:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e) - ((651972543779790821832093:ℝ)/512000000000000) - ((-38505879093024369376227:ℝ)/25600000000000)*t| ≤ ((19476740651385244079767:ℝ)/768000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((651972543779790821832093:ℝ)/512000000000000), ((-38505879093024369376227:ℝ)/25600000000000), ((-12050021471563508006583:ℝ)/1280000000000), ((-179404721658256265541:ℝ)/12800000000), ((-911829443035876551:ℝ)/80000000), ((-478960752345601671:ℝ)/80000000), ((-8681659686455511:ℝ)/4000000), ((-111568759607889:ℝ)/200000), ((-407858116823:ℝ)/4000), ((-7805433817:ℝ)/600), ((-55212363:ℝ)/50), ((-280746:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((1055194374960608030892247:ℝ)/768000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((122570082855806967:ℝ)/16000000000) - ((14162665351154949:ℝ)/800000000)*t| ≤ ((186430602969793:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((22:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-3444:ℝ), (162624:ℝ), (-1531216:ℝ), (4800960:ℝ), (-6350848:ℝ), ((12025856:ℝ)/3), (-1048576:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_11 q| ≤ ((90558723601702903199488:ℝ)/732421875) := by
    rw [centralNum13_11_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((22:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-4074:ℝ), (159906:ℝ), (-1104799:ℝ), (2801499:ℝ), (-3931375:ℝ), ((5896250:ℝ)/3), (-250000:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_11 q| ≤ ((288677677650444646784:ℝ)/5859375) := by
    rw [centralNum23_11_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece16_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece16_E11 h0) m23'
  have c5 := scaled_affine (X := ((167843206691:ℝ)/10000000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1))| ≤ ((18804649440150704767369216000000:ℝ)/60852466536744843271519588159730847) := by
    rw [abs_neg, tailWeight_1, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((22:ℝ)/5)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((22:ℝ)/5)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece16_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((4814744136400:ℝ)/531441)) ≤ ((22:ℝ)/5)^6*(8000*(2*((22:ℝ)/5)-3)^2*(1/((114504651573259954108771412367:ℝ)/2000000000))*((4814744136400:ℝ)/531441)) := by
          gcongr
      _ ≤ ((18804649440150704767369216000000:ℝ)/60852466536744843271519588159730847) := by norm_num
  have c7 := affine_round (α := ((3365372946030849:ℝ)/500000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((651972543779790821832093:ℝ)/512000000000000) + ((122570082855806967:ℝ)/16000000000)*((167843206691:ℝ)/10000000000000) - ((688122750373900493:ℝ)/100000000000)) (β := ((5629709157189363:ℝ)/400000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((-38505879093024369376227:ℝ)/25600000000000) - 3*((651972543779790821832093:ℝ)/512000000000000)) + ((14162665351154949:ℝ)/800000000)*((167843206691:ℝ)/10000000000000) - ((14279829631602213:ℝ)/1000000000)) ht
  have hW : pieceW q pieceX_16 1 1 = centralNum11_11 q + 8*(Real.exp (-(3*((87:ℝ)/20)))*Real.exp (-3*t))*centralNum12_11 q + 18*Real.exp (-8*q)*centralNum13_11 q + 72*Real.exp (-11*q)*centralNum23_11 q + 8*q^7*(2*q-3)^2*((167843206691:ℝ)/10000000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1)) := by
    rw [pieceW_11, pieceX_16, sym4_11, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((14618302691396916511191941087207358739095605491068507341629555251507599:ℝ)/5768391256755805776901313961163585065155037509056248975758320000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((3365372946030849:ℝ)/500000000) + ((5629709157189363:ℝ)/400000000)*t) + (8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((651972543779790821832093:ℝ)/512000000000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((-38505879093024369376227:ℝ)/25600000000000) - 3*((651972543779790821832093:ℝ)/512000000000000))*t) + (((122570082855806967:ℝ)/16000000000) + ((14162665351154949:ℝ)/800000000)*t)*((167843206691:ℝ)/10000000000000) - (((688122750373900493:ℝ)/100000000000) + t * ((14279829631602213:ℝ)/1000000000)) = (((3365372946030849:ℝ)/500000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((651972543779790821832093:ℝ)/512000000000000) + ((122570082855806967:ℝ)/16000000000)*((167843206691:ℝ)/10000000000000) - ((688122750373900493:ℝ)/100000000000)) + t*(((5629709157189363:ℝ)/400000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((-38505879093024369376227:ℝ)/25600000000000) - 3*((651972543779790821832093:ℝ)/512000000000000)) + ((14162665351154949:ℝ)/800000000)*((167843206691:ℝ)/10000000000000) - ((14279829631602213:ℝ)/1000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece16_e12 {q : ℝ} (h0 : ((43:ℝ)/10) ≤ q) (h1 : q ≤ ((22:ℝ)/5)) :
    |pieceW q pieceX_16 1 2 - (((-83648329528670721:ℝ)/125000000000) + (q - ((87:ℝ)/20)) * ((-138793726958519997:ℝ)/100000000000))| ≤ ((208144499941291797:ℝ)/10000000000000) := by
  set t := q - ((87:ℝ)/20) with htd
  have hq : q = ((87:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece16_L3 piece16_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((87:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_12 q = ∑ e ∈ Finset.range 9, ([((-519050562607773:ℝ)/640000000), ((-9165960731673:ℝ)/8000000), ((-235976525559:ℝ)/400000), ((-1878709059:ℝ)/20000), ((12420729:ℝ)/400), ((884529:ℝ)/50), ((17802:ℝ)/5), (344:ℝ), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_12; ring
  have h12 : centralNum12_12 q = ∑ e ∈ Finset.range 14, ([((1347045474759571849790341359:ℝ)/81920000000000000), ((55495447353627378300268209:ℝ)/1024000000000000), ((1924862597866288324249641:ℝ)/25600000000000), ((291506766436540131461919:ℝ)/5120000000000), ((2473650424132030735227:ℝ)/102400000000), ((50587193690202751047:ℝ)/12800000000), ((-254763923662388583:ℝ)/160000000), ((-20499147439456453:ℝ)/16000000), ((-4187441060877241:ℝ)/9600000), ((-11526227194:ℝ)/125), ((-6422571789:ℝ)/500), ((-231154533:ℝ)/200), ((-1224963:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_12; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-519050562607773:ℝ)/640000000), ((-9165960731673:ℝ)/8000000), ((-235976525559:ℝ)/400000), ((-1878709059:ℝ)/20000), ((12420729:ℝ)/400), ((884529:ℝ)/50), ((17802:ℝ)/5), (344:ℝ), ((40:ℝ)/3)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((1347045474759571849790341359:ℝ)/81920000000000000), ((55495447353627378300268209:ℝ)/1024000000000000), ((1924862597866288324249641:ℝ)/25600000000000), ((291506766436540131461919:ℝ)/5120000000000), ((2473650424132030735227:ℝ)/102400000000), ((50587193690202751047:ℝ)/12800000000), ((-254763923662388583:ℝ)/160000000), ((-20499147439456453:ℝ)/16000000), ((-4187441060877241:ℝ)/9600000), ((-11526227194:ℝ)/125), ((-6422571789:ℝ)/500), ((-231154533:ℝ)/200), ((-1224963:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((1347045474759571849790341359:ℝ)/81920000000000000), ((55495447353627378300268209:ℝ)/1024000000000000), ((1924862597866288324249641:ℝ)/25600000000000), ((291506766436540131461919:ℝ)/5120000000000), ((2473650424132030735227:ℝ)/102400000000), ((50587193690202751047:ℝ)/12800000000), ((-254763923662388583:ℝ)/160000000), ((-20499147439456453:ℝ)/16000000), ((-4187441060877241:ℝ)/9600000), ((-11526227194:ℝ)/125), ((-6422571789:ℝ)/500), ((-231154533:ℝ)/200), ((-1224963:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((-519050562607773:ℝ)/640000000), ((-9165960731673:ℝ)/8000000), ((-235976525559:ℝ)/400000), ((-1878709059:ℝ)/20000), ((12420729:ℝ)/400), ((884529:ℝ)/50), ((17802:ℝ)/5), (344:ℝ), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((-519050562607773:ℝ)/640000000) + ((-9165960731673:ℝ)/8000000)*t)| ≤ ((2854646158963:ℝ)/1920000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((1347045474759571849790341359:ℝ)/81920000000000000), ((55495447353627378300268209:ℝ)/1024000000000000), ((1924862597866288324249641:ℝ)/25600000000000), ((291506766436540131461919:ℝ)/5120000000000), ((2473650424132030735227:ℝ)/102400000000), ((50587193690202751047:ℝ)/12800000000), ((-254763923662388583:ℝ)/160000000), ((-20499147439456453:ℝ)/16000000), ((-4187441060877241:ℝ)/9600000), ((-11526227194:ℝ)/125), ((-6422571789:ℝ)/500), ((-231154533:ℝ)/200), ((-1224963:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e) - ((1347045474759571849790341359:ℝ)/81920000000000000) - ((55495447353627378300268209:ℝ)/1024000000000000)*t| ≤ ((47983157591490230866455547:ℝ)/245760000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((1347045474759571849790341359:ℝ)/81920000000000000), ((55495447353627378300268209:ℝ)/1024000000000000), ((1924862597866288324249641:ℝ)/25600000000000), ((291506766436540131461919:ℝ)/5120000000000), ((2473650424132030735227:ℝ)/102400000000), ((50587193690202751047:ℝ)/12800000000), ((-254763923662388583:ℝ)/160000000), ((-20499147439456453:ℝ)/16000000), ((-4187441060877241:ℝ)/9600000), ((-11526227194:ℝ)/125), ((-6422571789:ℝ)/500), ((-231154533:ℝ)/200), ((-1224963:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((1188766237528433579960174533:ℝ)/61440000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((122570082855806967:ℝ)/16000000000) - ((14162665351154949:ℝ)/800000000)*t| ≤ ((186430602969793:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((22:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (122790:ℝ), (-3586680:ℝ), (28529720:ℝ), (-90761600:ℝ), (137804800:ℝ), ((-332136448:ℝ)/3), ((141819904:ℝ)/3), (-8388608:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_12 q| ≤ ((7559180670142486078505856:ℝ)/1220703125) := by
    rw [centralNum13_12_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((22:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (132555:ℝ), (-3252375:ℝ), ((39743695:ℝ)/2), ((-197111615:ℝ)/4), ((281947375:ℝ)/4), ((-1100234375:ℝ)/24), ((131828125:ℝ)/12), (-781250:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_12 q| ≤ ((598866428713791089984:ℝ)/390625) := by
    rw [centralNum23_12_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece16_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece16_E11 h0) m23'
  have c5 := scaled_affine (X := ((-184069901641:ℝ)/10000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-519050562607773:ℝ)/640000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((1347045474759571849790341359:ℝ)/81920000000000000) + ((122570082855806967:ℝ)/16000000000)*((-184069901641:ℝ)/10000000000000) - ((-83648329528670721:ℝ)/125000000000)) (β := ((-9165960731673:ℝ)/8000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((55495447353627378300268209:ℝ)/1024000000000000) - 3*((1347045474759571849790341359:ℝ)/81920000000000000)) + ((14162665351154949:ℝ)/800000000)*((-184069901641:ℝ)/10000000000000) - ((-138793726958519997:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_16 1 2 = centralNum11_12 q + 8*(Real.exp (-(3*((87:ℝ)/20)))*Real.exp (-3*t))*centralNum12_12 q + 18*Real.exp (-8*q)*centralNum13_12 q + 72*Real.exp (-11*q)*centralNum23_12 q + 8*q^7*(2*q-3)^2*((-184069901641:ℝ)/10000000000000) + (0:ℝ) := by
    rw [pieceW_12, pieceX_16, sym4_12, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((1962131302434455656002006085684938863769590879499181539294097478203149:ℝ)/5768391256755805776901313961163585065155037509056248975758320000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-519050562607773:ℝ)/640000000) + ((-9165960731673:ℝ)/8000000)*t) + (8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((1347045474759571849790341359:ℝ)/81920000000000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((55495447353627378300268209:ℝ)/1024000000000000) - 3*((1347045474759571849790341359:ℝ)/81920000000000000))*t) + (((122570082855806967:ℝ)/16000000000) + ((14162665351154949:ℝ)/800000000)*t)*((-184069901641:ℝ)/10000000000000) - (((-83648329528670721:ℝ)/125000000000) + t * ((-138793726958519997:ℝ)/100000000000)) = (((-519050562607773:ℝ)/640000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((1347045474759571849790341359:ℝ)/81920000000000000) + ((122570082855806967:ℝ)/16000000000)*((-184069901641:ℝ)/10000000000000) - ((-83648329528670721:ℝ)/125000000000)) + t*(((-9165960731673:ℝ)/8000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((55495447353627378300268209:ℝ)/1024000000000000) - 3*((1347045474759571849790341359:ℝ)/81920000000000000)) + ((14162665351154949:ℝ)/800000000)*((-184069901641:ℝ)/10000000000000) - ((-138793726958519997:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece16_e13 {q : ℝ} (h0 : ((43:ℝ)/10) ≤ q) (h1 : q ≤ ((22:ℝ)/5)) :
    |pieceW q pieceX_16 1 3 - (((-167269002310683869:ℝ)/1000000000000) + (q - ((87:ℝ)/20)) * ((9658935593545031:ℝ)/6250000000))| ≤ ((67876121009053133:ℝ)/2500000000000) := by
  set t := q - ((87:ℝ)/20) with htd
  have hq : q = ((87:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece16_L3 piece16_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((87:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_13 q = ∑ e ∈ Finset.range 7, ([((-1300878603027:ℝ)/3200000), ((-44857882863:ℝ)/80000), ((-515607849:ℝ)/1600), ((-1975509:ℝ)/20), ((-68121:ℝ)/4), (-1566:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_13; ring
  have h12 : centralNum12_13 q = ∑ e ∈ Finset.range 15, ([((-601711028899673813451037020843:ℝ)/22937600000000000000), ((-56218302464574116242589268141:ℝ)/1146880000000000000), ((-179969010350315336346407733:ℝ)/14336000000000000), ((66939383249809688378689713:ℝ)/1433600000000000), ((9170192982075013512681147:ℝ)/143360000000000), ((299507635333269963240777:ℝ)/7168000000000), ((2937273976489232868987:ℝ)/179200000000), ((17231031898143897987:ℝ)/4480000000), ((342586434498952011:ℝ)/896000000), ((-3026850218899083:ℝ)/44800000), ((-576167039919:ℝ)/17500), ((-340139077767:ℝ)/56000), ((-3550278843:ℝ)/5600), ((-10329201:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_13; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-1300878603027:ℝ)/3200000), ((-44857882863:ℝ)/80000), ((-515607849:ℝ)/1600), ((-1975509:ℝ)/20), ((-68121:ℝ)/4), (-1566:ℝ), (-60:ℝ)] : List ℝ).getD e 0) 5 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-601711028899673813451037020843:ℝ)/22937600000000000000), ((-56218302464574116242589268141:ℝ)/1146880000000000000), ((-179969010350315336346407733:ℝ)/14336000000000000), ((66939383249809688378689713:ℝ)/1433600000000000), ((9170192982075013512681147:ℝ)/143360000000000), ((299507635333269963240777:ℝ)/7168000000000), ((2937273976489232868987:ℝ)/179200000000), ((17231031898143897987:ℝ)/4480000000), ((342586434498952011:ℝ)/896000000), ((-3026850218899083:ℝ)/44800000), ((-576167039919:ℝ)/17500), ((-340139077767:ℝ)/56000), ((-3550278843:ℝ)/5600), ((-10329201:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-601711028899673813451037020843:ℝ)/22937600000000000000), ((-56218302464574116242589268141:ℝ)/1146880000000000000), ((-179969010350315336346407733:ℝ)/14336000000000000), ((66939383249809688378689713:ℝ)/1433600000000000), ((9170192982075013512681147:ℝ)/143360000000000), ((299507635333269963240777:ℝ)/7168000000000), ((2937273976489232868987:ℝ)/179200000000), ((17231031898143897987:ℝ)/4480000000), ((342586434498952011:ℝ)/896000000), ((-3026850218899083:ℝ)/44800000), ((-576167039919:ℝ)/17500), ((-340139077767:ℝ)/56000), ((-3550278843:ℝ)/5600), ((-10329201:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 7, ([((-1300878603027:ℝ)/3200000), ((-44857882863:ℝ)/80000), ((-515607849:ℝ)/1600), ((-1975509:ℝ)/20), ((-68121:ℝ)/4), (-1566:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e) - (((-1300878603027:ℝ)/3200000) + ((-44857882863:ℝ)/80000)*t)| ≤ ((2617891599:ℝ)/3200000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-601711028899673813451037020843:ℝ)/22937600000000000000), ((-56218302464574116242589268141:ℝ)/1146880000000000000), ((-179969010350315336346407733:ℝ)/14336000000000000), ((66939383249809688378689713:ℝ)/1433600000000000), ((9170192982075013512681147:ℝ)/143360000000000), ((299507635333269963240777:ℝ)/7168000000000), ((2937273976489232868987:ℝ)/179200000000), ((17231031898143897987:ℝ)/4480000000), ((342586434498952011:ℝ)/896000000), ((-3026850218899083:ℝ)/44800000), ((-576167039919:ℝ)/17500), ((-340139077767:ℝ)/56000), ((-3550278843:ℝ)/5600), ((-10329201:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((-601711028899673813451037020843:ℝ)/22937600000000000000) - ((-56218302464574116242589268141:ℝ)/1146880000000000000)*t| ≤ ((86323045233605729459799963:ℝ)/2293760000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-601711028899673813451037020843:ℝ)/22937600000000000000), ((-56218302464574116242589268141:ℝ)/1146880000000000000), ((-179969010350315336346407733:ℝ)/14336000000000000), ((66939383249809688378689713:ℝ)/1433600000000000), ((9170192982075013512681147:ℝ)/143360000000000), ((299507635333269963240777:ℝ)/7168000000000), ((2937273976489232868987:ℝ)/179200000000), ((17231031898143897987:ℝ)/4480000000), ((342586434498952011:ℝ)/896000000), ((-3026850218899083:ℝ)/44800000), ((-576167039919:ℝ)/17500), ((-340139077767:ℝ)/56000), ((-3550278843:ℝ)/5600), ((-10329201:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((329396280908291993494112144307:ℝ)/11468800000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((122570082855806967:ℝ)/16000000000) - ((14162665351154949:ℝ)/800000000)*t| ≤ ((186430602969793:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((22:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2325540:ℝ), (52589280:ℝ), (-375655200:ℝ), (1192958720:ℝ), (-1965096960:ℝ), ((12857851904:ℝ)/7), ((-21171273728:ℝ)/21), ((914358272:ℝ)/3), ((-268435456:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_13 q| ≤ ((8156321009621129994464102144:ℝ)/42724609375) := by
    rw [centralNum13_13_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((22:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2399070:ℝ), (45666930:ℝ), (-251781675:ℝ), ((2452738385:ℝ)/4), ((-14104310625:ℝ)/16), ((74345740625:ℝ)/112), ((-74899765625:ℝ)/336), ((5161328125:ℝ)/168), ((-9765625:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_13 q| ≤ ((84859129531185339223872:ℝ)/2734375) := by
    rw [centralNum23_13_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece16_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece16_E11 h0) m23'
  have c5 := scaled_affine (X := ((901328149831:ℝ)/10000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-1300878603027:ℝ)/3200000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((-601711028899673813451037020843:ℝ)/22937600000000000000) + ((122570082855806967:ℝ)/16000000000)*((901328149831:ℝ)/10000000000000) - ((-167269002310683869:ℝ)/1000000000000)) (β := ((-44857882863:ℝ)/80000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((-56218302464574116242589268141:ℝ)/1146880000000000000) - 3*((-601711028899673813451037020843:ℝ)/22937600000000000000)) + ((14162665351154949:ℝ)/800000000)*((901328149831:ℝ)/10000000000000) - ((9658935593545031:ℝ)/6250000000)) ht
  have hW : pieceW q pieceX_16 1 3 = centralNum11_13 q + 8*(Real.exp (-(3*((87:ℝ)/20)))*Real.exp (-3*t))*centralNum12_13 q + 18*Real.exp (-8*q)*centralNum13_13 q + 72*Real.exp (-11*q)*centralNum23_13 q + 8*q^7*(2*q-3)^2*((901328149831:ℝ)/10000000000000) + (0:ℝ) := by
    rw [pieceW_13, pieceX_16, sym4_13, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((5294706227309099500595816876745554750809016425399725403653402557340797:ℝ)/20189369398645320219154598864072547728042631281696871415154120000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-1300878603027:ℝ)/3200000) + ((-44857882863:ℝ)/80000)*t) + (8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((-601711028899673813451037020843:ℝ)/22937600000000000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((-56218302464574116242589268141:ℝ)/1146880000000000000) - 3*((-601711028899673813451037020843:ℝ)/22937600000000000000))*t) + (((122570082855806967:ℝ)/16000000000) + ((14162665351154949:ℝ)/800000000)*t)*((901328149831:ℝ)/10000000000000) - (((-167269002310683869:ℝ)/1000000000000) + t * ((9658935593545031:ℝ)/6250000000)) = (((-1300878603027:ℝ)/3200000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((-601711028899673813451037020843:ℝ)/22937600000000000000) + ((122570082855806967:ℝ)/16000000000)*((901328149831:ℝ)/10000000000000) - ((-167269002310683869:ℝ)/1000000000000)) + t*(((-44857882863:ℝ)/80000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((-56218302464574116242589268141:ℝ)/1146880000000000000) - 3*((-601711028899673813451037020843:ℝ)/22937600000000000000)) + ((14162665351154949:ℝ)/800000000)*((901328149831:ℝ)/10000000000000) - ((9658935593545031:ℝ)/6250000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece16_e22 {q : ℝ} (h0 : ((43:ℝ)/10) ≤ q) (h1 : q ≤ ((22:ℝ)/5)) :
    |pieceW q pieceX_16 2 2 - (((337711526424263:ℝ)/62500000) + (q - ((87:ℝ)/20)) * ((149732671603349103:ℝ)/10000000000))| ≤ ((899292008164108873:ℝ)/10000000000000) := by
  set t := q - ((87:ℝ)/20) with htd
  have hq : q = ((87:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece16_L3 piece16_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((87:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_22 q = ∑ e ∈ Finset.range 10, ([((37614216985655139:ℝ)/6400000000), ((4153496386417083:ℝ)/320000000), ((51052626695439:ℝ)/4000000), ((1474903189053:ℝ)/200000), ((55412225397:ℝ)/20000), ((703709001:ℝ)/1000), ((3023611:ℝ)/25), ((203324:ℝ)/15), ((2692:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_22; ring
  have h12 : centralNum12_22 q = ∑ e ∈ Finset.range 15, ([((-767289255545751335496374641083:ℝ)/13107200000000000000), ((-86073750925326829351721692701:ℝ)/655360000000000000), ((-742012091905959888865731153:ℝ)/8192000000000000), ((20168011445224230690941673:ℝ)/819200000000000), ((6865481011127764910483547:ℝ)/81920000000000), ((269210802371876811728937:ℝ)/4096000000000), ((2932629706479889517707:ℝ)/102400000000), ((57634121570082918001:ℝ)/7680000000), ((1532909848689876593:ℝ)/1536000000), ((-3185571652137649:ℝ)/76800000), ((-3698266577187:ℝ)/80000), ((-305757687087:ℝ)/32000), ((-3360829563:ℝ)/3200), ((-10095921:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_22; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((37614216985655139:ℝ)/6400000000), ((4153496386417083:ℝ)/320000000), ((51052626695439:ℝ)/4000000), ((1474903189053:ℝ)/200000), ((55412225397:ℝ)/20000), ((703709001:ℝ)/1000), ((3023611:ℝ)/25), ((203324:ℝ)/15), ((2692:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-767289255545751335496374641083:ℝ)/13107200000000000000), ((-86073750925326829351721692701:ℝ)/655360000000000000), ((-742012091905959888865731153:ℝ)/8192000000000000), ((20168011445224230690941673:ℝ)/819200000000000), ((6865481011127764910483547:ℝ)/81920000000000), ((269210802371876811728937:ℝ)/4096000000000), ((2932629706479889517707:ℝ)/102400000000), ((57634121570082918001:ℝ)/7680000000), ((1532909848689876593:ℝ)/1536000000), ((-3185571652137649:ℝ)/76800000), ((-3698266577187:ℝ)/80000), ((-305757687087:ℝ)/32000), ((-3360829563:ℝ)/3200), ((-10095921:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-767289255545751335496374641083:ℝ)/13107200000000000000), ((-86073750925326829351721692701:ℝ)/655360000000000000), ((-742012091905959888865731153:ℝ)/8192000000000000), ((20168011445224230690941673:ℝ)/819200000000000), ((6865481011127764910483547:ℝ)/81920000000000), ((269210802371876811728937:ℝ)/4096000000000), ((2932629706479889517707:ℝ)/102400000000), ((57634121570082918001:ℝ)/7680000000), ((1532909848689876593:ℝ)/1536000000), ((-3185571652137649:ℝ)/76800000), ((-3698266577187:ℝ)/80000), ((-305757687087:ℝ)/32000), ((-3360829563:ℝ)/3200), ((-10095921:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((37614216985655139:ℝ)/6400000000), ((4153496386417083:ℝ)/320000000), ((51052626695439:ℝ)/4000000), ((1474903189053:ℝ)/200000), ((55412225397:ℝ)/20000), ((703709001:ℝ)/1000), ((3023611:ℝ)/25), ((203324:ℝ)/15), ((2692:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((37614216985655139:ℝ)/6400000000) + ((4153496386417083:ℝ)/320000000)*t)| ≤ ((315333545353811:ℝ)/9600000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-767289255545751335496374641083:ℝ)/13107200000000000000), ((-86073750925326829351721692701:ℝ)/655360000000000000), ((-742012091905959888865731153:ℝ)/8192000000000000), ((20168011445224230690941673:ℝ)/819200000000000), ((6865481011127764910483547:ℝ)/81920000000000), ((269210802371876811728937:ℝ)/4096000000000), ((2932629706479889517707:ℝ)/102400000000), ((57634121570082918001:ℝ)/7680000000), ((1532909848689876593:ℝ)/1536000000), ((-3185571652137649:ℝ)/76800000), ((-3698266577187:ℝ)/80000), ((-305757687087:ℝ)/32000), ((-3360829563:ℝ)/3200), ((-10095921:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e) - ((-767289255545751335496374641083:ℝ)/13107200000000000000) - ((-86073750925326829351721692701:ℝ)/655360000000000000)*t| ≤ ((904657507483436291716649713:ℝ)/3932160000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-767289255545751335496374641083:ℝ)/13107200000000000000), ((-86073750925326829351721692701:ℝ)/655360000000000000), ((-742012091905959888865731153:ℝ)/8192000000000000), ((20168011445224230690941673:ℝ)/819200000000000), ((6865481011127764910483547:ℝ)/81920000000000), ((269210802371876811728937:ℝ)/4096000000000), ((2932629706479889517707:ℝ)/102400000000), ((57634121570082918001:ℝ)/7680000000), ((1532909848689876593:ℝ)/1536000000), ((-3185571652137649:ℝ)/76800000), ((-3698266577187:ℝ)/80000), ((-305757687087:ℝ)/32000), ((-3360829563:ℝ)/3200), ((-10095921:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e)| ≤ ((1284567797244034428730727749241:ℝ)/19660800000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((122570082855806967:ℝ)/16000000000) - ((14162665351154949:ℝ)/800000000)*t| ≤ ((186430602969793:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((22:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82125:ℝ), (-6663750:ℝ), (115666200:ℝ), (-750437000:ℝ), (2277262000:ℝ), (-3656824320:ℝ), (3359621120:ℝ), (-1817706496:ℝ), ((1625292800:ℝ)/3), (-67108864:ℝ)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_22 q| ≤ ((6249401075513638166792729248:ℝ)/18310546875) := by
    rw [centralNum13_22_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((22:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((178425:ℝ)/2), ((-13176075:ℝ)/2), ((777815145:ℝ)/8), ((-3968389015:ℝ)/8), ((9393350195:ℝ)/8), ((-26366634375:ℝ)/16), ((77851609375:ℝ)/64), ((-25714921875:ℝ)/64), ((5236328125:ℝ)/96), ((-9765625:ℝ)/4)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_22 q| ≤ ((65764638776365884475648:ℝ)/1171875) := by
    rw [centralNum23_22_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece16_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece16_E11 h0) m23'
  have c5 := scaled_affine (X := ((695877282219:ℝ)/10000000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2))| ≤ ((10039173711143956009017671680000000:ℝ)/547672198830703589443676293437577623) := by
    rw [abs_neg, tailWeight_2, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((22:ℝ)/5)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((22:ℝ)/5)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece16_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((2570430941234500:ℝ)/4782969)) ≤ ((22:ℝ)/5)^6*(8000*(2*((22:ℝ)/5)-3)^2*(1/((114504651573259954108771412367:ℝ)/2000000000))*((2570430941234500:ℝ)/4782969)) := by
          gcongr
      _ ≤ ((10039173711143956009017671680000000:ℝ)/547672198830703589443676293437577623) := by norm_num
  have c7 := affine_round (α := ((37614216985655139:ℝ)/6400000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((-767289255545751335496374641083:ℝ)/13107200000000000000) + ((122570082855806967:ℝ)/16000000000)*((695877282219:ℝ)/10000000000000) - ((337711526424263:ℝ)/62500000)) (β := ((4153496386417083:ℝ)/320000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((-86073750925326829351721692701:ℝ)/655360000000000000) - 3*((-767289255545751335496374641083:ℝ)/13107200000000000000)) + ((14162665351154949:ℝ)/800000000)*((695877282219:ℝ)/10000000000000) - ((149732671603349103:ℝ)/10000000000)) ht
  have hW : pieceW q pieceX_16 2 2 = centralNum11_22 q + 8*(Real.exp (-(3*((87:ℝ)/20)))*Real.exp (-3*t))*centralNum12_22 q + 18*Real.exp (-8*q)*centralNum13_22 q + 72*Real.exp (-11*q)*centralNum23_22 q + 8*q^7*(2*q-3)^2*((695877282219:ℝ)/10000000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2)) := by
    rw [pieceW_22, pieceX_16, sym4_22, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((14371207335608573166265919812303244149123452557435546212734303949396079:ℝ)/2884195628377902888450656980581792532577518754528124487879160000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((37614216985655139:ℝ)/6400000000) + ((4153496386417083:ℝ)/320000000)*t) + (8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((-767289255545751335496374641083:ℝ)/13107200000000000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((-86073750925326829351721692701:ℝ)/655360000000000000) - 3*((-767289255545751335496374641083:ℝ)/13107200000000000000))*t) + (((122570082855806967:ℝ)/16000000000) + ((14162665351154949:ℝ)/800000000)*t)*((695877282219:ℝ)/10000000000000) - (((337711526424263:ℝ)/62500000) + t * ((149732671603349103:ℝ)/10000000000)) = (((37614216985655139:ℝ)/6400000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((-767289255545751335496374641083:ℝ)/13107200000000000000) + ((122570082855806967:ℝ)/16000000000)*((695877282219:ℝ)/10000000000000) - ((337711526424263:ℝ)/62500000)) + t*(((4153496386417083:ℝ)/320000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((-86073750925326829351721692701:ℝ)/655360000000000000) - 3*((-767289255545751335496374641083:ℝ)/13107200000000000000)) + ((14162665351154949:ℝ)/800000000)*((695877282219:ℝ)/10000000000000) - ((149732671603349103:ℝ)/10000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece16_e23 {q : ℝ} (h0 : ((43:ℝ)/10) ≤ q) (h1 : q ≤ ((22:ℝ)/5)) :
    |pieceW q pieceX_16 2 3 - (((-241336647148084857:ℝ)/1000000000000) + (q - ((87:ℝ)/20)) * ((-147741738243368091:ℝ)/25000000000))| ≤ ((76559386002309443:ℝ)/250000000000) := by
  set t := q - ((87:ℝ)/20) with htd
  have hq : q = ((87:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece16_L3 piece16_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((87:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_23 q = ∑ e ∈ Finset.range 9, ([((446829371198343:ℝ)/320000000), ((80651895348429:ℝ)/32000000), ((3442310603937:ℝ)/1600000), ((90483557517:ℝ)/80000), ((314627409:ℝ)/800), ((18100863:ℝ)/200), ((132027:ℝ)/10), (1102:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_23; ring
  have h12 : centralNum12_23 q = ∑ e ∈ Finset.range 16, ([((119338543952229579486519928262391:ℝ)/3670016000000000000000), ((-1786850324546742150748028436357:ℝ)/18350080000000000000), ((-768657068999727064624891141677:ℝ)/1835008000000000000), ((-1048845686341080207935146059:ℝ)/1835008000000000), ((-1881295653816666144195510321:ℝ)/4587520000000000), ((-13529682816969230744560659:ℝ)/81920000000000), ((-325517465802746995451049:ℝ)/11468800000000), ((1797309423679392329809:ℝ)/286720000000), ((29720137641024123101:ℝ)/5734400000), ((1044134074971253617:ℝ)/716800000), ((74459763551191437:ℝ)/358400000), ((13979658815127:ℝ)/1792000), ((-63341620029:ℝ)/25600), ((-420282351:ℝ)/896), ((-15871059:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_23; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((446829371198343:ℝ)/320000000), ((80651895348429:ℝ)/32000000), ((3442310603937:ℝ)/1600000), ((90483557517:ℝ)/80000), ((314627409:ℝ)/800), ((18100863:ℝ)/200), ((132027:ℝ)/10), (1102:ℝ), (40:ℝ)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((119338543952229579486519928262391:ℝ)/3670016000000000000000), ((-1786850324546742150748028436357:ℝ)/18350080000000000000), ((-768657068999727064624891141677:ℝ)/1835008000000000000), ((-1048845686341080207935146059:ℝ)/1835008000000000), ((-1881295653816666144195510321:ℝ)/4587520000000000), ((-13529682816969230744560659:ℝ)/81920000000000), ((-325517465802746995451049:ℝ)/11468800000000), ((1797309423679392329809:ℝ)/286720000000), ((29720137641024123101:ℝ)/5734400000), ((1044134074971253617:ℝ)/716800000), ((74459763551191437:ℝ)/358400000), ((13979658815127:ℝ)/1792000), ((-63341620029:ℝ)/25600), ((-420282351:ℝ)/896), ((-15871059:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 14 ht
  have m12 := abs_poly_le (fun e => ([((119338543952229579486519928262391:ℝ)/3670016000000000000000), ((-1786850324546742150748028436357:ℝ)/18350080000000000000), ((-768657068999727064624891141677:ℝ)/1835008000000000000), ((-1048845686341080207935146059:ℝ)/1835008000000000), ((-1881295653816666144195510321:ℝ)/4587520000000000), ((-13529682816969230744560659:ℝ)/81920000000000), ((-325517465802746995451049:ℝ)/11468800000000), ((1797309423679392329809:ℝ)/286720000000), ((29720137641024123101:ℝ)/5734400000), ((1044134074971253617:ℝ)/716800000), ((74459763551191437:ℝ)/358400000), ((13979658815127:ℝ)/1792000), ((-63341620029:ℝ)/25600), ((-420282351:ℝ)/896), ((-15871059:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 16 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((446829371198343:ℝ)/320000000), ((80651895348429:ℝ)/32000000), ((3442310603937:ℝ)/1600000), ((90483557517:ℝ)/80000), ((314627409:ℝ)/800), ((18100863:ℝ)/200), ((132027:ℝ)/10), (1102:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e) - (((446829371198343:ℝ)/320000000) + ((80651895348429:ℝ)/32000000)*t)| ≤ ((3534385531941:ℝ)/640000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 16, ([((119338543952229579486519928262391:ℝ)/3670016000000000000000), ((-1786850324546742150748028436357:ℝ)/18350080000000000000), ((-768657068999727064624891141677:ℝ)/1835008000000000000), ((-1048845686341080207935146059:ℝ)/1835008000000000), ((-1881295653816666144195510321:ℝ)/4587520000000000), ((-13529682816969230744560659:ℝ)/81920000000000), ((-325517465802746995451049:ℝ)/11468800000000), ((1797309423679392329809:ℝ)/286720000000), ((29720137641024123101:ℝ)/5734400000), ((1044134074971253617:ℝ)/716800000), ((74459763551191437:ℝ)/358400000), ((13979658815127:ℝ)/1792000), ((-63341620029:ℝ)/25600), ((-420282351:ℝ)/896), ((-15871059:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e) - ((119338543952229579486519928262391:ℝ)/3670016000000000000000) - ((-1786850324546742150748028436357:ℝ)/18350080000000000000)*t| ≤ ((4115094306726368909162049425661:ℝ)/3670016000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 16, ([((119338543952229579486519928262391:ℝ)/3670016000000000000000), ((-1786850324546742150748028436357:ℝ)/18350080000000000000), ((-768657068999727064624891141677:ℝ)/1835008000000000000), ((-1048845686341080207935146059:ℝ)/1835008000000000), ((-1881295653816666144195510321:ℝ)/4587520000000000), ((-13529682816969230744560659:ℝ)/81920000000000), ((-325517465802746995451049:ℝ)/11468800000000), ((1797309423679392329809:ℝ)/286720000000), ((29720137641024123101:ℝ)/5734400000), ((1044134074971253617:ℝ)/716800000), ((74459763551191437:ℝ)/358400000), ((13979658815127:ℝ)/1792000), ((-63341620029:ℝ)/25600), ((-420282351:ℝ)/896), ((-15871059:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e)| ≤ ((70661070752211684951581131025811:ℝ)/1835008000000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((122570082855806967:ℝ)/16000000000) - ((14162665351154949:ℝ)/800000000)*t| ≤ ((186430602969793:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((22:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-7627725:ℝ)/2), (173988600:ℝ), (-2299614450:ℝ), (13088188200:ℝ), (-38221499200:ℝ), (63366115840:ℝ), ((-445610508288:ℝ)/7), ((841540698112:ℝ)/21), ((-326820167680:ℝ)/21), ((10133438464:ℝ)/3), ((-2147483648:ℝ)/7)] : List ℝ).getD e 0) 16 hq1'
  have m13' : |centralNum13_23 q| ≤ ((7366513738328260175782069090352:ℝ)/640869140625) := by
    rw [centralNum13_23_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((22:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-15801525:ℝ)/4), ((655493865:ℝ)/4), ((-7334421225:ℝ)/4), ((16442962485:ℝ)/2), ((-598626108395:ℝ)/32), ((414013307125:ℝ)/16), ((-4611984703125:ℝ)/224), ((399923828125:ℝ)/48), ((-4353201171875:ℝ)/2688), ((189736328125:ℝ)/1344), ((-244140625:ℝ)/56)] : List ℝ).getD e 0) 16 hq1'
  have m23' : |centralNum23_23 q| ≤ ((10720717798443224200285624:ℝ)/8203125) := by
    rw [centralNum23_23_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece16_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece16_E11 h0) m23'
  have c5 := scaled_affine (X := ((-7169768159:ℝ)/25000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((446829371198343:ℝ)/320000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((119338543952229579486519928262391:ℝ)/3670016000000000000000) + ((122570082855806967:ℝ)/16000000000)*((-7169768159:ℝ)/25000000000) - ((-241336647148084857:ℝ)/1000000000000)) (β := ((80651895348429:ℝ)/32000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((-1786850324546742150748028436357:ℝ)/18350080000000000000) - 3*((119338543952229579486519928262391:ℝ)/3670016000000000000000)) + ((14162665351154949:ℝ)/800000000)*((-7169768159:ℝ)/25000000000) - ((-147741738243368091:ℝ)/25000000000)) ht
  have hW : pieceW q pieceX_16 2 3 = centralNum11_23 q + 8*(Real.exp (-(3*((87:ℝ)/20)))*Real.exp (-3*t))*centralNum12_23 q + 18*Real.exp (-8*q)*centralNum13_23 q + 72*Real.exp (-11*q)*centralNum23_23 q + 8*q^7*(2*q-3)^2*((-7169768159:ℝ)/25000000000) + (0:ℝ) := by
    rw [pieceW_23, pieceX_16, sym4_23, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((15921130769520470712305108819842261159841008235646718384432703523357:ℝ)/100946846993226601095772994320362738640213156408484357075770600000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((446829371198343:ℝ)/320000000) + ((80651895348429:ℝ)/32000000)*t) + (8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((119338543952229579486519928262391:ℝ)/3670016000000000000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((-1786850324546742150748028436357:ℝ)/18350080000000000000) - 3*((119338543952229579486519928262391:ℝ)/3670016000000000000000))*t) + (((122570082855806967:ℝ)/16000000000) + ((14162665351154949:ℝ)/800000000)*t)*((-7169768159:ℝ)/25000000000) - (((-241336647148084857:ℝ)/1000000000000) + t * ((-147741738243368091:ℝ)/25000000000)) = (((446829371198343:ℝ)/320000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((119338543952229579486519928262391:ℝ)/3670016000000000000000) + ((122570082855806967:ℝ)/16000000000)*((-7169768159:ℝ)/25000000000) - ((-241336647148084857:ℝ)/1000000000000)) + t*(((80651895348429:ℝ)/32000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((-1786850324546742150748028436357:ℝ)/18350080000000000000) - 3*((119338543952229579486519928262391:ℝ)/3670016000000000000000)) + ((14162665351154949:ℝ)/800000000)*((-7169768159:ℝ)/25000000000) - ((-147741738243368091:ℝ)/25000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece16_e33 {q : ℝ} (h0 : ((43:ℝ)/10) ≤ q) (h1 : q ≤ ((22:ℝ)/5)) :
    |pieceW q pieceX_16 3 3 - (((39151356138938649:ℝ)/2500000000) + (q - ((87:ℝ)/20)) * ((384806226992143101:ℝ)/10000000000))| ≤ ((36420437199400779:ℝ)/4000000000) := by
  set t := q - ((87:ℝ)/20) with htd
  have hq : q = ((87:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece16_L3 piece16_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((87:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_33 q = ∑ e ∈ Finset.range 10, ([((36207794487153537:ℝ)/22400000000), ((2726616097511127:ℝ)/560000000), ((327837906800883:ℝ)/56000000), ((1554048774243:ℝ)/400000), ((32284884951:ℝ)/20000), ((443990763:ℝ)/1000), ((4097271:ℝ)/50), ((345438:ℝ)/35), ((4944:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_33; ring
  have h12 : centralNum12_33 q = ∑ e ∈ Finset.range 17, ([((191179323915751418315584239922081293:ℝ)/1027604480000000000000000), ((7745924618068614475784000020707087:ℝ)/7340032000000000000000), ((998071207319306895378601811215383:ℝ)/513802240000000000000), ((6283145183981117900810344520031:ℝ)/3670016000000000000), ((131255497541400670706065024041:ℝ)/183500800000000000), ((98943977208172118766553251:ℝ)/45875200000000000), ((-361265130846600023864175567:ℝ)/2293760000000000), ((-13816122356914917820265547:ℝ)/160563200000000), ((-25985703022206638761509:ℝ)/1146880000000), ((-966460294071803179153:ℝ)/401408000000), ((4885765762886107983:ℝ)/14336000000), ((112698184753158849:ℝ)/716800000), ((157885945281891:ℝ)/7168000), ((307277189469:ℝ)/358400), ((-16650814167:ℝ)/125440), ((-80483787:ℝ)/4480), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_33; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((36207794487153537:ℝ)/22400000000), ((2726616097511127:ℝ)/560000000), ((327837906800883:ℝ)/56000000), ((1554048774243:ℝ)/400000), ((32284884951:ℝ)/20000), ((443990763:ℝ)/1000), ((4097271:ℝ)/50), ((345438:ℝ)/35), ((4944:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((191179323915751418315584239922081293:ℝ)/1027604480000000000000000), ((7745924618068614475784000020707087:ℝ)/7340032000000000000000), ((998071207319306895378601811215383:ℝ)/513802240000000000000), ((6283145183981117900810344520031:ℝ)/3670016000000000000), ((131255497541400670706065024041:ℝ)/183500800000000000), ((98943977208172118766553251:ℝ)/45875200000000000), ((-361265130846600023864175567:ℝ)/2293760000000000), ((-13816122356914917820265547:ℝ)/160563200000000), ((-25985703022206638761509:ℝ)/1146880000000), ((-966460294071803179153:ℝ)/401408000000), ((4885765762886107983:ℝ)/14336000000), ((112698184753158849:ℝ)/716800000), ((157885945281891:ℝ)/7168000), ((307277189469:ℝ)/358400), ((-16650814167:ℝ)/125440), ((-80483787:ℝ)/4480), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 15 ht
  have m12 := abs_poly_le (fun e => ([((191179323915751418315584239922081293:ℝ)/1027604480000000000000000), ((7745924618068614475784000020707087:ℝ)/7340032000000000000000), ((998071207319306895378601811215383:ℝ)/513802240000000000000), ((6283145183981117900810344520031:ℝ)/3670016000000000000), ((131255497541400670706065024041:ℝ)/183500800000000000), ((98943977208172118766553251:ℝ)/45875200000000000), ((-361265130846600023864175567:ℝ)/2293760000000000), ((-13816122356914917820265547:ℝ)/160563200000000), ((-25985703022206638761509:ℝ)/1146880000000), ((-966460294071803179153:ℝ)/401408000000), ((4885765762886107983:ℝ)/14336000000), ((112698184753158849:ℝ)/716800000), ((157885945281891:ℝ)/7168000), ((307277189469:ℝ)/358400), ((-16650814167:ℝ)/125440), ((-80483787:ℝ)/4480), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 17 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((36207794487153537:ℝ)/22400000000), ((2726616097511127:ℝ)/560000000), ((327837906800883:ℝ)/56000000), ((1554048774243:ℝ)/400000), ((32284884951:ℝ)/20000), ((443990763:ℝ)/1000), ((4097271:ℝ)/50), ((345438:ℝ)/35), ((4944:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e) - (((36207794487153537:ℝ)/22400000000) + ((2726616097511127:ℝ)/560000000)*t)| ≤ ((48420768457831:ℝ)/3200000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 17, ([((191179323915751418315584239922081293:ℝ)/1027604480000000000000000), ((7745924618068614475784000020707087:ℝ)/7340032000000000000000), ((998071207319306895378601811215383:ℝ)/513802240000000000000), ((6283145183981117900810344520031:ℝ)/3670016000000000000), ((131255497541400670706065024041:ℝ)/183500800000000000), ((98943977208172118766553251:ℝ)/45875200000000000), ((-361265130846600023864175567:ℝ)/2293760000000000), ((-13816122356914917820265547:ℝ)/160563200000000), ((-25985703022206638761509:ℝ)/1146880000000), ((-966460294071803179153:ℝ)/401408000000), ((4885765762886107983:ℝ)/14336000000), ((112698184753158849:ℝ)/716800000), ((157885945281891:ℝ)/7168000), ((307277189469:ℝ)/358400), ((-16650814167:ℝ)/125440), ((-80483787:ℝ)/4480), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e) - ((191179323915751418315584239922081293:ℝ)/1027604480000000000000000) - ((7745924618068614475784000020707087:ℝ)/7340032000000000000000)*t| ≤ ((2607431675954278848453871179491563:ℝ)/513802240000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 17, ([((191179323915751418315584239922081293:ℝ)/1027604480000000000000000), ((7745924618068614475784000020707087:ℝ)/7340032000000000000000), ((998071207319306895378601811215383:ℝ)/513802240000000000000), ((6283145183981117900810344520031:ℝ)/3670016000000000000), ((131255497541400670706065024041:ℝ)/183500800000000000), ((98943977208172118766553251:ℝ)/45875200000000000), ((-361265130846600023864175567:ℝ)/2293760000000000), ((-13816122356914917820265547:ℝ)/160563200000000), ((-25985703022206638761509:ℝ)/1146880000000), ((-966460294071803179153:ℝ)/401408000000), ((4885765762886107983:ℝ)/14336000000), ((112698184753158849:ℝ)/716800000), ((157885945281891:ℝ)/7168000), ((307277189469:ℝ)/358400), ((-16650814167:ℝ)/125440), ((-80483787:ℝ)/4480), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e)| ≤ ((8950559271219295619392142229500501:ℝ)/36700160000000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((122570082855806967:ℝ)/16000000000), ((14162665351154949:ℝ)/800000000), ((90478349734671:ℝ)/5000000), ((335660709699:ℝ)/31250), ((204068104191:ℝ)/50000), ((2574496953:ℝ)/2500), ((21573216:ℝ)/125), ((463248:ℝ)/25), ((5784:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((122570082855806967:ℝ)/16000000000) - ((14162665351154949:ℝ)/800000000)*t| ≤ ((186430602969793:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((22:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-8120475:ℝ)/4), ((464861025:ℝ)/2), (-5906535975:ℝ), ((411904731750:ℝ)/7), ((-2024051769000:ℝ)/7), ((5554394637600:ℝ)/7), (-1314913862656:ℝ), ((9709155336192:ℝ)/7), ((-6724555112448:ℝ)/7), ((1313173667840:ℝ)/3), ((-6168244125696:ℝ)/49), ((3004329623552:ℝ)/147), ((-68719476736:ℝ)/49)] : List ℝ).getD e 0) 17 hq1'
  have m13' : |centralNum13_33 q| ≤ ((9429062636547989834902074594966548:ℝ)/22430419921875) := by
    rw [centralNum13_33_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((22:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-16872075:ℝ)/8), ((1833754545:ℝ)/8), ((-83998007145:ℝ)/16), ((4929124002765:ℝ)/112), ((-76723155584685:ℝ)/448), ((164888745653055:ℝ)/448), ((-63358359907625:ℝ)/128), ((364713160040625:ℝ)/896), ((-334937462578125:ℝ)/1792), ((245466998046875:ℝ)/5376), ((-72144521484375:ℝ)/12544), ((6518798828125:ℝ)/18816), ((-6103515625:ℝ)/784)] : List ℝ).getD e 0) 17 hq1'
  have m23' : |centralNum23_33 q| ≤ ((1978783366642603896026230238:ℝ)/57421875) := by
    rw [centralNum23_33_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece16_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece16_E11 h0) m23'
  have c5 := scaled_affine (X := ((35388847709:ℝ)/25000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3))| ≤ ((12922085021117101361262576271360000000:ℝ)/14787149368428996914979259922814595821) := by
    rw [abs_neg, tailWeight_3, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((22:ℝ)/5)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((22:ℝ)/5)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece16_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((3308571812705231500:ℝ)/129140163)) ≤ ((22:ℝ)/5)^6*(8000*(2*((22:ℝ)/5)-3)^2*(1/((114504651573259954108771412367:ℝ)/2000000000))*((3308571812705231500:ℝ)/129140163)) := by
          gcongr
      _ ≤ ((12922085021117101361262576271360000000:ℝ)/14787149368428996914979259922814595821) := by norm_num
  have c7 := affine_round (α := ((36207794487153537:ℝ)/22400000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((191179323915751418315584239922081293:ℝ)/1027604480000000000000000) + ((122570082855806967:ℝ)/16000000000)*((35388847709:ℝ)/25000000000) - ((39151356138938649:ℝ)/2500000000)) (β := ((2726616097511127:ℝ)/560000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((7745924618068614475784000020707087:ℝ)/7340032000000000000000) - 3*((191179323915751418315584239922081293:ℝ)/1027604480000000000000000)) + ((14162665351154949:ℝ)/800000000)*((35388847709:ℝ)/25000000000) - ((384806226992143101:ℝ)/10000000000)) ht
  have hW : pieceW q pieceX_16 3 3 = centralNum11_33 q + 8*(Real.exp (-(3*((87:ℝ)/20)))*Real.exp (-3*t))*centralNum12_33 q + 18*Real.exp (-8*q)*centralNum13_33 q + 72*Real.exp (-11*q)*centralNum23_33 q + 8*q^7*(2*q-3)^2*((35388847709:ℝ)/25000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3)) := by
    rw [pieceW_33, pieceX_16, sym4_33, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((10738606572803877292596368771197876906906852034983801794781430109706281:ℝ)/353313964476293103835205480121269585240746047429695249765197100000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((36207794487153537:ℝ)/22400000000) + ((2726616097511127:ℝ)/560000000)*t) + (8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((191179323915751418315584239922081293:ℝ)/1027604480000000000000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((7745924618068614475784000020707087:ℝ)/7340032000000000000000) - 3*((191179323915751418315584239922081293:ℝ)/1027604480000000000000000))*t) + (((122570082855806967:ℝ)/16000000000) + ((14162665351154949:ℝ)/800000000)*t)*((35388847709:ℝ)/25000000000) - (((39151356138938649:ℝ)/2500000000) + t * ((384806226992143101:ℝ)/10000000000)) = (((36207794487153537:ℝ)/22400000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*((191179323915751418315584239922081293:ℝ)/1027604480000000000000000) + ((122570082855806967:ℝ)/16000000000)*((35388847709:ℝ)/25000000000) - ((39151356138938649:ℝ)/2500000000)) + t*(((2726616097511127:ℝ)/560000000) + 8*(((1/((465096411982178219697953578871:ℝ)/1000000000000000000000000))+(1/((465096411314890046271789904047:ℝ)/1000000000000000000000000)))/2)*(((7745924618068614475784000020707087:ℝ)/7340032000000000000000) - 3*((191179323915751418315584239922081293:ℝ)/1027604480000000000000000)) + ((14162665351154949:ℝ)/800000000)*((35388847709:ℝ)/25000000000) - ((384806226992143101:ℝ)/10000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece16_plus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((914623869287462287:ℝ)/100000000000) + ((1:ℝ)/20)*((100912001942736407:ℝ)/5000000000) - (((518153597132078979:ℝ)/10000000000000) + ((27091723328696237:ℝ)/4000000000000) + ((246633584566337933:ℝ)/100000000000000) + ((141656869163727507:ℝ)/20000000000000)))
      (((-146388986721594643:ℝ)/100000000000) + ((1:ℝ)/20)*((-113687082922384783:ℝ)/50000000000))
      (((-153761552051803023:ℝ)/10000000000000) + ((1:ℝ)/20)*((-262199287045914349:ℝ)/5000000000000))
      (((478204482056410431:ℝ)/5000000000000) + ((1:ℝ)/20)*((-498747630188075017:ℝ)/5000000000000))
      (((688122750373900493:ℝ)/100000000000) + ((1:ℝ)/20)*((14279829631602213:ℝ)/1000000000) - (((27091723328696237:ℝ)/4000000000000) + ((361766913029551263:ℝ)/10000000000000) + ((208144499941291797:ℝ)/10000000000000) + ((67876121009053133:ℝ)/2500000000000)))
      (((-83648329528670721:ℝ)/125000000000) + ((1:ℝ)/20)*((-138793726958519997:ℝ)/100000000000))
      (((-167269002310683869:ℝ)/1000000000000) + ((1:ℝ)/20)*((9658935593545031:ℝ)/6250000000))
      (((337711526424263:ℝ)/62500000) + ((1:ℝ)/20)*((149732671603349103:ℝ)/10000000000) - (((246633584566337933:ℝ)/100000000000000) + ((208144499941291797:ℝ)/10000000000000) + ((899292008164108873:ℝ)/10000000000000) + ((76559386002309443:ℝ)/250000000000)))
      (((-241336647148084857:ℝ)/1000000000000) + ((1:ℝ)/20)*((-147741738243368091:ℝ)/25000000000))
      (((39151356138938649:ℝ)/2500000000) + ((1:ℝ)/20)*((384806226992143101:ℝ)/10000000000) - (((141656869163727507:ℝ)/20000000000000) + ((67876121009053133:ℝ)/2500000000000) + ((76559386002309443:ℝ)/250000000000) + ((36420437199400779:ℝ)/4000000000))) i j :=
  quadForm_nonneg_of_ldl ((1008722124245275522817:ℝ)/100000000000000) ((146417660746834029389150162027313956455727:ℝ)/20174442484905510456340000000000000) ((41412995099395363481449848516722645020098709878202759150841369:ℝ)/7320883037341701469457508101365697822786350000000000000) ((66964764825228046322240973734908234312592639887142491898946998968027648526056565617:ℝ)/8282599019879072696289969703344529004019741975640551830168273800000000000000) ((-157757695013833121300:ℝ)/1008722124245275522817) ((-1799814807563944579:ℝ)/1008722124245275522817) ((9065342010940133603:ℝ)/1008722124245275522817) ((-14957297262270507070489286682431254171150:ℝ)/146417660746834029389150162027313956455727) ((-1529624249813775023283512214408770198360:ℝ)/146417660746834029389150162027313956455727) ((-7971032470711678077050030338347698999003528690521034313100653:ℝ)/82825990198790726962899697033445290040197419756405518301682738)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece16_minus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((914623869287462287:ℝ)/100000000000) - ((1:ℝ)/20)*((100912001942736407:ℝ)/5000000000) - (((518153597132078979:ℝ)/10000000000000) + ((27091723328696237:ℝ)/4000000000000) + ((246633584566337933:ℝ)/100000000000000) + ((141656869163727507:ℝ)/20000000000000)))
      (((-146388986721594643:ℝ)/100000000000) - ((1:ℝ)/20)*((-113687082922384783:ℝ)/50000000000))
      (((-153761552051803023:ℝ)/10000000000000) - ((1:ℝ)/20)*((-262199287045914349:ℝ)/5000000000000))
      (((478204482056410431:ℝ)/5000000000000) - ((1:ℝ)/20)*((-498747630188075017:ℝ)/5000000000000))
      (((688122750373900493:ℝ)/100000000000) - ((1:ℝ)/20)*((14279829631602213:ℝ)/1000000000) - (((27091723328696237:ℝ)/4000000000000) + ((361766913029551263:ℝ)/10000000000000) + ((208144499941291797:ℝ)/10000000000000) + ((67876121009053133:ℝ)/2500000000000)))
      (((-83648329528670721:ℝ)/125000000000) - ((1:ℝ)/20)*((-138793726958519997:ℝ)/100000000000))
      (((-167269002310683869:ℝ)/1000000000000) - ((1:ℝ)/20)*((9658935593545031:ℝ)/6250000000))
      (((337711526424263:ℝ)/62500000) - ((1:ℝ)/20)*((149732671603349103:ℝ)/10000000000) - (((246633584566337933:ℝ)/100000000000000) + ((208144499941291797:ℝ)/10000000000000) + ((899292008164108873:ℝ)/10000000000000) + ((76559386002309443:ℝ)/250000000000)))
      (((-241336647148084857:ℝ)/1000000000000) - ((1:ℝ)/20)*((-147741738243368091:ℝ)/25000000000))
      (((39151356138938649:ℝ)/2500000000) - ((1:ℝ)/20)*((384806226992143101:ℝ)/10000000000) - (((141656869163727507:ℝ)/20000000000000) + ((67876121009053133:ℝ)/2500000000000) + ((76559386002309443:ℝ)/250000000000) + ((36420437199400779:ℝ)/4000000000))) i j :=
  quadForm_nonneg_of_ldl ((806898120359802708817:ℝ)/100000000000000) ((94413352849849529864110590752858243899727:ℝ)/16137962407196054176340000000000000) ((19700874325622702868012363672130556894217744384025362807674609:ℝ)/4720667642492476493205529537642912194986350000000000000) ((16866255072446778463501912646969692920719417180169637263503775637939588420889078297:ℝ)/3940174865124540573602472734426111378843548876805072561534921800000000000000) ((-135020278429356164700:ℝ)/806898120359802708817) ((-1275416233472115881:ℝ)/806898120359802708817) ((10062837271316283637:ℝ)/806898120359802708817) ((-9713826215853216366118593421199228713770:ℝ)/94413352849849529864110590752858243899727) ((-3674647769163781681391220152498220189000:ℝ)/94413352849849529864110590752858243899727) ((291534230814258199429653242630854143247673907889638988515007:ℝ)/39401748651245405736024727344261113788435488768050725615349218)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

/-- **Piece 16.** The piece matrix is positive semidefinite on `q ∈ [43/10, 22/5]`. -/
theorem piece_16 {q : ℝ} (h0 : ((43:ℝ)/10) ≤ q) (h1 : q ≤ ((22:ℝ)/5)) (y : Fin 4 → ℝ) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceW q pieceX_16 i j :=
  pieceForm_nonneg (pieceW_symm (sym4_symm _ _ _ _ _ _ _ _ _ _) q) (by norm_num : (0:ℝ) < ((1:ℝ)/20))
    (abs_le.mpr ⟨by linarith, by linarith⟩)
    (piece16_e00 h0 h1) (piece16_e01 h0 h1) (piece16_e02 h0 h1) (piece16_e03 h0 h1) (piece16_e11 h0 h1) (piece16_e12 h0 h1) (piece16_e13 h0 h1) (piece16_e22 h0 h1) (piece16_e23 h0 h1) (piece16_e33 h0 h1)
    piece16_plus piece16_minus y

/-! #### Piece 17 (seam), `q ∈ [22/5, 9/2]` -/

/-- The compensation matrix of piece 17. -/
def pieceX_17 : Fin 4 → Fin 4 → ℝ :=
  sym4 ((27500004167:ℝ)/2500000000000) ((-117570972237:ℝ)/100000000000000000) ((425575559063:ℝ)/100000000000000000) ((-35987352907:ℝ)/2500000000000000) ((118293027137:ℝ)/10000000000000) ((-150092730929:ℝ)/50000000000000) ((101536659457:ℝ)/10000000000000) ((2733239127:ℝ)/125000000000) ((-367535623733:ℝ)/10000000000000) ((135317610967:ℝ)/1000000000000)

theorem piece17_L3 : ((627814484614950587090063078629:ℝ)/1000000000000000000000000) ≤ Real.exp ((3:ℝ)*((89:ℝ)/20)) := by
  have h := le_exp_nat_add 13 (f := ((7:ℝ)/20)) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((89:ℝ)/20) = ((13:ℕ):ℝ) + ((7:ℝ)/20) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece17_U3 : Real.exp ((3:ℝ)*((89:ℝ)/20)) ≤ ((627814488295437581570535126581:ℝ)/1000000000000000000000000) := by
  have h := exp_nat_add_le 13 (f := ((7:ℝ)/20)) (by norm_num) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((89:ℝ)/20) = ((13:ℕ):ℝ) + ((7:ℝ)/20) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem piece17_L8_at : ((193716120106479488025927187529:ℝ)/100000000000000) ≤ Real.exp ((8:ℝ)*((22:ℝ)/5)) := by
  have h := le_exp_nat_add 35 (f := ((1:ℝ)/5)) (by norm_num)
  rw [show ((8:ℝ):ℝ)*((22:ℝ)/5) = ((35:ℕ):ℝ) + ((1:ℝ)/5) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece17_E8 {q : ℝ} (h0 : ((22:ℝ)/5) ≤ q) : Real.exp (-((8:ℝ))*q) ≤ 1/((193716120106479488025927187529:ℝ)/100000000000000) := by
  have hm : Real.exp (-((8:ℝ))*q) ≤ Real.exp (-((8:ℝ)*((22:ℝ)/5))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece17_L8_at (le_refl _)).2

theorem piece17_L11_at : ((52338698908832276471028231813:ℝ)/50000000) ≤ Real.exp ((11:ℝ)*((22:ℝ)/5)) := by
  have h := le_exp_nat_add 48 (f := ((2:ℝ)/5)) (by norm_num)
  rw [show ((11:ℝ):ℝ)*((22:ℝ)/5) = ((48:ℕ):ℝ) + ((2:ℝ)/5) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece17_E11 {q : ℝ} (h0 : ((22:ℝ)/5) ≤ q) : Real.exp (-((11:ℝ))*q) ≤ 1/((52338698908832276471028231813:ℝ)/50000000) := by
  have hm : Real.exp (-((11:ℝ))*q) ≤ Real.exp (-((11:ℝ)*((22:ℝ)/5))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece17_L11_at (le_refl _)).2

theorem piece17_Lt_at : ((82460633665245974453163323973:ℝ)/500000000) ≤ Real.exp (((529:ℝ)/50)*((22:ℝ)/5)) := by
  have h := le_exp_nat_add 46 (f := ((69:ℝ)/125)) (by norm_num)
  rw [show (((529:ℝ)/50):ℝ)*((22:ℝ)/5) = ((46:ℕ):ℝ) + ((69:ℝ)/125) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece17_Et {q : ℝ} (h0 : ((22:ℝ)/5) ≤ q) : Real.exp (-(((529:ℝ)/50))*q) ≤ 1/((82460633665245974453163323973:ℝ)/500000000) := by
  have hm : Real.exp (-(((529:ℝ)/50))*q) ≤ Real.exp (-(((529:ℝ)/50)*((22:ℝ)/5))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece17_Lt_at (le_refl _)).2

theorem piece17_e00 {q : ℝ} (h0 : ((22:ℝ)/5) ≤ q) (h1 : q ≤ ((9:ℝ)/2)) :
    |pieceW q pieceX_17 0 0 - (((113749411177950829:ℝ)/10000000000) + (q - ((89:ℝ)/20)) * ((245168778352086519:ℝ)/10000000000))| ≤ ((153141533040379899:ℝ)/2500000000000) := by
  set t := q - ((89:ℝ)/20) with htd
  have hq : q = ((89:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece17_L3 piece17_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((89:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_00 q = ∑ e ∈ Finset.range 10, ([((180508077708653849:ℝ)/16000000000), ((19416562056555309:ℝ)/800000000), ((29165542502127:ℝ)/1250000), ((3284744543073:ℝ)/250000), ((238542475437:ℝ)/50000), ((2893169013:ℝ)/2500), ((23422308:ℝ)/125), ((487872:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_00; ring
  have h12 : centralNum12_00 q = ∑ e ∈ Finset.range 11, ([((-318116935634827344893:ℝ)/320000000000), ((-7560073931304531429:ℝ)/3200000000), ((-202242231046743771:ℝ)/80000000), ((-3207362466753747:ℝ)/2000000), ((-133553985090183:ℝ)/200000), ((-9534321295107:ℝ)/50000), ((-4726575777:ℝ)/125), ((-128521494:ℝ)/25), ((-2292834:ℝ)/5), (-24232:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_00; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((180508077708653849:ℝ)/16000000000), ((19416562056555309:ℝ)/800000000), ((29165542502127:ℝ)/1250000), ((3284744543073:ℝ)/250000), ((238542475437:ℝ)/50000), ((2893169013:ℝ)/2500), ((23422308:ℝ)/125), ((487872:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-318116935634827344893:ℝ)/320000000000), ((-7560073931304531429:ℝ)/3200000000), ((-202242231046743771:ℝ)/80000000), ((-3207362466753747:ℝ)/2000000), ((-133553985090183:ℝ)/200000), ((-9534321295107:ℝ)/50000), ((-4726575777:ℝ)/125), ((-128521494:ℝ)/25), ((-2292834:ℝ)/5), (-24232:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 9 ht
  have m12 := abs_poly_le (fun e => ([((-318116935634827344893:ℝ)/320000000000), ((-7560073931304531429:ℝ)/3200000000), ((-202242231046743771:ℝ)/80000000), ((-3207362466753747:ℝ)/2000000), ((-133553985090183:ℝ)/200000), ((-9534321295107:ℝ)/50000), ((-4726575777:ℝ)/125), ((-128521494:ℝ)/25), ((-2292834:ℝ)/5), (-24232:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 11 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((180508077708653849:ℝ)/16000000000), ((19416562056555309:ℝ)/800000000), ((29165542502127:ℝ)/1250000), ((3284744543073:ℝ)/250000), ((238542475437:ℝ)/50000), ((2893169013:ℝ)/2500), ((23422308:ℝ)/125), ((487872:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - (((180508077708653849:ℝ)/16000000000) + ((19416562056555309:ℝ)/800000000)*t)| ≤ ((480029117395421:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 11, ([((-318116935634827344893:ℝ)/320000000000), ((-7560073931304531429:ℝ)/3200000000), ((-202242231046743771:ℝ)/80000000), ((-3207362466753747:ℝ)/2000000), ((-133553985090183:ℝ)/200000), ((-9534321295107:ℝ)/50000), ((-4726575777:ℝ)/125), ((-128521494:ℝ)/25), ((-2292834:ℝ)/5), (-24232:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e) - ((-318116935634827344893:ℝ)/320000000000) - ((-7560073931304531429:ℝ)/3200000000)*t| ≤ ((1043962179324998981:ℝ)/160000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 11, ([((-318116935634827344893:ℝ)/320000000000), ((-7560073931304531429:ℝ)/3200000000), ((-202242231046743771:ℝ)/80000000), ((-3207362466753747:ℝ)/2000000), ((-133553985090183:ℝ)/200000), ((-9534321295107:ℝ)/50000), ((-4726575777:ℝ)/125), ((-128521494:ℝ)/25), ((-2292834:ℝ)/5), (-24232:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((35800522965:ℝ)/32) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((153969276771336449:ℝ)/16000000000) - ((17329240634519109:ℝ)/800000000)*t| ≤ ((444183297072221:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((9:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (600:ℝ), (-7776:ℝ), (16800:ℝ), (-9216:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m13' : |centralNum13_00 q| ≤ ((363386069775:ℝ)/8) := by
    rw [centralNum13_00_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((9:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (780:ℝ), (-6156:ℝ), (15288:ℝ), (-14400:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m23' : |centralNum23_00 q| ≤ ((986645194227:ℝ)/16) := by
    rw [centralNum23_00_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece17_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece17_E11 h0) m23'
  have c5 := scaled_affine (X := ((27500004167:ℝ)/2500000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0))| ≤ ((70642122300000000000000:ℝ)/27486877888415324817721107991) := by
    rw [abs_neg, tailWeight_0, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((9:ℝ)/2)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((9:ℝ)/2)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece17_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((10465499600:ℝ)/59049)) ≤ ((9:ℝ)/2)^6*(8000*(2*((9:ℝ)/2)-3)^2*(1/((82460633665245974453163323973:ℝ)/500000000))*((10465499600:ℝ)/59049)) := by
          gcongr
      _ ≤ ((70642122300000000000000:ℝ)/27486877888415324817721107991) := by norm_num
  have c7 := affine_round (α := ((180508077708653849:ℝ)/16000000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((-318116935634827344893:ℝ)/320000000000) + ((153969276771336449:ℝ)/16000000000)*((27500004167:ℝ)/2500000000000) - ((113749411177950829:ℝ)/10000000000)) (β := ((19416562056555309:ℝ)/800000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((-7560073931304531429:ℝ)/3200000000) - 3*((-318116935634827344893:ℝ)/320000000000)) + ((17329240634519109:ℝ)/800000000)*((27500004167:ℝ)/2500000000000) - ((245168778352086519:ℝ)/10000000000)) ht
  have hW : pieceW q pieceX_17 0 0 = centralNum11_00 q + 8*(Real.exp (-(3*((89:ℝ)/20)))*Real.exp (-3*t))*centralNum12_00 q + 18*Real.exp (-8*q)*centralNum13_00 q + 72*Real.exp (-11*q)*centralNum23_00 q + 8*q^7*(2*q-3)^2*((27500004167:ℝ)/2500000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0)) := by
    rw [pieceW_00, pieceX_17, sym4_00, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((6409900932626773789389484457410297958043713356704009162310896819155261:ℝ)/788302058805998145977680591861527104580107918923742141874898000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((180508077708653849:ℝ)/16000000000) + ((19416562056555309:ℝ)/800000000)*t) + (8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((-318116935634827344893:ℝ)/320000000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((-7560073931304531429:ℝ)/3200000000) - 3*((-318116935634827344893:ℝ)/320000000000))*t) + (((153969276771336449:ℝ)/16000000000) + ((17329240634519109:ℝ)/800000000)*t)*((27500004167:ℝ)/2500000000000) - (((113749411177950829:ℝ)/10000000000) + t * ((245168778352086519:ℝ)/10000000000)) = (((180508077708653849:ℝ)/16000000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((-318116935634827344893:ℝ)/320000000000) + ((153969276771336449:ℝ)/16000000000)*((27500004167:ℝ)/2500000000000) - ((113749411177950829:ℝ)/10000000000)) + t*(((19416562056555309:ℝ)/800000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((-7560073931304531429:ℝ)/3200000000) - 3*((-318116935634827344893:ℝ)/320000000000)) + ((17329240634519109:ℝ)/800000000)*((27500004167:ℝ)/2500000000000) - ((245168778352086519:ℝ)/10000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece17_e01 {q : ℝ} (h0 : ((22:ℝ)/5) ≤ q) (h1 : q ≤ ((9:ℝ)/2)) :
    |pieceW q pieceX_17 0 1 - (((-42628764083640127:ℝ)/25000000000) + (q - ((89:ℝ)/20)) * ((-259880984430167821:ℝ)/100000000000))| ≤ ((89170114319025149:ℝ)/12500000000000) := by
  set t := q - ((89:ℝ)/20) with htd
  have hq : q = ((89:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece17_L3 piece17_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((89:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_01 q = ∑ e ∈ Finset.range 8, ([((-132694004686587:ℝ)/80000000), ((-10436607110181:ℝ)/4000000), ((-351795745287:ℝ)/200000), ((-1317587061:ℝ)/2000), ((-14804349:ℝ)/100), ((-499023:ℝ)/25), ((-7476:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_01; ring
  have h12 : centralNum12_01 q = ∑ e ∈ Finset.range 12, ([((-46673427351909331057251:ℝ)/12800000000000), ((-3240154871526392359647:ℝ)/320000000000), ((-81577270130949038601:ℝ)/6400000000), ((-1536833754435115131:ℝ)/160000000), ((-38523246490759323:ℝ)/8000000), ((-1686668192349147:ℝ)/1000000), ((-42123144329301:ℝ)/100000), ((-37506757011:ℝ)/500), ((-933542163:ℝ)/100), ((-3866334:ℝ)/5), ((-191844:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_01; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-132694004686587:ℝ)/80000000), ((-10436607110181:ℝ)/4000000), ((-351795745287:ℝ)/200000), ((-1317587061:ℝ)/2000), ((-14804349:ℝ)/100), ((-499023:ℝ)/25), ((-7476:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0) 6 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-46673427351909331057251:ℝ)/12800000000000), ((-3240154871526392359647:ℝ)/320000000000), ((-81577270130949038601:ℝ)/6400000000), ((-1536833754435115131:ℝ)/160000000), ((-38523246490759323:ℝ)/8000000), ((-1686668192349147:ℝ)/1000000), ((-42123144329301:ℝ)/100000), ((-37506757011:ℝ)/500), ((-933542163:ℝ)/100), ((-3866334:ℝ)/5), ((-191844:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0) 10 ht
  have m12 := abs_poly_le (fun e => ([((-46673427351909331057251:ℝ)/12800000000000), ((-3240154871526392359647:ℝ)/320000000000), ((-81577270130949038601:ℝ)/6400000000), ((-1536833754435115131:ℝ)/160000000), ((-38523246490759323:ℝ)/8000000), ((-1686668192349147:ℝ)/1000000), ((-42123144329301:ℝ)/100000), ((-37506757011:ℝ)/500), ((-933542163:ℝ)/100), ((-3866334:ℝ)/5), ((-191844:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0) 12 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 8, ([((-132694004686587:ℝ)/80000000), ((-10436607110181:ℝ)/4000000), ((-351795745287:ℝ)/200000), ((-1317587061:ℝ)/2000), ((-14804349:ℝ)/100), ((-499023:ℝ)/25), ((-7476:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0 * t^e) - (((-132694004686587:ℝ)/80000000) + ((-10436607110181:ℝ)/4000000)*t)| ≤ ((11201818851:ℝ)/2500000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 12, ([((-46673427351909331057251:ℝ)/12800000000000), ((-3240154871526392359647:ℝ)/320000000000), ((-81577270130949038601:ℝ)/6400000000), ((-1536833754435115131:ℝ)/160000000), ((-38523246490759323:ℝ)/8000000), ((-1686668192349147:ℝ)/1000000), ((-42123144329301:ℝ)/100000), ((-37506757011:ℝ)/500), ((-933542163:ℝ)/100), ((-3866334:ℝ)/5), ((-191844:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e) - ((-46673427351909331057251:ℝ)/12800000000000) - ((-3240154871526392359647:ℝ)/320000000000)*t| ≤ ((84729350467576844691:ℝ)/2560000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 12, ([((-46673427351909331057251:ℝ)/12800000000000), ((-3240154871526392359647:ℝ)/320000000000), ((-81577270130949038601:ℝ)/6400000000), ((-1536833754435115131:ℝ)/160000000), ((-38523246490759323:ℝ)/8000000), ((-1686668192349147:ℝ)/1000000), ((-42123144329301:ℝ)/100000), ((-37506757011:ℝ)/500), ((-933542163:ℝ)/100), ((-3866334:ℝ)/5), ((-191844:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((535773838473:ℝ)/128) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((153969276771336449:ℝ)/16000000000) - ((17329240634519109:ℝ)/800000000)*t| ≤ ((444183297072221:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((9:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-6288:ℝ), (81024:ℝ), (-238720:ℝ), (246784:ℝ), (-98304:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m13' : |centralNum13_01 q| ≤ ((20328799643343:ℝ)/8) := by
    rw [centralNum13_01_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((9:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-7368:ℝ), (59208:ℝ), (-155734:ℝ), (205300:ℝ), (-60000:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m23' : |centralNum23_01 q| ≤ ((111775904938485:ℝ)/64) := by
    rw [centralNum23_01_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece17_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece17_E11 h0) m23'
  have c5 := scaled_affine (X := ((-117570972237:ℝ)/100000000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-132694004686587:ℝ)/80000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((-46673427351909331057251:ℝ)/12800000000000) + ((153969276771336449:ℝ)/16000000000)*((-117570972237:ℝ)/100000000000000000) - ((-42628764083640127:ℝ)/25000000000)) (β := ((-10436607110181:ℝ)/4000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((-3240154871526392359647:ℝ)/320000000000) - 3*((-46673427351909331057251:ℝ)/12800000000000)) + ((17329240634519109:ℝ)/800000000)*((-117570972237:ℝ)/100000000000000000) - ((-259880984430167821:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_17 0 1 = centralNum11_01 q + 8*(Real.exp (-(3*((89:ℝ)/20)))*Real.exp (-3*t))*centralNum12_01 q + 18*Real.exp (-8*q)*centralNum13_01 q + 72*Real.exp (-11*q)*centralNum23_01 q + 8*q^7*(2*q-3)^2*((-117570972237:ℝ)/100000000000000000) + (0:ℝ) := by
    rw [pieceW_01, pieceX_17, sym4_01, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((459303582059666015122374141944429396831441118399275137736347523344577909727:ℝ)/315320823522399258391072236744610841832043167569496856749959200000000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-132694004686587:ℝ)/80000000) + ((-10436607110181:ℝ)/4000000)*t) + (8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((-46673427351909331057251:ℝ)/12800000000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((-3240154871526392359647:ℝ)/320000000000) - 3*((-46673427351909331057251:ℝ)/12800000000000))*t) + (((153969276771336449:ℝ)/16000000000) + ((17329240634519109:ℝ)/800000000)*t)*((-117570972237:ℝ)/100000000000000000) - (((-42628764083640127:ℝ)/25000000000) + t * ((-259880984430167821:ℝ)/100000000000)) = (((-132694004686587:ℝ)/80000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((-46673427351909331057251:ℝ)/12800000000000) + ((153969276771336449:ℝ)/16000000000)*((-117570972237:ℝ)/100000000000000000) - ((-42628764083640127:ℝ)/25000000000)) + t*(((-10436607110181:ℝ)/4000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((-3240154871526392359647:ℝ)/320000000000) - 3*((-46673427351909331057251:ℝ)/12800000000000)) + ((17329240634519109:ℝ)/800000000)*((-117570972237:ℝ)/100000000000000000) - ((-259880984430167821:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece17_e02 {q : ℝ} (h0 : ((22:ℝ)/5) ≤ q) (h1 : q ≤ ((9:ℝ)/2)) :
    |pieceW q pieceX_17 0 2 - (((-275543473991665017:ℝ)/10000000000000) + (q - ((89:ℝ)/20)) * ((-602518226650085231:ℝ)/10000000000000))| ≤ ((270482367695097213:ℝ)/100000000000000) := by
  set t := q - ((89:ℝ)/20) with htd
  have hq : q = ((89:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece17_L3 piece17_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((89:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_02 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_02; ring
  have h12 : centralNum12_02 q = ∑ e ∈ Finset.range 13, ([((-4435130789708718367779831:ℝ)/2048000000000000), ((-1150195608569581193155473:ℝ)/102400000000000), ((-110241529265444696512551:ℝ)/5120000000000), ((-1162574701423314173631:ℝ)/51200000000), ((-9791864021867315121:ℝ)/640000000), ((-2264702624640794349:ℝ)/320000000), ((-37270793294729127:ℝ)/16000000), ((-442629528473619:ℝ)/800000), ((-1512257454099:ℝ)/16000), ((-9085418721:ℝ)/800), ((-182581371:ℝ)/200), ((-441423:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_02; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-4435130789708718367779831:ℝ)/2048000000000000), ((-1150195608569581193155473:ℝ)/102400000000000), ((-110241529265444696512551:ℝ)/5120000000000), ((-1162574701423314173631:ℝ)/51200000000), ((-9791864021867315121:ℝ)/640000000), ((-2264702624640794349:ℝ)/320000000), ((-37270793294729127:ℝ)/16000000), ((-442629528473619:ℝ)/800000), ((-1512257454099:ℝ)/16000), ((-9085418721:ℝ)/800), ((-182581371:ℝ)/200), ((-441423:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((-4435130789708718367779831:ℝ)/2048000000000000), ((-1150195608569581193155473:ℝ)/102400000000000), ((-110241529265444696512551:ℝ)/5120000000000), ((-1162574701423314173631:ℝ)/51200000000), ((-9791864021867315121:ℝ)/640000000), ((-2264702624640794349:ℝ)/320000000), ((-37270793294729127:ℝ)/16000000), ((-442629528473619:ℝ)/800000), ((-1512257454099:ℝ)/16000), ((-9085418721:ℝ)/800), ((-182581371:ℝ)/200), ((-441423:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((-4435130789708718367779831:ℝ)/2048000000000000), ((-1150195608569581193155473:ℝ)/102400000000000), ((-110241529265444696512551:ℝ)/5120000000000), ((-1162574701423314173631:ℝ)/51200000000), ((-9791864021867315121:ℝ)/640000000), ((-2264702624640794349:ℝ)/320000000), ((-37270793294729127:ℝ)/16000000), ((-442629528473619:ℝ)/800000), ((-1512257454099:ℝ)/16000), ((-9085418721:ℝ)/800), ((-182581371:ℝ)/200), ((-441423:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e) - ((-4435130789708718367779831:ℝ)/2048000000000000) - ((-1150195608569581193155473:ℝ)/102400000000000)*t| ≤ ((14531855611587554883087:ℝ)/256000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((-4435130789708718367779831:ℝ)/2048000000000000), ((-1150195608569581193155473:ℝ)/102400000000000), ((-110241529265444696512551:ℝ)/5120000000000), ((-1162574701423314173631:ℝ)/51200000000), ((-9791864021867315121:ℝ)/640000000), ((-2264702624640794349:ℝ)/320000000), ((-37270793294729127:ℝ)/16000000), ((-442629528473619:ℝ)/800000), ((-1512257454099:ℝ)/16000), ((-9085418721:ℝ)/800), ((-182581371:ℝ)/200), ((-441423:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((5701581243171:ℝ)/2048) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((153969276771336449:ℝ)/16000000000) - ((17329240634519109:ℝ)/800000000)*t| ≤ ((444183297072221:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((9:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82080:ℝ), (-967680:ℝ), (3257600:ℝ), (-4474880:ℝ), (2908160:ℝ), (-786432:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_02 q| ≤ ((466622280108063:ℝ)/4) := by
    rw [centralNum13_02_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((9:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (87660:ℝ), (-702180:ℝ), ((7421435:ℝ)/4), ((-10854125:ℝ)/4), ((2828125:ℝ)/2), (-187500:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_02 q| ≤ ((46449641133446985:ℝ)/1024) := by
    rw [centralNum23_02_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece17_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece17_E11 h0) m23'
  have c5 := scaled_affine (X := ((425575559063:ℝ)/100000000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((-4435130789708718367779831:ℝ)/2048000000000000) + ((153969276771336449:ℝ)/16000000000)*((425575559063:ℝ)/100000000000000000) - ((-275543473991665017:ℝ)/10000000000000)) (β := (0:ℝ) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((-1150195608569581193155473:ℝ)/102400000000000) - 3*((-4435130789708718367779831:ℝ)/2048000000000000)) + ((17329240634519109:ℝ)/800000000)*((425575559063:ℝ)/100000000000000000) - ((-602518226650085231:ℝ)/10000000000000)) ht
  have hW : pieceW q pieceX_17 0 2 = centralNum11_02 q + 8*(Real.exp (-(3*((89:ℝ)/20)))*Real.exp (-3*t))*centralNum12_02 q + 18*Real.exp (-8*q)*centralNum13_02 q + 72*Real.exp (-11*q)*centralNum23_02 q + 8*q^7*(2*q-3)^2*((425575559063:ℝ)/100000000000000000) + (0:ℝ) := by
    rw [pieceW_02, pieceX_17, sym4_02, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((233970599101061884684215609780936561337211431613941077256063631432678829:ℝ)/31532082352239925839107223674461084183204316756949685674995920000000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((-4435130789708718367779831:ℝ)/2048000000000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((-1150195608569581193155473:ℝ)/102400000000000) - 3*((-4435130789708718367779831:ℝ)/2048000000000000))*t) + (((153969276771336449:ℝ)/16000000000) + ((17329240634519109:ℝ)/800000000)*t)*((425575559063:ℝ)/100000000000000000) - (((-275543473991665017:ℝ)/10000000000000) + t * ((-602518226650085231:ℝ)/10000000000000)) = ((0:ℝ) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((-4435130789708718367779831:ℝ)/2048000000000000) + ((153969276771336449:ℝ)/16000000000)*((425575559063:ℝ)/100000000000000000) - ((-275543473991665017:ℝ)/10000000000000)) + t*((0:ℝ) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((-1150195608569581193155473:ℝ)/102400000000000) - 3*((-4435130789708718367779831:ℝ)/2048000000000000)) + ((17329240634519109:ℝ)/800000000)*((425575559063:ℝ)/100000000000000000) - ((-602518226650085231:ℝ)/10000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece17_e03 {q : ℝ} (h0 : ((22:ℝ)/5) ≤ q) (h1 : q ≤ ((9:ℝ)/2)) :
    |pieceW q pieceX_17 0 3 - (((60034209397797821:ℝ)/500000000000) + (q - ((89:ℝ)/20)) * ((-49510460738065469:ℝ)/1000000000000))| ≤ ((12758010308997551:ℝ)/2000000000000) := by
  set t := q - ((89:ℝ)/20) with htd
  have hq : q = ((89:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece17_L3 piece17_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((89:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_03 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_03; ring
  have h12 : centralNum12_03 q = ∑ e ∈ Finset.range 14, ([((5409521858106601380013453029:ℝ)/573440000000000000), ((175181760895471690732612857:ℝ)/7168000000000000), ((8987823610784622539626563:ℝ)/358400000000000), ((378803712887139943081593:ℝ)/35840000000000), ((-1548455306231330436123:ℝ)/716800000000), ((-477492531930668977299:ℝ)/89600000000), ((-939900385111451103:ℝ)/280000000), ((-141639594651431811:ℝ)/112000000), ((-7220576144870937:ℝ)/22400000), ((-1605490665669:ℝ)/28000), ((-98859092139:ℝ)/14000), ((-807230691:ℝ)/1400), ((-3944133:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_03; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((5409521858106601380013453029:ℝ)/573440000000000000), ((175181760895471690732612857:ℝ)/7168000000000000), ((8987823610784622539626563:ℝ)/358400000000000), ((378803712887139943081593:ℝ)/35840000000000), ((-1548455306231330436123:ℝ)/716800000000), ((-477492531930668977299:ℝ)/89600000000), ((-939900385111451103:ℝ)/280000000), ((-141639594651431811:ℝ)/112000000), ((-7220576144870937:ℝ)/22400000), ((-1605490665669:ℝ)/28000), ((-98859092139:ℝ)/14000), ((-807230691:ℝ)/1400), ((-3944133:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((5409521858106601380013453029:ℝ)/573440000000000000), ((175181760895471690732612857:ℝ)/7168000000000000), ((8987823610784622539626563:ℝ)/358400000000000), ((378803712887139943081593:ℝ)/35840000000000), ((-1548455306231330436123:ℝ)/716800000000), ((-477492531930668977299:ℝ)/89600000000), ((-939900385111451103:ℝ)/280000000), ((-141639594651431811:ℝ)/112000000), ((-7220576144870937:ℝ)/22400000), ((-1605490665669:ℝ)/28000), ((-98859092139:ℝ)/14000), ((-807230691:ℝ)/1400), ((-3944133:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((5409521858106601380013453029:ℝ)/573440000000000000), ((175181760895471690732612857:ℝ)/7168000000000000), ((8987823610784622539626563:ℝ)/358400000000000), ((378803712887139943081593:ℝ)/35840000000000), ((-1548455306231330436123:ℝ)/716800000000), ((-477492531930668977299:ℝ)/89600000000), ((-939900385111451103:ℝ)/280000000), ((-141639594651431811:ℝ)/112000000), ((-7220576144870937:ℝ)/22400000), ((-1605490665669:ℝ)/28000), ((-98859092139:ℝ)/14000), ((-807230691:ℝ)/1400), ((-3944133:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((5409521858106601380013453029:ℝ)/573440000000000000) - ((175181760895471690732612857:ℝ)/7168000000000000)*t| ≤ ((36717629781163683033243333:ℝ)/573440000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((5409521858106601380013453029:ℝ)/573440000000000000), ((175181760895471690732612857:ℝ)/7168000000000000), ((8987823610784622539626563:ℝ)/358400000000000), ((378803712887139943081593:ℝ)/35840000000000), ((-1548455306231330436123:ℝ)/716800000000), ((-477492531930668977299:ℝ)/89600000000), ((-939900385111451103:ℝ)/280000000), ((-141639594651431811:ℝ)/112000000), ((-7220576144870937:ℝ)/22400000), ((-1605490665669:ℝ)/28000), ((-98859092139:ℝ)/14000), ((-807230691:ℝ)/1400), ((-3944133:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((614696653146965182597714779:ℝ)/57344000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((153969276771336449:ℝ)/16000000000) - ((17329240634519109:ℝ)/800000000)*t| ≤ ((444183297072221:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((9:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-812160:ℝ), (8985600:ℝ), (-32225280:ℝ), (52019200:ℝ), ((-305233920:ℝ)/7), ((135528448:ℝ)/7), ((-25165824:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_03 q| ≤ ((23252052718792431:ℝ)/7) := by
    rw [centralNum13_03_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((9:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-833220:ℝ), (6469740:ℝ), ((-68603955:ℝ)/4), ((104396875:ℝ)/4), ((-1001334375:ℝ)/56), ((125828125:ℝ)/28), ((-2343750:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_03 q| ≤ ((22671127877974207605:ℝ)/28672) := by
    rw [centralNum23_03_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece17_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece17_E11 h0) m23'
  have c5 := scaled_affine (X := ((-35987352907:ℝ)/2500000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((5409521858106601380013453029:ℝ)/573440000000000000) + ((153969276771336449:ℝ)/16000000000)*((-35987352907:ℝ)/2500000000000000) - ((60034209397797821:ℝ)/500000000000)) (β := (0:ℝ) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((175181760895471690732612857:ℝ)/7168000000000000) - 3*((5409521858106601380013453029:ℝ)/573440000000000000)) + ((17329240634519109:ℝ)/800000000)*((-35987352907:ℝ)/2500000000000000) - ((-49510460738065469:ℝ)/1000000000000)) ht
  have hW : pieceW q pieceX_17 0 3 = centralNum11_03 q + 8*(Real.exp (-(3*((89:ℝ)/20)))*Real.exp (-3*t))*centralNum12_03 q + 18*Real.exp (-8*q)*centralNum13_03 q + 72*Real.exp (-11*q)*centralNum23_03 q + 8*q^7*(2*q-3)^2*((-35987352907:ℝ)/2500000000000000) + (0:ℝ) := by
    rw [pieceW_03, pieceX_17, sym4_03, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((1375907948365745721153050194566767057137202007242768691968636211050943703:ℝ)/7883020588059981459776805918615271045801079189237421418748980000000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((5409521858106601380013453029:ℝ)/573440000000000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((175181760895471690732612857:ℝ)/7168000000000000) - 3*((5409521858106601380013453029:ℝ)/573440000000000000))*t) + (((153969276771336449:ℝ)/16000000000) + ((17329240634519109:ℝ)/800000000)*t)*((-35987352907:ℝ)/2500000000000000) - (((60034209397797821:ℝ)/500000000000) + t * ((-49510460738065469:ℝ)/1000000000000)) = ((0:ℝ) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((5409521858106601380013453029:ℝ)/573440000000000000) + ((153969276771336449:ℝ)/16000000000)*((-35987352907:ℝ)/2500000000000000) - ((60034209397797821:ℝ)/500000000000)) + t*((0:ℝ) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((175181760895471690732612857:ℝ)/7168000000000000) - 3*((5409521858106601380013453029:ℝ)/573440000000000000)) + ((17329240634519109:ℝ)/800000000)*((-35987352907:ℝ)/2500000000000000) - ((-49510460738065469:ℝ)/1000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece17_e11 {q : ℝ} (h0 : ((22:ℝ)/5) ≤ q) (h1 : q ≤ ((9:ℝ)/2)) :
    |pieceW q pieceX_17 1 1 - (((840550614921579849:ℝ)/100000000000) + (q - ((89:ℝ)/20)) * ((3426844346515487:ℝ)/200000000))| ≤ ((422548153020730473:ℝ)/10000000000000) := by
  set t := q - ((89:ℝ)/20) with htd
  have hq : q = ((89:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece17_L3 piece17_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((89:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_11 q = ∑ e ∈ Finset.range 10, ([((99345069119231017:ℝ)/12000000000), ((6786346536785843:ℝ)/400000000), ((78431377557737:ℝ)/5000000), ((2146230887577:ℝ)/250000), ((19136589451:ℝ)/6250), ((921109861:ℝ)/1250), ((14931532:ℝ)/125), ((313808:ℝ)/25), ((3872:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_11; ring
  have h12 : centralNum12_11 q = ∑ e ∈ Finset.range 13, ([((1556907438499939629027929:ℝ)/1536000000000000), ((-98717459527653899604811:ℝ)/25600000000000), ((-18388473967057814099917:ℝ)/1280000000000), ((-246006540712051958037:ℝ)/12800000000), ((-2357950382103783827:ℝ)/160000000), ((-592982583309518303:ℝ)/80000000), ((-10362287435810989:ℝ)/4000000), ((-128846610910673:ℝ)/200000), ((-456715679873:ℝ)/4000), ((-8486682481:ℝ)/600), ((-58343337:ℝ)/50), ((-288522:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_11; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((99345069119231017:ℝ)/12000000000), ((6786346536785843:ℝ)/400000000), ((78431377557737:ℝ)/5000000), ((2146230887577:ℝ)/250000), ((19136589451:ℝ)/6250), ((921109861:ℝ)/1250), ((14931532:ℝ)/125), ((313808:ℝ)/25), ((3872:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((1556907438499939629027929:ℝ)/1536000000000000), ((-98717459527653899604811:ℝ)/25600000000000), ((-18388473967057814099917:ℝ)/1280000000000), ((-246006540712051958037:ℝ)/12800000000), ((-2357950382103783827:ℝ)/160000000), ((-592982583309518303:ℝ)/80000000), ((-10362287435810989:ℝ)/4000000), ((-128846610910673:ℝ)/200000), ((-456715679873:ℝ)/4000), ((-8486682481:ℝ)/600), ((-58343337:ℝ)/50), ((-288522:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((1556907438499939629027929:ℝ)/1536000000000000), ((-98717459527653899604811:ℝ)/25600000000000), ((-18388473967057814099917:ℝ)/1280000000000), ((-246006540712051958037:ℝ)/12800000000), ((-2357950382103783827:ℝ)/160000000), ((-592982583309518303:ℝ)/80000000), ((-10362287435810989:ℝ)/4000000), ((-128846610910673:ℝ)/200000), ((-456715679873:ℝ)/4000), ((-8486682481:ℝ)/600), ((-58343337:ℝ)/50), ((-288522:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((99345069119231017:ℝ)/12000000000), ((6786346536785843:ℝ)/400000000), ((78431377557737:ℝ)/5000000), ((2146230887577:ℝ)/250000), ((19136589451:ℝ)/6250), ((921109861:ℝ)/1250), ((14931532:ℝ)/125), ((313808:ℝ)/25), ((3872:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((99345069119231017:ℝ)/12000000000) + ((6786346536785843:ℝ)/400000000)*t)| ≤ ((967396151180437:ℝ)/24000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((1556907438499939629027929:ℝ)/1536000000000000), ((-98717459527653899604811:ℝ)/25600000000000), ((-18388473967057814099917:ℝ)/1280000000000), ((-246006540712051958037:ℝ)/12800000000), ((-2357950382103783827:ℝ)/160000000), ((-592982583309518303:ℝ)/80000000), ((-10362287435810989:ℝ)/4000000), ((-128846610910673:ℝ)/200000), ((-456715679873:ℝ)/4000), ((-8486682481:ℝ)/600), ((-58343337:ℝ)/50), ((-288522:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e) - ((1556907438499939629027929:ℝ)/1536000000000000) - ((-98717459527653899604811:ℝ)/25600000000000)*t| ≤ ((7375077235497241276687:ℝ)/192000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((1556907438499939629027929:ℝ)/1536000000000000), ((-98717459527653899604811:ℝ)/25600000000000), ((-18388473967057814099917:ℝ)/1280000000000), ((-246006540712051958037:ℝ)/12800000000), ((-2357950382103783827:ℝ)/160000000), ((-592982583309518303:ℝ)/80000000), ((-10362287435810989:ℝ)/4000000), ((-128846610910673:ℝ)/200000), ((-456715679873:ℝ)/4000), ((-8486682481:ℝ)/600), ((-58343337:ℝ)/50), ((-288522:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((956030217483439629027929:ℝ)/768000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((153969276771336449:ℝ)/16000000000) - ((17329240634519109:ℝ)/800000000)*t| ≤ ((444183297072221:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((9:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-3444:ℝ), (162624:ℝ), (-1531216:ℝ), (4800960:ℝ), (-6350848:ℝ), ((12025856:ℝ)/3), (-1048576:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_11 q| ≤ ((318493133901261:ℝ)/2) := by
    rw [centralNum13_11_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((9:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-4074:ℝ), (159906:ℝ), (-1104799:ℝ), (2801499:ℝ), (-3931375:ℝ), ((5896250:ℝ)/3), (-250000:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_11 q| ≤ ((16141308302099511:ℝ)/256) := by
    rw [centralNum23_11_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece17_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece17_E11 h0) m23'
  have c5 := scaled_affine (X := ((118293027137:ℝ)/10000000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1))| ≤ ((3611058102300000000000000:ℝ)/27486877888415324817721107991) := by
    rw [abs_neg, tailWeight_1, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((9:ℝ)/2)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((9:ℝ)/2)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece17_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((4814744136400:ℝ)/531441)) ≤ ((9:ℝ)/2)^6*(8000*(2*((9:ℝ)/2)-3)^2*(1/((82460633665245974453163323973:ℝ)/500000000))*((4814744136400:ℝ)/531441)) := by
          gcongr
      _ ≤ ((3611058102300000000000000:ℝ)/27486877888415324817721107991) := by norm_num
  have c7 := affine_round (α := ((99345069119231017:ℝ)/12000000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((1556907438499939629027929:ℝ)/1536000000000000) + ((153969276771336449:ℝ)/16000000000)*((118293027137:ℝ)/10000000000000) - ((840550614921579849:ℝ)/100000000000)) (β := ((6786346536785843:ℝ)/400000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((-98717459527653899604811:ℝ)/25600000000000) - 3*((1556907438499939629027929:ℝ)/1536000000000000)) + ((17329240634519109:ℝ)/800000000)*((118293027137:ℝ)/10000000000000) - ((3426844346515487:ℝ)/200000000)) ht
  have hW : pieceW q pieceX_17 1 1 = centralNum11_11 q + 8*(Real.exp (-(3*((89:ℝ)/20)))*Real.exp (-3*t))*centralNum12_11 q + 18*Real.exp (-8*q)*centralNum13_11 q + 72*Real.exp (-11*q)*centralNum23_11 q + 8*q^7*(2*q-3)^2*((118293027137:ℝ)/10000000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1)) := by
    rw [pieceW_11, pieceX_17, sym4_11, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((37250933509722099152443890980123018120875040038661001217423839912447313:ℝ)/9459624705671977751732167102338325254961295027084905702498776000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((99345069119231017:ℝ)/12000000000) + ((6786346536785843:ℝ)/400000000)*t) + (8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((1556907438499939629027929:ℝ)/1536000000000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((-98717459527653899604811:ℝ)/25600000000000) - 3*((1556907438499939629027929:ℝ)/1536000000000000))*t) + (((153969276771336449:ℝ)/16000000000) + ((17329240634519109:ℝ)/800000000)*t)*((118293027137:ℝ)/10000000000000) - (((840550614921579849:ℝ)/100000000000) + t * ((3426844346515487:ℝ)/200000000)) = (((99345069119231017:ℝ)/12000000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((1556907438499939629027929:ℝ)/1536000000000000) + ((153969276771336449:ℝ)/16000000000)*((118293027137:ℝ)/10000000000000) - ((840550614921579849:ℝ)/100000000000)) + t*(((6786346536785843:ℝ)/400000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((-98717459527653899604811:ℝ)/25600000000000) - 3*((1556907438499939629027929:ℝ)/1536000000000000)) + ((17329240634519109:ℝ)/800000000)*((118293027137:ℝ)/10000000000000) - ((3426844346515487:ℝ)/200000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece17_e12 {q : ℝ} (h0 : ((22:ℝ)/5) ≤ q) (h1 : q ≤ ((9:ℝ)/2)) :
    |pieceW q pieceX_17 1 2 - (((-134307922101684291:ℝ)/200000000000) + (q - ((89:ℝ)/20)) * ((-129300189364154979:ℝ)/100000000000))| ≤ ((197303102443905141:ℝ)/10000000000000) := by
  set t := q - ((89:ℝ)/20) with htd
  have hq : q = ((89:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece17_L3 piece17_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((89:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_12 q = ∑ e ∈ Finset.range 9, ([((-1788635666168639:ℝ)/1920000000), ((-30394035580907:ℝ)/24000000), ((-739291825703:ℝ)/1200000), ((-4780394789:ℝ)/60000), ((48531967:ℝ)/1200), ((2984971:ℝ)/150), ((57074:ℝ)/15), ((1064:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_12; ring
  have h12 : centralNum12_12 q = ∑ e ∈ Finset.range 14, ([((5572409259893828293776474149:ℝ)/245760000000000000), ((218232752582897614390541897:ℝ)/3072000000000000), ((14401025372350367897434643:ℝ)/153600000000000), ((1028447890814436287602393:ℝ)/15360000000000), ((7939875640472186473957:ℝ)/307200000000), ((103760140467798603181:ℝ)/38400000000), ((-314312002821332363:ℝ)/120000000), ((-79916434384276771:ℝ)/48000000), ((-5041484933944537:ℝ)/9600000), ((-422816859743:ℝ)/4000), ((-28314668553:ℝ)/2000), ((-246081537:ℝ)/200), ((-1262871:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_12; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-1788635666168639:ℝ)/1920000000), ((-30394035580907:ℝ)/24000000), ((-739291825703:ℝ)/1200000), ((-4780394789:ℝ)/60000), ((48531967:ℝ)/1200), ((2984971:ℝ)/150), ((57074:ℝ)/15), ((1064:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((5572409259893828293776474149:ℝ)/245760000000000000), ((218232752582897614390541897:ℝ)/3072000000000000), ((14401025372350367897434643:ℝ)/153600000000000), ((1028447890814436287602393:ℝ)/15360000000000), ((7939875640472186473957:ℝ)/307200000000), ((103760140467798603181:ℝ)/38400000000), ((-314312002821332363:ℝ)/120000000), ((-79916434384276771:ℝ)/48000000), ((-5041484933944537:ℝ)/9600000), ((-422816859743:ℝ)/4000), ((-28314668553:ℝ)/2000), ((-246081537:ℝ)/200), ((-1262871:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((5572409259893828293776474149:ℝ)/245760000000000000), ((218232752582897614390541897:ℝ)/3072000000000000), ((14401025372350367897434643:ℝ)/153600000000000), ((1028447890814436287602393:ℝ)/15360000000000), ((7939875640472186473957:ℝ)/307200000000), ((103760140467798603181:ℝ)/38400000000), ((-314312002821332363:ℝ)/120000000), ((-79916434384276771:ℝ)/48000000), ((-5041484933944537:ℝ)/9600000), ((-422816859743:ℝ)/4000), ((-28314668553:ℝ)/2000), ((-246081537:ℝ)/200), ((-1262871:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((-1788635666168639:ℝ)/1920000000), ((-30394035580907:ℝ)/24000000), ((-739291825703:ℝ)/1200000), ((-4780394789:ℝ)/60000), ((48531967:ℝ)/1200), ((2984971:ℝ)/150), ((57074:ℝ)/15), ((1064:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((-1788635666168639:ℝ)/1920000000) + ((-30394035580907:ℝ)/24000000)*t)| ≤ ((992262085401:ℝ)/640000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((5572409259893828293776474149:ℝ)/245760000000000000), ((218232752582897614390541897:ℝ)/3072000000000000), ((14401025372350367897434643:ℝ)/153600000000000), ((1028447890814436287602393:ℝ)/15360000000000), ((7939875640472186473957:ℝ)/307200000000), ((103760140467798603181:ℝ)/38400000000), ((-314312002821332363:ℝ)/120000000), ((-79916434384276771:ℝ)/48000000), ((-5041484933944537:ℝ)/9600000), ((-422816859743:ℝ)/4000), ((-28314668553:ℝ)/2000), ((-246081537:ℝ)/200), ((-1262871:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e) - ((5572409259893828293776474149:ℝ)/245760000000000000) - ((218232752582897614390541897:ℝ)/3072000000000000)*t| ≤ ((59700914552256032727680747:ℝ)/245760000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((5572409259893828293776474149:ℝ)/245760000000000000), ((218232752582897614390541897:ℝ)/3072000000000000), ((14401025372350367897434643:ℝ)/153600000000000), ((1028447890814436287602393:ℝ)/15360000000000), ((7939875640472186473957:ℝ)/307200000000), ((103760140467798603181:ℝ)/38400000000), ((-314312002821332363:ℝ)/120000000), ((-79916434384276771:ℝ)/48000000), ((-5041484933944537:ℝ)/9600000), ((-422816859743:ℝ)/4000), ((-28314668553:ℝ)/2000), ((-246081537:ℝ)/200), ((-1262871:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((542086765398139565338860207:ℝ)/20480000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((153969276771336449:ℝ)/16000000000) - ((17329240634519109:ℝ)/800000000)*t| ≤ ((444183297072221:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((9:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (122790:ℝ), (-3586680:ℝ), (28529720:ℝ), (-90761600:ℝ), (137804800:ℝ), ((-332136448:ℝ)/3), ((141819904:ℝ)/3), (-8388608:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_12 q| ≤ ((16203492361250109:ℝ)/2) := by
    rw [centralNum13_12_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((9:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (132555:ℝ), (-3252375:ℝ), ((39743695:ℝ)/2), ((-197111615:ℝ)/4), ((281947375:ℝ)/4), ((-1100234375:ℝ)/24), ((131828125:ℝ)/12), (-781250:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_12 q| ≤ ((8122814920280327175:ℝ)/4096) := by
    rw [centralNum23_12_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece17_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece17_E11 h0) m23'
  have c5 := scaled_affine (X := ((-150092730929:ℝ)/50000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-1788635666168639:ℝ)/1920000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((5572409259893828293776474149:ℝ)/245760000000000000) + ((153969276771336449:ℝ)/16000000000)*((-150092730929:ℝ)/50000000000000) - ((-134307922101684291:ℝ)/200000000000)) (β := ((-30394035580907:ℝ)/24000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((218232752582897614390541897:ℝ)/3072000000000000) - 3*((5572409259893828293776474149:ℝ)/245760000000000000)) + ((17329240634519109:ℝ)/800000000)*((-150092730929:ℝ)/50000000000000) - ((-129300189364154979:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_17 1 2 = centralNum11_12 q + 8*(Real.exp (-(3*((89:ℝ)/20)))*Real.exp (-3*t))*centralNum12_12 q + 18*Real.exp (-8*q)*centralNum13_12 q + 72*Real.exp (-11*q)*centralNum23_12 q + 8*q^7*(2*q-3)^2*((-150092730929:ℝ)/50000000000000) + (0:ℝ) := by
    rw [pieceW_12, pieceX_17, sym4_12, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((339292539946975551881247293700955101914819823543672953913066643832796223:ℝ)/472981235283598887586608355116916262748064751354245285124938800000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-1788635666168639:ℝ)/1920000000) + ((-30394035580907:ℝ)/24000000)*t) + (8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((5572409259893828293776474149:ℝ)/245760000000000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((218232752582897614390541897:ℝ)/3072000000000000) - 3*((5572409259893828293776474149:ℝ)/245760000000000000))*t) + (((153969276771336449:ℝ)/16000000000) + ((17329240634519109:ℝ)/800000000)*t)*((-150092730929:ℝ)/50000000000000) - (((-134307922101684291:ℝ)/200000000000) + t * ((-129300189364154979:ℝ)/100000000000)) = (((-1788635666168639:ℝ)/1920000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((5572409259893828293776474149:ℝ)/245760000000000000) + ((153969276771336449:ℝ)/16000000000)*((-150092730929:ℝ)/50000000000000) - ((-134307922101684291:ℝ)/200000000000)) + t*(((-30394035580907:ℝ)/24000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((218232752582897614390541897:ℝ)/3072000000000000) - 3*((5572409259893828293776474149:ℝ)/245760000000000000)) + ((17329240634519109:ℝ)/800000000)*((-150092730929:ℝ)/50000000000000) - ((-129300189364154979:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece17_e13 {q : ℝ} (h0 : ((22:ℝ)/5) ≤ q) (h1 : q ≤ ((9:ℝ)/2)) :
    |pieceW q pieceX_17 1 3 - (((-765861367716074391:ℝ)/1000000000000) + (q - ((89:ℝ)/20)) * ((37365680339362321:ℝ)/250000000000))| ≤ ((46515989568943053:ℝ)/2500000000000) := by
  set t := q - ((89:ℝ)/20) with htd
  have hq : q = ((89:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece17_L3 piece17_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((89:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_13 q = ∑ e ∈ Finset.range 7, ([((-1490943872883:ℝ)/3200000), ((-50256535041:ℝ)/80000), ((-564680169:ℝ)/1600), ((-2114907:ℝ)/20), ((-71289:ℝ)/4), (-1602:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_13; ring
  have h12 : centralNum12_13 q = ∑ e ∈ Finset.range 15, ([((-715799415650953496260226801397:ℝ)/22937600000000000000), ((-57172695511265234999300251317:ℝ)/1146880000000000000), ((20556162975846724520321103:ℝ)/3584000000000000), ((110099868717047072091387729:ℝ)/1433600000000000), ((12537411440478580977800253:ℝ)/143360000000000), ((375938598886598660003169:ℝ)/7168000000000), ((3437781654605180456967:ℝ)/179200000000), ((2639112918574474293:ℝ)/640000000), ((273901728665535909:ℝ)/896000000), ((-4657866532780131:ℝ)/44800000), ((-22419154379943:ℝ)/560000), ((-384372884871:ℝ)/56000), ((-3823614477:ℝ)/5600), ((-10696617:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_13; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-1490943872883:ℝ)/3200000), ((-50256535041:ℝ)/80000), ((-564680169:ℝ)/1600), ((-2114907:ℝ)/20), ((-71289:ℝ)/4), (-1602:ℝ), (-60:ℝ)] : List ℝ).getD e 0) 5 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-715799415650953496260226801397:ℝ)/22937600000000000000), ((-57172695511265234999300251317:ℝ)/1146880000000000000), ((20556162975846724520321103:ℝ)/3584000000000000), ((110099868717047072091387729:ℝ)/1433600000000000), ((12537411440478580977800253:ℝ)/143360000000000), ((375938598886598660003169:ℝ)/7168000000000), ((3437781654605180456967:ℝ)/179200000000), ((2639112918574474293:ℝ)/640000000), ((273901728665535909:ℝ)/896000000), ((-4657866532780131:ℝ)/44800000), ((-22419154379943:ℝ)/560000), ((-384372884871:ℝ)/56000), ((-3823614477:ℝ)/5600), ((-10696617:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-715799415650953496260226801397:ℝ)/22937600000000000000), ((-57172695511265234999300251317:ℝ)/1146880000000000000), ((20556162975846724520321103:ℝ)/3584000000000000), ((110099868717047072091387729:ℝ)/1433600000000000), ((12537411440478580977800253:ℝ)/143360000000000), ((375938598886598660003169:ℝ)/7168000000000), ((3437781654605180456967:ℝ)/179200000000), ((2639112918574474293:ℝ)/640000000), ((273901728665535909:ℝ)/896000000), ((-4657866532780131:ℝ)/44800000), ((-22419154379943:ℝ)/560000), ((-384372884871:ℝ)/56000), ((-3823614477:ℝ)/5600), ((-10696617:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 7, ([((-1490943872883:ℝ)/3200000), ((-50256535041:ℝ)/80000), ((-564680169:ℝ)/1600), ((-2114907:ℝ)/20), ((-71289:ℝ)/4), (-1602:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e) - (((-1490943872883:ℝ)/3200000) + ((-50256535041:ℝ)/80000)*t)| ≤ ((573211407:ℝ)/640000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-715799415650953496260226801397:ℝ)/22937600000000000000), ((-57172695511265234999300251317:ℝ)/1146880000000000000), ((20556162975846724520321103:ℝ)/3584000000000000), ((110099868717047072091387729:ℝ)/1433600000000000), ((12537411440478580977800253:ℝ)/143360000000000), ((375938598886598660003169:ℝ)/7168000000000), ((3437781654605180456967:ℝ)/179200000000), ((2639112918574474293:ℝ)/640000000), ((273901728665535909:ℝ)/896000000), ((-4657866532780131:ℝ)/44800000), ((-22419154379943:ℝ)/560000), ((-384372884871:ℝ)/56000), ((-3823614477:ℝ)/5600), ((-10696617:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((-715799415650953496260226801397:ℝ)/22937600000000000000) - ((-57172695511265234999300251317:ℝ)/1146880000000000000)*t| ≤ ((140504661206031972746960109:ℝ)/5734400000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-715799415650953496260226801397:ℝ)/22937600000000000000), ((-57172695511265234999300251317:ℝ)/1146880000000000000), ((20556162975846724520321103:ℝ)/3584000000000000), ((110099868717047072091387729:ℝ)/1433600000000000), ((12537411440478580977800253:ℝ)/143360000000000), ((375938598886598660003169:ℝ)/7168000000000), ((3437781654605180456967:ℝ)/179200000000), ((2639112918574474293:ℝ)/640000000), ((273901728665535909:ℝ)/896000000), ((-4657866532780131:ℝ)/44800000), ((-22419154379943:ℝ)/560000), ((-384372884871:ℝ)/56000), ((-3823614477:ℝ)/5600), ((-10696617:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((15470682596140857183010297863:ℝ)/458752000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((153969276771336449:ℝ)/16000000000) - ((17329240634519109:ℝ)/800000000)*t| ≤ ((444183297072221:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((9:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2325540:ℝ), (52589280:ℝ), (-375655200:ℝ), (1192958720:ℝ), (-1965096960:ℝ), ((12857851904:ℝ)/7), ((-21171273728:ℝ)/21), ((914358272:ℝ)/3), ((-268435456:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_13 q| ≤ ((28384740514486467513:ℝ)/112) := by
    rw [centralNum13_13_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((9:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2399070:ℝ), (45666930:ℝ), (-251781675:ℝ), ((2452738385:ℝ)/4), ((-14104310625:ℝ)/16), ((74345740625:ℝ)/112), ((-74899765625:ℝ)/336), ((5161328125:ℝ)/168), ((-9765625:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_13 q| ≤ ((664079613349595002425:ℝ)/16384) := by
    rw [centralNum23_13_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece17_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece17_E11 h0) m23'
  have c5 := scaled_affine (X := ((101536659457:ℝ)/10000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-1490943872883:ℝ)/3200000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((-715799415650953496260226801397:ℝ)/22937600000000000000) + ((153969276771336449:ℝ)/16000000000)*((101536659457:ℝ)/10000000000000) - ((-765861367716074391:ℝ)/1000000000000)) (β := ((-50256535041:ℝ)/80000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((-57172695511265234999300251317:ℝ)/1146880000000000000) - 3*((-715799415650953496260226801397:ℝ)/22937600000000000000)) + ((17329240634519109:ℝ)/800000000)*((101536659457:ℝ)/10000000000000) - ((37365680339362321:ℝ)/250000000000)) ht
  have hW : pieceW q pieceX_17 1 3 = centralNum11_13 q + 8*(Real.exp (-(3*((89:ℝ)/20)))*Real.exp (-3*t))*centralNum12_13 q + 18*Real.exp (-8*q)*centralNum13_13 q + 72*Real.exp (-11*q)*centralNum23_13 q + 8*q^7*(2*q-3)^2*((101536659457:ℝ)/10000000000000) + (0:ℝ) := by
    rw [pieceW_13, pieceX_17, sym4_13, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((1185952697341433630988310025912135531226518427664392137512683928277669:ℝ)/3153208235223992583910722367446108418320431675694968567499592000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-1490943872883:ℝ)/3200000) + ((-50256535041:ℝ)/80000)*t) + (8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((-715799415650953496260226801397:ℝ)/22937600000000000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((-57172695511265234999300251317:ℝ)/1146880000000000000) - 3*((-715799415650953496260226801397:ℝ)/22937600000000000000))*t) + (((153969276771336449:ℝ)/16000000000) + ((17329240634519109:ℝ)/800000000)*t)*((101536659457:ℝ)/10000000000000) - (((-765861367716074391:ℝ)/1000000000000) + t * ((37365680339362321:ℝ)/250000000000)) = (((-1490943872883:ℝ)/3200000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((-715799415650953496260226801397:ℝ)/22937600000000000000) + ((153969276771336449:ℝ)/16000000000)*((101536659457:ℝ)/10000000000000) - ((-765861367716074391:ℝ)/1000000000000)) + t*(((-50256535041:ℝ)/80000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((-57172695511265234999300251317:ℝ)/1146880000000000000) - 3*((-715799415650953496260226801397:ℝ)/22937600000000000000)) + ((17329240634519109:ℝ)/800000000)*((101536659457:ℝ)/10000000000000) - ((37365680339362321:ℝ)/250000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece17_e22 {q : ℝ} (h0 : ((22:ℝ)/5) ≤ q) (h1 : q ≤ ((9:ℝ)/2)) :
    |pieceW q pieceX_17 2 2 - (((13192956231803223:ℝ)/2000000000) + (q - ((89:ℝ)/20)) * ((85607919159253531:ℝ)/5000000000))| ≤ ((422574070070647497:ℝ)/5000000000000) := by
  set t := q - ((89:ℝ)/20) with htd
  have hq : q = ((89:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece17_L3 piece17_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((89:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_22 q = ∑ e ∈ Finset.range 10, ([((140361203097095899:ℝ)/19200000000), ((5044795095211003:ℝ)/320000000), ((181787634144691:ℝ)/12000000), ((5133358913471:ℝ)/600000), ((62821763479:ℝ)/20000), ((2337518363:ℝ)/3000), ((9801479:ℝ)/75), ((71412:ℝ)/5), ((2764:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_22; ring
  have h12 : centralNum12_22 q = ∑ e ∈ Finset.range 15, ([((-2852602244696682596459368856431:ℝ)/39321600000000000000), ((-97219518787524951859194087077:ℝ)/655360000000000000), ((-237962213374340353854878093:ℝ)/3072000000000000), ((160516030608548244066769307:ℝ)/2457600000000000), ((9931588521743579956129053:ℝ)/81920000000000), ((1038825645558050686184387:ℝ)/12288000000000), ((10496105032211302553381:ℝ)/307200000000), ((21201996678320686571:ℝ)/2560000000), ((1441113826595295647:ℝ)/1536000000), ((-7157601907236793:ℝ)/76800000), ((-18384043025163:ℝ)/320000), ((-347681711151:ℝ)/32000), ((-3628099917:ℝ)/3200), ((-10463337:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_22; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((140361203097095899:ℝ)/19200000000), ((5044795095211003:ℝ)/320000000), ((181787634144691:ℝ)/12000000), ((5133358913471:ℝ)/600000), ((62821763479:ℝ)/20000), ((2337518363:ℝ)/3000), ((9801479:ℝ)/75), ((71412:ℝ)/5), ((2764:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-2852602244696682596459368856431:ℝ)/39321600000000000000), ((-97219518787524951859194087077:ℝ)/655360000000000000), ((-237962213374340353854878093:ℝ)/3072000000000000), ((160516030608548244066769307:ℝ)/2457600000000000), ((9931588521743579956129053:ℝ)/81920000000000), ((1038825645558050686184387:ℝ)/12288000000000), ((10496105032211302553381:ℝ)/307200000000), ((21201996678320686571:ℝ)/2560000000), ((1441113826595295647:ℝ)/1536000000), ((-7157601907236793:ℝ)/76800000), ((-18384043025163:ℝ)/320000), ((-347681711151:ℝ)/32000), ((-3628099917:ℝ)/3200), ((-10463337:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-2852602244696682596459368856431:ℝ)/39321600000000000000), ((-97219518787524951859194087077:ℝ)/655360000000000000), ((-237962213374340353854878093:ℝ)/3072000000000000), ((160516030608548244066769307:ℝ)/2457600000000000), ((9931588521743579956129053:ℝ)/81920000000000), ((1038825645558050686184387:ℝ)/12288000000000), ((10496105032211302553381:ℝ)/307200000000), ((21201996678320686571:ℝ)/2560000000), ((1441113826595295647:ℝ)/1536000000), ((-7157601907236793:ℝ)/76800000), ((-18384043025163:ℝ)/320000), ((-347681711151:ℝ)/32000), ((-3628099917:ℝ)/3200), ((-10463337:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((140361203097095899:ℝ)/19200000000), ((5044795095211003:ℝ)/320000000), ((181787634144691:ℝ)/12000000), ((5133358913471:ℝ)/600000), ((62821763479:ℝ)/20000), ((2337518363:ℝ)/3000), ((9801479:ℝ)/75), ((71412:ℝ)/5), ((2764:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((140361203097095899:ℝ)/19200000000) + ((5044795095211003:ℝ)/320000000)*t)| ≤ ((187016404317773:ℝ)/4800000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-2852602244696682596459368856431:ℝ)/39321600000000000000), ((-97219518787524951859194087077:ℝ)/655360000000000000), ((-237962213374340353854878093:ℝ)/3072000000000000), ((160516030608548244066769307:ℝ)/2457600000000000), ((9931588521743579956129053:ℝ)/81920000000000), ((1038825645558050686184387:ℝ)/12288000000000), ((10496105032211302553381:ℝ)/307200000000), ((21201996678320686571:ℝ)/2560000000), ((1441113826595295647:ℝ)/1536000000), ((-7157601907236793:ℝ)/76800000), ((-18384043025163:ℝ)/320000), ((-347681711151:ℝ)/32000), ((-3628099917:ℝ)/3200), ((-10463337:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e) - ((-2852602244696682596459368856431:ℝ)/39321600000000000000) - ((-97219518787524951859194087077:ℝ)/655360000000000000)*t| ≤ ((398333886424464764926119259:ℝ)/1966080000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-2852602244696682596459368856431:ℝ)/39321600000000000000), ((-97219518787524951859194087077:ℝ)/655360000000000000), ((-237962213374340353854878093:ℝ)/3072000000000000), ((160516030608548244066769307:ℝ)/2457600000000000), ((9931588521743579956129053:ℝ)/81920000000000), ((1038825645558050686184387:ℝ)/12288000000000), ((10496105032211302553381:ℝ)/307200000000), ((21201996678320686571:ℝ)/2560000000), ((1441113826595295647:ℝ)/1536000000), ((-7157601907236793:ℝ)/76800000), ((-18384043025163:ℝ)/320000), ((-347681711151:ℝ)/32000), ((-3628099917:ℝ)/3200), ((-10463337:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e)| ≤ ((525371246464624457889245583807:ℝ)/6553600000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((153969276771336449:ℝ)/16000000000) - ((17329240634519109:ℝ)/800000000)*t| ≤ ((444183297072221:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((9:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82125:ℝ), (-6663750:ℝ), (115666200:ℝ), (-750437000:ℝ), (2277262000:ℝ), (-3656824320:ℝ), (3359621120:ℝ), (-1817706496:ℝ), ((1625292800:ℝ)/3), (-67108864:ℝ)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_22 q| ≤ ((7246800620525887857:ℝ)/16) := by
    rw [centralNum13_22_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((9:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((178425:ℝ)/2), ((-13176075:ℝ)/2), ((777815145:ℝ)/8), ((-3968389015:ℝ)/8), ((9393350195:ℝ)/8), ((-26366634375:ℝ)/16), ((77851609375:ℝ)/64), ((-25714921875:ℝ)/64), ((5236328125:ℝ)/96), ((-9765625:ℝ)/4)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_22 q| ≤ ((4801446862184500828155:ℝ)/65536) := by
    rw [centralNum23_22_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece17_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece17_E11 h0) m23'
  have c5 := scaled_affine (X := ((2733239127:ℝ)/125000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2))| ≤ ((642607735308625000000000000:ℝ)/82460633665245974453163323973) := by
    rw [abs_neg, tailWeight_2, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((9:ℝ)/2)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((9:ℝ)/2)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece17_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((2570430941234500:ℝ)/4782969)) ≤ ((9:ℝ)/2)^6*(8000*(2*((9:ℝ)/2)-3)^2*(1/((82460633665245974453163323973:ℝ)/500000000))*((2570430941234500:ℝ)/4782969)) := by
          gcongr
      _ ≤ ((642607735308625000000000000:ℝ)/82460633665245974453163323973) := by norm_num
  have c7 := affine_round (α := ((140361203097095899:ℝ)/19200000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((-2852602244696682596459368856431:ℝ)/39321600000000000000) + ((153969276771336449:ℝ)/16000000000)*((2733239127:ℝ)/125000000000) - ((13192956231803223:ℝ)/2000000000)) (β := ((5044795095211003:ℝ)/320000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((-97219518787524951859194087077:ℝ)/655360000000000000) - 3*((-2852602244696682596459368856431:ℝ)/39321600000000000000)) + ((17329240634519109:ℝ)/800000000)*((2733239127:ℝ)/125000000000) - ((85607919159253531:ℝ)/5000000000)) ht
  have hW : pieceW q pieceX_17 2 2 = centralNum11_22 q + 8*(Real.exp (-(3*((89:ℝ)/20)))*Real.exp (-3*t))*centralNum12_22 q + 18*Real.exp (-8*q)*centralNum13_22 q + 72*Real.exp (-11*q)*centralNum23_22 q + 8*q^7*(2*q-3)^2*((2733239127:ℝ)/125000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2)) := by
    rw [pieceW_22, pieceX_17, sym4_22, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((4681396648895521600401267612689670145682874715548617396168917701304249:ℝ)/1182453088208997218966520887792290656870161878385613212812347000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((140361203097095899:ℝ)/19200000000) + ((5044795095211003:ℝ)/320000000)*t) + (8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((-2852602244696682596459368856431:ℝ)/39321600000000000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((-97219518787524951859194087077:ℝ)/655360000000000000) - 3*((-2852602244696682596459368856431:ℝ)/39321600000000000000))*t) + (((153969276771336449:ℝ)/16000000000) + ((17329240634519109:ℝ)/800000000)*t)*((2733239127:ℝ)/125000000000) - (((13192956231803223:ℝ)/2000000000) + t * ((85607919159253531:ℝ)/5000000000)) = (((140361203097095899:ℝ)/19200000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((-2852602244696682596459368856431:ℝ)/39321600000000000000) + ((153969276771336449:ℝ)/16000000000)*((2733239127:ℝ)/125000000000) - ((13192956231803223:ℝ)/2000000000)) + t*(((5044795095211003:ℝ)/320000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((-97219518787524951859194087077:ℝ)/655360000000000000) - 3*((-2852602244696682596459368856431:ℝ)/39321600000000000000)) + ((17329240634519109:ℝ)/800000000)*((2733239127:ℝ)/125000000000) - ((85607919159253531:ℝ)/5000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece17_e23 {q : ℝ} (h0 : ((22:ℝ)/5) ≤ q) (h1 : q ≤ ((9:ℝ)/2)) :
    |pieceW q pieceX_17 2 3 - (((154644987859646777:ℝ)/100000000000) + (q - ((89:ℝ)/20)) * ((-130745760910533:ℝ)/125000000))| ≤ ((50939441508390569:ℝ)/250000000000) := by
  set t := q - ((89:ℝ)/20) with htd
  have hq : q = ((89:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece17_L3 piece17_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((89:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_23 q = ∑ e ∈ Finset.range 9, ([((267370350477569:ℝ)/160000000), ((95558754505917:ℝ)/32000000), ((4024447365703:ℝ)/1600000), ((103814123069:ℝ)/80000), ((352444539:ℝ)/800), ((19731919:ℝ)/200), ((139853:ℝ)/10), (1134:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_23; ring
  have h12 : centralNum12_23 q = ∑ e ∈ Finset.range 16, ([((65974038089009075900455513284943:ℝ)/3670016000000000000000), ((-146818583573586809420152795707:ℝ)/734003200000000000), ((-1131567952065094571683103183993:ℝ)/1835008000000000000), ((-34528883041114382726132716127:ℝ)/45875200000000000), ((-2278476273423634113989043537:ℝ)/4587520000000000), ((-103541173920012572389504367:ℝ)/573440000000000), ((-51419157101624930318873:ℝ)/2293760000000), ((3143686333069667030313:ℝ)/286720000000), ((188903284872957165673:ℝ)/28672000000), ((1195714390318431567:ℝ)/716800000), ((76900649317346889:ℝ)/358400000), ((1595991215439:ℝ)/358400), ((-558527792283:ℝ)/179200), ((-2328566697:ℝ)/4480), ((-2368521:ℝ)/64), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_23; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((267370350477569:ℝ)/160000000), ((95558754505917:ℝ)/32000000), ((4024447365703:ℝ)/1600000), ((103814123069:ℝ)/80000), ((352444539:ℝ)/800), ((19731919:ℝ)/200), ((139853:ℝ)/10), (1134:ℝ), (40:ℝ)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((65974038089009075900455513284943:ℝ)/3670016000000000000000), ((-146818583573586809420152795707:ℝ)/734003200000000000), ((-1131567952065094571683103183993:ℝ)/1835008000000000000), ((-34528883041114382726132716127:ℝ)/45875200000000000), ((-2278476273423634113989043537:ℝ)/4587520000000000), ((-103541173920012572389504367:ℝ)/573440000000000), ((-51419157101624930318873:ℝ)/2293760000000), ((3143686333069667030313:ℝ)/286720000000), ((188903284872957165673:ℝ)/28672000000), ((1195714390318431567:ℝ)/716800000), ((76900649317346889:ℝ)/358400000), ((1595991215439:ℝ)/358400), ((-558527792283:ℝ)/179200), ((-2328566697:ℝ)/4480), ((-2368521:ℝ)/64), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 14 ht
  have m12 := abs_poly_le (fun e => ([((65974038089009075900455513284943:ℝ)/3670016000000000000000), ((-146818583573586809420152795707:ℝ)/734003200000000000), ((-1131567952065094571683103183993:ℝ)/1835008000000000000), ((-34528883041114382726132716127:ℝ)/45875200000000000), ((-2278476273423634113989043537:ℝ)/4587520000000000), ((-103541173920012572389504367:ℝ)/573440000000000), ((-51419157101624930318873:ℝ)/2293760000000), ((3143686333069667030313:ℝ)/286720000000), ((188903284872957165673:ℝ)/28672000000), ((1195714390318431567:ℝ)/716800000), ((76900649317346889:ℝ)/358400000), ((1595991215439:ℝ)/358400), ((-558527792283:ℝ)/179200), ((-2328566697:ℝ)/4480), ((-2368521:ℝ)/64), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 16 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((267370350477569:ℝ)/160000000), ((95558754505917:ℝ)/32000000), ((4024447365703:ℝ)/1600000), ((103814123069:ℝ)/80000), ((352444539:ℝ)/800), ((19731919:ℝ)/200), ((139853:ℝ)/10), (1134:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e) - (((267370350477569:ℝ)/160000000) + ((95558754505917:ℝ)/32000000)*t)| ≤ ((4130043583807:ℝ)/640000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 16, ([((65974038089009075900455513284943:ℝ)/3670016000000000000000), ((-146818583573586809420152795707:ℝ)/734003200000000000), ((-1131567952065094571683103183993:ℝ)/1835008000000000000), ((-34528883041114382726132716127:ℝ)/45875200000000000), ((-2278476273423634113989043537:ℝ)/4587520000000000), ((-103541173920012572389504367:ℝ)/573440000000000), ((-51419157101624930318873:ℝ)/2293760000000), ((3143686333069667030313:ℝ)/286720000000), ((188903284872957165673:ℝ)/28672000000), ((1195714390318431567:ℝ)/716800000), ((76900649317346889:ℝ)/358400000), ((1595991215439:ℝ)/358400), ((-558527792283:ℝ)/179200), ((-2328566697:ℝ)/4480), ((-2368521:ℝ)/64), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e) - ((65974038089009075900455513284943:ℝ)/3670016000000000000000) - ((-146818583573586809420152795707:ℝ)/734003200000000000)*t| ≤ ((6014729372323916304244351490201:ℝ)/3670016000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 16, ([((65974038089009075900455513284943:ℝ)/3670016000000000000000), ((-146818583573586809420152795707:ℝ)/734003200000000000), ((-1131567952065094571683103183993:ℝ)/1835008000000000000), ((-34528883041114382726132716127:ℝ)/45875200000000000), ((-2278476273423634113989043537:ℝ)/4587520000000000), ((-103541173920012572389504367:ℝ)/573440000000000), ((-51419157101624930318873:ℝ)/2293760000000), ((3143686333069667030313:ℝ)/286720000000), ((188903284872957165673:ℝ)/28672000000), ((1195714390318431567:ℝ)/716800000), ((76900649317346889:ℝ)/358400000), ((1595991215439:ℝ)/358400), ((-558527792283:ℝ)/179200), ((-2328566697:ℝ)/4480), ((-2368521:ℝ)/64), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e)| ≤ ((54346706677364847279869031850947:ℝ)/1835008000000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((153969276771336449:ℝ)/16000000000) - ((17329240634519109:ℝ)/800000000)*t| ≤ ((444183297072221:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((9:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-7627725:ℝ)/2), (173988600:ℝ), (-2299614450:ℝ), (13088188200:ℝ), (-38221499200:ℝ), (63366115840:ℝ), ((-445610508288:ℝ)/7), ((841540698112:ℝ)/21), ((-326820167680:ℝ)/21), ((10133438464:ℝ)/3), ((-2147483648:ℝ)/7)] : List ℝ).getD e 0) 16 hq1'
  have m13' : |centralNum13_23 q| ≤ ((432838572690716001639:ℝ)/28) := by
    rw [centralNum13_23_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((9:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-15801525:ℝ)/4), ((655493865:ℝ)/4), ((-7334421225:ℝ)/4), ((16442962485:ℝ)/2), ((-598626108395:ℝ)/32), ((414013307125:ℝ)/16), ((-4611984703125:ℝ)/224), ((399923828125:ℝ)/48), ((-4353201171875:ℝ)/2688), ((189736328125:ℝ)/1344), ((-244140625:ℝ)/56)] : List ℝ).getD e 0) 16 hq1'
  have m23' : |centralNum23_23 q| ≤ ((451074748035945418065585:ℝ)/262144) := by
    rw [centralNum23_23_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece17_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece17_E11 h0) m23'
  have c5 := scaled_affine (X := ((-367535623733:ℝ)/10000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((267370350477569:ℝ)/160000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((65974038089009075900455513284943:ℝ)/3670016000000000000000) + ((153969276771336449:ℝ)/16000000000)*((-367535623733:ℝ)/10000000000000) - ((154644987859646777:ℝ)/100000000000)) (β := ((95558754505917:ℝ)/32000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((-146818583573586809420152795707:ℝ)/734003200000000000) - 3*((65974038089009075900455513284943:ℝ)/3670016000000000000000)) + ((17329240634519109:ℝ)/800000000)*((-367535623733:ℝ)/10000000000000) - ((-130745760910533:ℝ)/125000000)) ht
  have hW : pieceW q pieceX_17 2 3 = centralNum11_23 q + 8*(Real.exp (-(3*((89:ℝ)/20)))*Real.exp (-3*t))*centralNum12_23 q + 18*Real.exp (-8*q)*centralNum13_23 q + 72*Real.exp (-11*q)*centralNum23_23 q + 8*q^7*(2*q-3)^2*((-367535623733:ℝ)/10000000000000) + (0:ℝ) := by
    rw [pieceW_23, pieceX_17, sym4_23, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((10596168796929676845549155817412875924393619577248409090055109654740439:ℝ)/3153208235223992583910722367446108418320431675694968567499592000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((267370350477569:ℝ)/160000000) + ((95558754505917:ℝ)/32000000)*t) + (8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((65974038089009075900455513284943:ℝ)/3670016000000000000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((-146818583573586809420152795707:ℝ)/734003200000000000) - 3*((65974038089009075900455513284943:ℝ)/3670016000000000000000))*t) + (((153969276771336449:ℝ)/16000000000) + ((17329240634519109:ℝ)/800000000)*t)*((-367535623733:ℝ)/10000000000000) - (((154644987859646777:ℝ)/100000000000) + t * ((-130745760910533:ℝ)/125000000)) = (((267370350477569:ℝ)/160000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((65974038089009075900455513284943:ℝ)/3670016000000000000000) + ((153969276771336449:ℝ)/16000000000)*((-367535623733:ℝ)/10000000000000) - ((154644987859646777:ℝ)/100000000000)) + t*(((95558754505917:ℝ)/32000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((-146818583573586809420152795707:ℝ)/734003200000000000) - 3*((65974038089009075900455513284943:ℝ)/3670016000000000000000)) + ((17329240634519109:ℝ)/800000000)*((-367535623733:ℝ)/10000000000000) - ((-130745760910533:ℝ)/125000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece17_e33 {q : ℝ} (h0 : ((22:ℝ)/5) ≤ q) (h1 : q ≤ ((9:ℝ)/2)) :
    |pieceW q pieceX_17 3 3 - (((93171801014287101:ℝ)/12500000000) + (q - ((89:ℝ)/20)) * ((162258804948378011:ℝ)/10000000000))| ≤ ((56949350470293521:ℝ)/10000000000) := by
  set t := q - ((89:ℝ)/20) with htd
  have hq : q = ((89:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece17_L3 piece17_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((89:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_33 q = ∑ e ∈ Finset.range 10, ([((48516354454648769:ℝ)/22400000000), ((3451304976531987:ℝ)/560000000), ((398787451412649:ℝ)/56000000), ((1830757024227:ℝ)/400000), ((36977637057:ℝ)/20000), ((495270483:ℝ)/1000), ((4452693:ℝ)/50), ((365502:ℝ)/35), ((5088:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_33; ring
  have h12 : centralNum12_33 q = ∑ e ∈ Finset.range 17, ([((321416327684320645299769832341936163:ℝ)/1027604480000000000000000), ((76968361585285086102103629800635137:ℝ)/51380224000000000000000), ((1283894310505936099794550169253717:ℝ)/513802240000000000000), ((7321267649512041756078774164847:ℝ)/3670016000000000000), ((126535912467996908165346861411:ℝ)/183500800000000000), ((-5124761800361106625771608837:ℝ)/45875200000000000), ((-514424119734583080492151533:ℝ)/2293760000000000), ((-16858263604628237036284779:ℝ)/160563200000000), ((-197847888743598662161833:ℝ)/8028160000000), ((-792979153325645636809:ℝ)/401408000000), ((7576852228971189597:ℝ)/14336000000), ((132087437919554193:ℝ)/716800000), ((164949833356641:ℝ)/7168000), ((233777245797:ℝ)/358400), ((-20133169893:ℝ)/125440), ((-597398733:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_33; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((48516354454648769:ℝ)/22400000000), ((3451304976531987:ℝ)/560000000), ((398787451412649:ℝ)/56000000), ((1830757024227:ℝ)/400000), ((36977637057:ℝ)/20000), ((495270483:ℝ)/1000), ((4452693:ℝ)/50), ((365502:ℝ)/35), ((5088:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((321416327684320645299769832341936163:ℝ)/1027604480000000000000000), ((76968361585285086102103629800635137:ℝ)/51380224000000000000000), ((1283894310505936099794550169253717:ℝ)/513802240000000000000), ((7321267649512041756078774164847:ℝ)/3670016000000000000), ((126535912467996908165346861411:ℝ)/183500800000000000), ((-5124761800361106625771608837:ℝ)/45875200000000000), ((-514424119734583080492151533:ℝ)/2293760000000000), ((-16858263604628237036284779:ℝ)/160563200000000), ((-197847888743598662161833:ℝ)/8028160000000), ((-792979153325645636809:ℝ)/401408000000), ((7576852228971189597:ℝ)/14336000000), ((132087437919554193:ℝ)/716800000), ((164949833356641:ℝ)/7168000), ((233777245797:ℝ)/358400), ((-20133169893:ℝ)/125440), ((-597398733:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 15 ht
  have m12 := abs_poly_le (fun e => ([((321416327684320645299769832341936163:ℝ)/1027604480000000000000000), ((76968361585285086102103629800635137:ℝ)/51380224000000000000000), ((1283894310505936099794550169253717:ℝ)/513802240000000000000), ((7321267649512041756078774164847:ℝ)/3670016000000000000), ((126535912467996908165346861411:ℝ)/183500800000000000), ((-5124761800361106625771608837:ℝ)/45875200000000000), ((-514424119734583080492151533:ℝ)/2293760000000000), ((-16858263604628237036284779:ℝ)/160563200000000), ((-197847888743598662161833:ℝ)/8028160000000), ((-792979153325645636809:ℝ)/401408000000), ((7576852228971189597:ℝ)/14336000000), ((132087437919554193:ℝ)/716800000), ((164949833356641:ℝ)/7168000), ((233777245797:ℝ)/358400), ((-20133169893:ℝ)/125440), ((-597398733:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 17 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((48516354454648769:ℝ)/22400000000), ((3451304976531987:ℝ)/560000000), ((398787451412649:ℝ)/56000000), ((1830757024227:ℝ)/400000), ((36977637057:ℝ)/20000), ((495270483:ℝ)/1000), ((4452693:ℝ)/50), ((365502:ℝ)/35), ((5088:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e) - (((48516354454648769:ℝ)/22400000000) + ((3451304976531987:ℝ)/560000000)*t)| ≤ ((58837870326751:ℝ)/3200000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 17, ([((321416327684320645299769832341936163:ℝ)/1027604480000000000000000), ((76968361585285086102103629800635137:ℝ)/51380224000000000000000), ((1283894310505936099794550169253717:ℝ)/513802240000000000000), ((7321267649512041756078774164847:ℝ)/3670016000000000000), ((126535912467996908165346861411:ℝ)/183500800000000000), ((-5124761800361106625771608837:ℝ)/45875200000000000), ((-514424119734583080492151533:ℝ)/2293760000000000), ((-16858263604628237036284779:ℝ)/160563200000000), ((-197847888743598662161833:ℝ)/8028160000000), ((-792979153325645636809:ℝ)/401408000000), ((7576852228971189597:ℝ)/14336000000), ((132087437919554193:ℝ)/716800000), ((164949833356641:ℝ)/7168000), ((233777245797:ℝ)/358400), ((-20133169893:ℝ)/125440), ((-597398733:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e) - ((321416327684320645299769832341936163:ℝ)/1027604480000000000000000) - ((76968361585285086102103629800635137:ℝ)/51380224000000000000000)*t| ≤ ((3817248135305713630305280868303:ℝ)/587202560000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 17, ([((321416327684320645299769832341936163:ℝ)/1027604480000000000000000), ((76968361585285086102103629800635137:ℝ)/51380224000000000000000), ((1283894310505936099794550169253717:ℝ)/513802240000000000000), ((7321267649512041756078774164847:ℝ)/3670016000000000000), ((126535912467996908165346861411:ℝ)/183500800000000000), ((-5124761800361106625771608837:ℝ)/45875200000000000), ((-514424119734583080492151533:ℝ)/2293760000000000), ((-16858263604628237036284779:ℝ)/160563200000000), ((-197847888743598662161833:ℝ)/8028160000000), ((-792979153325645636809:ℝ)/401408000000), ((7576852228971189597:ℝ)/14336000000), ((132087437919554193:ℝ)/716800000), ((164949833356641:ℝ)/7168000), ((233777245797:ℝ)/358400), ((-20133169893:ℝ)/125440), ((-597398733:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e)| ≤ ((1157328210018259229299736296177433:ℝ)/2936012800000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((153969276771336449:ℝ)/16000000000), ((17329240634519109:ℝ)/800000000), ((107867276376333:ℝ)/5000000), ((195002885028:ℝ)/15625), ((231140300937:ℝ)/50000), ((2843266713:ℝ)/2500), ((23235408:ℝ)/125), ((486672:ℝ)/25), ((5928:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((153969276771336449:ℝ)/16000000000) - ((17329240634519109:ℝ)/800000000)*t| ≤ ((444183297072221:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((9:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-8120475:ℝ)/4), ((464861025:ℝ)/2), (-5906535975:ℝ), ((411904731750:ℝ)/7), ((-2024051769000:ℝ)/7), ((5554394637600:ℝ)/7), (-1314913862656:ℝ), ((9709155336192:ℝ)/7), ((-6724555112448:ℝ)/7), ((1313173667840:ℝ)/3), ((-6168244125696:ℝ)/49), ((3004329623552:ℝ)/147), ((-68719476736:ℝ)/49)] : List ℝ).getD e 0) 17 hq1'
  have m13' : |centralNum13_33 q| ≤ ((18312917053383518668533:ℝ)/32) := by
    rw [centralNum13_33_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((9:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-16872075:ℝ)/8), ((1833754545:ℝ)/8), ((-83998007145:ℝ)/16), ((4929124002765:ℝ)/112), ((-76723155584685:ℝ)/448), ((164888745653055:ℝ)/448), ((-63358359907625:ℝ)/128), ((364713160040625:ℝ)/896), ((-334937462578125:ℝ)/1792), ((245466998046875:ℝ)/5376), ((-72144521484375:ℝ)/12544), ((6518798828125:ℝ)/18816), ((-6103515625:ℝ)/784)] : List ℝ).getD e 0) 17 hq1'
  have m23' : |centralNum23_33 q| ≤ ((335544535434834898114184145:ℝ)/7340032) := by
    rw [centralNum23_33_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece17_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece17_E11 h0) m23'
  have c5 := scaled_affine (X := ((135317610967:ℝ)/1000000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3))| ≤ ((827142953176307875000000000000:ℝ)/2226437108961641310235409747271) := by
    rw [abs_neg, tailWeight_3, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((9:ℝ)/2)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((9:ℝ)/2)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece17_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((3308571812705231500:ℝ)/129140163)) ≤ ((9:ℝ)/2)^6*(8000*(2*((9:ℝ)/2)-3)^2*(1/((82460633665245974453163323973:ℝ)/500000000))*((3308571812705231500:ℝ)/129140163)) := by
          gcongr
      _ ≤ ((827142953176307875000000000000:ℝ)/2226437108961641310235409747271) := by norm_num
  have c7 := affine_round (α := ((48516354454648769:ℝ)/22400000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((321416327684320645299769832341936163:ℝ)/1027604480000000000000000) + ((153969276771336449:ℝ)/16000000000)*((135317610967:ℝ)/1000000000000) - ((93171801014287101:ℝ)/12500000000)) (β := ((3451304976531987:ℝ)/560000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((76968361585285086102103629800635137:ℝ)/51380224000000000000000) - 3*((321416327684320645299769832341936163:ℝ)/1027604480000000000000000)) + ((17329240634519109:ℝ)/800000000)*((135317610967:ℝ)/1000000000000) - ((162258804948378011:ℝ)/10000000000)) ht
  have hW : pieceW q pieceX_17 3 3 = centralNum11_33 q + 8*(Real.exp (-(3*((89:ℝ)/20)))*Real.exp (-3*t))*centralNum12_33 q + 18*Real.exp (-8*q)*centralNum13_33 q + 72*Real.exp (-11*q)*centralNum23_33 q + 8*q^7*(2*q-3)^2*((135317610967:ℝ)/1000000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3)) := by
    rw [pieceW_33, pieceX_17, sym4_33, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((131679511008807528204429175172695682059795391457685257895720128884043899:ℝ)/22072457646567948087375056572122758928243021729864779972497144000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((48516354454648769:ℝ)/22400000000) + ((3451304976531987:ℝ)/560000000)*t) + (8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((321416327684320645299769832341936163:ℝ)/1027604480000000000000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((76968361585285086102103629800635137:ℝ)/51380224000000000000000) - 3*((321416327684320645299769832341936163:ℝ)/1027604480000000000000000))*t) + (((153969276771336449:ℝ)/16000000000) + ((17329240634519109:ℝ)/800000000)*t)*((135317610967:ℝ)/1000000000000) - (((93171801014287101:ℝ)/12500000000) + t * ((162258804948378011:ℝ)/10000000000)) = (((48516354454648769:ℝ)/22400000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*((321416327684320645299769832341936163:ℝ)/1027604480000000000000000) + ((153969276771336449:ℝ)/16000000000)*((135317610967:ℝ)/1000000000000) - ((93171801014287101:ℝ)/12500000000)) + t*(((3451304976531987:ℝ)/560000000) + 8*(((1/((627814488295437581570535126581:ℝ)/1000000000000000000000000))+(1/((627814484614950587090063078629:ℝ)/1000000000000000000000000)))/2)*(((76968361585285086102103629800635137:ℝ)/51380224000000000000000) - 3*((321416327684320645299769832341936163:ℝ)/1027604480000000000000000)) + ((17329240634519109:ℝ)/800000000)*((135317610967:ℝ)/1000000000000) - ((162258804948378011:ℝ)/10000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece17_plus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((113749411177950829:ℝ)/10000000000) + ((1:ℝ)/20)*((245168778352086519:ℝ)/10000000000) - (((153141533040379899:ℝ)/2500000000000) + ((89170114319025149:ℝ)/12500000000000) + ((270482367695097213:ℝ)/100000000000000) + ((12758010308997551:ℝ)/2000000000000)))
      (((-42628764083640127:ℝ)/25000000000) + ((1:ℝ)/20)*((-259880984430167821:ℝ)/100000000000))
      (((-275543473991665017:ℝ)/10000000000000) + ((1:ℝ)/20)*((-602518226650085231:ℝ)/10000000000000))
      (((60034209397797821:ℝ)/500000000000) + ((1:ℝ)/20)*((-49510460738065469:ℝ)/1000000000000))
      (((840550614921579849:ℝ)/100000000000) + ((1:ℝ)/20)*((3426844346515487:ℝ)/200000000) - (((89170114319025149:ℝ)/12500000000000) + ((422548153020730473:ℝ)/10000000000000) + ((197303102443905141:ℝ)/10000000000000) + ((46515989568943053:ℝ)/2500000000000)))
      (((-134307922101684291:ℝ)/200000000000) + ((1:ℝ)/20)*((-129300189364154979:ℝ)/100000000000))
      (((-765861367716074391:ℝ)/1000000000000) + ((1:ℝ)/20)*((37365680339362321:ℝ)/250000000000))
      (((13192956231803223:ℝ)/2000000000) + ((1:ℝ)/20)*((85607919159253531:ℝ)/5000000000) - (((270482367695097213:ℝ)/100000000000000) + ((197303102443905141:ℝ)/10000000000000) + ((422574070070647497:ℝ)/5000000000000) + ((50939441508390569:ℝ)/250000000000)))
      (((154644987859646777:ℝ)/100000000000) + ((1:ℝ)/20)*((-130745760910533:ℝ)/125000000))
      (((93171801014287101:ℝ)/12500000000) + ((1:ℝ)/20)*((162258804948378011:ℝ)/10000000000) - (((12758010308997551:ℝ)/2000000000000) + ((46515989568943053:ℝ)/2500000000000) + ((50939441508390569:ℝ)/250000000000) + ((56949350470293521:ℝ)/10000000000))) i j :=
  quadForm_nonneg_of_ldl ((250466219167247835517:ℝ)/20000000000000) ((3485233073057135155736131574985363911419:ℝ)/391353467448824742995312500000000) ((789633845585859033433089023631012659547136080679376632046141343:ℝ)/111527458337828324983556210399531645165408000000000000000) ((15702833745885403486923107356879447274928953162210660202441802222970751927845255809:ℝ)/7896338455858590334330890236310126595471360806793766320461413430000000000000) ((-36701821111213779810:ℝ)/250466219167247835517) ((-6113387706483385571:ℝ)/2504662191672478355170) ((2351857915173847371:ℝ)/250466219167247835517) ((-18551251435884931363032927883748073741405:ℝ)/223054916675656649967112420799063290330816) ((-9281737980888746402906105667140090259005:ℝ)/111527458337828324983556210399531645165408) ((159796244436450216387535325635113050060769269460462328309092670:ℝ)/789633845585859033433089023631012659547136080679376632046141343)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece17_minus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((113749411177950829:ℝ)/10000000000) - ((1:ℝ)/20)*((245168778352086519:ℝ)/10000000000) - (((153141533040379899:ℝ)/2500000000000) + ((89170114319025149:ℝ)/12500000000000) + ((270482367695097213:ℝ)/100000000000000) + ((12758010308997551:ℝ)/2000000000000)))
      (((-42628764083640127:ℝ)/25000000000) - ((1:ℝ)/20)*((-259880984430167821:ℝ)/100000000000))
      (((-275543473991665017:ℝ)/10000000000000) - ((1:ℝ)/20)*((-602518226650085231:ℝ)/10000000000000))
      (((60034209397797821:ℝ)/500000000000) - ((1:ℝ)/20)*((-49510460738065469:ℝ)/1000000000000))
      (((840550614921579849:ℝ)/100000000000) - ((1:ℝ)/20)*((3426844346515487:ℝ)/200000000) - (((89170114319025149:ℝ)/12500000000000) + ((422548153020730473:ℝ)/10000000000000) + ((197303102443905141:ℝ)/10000000000000) + ((46515989568943053:ℝ)/2500000000000)))
      (((-134307922101684291:ℝ)/200000000000) - ((1:ℝ)/20)*((-129300189364154979:ℝ)/100000000000))
      (((-765861367716074391:ℝ)/1000000000000) - ((1:ℝ)/20)*((37365680339362321:ℝ)/250000000000))
      (((13192956231803223:ℝ)/2000000000) - ((1:ℝ)/20)*((85607919159253531:ℝ)/5000000000) - (((270482367695097213:ℝ)/100000000000000) + ((197303102443905141:ℝ)/10000000000000) + ((422574070070647497:ℝ)/5000000000000) + ((50939441508390569:ℝ)/250000000000)))
      (((154644987859646777:ℝ)/100000000000) - ((1:ℝ)/20)*((-130745760910533:ℝ)/125000000))
      (((93171801014287101:ℝ)/12500000000) - ((1:ℝ)/20)*((162258804948378011:ℝ)/10000000000) - (((12758010308997551:ℝ)/2000000000000) + ((46515989568943053:ℝ)/2500000000000) + ((50939441508390569:ℝ)/250000000000) + ((56949350470293521:ℝ)/10000000000))) i j :=
  quadForm_nonneg_of_ldl ((201432463496830531717:ℝ)/20000000000000) ((9082974758591491948342743615260190276151:ℝ)/1258952896855190823231250000000000) ((390781040390569075857398941922712184874338054577336470216919763:ℝ)/72663798068731935586741948922081522209208000000000000000) ((782343458570839718394999754421440436250681361711912861111725435881187819386199169:ℝ)/3907810403905690758573989419227121848743380545773364702169197630000000000000) ((-31504201422610423390:ℝ)/201432463496830531717) ((-4908351253183215109:ℝ)/2014324634968305317170) ((2450878836649978309:ℝ)/201432463496830531717) ((-12302041867596521759670102817277897876105:ℝ)/145327596137463871173483897844163044418416) ((-7595701258884386315389515879392284700145:ℝ)/72663798068731935586741948922081522209208) ((111553906525390852746791071268157435238764219393704581364142470:ℝ)/390781040390569075857398941922712184874338054577336470216919763)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

/-- **Piece 17.** The piece matrix is positive semidefinite on `q ∈ [22/5, 9/2]`. -/
theorem piece_17 {q : ℝ} (h0 : ((22:ℝ)/5) ≤ q) (h1 : q ≤ ((9:ℝ)/2)) (y : Fin 4 → ℝ) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceW q pieceX_17 i j :=
  pieceForm_nonneg (pieceW_symm (sym4_symm _ _ _ _ _ _ _ _ _ _) q) (by norm_num : (0:ℝ) < ((1:ℝ)/20))
    (abs_le.mpr ⟨by linarith, by linarith⟩)
    (piece17_e00 h0 h1) (piece17_e01 h0 h1) (piece17_e02 h0 h1) (piece17_e03 h0 h1) (piece17_e11 h0 h1) (piece17_e12 h0 h1) (piece17_e13 h0 h1) (piece17_e22 h0 h1) (piece17_e23 h0 h1) (piece17_e33 h0 h1)
    piece17_plus piece17_minus y

/-! #### Piece 18 (seam), `q ∈ [9/2, 23/5]` -/

/-- The compensation matrix of piece 18. -/
def pieceX_18 : Fin 4 → Fin 4 → ℝ :=
  sym4 ((11:ℝ)/1000) (0:ℝ) (0:ℝ) (0:ℝ) ((11:ℝ)/1000) (0:ℝ) (0:ℝ) ((11:ℝ)/1000) (0:ℝ) ((11:ℝ)/1000)

theorem piece18_L3 : ((847460538421008944439567461473:ℝ)/1000000000000000000000000) ≤ Real.exp ((3:ℝ)*((91:ℝ)/20)) := by
  have h := le_exp_nat_add 13 (f := ((13:ℝ)/20)) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((91:ℝ)/20) = ((13:ℕ):ℝ) + ((13:ℝ)/20) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece18_U3 : Real.exp ((3:ℝ)*((91:ℝ)/20)) ≤ ((423730466487991770665586377133:ℝ)/500000000000000000000000) := by
  have h := exp_nat_add_le 13 (f := ((13:ℝ)/20)) (by norm_num) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((91:ℝ)/20) = ((13:ℕ):ℝ) + ((13:ℝ)/20) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem piece18_L8_at : ((107780788450856786383293588681:ℝ)/25000000000000) ≤ Real.exp ((8:ℝ)*((9:ℝ)/2)) := by
  have h := le_exp_nat_add 36 (f := (0:ℝ)) (by norm_num)
  rw [show ((8:ℝ):ℝ)*((9:ℝ)/2) = ((36:ℕ):ℝ) + (0:ℝ) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece18_E8 {q : ℝ} (h0 : ((9:ℝ)/2) ≤ q) : Real.exp (-((8:ℝ))*q) ≤ 1/((107780788450856786383293588681:ℝ)/25000000000000) := by
  have hm : Real.exp (-((8:ℝ))*q) ≤ Real.exp (-((8:ℝ)*((9:ℝ)/2))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece18_L8_at (le_refl _)).2

theorem piece18_L11_at : ((4913566656350639975088254891:ℝ)/1562500) ≤ Real.exp ((11:ℝ)*((9:ℝ)/2)) := by
  have h := le_exp_nat_add 49 (f := ((1:ℝ)/2)) (by norm_num)
  rw [show ((11:ℝ):ℝ)*((9:ℝ)/2) = ((49:ℕ):ℝ) + ((1:ℝ)/2) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece18_E11 {q : ℝ} (h0 : ((9:ℝ)/2) ≤ q) : Real.exp (-((11:ℝ))*q) ≤ 1/((4913566656350639975088254891:ℝ)/1562500) := by
  have hm : Real.exp (-((11:ℝ))*q) ≤ Real.exp (-((11:ℝ)*((9:ℝ)/2))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece18_L11_at (le_refl _)).2

theorem piece18_Lt_at : ((475072795688088943343832220359:ℝ)/1000000000) ≤ Real.exp (((529:ℝ)/50)*((9:ℝ)/2)) := by
  have h := le_exp_nat_add 47 (f := ((61:ℝ)/100)) (by norm_num)
  rw [show (((529:ℝ)/50):ℝ)*((9:ℝ)/2) = ((47:ℕ):ℝ) + ((61:ℝ)/100) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece18_Et {q : ℝ} (h0 : ((9:ℝ)/2) ≤ q) : Real.exp (-(((529:ℝ)/50))*q) ≤ 1/((475072795688088943343832220359:ℝ)/1000000000) := by
  have hm : Real.exp (-(((529:ℝ)/50))*q) ≤ Real.exp (-(((529:ℝ)/50)*((9:ℝ)/2))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece18_Lt_at (le_refl _)).2

theorem piece18_e00 {q : ℝ} (h0 : ((9:ℝ)/2) ≤ q) (h1 : q ≤ ((23:ℝ)/5)) :
    |pieceW q pieceX_18 0 0 - (((140761053758443601:ℝ)/10000000000) + (q - ((91:ℝ)/20)) * ((148245754415013519:ℝ)/5000000000))| ≤ ((721767640417918651:ℝ)/10000000000000) := by
  set t := q - ((91:ℝ)/20) with htd
  have hq : q = ((91:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece18_L3 piece18_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((91:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_00 q = ∑ e ∈ Finset.range 10, ([((223292436464293651:ℝ)/16000000000), ((23480825702643309:ℝ)/800000000), ((34465295373873:ℝ)/1250000), ((3791715318573:ℝ)/250000), ((268914072063:ℝ)/50000), ((3184649013:ℝ)/2500), ((25171692:ℝ)/125), ((511872:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_00; ring
  have h12 : centralNum12_00 q = ∑ e ∈ Finset.range 11, ([((-402342533284617013543:ℝ)/320000000000), ((-9340825107766456941:ℝ)/3200000000), ((-244093050344053911:ℝ)/80000000), ((-3781264700241483:ℝ)/2000000), ((-153793640009373:ℝ)/200000), ((-10723977834843:ℝ)/50000), ((-5192706792:ℝ)/125), ((-137912646:ℝ)/25), ((-2403174:ℝ)/5), (-24808:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_00; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((223292436464293651:ℝ)/16000000000), ((23480825702643309:ℝ)/800000000), ((34465295373873:ℝ)/1250000), ((3791715318573:ℝ)/250000), ((268914072063:ℝ)/50000), ((3184649013:ℝ)/2500), ((25171692:ℝ)/125), ((511872:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-402342533284617013543:ℝ)/320000000000), ((-9340825107766456941:ℝ)/3200000000), ((-244093050344053911:ℝ)/80000000), ((-3781264700241483:ℝ)/2000000), ((-153793640009373:ℝ)/200000), ((-10723977834843:ℝ)/50000), ((-5192706792:ℝ)/125), ((-137912646:ℝ)/25), ((-2403174:ℝ)/5), (-24808:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 9 ht
  have m12 := abs_poly_le (fun e => ([((-402342533284617013543:ℝ)/320000000000), ((-9340825107766456941:ℝ)/3200000000), ((-244093050344053911:ℝ)/80000000), ((-3781264700241483:ℝ)/2000000), ((-153793640009373:ℝ)/200000), ((-10723977834843:ℝ)/50000), ((-5192706792:ℝ)/125), ((-137912646:ℝ)/25), ((-2403174:ℝ)/5), (-24808:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 11 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((223292436464293651:ℝ)/16000000000), ((23480825702643309:ℝ)/800000000), ((34465295373873:ℝ)/1250000), ((3791715318573:ℝ)/250000), ((268914072063:ℝ)/50000), ((3184649013:ℝ)/2500), ((25171692:ℝ)/125), ((511872:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - (((223292436464293651:ℝ)/16000000000) + ((23480825702643309:ℝ)/800000000)*t)| ≤ ((8857557988709:ℝ)/125000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 11, ([((-402342533284617013543:ℝ)/320000000000), ((-9340825107766456941:ℝ)/3200000000), ((-244093050344053911:ℝ)/80000000), ((-3781264700241483:ℝ)/2000000), ((-153793640009373:ℝ)/200000), ((-10723977834843:ℝ)/50000), ((-5192706792:ℝ)/125), ((-137912646:ℝ)/25), ((-2403174:ℝ)/5), (-24808:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e) - ((-402342533284617013543:ℝ)/320000000000) - ((-9340825107766456941:ℝ)/3200000000)*t| ≤ ((314764423861819223:ℝ)/40000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 11, ([((-402342533284617013543:ℝ)/320000000000), ((-9340825107766456941:ℝ)/3200000000), ((-244093050344053911:ℝ)/80000000), ((-3781264700241483:ℝ)/2000000), ((-153793640009373:ℝ)/200000), ((-10723977834843:ℝ)/50000), ((-5192706792:ℝ)/125), ((-137912646:ℝ)/25), ((-2403174:ℝ)/5), (-24808:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((13780663275584224:ℝ)/9765625) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((192286775302855051:ℝ)/16000000000) - ((21095774844071109:ℝ)/800000000)*t| ≤ ((65855210523547:ℝ)/1000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((23:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (600:ℝ), (-7776:ℝ), (16800:ℝ), (-9216:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m13' : |centralNum13_00 q| ≤ ((548562568355032584:ℝ)/9765625) := by
    rw [centralNum13_00_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((23:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (780:ℝ), (-6156:ℝ), (15288:ℝ), (-14400:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m23' : |centralNum23_00 q| ≤ ((149321180406921144:ℝ)/1953125) := by
    rw [centralNum23_00_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((423730466487991770665586377133:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece18_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece18_E11 h0) m23'
  have c5 := scaled_affine (X := ((11:ℝ)/1000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0))| ≤ ((30491607555433549176832000000:ℝ)/28052573512585964015509948779978591) := by
    rw [abs_neg, tailWeight_0, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((23:ℝ)/5)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((23:ℝ)/5)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece18_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((10465499600:ℝ)/59049)) ≤ ((23:ℝ)/5)^6*(8000*(2*((23:ℝ)/5)-3)^2*(1/((475072795688088943343832220359:ℝ)/1000000000))*((10465499600:ℝ)/59049)) := by
          gcongr
      _ ≤ ((30491607555433549176832000000:ℝ)/28052573512585964015509948779978591) := by norm_num
  have c7 := affine_round (α := ((223292436464293651:ℝ)/16000000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((-402342533284617013543:ℝ)/320000000000) + ((192286775302855051:ℝ)/16000000000)*((11:ℝ)/1000) - ((140761053758443601:ℝ)/10000000000)) (β := ((23480825702643309:ℝ)/800000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((-9340825107766456941:ℝ)/3200000000) - 3*((-402342533284617013543:ℝ)/320000000000)) + ((21095774844071109:ℝ)/800000000)*((11:ℝ)/1000) - ((148245754415013519:ℝ)/5000000000)) ht
  have hW : pieceW q pieceX_18 0 0 = centralNum11_00 q + 8*(Real.exp (-(3*((91:ℝ)/20)))*Real.exp (-3*t))*centralNum12_00 q + 18*Real.exp (-8*q)*centralNum13_00 q + 72*Real.exp (-11*q)*centralNum23_00 q + 8*q^7*(2*q-3)^2*((11:ℝ)/1000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0)) := by
    rw [pieceW_00, pieceX_18, sym4_00, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((45917871580686860020591743917110142523733473385565801766023:ℝ)/5524536142696904506628082750801667932319019522297901933798600000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((223292436464293651:ℝ)/16000000000) + ((23480825702643309:ℝ)/800000000)*t) + (8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((-402342533284617013543:ℝ)/320000000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((-9340825107766456941:ℝ)/3200000000) - 3*((-402342533284617013543:ℝ)/320000000000))*t) + (((192286775302855051:ℝ)/16000000000) + ((21095774844071109:ℝ)/800000000)*t)*((11:ℝ)/1000) - (((140761053758443601:ℝ)/10000000000) + t * ((148245754415013519:ℝ)/5000000000)) = (((223292436464293651:ℝ)/16000000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((-402342533284617013543:ℝ)/320000000000) + ((192286775302855051:ℝ)/16000000000)*((11:ℝ)/1000) - ((140761053758443601:ℝ)/10000000000)) + t*(((23480825702643309:ℝ)/800000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((-9340825107766456941:ℝ)/3200000000) - 3*((-402342533284617013543:ℝ)/320000000000)) + ((21095774844071109:ℝ)/800000000)*((11:ℝ)/1000) - ((148245754415013519:ℝ)/5000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece18_e01 {q : ℝ} (h0 : ((9:ℝ)/2) ≤ q) (h1 : q ≤ ((23:ℝ)/5)) :
    |pieceW q pieceX_18 0 1 - (((-49578310324602231:ℝ)/25000000000) + (q - ((91:ℝ)/20)) * ((-296803744602358439:ℝ)/100000000000))| ≤ ((150773132565981793:ℝ)/20000000000000) := by
  set t := q - ((91:ℝ)/20) with htd
  have hq : q = ((91:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece18_L3 piece18_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((91:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_01 q = ∑ e ∈ Finset.range 8, ([((-155028305807193:ℝ)/80000000), ((-11925254292861:ℝ)/4000000), ((-393140251413:ℝ)/200000), ((-1440074181:ℝ)/2000), ((-15824991:ℝ)/100), ((-521703:ℝ)/25), ((-7644:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_01; ring
  have h12 : centralNum12_01 q = ∑ e ∈ Finset.range 12, ([((-61394924042940485765859:ℝ)/12800000000000), ((-4154579442537530749197:ℝ)/320000000000), ((-101980484110890100989:ℝ)/6400000000), ((-1873397212545546051:ℝ)/160000000), ((-45796931418861987:ℝ)/8000000), ((-1955692520131077:ℝ)/1000000), ((-47642058531249:ℝ)/100000), ((-41382430071:ℝ)/500), ((-1004877027:ℝ)/100), ((-4060554:ℝ)/5), ((-196596:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_01; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-155028305807193:ℝ)/80000000), ((-11925254292861:ℝ)/4000000), ((-393140251413:ℝ)/200000), ((-1440074181:ℝ)/2000), ((-15824991:ℝ)/100), ((-521703:ℝ)/25), ((-7644:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0) 6 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-61394924042940485765859:ℝ)/12800000000000), ((-4154579442537530749197:ℝ)/320000000000), ((-101980484110890100989:ℝ)/6400000000), ((-1873397212545546051:ℝ)/160000000), ((-45796931418861987:ℝ)/8000000), ((-1955692520131077:ℝ)/1000000), ((-47642058531249:ℝ)/100000), ((-41382430071:ℝ)/500), ((-1004877027:ℝ)/100), ((-4060554:ℝ)/5), ((-196596:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0) 10 ht
  have m12 := abs_poly_le (fun e => ([((-61394924042940485765859:ℝ)/12800000000000), ((-4154579442537530749197:ℝ)/320000000000), ((-101980484110890100989:ℝ)/6400000000), ((-1873397212545546051:ℝ)/160000000), ((-45796931418861987:ℝ)/8000000), ((-1955692520131077:ℝ)/1000000), ((-47642058531249:ℝ)/100000), ((-41382430071:ℝ)/500), ((-1004877027:ℝ)/100), ((-4060554:ℝ)/5), ((-196596:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0) 12 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 8, ([((-155028305807193:ℝ)/80000000), ((-11925254292861:ℝ)/4000000), ((-393140251413:ℝ)/200000), ((-1440074181:ℝ)/2000), ((-15824991:ℝ)/100), ((-521703:ℝ)/25), ((-7644:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0 * t^e) - (((-155028305807193:ℝ)/80000000) + ((-11925254292861:ℝ)/4000000)*t)| ≤ ((40042027089:ℝ)/8000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 12, ([((-61394924042940485765859:ℝ)/12800000000000), ((-4154579442537530749197:ℝ)/320000000000), ((-101980484110890100989:ℝ)/6400000000), ((-1873397212545546051:ℝ)/160000000), ((-45796931418861987:ℝ)/8000000), ((-1955692520131077:ℝ)/1000000), ((-47642058531249:ℝ)/100000), ((-41382430071:ℝ)/500), ((-1004877027:ℝ)/100), ((-4060554:ℝ)/5), ((-196596:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e) - ((-61394924042940485765859:ℝ)/12800000000000) - ((-4154579442537530749197:ℝ)/320000000000)*t| ≤ ((529102280880985510659:ℝ)/12800000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 12, ([((-61394924042940485765859:ℝ)/12800000000000), ((-4154579442537530749197:ℝ)/320000000000), ((-101980484110890100989:ℝ)/6400000000), ((-1873397212545546051:ℝ)/160000000), ((-45796931418861987:ℝ)/8000000), ((-1955692520131077:ℝ)/1000000), ((-47642058531249:ℝ)/100000), ((-41382430071:ℝ)/500), ((-1004877027:ℝ)/100), ((-4060554:ℝ)/5), ((-196596:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((267918339572511798:ℝ)/48828125) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((192286775302855051:ℝ)/16000000000) - ((21095774844071109:ℝ)/800000000)*t| ≤ ((65855210523547:ℝ)/1000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((23:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-6288:ℝ), (81024:ℝ), (-238720:ℝ), (246784:ℝ), (-98304:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m13' : |centralNum13_01 q| ≤ ((156337804865260315888:ℝ)/48828125) := by
    rw [centralNum13_01_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((23:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-7368:ℝ), (59208:ℝ), (-155734:ℝ), (205300:ℝ), (-60000:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m23' : |centralNum23_01 q| ≤ ((4292027030936056222:ℝ)/1953125) := by
    rw [centralNum23_01_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((423730466487991770665586377133:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece18_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece18_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-155028305807193:ℝ)/80000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((-61394924042940485765859:ℝ)/12800000000000) + ((192286775302855051:ℝ)/16000000000)*(0:ℝ) - ((-49578310324602231:ℝ)/25000000000)) (β := ((-11925254292861:ℝ)/4000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((-4154579442537530749197:ℝ)/320000000000) - 3*((-61394924042940485765859:ℝ)/12800000000000)) + ((21095774844071109:ℝ)/800000000)*(0:ℝ) - ((-296803744602358439:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_18 0 1 = centralNum11_01 q + 8*(Real.exp (-(3*((91:ℝ)/20)))*Real.exp (-3*t))*centralNum12_01 q + 18*Real.exp (-8*q)*centralNum13_01 q + 72*Real.exp (-11*q)*centralNum23_01 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_01, pieceX_18, sym4_01, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((49335555392970717056526832727158367586804762186614111834189:ℝ)/18415120475656348355426942502672226441063398407659673112662000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-155028305807193:ℝ)/80000000) + ((-11925254292861:ℝ)/4000000)*t) + (8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((-61394924042940485765859:ℝ)/12800000000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((-4154579442537530749197:ℝ)/320000000000) - 3*((-61394924042940485765859:ℝ)/12800000000000))*t) + (((192286775302855051:ℝ)/16000000000) + ((21095774844071109:ℝ)/800000000)*t)*(0:ℝ) - (((-49578310324602231:ℝ)/25000000000) + t * ((-296803744602358439:ℝ)/100000000000)) = (((-155028305807193:ℝ)/80000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((-61394924042940485765859:ℝ)/12800000000000) + ((192286775302855051:ℝ)/16000000000)*(0:ℝ) - ((-49578310324602231:ℝ)/25000000000)) + t*(((-11925254292861:ℝ)/4000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((-4154579442537530749197:ℝ)/320000000000) - 3*((-61394924042940485765859:ℝ)/12800000000000)) + ((21095774844071109:ℝ)/800000000)*(0:ℝ) - ((-296803744602358439:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece18_e02 {q : ℝ} (h0 : ((9:ℝ)/2) ≤ q) (h1 : q ≤ ((23:ℝ)/5)) :
    |pieceW q pieceX_18 0 2 - (((-333084860848658943:ℝ)/10000000000000) + (q - ((91:ℝ)/20)) * ((-538021717640617213:ℝ)/10000000000000))| ≤ ((293001859158566157:ℝ)/100000000000000) := by
  set t := q - ((91:ℝ)/20) with htd
  have hq : q = ((91:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece18_L3 piece18_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((91:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_02 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_02; ring
  have h12 : centralNum12_02 q = ∑ e ∈ Finset.range 13, ([((-7226274335355403755859341:ℝ)/2048000000000000), ((-1667560069539741116149137:ℝ)/102400000000000), ((-150199716094721335370601:ℝ)/5120000000000), ((-1514636831275760573199:ℝ)/51200000000), ((-3073254436723252509:ℝ)/160000000), ((-2750873286146992461:ℝ)/320000000), ((-43906612298030937:ℝ)/16000000), ((-506479387950531:ℝ)/800000), ((-1682485225929:ℝ)/16000), ((-9835337889:ℝ)/800), ((-192420981:ℝ)/200), ((-453087:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_02; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-7226274335355403755859341:ℝ)/2048000000000000), ((-1667560069539741116149137:ℝ)/102400000000000), ((-150199716094721335370601:ℝ)/5120000000000), ((-1514636831275760573199:ℝ)/51200000000), ((-3073254436723252509:ℝ)/160000000), ((-2750873286146992461:ℝ)/320000000), ((-43906612298030937:ℝ)/16000000), ((-506479387950531:ℝ)/800000), ((-1682485225929:ℝ)/16000), ((-9835337889:ℝ)/800), ((-192420981:ℝ)/200), ((-453087:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((-7226274335355403755859341:ℝ)/2048000000000000), ((-1667560069539741116149137:ℝ)/102400000000000), ((-150199716094721335370601:ℝ)/5120000000000), ((-1514636831275760573199:ℝ)/51200000000), ((-3073254436723252509:ℝ)/160000000), ((-2750873286146992461:ℝ)/320000000), ((-43906612298030937:ℝ)/16000000), ((-506479387950531:ℝ)/800000), ((-1682485225929:ℝ)/16000), ((-9835337889:ℝ)/800), ((-192420981:ℝ)/200), ((-453087:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((-7226274335355403755859341:ℝ)/2048000000000000), ((-1667560069539741116149137:ℝ)/102400000000000), ((-150199716094721335370601:ℝ)/5120000000000), ((-1514636831275760573199:ℝ)/51200000000), ((-3073254436723252509:ℝ)/160000000), ((-2750873286146992461:ℝ)/320000000), ((-43906612298030937:ℝ)/16000000), ((-506479387950531:ℝ)/800000), ((-1682485225929:ℝ)/16000), ((-9835337889:ℝ)/800), ((-192420981:ℝ)/200), ((-453087:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e) - ((-7226274335355403755859341:ℝ)/2048000000000000) - ((-1667560069539741116149137:ℝ)/102400000000000)*t| ≤ ((79012175593627730039409:ℝ)/1024000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((-7226274335355403755859341:ℝ)/2048000000000000), ((-1667560069539741116149137:ℝ)/102400000000000), ((-150199716094721335370601:ℝ)/5120000000000), ((-1514636831275760573199:ℝ)/51200000000), ((-3073254436723252509:ℝ)/160000000), ((-2750873286146992461:ℝ)/320000000), ((-43906612298030937:ℝ)/16000000), ((-506479387950531:ℝ)/800000), ((-1682485225929:ℝ)/16000), ((-9835337889:ℝ)/800), ((-192420981:ℝ)/200), ((-453087:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((2158131302853202899:ℝ)/488281250) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((192286775302855051:ℝ)/16000000000) - ((21095774844071109:ℝ)/800000000)*t| ≤ ((65855210523547:ℝ)/1000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((23:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82080:ℝ), (-967680:ℝ), (3257600:ℝ), (-4474880:ℝ), (2908160:ℝ), (-786432:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_02 q| ≤ ((36505109897063613634272:ℝ)/244140625) := by
    rw [centralNum13_02_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((23:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (87660:ℝ), (-702180:ℝ), ((7421435:ℝ)/4), ((-10854125:ℝ)/4), ((2828125:ℝ)/2), (-187500:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_02 q| ≤ ((22574370639020140659:ℝ)/390625) := by
    rw [centralNum23_02_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((423730466487991770665586377133:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece18_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece18_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((-7226274335355403755859341:ℝ)/2048000000000000) + ((192286775302855051:ℝ)/16000000000)*(0:ℝ) - ((-333084860848658943:ℝ)/10000000000000)) (β := (0:ℝ) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((-1667560069539741116149137:ℝ)/102400000000000) - 3*((-7226274335355403755859341:ℝ)/2048000000000000)) + ((21095774844071109:ℝ)/800000000)*(0:ℝ) - ((-538021717640617213:ℝ)/10000000000000)) ht
  have hW : pieceW q pieceX_18 0 2 = centralNum11_02 q + 8*(Real.exp (-(3*((91:ℝ)/20)))*Real.exp (-3*t))*centralNum12_02 q + 18*Real.exp (-8*q)*centralNum13_02 q + 72*Real.exp (-11*q)*centralNum23_02 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_02, pieceX_18, sym4_02, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((44654109917127877134725821258530702231808957812916754362843:ℝ)/1841512047565634835542694250267222644106339840765967311266200000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((-7226274335355403755859341:ℝ)/2048000000000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((-1667560069539741116149137:ℝ)/102400000000000) - 3*((-7226274335355403755859341:ℝ)/2048000000000000))*t) + (((192286775302855051:ℝ)/16000000000) + ((21095774844071109:ℝ)/800000000)*t)*(0:ℝ) - (((-333084860848658943:ℝ)/10000000000000) + t * ((-538021717640617213:ℝ)/10000000000000)) = ((0:ℝ) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((-7226274335355403755859341:ℝ)/2048000000000000) + ((192286775302855051:ℝ)/16000000000)*(0:ℝ) - ((-333084860848658943:ℝ)/10000000000000)) + t*((0:ℝ) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((-1667560069539741116149137:ℝ)/102400000000000) - 3*((-7226274335355403755859341:ℝ)/2048000000000000)) + ((21095774844071109:ℝ)/800000000)*(0:ℝ) - ((-538021717640617213:ℝ)/10000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece18_e03 {q : ℝ} (h0 : ((9:ℝ)/2) ≤ q) (h1 : q ≤ ((23:ℝ)/5)) :
    |pieceW q pieceX_18 0 3 - (((114586758053177121:ℝ)/1000000000000) + (q - ((91:ℝ)/20)) * ((-15705524216794431:ℝ)/250000000000))| ≤ ((145220887687742467:ℝ)/25000000000000) := by
  set t := q - ((91:ℝ)/20) with htd
  have hq : q = ((91:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece18_L3 piece18_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((91:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_03 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_03; ring
  have h12 : centralNum12_03 q = ∑ e ∈ Finset.range 14, ([((994383649597909096456304283:ℝ)/81920000000000000), ((30474761524986839764681341:ℝ)/1024000000000000), ((359170653160194421709709:ℝ)/12800000000000), ((46594782689076852966099:ℝ)/5120000000000), ((-550392103353470855841:ℝ)/102400000000), ((-97633231240267836477:ℝ)/12800000000), ((-693961473392174169:ℝ)/160000000), ((-24704409531010833:ℝ)/16000000), ((-1207124353884159:ℝ)/3200000), ((-64723685013:ℝ)/1000), ((-7714388889:ℝ)/1000), ((-855242631:ℝ)/1400), ((-4057857:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_03; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((994383649597909096456304283:ℝ)/81920000000000000), ((30474761524986839764681341:ℝ)/1024000000000000), ((359170653160194421709709:ℝ)/12800000000000), ((46594782689076852966099:ℝ)/5120000000000), ((-550392103353470855841:ℝ)/102400000000), ((-97633231240267836477:ℝ)/12800000000), ((-693961473392174169:ℝ)/160000000), ((-24704409531010833:ℝ)/16000000), ((-1207124353884159:ℝ)/3200000), ((-64723685013:ℝ)/1000), ((-7714388889:ℝ)/1000), ((-855242631:ℝ)/1400), ((-4057857:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((994383649597909096456304283:ℝ)/81920000000000000), ((30474761524986839764681341:ℝ)/1024000000000000), ((359170653160194421709709:ℝ)/12800000000000), ((46594782689076852966099:ℝ)/5120000000000), ((-550392103353470855841:ℝ)/102400000000), ((-97633231240267836477:ℝ)/12800000000), ((-693961473392174169:ℝ)/160000000), ((-24704409531010833:ℝ)/16000000), ((-1207124353884159:ℝ)/3200000), ((-64723685013:ℝ)/1000), ((-7714388889:ℝ)/1000), ((-855242631:ℝ)/1400), ((-4057857:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((994383649597909096456304283:ℝ)/81920000000000000), ((30474761524986839764681341:ℝ)/1024000000000000), ((359170653160194421709709:ℝ)/12800000000000), ((46594782689076852966099:ℝ)/5120000000000), ((-550392103353470855841:ℝ)/102400000000), ((-97633231240267836477:ℝ)/12800000000), ((-693961473392174169:ℝ)/160000000), ((-24704409531010833:ℝ)/16000000), ((-1207124353884159:ℝ)/3200000), ((-64723685013:ℝ)/1000), ((-7714388889:ℝ)/1000), ((-855242631:ℝ)/1400), ((-4057857:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((994383649597909096456304283:ℝ)/81920000000000000) - ((30474761524986839764681341:ℝ)/1024000000000000)*t| ≤ ((8180022052506471591492729:ℝ)/114688000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((994383649597909096456304283:ℝ)/81920000000000000), ((30474761524986839764681341:ℝ)/1024000000000000), ((359170653160194421709709:ℝ)/12800000000000), ((46594782689076852966099:ℝ)/5120000000000), ((-550392103353470855841:ℝ)/102400000000), ((-97633231240267836477:ℝ)/12800000000), ((-693961473392174169:ℝ)/160000000), ((-24704409531010833:ℝ)/16000000), ((-1207124353884159:ℝ)/3200000), ((-64723685013:ℝ)/1000), ((-7714388889:ℝ)/1000), ((-855242631:ℝ)/1400), ((-4057857:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((3927439490073763773281335587:ℝ)/286720000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((192286775302855051:ℝ)/16000000000) - ((21095774844071109:ℝ)/800000000)*t| ≤ ((65855210523547:ℝ)/1000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((23:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-812160:ℝ), (8985600:ℝ), (-32225280:ℝ), (52019200:ℝ), ((-305233920:ℝ)/7), ((135528448:ℝ)/7), ((-25165824:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_03 q| ≤ ((36960746070713056516373632:ℝ)/8544921875) := by
    rw [centralNum13_03_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((23:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-833220:ℝ), (6469740:ℝ), ((-68603955:ℝ)/4), ((104396875:ℝ)/4), ((-1001334375:ℝ)/56), ((125828125:ℝ)/28), ((-2343750:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_03 q| ≤ ((22277830258231043094727:ℝ)/21875000) := by
    rw [centralNum23_03_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((423730466487991770665586377133:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece18_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece18_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((994383649597909096456304283:ℝ)/81920000000000000) + ((192286775302855051:ℝ)/16000000000)*(0:ℝ) - ((114586758053177121:ℝ)/1000000000000)) (β := (0:ℝ) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((30474761524986839764681341:ℝ)/1024000000000000) - 3*((994383649597909096456304283:ℝ)/81920000000000000)) + ((21095774844071109:ℝ)/800000000)*(0:ℝ) - ((-15705524216794431:ℝ)/250000000000)) ht
  have hW : pieceW q pieceX_18 0 3 = centralNum11_03 q + 8*(Real.exp (-(3*((91:ℝ)/20)))*Real.exp (-3*t))*centralNum12_03 q + 18*Real.exp (-8*q)*centralNum13_03 q + 72*Real.exp (-11*q)*centralNum23_03 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_03, pieceX_18, sym4_03, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((10892629990476392355481739771459185882363113779775297038703:ℝ)/23018900594570435444283678128340283051329248009574591390827500000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((994383649597909096456304283:ℝ)/81920000000000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((30474761524986839764681341:ℝ)/1024000000000000) - 3*((994383649597909096456304283:ℝ)/81920000000000000))*t) + (((192286775302855051:ℝ)/16000000000) + ((21095774844071109:ℝ)/800000000)*t)*(0:ℝ) - (((114586758053177121:ℝ)/1000000000000) + t * ((-15705524216794431:ℝ)/250000000000)) = ((0:ℝ) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((994383649597909096456304283:ℝ)/81920000000000000) + ((192286775302855051:ℝ)/16000000000)*(0:ℝ) - ((114586758053177121:ℝ)/1000000000000)) + t*((0:ℝ) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((30474761524986839764681341:ℝ)/1024000000000000) - 3*((994383649597909096456304283:ℝ)/81920000000000000)) + ((21095774844071109:ℝ)/800000000)*(0:ℝ) - ((-15705524216794431:ℝ)/250000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece18_e11 {q : ℝ} (h0 : ((9:ℝ)/2) ≤ q) (h1 : q ≤ ((23:ℝ)/5)) :
    |pieceW q pieceX_18 1 1 - (((51388384803125341:ℝ)/5000000000) + (q - ((91:ℝ)/20)) * ((102903351662483799:ℝ)/5000000000))| ≤ ((123586699897576311:ℝ)/2500000000000) := by
  set t := q - ((91:ℝ)/20) with htd
  have hq : q = ((91:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece18_L3 piece18_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((91:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_11 q = ∑ e ∈ Finset.range 10, ([((60846622486941109:ℝ)/6000000000), ((8149316907039763:ℝ)/400000000), ((92265072751943:ℝ)/5000000), ((2471446869437:ℝ)/250000), ((43108260923:ℝ)/12500), ((1014048581:ℝ)/1250), ((16057188:ℝ)/125), ((329488:ℝ)/25), ((3968:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_11; ring
  have h12 : centralNum12_11 q = ∑ e ∈ Finset.range 13, ([((712038643972794399505699:ℝ)/1536000000000000), ((-188639810232696433946699:ℝ)/25600000000000), ((-27000514810999366922467:ℝ)/1280000000000), ((-331641556132147663493:ℝ)/12800000000), ((-754211291640443273:ℝ)/40000000), ((-728679164425073407:ℝ)/80000000), ((-12298872009087699:ℝ)/4000000), ((-148162027706977:ℝ)/200000), ((-509774476403:ℝ)/4000), ((-9206016049:ℝ)/600), ((-61559847:ℝ)/50), ((-296298:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_11; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((60846622486941109:ℝ)/6000000000), ((8149316907039763:ℝ)/400000000), ((92265072751943:ℝ)/5000000), ((2471446869437:ℝ)/250000), ((43108260923:ℝ)/12500), ((1014048581:ℝ)/1250), ((16057188:ℝ)/125), ((329488:ℝ)/25), ((3968:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((712038643972794399505699:ℝ)/1536000000000000), ((-188639810232696433946699:ℝ)/25600000000000), ((-27000514810999366922467:ℝ)/1280000000000), ((-331641556132147663493:ℝ)/12800000000), ((-754211291640443273:ℝ)/40000000), ((-728679164425073407:ℝ)/80000000), ((-12298872009087699:ℝ)/4000000), ((-148162027706977:ℝ)/200000), ((-509774476403:ℝ)/4000), ((-9206016049:ℝ)/600), ((-61559847:ℝ)/50), ((-296298:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((712038643972794399505699:ℝ)/1536000000000000), ((-188639810232696433946699:ℝ)/25600000000000), ((-27000514810999366922467:ℝ)/1280000000000), ((-331641556132147663493:ℝ)/12800000000), ((-754211291640443273:ℝ)/40000000), ((-728679164425073407:ℝ)/80000000), ((-12298872009087699:ℝ)/4000000), ((-148162027706977:ℝ)/200000), ((-509774476403:ℝ)/4000), ((-9206016049:ℝ)/600), ((-61559847:ℝ)/50), ((-296298:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((60846622486941109:ℝ)/6000000000), ((8149316907039763:ℝ)/400000000), ((92265072751943:ℝ)/5000000), ((2471446869437:ℝ)/250000), ((43108260923:ℝ)/12500), ((1014048581:ℝ)/1250), ((16057188:ℝ)/125), ((329488:ℝ)/25), ((3968:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((60846622486941109:ℝ)/6000000000) + ((8149316907039763:ℝ)/400000000)*t)| ≤ ((1137361667298547:ℝ)/24000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((712038643972794399505699:ℝ)/1536000000000000), ((-188639810232696433946699:ℝ)/25600000000000), ((-27000514810999366922467:ℝ)/1280000000000), ((-331641556132147663493:ℝ)/12800000000), ((-754211291640443273:ℝ)/40000000), ((-728679164425073407:ℝ)/80000000), ((-12298872009087699:ℝ)/4000000), ((-148162027706977:ℝ)/200000), ((-509774476403:ℝ)/4000), ((-9206016049:ℝ)/600), ((-61559847:ℝ)/50), ((-296298:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e) - ((712038643972794399505699:ℝ)/1536000000000000) - ((-188639810232696433946699:ℝ)/25600000000000)*t| ≤ ((43080812624928812832289:ℝ)/768000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((712038643972794399505699:ℝ)/1536000000000000), ((-188639810232696433946699:ℝ)/25600000000000), ((-27000514810999366922467:ℝ)/1280000000000), ((-331641556132147663493:ℝ)/12800000000), ((-754211291640443273:ℝ)/40000000), ((-728679164425073407:ℝ)/80000000), ((-12298872009087699:ℝ)/4000000), ((-148162027706977:ℝ)/200000), ((-509774476403:ℝ)/4000), ((-9206016049:ℝ)/600), ((-61559847:ℝ)/50), ((-296298:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((227353283320123554501729:ℝ)/256000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((192286775302855051:ℝ)/16000000000) - ((21095774844071109:ℝ)/800000000)*t| ≤ ((65855210523547:ℝ)/1000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((23:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-3444:ℝ), (162624:ℝ), (-1531216:ℝ), (4800960:ℝ), (-6350848:ℝ), ((12025856:ℝ)/3), (-1048576:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_11 q| ≤ ((149433994386325839895148:ℝ)/732421875) := by
    rw [centralNum13_11_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((23:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-4074:ℝ), (159906:ℝ), (-1104799:ℝ), (2801499:ℝ), (-3931375:ℝ), ((5896250:ℝ)/3), (-250000:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_11 q| ≤ ((470402428986050981671:ℝ)/5859375) := by
    rw [centralNum23_11_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((423730466487991770665586377133:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece18_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece18_E11 h0) m23'
  have c5 := scaled_affine (X := ((11:ℝ)/1000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1))| ≤ ((14027929319966112163340288000000:ℝ)/252473161613273676139589539019807319) := by
    rw [abs_neg, tailWeight_1, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((23:ℝ)/5)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((23:ℝ)/5)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece18_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((4814744136400:ℝ)/531441)) ≤ ((23:ℝ)/5)^6*(8000*(2*((23:ℝ)/5)-3)^2*(1/((475072795688088943343832220359:ℝ)/1000000000))*((4814744136400:ℝ)/531441)) := by
          gcongr
      _ ≤ ((14027929319966112163340288000000:ℝ)/252473161613273676139589539019807319) := by norm_num
  have c7 := affine_round (α := ((60846622486941109:ℝ)/6000000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((712038643972794399505699:ℝ)/1536000000000000) + ((192286775302855051:ℝ)/16000000000)*((11:ℝ)/1000) - ((51388384803125341:ℝ)/5000000000)) (β := ((8149316907039763:ℝ)/400000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((-188639810232696433946699:ℝ)/25600000000000) - 3*((712038643972794399505699:ℝ)/1536000000000000)) + ((21095774844071109:ℝ)/800000000)*((11:ℝ)/1000) - ((102903351662483799:ℝ)/5000000000)) ht
  have hW : pieceW q pieceX_18 1 1 = centralNum11_11 q + 8*(Real.exp (-(3*((91:ℝ)/20)))*Real.exp (-3*t))*centralNum12_11 q + 18*Real.exp (-8*q)*centralNum13_11 q + 72*Real.exp (-11*q)*centralNum23_11 q + 8*q^7*(2*q-3)^2*((11:ℝ)/1000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1)) := by
    rw [pieceW_11, pieceX_18, sym4_11, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((26093749450841418133224480149563901547604335704042372304892021:ℝ)/662944337123628540795369930096200151878282342675748232055832000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((60846622486941109:ℝ)/6000000000) + ((8149316907039763:ℝ)/400000000)*t) + (8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((712038643972794399505699:ℝ)/1536000000000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((-188639810232696433946699:ℝ)/25600000000000) - 3*((712038643972794399505699:ℝ)/1536000000000000))*t) + (((192286775302855051:ℝ)/16000000000) + ((21095774844071109:ℝ)/800000000)*t)*((11:ℝ)/1000) - (((51388384803125341:ℝ)/5000000000) + t * ((102903351662483799:ℝ)/5000000000)) = (((60846622486941109:ℝ)/6000000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((712038643972794399505699:ℝ)/1536000000000000) + ((192286775302855051:ℝ)/16000000000)*((11:ℝ)/1000) - ((51388384803125341:ℝ)/5000000000)) + t*(((8149316907039763:ℝ)/400000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((-188639810232696433946699:ℝ)/25600000000000) - 3*((712038643972794399505699:ℝ)/1536000000000000)) + ((21095774844071109:ℝ)/800000000)*((11:ℝ)/1000) - ((102903351662483799:ℝ)/5000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece18_e12 {q : ℝ} (h0 : ((9:ℝ)/2) ≤ q) (h1 : q ≤ ((23:ℝ)/5)) :
    |pieceW q pieceX_18 1 2 - (((-154769470312301349:ℝ)/200000000000) + (q - ((91:ℝ)/20)) * ((-139611729824300399:ℝ)/100000000000))| ≤ ((303517232516929:ℝ)/16000000000) := by
  set t := q - ((91:ℝ)/20) with htd
  have hq : q = ((91:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece18_L3 piece18_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((91:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_12 q = ∑ e ∈ Finset.range 9, ([((-2043761438095559:ℝ)/1920000000), ((-33404440727203:ℝ)/24000000), ((-764816540033:ℝ)/1200000), ((-3685715761:ℝ)/60000), ((61171747:ℝ)/1200), ((3338699:ℝ)/150), ((60854:ℝ)/15), ((1096:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_12; ring
  have h12 : centralNum12_12 q = ∑ e ∈ Finset.range 14, ([((7565783997522728626048027901:ℝ)/245760000000000000), ((282328766942340026513151547:ℝ)/3072000000000000), ((4432014054678191098008983:ℝ)/38400000000000), ((1190497007913674545977893:ℝ)/15360000000000), ((8215147978303155427993:ℝ)/307200000000), ((28804446398888504981:ℝ)/38400000000), ((-1891651297603809023:ℝ)/480000000), ((-101992462290094871:ℝ)/48000000), ((-6017908186790713:ℝ)/9600000), ((-120552269267:ℝ)/1000), ((-15552874461:ℝ)/1000), ((-261463437:ℝ)/200), ((-1300779:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_12; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-2043761438095559:ℝ)/1920000000), ((-33404440727203:ℝ)/24000000), ((-764816540033:ℝ)/1200000), ((-3685715761:ℝ)/60000), ((61171747:ℝ)/1200), ((3338699:ℝ)/150), ((60854:ℝ)/15), ((1096:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((7565783997522728626048027901:ℝ)/245760000000000000), ((282328766942340026513151547:ℝ)/3072000000000000), ((4432014054678191098008983:ℝ)/38400000000000), ((1190497007913674545977893:ℝ)/15360000000000), ((8215147978303155427993:ℝ)/307200000000), ((28804446398888504981:ℝ)/38400000000), ((-1891651297603809023:ℝ)/480000000), ((-101992462290094871:ℝ)/48000000), ((-6017908186790713:ℝ)/9600000), ((-120552269267:ℝ)/1000), ((-15552874461:ℝ)/1000), ((-261463437:ℝ)/200), ((-1300779:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((7565783997522728626048027901:ℝ)/245760000000000000), ((282328766942340026513151547:ℝ)/3072000000000000), ((4432014054678191098008983:ℝ)/38400000000000), ((1190497007913674545977893:ℝ)/15360000000000), ((8215147978303155427993:ℝ)/307200000000), ((28804446398888504981:ℝ)/38400000000), ((-1891651297603809023:ℝ)/480000000), ((-101992462290094871:ℝ)/48000000), ((-6017908186790713:ℝ)/9600000), ((-120552269267:ℝ)/1000), ((-15552874461:ℝ)/1000), ((-261463437:ℝ)/200), ((-1300779:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((-2043761438095559:ℝ)/1920000000), ((-33404440727203:ℝ)/24000000), ((-764816540033:ℝ)/1200000), ((-3685715761:ℝ)/60000), ((61171747:ℝ)/1200), ((3338699:ℝ)/150), ((60854:ℝ)/15), ((1096:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((-2043761438095559:ℝ)/1920000000) + ((-33404440727203:ℝ)/24000000)*t)| ≤ ((3074634217699:ℝ)/1920000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((7565783997522728626048027901:ℝ)/245760000000000000), ((282328766942340026513151547:ℝ)/3072000000000000), ((4432014054678191098008983:ℝ)/38400000000000), ((1190497007913674545977893:ℝ)/15360000000000), ((8215147978303155427993:ℝ)/307200000000), ((28804446398888504981:ℝ)/38400000000), ((-1891651297603809023:ℝ)/480000000), ((-101992462290094871:ℝ)/48000000), ((-6017908186790713:ℝ)/9600000), ((-120552269267:ℝ)/1000), ((-15552874461:ℝ)/1000), ((-261463437:ℝ)/200), ((-1300779:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e) - ((7565783997522728626048027901:ℝ)/245760000000000000) - ((282328766942340026513151547:ℝ)/3072000000000000)*t| ≤ ((73334367786719098322814379:ℝ)/245760000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((7565783997522728626048027901:ℝ)/245760000000000000), ((282328766942340026513151547:ℝ)/3072000000000000), ((4432014054678191098008983:ℝ)/38400000000000), ((1190497007913674545977893:ℝ)/15360000000000), ((8215147978303155427993:ℝ)/307200000000), ((28804446398888504981:ℝ)/38400000000), ((-1891651297603809023:ℝ)/480000000), ((-101992462290094871:ℝ)/48000000), ((-6017908186790713:ℝ)/9600000), ((-120552269267:ℝ)/1000), ((-15552874461:ℝ)/1000), ((-261463437:ℝ)/200), ((-1300779:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((2192108358269701957605862117:ℝ)/61440000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((192286775302855051:ℝ)/16000000000) - ((21095774844071109:ℝ)/800000000)*t| ≤ ((65855210523547:ℝ)/1000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((23:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (122790:ℝ), (-3586680:ℝ), (28529720:ℝ), (-90761600:ℝ), (137804800:ℝ), ((-332136448:ℝ)/3), ((141819904:ℝ)/3), (-8388608:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_12 q| ≤ ((38604539581954361790553162:ℝ)/3662109375) := by
    rw [centralNum13_12_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((23:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (132555:ℝ), (-3252375:ℝ), ((39743695:ℝ)/2), ((-197111615:ℝ)/4), ((281947375:ℝ)/4), ((-1100234375:ℝ)/24), ((131828125:ℝ)/12), (-781250:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_12 q| ≤ ((23923360711271215960939:ℝ)/9375000) := by
    rw [centralNum23_12_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((423730466487991770665586377133:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece18_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece18_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-2043761438095559:ℝ)/1920000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((7565783997522728626048027901:ℝ)/245760000000000000) + ((192286775302855051:ℝ)/16000000000)*(0:ℝ) - ((-154769470312301349:ℝ)/200000000000)) (β := ((-33404440727203:ℝ)/24000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((282328766942340026513151547:ℝ)/3072000000000000) - 3*((7565783997522728626048027901:ℝ)/245760000000000000)) + ((21095774844071109:ℝ)/800000000)*(0:ℝ) - ((-139611729824300399:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_18 1 2 = centralNum11_12 q + 8*(Real.exp (-(3*((91:ℝ)/20)))*Real.exp (-3*t))*centralNum12_12 q + 18*Real.exp (-8*q)*centralNum13_12 q + 72*Real.exp (-11*q)*centralNum23_12 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_12, pieceX_18, sym4_12, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((33829799868310738106418230774040789224010240321747372938857:ℝ)/82868042140453567599421241262025018984785292834468529006979000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-2043761438095559:ℝ)/1920000000) + ((-33404440727203:ℝ)/24000000)*t) + (8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((7565783997522728626048027901:ℝ)/245760000000000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((282328766942340026513151547:ℝ)/3072000000000000) - 3*((7565783997522728626048027901:ℝ)/245760000000000000))*t) + (((192286775302855051:ℝ)/16000000000) + ((21095774844071109:ℝ)/800000000)*t)*(0:ℝ) - (((-154769470312301349:ℝ)/200000000000) + t * ((-139611729824300399:ℝ)/100000000000)) = (((-2043761438095559:ℝ)/1920000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((7565783997522728626048027901:ℝ)/245760000000000000) + ((192286775302855051:ℝ)/16000000000)*(0:ℝ) - ((-154769470312301349:ℝ)/200000000000)) + t*(((-33404440727203:ℝ)/24000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((282328766942340026513151547:ℝ)/3072000000000000) - 3*((7565783997522728626048027901:ℝ)/245760000000000000)) + ((21095774844071109:ℝ)/800000000)*(0:ℝ) - ((-139611729824300399:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece18_e13 {q : ℝ} (h0 : ((9:ℝ)/2) ≤ q) (h1 : q ≤ ((23:ℝ)/5)) :
    |pieceW q pieceX_18 1 3 - (((-872669267308081283:ℝ)/1000000000000) + (q - ((91:ℝ)/20)) * ((-57804870482199827:ℝ)/500000000000))| ≤ ((14906657229642323:ℝ)/1000000000000) := by
  set t := q - ((91:ℝ)/20) with htd
  have hq : q = ((91:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece18_L3 piece18_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((91:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_13 q = ∑ e ∈ Finset.range 7, ([((-1703607756123:ℝ)/3200000), ((-56162893059:ℝ)/80000), ((-617174649:ℝ)/1600), ((-2260713:ℝ)/20), ((-74529:ℝ)/4), (-1638:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_13; ring
  have h12 : centralNum12_13 q = ∑ e ∈ Finset.range 15, ([((-118122076594724558396104967721:ℝ)/3276800000000000000), ((-7540296927876015105787367019:ℝ)/163840000000000000), ((70813223419888529276087391:ℝ)/2048000000000000), ((24048464908163745109599903:ℝ)/204800000000000), ((2390044089197577123967929:ℝ)/20480000000000), ((66395017660491886185183:ℝ)/1024000000000), ((566952112396206878181:ℝ)/25600000000), ((2768450356476260157:ℝ)/640000000), ((24696124203971337:ℝ)/128000000), ((-946767960563517:ℝ)/6400000), ((-1921841833887:ℝ)/40000), ((-431944036479:ℝ)/56000), ((-4106502927:ℝ)/5600), ((-11064033:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_13; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-1703607756123:ℝ)/3200000), ((-56162893059:ℝ)/80000), ((-617174649:ℝ)/1600), ((-2260713:ℝ)/20), ((-74529:ℝ)/4), (-1638:ℝ), (-60:ℝ)] : List ℝ).getD e 0) 5 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-118122076594724558396104967721:ℝ)/3276800000000000000), ((-7540296927876015105787367019:ℝ)/163840000000000000), ((70813223419888529276087391:ℝ)/2048000000000000), ((24048464908163745109599903:ℝ)/204800000000000), ((2390044089197577123967929:ℝ)/20480000000000), ((66395017660491886185183:ℝ)/1024000000000), ((566952112396206878181:ℝ)/25600000000), ((2768450356476260157:ℝ)/640000000), ((24696124203971337:ℝ)/128000000), ((-946767960563517:ℝ)/6400000), ((-1921841833887:ℝ)/40000), ((-431944036479:ℝ)/56000), ((-4106502927:ℝ)/5600), ((-11064033:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-118122076594724558396104967721:ℝ)/3276800000000000000), ((-7540296927876015105787367019:ℝ)/163840000000000000), ((70813223419888529276087391:ℝ)/2048000000000000), ((24048464908163745109599903:ℝ)/204800000000000), ((2390044089197577123967929:ℝ)/20480000000000), ((66395017660491886185183:ℝ)/1024000000000), ((566952112396206878181:ℝ)/25600000000), ((2768450356476260157:ℝ)/640000000), ((24696124203971337:ℝ)/128000000), ((-946767960563517:ℝ)/6400000), ((-1921841833887:ℝ)/40000), ((-431944036479:ℝ)/56000), ((-4106502927:ℝ)/5600), ((-11064033:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 7, ([((-1703607756123:ℝ)/3200000), ((-56162893059:ℝ)/80000), ((-617174649:ℝ)/1600), ((-2260713:ℝ)/20), ((-74529:ℝ)/4), (-1638:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e) - (((-1703607756123:ℝ)/3200000) + ((-56162893059:ℝ)/80000)*t)| ≤ ((3131461791:ℝ)/3200000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-118122076594724558396104967721:ℝ)/3276800000000000000), ((-7540296927876015105787367019:ℝ)/163840000000000000), ((70813223419888529276087391:ℝ)/2048000000000000), ((24048464908163745109599903:ℝ)/204800000000000), ((2390044089197577123967929:ℝ)/20480000000000), ((66395017660491886185183:ℝ)/1024000000000), ((566952112396206878181:ℝ)/25600000000), ((2768450356476260157:ℝ)/640000000), ((24696124203971337:ℝ)/128000000), ((-946767960563517:ℝ)/6400000), ((-1921841833887:ℝ)/40000), ((-431944036479:ℝ)/56000), ((-4106502927:ℝ)/5600), ((-11064033:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((-118122076594724558396104967721:ℝ)/3276800000000000000) - ((-7540296927876015105787367019:ℝ)/163840000000000000)*t| ≤ ((1168325926622484999433795497:ℝ)/11468800000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-118122076594724558396104967721:ℝ)/3276800000000000000), ((-7540296927876015105787367019:ℝ)/163840000000000000), ((70813223419888529276087391:ℝ)/2048000000000000), ((24048464908163745109599903:ℝ)/204800000000000), ((2390044089197577123967929:ℝ)/20480000000000), ((66395017660491886185183:ℝ)/1024000000000), ((566952112396206878181:ℝ)/25600000000), ((2768450356476260157:ℝ)/640000000), ((24696124203971337:ℝ)/128000000), ((-946767960563517:ℝ)/6400000), ((-1921841833887:ℝ)/40000), ((-431944036479:ℝ)/56000), ((-4106502927:ℝ)/5600), ((-11064033:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((440986633255724492256056967087:ℝ)/11468800000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((192286775302855051:ℝ)/16000000000) - ((21095774844071109:ℝ)/800000000)*t| ≤ ((65855210523547:ℝ)/1000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((23:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2325540:ℝ), (52589280:ℝ), (-375655200:ℝ), (1192958720:ℝ), (-1965096960:ℝ), ((12857851904:ℝ)/7), ((-21171273728:ℝ)/21), ((914358272:ℝ)/3), ((-268435456:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_13 q| ≤ ((42878825026376425095126467572:ℝ)/128173828125) := by
    rw [centralNum13_13_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((23:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2399070:ℝ), (45666930:ℝ), (-251781675:ℝ), ((2452738385:ℝ)/4), ((-14104310625:ℝ)/16), ((74345740625:ℝ)/112), ((-74899765625:ℝ)/336), ((5161328125:ℝ)/168), ((-9765625:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_13 q| ≤ ((6910993019769648667315609:ℝ)/131250000) := by
    rw [centralNum23_13_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((423730466487991770665586377133:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece18_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece18_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-1703607756123:ℝ)/3200000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((-118122076594724558396104967721:ℝ)/3276800000000000000) + ((192286775302855051:ℝ)/16000000000)*(0:ℝ) - ((-872669267308081283:ℝ)/1000000000000)) (β := ((-56162893059:ℝ)/80000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((-7540296927876015105787367019:ℝ)/163840000000000000) - 3*((-118122076594724558396104967721:ℝ)/3276800000000000000)) + ((21095774844071109:ℝ)/800000000)*(0:ℝ) - ((-57804870482199827:ℝ)/500000000000)) ht
  have hW : pieceW q pieceX_18 1 3 = centralNum11_13 q + 8*(Real.exp (-(3*((91:ℝ)/20)))*Real.exp (-3*t))*centralNum12_13 q + 18*Real.exp (-8*q)*centralNum13_13 q + 72*Real.exp (-11*q)*centralNum23_13 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_13, pieceX_18, sym4_13, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((18251580564608188983157297355925219434226654559566306696993:ℝ)/92075602378281741777134712513361132205316992038298365563310000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-1703607756123:ℝ)/3200000) + ((-56162893059:ℝ)/80000)*t) + (8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((-118122076594724558396104967721:ℝ)/3276800000000000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((-7540296927876015105787367019:ℝ)/163840000000000000) - 3*((-118122076594724558396104967721:ℝ)/3276800000000000000))*t) + (((192286775302855051:ℝ)/16000000000) + ((21095774844071109:ℝ)/800000000)*t)*(0:ℝ) - (((-872669267308081283:ℝ)/1000000000000) + t * ((-57804870482199827:ℝ)/500000000000)) = (((-1703607756123:ℝ)/3200000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((-118122076594724558396104967721:ℝ)/3276800000000000000) + ((192286775302855051:ℝ)/16000000000)*(0:ℝ) - ((-872669267308081283:ℝ)/1000000000000)) + t*(((-56162893059:ℝ)/80000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((-7540296927876015105787367019:ℝ)/163840000000000000) - 3*((-118122076594724558396104967721:ℝ)/3276800000000000000)) + ((21095774844071109:ℝ)/800000000)*(0:ℝ) - ((-57804870482199827:ℝ)/500000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece18_e22 {q : ℝ} (h0 : ((9:ℝ)/2) ≤ q) (h1 : q ≤ ((23:ℝ)/5)) :
    |pieceW q pieceX_18 2 2 - (((834810556333609741:ℝ)/100000000000) + (q - ((91:ℝ)/20)) * ((101628291800212239:ℝ)/5000000000))| ≤ ((826609247315420707:ℝ)/10000000000000) := by
  set t := q - ((91:ℝ)/20) with htd
  have hq : q = ((91:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece18_L3 piece18_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((91:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_22 q = ∑ e ∈ Finset.range 10, ([((173709026327155501:ℝ)/19200000000), ((18301832065544209:ℝ)/960000000), ((214945260502609:ℝ)/12000000), ((1978522994357:ℝ)/200000), ((213047033563:ℝ)/60000), ((2581907563:ℝ)/3000), ((3523607:ℝ)/25), ((225436:ℝ)/15), ((2836:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_22; ring
  have h12 : centralNum12_22 q = ∑ e ∈ Finset.range 15, ([((-3463298929141568303437289066701:ℝ)/39321600000000000000), ((-317224650445830562343973616279:ℝ)/1966080000000000000), ((-1221301596314150638155514009:ℝ)/24576000000000000), ((100741163851343546446185361:ℝ)/819200000000000), ((41515375467064955252724109:ℝ)/245760000000000), ((1312733126469357179398123:ℝ)/12288000000000), ((4118327935087540565907:ℝ)/102400000000), ((69057002160527236457:ℝ)/7680000000), ((1269726316192294157:ℝ)/1536000000), ((-12048230083226257:ℝ)/76800000), ((-11227017005799:ℝ)/160000), ((-392870296359:ℝ)/32000), ((-3904923087:ℝ)/3200), ((-10830753:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_22; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((173709026327155501:ℝ)/19200000000), ((18301832065544209:ℝ)/960000000), ((214945260502609:ℝ)/12000000), ((1978522994357:ℝ)/200000), ((213047033563:ℝ)/60000), ((2581907563:ℝ)/3000), ((3523607:ℝ)/25), ((225436:ℝ)/15), ((2836:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-3463298929141568303437289066701:ℝ)/39321600000000000000), ((-317224650445830562343973616279:ℝ)/1966080000000000000), ((-1221301596314150638155514009:ℝ)/24576000000000000), ((100741163851343546446185361:ℝ)/819200000000000), ((41515375467064955252724109:ℝ)/245760000000000), ((1312733126469357179398123:ℝ)/12288000000000), ((4118327935087540565907:ℝ)/102400000000), ((69057002160527236457:ℝ)/7680000000), ((1269726316192294157:ℝ)/1536000000), ((-12048230083226257:ℝ)/76800000), ((-11227017005799:ℝ)/160000), ((-392870296359:ℝ)/32000), ((-3904923087:ℝ)/3200), ((-10830753:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-3463298929141568303437289066701:ℝ)/39321600000000000000), ((-317224650445830562343973616279:ℝ)/1966080000000000000), ((-1221301596314150638155514009:ℝ)/24576000000000000), ((100741163851343546446185361:ℝ)/819200000000000), ((41515375467064955252724109:ℝ)/245760000000000), ((1312733126469357179398123:ℝ)/12288000000000), ((4118327935087540565907:ℝ)/102400000000), ((69057002160527236457:ℝ)/7680000000), ((1269726316192294157:ℝ)/1536000000), ((-12048230083226257:ℝ)/76800000), ((-11227017005799:ℝ)/160000), ((-392870296359:ℝ)/32000), ((-3904923087:ℝ)/3200), ((-10830753:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((173709026327155501:ℝ)/19200000000), ((18301832065544209:ℝ)/960000000), ((214945260502609:ℝ)/12000000), ((1978522994357:ℝ)/200000), ((213047033563:ℝ)/60000), ((2581907563:ℝ)/3000), ((3523607:ℝ)/25), ((225436:ℝ)/15), ((2836:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((173709026327155501:ℝ)/19200000000) + ((18301832065544209:ℝ)/960000000)*t)| ≤ ((441977309167201:ℝ)/9600000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-3463298929141568303437289066701:ℝ)/39321600000000000000), ((-317224650445830562343973616279:ℝ)/1966080000000000000), ((-1221301596314150638155514009:ℝ)/24576000000000000), ((100741163851343546446185361:ℝ)/819200000000000), ((41515375467064955252724109:ℝ)/245760000000000), ((1312733126469357179398123:ℝ)/12288000000000), ((4118327935087540565907:ℝ)/102400000000), ((69057002160527236457:ℝ)/7680000000), ((1269726316192294157:ℝ)/1536000000), ((-12048230083226257:ℝ)/76800000), ((-11227017005799:ℝ)/160000), ((-392870296359:ℝ)/32000), ((-3904923087:ℝ)/3200), ((-10830753:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e) - ((-3463298929141568303437289066701:ℝ)/39321600000000000000) - ((-317224650445830562343973616279:ℝ)/1966080000000000000)*t| ≤ ((2766253232217931837368185167:ℝ)/19660800000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-3463298929141568303437289066701:ℝ)/39321600000000000000), ((-317224650445830562343973616279:ℝ)/1966080000000000000), ((-1221301596314150638155514009:ℝ)/24576000000000000), ((100741163851343546446185361:ℝ)/819200000000000), ((41515375467064955252724109:ℝ)/245760000000000), ((1312733126469357179398123:ℝ)/12288000000000), ((4118327935087540565907:ℝ)/102400000000), ((69057002160527236457:ℝ)/7680000000), ((1269726316192294157:ℝ)/1536000000), ((-12048230083226257:ℝ)/76800000), ((-11227017005799:ℝ)/160000), ((-392870296359:ℝ)/32000), ((-3904923087:ℝ)/3200), ((-10830753:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e)| ≤ ((1893028043025917364727999526657:ℝ)/19660800000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((192286775302855051:ℝ)/16000000000) - ((21095774844071109:ℝ)/800000000)*t| ≤ ((65855210523547:ℝ)/1000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((23:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82125:ℝ), (-6663750:ℝ), (115666200:ℝ), (-750437000:ℝ), (2277262000:ℝ), (-3656824320:ℝ), (3359621120:ℝ), (-1817706496:ℝ), ((1625292800:ℝ)/3), (-67108864:ℝ)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_22 q| ≤ ((10943305491776870872605948503:ℝ)/18310546875) := by
    rw [centralNum13_22_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((23:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((178425:ℝ)/2), ((-13176075:ℝ)/2), ((777815145:ℝ)/8), ((-3968389015:ℝ)/8), ((9393350195:ℝ)/8), ((-26366634375:ℝ)/16), ((77851609375:ℝ)/64), ((-25714921875:ℝ)/64), ((5236328125:ℝ)/96), ((-9765625:ℝ)/4)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_22 q| ≤ ((3567722972129215821427789:ℝ)/37500000) := by
    rw [centralNum23_22_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((423730466487991770665586377133:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece18_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece18_E11 h0) m23'
  have c5 := scaled_affine (X := ((11:ℝ)/1000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2))| ≤ ((7489042521053275798254602240000000:ℝ)/2272258454519463085256305851178265871) := by
    rw [abs_neg, tailWeight_2, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((23:ℝ)/5)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((23:ℝ)/5)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece18_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((2570430941234500:ℝ)/4782969)) ≤ ((23:ℝ)/5)^6*(8000*(2*((23:ℝ)/5)-3)^2*(1/((475072795688088943343832220359:ℝ)/1000000000))*((2570430941234500:ℝ)/4782969)) := by
          gcongr
      _ ≤ ((7489042521053275798254602240000000:ℝ)/2272258454519463085256305851178265871) := by norm_num
  have c7 := affine_round (α := ((173709026327155501:ℝ)/19200000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((-3463298929141568303437289066701:ℝ)/39321600000000000000) + ((192286775302855051:ℝ)/16000000000)*((11:ℝ)/1000) - ((834810556333609741:ℝ)/100000000000)) (β := ((18301832065544209:ℝ)/960000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((-317224650445830562343973616279:ℝ)/1966080000000000000) - 3*((-3463298929141568303437289066701:ℝ)/39321600000000000000)) + ((21095774844071109:ℝ)/800000000)*((11:ℝ)/1000) - ((101628291800212239:ℝ)/5000000000)) ht
  have hW : pieceW q pieceX_18 2 2 = centralNum11_22 q + 8*(Real.exp (-(3*((91:ℝ)/20)))*Real.exp (-3*t))*centralNum12_22 q + 18*Real.exp (-8*q)*centralNum13_22 q + 72*Real.exp (-11*q)*centralNum23_22 q + 8*q^7*(2*q-3)^2*((11:ℝ)/1000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2)) := by
    rw [pieceW_22, pieceX_18, sym4_22, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((213602494996701936072406250887432898195383801792607900655549:ℝ)/73660481902625393421707770010688905764253593630638692450648000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((173709026327155501:ℝ)/19200000000) + ((18301832065544209:ℝ)/960000000)*t) + (8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((-3463298929141568303437289066701:ℝ)/39321600000000000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((-317224650445830562343973616279:ℝ)/1966080000000000000) - 3*((-3463298929141568303437289066701:ℝ)/39321600000000000000))*t) + (((192286775302855051:ℝ)/16000000000) + ((21095774844071109:ℝ)/800000000)*t)*((11:ℝ)/1000) - (((834810556333609741:ℝ)/100000000000) + t * ((101628291800212239:ℝ)/5000000000)) = (((173709026327155501:ℝ)/19200000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((-3463298929141568303437289066701:ℝ)/39321600000000000000) + ((192286775302855051:ℝ)/16000000000)*((11:ℝ)/1000) - ((834810556333609741:ℝ)/100000000000)) + t*(((18301832065544209:ℝ)/960000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((-317224650445830562343973616279:ℝ)/1966080000000000000) - 3*((-3463298929141568303437289066701:ℝ)/39321600000000000000)) + ((21095774844071109:ℝ)/800000000)*((11:ℝ)/1000) - ((101628291800212239:ℝ)/5000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece18_e23 {q : ℝ} (h0 : ((9:ℝ)/2) ≤ q) (h1 : q ≤ ((23:ℝ)/5)) :
    |pieceW q pieceX_18 2 3 - (((3822506233817391:ℝ)/2000000000) + (q - ((91:ℝ)/20)) * ((499555347240601719:ℝ)/1000000000000))| ≤ ((29925558548528623:ℝ)/200000000000) := by
  set t := q - ((91:ℝ)/20) with htd
  have hq : q = ((91:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece18_L3 piece18_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((91:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_23 q = ∑ e ∈ Finset.range 9, ([((638778024688713:ℝ)/320000000), ((112960310232133:ℝ)/32000000), ((4691237949853:ℝ)/1600000), ((118723877181:ℝ)/80000), ((393618589:ℝ)/800), ((21458231:ℝ)/200), ((147903:ℝ)/10), (1166:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_23; ring
  have h12 : centralNum12_23 q = ∑ e ∈ Finset.range 16, ([((-4716843731159405469484401019479:ℝ)/524288000000000000000), ((-912297506061685434647515074607:ℝ)/2621440000000000000), ((-229138346406883535251004041667:ℝ)/262144000000000000), ((-6355678417247859420371562093:ℝ)/6553600000000000), ((-77316709447347376017551267:ℝ)/131072000000000), ((-15672823378216016457715111:ℝ)/81920000000000), ((-20893783001852605918983:ℝ)/1638400000000), ((690644677671985336343:ℝ)/40960000000), ((33533410691208842383:ℝ)/4096000000), ((38592931461934791:ℝ)/20480000), ((11123480902230243:ℝ)/51200000), ((526711868271:ℝ)/1792000), ((-685734227379:ℝ)/179200), ((-2565641871:ℝ)/4480), ((-17288235:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_23; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((638778024688713:ℝ)/320000000), ((112960310232133:ℝ)/32000000), ((4691237949853:ℝ)/1600000), ((118723877181:ℝ)/80000), ((393618589:ℝ)/800), ((21458231:ℝ)/200), ((147903:ℝ)/10), (1166:ℝ), (40:ℝ)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-4716843731159405469484401019479:ℝ)/524288000000000000000), ((-912297506061685434647515074607:ℝ)/2621440000000000000), ((-229138346406883535251004041667:ℝ)/262144000000000000), ((-6355678417247859420371562093:ℝ)/6553600000000000), ((-77316709447347376017551267:ℝ)/131072000000000), ((-15672823378216016457715111:ℝ)/81920000000000), ((-20893783001852605918983:ℝ)/1638400000000), ((690644677671985336343:ℝ)/40960000000), ((33533410691208842383:ℝ)/4096000000), ((38592931461934791:ℝ)/20480000), ((11123480902230243:ℝ)/51200000), ((526711868271:ℝ)/1792000), ((-685734227379:ℝ)/179200), ((-2565641871:ℝ)/4480), ((-17288235:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 14 ht
  have m12 := abs_poly_le (fun e => ([((-4716843731159405469484401019479:ℝ)/524288000000000000000), ((-912297506061685434647515074607:ℝ)/2621440000000000000), ((-229138346406883535251004041667:ℝ)/262144000000000000), ((-6355678417247859420371562093:ℝ)/6553600000000000), ((-77316709447347376017551267:ℝ)/131072000000000), ((-15672823378216016457715111:ℝ)/81920000000000), ((-20893783001852605918983:ℝ)/1638400000000), ((690644677671985336343:ℝ)/40960000000), ((33533410691208842383:ℝ)/4096000000), ((38592931461934791:ℝ)/20480000), ((11123480902230243:ℝ)/51200000), ((526711868271:ℝ)/1792000), ((-685734227379:ℝ)/179200), ((-2565641871:ℝ)/4480), ((-17288235:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 16 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((638778024688713:ℝ)/320000000), ((112960310232133:ℝ)/32000000), ((4691237949853:ℝ)/1600000), ((118723877181:ℝ)/80000), ((393618589:ℝ)/800), ((21458231:ℝ)/200), ((147903:ℝ)/10), (1166:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e) - (((638778024688713:ℝ)/320000000) + ((112960310232133:ℝ)/32000000)*t)| ≤ ((4811951526697:ℝ)/640000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 16, ([((-4716843731159405469484401019479:ℝ)/524288000000000000000), ((-912297506061685434647515074607:ℝ)/2621440000000000000), ((-229138346406883535251004041667:ℝ)/262144000000000000), ((-6355678417247859420371562093:ℝ)/6553600000000000), ((-77316709447347376017551267:ℝ)/131072000000000), ((-15672823378216016457715111:ℝ)/81920000000000), ((-20893783001852605918983:ℝ)/1638400000000), ((690644677671985336343:ℝ)/40960000000), ((33533410691208842383:ℝ)/4096000000), ((38592931461934791:ℝ)/20480000), ((11123480902230243:ℝ)/51200000), ((526711868271:ℝ)/1792000), ((-685734227379:ℝ)/179200), ((-2565641871:ℝ)/4480), ((-17288235:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e) - ((-4716843731159405469484401019479:ℝ)/524288000000000000000) - ((-912297506061685434647515074607:ℝ)/2621440000000000000)*t| ≤ ((8478490237943641983416646066093:ℝ)/3670016000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 16, ([((-4716843731159405469484401019479:ℝ)/524288000000000000000), ((-912297506061685434647515074607:ℝ)/2621440000000000000), ((-229138346406883535251004041667:ℝ)/262144000000000000), ((-6355678417247859420371562093:ℝ)/6553600000000000), ((-77316709447347376017551267:ℝ)/131072000000000), ((-15672823378216016457715111:ℝ)/81920000000000), ((-20893783001852605918983:ℝ)/1638400000000), ((690644677671985336343:ℝ)/40960000000), ((33533410691208842383:ℝ)/4096000000), ((38592931461934791:ℝ)/20480000), ((11123480902230243:ℝ)/51200000), ((526711868271:ℝ)/1792000), ((-685734227379:ℝ)/179200), ((-2565641871:ℝ)/4480), ((-17288235:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e)| ≤ ((13169652722547182586891688553117:ℝ)/458752000000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((192286775302855051:ℝ)/16000000000) - ((21095774844071109:ℝ)/800000000)*t| ≤ ((65855210523547:ℝ)/1000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((23:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-7627725:ℝ)/2), (173988600:ℝ), (-2299614450:ℝ), (13088188200:ℝ), (-38221499200:ℝ), (63366115840:ℝ), ((-445610508288:ℝ)/7), ((841540698112:ℝ)/21), ((-326820167680:ℝ)/21), ((10133438464:ℝ)/3), ((-2147483648:ℝ)/7)] : List ℝ).getD e 0) 16 hq1'
  have m13' : |centralNum13_23 q| ≤ ((8830401473856933396339042169737:ℝ)/427246093750) := by
    rw [centralNum13_23_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((23:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-15801525:ℝ)/4), ((655493865:ℝ)/4), ((-7334421225:ℝ)/4), ((16442962485:ℝ)/2), ((-598626108395:ℝ)/32), ((414013307125:ℝ)/16), ((-4611984703125:ℝ)/224), ((399923828125:ℝ)/48), ((-4353201171875:ℝ)/2688), ((189736328125:ℝ)/1344), ((-244140625:ℝ)/56)] : List ℝ).getD e 0) 16 hq1'
  have m23' : |centralNum23_23 q| ≤ ((788663376510063091952340401:ℝ)/350000000) := by
    rw [centralNum23_23_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((423730466487991770665586377133:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece18_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece18_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((638778024688713:ℝ)/320000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((-4716843731159405469484401019479:ℝ)/524288000000000000000) + ((192286775302855051:ℝ)/16000000000)*(0:ℝ) - ((3822506233817391:ℝ)/2000000000)) (β := ((112960310232133:ℝ)/32000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((-912297506061685434647515074607:ℝ)/2621440000000000000) - 3*((-4716843731159405469484401019479:ℝ)/524288000000000000000)) + ((21095774844071109:ℝ)/800000000)*(0:ℝ) - ((499555347240601719:ℝ)/1000000000000)) ht
  have hW : pieceW q pieceX_18 2 3 = centralNum11_23 q + 8*(Real.exp (-(3*((91:ℝ)/20)))*Real.exp (-3*t))*centralNum12_23 q + 18*Real.exp (-8*q)*centralNum13_23 q + 72*Real.exp (-11*q)*centralNum23_23 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_23, pieceX_18, sym4_23, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((2403612847761861486469403923456975728697555997117976047335217:ℝ)/552453614269690450662808275080166793231901952229790193379860000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((638778024688713:ℝ)/320000000) + ((112960310232133:ℝ)/32000000)*t) + (8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((-4716843731159405469484401019479:ℝ)/524288000000000000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((-912297506061685434647515074607:ℝ)/2621440000000000000) - 3*((-4716843731159405469484401019479:ℝ)/524288000000000000000))*t) + (((192286775302855051:ℝ)/16000000000) + ((21095774844071109:ℝ)/800000000)*t)*(0:ℝ) - (((3822506233817391:ℝ)/2000000000) + t * ((499555347240601719:ℝ)/1000000000000)) = (((638778024688713:ℝ)/320000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((-4716843731159405469484401019479:ℝ)/524288000000000000000) + ((192286775302855051:ℝ)/16000000000)*(0:ℝ) - ((3822506233817391:ℝ)/2000000000)) + t*(((112960310232133:ℝ)/32000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((-912297506061685434647515074607:ℝ)/2621440000000000000) - 3*((-4716843731159405469484401019479:ℝ)/524288000000000000000)) + ((21095774844071109:ℝ)/800000000)*(0:ℝ) - ((499555347240601719:ℝ)/1000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece18_e33 {q : ℝ} (h0 : ((9:ℝ)/2) ≤ q) (h1 : q ≤ ((23:ℝ)/5)) :
    |pieceW q pieceX_18 3 3 - (((761251965983191817:ℝ)/100000000000) + (q - ((91:ℝ)/20)) * ((68025958747256129:ℝ)/5000000000))| ≤ ((361802895941534139:ℝ)/100000000000) := by
  set t := q - ((91:ℝ)/20) with htd
  have hq : q = ((91:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece18_L3 piece18_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((91:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_33 q = ∑ e ∈ Finset.range 10, ([((9146214430583503:ℝ)/3200000000), ((618579268419021:ℝ)/80000000), ((68882349343353:ℝ)/8000000), ((2147116154547:ℝ)/400000), ((42204915843:ℝ)/20000), ((550936803:ℝ)/1000), ((4828467:ℝ)/50), ((386142:ℝ)/35), ((5232:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_33; ring
  have h12 : centralNum12_33 q = ∑ e ∈ Finset.range 17, ([((10268374748259148254846977898683377:ℝ)/20971520000000000000000), ((2160393885575371910489147979830337:ℝ)/1048576000000000000000), ((32895654661858619806694481485523:ℝ)/10485760000000000000), ((1182099341182336299509170389369:ℝ)/524288000000000000), ((15629553995931681728929910643:ℝ)/26214400000000000), ((-1767676454079273880830932739:ℝ)/6553600000000000), ((-99883965264563332232998269:ℝ)/327680000000000), ((-2875261386967122917642493:ℝ)/22937600000000), ((-29994120130156560666609:ℝ)/1146880000000), ((-76870683657265817983:ℝ)/57344000000), ((1528992207507244941:ℝ)/2048000000), ((152202348324742257:ℝ)/716800000), ((169918103126871:ℝ)/7168000), ((20848533219:ℝ)/51200), ((-23819598963:ℝ)/125440), ((-631410957:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_33; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((9146214430583503:ℝ)/3200000000), ((618579268419021:ℝ)/80000000), ((68882349343353:ℝ)/8000000), ((2147116154547:ℝ)/400000), ((42204915843:ℝ)/20000), ((550936803:ℝ)/1000), ((4828467:ℝ)/50), ((386142:ℝ)/35), ((5232:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((10268374748259148254846977898683377:ℝ)/20971520000000000000000), ((2160393885575371910489147979830337:ℝ)/1048576000000000000000), ((32895654661858619806694481485523:ℝ)/10485760000000000000), ((1182099341182336299509170389369:ℝ)/524288000000000000), ((15629553995931681728929910643:ℝ)/26214400000000000), ((-1767676454079273880830932739:ℝ)/6553600000000000), ((-99883965264563332232998269:ℝ)/327680000000000), ((-2875261386967122917642493:ℝ)/22937600000000), ((-29994120130156560666609:ℝ)/1146880000000), ((-76870683657265817983:ℝ)/57344000000), ((1528992207507244941:ℝ)/2048000000), ((152202348324742257:ℝ)/716800000), ((169918103126871:ℝ)/7168000), ((20848533219:ℝ)/51200), ((-23819598963:ℝ)/125440), ((-631410957:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 15 ht
  have m12 := abs_poly_le (fun e => ([((10268374748259148254846977898683377:ℝ)/20971520000000000000000), ((2160393885575371910489147979830337:ℝ)/1048576000000000000000), ((32895654661858619806694481485523:ℝ)/10485760000000000000), ((1182099341182336299509170389369:ℝ)/524288000000000000), ((15629553995931681728929910643:ℝ)/26214400000000000), ((-1767676454079273880830932739:ℝ)/6553600000000000), ((-99883965264563332232998269:ℝ)/327680000000000), ((-2875261386967122917642493:ℝ)/22937600000000), ((-29994120130156560666609:ℝ)/1146880000000), ((-76870683657265817983:ℝ)/57344000000), ((1528992207507244941:ℝ)/2048000000), ((152202348324742257:ℝ)/716800000), ((169918103126871:ℝ)/7168000), ((20848533219:ℝ)/51200), ((-23819598963:ℝ)/125440), ((-631410957:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 17 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((9146214430583503:ℝ)/3200000000), ((618579268419021:ℝ)/80000000), ((68882349343353:ℝ)/8000000), ((2147116154547:ℝ)/400000), ((42204915843:ℝ)/20000), ((550936803:ℝ)/1000), ((4828467:ℝ)/50), ((386142:ℝ)/35), ((5232:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e) - (((9146214430583503:ℝ)/3200000000) + ((618579268419021:ℝ)/80000000)*t)| ≤ ((497505583446817:ℝ)/22400000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 17, ([((10268374748259148254846977898683377:ℝ)/20971520000000000000000), ((2160393885575371910489147979830337:ℝ)/1048576000000000000000), ((32895654661858619806694481485523:ℝ)/10485760000000000000), ((1182099341182336299509170389369:ℝ)/524288000000000000), ((15629553995931681728929910643:ℝ)/26214400000000000), ((-1767676454079273880830932739:ℝ)/6553600000000000), ((-99883965264563332232998269:ℝ)/327680000000000), ((-2875261386967122917642493:ℝ)/22937600000000), ((-29994120130156560666609:ℝ)/1146880000000), ((-76870683657265817983:ℝ)/57344000000), ((1528992207507244941:ℝ)/2048000000), ((152202348324742257:ℝ)/716800000), ((169918103126871:ℝ)/7168000), ((20848533219:ℝ)/51200), ((-23819598963:ℝ)/125440), ((-631410957:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e) - ((10268374748259148254846977898683377:ℝ)/20971520000000000000000) - ((2160393885575371910489147979830337:ℝ)/1048576000000000000000)*t| ≤ ((1044121322952661821298334509158643:ℝ)/128450560000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 17, ([((10268374748259148254846977898683377:ℝ)/20971520000000000000000), ((2160393885575371910489147979830337:ℝ)/1048576000000000000000), ((32895654661858619806694481485523:ℝ)/10485760000000000000), ((1182099341182336299509170389369:ℝ)/524288000000000000), ((15629553995931681728929910643:ℝ)/26214400000000000), ((-1767676454079273880830932739:ℝ)/6553600000000000), ((-99883965264563332232998269:ℝ)/327680000000000), ((-2875261386967122917642493:ℝ)/22937600000000), ((-29994120130156560666609:ℝ)/1146880000000), ((-76870683657265817983:ℝ)/57344000000), ((1528992207507244941:ℝ)/2048000000), ((152202348324742257:ℝ)/716800000), ((169918103126871:ℝ)/7168000), ((20848533219:ℝ)/51200), ((-23819598963:ℝ)/125440), ((-631410957:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e)| ≤ ((61736263364151278267185684412044113:ℝ)/102760448000000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((192286775302855051:ℝ)/16000000000), ((21095774844071109:ℝ)/800000000), ((128032675210167:ℝ)/5000000), ((902926511487:ℝ)/62500), ((261001576563:ℝ)/50000), ((3132478713:ℝ)/2500), ((24980592:ℝ)/125), ((510672:ℝ)/25), ((6072:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((192286775302855051:ℝ)/16000000000) - ((21095774844071109:ℝ)/800000000)*t| ≤ ((65855210523547:ℝ)/1000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((23:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-8120475:ℝ)/4), ((464861025:ℝ)/2), (-5906535975:ℝ), ((411904731750:ℝ)/7), ((-2024051769000:ℝ)/7), ((5554394637600:ℝ)/7), (-1314913862656:ℝ), ((9709155336192:ℝ)/7), ((-6724555112448:ℝ)/7), ((1313173667840:ℝ)/3), ((-6168244125696:ℝ)/49), ((3004329623552:ℝ)/147), ((-68719476736:ℝ)/49)] : List ℝ).getD e 0) 17 hq1'
  have m13' : |centralNum13_33 q| ≤ ((69483487326183213103708643404415407:ℝ)/89721679687500) := by
    rw [centralNum13_33_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((23:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-16872075:ℝ)/8), ((1833754545:ℝ)/8), ((-83998007145:ℝ)/16), ((4929124002765:ℝ)/112), ((-76723155584685:ℝ)/448), ((164888745653055:ℝ)/448), ((-63358359907625:ℝ)/128), ((364713160040625:ℝ)/896), ((-334937462578125:ℝ)/1792), ((245466998046875:ℝ)/5376), ((-72144521484375:ℝ)/12544), ((6518798828125:ℝ)/18816), ((-6103515625:ℝ)/784)] : List ℝ).getD e 0) 17 hq1'
  have m23' : |centralNum23_33 q| ≤ ((886594780693082690236307594407:ℝ)/14700000000) := by
    rw [centralNum23_33_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((423730466487991770665586377133:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece18_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece18_E11 h0) m23'
  have c5 := scaled_affine (X := ((11:ℝ)/1000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3))| ≤ ((9639642361839783585612281108480000000:ℝ)/61350978272025503301920257981813178517) := by
    rw [abs_neg, tailWeight_3, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((23:ℝ)/5)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((23:ℝ)/5)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece18_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((3308571812705231500:ℝ)/129140163)) ≤ ((23:ℝ)/5)^6*(8000*(2*((23:ℝ)/5)-3)^2*(1/((475072795688088943343832220359:ℝ)/1000000000))*((3308571812705231500:ℝ)/129140163)) := by
          gcongr
      _ ≤ ((9639642361839783585612281108480000000:ℝ)/61350978272025503301920257981813178517) := by norm_num
  have c7 := affine_round (α := ((9146214430583503:ℝ)/3200000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((10268374748259148254846977898683377:ℝ)/20971520000000000000000) + ((192286775302855051:ℝ)/16000000000)*((11:ℝ)/1000) - ((761251965983191817:ℝ)/100000000000)) (β := ((618579268419021:ℝ)/80000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((2160393885575371910489147979830337:ℝ)/1048576000000000000000) - 3*((10268374748259148254846977898683377:ℝ)/20971520000000000000000)) + ((21095774844071109:ℝ)/800000000)*((11:ℝ)/1000) - ((68025958747256129:ℝ)/5000000000)) ht
  have hW : pieceW q pieceX_18 3 3 = centralNum11_33 q + 8*(Real.exp (-(3*((91:ℝ)/20)))*Real.exp (-3*t))*centralNum12_33 q + 18*Real.exp (-8*q)*centralNum13_33 q + 72*Real.exp (-11*q)*centralNum23_33 q + 8*q^7*(2*q-3)^2*((11:ℝ)/1000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3)) := by
    rw [pieceW_33, pieceX_18, sym4_33, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((248515842814463708704645485324287241004588387406877812153737:ℝ)/220981445707876180265123310032066717292760780891916077351944000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((9146214430583503:ℝ)/3200000000) + ((618579268419021:ℝ)/80000000)*t) + (8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((10268374748259148254846977898683377:ℝ)/20971520000000000000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((2160393885575371910489147979830337:ℝ)/1048576000000000000000) - 3*((10268374748259148254846977898683377:ℝ)/20971520000000000000000))*t) + (((192286775302855051:ℝ)/16000000000) + ((21095774844071109:ℝ)/800000000)*t)*((11:ℝ)/1000) - (((761251965983191817:ℝ)/100000000000) + t * ((68025958747256129:ℝ)/5000000000)) = (((9146214430583503:ℝ)/3200000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*((10268374748259148254846977898683377:ℝ)/20971520000000000000000) + ((192286775302855051:ℝ)/16000000000)*((11:ℝ)/1000) - ((761251965983191817:ℝ)/100000000000)) + t*(((618579268419021:ℝ)/80000000) + 8*(((1/((423730466487991770665586377133:ℝ)/500000000000000000000000))+(1/((847460538421008944439567461473:ℝ)/1000000000000000000000000)))/2)*(((2160393885575371910489147979830337:ℝ)/1048576000000000000000) - 3*((10268374748259148254846977898683377:ℝ)/20971520000000000000000)) + ((21095774844071109:ℝ)/800000000)*((11:ℝ)/1000) - ((68025958747256129:ℝ)/5000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece18_plus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((140761053758443601:ℝ)/10000000000) + ((1:ℝ)/20)*((148245754415013519:ℝ)/5000000000) - (((721767640417918651:ℝ)/10000000000000) + ((150773132565981793:ℝ)/20000000000000) + ((293001859158566157:ℝ)/100000000000000) + ((145220887687742467:ℝ)/25000000000000)))
      (((-49578310324602231:ℝ)/25000000000) + ((1:ℝ)/20)*((-296803744602358439:ℝ)/100000000000))
      (((-333084860848658943:ℝ)/10000000000000) + ((1:ℝ)/20)*((-538021717640617213:ℝ)/10000000000000))
      (((114586758053177121:ℝ)/1000000000000) + ((1:ℝ)/20)*((-15705524216794431:ℝ)/250000000000))
      (((51388384803125341:ℝ)/5000000000) + ((1:ℝ)/20)*((102903351662483799:ℝ)/5000000000) - (((150773132565981793:ℝ)/20000000000000) + ((123586699897576311:ℝ)/2500000000000) + ((303517232516929:ℝ)/16000000000) + ((14906657229642323:ℝ)/1000000000000)))
      (((-154769470312301349:ℝ)/200000000000) + ((1:ℝ)/20)*((-139611729824300399:ℝ)/100000000000))
      (((-872669267308081283:ℝ)/1000000000000) + ((1:ℝ)/20)*((-57804870482199827:ℝ)/500000000000))
      (((834810556333609741:ℝ)/100000000000) + ((1:ℝ)/20)*((101628291800212239:ℝ)/5000000000) - (((293001859158566157:ℝ)/100000000000000) + ((303517232516929:ℝ)/16000000000) + ((826609247315420707:ℝ)/10000000000000) + ((29925558548528623:ℝ)/200000000000)))
      (((3822506233817391:ℝ)/2000000000) + ((1:ℝ)/20)*((499555347240601719:ℝ)/1000000000000))
      (((761251965983191817:ℝ)/100000000000) + ((1:ℝ)/20)*((68025958747256129:ℝ)/5000000000) - (((145220887687742467:ℝ)/25000000000000) + ((14906657229642323:ℝ)/1000000000000) + ((29925558548528623:ℝ)/200000000000) + ((361802895941534139:ℝ)/100000000000))) i j :=
  quadForm_nonneg_of_ldl ((618804345809012359:ℝ)/40000000000) ((337934288989758311303484535415185882297:ℝ)/30940217290450617950000000000000) ((1222535679292959669439856321727660596370884489763036528757515839:ℝ)/135173715595903324521393814166074352918800000000000000000) ((30937712949043003179512109038880797819241197129507691843037080429959945656390628373:ℝ)/7640847995580997933999102010797878727318028061018978304734473993750000000000) ((-4263068570570536919:ℝ)/30940217290450617950) ((-7199718934613796073:ℝ)/3094021729045061795000) ((557228266049091174:ℝ)/77350543226126544875) ((-5251255662603597405918963428543154474087:ℝ)/67586857797951662260696907083037176459400) ((-133521629085007254385695158033496643669:ℝ)/1689671444948791556517422677075929411485) ((252697919809202115166357151078640619997872670495929233618184920:ℝ)/1222535679292959669439856321727660596370884489763036528757515839)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece18_minus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((140761053758443601:ℝ)/10000000000) - ((1:ℝ)/20)*((148245754415013519:ℝ)/5000000000) - (((721767640417918651:ℝ)/10000000000000) + ((150773132565981793:ℝ)/20000000000000) + ((293001859158566157:ℝ)/100000000000000) + ((145220887687742467:ℝ)/25000000000000)))
      (((-49578310324602231:ℝ)/25000000000) - ((1:ℝ)/20)*((-296803744602358439:ℝ)/100000000000))
      (((-333084860848658943:ℝ)/10000000000000) - ((1:ℝ)/20)*((-538021717640617213:ℝ)/10000000000000))
      (((114586758053177121:ℝ)/1000000000000) - ((1:ℝ)/20)*((-15705524216794431:ℝ)/250000000000))
      (((51388384803125341:ℝ)/5000000000) - ((1:ℝ)/20)*((102903351662483799:ℝ)/5000000000) - (((150773132565981793:ℝ)/20000000000000) + ((123586699897576311:ℝ)/2500000000000) + ((303517232516929:ℝ)/16000000000) + ((14906657229642323:ℝ)/1000000000000)))
      (((-154769470312301349:ℝ)/200000000000) - ((1:ℝ)/20)*((-139611729824300399:ℝ)/100000000000))
      (((-872669267308081283:ℝ)/1000000000000) - ((1:ℝ)/20)*((-57804870482199827:ℝ)/500000000000))
      (((834810556333609741:ℝ)/100000000000) - ((1:ℝ)/20)*((101628291800212239:ℝ)/5000000000) - (((293001859158566157:ℝ)/100000000000000) + ((303517232516929:ℝ)/16000000000) + ((826609247315420707:ℝ)/10000000000000) + ((29925558548528623:ℝ)/200000000000)))
      (((3822506233817391:ℝ)/2000000000) - ((1:ℝ)/20)*((499555347240601719:ℝ)/1000000000000))
      (((761251965983191817:ℝ)/100000000000) - ((1:ℝ)/20)*((68025958747256129:ℝ)/5000000000) - (((145220887687742467:ℝ)/25000000000000) + ((14906657229642323:ℝ)/1000000000000) + ((29925558548528623:ℝ)/200000000000) + ((361802895941534139:ℝ)/100000000000))) i j :=
  quadForm_nonneg_of_ldl ((2501038711385007719:ℝ)/200000000000) ((44461498261984745676649032031876124759:ℝ)/5002077422770015438000000000000) ((624335478149787630807970140118461923619137934578052053988094719:ℝ)/88922996523969491353298064063752249518000000000000000000) ((1684659889666605465804114052533831288078060372164382526146769481564895459615992843:ℝ)/650349456406028782091635562623397837103268681852137556237598665625000000000) ((-3669461081365820041:ℝ)/25010387113850077190) ((-6123675499332561647:ℝ)/2501038711385007719000) ((588639314482680036:ℝ)/62525967784625192975) ((-3544140613981897860447877427382689996527:ℝ)/44461498261984745676649032031876124759000) ((-106246130839306181073945922168684449309:ℝ)/1111537456549618641916225800796903118975) ((53912190348914426534771980989950135610831596189258590359341640:ℝ)/208111826049929210269323380039487307873045978192684017996031573)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

/-- **Piece 18.** The piece matrix is positive semidefinite on `q ∈ [9/2, 23/5]`. -/
theorem piece_18 {q : ℝ} (h0 : ((9:ℝ)/2) ≤ q) (h1 : q ≤ ((23:ℝ)/5)) (y : Fin 4 → ℝ) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceW q pieceX_18 i j :=
  pieceForm_nonneg (pieceW_symm (sym4_symm _ _ _ _ _ _ _ _ _ _) q) (by norm_num : (0:ℝ) < ((1:ℝ)/20))
    (abs_le.mpr ⟨by linarith, by linarith⟩)
    (piece18_e00 h0 h1) (piece18_e01 h0 h1) (piece18_e02 h0 h1) (piece18_e03 h0 h1) (piece18_e11 h0 h1) (piece18_e12 h0 h1) (piece18_e13 h0 h1) (piece18_e22 h0 h1) (piece18_e23 h0 h1) (piece18_e33 h0 h1)
    piece18_plus piece18_minus y

/-! #### Piece 19 (seam), `q ∈ [23/5, 47/10]` -/

/-- The compensation matrix of piece 19. -/
def pieceX_19 : Fin 4 → Fin 4 → ℝ :=
  sym4 ((11:ℝ)/1000) (0:ℝ) (0:ℝ) (0:ℝ) ((11:ℝ)/1000) (0:ℝ) (0:ℝ) ((11:ℝ)/1000) (0:ℝ) ((11:ℝ)/1000)

theorem piece19_L3 : ((57197222630980538693091656663:ℝ)/50000000000000000000000) ≤ Real.exp ((3:ℝ)*((93:ℝ)/20)) := by
  have h := le_exp_nat_add 13 (f := ((19:ℝ)/20)) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((93:ℝ)/20) = ((13:ℕ):ℝ) + ((19:ℝ)/20) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece19_U3 : Real.exp ((3:ℝ)*((93:ℝ)/20)) ≤ ((114395264360471055649991694439:ℝ)/100000000000000000000000) := by
  have h := exp_nat_add_le 13 (f := ((19:ℝ)/20)) (by norm_num) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((93:ℝ)/20) = ((13:ℕ):ℝ) + ((19:ℝ)/20) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem piece19_L8_at : ((959480256890960283871817658563:ℝ)/100000000000000) ≤ Real.exp ((8:ℝ)*((23:ℝ)/5)) := by
  have h := le_exp_nat_add 36 (f := ((4:ℝ)/5)) (by norm_num)
  rw [show ((8:ℝ):ℝ)*((23:ℝ)/5) = ((36:ℕ):ℝ) + ((4:ℝ)/5) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece19_E8 {q : ℝ} (h0 : ((23:ℝ)/5) ≤ q) : Real.exp (-((8:ℝ))*q) ≤ 1/((959480256890960283871817658563:ℝ)/100000000000000) := by
  have hm : Real.exp (-((8:ℝ))*q) ≤ Real.exp (-((8:ℝ)*((23:ℝ)/5))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece19_L8_at (le_refl _)).2

theorem piece19_L11_at : ((944714707756774130448300333717:ℝ)/100000000) ≤ Real.exp ((11:ℝ)*((23:ℝ)/5)) := by
  have h := le_exp_nat_add 50 (f := ((3:ℝ)/5)) (by norm_num)
  rw [show ((11:ℝ):ℝ)*((23:ℝ)/5) = ((50:ℕ):ℝ) + ((3:ℝ)/5) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece19_E11 {q : ℝ} (h0 : ((23:ℝ)/5) ≤ q) : Real.exp (-((11:ℝ))*q) ≤ 1/((944714707756774130448300333717:ℝ)/100000000) := by
  have hm : Real.exp (-((11:ℝ))*q) ≤ Real.exp (-((11:ℝ)*((23:ℝ)/5))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece19_L11_at (le_refl _)).2

theorem piece19_Lt_at : ((136849623739649786158649343719:ℝ)/100000000) ≤ Real.exp (((529:ℝ)/50)*((23:ℝ)/5)) := by
  have h := le_exp_nat_add 48 (f := ((167:ℝ)/250)) (by norm_num)
  rw [show (((529:ℝ)/50):ℝ)*((23:ℝ)/5) = ((48:ℕ):ℝ) + ((167:ℝ)/250) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece19_Et {q : ℝ} (h0 : ((23:ℝ)/5) ≤ q) : Real.exp (-(((529:ℝ)/50))*q) ≤ 1/((136849623739649786158649343719:ℝ)/100000000) := by
  have hm : Real.exp (-(((529:ℝ)/50))*q) ≤ Real.exp (-(((529:ℝ)/50)*((23:ℝ)/5))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece19_Lt_at (le_refl _)).2

theorem piece19_e00 {q : ℝ} (h0 : ((23:ℝ)/5) ≤ q) (h1 : q ≤ ((47:ℝ)/10)) :
    |pieceW q pieceX_19 0 0 - (((86677222481261519:ℝ)/5000000000) + (q - ((93:ℝ)/20)) * ((357021369659716147:ℝ)/10000000000))| ≤ ((211907933216721309:ℝ)/2500000000000) := by
  set t := q - ((93:ℝ)/20) with htd
  have hq : q = ((93:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece19_L3 piece19_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((93:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_00 q = ∑ e ∈ Finset.range 10, ([((274917127780598733:ℝ)/16000000000), ((28274118006904749:ℝ)/800000000), ((5071568212197:ℝ)/156250), ((4362414906717:ℝ)/250000), ((302307121809:ℝ)/50000), ((3497629653:ℝ)/2500), ((27006084:ℝ)/125), ((536448:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_00; ring
  have h12 : centralNum12_00 q = ∑ e ∈ Finset.range 11, ([((-506144815516468869057:ℝ)/320000000000), ((-11485264277186745813:ℝ)/3200000000), ((-293335936512139971:ℝ)/80000000), ((-4441035995825211:ℝ)/2000000), ((-176527140014547:ℝ)/200000), ((-12029512255299:ℝ)/50000), ((-5692485267:ℝ)/125), ((-147750342:ℝ)/25), ((-2516106:ℝ)/5), (-25384:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_00; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((274917127780598733:ℝ)/16000000000), ((28274118006904749:ℝ)/800000000), ((5071568212197:ℝ)/156250), ((4362414906717:ℝ)/250000), ((302307121809:ℝ)/50000), ((3497629653:ℝ)/2500), ((27006084:ℝ)/125), ((536448:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-506144815516468869057:ℝ)/320000000000), ((-11485264277186745813:ℝ)/3200000000), ((-293335936512139971:ℝ)/80000000), ((-4441035995825211:ℝ)/2000000), ((-176527140014547:ℝ)/200000), ((-12029512255299:ℝ)/50000), ((-5692485267:ℝ)/125), ((-147750342:ℝ)/25), ((-2516106:ℝ)/5), (-25384:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 9 ht
  have m12 := abs_poly_le (fun e => ([((-506144815516468869057:ℝ)/320000000000), ((-11485264277186745813:ℝ)/3200000000), ((-293335936512139971:ℝ)/80000000), ((-4441035995825211:ℝ)/2000000), ((-176527140014547:ℝ)/200000), ((-12029512255299:ℝ)/50000), ((-5692485267:ℝ)/125), ((-147750342:ℝ)/25), ((-2516106:ℝ)/5), (-25384:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 11 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((274917127780598733:ℝ)/16000000000), ((28274118006904749:ℝ)/800000000), ((5071568212197:ℝ)/156250), ((4362414906717:ℝ)/250000), ((302307121809:ℝ)/50000), ((3497629653:ℝ)/2500), ((27006084:ℝ)/125), ((536448:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - (((274917127780598733:ℝ)/16000000000) + ((28274118006904749:ℝ)/800000000)*t)| ≤ ((666916222680131:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 11, ([((-506144815516468869057:ℝ)/320000000000), ((-11485264277186745813:ℝ)/3200000000), ((-293335936512139971:ℝ)/80000000), ((-4441035995825211:ℝ)/2000000), ((-176527140014547:ℝ)/200000), ((-12029512255299:ℝ)/50000), ((-5692485267:ℝ)/125), ((-147750342:ℝ)/25), ((-2516106:ℝ)/5), (-25384:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e) - ((-506144815516468869057:ℝ)/320000000000) - ((-11485264277186745813:ℝ)/3200000000)*t| ≤ ((1511984822322890123:ℝ)/160000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 11, ([((-506144815516468869057:ℝ)/320000000000), ((-11485264277186745813:ℝ)/3200000000), ((-293335936512139971:ℝ)/80000000), ((-4441035995825211:ℝ)/2000000), ((-176527140014547:ℝ)/200000), ((-12029512255299:ℝ)/50000), ((-5692485267:ℝ)/125), ((-147750342:ℝ)/25), ((-2516106:ℝ)/5), (-25384:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((138328883434337983:ℝ)/78125000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((238815075544144533:ℝ)/16000000000) - ((25556759236418949:ℝ)/800000000)*t| ≤ ((622293900370931:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((47:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (600:ℝ), (-7776:ℝ), (16800:ℝ), (-9216:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m13' : |centralNum13_00 q| ≤ ((5403024629274513603:ℝ)/78125000) := by
    rw [centralNum13_00_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((47:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (780:ℝ), (-6156:ℝ), (15288:ℝ), (-14400:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m23' : |centralNum23_00 q| ≤ ((5897334781417780851:ℝ)/62500000) := by
    rw [centralNum23_00_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((114395264360471055649991694439:ℝ)/100000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece19_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece19_E11 h0) m23'
  have c5 := scaled_affine (X := ((11:ℝ)/1000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0))| ≤ ((3696553941859151655731200000:ℝ)/8080833432202580222882085097263231) := by
    rw [abs_neg, tailWeight_0, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((47:ℝ)/10)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((47:ℝ)/10)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece19_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((10465499600:ℝ)/59049)) ≤ ((47:ℝ)/10)^6*(8000*(2*((47:ℝ)/10)-3)^2*(1/((136849623739649786158649343719:ℝ)/100000000))*((10465499600:ℝ)/59049)) := by
          gcongr
      _ ≤ ((3696553941859151655731200000:ℝ)/8080833432202580222882085097263231) := by norm_num
  have c7 := affine_round (α := ((274917127780598733:ℝ)/16000000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((-506144815516468869057:ℝ)/320000000000) + ((238815075544144533:ℝ)/16000000000)*((11:ℝ)/1000) - ((86677222481261519:ℝ)/5000000000)) (β := ((28274118006904749:ℝ)/800000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((-11485264277186745813:ℝ)/3200000000) - 3*((-506144815516468869057:ℝ)/320000000000)) + ((25556759236418949:ℝ)/800000000)*((11:ℝ)/1000) - ((357021369659716147:ℝ)/10000000000)) ht
  have hW : pieceW q pieceX_19 0 0 = centralNum11_00 q + 8*(Real.exp (-(3*((93:ℝ)/20)))*Real.exp (-3*t))*centralNum12_00 q + 18*Real.exp (-8*q)*centralNum13_00 q + 72*Real.exp (-11*q)*centralNum23_00 q + 8*q^7*(2*q-3)^2*((11:ℝ)/1000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0)) := by
    rw [pieceW_00, pieceX_19, sym4_00, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((146187705712213281177775297524649949241523492023651616672353:ℝ)/52344731228445892197564681299552581457320303703335955176456000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((274917127780598733:ℝ)/16000000000) + ((28274118006904749:ℝ)/800000000)*t) + (8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((-506144815516468869057:ℝ)/320000000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((-11485264277186745813:ℝ)/3200000000) - 3*((-506144815516468869057:ℝ)/320000000000))*t) + (((238815075544144533:ℝ)/16000000000) + ((25556759236418949:ℝ)/800000000)*t)*((11:ℝ)/1000) - (((86677222481261519:ℝ)/5000000000) + t * ((357021369659716147:ℝ)/10000000000)) = (((274917127780598733:ℝ)/16000000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((-506144815516468869057:ℝ)/320000000000) + ((238815075544144533:ℝ)/16000000000)*((11:ℝ)/1000) - ((86677222481261519:ℝ)/5000000000)) + t*(((28274118006904749:ℝ)/800000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((-11485264277186745813:ℝ)/3200000000) - 3*((-506144815516468869057:ℝ)/320000000000)) + ((25556759236418949:ℝ)/800000000)*((11:ℝ)/1000) - ((357021369659716147:ℝ)/10000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece19_e01 {q : ℝ} (h0 : ((23:ℝ)/5) ≤ q) (h1 : q ≤ ((47:ℝ)/10)) :
    |pieceW q pieceX_19 0 1 - (((-230020142636681661:ℝ)/100000000000) + (q - ((93:ℝ)/20)) * ((-338093431055072137:ℝ)/100000000000))| ≤ ((7983012606004623:ℝ)/1000000000000) := by
  set t := q - ((93:ℝ)/20) with htd
  have hq : q = ((93:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece19_L3 piece19_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((93:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_01 q = ∑ e ∈ Finset.range 8, ([((-180510261182271:ℝ)/80000000), ((-13586793852429:ℝ)/4000000), ((-438283672659:ℝ)/200000), ((-1570909221:ℝ)/2000), ((-16891497:ℝ)/100), ((-544887:ℝ)/25), ((-7812:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_01; ring
  have h12 : centralNum12_01 q = ∑ e ∈ Finset.range 12, ([((-80210307315400850195883:ℝ)/12800000000000), ((-5294437871493928236003:ℝ)/320000000000), ((-126789354383985657297:ℝ)/6400000000), ((-2272635549773524971:ℝ)/160000000), ((-54215151346097379:ℝ)/8000000), ((-2259498555163143:ℝ)/1000000), ((-53723869008957:ℝ)/100000), ((-45550491531:ℝ)/500), ((-1079750619:ℝ)/100), ((-4259526:ℝ)/5), ((-201348:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_01; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-180510261182271:ℝ)/80000000), ((-13586793852429:ℝ)/4000000), ((-438283672659:ℝ)/200000), ((-1570909221:ℝ)/2000), ((-16891497:ℝ)/100), ((-544887:ℝ)/25), ((-7812:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0) 6 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-80210307315400850195883:ℝ)/12800000000000), ((-5294437871493928236003:ℝ)/320000000000), ((-126789354383985657297:ℝ)/6400000000), ((-2272635549773524971:ℝ)/160000000), ((-54215151346097379:ℝ)/8000000), ((-2259498555163143:ℝ)/1000000), ((-53723869008957:ℝ)/100000), ((-45550491531:ℝ)/500), ((-1079750619:ℝ)/100), ((-4259526:ℝ)/5), ((-201348:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0) 10 ht
  have m12 := abs_poly_le (fun e => ([((-80210307315400850195883:ℝ)/12800000000000), ((-5294437871493928236003:ℝ)/320000000000), ((-126789354383985657297:ℝ)/6400000000), ((-2272635549773524971:ℝ)/160000000), ((-54215151346097379:ℝ)/8000000), ((-2259498555163143:ℝ)/1000000), ((-53723869008957:ℝ)/100000), ((-45550491531:ℝ)/500), ((-1079750619:ℝ)/100), ((-4259526:ℝ)/5), ((-201348:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0) 12 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 8, ([((-180510261182271:ℝ)/80000000), ((-13586793852429:ℝ)/4000000), ((-438283672659:ℝ)/200000), ((-1570909221:ℝ)/2000), ((-16891497:ℝ)/100), ((-544887:ℝ)/25), ((-7812:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0 * t^e) - (((-180510261182271:ℝ)/80000000) + ((-13586793852429:ℝ)/4000000)*t)| ≤ ((111555805773:ℝ)/20000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 12, ([((-80210307315400850195883:ℝ)/12800000000000), ((-5294437871493928236003:ℝ)/320000000000), ((-126789354383985657297:ℝ)/6400000000), ((-2272635549773524971:ℝ)/160000000), ((-54215151346097379:ℝ)/8000000), ((-2259498555163143:ℝ)/1000000), ((-53723869008957:ℝ)/100000), ((-45550491531:ℝ)/500), ((-1079750619:ℝ)/100), ((-4259526:ℝ)/5), ((-201348:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e) - ((-80210307315400850195883:ℝ)/12800000000000) - ((-5294437871493928236003:ℝ)/320000000000)*t| ≤ ((657224425289513112207:ℝ)/12800000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 12, ([((-80210307315400850195883:ℝ)/12800000000000), ((-5294437871493928236003:ℝ)/320000000000), ((-126789354383985657297:ℝ)/6400000000), ((-2272635549773524971:ℝ)/160000000), ((-54215151346097379:ℝ)/8000000), ((-2259498555163143:ℝ)/1000000), ((-53723869008957:ℝ)/100000), ((-45550491531:ℝ)/500), ((-1079750619:ℝ)/100), ((-4259526:ℝ)/5), ((-201348:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((5582056120829969469:ℝ)/781250000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((238815075544144533:ℝ)/16000000000) - ((25556759236418949:ℝ)/800000000)*t| ≤ ((622293900370931:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((47:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-6288:ℝ), (81024:ℝ), (-238720:ℝ), (246784:ℝ), (-98304:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m13' : |centralNum13_01 q| ≤ ((1568384401494906500337:ℝ)/390625000) := by
    rw [centralNum13_01_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((47:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-7368:ℝ), (59208:ℝ), (-155734:ℝ), (205300:ℝ), (-60000:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m23' : |centralNum23_01 q| ≤ ((687978461368009298757:ℝ)/250000000) := by
    rw [centralNum23_01_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((114395264360471055649991694439:ℝ)/100000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece19_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece19_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-180510261182271:ℝ)/80000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((-80210307315400850195883:ℝ)/12800000000000) + ((238815075544144533:ℝ)/16000000000)*(0:ℝ) - ((-230020142636681661:ℝ)/100000000000)) (β := ((-13586793852429:ℝ)/4000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((-5294437871493928236003:ℝ)/320000000000) - 3*((-80210307315400850195883:ℝ)/12800000000000)) + ((25556759236418949:ℝ)/800000000)*(0:ℝ) - ((-338093431055072137:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_19 0 1 = centralNum11_01 q + 8*(Real.exp (-(3*((93:ℝ)/20)))*Real.exp (-3*t))*centralNum12_01 q + 18*Real.exp (-8*q)*centralNum13_01 q + 72*Real.exp (-11*q)*centralNum23_01 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_01, pieceX_19, sym4_01, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((44902767822072879714793574409640886146850927767842055082731:ℝ)/13086182807111473049391170324888145364330075925833988794114000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-180510261182271:ℝ)/80000000) + ((-13586793852429:ℝ)/4000000)*t) + (8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((-80210307315400850195883:ℝ)/12800000000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((-5294437871493928236003:ℝ)/320000000000) - 3*((-80210307315400850195883:ℝ)/12800000000000))*t) + (((238815075544144533:ℝ)/16000000000) + ((25556759236418949:ℝ)/800000000)*t)*(0:ℝ) - (((-230020142636681661:ℝ)/100000000000) + t * ((-338093431055072137:ℝ)/100000000000)) = (((-180510261182271:ℝ)/80000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((-80210307315400850195883:ℝ)/12800000000000) + ((238815075544144533:ℝ)/16000000000)*(0:ℝ) - ((-230020142636681661:ℝ)/100000000000)) + t*(((-13586793852429:ℝ)/4000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((-5294437871493928236003:ℝ)/320000000000) - 3*((-80210307315400850195883:ℝ)/12800000000000)) + ((25556759236418949:ℝ)/800000000)*(0:ℝ) - ((-338093431055072137:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece19_e02 {q : ℝ} (h0 : ((23:ℝ)/5) ≤ q) (h1 : q ≤ ((47:ℝ)/10)) :
    |pieceW q pieceX_19 0 2 - (((-383365635337059121:ℝ)/10000000000000) + (q - ((93:ℝ)/20)) * ((-233404830596569067:ℝ)/5000000000000))| ≤ ((310686493859183173:ℝ)/100000000000000) := by
  set t := q - ((93:ℝ)/20) with htd
  have hq : q = ((93:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece19_L3 piece19_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((93:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_02 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_02; ring
  have h12 : centralNum12_02 q = ∑ e ∈ Finset.range 13, ([((-11226894385518175909775211:ℝ)/2048000000000000), ((-2367562137552238944972249:ℝ)/102400000000000), ((-202001380463390067304299:ℝ)/5120000000000), ((-1954953914807920909887:ℝ)/51200000000), ((-15321993269841553491:ℝ)/640000000), ((-3322231638431677317:ℝ)/320000000), ((-51485269591089243:ℝ)/16000000), ((-577413083006883:ℝ)/800000), ((-1866568848039:ℝ)/16000), ((-10625128713:ℝ)/800), ((-202517199:ℝ)/200), ((-464751:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_02; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-11226894385518175909775211:ℝ)/2048000000000000), ((-2367562137552238944972249:ℝ)/102400000000000), ((-202001380463390067304299:ℝ)/5120000000000), ((-1954953914807920909887:ℝ)/51200000000), ((-15321993269841553491:ℝ)/640000000), ((-3322231638431677317:ℝ)/320000000), ((-51485269591089243:ℝ)/16000000), ((-577413083006883:ℝ)/800000), ((-1866568848039:ℝ)/16000), ((-10625128713:ℝ)/800), ((-202517199:ℝ)/200), ((-464751:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((-11226894385518175909775211:ℝ)/2048000000000000), ((-2367562137552238944972249:ℝ)/102400000000000), ((-202001380463390067304299:ℝ)/5120000000000), ((-1954953914807920909887:ℝ)/51200000000), ((-15321993269841553491:ℝ)/640000000), ((-3322231638431677317:ℝ)/320000000), ((-51485269591089243:ℝ)/16000000), ((-577413083006883:ℝ)/800000), ((-1866568848039:ℝ)/16000), ((-10625128713:ℝ)/800), ((-202517199:ℝ)/200), ((-464751:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((-11226894385518175909775211:ℝ)/2048000000000000), ((-2367562137552238944972249:ℝ)/102400000000000), ((-202001380463390067304299:ℝ)/5120000000000), ((-1954953914807920909887:ℝ)/51200000000), ((-15321993269841553491:ℝ)/640000000), ((-3322231638431677317:ℝ)/320000000), ((-51485269591089243:ℝ)/16000000), ((-577413083006883:ℝ)/800000), ((-1866568848039:ℝ)/16000), ((-10625128713:ℝ)/800), ((-202517199:ℝ)/200), ((-464751:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e) - ((-11226894385518175909775211:ℝ)/2048000000000000) - ((-2367562137552238944972249:ℝ)/102400000000000)*t| ≤ ((53022334625213721834159:ℝ)/512000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((-11226894385518175909775211:ℝ)/2048000000000000), ((-2367562137552238944972249:ℝ)/102400000000000), ((-202001380463390067304299:ℝ)/5120000000000), ((-1954953914807920909887:ℝ)/51200000000), ((-15321993269841553491:ℝ)/640000000), ((-3322231638431677317:ℝ)/320000000), ((-51485269591089243:ℝ)/16000000), ((-577413083006883:ℝ)/800000), ((-1866568848039:ℝ)/16000), ((-10625128713:ℝ)/800), ((-202517199:ℝ)/200), ((-464751:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((842684683933793319219:ℝ)/125000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((238815075544144533:ℝ)/16000000000) - ((25556759236418949:ℝ)/800000000)*t| ≤ ((622293900370931:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((47:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82080:ℝ), (-967680:ℝ), (3257600:ℝ), (-4474880:ℝ), (2908160:ℝ), (-786432:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_02 q| ≤ ((186219512900577969110413:ℝ)/976562500) := by
    rw [centralNum13_02_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((47:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (87660:ℝ), (-702180:ℝ), ((7421435:ℝ)/4), ((-10854125:ℝ)/4), ((2828125:ℝ)/2), (-187500:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_02 q| ≤ ((58611796843859464886249:ℝ)/800000000) := by
    rw [centralNum23_02_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((114395264360471055649991694439:ℝ)/100000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece19_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece19_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((-11226894385518175909775211:ℝ)/2048000000000000) + ((238815075544144533:ℝ)/16000000000)*(0:ℝ) - ((-383365635337059121:ℝ)/10000000000000)) (β := (0:ℝ) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((-2367562137552238944972249:ℝ)/102400000000000) - 3*((-11226894385518175909775211:ℝ)/2048000000000000)) + ((25556759236418949:ℝ)/800000000)*(0:ℝ) - ((-233404830596569067:ℝ)/5000000000000)) ht
  have hW : pieceW q pieceX_19 0 2 = centralNum11_02 q + 8*(Real.exp (-(3*((93:ℝ)/20)))*Real.exp (-3*t))*centralNum12_02 q + 18*Real.exp (-8*q)*centralNum13_02 q + 72*Real.exp (-11*q)*centralNum23_02 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_02, pieceX_19, sym4_02, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((33095682411527035771608159394521270410420736417496096104789:ℝ)/654309140355573652469558516244407268216503796291699439705700000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((-11226894385518175909775211:ℝ)/2048000000000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((-2367562137552238944972249:ℝ)/102400000000000) - 3*((-11226894385518175909775211:ℝ)/2048000000000000))*t) + (((238815075544144533:ℝ)/16000000000) + ((25556759236418949:ℝ)/800000000)*t)*(0:ℝ) - (((-383365635337059121:ℝ)/10000000000000) + t * ((-233404830596569067:ℝ)/5000000000000)) = ((0:ℝ) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((-11226894385518175909775211:ℝ)/2048000000000000) + ((238815075544144533:ℝ)/16000000000)*(0:ℝ) - ((-383365635337059121:ℝ)/10000000000000)) + t*((0:ℝ) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((-2367562137552238944972249:ℝ)/102400000000000) - 3*((-11226894385518175909775211:ℝ)/2048000000000000)) + ((25556759236418949:ℝ)/800000000)*(0:ℝ) - ((-233404830596569067:ℝ)/5000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece19_e03 {q : ℝ} (h0 : ((23:ℝ)/5) ≤ q) (h1 : q ≤ ((47:ℝ)/10)) :
    |pieceW q pieceX_19 0 3 - (((2693059507518667:ℝ)/25000000000) + (q - ((93:ℝ)/20)) * ((-740651526676598731:ℝ)/10000000000000))| ≤ ((521292597849076557:ℝ)/100000000000000) := by
  set t := q - ((93:ℝ)/20) with htd
  have hq : q = ((93:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece19_L3 piece19_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((93:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_03 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_03; ring
  have h12 : centralNum12_03 q = ∑ e ∈ Finset.range 14, ([((8833044723696844544368028853:ℝ)/573440000000000000), ((255324032561156672213084457:ℝ)/7168000000000000), ((10889897288104173941663409:ℝ)/358400000000000), ((218460880342613276226657:ℝ)/35840000000000), ((-7093506225598870373811:ℝ)/716800000000), ((-947623668129952102899:ℝ)/89600000000), ((-3096409202625312783:ℝ)/560000000), ((-209445972663444939:ℝ)/112000000), ((-9834751165964409:ℝ)/22400000), ((-2037853534869:ℝ)/28000), ((-117679433877:ℝ)/14000), ((-904619259:ℝ)/1400), ((-4171581:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_03; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((8833044723696844544368028853:ℝ)/573440000000000000), ((255324032561156672213084457:ℝ)/7168000000000000), ((10889897288104173941663409:ℝ)/358400000000000), ((218460880342613276226657:ℝ)/35840000000000), ((-7093506225598870373811:ℝ)/716800000000), ((-947623668129952102899:ℝ)/89600000000), ((-3096409202625312783:ℝ)/560000000), ((-209445972663444939:ℝ)/112000000), ((-9834751165964409:ℝ)/22400000), ((-2037853534869:ℝ)/28000), ((-117679433877:ℝ)/14000), ((-904619259:ℝ)/1400), ((-4171581:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((8833044723696844544368028853:ℝ)/573440000000000000), ((255324032561156672213084457:ℝ)/7168000000000000), ((10889897288104173941663409:ℝ)/358400000000000), ((218460880342613276226657:ℝ)/35840000000000), ((-7093506225598870373811:ℝ)/716800000000), ((-947623668129952102899:ℝ)/89600000000), ((-3096409202625312783:ℝ)/560000000), ((-209445972663444939:ℝ)/112000000), ((-9834751165964409:ℝ)/22400000), ((-2037853534869:ℝ)/28000), ((-117679433877:ℝ)/14000), ((-904619259:ℝ)/1400), ((-4171581:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((8833044723696844544368028853:ℝ)/573440000000000000), ((255324032561156672213084457:ℝ)/7168000000000000), ((10889897288104173941663409:ℝ)/358400000000000), ((218460880342613276226657:ℝ)/35840000000000), ((-7093506225598870373811:ℝ)/716800000000), ((-947623668129952102899:ℝ)/89600000000), ((-3096409202625312783:ℝ)/560000000), ((-209445972663444939:ℝ)/112000000), ((-9834751165964409:ℝ)/22400000), ((-2037853534869:ℝ)/28000), ((-117679433877:ℝ)/14000), ((-904619259:ℝ)/1400), ((-4171581:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((8833044723696844544368028853:ℝ)/573440000000000000) - ((255324032561156672213084457:ℝ)/7168000000000000)*t| ≤ ((44033924081814047072475237:ℝ)/573440000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((8833044723696844544368028853:ℝ)/573440000000000000), ((255324032561156672213084457:ℝ)/7168000000000000), ((10889897288104173941663409:ℝ)/358400000000000), ((218460880342613276226657:ℝ)/35840000000000), ((-7093506225598870373811:ℝ)/716800000000), ((-947623668129952102899:ℝ)/89600000000), ((-3096409202625312783:ℝ)/560000000), ((-209445972663444939:ℝ)/112000000), ((-9834751165964409:ℝ)/22400000), ((-2037853534869:ℝ)/28000), ((-117679433877:ℝ)/14000), ((-904619259:ℝ)/1400), ((-4171581:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((4949187389011642640146420959:ℝ)/286720000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((238815075544144533:ℝ)/16000000000) - ((25556759236418949:ℝ)/800000000)*t| ≤ ((622293900370931:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((47:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-812160:ℝ), (8985600:ℝ), (-32225280:ℝ), (52019200:ℝ), ((-305233920:ℝ)/7), ((135528448:ℝ)/7), ((-25165824:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_03 q| ≤ ((47875007483001918934583209:ℝ)/8544921875) := by
    rw [centralNum13_03_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((47:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-833220:ℝ), (6469740:ℝ), ((-68603955:ℝ)/4), ((104396875:ℝ)/4), ((-1001334375:ℝ)/56), ((125828125:ℝ)/28), ((-2343750:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_03 q| ≤ ((29234173928435196187046701:ℝ)/22400000000) := by
    rw [centralNum23_03_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((114395264360471055649991694439:ℝ)/100000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece19_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece19_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((8833044723696844544368028853:ℝ)/573440000000000000) + ((238815075544144533:ℝ)/16000000000)*(0:ℝ) - ((2693059507518667:ℝ)/25000000000)) (β := (0:ℝ) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((255324032561156672213084457:ℝ)/7168000000000000) - 3*((8833044723696844544368028853:ℝ)/573440000000000000)) + ((25556759236418949:ℝ)/800000000)*(0:ℝ) - ((-740651526676598731:ℝ)/10000000000000)) ht
  have hW : pieceW q pieceX_19 0 3 = centralNum11_03 q + 8*(Real.exp (-(3*((93:ℝ)/20)))*Real.exp (-3*t))*centralNum12_03 q + 18*Real.exp (-8*q)*centralNum13_03 q + 72*Real.exp (-11*q)*centralNum23_03 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_03, pieceX_19, sym4_03, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((2066647577139766907704510576363615491822726795338053536593331:ℝ)/9160327964978031134573819227421701755031053148083792155879800000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((8833044723696844544368028853:ℝ)/573440000000000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((255324032561156672213084457:ℝ)/7168000000000000) - 3*((8833044723696844544368028853:ℝ)/573440000000000000))*t) + (((238815075544144533:ℝ)/16000000000) + ((25556759236418949:ℝ)/800000000)*t)*(0:ℝ) - (((2693059507518667:ℝ)/25000000000) + t * ((-740651526676598731:ℝ)/10000000000000)) = ((0:ℝ) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((8833044723696844544368028853:ℝ)/573440000000000000) + ((238815075544144533:ℝ)/16000000000)*(0:ℝ) - ((2693059507518667:ℝ)/25000000000)) + t*((0:ℝ) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((255324032561156672213084457:ℝ)/7168000000000000) - 3*((8833044723696844544368028853:ℝ)/573440000000000000)) + ((25556759236418949:ℝ)/800000000)*(0:ℝ) - ((-740651526676598731:ℝ)/10000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece19_e11 {q : ℝ} (h0 : ((23:ℝ)/5) ≤ q) (h1 : q ≤ ((47:ℝ)/10)) :
    |pieceW q pieceX_19 1 1 - (((6266902916530419:ℝ)/500000000) + (q - ((93:ℝ)/20)) * ((61624487246809589:ℝ)/2500000000))| ≤ ((578689799666220977:ℝ)/10000000000000) := by
  set t := q - ((93:ℝ)/20) with htd
  have hq : q = ((93:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece19_L3 piece19_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((93:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_11 q = ∑ e ∈ Finset.range 10, ([((49492808063298153:ℝ)/4000000000), ((9749870746112403:ℝ)/400000000), ((108169891555221:ℝ)/5000000), ((2837247859593:ℝ)/250000), ((12106299366:ℝ)/3125), ((1113907221:ℝ)/1250), ((17238396:ℝ)/125), ((345552:ℝ)/25), ((4064:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_11; ring
  have h12 : centralNum12_11 q = ∑ e ∈ Finset.range 13, ([((-262214766062427808767177:ℝ)/512000000000000), ((-318592590583271903057763:ℝ)/25600000000000), ((-38520543068545924018233:ℝ)/1280000000000), ((-440660714399123088789:ℝ)/12800000000), ((-3823611971574087657:ℝ)/160000000), ((-889297902789794919:ℝ)/80000000), ((-14521137139816041:ℝ)/4000000), ((-169687670581761:ℝ)/200000), ((-567266095133:ℝ)/4000), ((-9964460953:ℝ)/600), ((-64861893:ℝ)/50), ((-304074:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_11; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((49492808063298153:ℝ)/4000000000), ((9749870746112403:ℝ)/400000000), ((108169891555221:ℝ)/5000000), ((2837247859593:ℝ)/250000), ((12106299366:ℝ)/3125), ((1113907221:ℝ)/1250), ((17238396:ℝ)/125), ((345552:ℝ)/25), ((4064:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-262214766062427808767177:ℝ)/512000000000000), ((-318592590583271903057763:ℝ)/25600000000000), ((-38520543068545924018233:ℝ)/1280000000000), ((-440660714399123088789:ℝ)/12800000000), ((-3823611971574087657:ℝ)/160000000), ((-889297902789794919:ℝ)/80000000), ((-14521137139816041:ℝ)/4000000), ((-169687670581761:ℝ)/200000), ((-567266095133:ℝ)/4000), ((-9964460953:ℝ)/600), ((-64861893:ℝ)/50), ((-304074:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((-262214766062427808767177:ℝ)/512000000000000), ((-318592590583271903057763:ℝ)/25600000000000), ((-38520543068545924018233:ℝ)/1280000000000), ((-440660714399123088789:ℝ)/12800000000), ((-3823611971574087657:ℝ)/160000000), ((-889297902789794919:ℝ)/80000000), ((-14521137139816041:ℝ)/4000000), ((-169687670581761:ℝ)/200000), ((-567266095133:ℝ)/4000), ((-9964460953:ℝ)/600), ((-64861893:ℝ)/50), ((-304074:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((49492808063298153:ℝ)/4000000000), ((9749870746112403:ℝ)/400000000), ((108169891555221:ℝ)/5000000), ((2837247859593:ℝ)/250000), ((12106299366:ℝ)/3125), ((1113907221:ℝ)/1250), ((17238396:ℝ)/125), ((345552:ℝ)/25), ((4064:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((49492808063298153:ℝ)/4000000000) + ((9749870746112403:ℝ)/400000000)*t)| ≤ ((1332673510765777:ℝ)/24000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((-262214766062427808767177:ℝ)/512000000000000), ((-318592590583271903057763:ℝ)/25600000000000), ((-38520543068545924018233:ℝ)/1280000000000), ((-440660714399123088789:ℝ)/12800000000), ((-3823611971574087657:ℝ)/160000000), ((-889297902789794919:ℝ)/80000000), ((-14521137139816041:ℝ)/4000000), ((-169687670581761:ℝ)/200000), ((-567266095133:ℝ)/4000), ((-9964460953:ℝ)/600), ((-64861893:ℝ)/50), ((-304074:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e) - ((-262214766062427808767177:ℝ)/512000000000000) - ((-318592590583271903057763:ℝ)/25600000000000)*t| ≤ ((30601595145210918394079:ℝ)/384000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((-262214766062427808767177:ℝ)/512000000000000), ((-318592590583271903057763:ℝ)/25600000000000), ((-38520543068545924018233:ℝ)/1280000000000), ((-440660714399123088789:ℝ)/12800000000), ((-3823611971574087657:ℝ)/160000000), ((-889297902789794919:ℝ)/80000000), ((-14521137139816041:ℝ)/4000000), ((-169687670581761:ℝ)/200000), ((-567266095133:ℝ)/4000), ((-9964460953:ℝ)/600), ((-64861893:ℝ)/50), ((-304074:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((113820095856808032779:ℝ)/93750000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((238815075544144533:ℝ)/16000000000) - ((25556759236418949:ℝ)/800000000)*t| ≤ ((622293900370931:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((47:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-3444:ℝ), (162624:ℝ), (-1531216:ℝ), (4800960:ℝ), (-6350848:ℝ), ((12025856:ℝ)/3), (-1048576:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_11 q| ≤ ((761969896385632122690697:ℝ)/2929687500) := by
    rw [centralNum13_11_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((47:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-4074:ℝ), (159906:ℝ), (-1104799:ℝ), (2801499:ℝ), (-3931375:ℝ), ((5896250:ℝ)/3), (-250000:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_11 q| ≤ ((305163738740352987418369:ℝ)/3000000000) := by
    rw [centralNum23_11_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((114395264360471055649991694439:ℝ)/100000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece19_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece19_E11 h0) m23'
  have c5 := scaled_affine (X := ((11:ℝ)/1000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1))| ≤ ((1700631799408091033619660800000:ℝ)/72727500889823222005938765875369079) := by
    rw [abs_neg, tailWeight_1, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((47:ℝ)/10)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((47:ℝ)/10)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece19_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((4814744136400:ℝ)/531441)) ≤ ((47:ℝ)/10)^6*(8000*(2*((47:ℝ)/10)-3)^2*(1/((136849623739649786158649343719:ℝ)/100000000))*((4814744136400:ℝ)/531441)) := by
          gcongr
      _ ≤ ((1700631799408091033619660800000:ℝ)/72727500889823222005938765875369079) := by norm_num
  have c7 := affine_round (α := ((49492808063298153:ℝ)/4000000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((-262214766062427808767177:ℝ)/512000000000000) + ((238815075544144533:ℝ)/16000000000)*((11:ℝ)/1000) - ((6266902916530419:ℝ)/500000000)) (β := ((9749870746112403:ℝ)/400000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((-318592590583271903057763:ℝ)/25600000000000) - 3*((-262214766062427808767177:ℝ)/512000000000000)) + ((25556759236418949:ℝ)/800000000)*((11:ℝ)/1000) - ((61624487246809589:ℝ)/2500000000)) ht
  have hW : pieceW q pieceX_19 1 1 = centralNum11_11 q + 8*(Real.exp (-(3*((93:ℝ)/20)))*Real.exp (-3*t))*centralNum12_11 q + 18*Real.exp (-8*q)*centralNum13_11 q + 72*Real.exp (-11*q)*centralNum23_11 q + 8*q^7*(2*q-3)^2*((11:ℝ)/1000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1)) := by
    rw [pieceW_11, pieceX_19, sym4_11, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((1421041076061891815526191853257908565521614074634499753848073:ℝ)/52344731228445892197564681299552581457320303703335955176456000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((49492808063298153:ℝ)/4000000000) + ((9749870746112403:ℝ)/400000000)*t) + (8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((-262214766062427808767177:ℝ)/512000000000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((-318592590583271903057763:ℝ)/25600000000000) - 3*((-262214766062427808767177:ℝ)/512000000000000))*t) + (((238815075544144533:ℝ)/16000000000) + ((25556759236418949:ℝ)/800000000)*t)*((11:ℝ)/1000) - (((6266902916530419:ℝ)/500000000) + t * ((61624487246809589:ℝ)/2500000000)) = (((49492808063298153:ℝ)/4000000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((-262214766062427808767177:ℝ)/512000000000000) + ((238815075544144533:ℝ)/16000000000)*((11:ℝ)/1000) - ((6266902916530419:ℝ)/500000000)) + t*(((9749870746112403:ℝ)/400000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((-318592590583271903057763:ℝ)/25600000000000) - 3*((-262214766062427808767177:ℝ)/512000000000000)) + ((25556759236418949:ℝ)/800000000)*((11:ℝ)/1000) - ((61624487246809589:ℝ)/2500000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece19_e12 {q : ℝ} (h0 : ((23:ℝ)/5) ≤ q) (h1 : q ≤ ((47:ℝ)/10)) :
    |pieceW q pieceX_19 1 2 - (((-921879064183362799:ℝ)/1000000000000) + (q - ((93:ℝ)/20)) * ((-156438009206838183:ℝ)/100000000000))| ≤ ((181975624548442573:ℝ)/10000000000000) := by
  set t := q - ((93:ℝ)/20) with htd
  have hq : q = ((93:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece19_L3 piece19_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((93:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_12 q = ∑ e ∈ Finset.range 9, ([((-774447249588453:ℝ)/640000000), ((-12167589579057:ℝ)/8000000), ((-260995346289:ℝ)/400000), ((-774595791:ℝ)/20000), ((25090749:ℝ)/400), ((1238481:ℝ)/50), ((21582:ℝ)/5), (376:ℝ), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_12; ring
  have h12 : centralNum12_12 q = ∑ e ∈ Finset.range 14, ([((3375923005898034566314157991:ℝ)/81920000000000000), ((120237652766847604680031059:ℝ)/1024000000000000), ((7182058188110584652638443:ℝ)/51200000000000), ((451540568820102566557419:ℝ)/5120000000000), ((2708175079078211565423:ℝ)/102400000000), ((-26845805802188100753:ℝ)/12800000000), ((-449144936132285421:ℝ)/80000000), ((-42746306147602553:ℝ)/16000000), ((-7128770087998009:ℝ)/9600000), ((-547354323983:ℝ)/4000), ((-34068532119:ℝ)/2000), ((-277300233:ℝ)/200), ((-1338687:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_12; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-774447249588453:ℝ)/640000000), ((-12167589579057:ℝ)/8000000), ((-260995346289:ℝ)/400000), ((-774595791:ℝ)/20000), ((25090749:ℝ)/400), ((1238481:ℝ)/50), ((21582:ℝ)/5), (376:ℝ), ((40:ℝ)/3)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((3375923005898034566314157991:ℝ)/81920000000000000), ((120237652766847604680031059:ℝ)/1024000000000000), ((7182058188110584652638443:ℝ)/51200000000000), ((451540568820102566557419:ℝ)/5120000000000), ((2708175079078211565423:ℝ)/102400000000), ((-26845805802188100753:ℝ)/12800000000), ((-449144936132285421:ℝ)/80000000), ((-42746306147602553:ℝ)/16000000), ((-7128770087998009:ℝ)/9600000), ((-547354323983:ℝ)/4000), ((-34068532119:ℝ)/2000), ((-277300233:ℝ)/200), ((-1338687:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((3375923005898034566314157991:ℝ)/81920000000000000), ((120237652766847604680031059:ℝ)/1024000000000000), ((7182058188110584652638443:ℝ)/51200000000000), ((451540568820102566557419:ℝ)/5120000000000), ((2708175079078211565423:ℝ)/102400000000), ((-26845805802188100753:ℝ)/12800000000), ((-449144936132285421:ℝ)/80000000), ((-42746306147602553:ℝ)/16000000), ((-7128770087998009:ℝ)/9600000), ((-547354323983:ℝ)/4000), ((-34068532119:ℝ)/2000), ((-277300233:ℝ)/200), ((-1338687:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((-774447249588453:ℝ)/640000000), ((-12167589579057:ℝ)/8000000), ((-260995346289:ℝ)/400000), ((-774595791:ℝ)/20000), ((25090749:ℝ)/400), ((1238481:ℝ)/50), ((21582:ℝ)/5), (376:ℝ), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((-774447249588453:ℝ)/640000000) + ((-12167589579057:ℝ)/8000000)*t)| ≤ ((3142007019259:ℝ)/1920000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((3375923005898034566314157991:ℝ)/81920000000000000), ((120237652766847604680031059:ℝ)/1024000000000000), ((7182058188110584652638443:ℝ)/51200000000000), ((451540568820102566557419:ℝ)/5120000000000), ((2708175079078211565423:ℝ)/102400000000), ((-26845805802188100753:ℝ)/12800000000), ((-449144936132285421:ℝ)/80000000), ((-42746306147602553:ℝ)/16000000), ((-7128770087998009:ℝ)/9600000), ((-547354323983:ℝ)/4000), ((-34068532119:ℝ)/2000), ((-277300233:ℝ)/200), ((-1338687:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e) - ((3375923005898034566314157991:ℝ)/81920000000000000) - ((120237652766847604680031059:ℝ)/1024000000000000)*t| ≤ ((88934747450376088751105767:ℝ)/245760000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((3375923005898034566314157991:ℝ)/81920000000000000), ((120237652766847604680031059:ℝ)/1024000000000000), ((7182058188110584652638443:ℝ)/51200000000000), ((451540568820102566557419:ℝ)/5120000000000), ((2708175079078211565423:ℝ)/102400000000), ((-26845805802188100753:ℝ)/12800000000), ((-449144936132285421:ℝ)/80000000), ((-42746306147602553:ℝ)/16000000), ((-7128770087998009:ℝ)/9600000), ((-547354323983:ℝ)/4000), ((-34068532119:ℝ)/2000), ((-277300233:ℝ)/200), ((-1338687:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((182180556224166422560218007:ℝ)/3840000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((238815075544144533:ℝ)/16000000000) - ((25556759236418949:ℝ)/800000000)*t| ≤ ((622293900370931:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((47:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (122790:ℝ), (-3586680:ℝ), (28529720:ℝ), (-90761600:ℝ), (137804800:ℝ), ((-332136448:ℝ)/3), ((141819904:ℝ)/3), (-8388608:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_12 q| ≤ ((133243611975086719712243729:ℝ)/9765625000) := by
    rw [centralNum13_12_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((47:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (132555:ℝ), (-3252375:ℝ), ((39743695:ℝ)/2), ((-197111615:ℝ)/4), ((281947375:ℝ)/4), ((-1100234375:ℝ)/24), ((131828125:ℝ)/12), (-781250:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_12 q| ≤ ((10455034048650963525895919:ℝ)/3200000000) := by
    rw [centralNum23_12_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((114395264360471055649991694439:ℝ)/100000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece19_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece19_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-774447249588453:ℝ)/640000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((3375923005898034566314157991:ℝ)/81920000000000000) + ((238815075544144533:ℝ)/16000000000)*(0:ℝ) - ((-921879064183362799:ℝ)/1000000000000)) (β := ((-12167589579057:ℝ)/8000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((120237652766847604680031059:ℝ)/1024000000000000) - 3*((3375923005898034566314157991:ℝ)/81920000000000000)) + ((25556759236418949:ℝ)/800000000)*(0:ℝ) - ((-156438009206838183:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_19 1 2 = centralNum11_12 q + 8*(Real.exp (-(3*((93:ℝ)/20)))*Real.exp (-3*t))*centralNum12_12 q + 18*Real.exp (-8*q)*centralNum13_12 q + 72*Real.exp (-11*q)*centralNum23_12 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_12, pieceX_19, sym4_12, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((727777636361555070073594301051946792423416415286663591951:ℝ)/1635772850888934131173896290611018170541259490729248599264250000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-774447249588453:ℝ)/640000000) + ((-12167589579057:ℝ)/8000000)*t) + (8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((3375923005898034566314157991:ℝ)/81920000000000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((120237652766847604680031059:ℝ)/1024000000000000) - 3*((3375923005898034566314157991:ℝ)/81920000000000000))*t) + (((238815075544144533:ℝ)/16000000000) + ((25556759236418949:ℝ)/800000000)*t)*(0:ℝ) - (((-921879064183362799:ℝ)/1000000000000) + t * ((-156438009206838183:ℝ)/100000000000)) = (((-774447249588453:ℝ)/640000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((3375923005898034566314157991:ℝ)/81920000000000000) + ((238815075544144533:ℝ)/16000000000)*(0:ℝ) - ((-921879064183362799:ℝ)/1000000000000)) + t*(((-12167589579057:ℝ)/8000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((120237652766847604680031059:ℝ)/1024000000000000) - 3*((3375923005898034566314157991:ℝ)/81920000000000000)) + ((25556759236418949:ℝ)/800000000)*(0:ℝ) - ((-156438009206838183:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece19_e13 {q : ℝ} (h0 : ((23:ℝ)/5) ≤ q) (h1 : q ≤ ((47:ℝ)/10)) :
    |pieceW q pieceX_19 1 3 - (((-110938482953987413:ℝ)/125000000000) + (q - ((93:ℝ)/20)) * ((-185137014440638157:ℝ)/1000000000000))| ≤ ((121017417146296129:ℝ)/10000000000000) := by
  set t := q - ((93:ℝ)/20) with htd
  have hq : q = ((93:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece19_L3 piece19_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((93:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_13 q = ∑ e ∈ Finset.range 7, ([((-1940970550347:ℝ)/3200000), ((-62611953237:ℝ)/80000), ((-673246809:ℝ)/1600), ((-2413071:ℝ)/20), ((-77841:ℝ)/4), (-1674:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_13; ring
  have h12 : centralNum12_13 q = ∑ e ∈ Finset.range 15, ([((-921511108686679156139018174793:ℝ)/22937600000000000000), ((-40236745425752074120674756309:ℝ)/1146880000000000000), ((555438406645258776864897021:ℝ)/7168000000000000), ((245212618578506870949145737:ℝ)/1433600000000000), ((21876069698389789867686897:ℝ)/143360000000000), ((80941095166293924151239:ℝ)/1024000000000), ((4518547823705920323087:ℝ)/179200000000), ((19805062236461520363:ℝ)/4480000000), ((33034626768650361:ℝ)/896000000), ((-8977248812285667:ℝ)/44800000), ((-31934580436233:ℝ)/560000), ((-482967166383:ℝ)/56000), ((-628420599:ℝ)/800), ((-11431449:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_13; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-1940970550347:ℝ)/3200000), ((-62611953237:ℝ)/80000), ((-673246809:ℝ)/1600), ((-2413071:ℝ)/20), ((-77841:ℝ)/4), (-1674:ℝ), (-60:ℝ)] : List ℝ).getD e 0) 5 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-921511108686679156139018174793:ℝ)/22937600000000000000), ((-40236745425752074120674756309:ℝ)/1146880000000000000), ((555438406645258776864897021:ℝ)/7168000000000000), ((245212618578506870949145737:ℝ)/1433600000000000), ((21876069698389789867686897:ℝ)/143360000000000), ((80941095166293924151239:ℝ)/1024000000000), ((4518547823705920323087:ℝ)/179200000000), ((19805062236461520363:ℝ)/4480000000), ((33034626768650361:ℝ)/896000000), ((-8977248812285667:ℝ)/44800000), ((-31934580436233:ℝ)/560000), ((-482967166383:ℝ)/56000), ((-628420599:ℝ)/800), ((-11431449:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-921511108686679156139018174793:ℝ)/22937600000000000000), ((-40236745425752074120674756309:ℝ)/1146880000000000000), ((555438406645258776864897021:ℝ)/7168000000000000), ((245212618578506870949145737:ℝ)/1433600000000000), ((21876069698389789867686897:ℝ)/143360000000000), ((80941095166293924151239:ℝ)/1024000000000), ((4518547823705920323087:ℝ)/179200000000), ((19805062236461520363:ℝ)/4480000000), ((33034626768650361:ℝ)/896000000), ((-8977248812285667:ℝ)/44800000), ((-31934580436233:ℝ)/560000), ((-482967166383:ℝ)/56000), ((-628420599:ℝ)/800), ((-11431449:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 7, ([((-1940970550347:ℝ)/3200000), ((-62611953237:ℝ)/80000), ((-673246809:ℝ)/1600), ((-2413071:ℝ)/20), ((-77841:ℝ)/4), (-1674:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e) - (((-1940970550347:ℝ)/3200000) + ((-62611953237:ℝ)/80000)*t)| ≤ ((3414886347:ℝ)/3200000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-921511108686679156139018174793:ℝ)/22937600000000000000), ((-40236745425752074120674756309:ℝ)/1146880000000000000), ((555438406645258776864897021:ℝ)/7168000000000000), ((245212618578506870949145737:ℝ)/1433600000000000), ((21876069698389789867686897:ℝ)/143360000000000), ((80941095166293924151239:ℝ)/1024000000000), ((4518547823705920323087:ℝ)/179200000000), ((19805062236461520363:ℝ)/4480000000), ((33034626768650361:ℝ)/896000000), ((-8977248812285667:ℝ)/44800000), ((-31934580436233:ℝ)/560000), ((-482967166383:ℝ)/56000), ((-628420599:ℝ)/800), ((-11431449:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((-921511108686679156139018174793:ℝ)/22937600000000000000) - ((-40236745425752074120674756309:ℝ)/1146880000000000000)*t| ≤ ((154887008251302335815260729:ℝ)/716800000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-921511108686679156139018174793:ℝ)/22937600000000000000), ((-40236745425752074120674756309:ℝ)/1146880000000000000), ((555438406645258776864897021:ℝ)/7168000000000000), ((245212618578506870949145737:ℝ)/1433600000000000), ((21876069698389789867686897:ℝ)/143360000000000), ((80941095166293924151239:ℝ)/1024000000000), ((4518547823705920323087:ℝ)/179200000000), ((19805062236461520363:ℝ)/4480000000), ((33034626768650361:ℝ)/896000000), ((-8977248812285667:ℝ)/44800000), ((-31934580436233:ℝ)/560000), ((-482967166383:ℝ)/56000), ((-628420599:ℝ)/800), ((-11431449:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((96670423837647290500578127443:ℝ)/2293760000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((238815075544144533:ℝ)/16000000000) - ((25556759236418949:ℝ)/800000000)*t| ≤ ((622293900370931:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((47:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2325540:ℝ), (52589280:ℝ), (-375655200:ℝ), (1192958720:ℝ), (-1965096960:ℝ), ((12857851904:ℝ)/7), ((-21171273728:ℝ)/21), ((914358272:ℝ)/3), ((-268435456:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_13 q| ≤ ((300222223142496282986428414801:ℝ)/683593750000) := by
    rw [centralNum13_13_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((47:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2399070:ℝ), (45666930:ℝ), (-251781675:ℝ), ((2452738385:ℝ)/4), ((-14104310625:ℝ)/16), ((74345740625:ℝ)/112), ((-74899765625:ℝ)/336), ((5161328125:ℝ)/168), ((-9765625:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_13 q| ≤ ((6097685298103057646996607283:ℝ)/89600000000) := by
    rw [centralNum23_13_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((114395264360471055649991694439:ℝ)/100000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece19_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece19_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-1940970550347:ℝ)/3200000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((-921511108686679156139018174793:ℝ)/22937600000000000000) + ((238815075544144533:ℝ)/16000000000)*(0:ℝ) - ((-110938482953987413:ℝ)/125000000000)) (β := ((-62611953237:ℝ)/80000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((-40236745425752074120674756309:ℝ)/1146880000000000000) - 3*((-921511108686679156139018174793:ℝ)/22937600000000000000)) + ((25556759236418949:ℝ)/800000000)*(0:ℝ) - ((-185137014440638157:ℝ)/1000000000000)) ht
  have hW : pieceW q pieceX_19 1 3 = centralNum11_13 q + 8*(Real.exp (-(3*((93:ℝ)/20)))*Real.exp (-3*t))*centralNum12_13 q + 18*Real.exp (-8*q)*centralNum13_13 q + 72*Real.exp (-11*q)*centralNum23_13 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_13, pieceX_19, sym4_13, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((231553980794422577566328753087834102646329006421345939911723:ℝ)/916032796497803113457381922742170175503105314808379215587980000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-1940970550347:ℝ)/3200000) + ((-62611953237:ℝ)/80000)*t) + (8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((-921511108686679156139018174793:ℝ)/22937600000000000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((-40236745425752074120674756309:ℝ)/1146880000000000000) - 3*((-921511108686679156139018174793:ℝ)/22937600000000000000))*t) + (((238815075544144533:ℝ)/16000000000) + ((25556759236418949:ℝ)/800000000)*t)*(0:ℝ) - (((-110938482953987413:ℝ)/125000000000) + t * ((-185137014440638157:ℝ)/1000000000000)) = (((-1940970550347:ℝ)/3200000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((-921511108686679156139018174793:ℝ)/22937600000000000000) + ((238815075544144533:ℝ)/16000000000)*(0:ℝ) - ((-110938482953987413:ℝ)/125000000000)) + t*(((-62611953237:ℝ)/80000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((-40236745425752074120674756309:ℝ)/1146880000000000000) - 3*((-921511108686679156139018174793:ℝ)/22937600000000000000)) + ((25556759236418949:ℝ)/800000000)*(0:ℝ) - ((-185137014440638157:ℝ)/1000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece19_e22 {q : ℝ} (h0 : ((23:ℝ)/5) ≤ q) (h1 : q ≤ ((47:ℝ)/10)) :
    |pieceW q pieceX_19 2 2 - (((105760774801005919:ℝ)/10000000000) + (q - ((93:ℝ)/20)) * ((243365152424811631:ℝ)/10000000000))| ≤ ((416523309221892699:ℝ)/5000000000000) := by
  set t := q - ((93:ℝ)/20) with htd
  have hq : q = ((93:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece19_L3 piece19_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((93:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_22 q = ∑ e ∈ Finset.range 10, ([((71316246105356661:ℝ)/6400000000), ((7346639960081883:ℝ)/320000000), ((84407030098461:ℝ)/4000000), ((2280372826653:ℝ)/200000), ((80055522603:ℝ)/20000), ((948411801:ℝ)/1000), ((3793289:ℝ)/25), ((236924:ℝ)/15), ((2908:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_22; ring
  have h12 : centralNum12_22 q = ∑ e ∈ Finset.range 15, ([((-1370581869709386219151679364153:ℝ)/13107200000000000000), ((-109357910729844436373271859269:ℝ)/655360000000000000), ((-6292441298862558106230069:ℝ)/4096000000000000), ((165531633457421137216469697:ℝ)/819200000000000), ((18734672807789395992892497:ℝ)/81920000000000), ((544332731650254918404433:ℝ)/4096000000000), ((4785055295427090605567:ℝ)/102400000000), ((73634316870390869929:ℝ)/7680000000), ((1001151801782434523:ℝ)/1536000000), ((-17976779264489401:ℝ)/76800000), ((-27039579926493:ℝ)/320000), ((-441438076503:ℝ)/32000), ((-4191299073:ℝ)/3200), ((-11198169:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_22; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((71316246105356661:ℝ)/6400000000), ((7346639960081883:ℝ)/320000000), ((84407030098461:ℝ)/4000000), ((2280372826653:ℝ)/200000), ((80055522603:ℝ)/20000), ((948411801:ℝ)/1000), ((3793289:ℝ)/25), ((236924:ℝ)/15), ((2908:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-1370581869709386219151679364153:ℝ)/13107200000000000000), ((-109357910729844436373271859269:ℝ)/655360000000000000), ((-6292441298862558106230069:ℝ)/4096000000000000), ((165531633457421137216469697:ℝ)/819200000000000), ((18734672807789395992892497:ℝ)/81920000000000), ((544332731650254918404433:ℝ)/4096000000000), ((4785055295427090605567:ℝ)/102400000000), ((73634316870390869929:ℝ)/7680000000), ((1001151801782434523:ℝ)/1536000000), ((-17976779264489401:ℝ)/76800000), ((-27039579926493:ℝ)/320000), ((-441438076503:ℝ)/32000), ((-4191299073:ℝ)/3200), ((-11198169:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-1370581869709386219151679364153:ℝ)/13107200000000000000), ((-109357910729844436373271859269:ℝ)/655360000000000000), ((-6292441298862558106230069:ℝ)/4096000000000000), ((165531633457421137216469697:ℝ)/819200000000000), ((18734672807789395992892497:ℝ)/81920000000000), ((544332731650254918404433:ℝ)/4096000000000), ((4785055295427090605567:ℝ)/102400000000), ((73634316870390869929:ℝ)/7680000000), ((1001151801782434523:ℝ)/1536000000), ((-17976779264489401:ℝ)/76800000), ((-27039579926493:ℝ)/320000), ((-441438076503:ℝ)/32000), ((-4191299073:ℝ)/3200), ((-11198169:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((71316246105356661:ℝ)/6400000000), ((7346639960081883:ℝ)/320000000), ((84407030098461:ℝ)/4000000), ((2280372826653:ℝ)/200000), ((80055522603:ℝ)/20000), ((948411801:ℝ)/1000), ((3793289:ℝ)/25), ((236924:ℝ)/15), ((2908:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((71316246105356661:ℝ)/6400000000) + ((7346639960081883:ℝ)/320000000)*t)| ≤ ((65045931529057:ℝ)/1200000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-1370581869709386219151679364153:ℝ)/13107200000000000000), ((-109357910729844436373271859269:ℝ)/655360000000000000), ((-6292441298862558106230069:ℝ)/4096000000000000), ((165531633457421137216469697:ℝ)/819200000000000), ((18734672807789395992892497:ℝ)/81920000000000), ((544332731650254918404433:ℝ)/4096000000000), ((4785055295427090605567:ℝ)/102400000000), ((73634316870390869929:ℝ)/7680000000), ((1001151801782434523:ℝ)/1536000000), ((-17976779264489401:ℝ)/76800000), ((-27039579926493:ℝ)/320000), ((-441438076503:ℝ)/32000), ((-4191299073:ℝ)/3200), ((-11198169:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e) - ((-1370581869709386219151679364153:ℝ)/13107200000000000000) - ((-109357910729844436373271859269:ℝ)/655360000000000000)*t| ≤ ((75129650901502683245710981:ℝ)/2457600000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-1370581869709386219151679364153:ℝ)/13107200000000000000), ((-109357910729844436373271859269:ℝ)/655360000000000000), ((-6292441298862558106230069:ℝ)/4096000000000000), ((165531633457421137216469697:ℝ)/819200000000000), ((18734672807789395992892497:ℝ)/81920000000000), ((544332731650254918404433:ℝ)/4096000000000), ((4785055295427090605567:ℝ)/102400000000), ((73634316870390869929:ℝ)/7680000000), ((1001151801782434523:ℝ)/1536000000), ((-17976779264489401:ℝ)/76800000), ((-27039579926493:ℝ)/320000), ((-441438076503:ℝ)/32000), ((-4191299073:ℝ)/3200), ((-11198169:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e)| ≤ ((2220510707866058004753392522981:ℝ)/19660800000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((238815075544144533:ℝ)/16000000000) - ((25556759236418949:ℝ)/800000000)*t| ≤ ((622293900370931:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((47:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82125:ℝ), (-6663750:ℝ), (115666200:ℝ), (-750437000:ℝ), (2277262000:ℝ), (-3656824320:ℝ), (3359621120:ℝ), (-1817706496:ℝ), ((1625292800:ℝ)/3), (-67108864:ℝ)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_22 q| ≤ ((229783798263628551653490544177:ℝ)/292968750000) := by
    rw [centralNum13_22_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((47:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((178425:ℝ)/2), ((-13176075:ℝ)/2), ((777815145:ℝ)/8), ((-3968389015:ℝ)/8), ((9393350195:ℝ)/8), ((-26366634375:ℝ)/16), ((77851609375:ℝ)/64), ((-25714921875:ℝ)/64), ((5236328125:ℝ)/96), ((-9765625:ℝ)/4)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_22 q| ≤ ((18879860033522659766646159653:ℝ)/153600000000) := by
    rw [centralNum23_22_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((114395264360471055649991694439:ℝ)/100000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece19_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece19_E11 h0) m23'
  have c5 := scaled_affine (X := ((11:ℝ)/1000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2))| ≤ ((907910466892294408885059584000000:ℝ)/654547508008408998053448892878321711) := by
    rw [abs_neg, tailWeight_2, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((47:ℝ)/10)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((47:ℝ)/10)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece19_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((2570430941234500:ℝ)/4782969)) ≤ ((47:ℝ)/10)^6*(8000*(2*((47:ℝ)/10)-3)^2*(1/((136849623739649786158649343719:ℝ)/100000000))*((2570430941234500:ℝ)/4782969)) := by
          gcongr
      _ ≤ ((907910466892294408885059584000000:ℝ)/654547508008408998053448892878321711) := by norm_num
  have c7 := affine_round (α := ((71316246105356661:ℝ)/6400000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((-1370581869709386219151679364153:ℝ)/13107200000000000000) + ((238815075544144533:ℝ)/16000000000)*((11:ℝ)/1000) - ((105760774801005919:ℝ)/10000000000)) (β := ((7346639960081883:ℝ)/320000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((-109357910729844436373271859269:ℝ)/655360000000000000) - 3*((-1370581869709386219151679364153:ℝ)/13107200000000000000)) + ((25556759236418949:ℝ)/800000000)*((11:ℝ)/1000) - ((243365152424811631:ℝ)/10000000000)) ht
  have hW : pieceW q pieceX_19 2 2 = centralNum11_22 q + 8*(Real.exp (-(3*((93:ℝ)/20)))*Real.exp (-3*t))*centralNum12_22 q + 18*Real.exp (-8*q)*centralNum13_22 q + 72*Real.exp (-11*q)*centralNum23_22 q + 8*q^7*(2*q-3)^2*((11:ℝ)/1000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2)) := by
    rw [pieceW_22, pieceX_19, sym4_22, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((502000612277954499342402347784565625177938465654565666360159:ℝ)/13086182807111473049391170324888145364330075925833988794114000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((71316246105356661:ℝ)/6400000000) + ((7346639960081883:ℝ)/320000000)*t) + (8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((-1370581869709386219151679364153:ℝ)/13107200000000000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((-109357910729844436373271859269:ℝ)/655360000000000000) - 3*((-1370581869709386219151679364153:ℝ)/13107200000000000000))*t) + (((238815075544144533:ℝ)/16000000000) + ((25556759236418949:ℝ)/800000000)*t)*((11:ℝ)/1000) - (((105760774801005919:ℝ)/10000000000) + t * ((243365152424811631:ℝ)/10000000000)) = (((71316246105356661:ℝ)/6400000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((-1370581869709386219151679364153:ℝ)/13107200000000000000) + ((238815075544144533:ℝ)/16000000000)*((11:ℝ)/1000) - ((105760774801005919:ℝ)/10000000000)) + t*(((7346639960081883:ℝ)/320000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((-109357910729844436373271859269:ℝ)/655360000000000000) - 3*((-1370581869709386219151679364153:ℝ)/13107200000000000000)) + ((25556759236418949:ℝ)/800000000)*((11:ℝ)/1000) - ((243365152424811631:ℝ)/10000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece19_e23 {q : ℝ} (h0 : ((23:ℝ)/5) ≤ q) (h1 : q ≤ ((47:ℝ)/10)) :
    |pieceW q pieceX_19 2 3 - (((20054067407836417:ℝ)/10000000000) + (q - ((93:ℝ)/20)) * ((28197495222373063:ℝ)/20000000000))| ≤ ((16011794588778577:ℝ)/125000000000) := by
  set t := q - ((93:ℝ)/20) with htd
  have hq : q = ((93:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece19_L3 piece19_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((93:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_23 q = ∑ e ∈ Finset.range 9, ([((190402949793717:ℝ)/80000000), ((133214672850021:ℝ)/32000000), ((5452567992387:ℝ)/1600000), ((135350942733:ℝ)/80000), ((438342759:ℝ)/800), ((23282487:ℝ)/200), ((156177:ℝ)/10), (1198:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_23; ring
  have h12 : centralNum12_23 q = ∑ e ∈ Finset.range 16, ([((-196601653895142978230720692962681:ℝ)/3670016000000000000000), ((-10172960844110588682468902170359:ℝ)/18350080000000000000), ((-441266066193758203895698474893:ℝ)/367001600000000000), ((-56200541841107933075665426503:ℝ)/45875200000000000), ((-3150717943307594853132939897:ℝ)/4587520000000000), ((-111790131350576112586985643:ℝ)/573440000000000), ((17267780024591991453243:ℝ)/11468800000000), ((1382872180394948729573:ℝ)/57344000000), ((286159830503208064561:ℝ)/28672000000), ((1505963855787204291:ℝ)/716800000), ((77014976069878353:ℝ)/358400000), ((-8528008720221:ℝ)/1792000), ((-165105299511:ℝ)/35840), ((-2812637277:ℝ)/4480), ((-17996823:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_23; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((190402949793717:ℝ)/80000000), ((133214672850021:ℝ)/32000000), ((5452567992387:ℝ)/1600000), ((135350942733:ℝ)/80000), ((438342759:ℝ)/800), ((23282487:ℝ)/200), ((156177:ℝ)/10), (1198:ℝ), (40:ℝ)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-196601653895142978230720692962681:ℝ)/3670016000000000000000), ((-10172960844110588682468902170359:ℝ)/18350080000000000000), ((-441266066193758203895698474893:ℝ)/367001600000000000), ((-56200541841107933075665426503:ℝ)/45875200000000000), ((-3150717943307594853132939897:ℝ)/4587520000000000), ((-111790131350576112586985643:ℝ)/573440000000000), ((17267780024591991453243:ℝ)/11468800000000), ((1382872180394948729573:ℝ)/57344000000), ((286159830503208064561:ℝ)/28672000000), ((1505963855787204291:ℝ)/716800000), ((77014976069878353:ℝ)/358400000), ((-8528008720221:ℝ)/1792000), ((-165105299511:ℝ)/35840), ((-2812637277:ℝ)/4480), ((-17996823:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 14 ht
  have m12 := abs_poly_le (fun e => ([((-196601653895142978230720692962681:ℝ)/3670016000000000000000), ((-10172960844110588682468902170359:ℝ)/18350080000000000000), ((-441266066193758203895698474893:ℝ)/367001600000000000), ((-56200541841107933075665426503:ℝ)/45875200000000000), ((-3150717943307594853132939897:ℝ)/4587520000000000), ((-111790131350576112586985643:ℝ)/573440000000000), ((17267780024591991453243:ℝ)/11468800000000), ((1382872180394948729573:ℝ)/57344000000), ((286159830503208064561:ℝ)/28672000000), ((1505963855787204291:ℝ)/716800000), ((77014976069878353:ℝ)/358400000), ((-8528008720221:ℝ)/1792000), ((-165105299511:ℝ)/35840), ((-2812637277:ℝ)/4480), ((-17996823:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 16 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((190402949793717:ℝ)/80000000), ((133214672850021:ℝ)/32000000), ((5452567992387:ℝ)/1600000), ((135350942733:ℝ)/80000), ((438342759:ℝ)/800), ((23282487:ℝ)/200), ((156177:ℝ)/10), (1198:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e) - (((190402949793717:ℝ)/80000000) + ((133214672850021:ℝ)/32000000)*t)| ≤ ((5590134088179:ℝ)/640000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 16, ([((-196601653895142978230720692962681:ℝ)/3670016000000000000000), ((-10172960844110588682468902170359:ℝ)/18350080000000000000), ((-441266066193758203895698474893:ℝ)/367001600000000000), ((-56200541841107933075665426503:ℝ)/45875200000000000), ((-3150717943307594853132939897:ℝ)/4587520000000000), ((-111790131350576112586985643:ℝ)/573440000000000), ((17267780024591991453243:ℝ)/11468800000000), ((1382872180394948729573:ℝ)/57344000000), ((286159830503208064561:ℝ)/28672000000), ((1505963855787204291:ℝ)/716800000), ((77014976069878353:ℝ)/358400000), ((-8528008720221:ℝ)/1792000), ((-165105299511:ℝ)/35840), ((-2812637277:ℝ)/4480), ((-17996823:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e) - ((-196601653895142978230720692962681:ℝ)/3670016000000000000000) - ((-10172960844110588682468902170359:ℝ)/18350080000000000000)*t| ≤ ((11609634400162718592833266962027:ℝ)/3670016000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 16, ([((-196601653895142978230720692962681:ℝ)/3670016000000000000000), ((-10172960844110588682468902170359:ℝ)/18350080000000000000), ((-441266066193758203895698474893:ℝ)/367001600000000000), ((-56200541841107933075665426503:ℝ)/45875200000000000), ((-3150717943307594853132939897:ℝ)/4587520000000000), ((-111790131350576112586985643:ℝ)/573440000000000), ((17267780024591991453243:ℝ)/11468800000000), ((1382872180394948729573:ℝ)/57344000000), ((286159830503208064561:ℝ)/28672000000), ((1505963855787204291:ℝ)/716800000), ((77014976069878353:ℝ)/358400000), ((-8528008720221:ℝ)/1792000), ((-165105299511:ℝ)/35840), ((-2812637277:ℝ)/4480), ((-17996823:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e)| ≤ ((154970448368205791824121490814149:ℝ)/1835008000000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((238815075544144533:ℝ)/16000000000) - ((25556759236418949:ℝ)/800000000)*t| ≤ ((622293900370931:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((47:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-7627725:ℝ)/2), (173988600:ℝ), (-2299614450:ℝ), (13088188200:ℝ), (-38221499200:ℝ), (63366115840:ℝ), ((-445610508288:ℝ)/7), ((841540698112:ℝ)/21), ((-326820167680:ℝ)/21), ((10133438464:ℝ)/3), ((-2147483648:ℝ)/7)] : List ℝ).getD e 0) 16 hq1'
  have m13' : |centralNum13_23 q| ≤ ((281763831322703163723204050749769:ℝ)/10253906250000) := by
    rw [centralNum13_23_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((47:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-15801525:ℝ)/4), ((655493865:ℝ)/4), ((-7334421225:ℝ)/4), ((16442962485:ℝ)/2), ((-598626108395:ℝ)/32), ((414013307125:ℝ)/16), ((-4611984703125:ℝ)/224), ((399923828125:ℝ)/48), ((-4353201171875:ℝ)/2688), ((189736328125:ℝ)/1344), ((-244140625:ℝ)/56)] : List ℝ).getD e 0) 16 hq1'
  have m23' : |centralNum23_23 q| ≤ ((1803577863118259497822372893263:ℝ)/614400000000) := by
    rw [centralNum23_23_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((114395264360471055649991694439:ℝ)/100000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece19_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece19_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((190402949793717:ℝ)/80000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((-196601653895142978230720692962681:ℝ)/3670016000000000000000) + ((238815075544144533:ℝ)/16000000000)*(0:ℝ) - ((20054067407836417:ℝ)/10000000000)) (β := ((133214672850021:ℝ)/32000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((-10172960844110588682468902170359:ℝ)/18350080000000000000) - 3*((-196601653895142978230720692962681:ℝ)/3670016000000000000000)) + ((25556759236418949:ℝ)/800000000)*(0:ℝ) - ((28197495222373063:ℝ)/20000000000)) ht
  have hW : pieceW q pieceX_19 2 3 = centralNum11_23 q + 8*(Real.exp (-(3*((93:ℝ)/20)))*Real.exp (-3*t))*centralNum12_23 q + 18*Real.exp (-8*q)*centralNum13_23 q + 72*Real.exp (-11*q)*centralNum23_23 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_23, pieceX_19, sym4_23, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((4459022108279471163817161856322326861061491325472924719521:ℝ)/2290081991244507783643454806855425438757763287020948038969950000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((190402949793717:ℝ)/80000000) + ((133214672850021:ℝ)/32000000)*t) + (8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((-196601653895142978230720692962681:ℝ)/3670016000000000000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((-10172960844110588682468902170359:ℝ)/18350080000000000000) - 3*((-196601653895142978230720692962681:ℝ)/3670016000000000000000))*t) + (((238815075544144533:ℝ)/16000000000) + ((25556759236418949:ℝ)/800000000)*t)*(0:ℝ) - (((20054067407836417:ℝ)/10000000000) + t * ((28197495222373063:ℝ)/20000000000)) = (((190402949793717:ℝ)/80000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((-196601653895142978230720692962681:ℝ)/3670016000000000000000) + ((238815075544144533:ℝ)/16000000000)*(0:ℝ) - ((20054067407836417:ℝ)/10000000000)) + t*(((133214672850021:ℝ)/32000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((-10172960844110588682468902170359:ℝ)/18350080000000000000) - 3*((-196601653895142978230720692962681:ℝ)/3670016000000000000000)) + ((25556759236418949:ℝ)/800000000)*(0:ℝ) - ((28197495222373063:ℝ)/20000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece19_e33 {q : ℝ} (h0 : ((23:ℝ)/5) ≤ q) (h1 : q ≤ ((47:ℝ)/10)) :
    |pieceW q pieceX_19 3 3 - (((449392870123219653:ℝ)/50000000000) + (q - ((93:ℝ)/20)) * ((13958665162750187:ℝ)/1000000000))| ≤ ((117241515234397993:ℝ)/50000000000) := by
  set t := q - ((93:ℝ)/20) with htd
  have hq : q = ((93:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece19_L3 piece19_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((93:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_33 q = ∑ e ∈ Finset.range 10, ([((11913931052076879:ℝ)/3200000000), ((769924449917721:ℝ)/80000000), ((579762517110597:ℝ)/56000000), ((2507581122003:ℝ)/400000), ((48011819949:ℝ)/20000), ((611237403:ℝ)/1000), ((5225169:ℝ)/50), ((58194:ℝ)/5), (768:ℝ), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_33; ring
  have h12 : centralNum12_33 q = ∑ e ∈ Finset.range 17, ([((107068827068010799564072602371704209:ℝ)/146800640000000000000000), ((141687034563282720155683540102253241:ℝ)/51380224000000000000000), ((1976169951034944588596274195866913:ℝ)/513802240000000000000), ((9026922247488490192846473260799:ℝ)/3670016000000000000), ((75430208063600266141949354271:ℝ)/183500800000000000), ((-22039468833665295100657977741:ℝ)/45875200000000000), ((-917472784265030439412084617:ℝ)/2293760000000000), ((-3364016675382195796003869:ℝ)/22937600000000), ((-216656677208506406789373:ℝ)/8028160000000), ((-189430478501895197857:ℝ)/401408000000), ((14277077320320968553:ℝ)/14336000000), ((172768650691061601:ℝ)/716800000), ((172407365969301:ℝ)/7168000), ((42948356301:ℝ)/358400), ((-565512273:ℝ)/2560), ((-665423181:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_33; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((11913931052076879:ℝ)/3200000000), ((769924449917721:ℝ)/80000000), ((579762517110597:ℝ)/56000000), ((2507581122003:ℝ)/400000), ((48011819949:ℝ)/20000), ((611237403:ℝ)/1000), ((5225169:ℝ)/50), ((58194:ℝ)/5), (768:ℝ), ((160:ℝ)/7)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((107068827068010799564072602371704209:ℝ)/146800640000000000000000), ((141687034563282720155683540102253241:ℝ)/51380224000000000000000), ((1976169951034944588596274195866913:ℝ)/513802240000000000000), ((9026922247488490192846473260799:ℝ)/3670016000000000000), ((75430208063600266141949354271:ℝ)/183500800000000000), ((-22039468833665295100657977741:ℝ)/45875200000000000), ((-917472784265030439412084617:ℝ)/2293760000000000), ((-3364016675382195796003869:ℝ)/22937600000000), ((-216656677208506406789373:ℝ)/8028160000000), ((-189430478501895197857:ℝ)/401408000000), ((14277077320320968553:ℝ)/14336000000), ((172768650691061601:ℝ)/716800000), ((172407365969301:ℝ)/7168000), ((42948356301:ℝ)/358400), ((-565512273:ℝ)/2560), ((-665423181:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 15 ht
  have m12 := abs_poly_le (fun e => ([((107068827068010799564072602371704209:ℝ)/146800640000000000000000), ((141687034563282720155683540102253241:ℝ)/51380224000000000000000), ((1976169951034944588596274195866913:ℝ)/513802240000000000000), ((9026922247488490192846473260799:ℝ)/3670016000000000000), ((75430208063600266141949354271:ℝ)/183500800000000000), ((-22039468833665295100657977741:ℝ)/45875200000000000), ((-917472784265030439412084617:ℝ)/2293760000000000), ((-3364016675382195796003869:ℝ)/22937600000000), ((-216656677208506406789373:ℝ)/8028160000000), ((-189430478501895197857:ℝ)/401408000000), ((14277077320320968553:ℝ)/14336000000), ((172768650691061601:ℝ)/716800000), ((172407365969301:ℝ)/7168000), ((42948356301:ℝ)/358400), ((-565512273:ℝ)/2560), ((-665423181:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 17 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((11913931052076879:ℝ)/3200000000), ((769924449917721:ℝ)/80000000), ((579762517110597:ℝ)/56000000), ((2507581122003:ℝ)/400000), ((48011819949:ℝ)/20000), ((611237403:ℝ)/1000), ((5225169:ℝ)/50), ((58194:ℝ)/5), (768:ℝ), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e) - (((11913931052076879:ℝ)/3200000000) + ((769924449917721:ℝ)/80000000)*t)| ≤ ((597655983146617:ℝ)/22400000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 17, ([((107068827068010799564072602371704209:ℝ)/146800640000000000000000), ((141687034563282720155683540102253241:ℝ)/51380224000000000000000), ((1976169951034944588596274195866913:ℝ)/513802240000000000000), ((9026922247488490192846473260799:ℝ)/3670016000000000000), ((75430208063600266141949354271:ℝ)/183500800000000000), ((-22039468833665295100657977741:ℝ)/45875200000000000), ((-917472784265030439412084617:ℝ)/2293760000000000), ((-3364016675382195796003869:ℝ)/22937600000000), ((-216656677208506406789373:ℝ)/8028160000000), ((-189430478501895197857:ℝ)/401408000000), ((14277077320320968553:ℝ)/14336000000), ((172768650691061601:ℝ)/716800000), ((172407365969301:ℝ)/7168000), ((42948356301:ℝ)/358400), ((-565512273:ℝ)/2560), ((-665423181:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e) - ((107068827068010799564072602371704209:ℝ)/146800640000000000000000) - ((141687034563282720155683540102253241:ℝ)/51380224000000000000000)*t| ≤ ((5099796454267643476547168966985091:ℝ)/513802240000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 17, ([((107068827068010799564072602371704209:ℝ)/146800640000000000000000), ((141687034563282720155683540102253241:ℝ)/51380224000000000000000), ((1976169951034944588596274195866913:ℝ)/513802240000000000000), ((9026922247488490192846473260799:ℝ)/3670016000000000000), ((75430208063600266141949354271:ℝ)/183500800000000000), ((-22039468833665295100657977741:ℝ)/45875200000000000), ((-917472784265030439412084617:ℝ)/2293760000000000), ((-3364016675382195796003869:ℝ)/22937600000000), ((-216656677208506406789373:ℝ)/8028160000000), ((-189430478501895197857:ℝ)/401408000000), ((14277077320320968553:ℝ)/14336000000), ((172768650691061601:ℝ)/716800000), ((172407365969301:ℝ)/7168000), ((42948356301:ℝ)/358400), ((-565512273:ℝ)/2560), ((-665423181:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e)| ≤ ((450684208473946802028643047319076443:ℝ)/513802240000000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((238815075544144533:ℝ)/16000000000), ((25556759236418949:ℝ)/800000000), ((151333090973829:ℝ)/5000000), ((1041512813523:ℝ)/62500), ((293861373309:ℝ)/50000), ((3443140953:ℝ)/2500), ((26810784:ℝ)/125), ((535248:ℝ)/25), ((6216:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((238815075544144533:ℝ)/16000000000) - ((25556759236418949:ℝ)/800000000)*t| ≤ ((622293900370931:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((47:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-8120475:ℝ)/4), ((464861025:ℝ)/2), (-5906535975:ℝ), ((411904731750:ℝ)/7), ((-2024051769000:ℝ)/7), ((5554394637600:ℝ)/7), (-1314913862656:ℝ), ((9709155336192:ℝ)/7), ((-6724555112448:ℝ)/7), ((1313173667840:ℝ)/3), ((-6168244125696:ℝ)/49), ((3004329623552:ℝ)/147), ((-68719476736:ℝ)/49)] : List ℝ).getD e 0) 17 hq1'
  have m13' : |centralNum13_33 q| ≤ ((747910237939589842582868339262300661:ℝ)/717773437500000) := by
    rw [centralNum13_33_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((47:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-16872075:ℝ)/8), ((1833754545:ℝ)/8), ((-83998007145:ℝ)/16), ((4929124002765:ℝ)/112), ((-76723155584685:ℝ)/448), ((164888745653055:ℝ)/448), ((-63358359907625:ℝ)/128), ((364713160040625:ℝ)/896), ((-334937462578125:ℝ)/1792), ((245466998046875:ℝ)/5376), ((-72144521484375:ℝ)/12544), ((6518798828125:ℝ)/18816), ((-6103515625:ℝ)/784)] : List ℝ).getD e 0) 17 hq1'
  have m23' : |centralNum23_33 q| ≤ ((1361730823221074812816407022740739:ℝ)/17203200000000) := by
    rw [centralNum23_33_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((114395264360471055649991694439:ℝ)/100000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece19_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece19_E11 h0) m23'
  have c5 := scaled_affine (X := ((11:ℝ)/1000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3))| ≤ ((1168631660563973680113046765568000000:ℝ)/17672782716227042947443120107714686197) := by
    rw [abs_neg, tailWeight_3, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((47:ℝ)/10)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((47:ℝ)/10)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece19_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((3308571812705231500:ℝ)/129140163)) ≤ ((47:ℝ)/10)^6*(8000*(2*((47:ℝ)/10)-3)^2*(1/((136849623739649786158649343719:ℝ)/100000000))*((3308571812705231500:ℝ)/129140163)) := by
          gcongr
      _ ≤ ((1168631660563973680113046765568000000:ℝ)/17672782716227042947443120107714686197) := by norm_num
  have c7 := affine_round (α := ((11913931052076879:ℝ)/3200000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((107068827068010799564072602371704209:ℝ)/146800640000000000000000) + ((238815075544144533:ℝ)/16000000000)*((11:ℝ)/1000) - ((449392870123219653:ℝ)/50000000000)) (β := ((769924449917721:ℝ)/80000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((141687034563282720155683540102253241:ℝ)/51380224000000000000000) - 3*((107068827068010799564072602371704209:ℝ)/146800640000000000000000)) + ((25556759236418949:ℝ)/800000000)*((11:ℝ)/1000) - ((13958665162750187:ℝ)/1000000000)) ht
  have hW : pieceW q pieceX_19 3 3 = centralNum11_33 q + 8*(Real.exp (-(3*((93:ℝ)/20)))*Real.exp (-3*t))*centralNum12_33 q + 18*Real.exp (-8*q)*centralNum13_33 q + 72*Real.exp (-11*q)*centralNum23_33 q + 8*q^7*(2*q-3)^2*((11:ℝ)/1000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3)) := by
    rw [pieceW_33, pieceX_19, sym4_33, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((5530742129664917212930647357641632402607811436241468656767289:ℝ)/1282445915096924358840334691839038245704347440731730901823172000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((11913931052076879:ℝ)/3200000000) + ((769924449917721:ℝ)/80000000)*t) + (8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((107068827068010799564072602371704209:ℝ)/146800640000000000000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((141687034563282720155683540102253241:ℝ)/51380224000000000000000) - 3*((107068827068010799564072602371704209:ℝ)/146800640000000000000000))*t) + (((238815075544144533:ℝ)/16000000000) + ((25556759236418949:ℝ)/800000000)*t)*((11:ℝ)/1000) - (((449392870123219653:ℝ)/50000000000) + t * ((13958665162750187:ℝ)/1000000000)) = (((11913931052076879:ℝ)/3200000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*((107068827068010799564072602371704209:ℝ)/146800640000000000000000) + ((238815075544144533:ℝ)/16000000000)*((11:ℝ)/1000) - ((449392870123219653:ℝ)/50000000000)) + t*(((769924449917721:ℝ)/80000000) + 8*(((1/((114395264360471055649991694439:ℝ)/100000000000000000000000))+(1/((57197222630980538693091656663:ℝ)/50000000000000000000000)))/2)*(((141687034563282720155683540102253241:ℝ)/51380224000000000000000) - 3*((107068827068010799564072602371704209:ℝ)/146800640000000000000000)) + ((25556759236418949:ℝ)/800000000)*((11:ℝ)/1000) - ((13958665162750187:ℝ)/1000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece19_plus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((86677222481261519:ℝ)/5000000000) + ((1:ℝ)/20)*((357021369659716147:ℝ)/10000000000) - (((211907933216721309:ℝ)/2500000000000) + ((7983012606004623:ℝ)/1000000000000) + ((310686493859183173:ℝ)/100000000000000) + ((521292597849076557:ℝ)/100000000000000)))
      (((-230020142636681661:ℝ)/100000000000) + ((1:ℝ)/20)*((-338093431055072137:ℝ)/100000000000))
      (((-383365635337059121:ℝ)/10000000000000) + ((1:ℝ)/20)*((-233404830596569067:ℝ)/5000000000000))
      (((2693059507518667:ℝ)/25000000000) + ((1:ℝ)/20)*((-740651526676598731:ℝ)/10000000000000))
      (((6266902916530419:ℝ)/500000000) + ((1:ℝ)/20)*((61624487246809589:ℝ)/2500000000) - (((7983012606004623:ℝ)/1000000000000) + ((578689799666220977:ℝ)/10000000000000) + ((181975624548442573:ℝ)/10000000000000) + ((121017417146296129:ℝ)/10000000000000)))
      (((-921879064183362799:ℝ)/1000000000000) + ((1:ℝ)/20)*((-156438009206838183:ℝ)/100000000000))
      (((-110938482953987413:ℝ)/125000000000) + ((1:ℝ)/20)*((-185137014440638157:ℝ)/1000000000000))
      (((105760774801005919:ℝ)/10000000000) + ((1:ℝ)/20)*((243365152424811631:ℝ)/10000000000) - (((310686493859183173:ℝ)/100000000000000) + ((181975624548442573:ℝ)/10000000000000) + ((416523309221892699:ℝ)/5000000000000) + ((16011794588778577:ℝ)/125000000000)))
      (((20054067407836417:ℝ)/10000000000) + ((1:ℝ)/20)*((28197495222373063:ℝ)/20000000000))
      (((449392870123219653:ℝ)/50000000000) + ((1:ℝ)/20)*((13958665162750187:ℝ)/1000000000) - (((521292597849076557:ℝ)/100000000000000) + ((121017417146296129:ℝ)/10000000000000) + ((16011794588778577:ℝ)/125000000000) + ((117241515234397993:ℝ)/50000000000))) i j :=
  quadForm_nonneg_of_ldl ((190194853677411087911:ℝ)/10000000000000) ((6347548068649730223794579670285246998369:ℝ)/475487134193527719777500000000000) ((291591025648590423918958545320553087181291948762912671565874381:ℝ)/25390192274598920895178318681140987993476000000000000000) ((158273065980475226674254993200503938421305967364653870129318329147396302240813164693:ℝ)/23327282051887233913516683625644246974503355901033013725269950480000000000000) ((-24692481418943526785:ℝ)/190194853677411087911) ((-4067061183967160277:ℝ)/1901948536774110879110) ((20803824533472737269:ℝ)/3803897073548221758220) ((-3824355283662230929190143989019113018799:ℝ)/50780384549197841790356637362281975986952) ((-6719661735037304492484222265934170747781:ℝ)/101560769098395683580713274724563951973904) ((102048418938124690840318570487389460716771817575063652343538183:ℝ)/583182051297180847837917090641106174362583897525825343131748762)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece19_minus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((86677222481261519:ℝ)/5000000000) - ((1:ℝ)/20)*((357021369659716147:ℝ)/10000000000) - (((211907933216721309:ℝ)/2500000000000) + ((7983012606004623:ℝ)/1000000000000) + ((310686493859183173:ℝ)/100000000000000) + ((521292597849076557:ℝ)/100000000000000)))
      (((-230020142636681661:ℝ)/100000000000) - ((1:ℝ)/20)*((-338093431055072137:ℝ)/100000000000))
      (((-383365635337059121:ℝ)/10000000000000) - ((1:ℝ)/20)*((-233404830596569067:ℝ)/5000000000000))
      (((2693059507518667:ℝ)/25000000000) - ((1:ℝ)/20)*((-740651526676598731:ℝ)/10000000000000))
      (((6266902916530419:ℝ)/500000000) - ((1:ℝ)/20)*((61624487246809589:ℝ)/2500000000) - (((7983012606004623:ℝ)/1000000000000) + ((578689799666220977:ℝ)/10000000000000) + ((181975624548442573:ℝ)/10000000000000) + ((121017417146296129:ℝ)/10000000000000)))
      (((-921879064183362799:ℝ)/1000000000000) - ((1:ℝ)/20)*((-156438009206838183:ℝ)/100000000000))
      (((-110938482953987413:ℝ)/125000000000) - ((1:ℝ)/20)*((-185137014440638157:ℝ)/1000000000000))
      (((105760774801005919:ℝ)/10000000000) - ((1:ℝ)/20)*((243365152424811631:ℝ)/10000000000) - (((310686493859183173:ℝ)/100000000000000) + ((181975624548442573:ℝ)/10000000000000) + ((416523309221892699:ℝ)/5000000000000) + ((16011794588778577:ℝ)/125000000000)))
      (((20054067407836417:ℝ)/10000000000) - ((1:ℝ)/20)*((28197495222373063:ℝ)/20000000000))
      (((449392870123219653:ℝ)/50000000000) - ((1:ℝ)/20)*((13958665162750187:ℝ)/1000000000) - (((521292597849076557:ℝ)/100000000000000) + ((121017417146296129:ℝ)/10000000000000) + ((16011794588778577:ℝ)/125000000000) + ((117241515234397993:ℝ)/50000000000))) i j :=
  quadForm_nonneg_of_ldl ((154492716711439473211:ℝ)/10000000000000) ((526780670563979634709251619616771643693:ℝ)/48278973972324835378437500000000) ((50910678469399328044835624203585576689622062025094681115006087:ℝ)/5618993819349116103565350609245564199392000000000000000) ((4354281059693920977760712047263733668534574523051175699377482682903629591380339979:ℝ)/814570855510389248717369987257369227033952992401514897840097392000000000000) ((-21311547108392805415:ℝ)/154492716711439473211) ((-3600251522774022143:ℝ)/1544927167114394732110) ((22285127586825934731:ℝ)/3089854334228789464220) ((-874044025898246706105516450976435152173:ℝ)/11237987638698232207130701218491128398784) ((-5332349288284119610706204374078255307833:ℝ)/67427925832189393242784207310946770392704) ((20993251064988145108675201447117511401755945925888345617051001:ℝ)/101821356938798656089671248407171153379244124050189362230012174)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

/-- **Piece 19.** The piece matrix is positive semidefinite on `q ∈ [23/5, 47/10]`. -/
theorem piece_19 {q : ℝ} (h0 : ((23:ℝ)/5) ≤ q) (h1 : q ≤ ((47:ℝ)/10)) (y : Fin 4 → ℝ) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceW q pieceX_19 i j :=
  pieceForm_nonneg (pieceW_symm (sym4_symm _ _ _ _ _ _ _ _ _ _) q) (by norm_num : (0:ℝ) < ((1:ℝ)/20))
    (abs_le.mpr ⟨by linarith, by linarith⟩)
    (piece19_e00 h0 h1) (piece19_e01 h0 h1) (piece19_e02 h0 h1) (piece19_e03 h0 h1) (piece19_e11 h0 h1) (piece19_e12 h0 h1) (piece19_e13 h0 h1) (piece19_e22 h0 h1) (piece19_e23 h0 h1) (piece19_e33 h0 h1)
    piece19_plus piece19_minus y

end
end RHTower.ThetaCuspOddFourPieces
