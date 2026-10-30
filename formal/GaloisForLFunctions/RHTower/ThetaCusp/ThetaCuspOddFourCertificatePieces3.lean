import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourPieceSetup

/-!
# Piece certificates 10–14 on `q ∈ [37/10, 21/5]`

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

/-! #### Piece 10 (seam), `q ∈ [37/10, 19/5]` -/

/-- The compensation matrix of piece 10. -/
def pieceX_10 : Fin 4 → Fin 4 → ℝ :=
  sym4 ((111140091739:ℝ)/10000000000000) ((-922669525289:ℝ)/1000000000000000) ((-30995684307:ℝ)/5000000000000) ((-34583834689:ℝ)/250000000000) ((10245427511:ℝ)/500000000000) ((35830011351:ℝ)/250000000000) ((987248065489:ℝ)/1000000000000) ((286382726407:ℝ)/50000000000) ((-180308963201:ℝ)/50000000000) ((199890813323:ℝ)/1000000000)

theorem piece10_L3 : ((768799196918931088273177269557:ℝ)/10000000000000000000000000) ≤ Real.exp ((3:ℝ)*((15:ℝ)/4)) := by
  have h := le_exp_nat_add 11 (f := ((1:ℝ)/4)) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((15:ℝ)/4) = ((11:ℕ):ℝ) + ((1:ℝ)/4) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece10_U3 : Real.exp ((3:ℝ)*((15:ℝ)/4)) ≤ ((38439959905358380531517881901:ℝ)/500000000000000000000000) := by
  have h := exp_nat_add_le 11 (f := ((1:ℝ)/4)) (by norm_num) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((15:ℝ)/4) = ((11:ℕ):ℝ) + ((1:ℝ)/4) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem piece10_L8_at : ((358167818375224268825234717439:ℝ)/50000000000000000) ≤ Real.exp ((8:ℝ)*((37:ℝ)/10)) := by
  have h := le_exp_nat_add 29 (f := ((3:ℝ)/5)) (by norm_num)
  rw [show ((8:ℝ):ℝ)*((37:ℝ)/10) = ((29:ℕ):ℝ) + ((3:ℝ)/5) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece10_E8 {q : ℝ} (h0 : ((37:ℝ)/10) ≤ q) : Real.exp (-((8:ℝ))*q) ≤ 1/((358167818375224268825234717439:ℝ)/50000000000000000) := by
  have hm : Real.exp (-((8:ℝ))*q) ≤ Real.exp (-((8:ℝ)*((37:ℝ)/10))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece10_L8_at (le_refl _)).2

theorem piece10_L11_at : ((18960294104224021848093835969:ℝ)/40000000000) ≤ Real.exp ((11:ℝ)*((37:ℝ)/10)) := by
  have h := le_exp_nat_add 40 (f := ((7:ℝ)/10)) (by norm_num)
  rw [show ((11:ℝ):ℝ)*((37:ℝ)/10) = ((40:ℕ):ℝ) + ((7:ℝ)/10) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece10_E11 {q : ℝ} (h0 : ((37:ℝ)/10) ≤ q) : Real.exp (-((11:ℝ))*q) ≤ 1/((18960294104224021848093835969:ℝ)/40000000000) := by
  have hm : Real.exp (-((11:ℝ))*q) ≤ Real.exp (-((11:ℝ)*((37:ℝ)/10))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece10_L11_at (le_refl _)).2

theorem piece10_Lt_at : ((25051388162973771983886131:ℝ)/250000000) ≤ Real.exp (((529:ℝ)/50)*((37:ℝ)/10)) := by
  have h := le_exp_nat_add 39 (f := ((73:ℝ)/500)) (by norm_num)
  rw [show (((529:ℝ)/50):ℝ)*((37:ℝ)/10) = ((39:ℕ):ℝ) + ((73:ℝ)/500) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece10_Et {q : ℝ} (h0 : ((37:ℝ)/10) ≤ q) : Real.exp (-(((529:ℝ)/50))*q) ≤ 1/((25051388162973771983886131:ℝ)/250000000) := by
  have hm : Real.exp (-(((529:ℝ)/50))*q) ≤ Real.exp (-(((529:ℝ)/50)*((37:ℝ)/10))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece10_Lt_at (le_refl _)).2

theorem piece10_e00 {q : ℝ} (h0 : ((37:ℝ)/10) ≤ q) (h1 : q ≤ ((19:ℝ)/5)) :
    |pieceW q pieceX_10 0 0 - (((54798896558359531:ℝ)/25000000000) + (q - ((15:ℝ)/4)) * ((70549480059238571:ℝ)/12500000000))| ≤ ((44273611092566819:ℝ)/2500000000000) := by
  set t := q - ((15:ℝ)/4) with htd
  have hq : q = ((15:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece10_L3 piece10_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((15:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_00 q = ∑ e ∈ Finset.range 10, ([((17940234375:ℝ)/8192), ((11447578125:ℝ)/2048), ((102515625:ℝ)/16), ((69103125:ℝ)/16), ((30121875:ℝ)/16), ((2197125:ℝ)/4), (107100:ℝ), (13440:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_00; ring
  have h12 : centralNum12_00 q = ∑ e ∈ Finset.range 11, ([((-5287243359375:ℝ)/32768), ((-3762152578125:ℝ)/8192), ((-603099421875:ℝ)/1024), ((-57345721875:ℝ)/128), ((-14322065625:ℝ)/64), ((-1226775375:ℝ)/16), (-18244800:ℝ), (-2976630:ℝ), (-318606:ℝ), (-20200:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_00; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((17940234375:ℝ)/8192), ((11447578125:ℝ)/2048), ((102515625:ℝ)/16), ((69103125:ℝ)/16), ((30121875:ℝ)/16), ((2197125:ℝ)/4), (107100:ℝ), (13440:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-5287243359375:ℝ)/32768), ((-3762152578125:ℝ)/8192), ((-603099421875:ℝ)/1024), ((-57345721875:ℝ)/128), ((-14322065625:ℝ)/64), ((-1226775375:ℝ)/16), (-18244800:ℝ), (-2976630:ℝ), (-318606:ℝ), (-20200:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 9 ht
  have m12 := abs_poly_le (fun e => ([((-5287243359375:ℝ)/32768), ((-3762152578125:ℝ)/8192), ((-603099421875:ℝ)/1024), ((-57345721875:ℝ)/128), ((-14322065625:ℝ)/64), ((-1226775375:ℝ)/16), (-18244800:ℝ), (-2976630:ℝ), (-318606:ℝ), (-20200:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 11 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((17940234375:ℝ)/8192), ((11447578125:ℝ)/2048), ((102515625:ℝ)/16), ((69103125:ℝ)/16), ((30121875:ℝ)/16), ((2197125:ℝ)/4), (107100:ℝ), (13440:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - (((17940234375:ℝ)/8192) + ((11447578125:ℝ)/2048)*t)| ≤ ((16569874262101:ℝ)/1000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 11, ([((-5287243359375:ℝ)/32768), ((-3762152578125:ℝ)/8192), ((-603099421875:ℝ)/1024), ((-57345721875:ℝ)/128), ((-14322065625:ℝ)/64), ((-1226775375:ℝ)/16), (-18244800:ℝ), (-2976630:ℝ), (-318606:ℝ), (-20200:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e) - ((-5287243359375:ℝ)/32768) - ((-3762152578125:ℝ)/8192)*t| ≤ ((61193410661851121:ℝ)/40000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 11, ([((-5287243359375:ℝ)/32768), ((-3762152578125:ℝ)/8192), ((-603099421875:ℝ)/1024), ((-57345721875:ℝ)/128), ((-14322065625:ℝ)/64), ((-1226775375:ℝ)/16), (-18244800:ℝ), (-2976630:ℝ), (-318606:ℝ), (-20200:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((1814902876917776:ℝ)/9765625) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((13839609375:ℝ)/8192) - ((9533953125:ℝ)/2048)*t| ≤ ((916188335461:ℝ)/62500000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((19:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (600:ℝ), (-7776:ℝ), (16800:ℝ), (-9216:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m13' : |centralNum13_00 q| ≤ ((86978318280925416:ℝ)/9765625) := by
    rw [centralNum13_00_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((19:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (780:ℝ), (-6156:ℝ), (15288:ℝ), (-14400:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m23' : |centralNum23_00 q| ≤ ((23130904915424712:ℝ)/1953125) := by
    rw [centralNum23_00_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((38439959905358380531517881901:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece10_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece10_E11 h0) m23'
  have c5 := scaled_affine (X := ((111140091739:ℝ)/10000000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0))| ≤ ((1333543553067013531648000000:ℝ)/1479259419635438261876492149419) := by
    rw [abs_neg, tailWeight_0, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((19:ℝ)/5)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((19:ℝ)/5)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece10_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((10465499600:ℝ)/59049)) ≤ ((19:ℝ)/5)^6*(8000*(2*((19:ℝ)/5)-3)^2*(1/((25051388162973771983886131:ℝ)/250000000))*((10465499600:ℝ)/59049)) := by
          gcongr
      _ ≤ ((1333543553067013531648000000:ℝ)/1479259419635438261876492149419) := by norm_num
  have c7 := affine_round (α := ((17940234375:ℝ)/8192) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((-5287243359375:ℝ)/32768) + ((13839609375:ℝ)/8192)*((111140091739:ℝ)/10000000000000) - ((54798896558359531:ℝ)/25000000000)) (β := ((11447578125:ℝ)/2048) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((-3762152578125:ℝ)/8192) - 3*((-5287243359375:ℝ)/32768)) + ((9533953125:ℝ)/2048)*((111140091739:ℝ)/10000000000000) - ((70549480059238571:ℝ)/12500000000)) ht
  have hW : pieceW q pieceX_10 0 0 = centralNum11_00 q + 8*(Real.exp (-(3*((15:ℝ)/4)))*Real.exp (-3*t))*centralNum12_00 q + 18*Real.exp (-8*q)*centralNum13_00 q + 72*Real.exp (-11*q)*centralNum23_00 q + 8*q^7*(2*q-3)^2*((111140091739:ℝ)/10000000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0)) := by
    rw [pieceW_00, pieceX_10, sym4_00, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((6086344772085063572169239093110698078109533689301495601571727:ℝ)/1891367059509467726944081741163766760312888297371850789622848000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((17940234375:ℝ)/8192) + ((11447578125:ℝ)/2048)*t) + (8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((-5287243359375:ℝ)/32768) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((-3762152578125:ℝ)/8192) - 3*((-5287243359375:ℝ)/32768))*t) + (((13839609375:ℝ)/8192) + ((9533953125:ℝ)/2048)*t)*((111140091739:ℝ)/10000000000000) - (((54798896558359531:ℝ)/25000000000) + t * ((70549480059238571:ℝ)/12500000000)) = (((17940234375:ℝ)/8192) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((-5287243359375:ℝ)/32768) + ((13839609375:ℝ)/8192)*((111140091739:ℝ)/10000000000000) - ((54798896558359531:ℝ)/25000000000)) + t*(((11447578125:ℝ)/2048) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((-3762152578125:ℝ)/8192) - 3*((-5287243359375:ℝ)/32768)) + ((9533953125:ℝ)/2048)*((111140091739:ℝ)/10000000000000) - ((70549480059238571:ℝ)/12500000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece10_e01 {q : ℝ} (h0 : ((37:ℝ)/10) ≤ q) (h1 : q ≤ ((19:ℝ)/5)) :
    |pieceW q pieceX_10 0 1 - (((-546481712166114717:ℝ)/1000000000000) + (q - ((15:ℝ)/4)) * ((-956435675908009427:ℝ)/1000000000000))| ≤ ((493633251905758273:ℝ)/100000000000000) := by
  set t := q - ((15:ℝ)/4) with htd
  have hq : q = ((15:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece10_L3 piece10_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((15:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_01 q = ∑ e ∈ Finset.range 8, ([((-512578125:ℝ)/1024), ((-239203125:ℝ)/256), ((-47840625:ℝ)/64), ((-5315625:ℝ)/16), ((-354375:ℝ)/4), (-14175:ℝ), (-1260:ℝ), (-48:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_01; ring
  have h12 : centralNum12_01 q = ∑ e ∈ Finset.range 12, ([((-111747669609375:ℝ)/262144), ((-47495864953125:ℝ)/32768), ((-36509962528125:ℝ)/16384), ((-4192018059375:ℝ)/2048), ((-639503656875:ℝ)/512), ((-34040681325:ℝ)/64), ((-5162731245:ℝ)/32), ((-139459107:ℝ)/4), ((-21043899:ℝ)/4), (-527970:ℝ), (-31716:ℝ), (-864:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_01; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-512578125:ℝ)/1024), ((-239203125:ℝ)/256), ((-47840625:ℝ)/64), ((-5315625:ℝ)/16), ((-354375:ℝ)/4), (-14175:ℝ), (-1260:ℝ), (-48:ℝ)] : List ℝ).getD e 0) 6 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-111747669609375:ℝ)/262144), ((-47495864953125:ℝ)/32768), ((-36509962528125:ℝ)/16384), ((-4192018059375:ℝ)/2048), ((-639503656875:ℝ)/512), ((-34040681325:ℝ)/64), ((-5162731245:ℝ)/32), ((-139459107:ℝ)/4), ((-21043899:ℝ)/4), (-527970:ℝ), (-31716:ℝ), (-864:ℝ)] : List ℝ).getD e 0) 10 ht
  have m12 := abs_poly_le (fun e => ([((-111747669609375:ℝ)/262144), ((-47495864953125:ℝ)/32768), ((-36509962528125:ℝ)/16384), ((-4192018059375:ℝ)/2048), ((-639503656875:ℝ)/512), ((-34040681325:ℝ)/64), ((-5162731245:ℝ)/32), ((-139459107:ℝ)/4), ((-21043899:ℝ)/4), (-527970:ℝ), (-31716:ℝ), (-864:ℝ)] : List ℝ).getD e 0) 12 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 8, ([((-512578125:ℝ)/1024), ((-239203125:ℝ)/256), ((-47840625:ℝ)/64), ((-5315625:ℝ)/16), ((-354375:ℝ)/4), (-14175:ℝ), (-1260:ℝ), (-48:ℝ)] : List ℝ).getD e 0 * t^e) - (((-512578125:ℝ)/1024) + ((-239203125:ℝ)/256)*t)| ≤ ((76434435789:ℝ)/40000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 12, ([((-111747669609375:ℝ)/262144), ((-47495864953125:ℝ)/32768), ((-36509962528125:ℝ)/16384), ((-4192018059375:ℝ)/2048), ((-639503656875:ℝ)/512), ((-34040681325:ℝ)/64), ((-5162731245:ℝ)/32), ((-139459107:ℝ)/4), ((-21043899:ℝ)/4), (-527970:ℝ), (-31716:ℝ), (-864:ℝ)] : List ℝ).getD e 0 * t^e) - ((-111747669609375:ℝ)/262144) - ((-47495864953125:ℝ)/32768)*t| ≤ ((74685617278962165699:ℝ)/12800000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 12, ([((-111747669609375:ℝ)/262144), ((-47495864953125:ℝ)/32768), ((-36509962528125:ℝ)/16384), ((-4192018059375:ℝ)/2048), ((-639503656875:ℝ)/512), ((-34040681325:ℝ)/64), ((-5162731245:ℝ)/32), ((-139459107:ℝ)/4), ((-21043899:ℝ)/4), (-527970:ℝ), (-31716:ℝ), (-864:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((24638246192130846:ℝ)/48828125) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((13839609375:ℝ)/8192) - ((9533953125:ℝ)/2048)*t| ≤ ((916188335461:ℝ)/62500000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((19:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-6288:ℝ), (81024:ℝ), (-238720:ℝ), (246784:ℝ), (-98304:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m13' : |centralNum13_01 q| ≤ ((21118026310314920496:ℝ)/48828125) := by
    rw [centralNum13_01_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((19:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-7368:ℝ), (59208:ℝ), (-155734:ℝ), (205300:ℝ), (-60000:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m23' : |centralNum23_01 q| ≤ ((586764113003930886:ℝ)/1953125) := by
    rw [centralNum23_01_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((38439959905358380531517881901:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece10_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece10_E11 h0) m23'
  have c5 := scaled_affine (X := ((-922669525289:ℝ)/1000000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-512578125:ℝ)/1024) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((-111747669609375:ℝ)/262144) + ((13839609375:ℝ)/8192)*((-922669525289:ℝ)/1000000000000000) - ((-546481712166114717:ℝ)/1000000000000)) (β := ((-239203125:ℝ)/256) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((-47495864953125:ℝ)/32768) - 3*((-111747669609375:ℝ)/262144)) + ((9533953125:ℝ)/2048)*((-922669525289:ℝ)/1000000000000000) - ((-956435675908009427:ℝ)/1000000000000)) ht
  have hW : pieceW q pieceX_10 0 1 = centralNum11_01 q + 8*(Real.exp (-(3*((15:ℝ)/4)))*Real.exp (-3*t))*centralNum12_01 q + 18*Real.exp (-8*q)*centralNum13_01 q + 72*Real.exp (-11*q)*centralNum23_01 q + 8*q^7*(2*q-3)^2*((-922669525289:ℝ)/1000000000000000) + (0:ℝ) := by
    rw [pieceW_01, pieceX_10, sym4_01, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((4024315863147347292933401896018677595178311611384588410232667:ℝ)/44421097911415021843824305113571035838541229736439798361784320000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-512578125:ℝ)/1024) + ((-239203125:ℝ)/256)*t) + (8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((-111747669609375:ℝ)/262144) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((-47495864953125:ℝ)/32768) - 3*((-111747669609375:ℝ)/262144))*t) + (((13839609375:ℝ)/8192) + ((9533953125:ℝ)/2048)*t)*((-922669525289:ℝ)/1000000000000000) - (((-546481712166114717:ℝ)/1000000000000) + t * ((-956435675908009427:ℝ)/1000000000000)) = (((-512578125:ℝ)/1024) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((-111747669609375:ℝ)/262144) + ((13839609375:ℝ)/8192)*((-922669525289:ℝ)/1000000000000000) - ((-546481712166114717:ℝ)/1000000000000)) + t*(((-239203125:ℝ)/256) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((-47495864953125:ℝ)/32768) - 3*((-111747669609375:ℝ)/262144)) + ((9533953125:ℝ)/2048)*((-922669525289:ℝ)/1000000000000000) - ((-956435675908009427:ℝ)/1000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece10_e02 {q : ℝ} (h0 : ((37:ℝ)/10) ≤ q) (h1 : q ≤ ((19:ℝ)/5)) :
    |pieceW q pieceX_10 0 2 - (((121534471818195159:ℝ)/10000000000000) + (q - ((15:ℝ)/4)) * ((-989819300633604313:ℝ)/10000000000000))| ≤ ((13622364173350551:ℝ)/12500000000000) := by
  set t := q - ((15:ℝ)/4) with htd
  have hq : q = ((15:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece10_L3 piece10_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((15:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_02 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_02; ring
  have h12 : centralNum12_02 q = ∑ e ∈ Finset.range 13, ([((1824006694921875:ℝ)/8388608), ((-45234506953125:ℝ)/2097152), ((-666360686390625:ℝ)/524288), ((-318390920859375:ℝ)/131072), ((-4870303959375:ℝ)/2048), ((-6056806802625:ℝ)/4096), ((-645709716225:ℝ)/1024), ((-48671534295:ℝ)/256), ((-5211558765:ℝ)/128), ((-194646825:ℝ)/32), ((-4835565:ℝ)/8), ((-71955:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_02; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((1824006694921875:ℝ)/8388608), ((-45234506953125:ℝ)/2097152), ((-666360686390625:ℝ)/524288), ((-318390920859375:ℝ)/131072), ((-4870303959375:ℝ)/2048), ((-6056806802625:ℝ)/4096), ((-645709716225:ℝ)/1024), ((-48671534295:ℝ)/256), ((-5211558765:ℝ)/128), ((-194646825:ℝ)/32), ((-4835565:ℝ)/8), ((-71955:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((1824006694921875:ℝ)/8388608), ((-45234506953125:ℝ)/2097152), ((-666360686390625:ℝ)/524288), ((-318390920859375:ℝ)/131072), ((-4870303959375:ℝ)/2048), ((-6056806802625:ℝ)/4096), ((-645709716225:ℝ)/1024), ((-48671534295:ℝ)/256), ((-5211558765:ℝ)/128), ((-194646825:ℝ)/32), ((-4835565:ℝ)/8), ((-71955:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((1824006694921875:ℝ)/8388608), ((-45234506953125:ℝ)/2097152), ((-666360686390625:ℝ)/524288), ((-318390920859375:ℝ)/131072), ((-4870303959375:ℝ)/2048), ((-6056806802625:ℝ)/4096), ((-645709716225:ℝ)/1024), ((-48671534295:ℝ)/256), ((-5211558765:ℝ)/128), ((-194646825:ℝ)/32), ((-4835565:ℝ)/8), ((-71955:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0 * t^e) - ((1824006694921875:ℝ)/8388608) - ((-45234506953125:ℝ)/2097152)*t| ≤ ((3580346053526657837193:ℝ)/1024000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((1824006694921875:ℝ)/8388608), ((-45234506953125:ℝ)/2097152), ((-666360686390625:ℝ)/524288), ((-318390920859375:ℝ)/131072), ((-4870303959375:ℝ)/2048), ((-6056806802625:ℝ)/4096), ((-645709716225:ℝ)/1024), ((-48671534295:ℝ)/256), ((-5211558765:ℝ)/128), ((-194646825:ℝ)/32), ((-4835565:ℝ)/8), ((-71955:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((227341771384642380493443:ℝ)/1024000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((13839609375:ℝ)/8192) - ((9533953125:ℝ)/2048)*t| ≤ ((916188335461:ℝ)/62500000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((19:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82080:ℝ), (-967680:ℝ), (3257600:ℝ), (-4474880:ℝ), (2908160:ℝ), (-786432:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_02 q| ≤ ((4262277246974834534752:ℝ)/244140625) := by
    rw [centralNum13_02_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((19:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (87660:ℝ), (-702180:ℝ), ((7421435:ℝ)/4), ((-10854125:ℝ)/4), ((2828125:ℝ)/2), (-187500:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_02 q| ≤ ((2779321715958151252:ℝ)/390625) := by
    rw [centralNum23_02_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((38439959905358380531517881901:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece10_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece10_E11 h0) m23'
  have c5 := scaled_affine (X := ((-30995684307:ℝ)/5000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((1824006694921875:ℝ)/8388608) + ((13839609375:ℝ)/8192)*((-30995684307:ℝ)/5000000000000) - ((121534471818195159:ℝ)/10000000000000)) (β := (0:ℝ) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((-45234506953125:ℝ)/2097152) - 3*((1824006694921875:ℝ)/8388608)) + ((9533953125:ℝ)/2048)*((-30995684307:ℝ)/5000000000000) - ((-989819300633604313:ℝ)/10000000000000)) ht
  have hW : pieceW q pieceX_10 0 2 = centralNum11_02 q + 8*(Real.exp (-(3*((15:ℝ)/4)))*Real.exp (-3*t))*centralNum12_02 q + 18*Real.exp (-8*q)*centralNum13_02 q + 72*Real.exp (-11*q)*centralNum23_02 q + 8*q^7*(2*q-3)^2*((-30995684307:ℝ)/5000000000000) + (0:ℝ) := by
    rw [pieceW_02, pieceX_10, sym4_02, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((463185650719492738203071731467365228111691268551810412127299:ℝ)/23642088243868346586801021764547084503911103717148134870285600000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((1824006694921875:ℝ)/8388608) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((-45234506953125:ℝ)/2097152) - 3*((1824006694921875:ℝ)/8388608))*t) + (((13839609375:ℝ)/8192) + ((9533953125:ℝ)/2048)*t)*((-30995684307:ℝ)/5000000000000) - (((121534471818195159:ℝ)/10000000000000) + t * ((-989819300633604313:ℝ)/10000000000000)) = ((0:ℝ) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((1824006694921875:ℝ)/8388608) + ((13839609375:ℝ)/8192)*((-30995684307:ℝ)/5000000000000) - ((121534471818195159:ℝ)/10000000000000)) + t*((0:ℝ) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((-45234506953125:ℝ)/2097152) - 3*((1824006694921875:ℝ)/8388608)) + ((9533953125:ℝ)/2048)*((-30995684307:ℝ)/5000000000000) - ((-989819300633604313:ℝ)/10000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece10_e03 {q : ℝ} (h0 : ((37:ℝ)/10) ≤ q) (h1 : q ≤ ((19:ℝ)/5)) :
    |pieceW q pieceX_10 0 3 - (((-123568888338666059:ℝ)/1000000000000) + (q - ((15:ℝ)/4)) * ((-28102228516557029:ℝ)/50000000000))| ≤ ((111715460936349221:ℝ)/10000000000000) := by
  set t := q - ((15:ℝ)/4) with htd
  have hq : q = ((15:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece10_L3 piece10_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((15:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_03 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_03; ring
  have h12 : centralNum12_03 q = ∑ e ∈ Finset.range 14, ([((497197031741015625:ℝ)/469762048), ((116344166275546875:ℝ)/29360128), ((11514865929890625:ℝ)/1835008), ((19954028861578125:ℝ)/3670016), ((4841521325465625:ℝ)/1835008), ((110726107147125:ℝ)/229376), ((-3510192111075:ℝ)/14336), ((-1593947407455:ℝ)/7168), ((-626451887925:ℝ)/7168), ((-1200078855:ℝ)/56), ((-194397975:ℝ)/56), ((-20374335:ℝ)/56), ((-629613:ℝ)/28), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_03; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((497197031741015625:ℝ)/469762048), ((116344166275546875:ℝ)/29360128), ((11514865929890625:ℝ)/1835008), ((19954028861578125:ℝ)/3670016), ((4841521325465625:ℝ)/1835008), ((110726107147125:ℝ)/229376), ((-3510192111075:ℝ)/14336), ((-1593947407455:ℝ)/7168), ((-626451887925:ℝ)/7168), ((-1200078855:ℝ)/56), ((-194397975:ℝ)/56), ((-20374335:ℝ)/56), ((-629613:ℝ)/28), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((497197031741015625:ℝ)/469762048), ((116344166275546875:ℝ)/29360128), ((11514865929890625:ℝ)/1835008), ((19954028861578125:ℝ)/3670016), ((4841521325465625:ℝ)/1835008), ((110726107147125:ℝ)/229376), ((-3510192111075:ℝ)/14336), ((-1593947407455:ℝ)/7168), ((-626451887925:ℝ)/7168), ((-1200078855:ℝ)/56), ((-194397975:ℝ)/56), ((-20374335:ℝ)/56), ((-629613:ℝ)/28), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((497197031741015625:ℝ)/469762048), ((116344166275546875:ℝ)/29360128), ((11514865929890625:ℝ)/1835008), ((19954028861578125:ℝ)/3670016), ((4841521325465625:ℝ)/1835008), ((110726107147125:ℝ)/229376), ((-3510192111075:ℝ)/14336), ((-1593947407455:ℝ)/7168), ((-626451887925:ℝ)/7168), ((-1200078855:ℝ)/56), ((-194397975:ℝ)/56), ((-20374335:ℝ)/56), ((-629613:ℝ)/28), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((497197031741015625:ℝ)/469762048) - ((116344166275546875:ℝ)/29360128)*t| ≤ ((9395261030513398809912939:ℝ)/573440000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((497197031741015625:ℝ)/469762048), ((116344166275546875:ℝ)/29360128), ((11514865929890625:ℝ)/1835008), ((19954028861578125:ℝ)/3670016), ((4841521325465625:ℝ)/1835008), ((110726107147125:ℝ)/229376), ((-3510192111075:ℝ)/14336), ((-1593947407455:ℝ)/7168), ((-626451887925:ℝ)/7168), ((-1200078855:ℝ)/56), ((-194397975:ℝ)/56), ((-20374335:ℝ)/56), ((-629613:ℝ)/28), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((182485645323989777009607141:ℝ)/143360000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((13839609375:ℝ)/8192) - ((9533953125:ℝ)/2048)*t| ≤ ((916188335461:ℝ)/62500000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((19:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-812160:ℝ), (8985600:ℝ), (-32225280:ℝ), (52019200:ℝ), ((-305233920:ℝ)/7), ((135528448:ℝ)/7), ((-25165824:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_03 q| ≤ ((3775031646305422366704256:ℝ)/8544921875) := by
    rw [centralNum13_03_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((19:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-833220:ℝ), (6469740:ℝ), ((-68603955:ℝ)/4), ((104396875:ℝ)/4), ((-1001334375:ℝ)/56), ((125828125:ℝ)/28), ((-2343750:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_03 q| ≤ ((2503457891385345330811:ℝ)/21875000) := by
    rw [centralNum23_03_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((38439959905358380531517881901:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece10_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece10_E11 h0) m23'
  have c5 := scaled_affine (X := ((-34583834689:ℝ)/250000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((497197031741015625:ℝ)/469762048) + ((13839609375:ℝ)/8192)*((-34583834689:ℝ)/250000000000) - ((-123568888338666059:ℝ)/1000000000000)) (β := (0:ℝ) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((116344166275546875:ℝ)/29360128) - 3*((497197031741015625:ℝ)/469762048)) + ((9533953125:ℝ)/2048)*((-34583834689:ℝ)/250000000000) - ((-28102228516557029:ℝ)/50000000000)) ht
  have hW : pieceW q pieceX_10 0 3 = centralNum11_03 q + 8*(Real.exp (-(3*((15:ℝ)/4)))*Real.exp (-3*t))*centralNum12_03 q + 18*Real.exp (-8*q)*centralNum13_03 q + 72*Real.exp (-11*q)*centralNum23_03 q + 8*q^7*(2*q-3)^2*((-34583834689:ℝ)/250000000000) + (0:ℝ) := by
    rw [pieceW_03, pieceX_10, sym4_03, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((1561991951283747254648380867237619063056174616198499215576067:ℝ)/6052374590430296726221061571724053633001242551589922526793113600000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((497197031741015625:ℝ)/469762048) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((116344166275546875:ℝ)/29360128) - 3*((497197031741015625:ℝ)/469762048))*t) + (((13839609375:ℝ)/8192) + ((9533953125:ℝ)/2048)*t)*((-34583834689:ℝ)/250000000000) - (((-123568888338666059:ℝ)/1000000000000) + t * ((-28102228516557029:ℝ)/50000000000)) = ((0:ℝ) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((497197031741015625:ℝ)/469762048) + ((13839609375:ℝ)/8192)*((-34583834689:ℝ)/250000000000) - ((-123568888338666059:ℝ)/1000000000000)) + t*((0:ℝ) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((116344166275546875:ℝ)/29360128) - 3*((497197031741015625:ℝ)/469762048)) + ((9533953125:ℝ)/2048)*((-34583834689:ℝ)/250000000000) - ((-28102228516557029:ℝ)/50000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece10_e11 {q : ℝ} (h0 : ((37:ℝ)/10) ≤ q) (h1 : q ≤ ((19:ℝ)/5)) :
    |pieceW q pieceX_10 1 1 - (((93886126428934261:ℝ)/50000000000) + (q - ((15:ℝ)/4)) * ((422362164317891599:ℝ)/100000000000))| ≤ ((152605956596803991:ℝ)/10000000000000) := by
  set t := q - ((15:ℝ)/4) with htd
  have hq : q = ((15:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece10_L3 piece10_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((15:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_11 q = ∑ e ∈ Finset.range 10, ([((1811109375:ℝ)/1024), ((4298821875:ℝ)/1024), ((289321875:ℝ)/64), ((46423125:ℝ)/16), ((4890375:ℝ)/4), ((700245:ℝ)/2), (67956:ℝ), (8592:ℝ), (640:ℝ), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_11; ring
  have h12 : centralNum12_11 q = ∑ e ∈ Finset.range 13, ([((1500308619890625:ℝ)/2097152), ((773366277065625:ℝ)/524288), ((91489301803125:ℝ)/131072), ((-31848790393125:ℝ)/32768), ((-894799416375:ℝ)/512), ((-1381814075835:ℝ)/1024), ((-165716224779:ℝ)/256), ((-13485498429:ℝ)/64), ((-1525965247:ℝ)/32), ((-178409785:ℝ)/24), ((-1528911:ℝ)/2), (-46818:ℝ), (-1296:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_11; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((1811109375:ℝ)/1024), ((4298821875:ℝ)/1024), ((289321875:ℝ)/64), ((46423125:ℝ)/16), ((4890375:ℝ)/4), ((700245:ℝ)/2), (67956:ℝ), (8592:ℝ), (640:ℝ), ((64:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((1500308619890625:ℝ)/2097152), ((773366277065625:ℝ)/524288), ((91489301803125:ℝ)/131072), ((-31848790393125:ℝ)/32768), ((-894799416375:ℝ)/512), ((-1381814075835:ℝ)/1024), ((-165716224779:ℝ)/256), ((-13485498429:ℝ)/64), ((-1525965247:ℝ)/32), ((-178409785:ℝ)/24), ((-1528911:ℝ)/2), (-46818:ℝ), (-1296:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((1500308619890625:ℝ)/2097152), ((773366277065625:ℝ)/524288), ((91489301803125:ℝ)/131072), ((-31848790393125:ℝ)/32768), ((-894799416375:ℝ)/512), ((-1381814075835:ℝ)/1024), ((-165716224779:ℝ)/256), ((-13485498429:ℝ)/64), ((-1525965247:ℝ)/32), ((-178409785:ℝ)/24), ((-1528911:ℝ)/2), (-46818:ℝ), (-1296:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((1811109375:ℝ)/1024), ((4298821875:ℝ)/1024), ((289321875:ℝ)/64), ((46423125:ℝ)/16), ((4890375:ℝ)/4), ((700245:ℝ)/2), (67956:ℝ), (8592:ℝ), (640:ℝ), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((1811109375:ℝ)/1024) + ((4298821875:ℝ)/1024)*t)| ≤ ((280129634376451:ℝ)/24000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((1500308619890625:ℝ)/2097152), ((773366277065625:ℝ)/524288), ((91489301803125:ℝ)/131072), ((-31848790393125:ℝ)/32768), ((-894799416375:ℝ)/512), ((-1381814075835:ℝ)/1024), ((-165716224779:ℝ)/256), ((-13485498429:ℝ)/64), ((-1525965247:ℝ)/32), ((-178409785:ℝ)/24), ((-1528911:ℝ)/2), (-46818:ℝ), (-1296:ℝ)] : List ℝ).getD e 0 * t^e) - ((1500308619890625:ℝ)/2097152) - ((773366277065625:ℝ)/524288)*t| ≤ ((45068838297046767089:ℝ)/24000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((1500308619890625:ℝ)/2097152), ((773366277065625:ℝ)/524288), ((91489301803125:ℝ)/131072), ((-31848790393125:ℝ)/32768), ((-894799416375:ℝ)/512), ((-1381814075835:ℝ)/1024), ((-165716224779:ℝ)/256), ((-13485498429:ℝ)/64), ((-1525965247:ℝ)/32), ((-178409785:ℝ)/24), ((-1528911:ℝ)/2), (-46818:ℝ), (-1296:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((607514666925999881312473:ℝ)/768000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((13839609375:ℝ)/8192) - ((9533953125:ℝ)/2048)*t| ≤ ((916188335461:ℝ)/62500000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((19:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-3444:ℝ), (162624:ℝ), (-1531216:ℝ), (4800960:ℝ), (-6350848:ℝ), ((12025856:ℝ)/3), (-1048576:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_11 q| ≤ ((17518357083773076663628:ℝ)/732421875) := by
    rw [centralNum13_11_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((19:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-4074:ℝ), (159906:ℝ), (-1104799:ℝ), (2801499:ℝ), (-3931375:ℝ), ((5896250:ℝ)/3), (-250000:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_11 q| ≤ ((58220500614398817323:ℝ)/5859375) := by
    rw [centralNum23_11_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((38439959905358380531517881901:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece10_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece10_E11 h0) m23'
  have c5 := scaled_affine (X := ((10245427511:ℝ)/500000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1))| ≤ ((613508312853351562668032000000:ℝ)/13313334776718944356888429344771) := by
    rw [abs_neg, tailWeight_1, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((19:ℝ)/5)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((19:ℝ)/5)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece10_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((4814744136400:ℝ)/531441)) ≤ ((19:ℝ)/5)^6*(8000*(2*((19:ℝ)/5)-3)^2*(1/((25051388162973771983886131:ℝ)/250000000))*((4814744136400:ℝ)/531441)) := by
          gcongr
      _ ≤ ((613508312853351562668032000000:ℝ)/13313334776718944356888429344771) := by norm_num
  have c7 := affine_round (α := ((1811109375:ℝ)/1024) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((1500308619890625:ℝ)/2097152) + ((13839609375:ℝ)/8192)*((10245427511:ℝ)/500000000000) - ((93886126428934261:ℝ)/50000000000)) (β := ((4298821875:ℝ)/1024) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((773366277065625:ℝ)/524288) - 3*((1500308619890625:ℝ)/2097152)) + ((9533953125:ℝ)/2048)*((10245427511:ℝ)/500000000000) - ((422362164317891599:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_10 1 1 = centralNum11_11 q + 8*(Real.exp (-(3*((15:ℝ)/4)))*Real.exp (-3*t))*centralNum12_11 q + 18*Real.exp (-8*q)*centralNum13_11 q + 72*Real.exp (-11*q)*centralNum23_11 q + 8*q^7*(2*q-3)^2*((10245427511:ℝ)/500000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1)) := by
    rw [pieceW_11, pieceX_10, sym4_11, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((172813182612895727302818593681716143389380571947791591924818937:ℝ)/60523745904302967262210615717240536330012425515899225267931136000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((1811109375:ℝ)/1024) + ((4298821875:ℝ)/1024)*t) + (8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((1500308619890625:ℝ)/2097152) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((773366277065625:ℝ)/524288) - 3*((1500308619890625:ℝ)/2097152))*t) + (((13839609375:ℝ)/8192) + ((9533953125:ℝ)/2048)*t)*((10245427511:ℝ)/500000000000) - (((93886126428934261:ℝ)/50000000000) + t * ((422362164317891599:ℝ)/100000000000)) = (((1811109375:ℝ)/1024) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((1500308619890625:ℝ)/2097152) + ((13839609375:ℝ)/8192)*((10245427511:ℝ)/500000000000) - ((93886126428934261:ℝ)/50000000000)) + t*(((4298821875:ℝ)/1024) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((773366277065625:ℝ)/524288) - 3*((1500308619890625:ℝ)/2097152)) + ((9533953125:ℝ)/2048)*((10245427511:ℝ)/500000000000) - ((422362164317891599:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece10_e12 {q : ℝ} (h0 : ((37:ℝ)/10) ≤ q) (h1 : q ≤ ((19:ℝ)/5)) :
    |pieceW q pieceX_10 1 2 - (((51757047620482177:ℝ)/625000000000) + (q - ((15:ℝ)/4)) * ((43660837952370271:ℝ)/100000000000))| ≤ ((208226583249375023:ℝ)/10000000000000) := by
  set t := q - ((15:ℝ)/4) with htd
  have hq : q = ((15:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece10_L3 piece10_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((15:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_12 q = ∑ e ∈ Finset.range 9, ([((-2562890625:ℝ)/8192), ((-284765625:ℝ)/512), ((-49359375:ℝ)/128), ((-3796875:ℝ)/32), ((-84375:ℝ)/16), ((14625:ℝ)/2), (2250:ℝ), (280:ℝ), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_12; ring
  have h12 : centralNum12_12 q = ∑ e ∈ Finset.range 14, ([((99019341398671875:ℝ)/67108864), ((31690178128265625:ℝ)/4194304), ((3895418110359375:ℝ)/262144), ((8300329848759375:ℝ)/524288), ((2678738400061875:ℝ)/262144), ((130974116761575:ℝ)/32768), ((1544910768495:ℝ)/2048), ((-97632348245:ℝ)/1024), ((-334668685685:ℝ)/3072), ((-281982775:ℝ)/8), ((-52657845:ℝ)/8), ((-6045813:ℝ)/8), ((-199503:ℝ)/4), (-1458:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_12; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-2562890625:ℝ)/8192), ((-284765625:ℝ)/512), ((-49359375:ℝ)/128), ((-3796875:ℝ)/32), ((-84375:ℝ)/16), ((14625:ℝ)/2), (2250:ℝ), (280:ℝ), ((40:ℝ)/3)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((99019341398671875:ℝ)/67108864), ((31690178128265625:ℝ)/4194304), ((3895418110359375:ℝ)/262144), ((8300329848759375:ℝ)/524288), ((2678738400061875:ℝ)/262144), ((130974116761575:ℝ)/32768), ((1544910768495:ℝ)/2048), ((-97632348245:ℝ)/1024), ((-334668685685:ℝ)/3072), ((-281982775:ℝ)/8), ((-52657845:ℝ)/8), ((-6045813:ℝ)/8), ((-199503:ℝ)/4), (-1458:ℝ)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((99019341398671875:ℝ)/67108864), ((31690178128265625:ℝ)/4194304), ((3895418110359375:ℝ)/262144), ((8300329848759375:ℝ)/524288), ((2678738400061875:ℝ)/262144), ((130974116761575:ℝ)/32768), ((1544910768495:ℝ)/2048), ((-97632348245:ℝ)/1024), ((-334668685685:ℝ)/3072), ((-281982775:ℝ)/8), ((-52657845:ℝ)/8), ((-6045813:ℝ)/8), ((-199503:ℝ)/4), (-1458:ℝ)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((-2562890625:ℝ)/8192), ((-284765625:ℝ)/512), ((-49359375:ℝ)/128), ((-3796875:ℝ)/32), ((-84375:ℝ)/16), ((14625:ℝ)/2), (2250:ℝ), (280:ℝ), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((-2562890625:ℝ)/8192) + ((-284765625:ℝ)/512)*t)| ≤ ((1879520861671:ℝ)/1920000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((99019341398671875:ℝ)/67108864), ((31690178128265625:ℝ)/4194304), ((3895418110359375:ℝ)/262144), ((8300329848759375:ℝ)/524288), ((2678738400061875:ℝ)/262144), ((130974116761575:ℝ)/32768), ((1544910768495:ℝ)/2048), ((-97632348245:ℝ)/1024), ((-334668685685:ℝ)/3072), ((-281982775:ℝ)/8), ((-52657845:ℝ)/8), ((-6045813:ℝ)/8), ((-199503:ℝ)/4), (-1458:ℝ)] : List ℝ).getD e 0 * t^e) - ((99019341398671875:ℝ)/67108864) - ((31690178128265625:ℝ)/4194304)*t| ≤ ((9632239267706225992122619:ℝ)/245760000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((99019341398671875:ℝ)/67108864), ((31690178128265625:ℝ)/4194304), ((3895418110359375:ℝ)/262144), ((8300329848759375:ℝ)/524288), ((2678738400061875:ℝ)/262144), ((130974116761575:ℝ)/32768), ((1544910768495:ℝ)/2048), ((-97632348245:ℝ)/1024), ((-334668685685:ℝ)/3072), ((-281982775:ℝ)/8), ((-52657845:ℝ)/8), ((-6045813:ℝ)/8), ((-199503:ℝ)/4), (-1458:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((116273554111315327555159561:ℝ)/61440000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((13839609375:ℝ)/8192) - ((9533953125:ℝ)/2048)*t| ≤ ((916188335461:ℝ)/62500000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((19:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (122790:ℝ), (-3586680:ℝ), (28529720:ℝ), (-90761600:ℝ), (137804800:ℝ), ((-332136448:ℝ)/3), ((141819904:ℝ)/3), (-8388608:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_12 q| ≤ ((1323822481307973177334462:ℝ)/1220703125) := by
    rw [centralNum13_12_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((19:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (132555:ℝ), (-3252375:ℝ), ((39743695:ℝ)/2), ((-197111615:ℝ)/4), ((281947375:ℝ)/4), ((-1100234375:ℝ)/24), ((131828125:ℝ)/12), (-781250:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_12 q| ≤ ((903663232936068871829:ℝ)/3125000) := by
    rw [centralNum23_12_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((38439959905358380531517881901:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece10_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece10_E11 h0) m23'
  have c5 := scaled_affine (X := ((35830011351:ℝ)/250000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-2562890625:ℝ)/8192) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((99019341398671875:ℝ)/67108864) + ((13839609375:ℝ)/8192)*((35830011351:ℝ)/250000000000) - ((51757047620482177:ℝ)/625000000000)) (β := ((-284765625:ℝ)/512) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((31690178128265625:ℝ)/4194304) - 3*((99019341398671875:ℝ)/67108864)) + ((9533953125:ℝ)/2048)*((35830011351:ℝ)/250000000000) - ((43660837952370271:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_10 1 2 = centralNum11_12 q + 8*(Real.exp (-(3*((15:ℝ)/4)))*Real.exp (-3*t))*centralNum12_12 q + 18*Real.exp (-8*q)*centralNum13_12 q + 72*Real.exp (-11*q)*centralNum23_12 q + 8*q^7*(2*q-3)^2*((35830011351:ℝ)/250000000000) + (0:ℝ) := by
    rw [pieceW_12, pieceX_10, sym4_12, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((6436355039108359857093242161578267686037890962015137820948157:ℝ)/151309364760757418155526539293101340825031063789748063169827840000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-2562890625:ℝ)/8192) + ((-284765625:ℝ)/512)*t) + (8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((99019341398671875:ℝ)/67108864) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((31690178128265625:ℝ)/4194304) - 3*((99019341398671875:ℝ)/67108864))*t) + (((13839609375:ℝ)/8192) + ((9533953125:ℝ)/2048)*t)*((35830011351:ℝ)/250000000000) - (((51757047620482177:ℝ)/625000000000) + t * ((43660837952370271:ℝ)/100000000000)) = (((-2562890625:ℝ)/8192) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((99019341398671875:ℝ)/67108864) + ((13839609375:ℝ)/8192)*((35830011351:ℝ)/250000000000) - ((51757047620482177:ℝ)/625000000000)) + t*(((-284765625:ℝ)/512) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((31690178128265625:ℝ)/4194304) - 3*((99019341398671875:ℝ)/67108864)) + ((9533953125:ℝ)/2048)*((35830011351:ℝ)/250000000000) - ((43660837952370271:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece10_e13 {q : ℝ} (h0 : ((37:ℝ)/10) ≤ q) (h1 : q ≤ ((19:ℝ)/5)) :
    |pieceW q pieceX_10 1 3 - (((905627934309187969:ℝ)/1000000000000) + (q - ((15:ℝ)/4)) * ((422115795223010041:ℝ)/100000000000))| ≤ ((128330161197032867:ℝ)/1000000000000) := by
  set t := q - ((15:ℝ)/4) with htd
  have hq : q = ((15:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece10_L3 piece10_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((15:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_13 q = ∑ e ∈ Finset.range 7, ([((-170859375:ℝ)/1024), ((-34171875:ℝ)/128), ((-11390625:ℝ)/64), ((-253125:ℝ)/4), ((-50625:ℝ)/4), (-1350:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_13; ring
  have h12 : centralNum12_13 q = ∑ e ∈ Finset.range 15, ([((-21502289125593984375:ℝ)/3758096384), ((-17099674580183765625:ℝ)/939524096), ((-1324645491451359375:ℝ)/58720256), ((-340600965881821875:ℝ)/29360128), ((28004264767344375:ℝ)/14680064), ((24416356106938725:ℝ)/3670016), ((2116434960571395:ℝ)/458752), ((14459705879985:ℝ)/8192), ((22547213294775:ℝ)/57344), ((524268861345:ℝ)/14336), ((-2572422165:ℝ)/448), ((-1107207819:ℝ)/448), ((-84434967:ℝ)/224), ((-1624941:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_13; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-170859375:ℝ)/1024), ((-34171875:ℝ)/128), ((-11390625:ℝ)/64), ((-253125:ℝ)/4), ((-50625:ℝ)/4), (-1350:ℝ), (-60:ℝ)] : List ℝ).getD e 0) 5 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-21502289125593984375:ℝ)/3758096384), ((-17099674580183765625:ℝ)/939524096), ((-1324645491451359375:ℝ)/58720256), ((-340600965881821875:ℝ)/29360128), ((28004264767344375:ℝ)/14680064), ((24416356106938725:ℝ)/3670016), ((2116434960571395:ℝ)/458752), ((14459705879985:ℝ)/8192), ((22547213294775:ℝ)/57344), ((524268861345:ℝ)/14336), ((-2572422165:ℝ)/448), ((-1107207819:ℝ)/448), ((-84434967:ℝ)/224), ((-1624941:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-21502289125593984375:ℝ)/3758096384), ((-17099674580183765625:ℝ)/939524096), ((-1324645491451359375:ℝ)/58720256), ((-340600965881821875:ℝ)/29360128), ((28004264767344375:ℝ)/14680064), ((24416356106938725:ℝ)/3670016), ((2116434960571395:ℝ)/458752), ((14459705879985:ℝ)/8192), ((22547213294775:ℝ)/57344), ((524268861345:ℝ)/14336), ((-2572422165:ℝ)/448), ((-1107207819:ℝ)/448), ((-84434967:ℝ)/224), ((-1624941:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 7, ([((-170859375:ℝ)/1024), ((-34171875:ℝ)/128), ((-11390625:ℝ)/64), ((-253125:ℝ)/4), ((-50625:ℝ)/4), (-1350:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e) - (((-170859375:ℝ)/1024) + ((-34171875:ℝ)/128)*t)| ≤ ((1449395103:ℝ)/3200000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-21502289125593984375:ℝ)/3758096384), ((-17099674580183765625:ℝ)/939524096), ((-1324645491451359375:ℝ)/58720256), ((-340600965881821875:ℝ)/29360128), ((28004264767344375:ℝ)/14680064), ((24416356106938725:ℝ)/3670016), ((2116434960571395:ℝ)/458752), ((14459705879985:ℝ)/8192), ((22547213294775:ℝ)/57344), ((524268861345:ℝ)/14336), ((-2572422165:ℝ)/448), ((-1107207819:ℝ)/448), ((-84434967:ℝ)/224), ((-1624941:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((-21502289125593984375:ℝ)/3758096384) - ((-17099674580183765625:ℝ)/939524096)*t| ≤ ((41474493081652375533192711:ℝ)/716800000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-21502289125593984375:ℝ)/3758096384), ((-17099674580183765625:ℝ)/939524096), ((-1324645491451359375:ℝ)/58720256), ((-340600965881821875:ℝ)/29360128), ((28004264767344375:ℝ)/14680064), ((24416356106938725:ℝ)/3670016), ((2116434960571395:ℝ)/458752), ((14459705879985:ℝ)/8192), ((22547213294775:ℝ)/57344), ((524268861345:ℝ)/14336), ((-2572422165:ℝ)/448), ((-1107207819:ℝ)/448), ((-84434967:ℝ)/224), ((-1624941:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((38360091906614183207146401063:ℝ)/5734400000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((13839609375:ℝ)/8192) - ((9533953125:ℝ)/2048)*t| ≤ ((916188335461:ℝ)/62500000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((19:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2325540:ℝ), (52589280:ℝ), (-375655200:ℝ), (1192958720:ℝ), (-1965096960:ℝ), ((12857851904:ℝ)/7), ((-21171273728:ℝ)/21), ((914358272:ℝ)/3), ((-268435456:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_13 q| ≤ ((1302653699964058140793612636:ℝ)/42724609375) := by
    rw [centralNum13_13_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((19:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2399070:ℝ), (45666930:ℝ), (-251781675:ℝ), ((2452738385:ℝ)/4), ((-14104310625:ℝ)/16), ((74345740625:ℝ)/112), ((-74899765625:ℝ)/336), ((5161328125:ℝ)/168), ((-9765625:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_13 q| ≤ ((34448542394958925045457:ℝ)/6250000) := by
    rw [centralNum23_13_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((38439959905358380531517881901:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece10_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece10_E11 h0) m23'
  have c5 := scaled_affine (X := ((987248065489:ℝ)/1000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-170859375:ℝ)/1024) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((-21502289125593984375:ℝ)/3758096384) + ((13839609375:ℝ)/8192)*((987248065489:ℝ)/1000000000000) - ((905627934309187969:ℝ)/1000000000000)) (β := ((-34171875:ℝ)/128) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((-17099674580183765625:ℝ)/939524096) - 3*((-21502289125593984375:ℝ)/3758096384)) + ((9533953125:ℝ)/2048)*((987248065489:ℝ)/1000000000000) - ((422115795223010041:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_10 1 3 = centralNum11_13 q + 8*(Real.exp (-(3*((15:ℝ)/4)))*Real.exp (-3*t))*centralNum12_13 q + 18*Real.exp (-8*q)*centralNum13_13 q + 72*Real.exp (-11*q)*centralNum23_13 q + 8*q^7*(2*q-3)^2*((987248065489:ℝ)/1000000000000) + (0:ℝ) := by
    rw [pieceW_13, pieceX_10, sym4_13, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((40113044539150837197205008701262679502001576663928507744640383:ℝ)/121047491808605934524421231434481072660024851031798450535862272000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-170859375:ℝ)/1024) + ((-34171875:ℝ)/128)*t) + (8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((-21502289125593984375:ℝ)/3758096384) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((-17099674580183765625:ℝ)/939524096) - 3*((-21502289125593984375:ℝ)/3758096384))*t) + (((13839609375:ℝ)/8192) + ((9533953125:ℝ)/2048)*t)*((987248065489:ℝ)/1000000000000) - (((905627934309187969:ℝ)/1000000000000) + t * ((422115795223010041:ℝ)/100000000000)) = (((-170859375:ℝ)/1024) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((-21502289125593984375:ℝ)/3758096384) + ((13839609375:ℝ)/8192)*((987248065489:ℝ)/1000000000000) - ((905627934309187969:ℝ)/1000000000000)) + t*(((-34171875:ℝ)/128) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((-17099674580183765625:ℝ)/939524096) - 3*((-21502289125593984375:ℝ)/3758096384)) + ((9533953125:ℝ)/2048)*((987248065489:ℝ)/1000000000000) - ((422115795223010041:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece10_e22 {q : ℝ} (h0 : ((37:ℝ)/10) ≤ q) (h1 : q ≤ ((19:ℝ)/5)) :
    |pieceW q pieceX_10 2 2 - (((497832143112578739:ℝ)/50000000000) + (q - ((15:ℝ)/4)) * ((14906158135306309:ℝ)/500000000))| ≤ ((61320942659881339:ℝ)/200000000000) := by
  set t := q - ((15:ℝ)/4) with htd
  have hq : q = ((15:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece10_L3 piece10_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((15:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_22 q = ∑ e ∈ Finset.range 10, ([((22952109375:ℝ)/16384), ((14902734375:ℝ)/4096), ((1066921875:ℝ)/256), ((178790625:ℝ)/64), ((38975625:ℝ)/32), ((2882925:ℝ)/8), (72575:ℝ), ((28780:ℝ)/3), ((2260:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_22; ring
  have h12 : centralNum12_22 q = ∑ e ∈ Finset.range 15, ([((-23125606235265234375:ℝ)/2147483648), ((-19870795340778515625:ℝ)/536870912), ((-1714636625343046875:ℝ)/33554432), ((-569828350356046875:ℝ)/16777216), ((-53391300598715625:ℝ)/8388608), ((15375242604637125:ℝ)/2097152), ((1828558501761875:ℝ)/262144), ((297459504406925:ℝ)/98304), ((73956173979125:ℝ)/98304), ((2236913417875:ℝ)/24576), ((-1135288995:ℝ)/256), ((-930798675:ℝ)/256), ((-78312663:ℝ)/128), ((-1578285:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_22; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((22952109375:ℝ)/16384), ((14902734375:ℝ)/4096), ((1066921875:ℝ)/256), ((178790625:ℝ)/64), ((38975625:ℝ)/32), ((2882925:ℝ)/8), (72575:ℝ), ((28780:ℝ)/3), ((2260:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-23125606235265234375:ℝ)/2147483648), ((-19870795340778515625:ℝ)/536870912), ((-1714636625343046875:ℝ)/33554432), ((-569828350356046875:ℝ)/16777216), ((-53391300598715625:ℝ)/8388608), ((15375242604637125:ℝ)/2097152), ((1828558501761875:ℝ)/262144), ((297459504406925:ℝ)/98304), ((73956173979125:ℝ)/98304), ((2236913417875:ℝ)/24576), ((-1135288995:ℝ)/256), ((-930798675:ℝ)/256), ((-78312663:ℝ)/128), ((-1578285:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-23125606235265234375:ℝ)/2147483648), ((-19870795340778515625:ℝ)/536870912), ((-1714636625343046875:ℝ)/33554432), ((-569828350356046875:ℝ)/16777216), ((-53391300598715625:ℝ)/8388608), ((15375242604637125:ℝ)/2097152), ((1828558501761875:ℝ)/262144), ((297459504406925:ℝ)/98304), ((73956173979125:ℝ)/98304), ((2236913417875:ℝ)/24576), ((-1135288995:ℝ)/256), ((-930798675:ℝ)/256), ((-78312663:ℝ)/128), ((-1578285:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((22952109375:ℝ)/16384), ((14902734375:ℝ)/4096), ((1066921875:ℝ)/256), ((178790625:ℝ)/64), ((38975625:ℝ)/32), ((2882925:ℝ)/8), (72575:ℝ), ((28780:ℝ)/3), ((2260:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((22952109375:ℝ)/16384) + ((14902734375:ℝ)/4096)*t)| ≤ ((103450421352233:ℝ)/9600000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-23125606235265234375:ℝ)/2147483648), ((-19870795340778515625:ℝ)/536870912), ((-1714636625343046875:ℝ)/33554432), ((-569828350356046875:ℝ)/16777216), ((-53391300598715625:ℝ)/8388608), ((15375242604637125:ℝ)/2097152), ((1828558501761875:ℝ)/262144), ((297459504406925:ℝ)/98304), ((73956173979125:ℝ)/98304), ((2236913417875:ℝ)/24576), ((-1135288995:ℝ)/256), ((-930798675:ℝ)/256), ((-78312663:ℝ)/128), ((-1578285:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e) - ((-23125606235265234375:ℝ)/2147483648) - ((-19870795340778515625:ℝ)/536870912)*t| ≤ ((2595975027601301114868281683:ℝ)/19660800000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-23125606235265234375:ℝ)/2147483648), ((-19870795340778515625:ℝ)/536870912), ((-1714636625343046875:ℝ)/33554432), ((-569828350356046875:ℝ)/16777216), ((-53391300598715625:ℝ)/8388608), ((15375242604637125:ℝ)/2097152), ((1828558501761875:ℝ)/262144), ((297459504406925:ℝ)/98304), ((73956173979125:ℝ)/98304), ((2236913417875:ℝ)/24576), ((-1135288995:ℝ)/256), ((-930798675:ℝ)/256), ((-78312663:ℝ)/128), ((-1578285:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e)| ≤ ((250701736472495138089965937933:ℝ)/19660800000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((13839609375:ℝ)/8192) - ((9533953125:ℝ)/2048)*t| ≤ ((916188335461:ℝ)/62500000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((19:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82125:ℝ), (-6663750:ℝ), (115666200:ℝ), (-750437000:ℝ), (2277262000:ℝ), (-3656824320:ℝ), (3359621120:ℝ), (-1817706496:ℝ), ((1625292800:ℝ)/3), (-67108864:ℝ)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_22 q| ≤ ((1000650421456607504856737707:ℝ)/18310546875) := by
    rw [centralNum13_22_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((19:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((178425:ℝ)/2), ((-13176075:ℝ)/2), ((777815145:ℝ)/8), ((-3968389015:ℝ)/8), ((9393350195:ℝ)/8), ((-26366634375:ℝ)/16), ((77851609375:ℝ)/64), ((-25714921875:ℝ)/64), ((5236328125:ℝ)/96), ((-9765625:ℝ)/4)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_22 q| ≤ ((374797364256447589994627:ℝ)/37500000) := by
    rw [centralNum23_22_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((38439959905358380531517881901:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece10_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece10_E11 h0) m23'
  have c5 := scaled_affine (X := ((286382726407:ℝ)/50000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2))| ≤ ((327531579121864663910351360000000:ℝ)/119820012990470499211995864102939) := by
    rw [abs_neg, tailWeight_2, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((19:ℝ)/5)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((19:ℝ)/5)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece10_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((2570430941234500:ℝ)/4782969)) ≤ ((19:ℝ)/5)^6*(8000*(2*((19:ℝ)/5)-3)^2*(1/((25051388162973771983886131:ℝ)/250000000))*((2570430941234500:ℝ)/4782969)) := by
          gcongr
      _ ≤ ((327531579121864663910351360000000:ℝ)/119820012990470499211995864102939) := by norm_num
  have c7 := affine_round (α := ((22952109375:ℝ)/16384) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((-23125606235265234375:ℝ)/2147483648) + ((13839609375:ℝ)/8192)*((286382726407:ℝ)/50000000000) - ((497832143112578739:ℝ)/50000000000)) (β := ((14902734375:ℝ)/4096) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((-19870795340778515625:ℝ)/536870912) - 3*((-23125606235265234375:ℝ)/2147483648)) + ((9533953125:ℝ)/2048)*((286382726407:ℝ)/50000000000) - ((14906158135306309:ℝ)/500000000)) ht
  have hW : pieceW q pieceX_10 2 2 = centralNum11_22 q + 8*(Real.exp (-(3*((15:ℝ)/4)))*Real.exp (-3*t))*centralNum12_22 q + 18*Real.exp (-8*q)*centralNum13_22 q + 72*Real.exp (-11*q)*centralNum23_22 q + 8*q^7*(2*q-3)^2*((286382726407:ℝ)/50000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2)) := by
    rw [pieceW_22, pieceX_10, sym4_22, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((34481202335779999649823890873936168690841613002715558675650857:ℝ)/6052374590430296726221061571724053633001242551589922526793113600000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((22952109375:ℝ)/16384) + ((14902734375:ℝ)/4096)*t) + (8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((-23125606235265234375:ℝ)/2147483648) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((-19870795340778515625:ℝ)/536870912) - 3*((-23125606235265234375:ℝ)/2147483648))*t) + (((13839609375:ℝ)/8192) + ((9533953125:ℝ)/2048)*t)*((286382726407:ℝ)/50000000000) - (((497832143112578739:ℝ)/50000000000) + t * ((14906158135306309:ℝ)/500000000)) = (((22952109375:ℝ)/16384) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((-23125606235265234375:ℝ)/2147483648) + ((13839609375:ℝ)/8192)*((286382726407:ℝ)/50000000000) - ((497832143112578739:ℝ)/50000000000)) + t*(((14902734375:ℝ)/4096) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((-19870795340778515625:ℝ)/536870912) - 3*((-23125606235265234375:ℝ)/2147483648)) + ((9533953125:ℝ)/2048)*((286382726407:ℝ)/50000000000) - ((14906158135306309:ℝ)/500000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece10_e23 {q : ℝ} (h0 : ((37:ℝ)/10) ≤ q) (h1 : q ≤ ((19:ℝ)/5)) :
    |pieceW q pieceX_10 2 3 - (((-67147227807925983:ℝ)/20000000000) + (q - ((15:ℝ)/4)) * ((-175804712376142503:ℝ)/10000000000))| ≤ ((441150507779066629:ℝ)/100000000000) := by
  set t := q - ((15:ℝ)/4) with htd
  have hq : q = ((15:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece10_L3 piece10_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((15:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_23 q = ∑ e ∈ Finset.range 9, ([((1879453125:ℝ)/4096), ((1788328125:ℝ)/2048), ((406265625:ℝ)/512), ((58978125:ℝ)/128), ((5923125:ℝ)/32), ((406575:ℝ)/8), ((17955:ℝ)/2), (910:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_23; ring
  have h12 : centralNum12_23 q = ∑ e ∈ Finset.range 16, ([((2630447344830295546875:ℝ)/120259084288), ((745744112375174296875:ℝ)/15032385536), ((157378077819969046875:ℝ)/7516192768), ((-45481787495773284375:ℝ)/939524096), ((-37855006460168360625:ℝ)/469762048), ((-3426367363938952425:ℝ)/58720256), ((-693183708535179825:ℝ)/29360128), ((-17116195401886075:ℝ)/3670016), ((528242101660225:ℝ)/1835008), ((101835610237425:ℝ)/229376), ((14004189878625:ℝ)/114688), ((215663127291:ℝ)/14336), ((913817781:ℝ)/7168), ((-189361395:ℝ)/896), ((-1659933:ℝ)/64), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_23; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((1879453125:ℝ)/4096), ((1788328125:ℝ)/2048), ((406265625:ℝ)/512), ((58978125:ℝ)/128), ((5923125:ℝ)/32), ((406575:ℝ)/8), ((17955:ℝ)/2), (910:ℝ), (40:ℝ)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((2630447344830295546875:ℝ)/120259084288), ((745744112375174296875:ℝ)/15032385536), ((157378077819969046875:ℝ)/7516192768), ((-45481787495773284375:ℝ)/939524096), ((-37855006460168360625:ℝ)/469762048), ((-3426367363938952425:ℝ)/58720256), ((-693183708535179825:ℝ)/29360128), ((-17116195401886075:ℝ)/3670016), ((528242101660225:ℝ)/1835008), ((101835610237425:ℝ)/229376), ((14004189878625:ℝ)/114688), ((215663127291:ℝ)/14336), ((913817781:ℝ)/7168), ((-189361395:ℝ)/896), ((-1659933:ℝ)/64), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 14 ht
  have m12 := abs_poly_le (fun e => ([((2630447344830295546875:ℝ)/120259084288), ((745744112375174296875:ℝ)/15032385536), ((157378077819969046875:ℝ)/7516192768), ((-45481787495773284375:ℝ)/939524096), ((-37855006460168360625:ℝ)/469762048), ((-3426367363938952425:ℝ)/58720256), ((-693183708535179825:ℝ)/29360128), ((-17116195401886075:ℝ)/3670016), ((528242101660225:ℝ)/1835008), ((101835610237425:ℝ)/229376), ((14004189878625:ℝ)/114688), ((215663127291:ℝ)/14336), ((913817781:ℝ)/7168), ((-189361395:ℝ)/896), ((-1659933:ℝ)/64), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 16 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((1879453125:ℝ)/4096), ((1788328125:ℝ)/2048), ((406265625:ℝ)/512), ((58978125:ℝ)/128), ((5923125:ℝ)/32), ((406575:ℝ)/8), ((17955:ℝ)/2), (910:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e) - (((1879453125:ℝ)/4096) + ((1788328125:ℝ)/2048)*t)| ≤ ((1307192051481:ℝ)/640000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 16, ([((2630447344830295546875:ℝ)/120259084288), ((745744112375174296875:ℝ)/15032385536), ((157378077819969046875:ℝ)/7516192768), ((-45481787495773284375:ℝ)/939524096), ((-37855006460168360625:ℝ)/469762048), ((-3426367363938952425:ℝ)/58720256), ((-693183708535179825:ℝ)/29360128), ((-17116195401886075:ℝ)/3670016), ((528242101660225:ℝ)/1835008), ((101835610237425:ℝ)/229376), ((14004189878625:ℝ)/114688), ((215663127291:ℝ)/14336), ((913817781:ℝ)/7168), ((-189361395:ℝ)/896), ((-1659933:ℝ)/64), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e) - ((2630447344830295546875:ℝ)/120259084288) - ((745744112375174296875:ℝ)/15032385536)*t| ≤ ((216236492967843493137757543753:ℝ)/3670016000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 16, ([((2630447344830295546875:ℝ)/120259084288), ((745744112375174296875:ℝ)/15032385536), ((157378077819969046875:ℝ)/7516192768), ((-45481787495773284375:ℝ)/939524096), ((-37855006460168360625:ℝ)/469762048), ((-3426367363938952425:ℝ)/58720256), ((-693183708535179825:ℝ)/29360128), ((-17116195401886075:ℝ)/3670016), ((528242101660225:ℝ)/1835008), ((101835610237425:ℝ)/229376), ((14004189878625:ℝ)/114688), ((215663127291:ℝ)/14336), ((913817781:ℝ)/7168), ((-189361395:ℝ)/896), ((-1659933:ℝ)/64), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e)| ≤ ((44797220263396233538942535998439:ℝ)/1835008000000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((13839609375:ℝ)/8192) - ((9533953125:ℝ)/2048)*t| ≤ ((916188335461:ℝ)/62500000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((19:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-7627725:ℝ)/2), (173988600:ℝ), (-2299614450:ℝ), (13088188200:ℝ), (-38221499200:ℝ), (63366115840:ℝ), ((-445610508288:ℝ)/7), ((841540698112:ℝ)/21), ((-326820167680:ℝ)/21), ((10133438464:ℝ)/3), ((-2147483648:ℝ)/7)] : List ℝ).getD e 0) 16 hq1'
  have m13' : |centralNum13_23 q| ≤ ((2169720469407101782204617066967:ℝ)/1281738281250) := by
    rw [centralNum13_23_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((19:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-15801525:ℝ)/4), ((655493865:ℝ)/4), ((-7334421225:ℝ)/4), ((16442962485:ℝ)/2), ((-598626108395:ℝ)/32), ((414013307125:ℝ)/16), ((-4611984703125:ℝ)/224), ((399923828125:ℝ)/48), ((-4353201171875:ℝ)/2688), ((189736328125:ℝ)/1344), ((-244140625:ℝ)/56)] : List ℝ).getD e 0) 16 hq1'
  have m23' : |centralNum23_23 q| ≤ ((33121412177253401215664177:ℝ)/150000000) := by
    rw [centralNum23_23_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((38439959905358380531517881901:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece10_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece10_E11 h0) m23'
  have c5 := scaled_affine (X := ((-180308963201:ℝ)/50000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((1879453125:ℝ)/4096) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((2630447344830295546875:ℝ)/120259084288) + ((13839609375:ℝ)/8192)*((-180308963201:ℝ)/50000000000) - ((-67147227807925983:ℝ)/20000000000)) (β := ((1788328125:ℝ)/2048) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((745744112375174296875:ℝ)/15032385536) - 3*((2630447344830295546875:ℝ)/120259084288)) + ((9533953125:ℝ)/2048)*((-180308963201:ℝ)/50000000000) - ((-175804712376142503:ℝ)/10000000000)) ht
  have hW : pieceW q pieceX_10 2 3 = centralNum11_23 q + 8*(Real.exp (-(3*((15:ℝ)/4)))*Real.exp (-3*t))*centralNum12_23 q + 18*Real.exp (-8*q)*centralNum13_23 q + 72*Real.exp (-11*q)*centralNum23_23 q + 8*q^7*(2*q-3)^2*((-180308963201:ℝ)/50000000000) + (0:ℝ) := by
    rw [pieceW_23, pieceX_10, sym4_23, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((250671402213048351698161367126587229207138945825739638308827:ℝ)/47284176487736693173602043529094169007822207434296269740571200000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((1879453125:ℝ)/4096) + ((1788328125:ℝ)/2048)*t) + (8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((2630447344830295546875:ℝ)/120259084288) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((745744112375174296875:ℝ)/15032385536) - 3*((2630447344830295546875:ℝ)/120259084288))*t) + (((13839609375:ℝ)/8192) + ((9533953125:ℝ)/2048)*t)*((-180308963201:ℝ)/50000000000) - (((-67147227807925983:ℝ)/20000000000) + t * ((-175804712376142503:ℝ)/10000000000)) = (((1879453125:ℝ)/4096) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((2630447344830295546875:ℝ)/120259084288) + ((13839609375:ℝ)/8192)*((-180308963201:ℝ)/50000000000) - ((-67147227807925983:ℝ)/20000000000)) + t*(((1788328125:ℝ)/2048) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((745744112375174296875:ℝ)/15032385536) - 3*((2630447344830295546875:ℝ)/120259084288)) + ((9533953125:ℝ)/2048)*((-180308963201:ℝ)/50000000000) - ((-175804712376142503:ℝ)/10000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece10_e33 {q : ℝ} (h0 : ((37:ℝ)/10) ≤ q) (h1 : q ≤ ((19:ℝ)/5)) :
    |pieceW q pieceX_10 3 3 - (((167338186373161907:ℝ)/500000000) + (q - ((15:ℝ)/4)) * ((23540592448596987:ℝ)/25000000))| ≤ ((29445423716394271:ℝ)/200000000) := by
  set t := q - ((15:ℝ)/4) with htd
  have hq : q = ((15:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece10_L3 piece10_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((15:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_33 q = ∑ e ∈ Finset.range 10, ([((8121515625:ℝ)/57344), ((6434184375:ℝ)/7168), ((5493774375:ℝ)/3584), ((166026375:ℝ)/128), ((21003075:ℝ)/32), ((1723455:ℝ)/8), ((94395:ℝ)/2), ((47430:ℝ)/7), ((4080:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_33; ring
  have h12 : centralNum12_33 q = ∑ e ∈ Finset.range 17, ([((-204632514522209087859375:ℝ)/6734508720128), ((11303168539281959503125:ℝ)/1683627180032), ((87793120572282397614375:ℝ)/420906795008), ((5737188031795358913375:ℝ)/15032385536), ((1236202806302017724025:ℝ)/3758096384), ((140577691032050221575:ℝ)/939524096), ((5572897543142863725:ℝ)/234881024), ((-4883463807981532875:ℝ)/411041792), ((-865961496527023875:ℝ)/102760448), ((-58831140385831825:ℝ)/25690112), ((-219987683878509:ℝ)/917504), ((6926348547981:ℝ)/229376), ((722321745939:ℝ)/57344), ((19716012765:ℝ)/14336), ((-8444007:ℝ)/25088), ((-71862633:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_33; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((8121515625:ℝ)/57344), ((6434184375:ℝ)/7168), ((5493774375:ℝ)/3584), ((166026375:ℝ)/128), ((21003075:ℝ)/32), ((1723455:ℝ)/8), ((94395:ℝ)/2), ((47430:ℝ)/7), ((4080:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-204632514522209087859375:ℝ)/6734508720128), ((11303168539281959503125:ℝ)/1683627180032), ((87793120572282397614375:ℝ)/420906795008), ((5737188031795358913375:ℝ)/15032385536), ((1236202806302017724025:ℝ)/3758096384), ((140577691032050221575:ℝ)/939524096), ((5572897543142863725:ℝ)/234881024), ((-4883463807981532875:ℝ)/411041792), ((-865961496527023875:ℝ)/102760448), ((-58831140385831825:ℝ)/25690112), ((-219987683878509:ℝ)/917504), ((6926348547981:ℝ)/229376), ((722321745939:ℝ)/57344), ((19716012765:ℝ)/14336), ((-8444007:ℝ)/25088), ((-71862633:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 15 ht
  have m12 := abs_poly_le (fun e => ([((-204632514522209087859375:ℝ)/6734508720128), ((11303168539281959503125:ℝ)/1683627180032), ((87793120572282397614375:ℝ)/420906795008), ((5737188031795358913375:ℝ)/15032385536), ((1236202806302017724025:ℝ)/3758096384), ((140577691032050221575:ℝ)/939524096), ((5572897543142863725:ℝ)/234881024), ((-4883463807981532875:ℝ)/411041792), ((-865961496527023875:ℝ)/102760448), ((-58831140385831825:ℝ)/25690112), ((-219987683878509:ℝ)/917504), ((6926348547981:ℝ)/229376), ((722321745939:ℝ)/57344), ((19716012765:ℝ)/14336), ((-8444007:ℝ)/25088), ((-71862633:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 17 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((8121515625:ℝ)/57344), ((6434184375:ℝ)/7168), ((5493774375:ℝ)/3584), ((166026375:ℝ)/128), ((21003075:ℝ)/32), ((1723455:ℝ)/8), ((94395:ℝ)/2), ((47430:ℝ)/7), ((4080:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e) - (((8121515625:ℝ)/57344) + ((6434184375:ℝ)/7168)*t)| ≤ ((12795066382423:ℝ)/3200000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 17, ([((-204632514522209087859375:ℝ)/6734508720128), ((11303168539281959503125:ℝ)/1683627180032), ((87793120572282397614375:ℝ)/420906795008), ((5737188031795358913375:ℝ)/15032385536), ((1236202806302017724025:ℝ)/3758096384), ((140577691032050221575:ℝ)/939524096), ((5572897543142863725:ℝ)/234881024), ((-4883463807981532875:ℝ)/411041792), ((-865961496527023875:ℝ)/102760448), ((-58831140385831825:ℝ)/25690112), ((-219987683878509:ℝ)/917504), ((6926348547981:ℝ)/229376), ((722321745939:ℝ)/57344), ((19716012765:ℝ)/14336), ((-8444007:ℝ)/25088), ((-71862633:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e) - ((-204632514522209087859375:ℝ)/6734508720128) - ((11303168539281959503125:ℝ)/1683627180032)*t| ≤ ((41930828416485466448531111761873:ℝ)/73400320000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 17, ([((-204632514522209087859375:ℝ)/6734508720128), ((11303168539281959503125:ℝ)/1683627180032), ((87793120572282397614375:ℝ)/420906795008), ((5737188031795358913375:ℝ)/15032385536), ((1236202806302017724025:ℝ)/3758096384), ((140577691032050221575:ℝ)/939524096), ((5572897543142863725:ℝ)/234881024), ((-4883463807981532875:ℝ)/411041792), ((-865961496527023875:ℝ)/102760448), ((-58831140385831825:ℝ)/25690112), ((-219987683878509:ℝ)/917504), ((6926348547981:ℝ)/229376), ((722321745939:ℝ)/57344), ((19716012765:ℝ)/14336), ((-8444007:ℝ)/25088), ((-71862633:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e)| ≤ ((16078210335510970146243233407333111:ℝ)/513802240000000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((13839609375:ℝ)/8192), ((9533953125:ℝ)/2048), ((362221875:ℝ)/64), ((15946875:ℝ)/4), ((28704375:ℝ)/16), ((2140425:ℝ)/4), (105840:ℝ), (13392:ℝ), (984:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((13839609375:ℝ)/8192) - ((9533953125:ℝ)/2048)*t| ≤ ((916188335461:ℝ)/62500000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((19:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-8120475:ℝ)/4), ((464861025:ℝ)/2), (-5906535975:ℝ), ((411904731750:ℝ)/7), ((-2024051769000:ℝ)/7), ((5554394637600:ℝ)/7), (-1314913862656:ℝ), ((9709155336192:ℝ)/7), ((-6724555112448:ℝ)/7), ((1313173667840:ℝ)/3), ((-6168244125696:ℝ)/49), ((3004329623552:ℝ)/147), ((-68719476736:ℝ)/49)] : List ℝ).getD e 0) 17 hq1'
  have m13' : |centralNum13_33 q| ≤ ((735263111809856534126735952832961:ℝ)/12817382812500) := by
    rw [centralNum13_33_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((19:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-16872075:ℝ)/8), ((1833754545:ℝ)/8), ((-83998007145:ℝ)/16), ((4929124002765:ℝ)/112), ((-76723155584685:ℝ)/448), ((164888745653055:ℝ)/448), ((-63358359907625:ℝ)/128), ((364713160040625:ℝ)/896), ((-334937462578125:ℝ)/1792), ((245466998046875:ℝ)/5376), ((-72144521484375:ℝ)/12544), ((6518798828125:ℝ)/18816), ((-6103515625:ℝ)/784)] : List ℝ).getD e 0) 17 hq1'
  have m23' : |centralNum23_33 q| ≤ ((11671835092137813231638235533:ℝ)/2100000000) := by
    rw [centralNum23_33_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((38439959905358380531517881901:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece10_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece10_E11 h0) m23'
  have c5 := scaled_affine (X := ((199890813323:ℝ)/1000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3))| ≤ ((421587576257926954397659358720000000:ℝ)/3235140350742703478723888330779353) := by
    rw [abs_neg, tailWeight_3, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((19:ℝ)/5)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((19:ℝ)/5)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece10_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((3308571812705231500:ℝ)/129140163)) ≤ ((19:ℝ)/5)^6*(8000*(2*((19:ℝ)/5)-3)^2*(1/((25051388162973771983886131:ℝ)/250000000))*((3308571812705231500:ℝ)/129140163)) := by
          gcongr
      _ ≤ ((421587576257926954397659358720000000:ℝ)/3235140350742703478723888330779353) := by norm_num
  have c7 := affine_round (α := ((8121515625:ℝ)/57344) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((-204632514522209087859375:ℝ)/6734508720128) + ((13839609375:ℝ)/8192)*((199890813323:ℝ)/1000000000) - ((167338186373161907:ℝ)/500000000)) (β := ((6434184375:ℝ)/7168) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((11303168539281959503125:ℝ)/1683627180032) - 3*((-204632514522209087859375:ℝ)/6734508720128)) + ((9533953125:ℝ)/2048)*((199890813323:ℝ)/1000000000) - ((23540592448596987:ℝ)/25000000)) ht
  have hW : pieceW q pieceX_10 3 3 = centralNum11_33 q + 8*(Real.exp (-(3*((15:ℝ)/4)))*Real.exp (-3*t))*centralNum12_33 q + 18*Real.exp (-8*q)*centralNum13_33 q + 72*Real.exp (-11*q)*centralNum23_33 q + 8*q^7*(2*q-3)^2*((199890813323:ℝ)/1000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3)) := by
    rw [pieceW_33, pieceX_10, sym4_33, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((18801942824371822232500674659928308133343745658447790722100697:ℝ)/169466488532048308334189724008273501724034791444517830750207180800000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((8121515625:ℝ)/57344) + ((6434184375:ℝ)/7168)*t) + (8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((-204632514522209087859375:ℝ)/6734508720128) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((11303168539281959503125:ℝ)/1683627180032) - 3*((-204632514522209087859375:ℝ)/6734508720128))*t) + (((13839609375:ℝ)/8192) + ((9533953125:ℝ)/2048)*t)*((199890813323:ℝ)/1000000000) - (((167338186373161907:ℝ)/500000000) + t * ((23540592448596987:ℝ)/25000000)) = (((8121515625:ℝ)/57344) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*((-204632514522209087859375:ℝ)/6734508720128) + ((13839609375:ℝ)/8192)*((199890813323:ℝ)/1000000000) - ((167338186373161907:ℝ)/500000000)) + t*(((6434184375:ℝ)/7168) + 8*(((1/((38439959905358380531517881901:ℝ)/500000000000000000000000))+(1/((768799196918931088273177269557:ℝ)/10000000000000000000000000)))/2)*(((11303168539281959503125:ℝ)/1683627180032) - 3*((-204632514522209087859375:ℝ)/6734508720128)) + ((9533953125:ℝ)/2048)*((199890813323:ℝ)/1000000000) - ((23540592448596987:ℝ)/25000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece10_plus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((54798896558359531:ℝ)/25000000000) + ((1:ℝ)/20)*((70549480059238571:ℝ)/12500000000) - (((44273611092566819:ℝ)/2500000000000) + ((493633251905758273:ℝ)/100000000000000) + ((13622364173350551:ℝ)/12500000000000) + ((111715460936349221:ℝ)/10000000000000)))
      (((-546481712166114717:ℝ)/1000000000000) + ((1:ℝ)/20)*((-956435675908009427:ℝ)/1000000000000))
      (((121534471818195159:ℝ)/10000000000000) + ((1:ℝ)/20)*((-989819300633604313:ℝ)/10000000000000))
      (((-123568888338666059:ℝ)/1000000000000) + ((1:ℝ)/20)*((-28102228516557029:ℝ)/50000000000))
      (((93886126428934261:ℝ)/50000000000) + ((1:ℝ)/20)*((422362164317891599:ℝ)/100000000000) - (((493633251905758273:ℝ)/100000000000000) + ((152605956596803991:ℝ)/10000000000000) + ((208226583249375023:ℝ)/10000000000000) + ((128330161197032867:ℝ)/1000000000000)))
      (((51757047620482177:ℝ)/625000000000) + ((1:ℝ)/20)*((43660837952370271:ℝ)/100000000000))
      (((905627934309187969:ℝ)/1000000000000) + ((1:ℝ)/20)*((422115795223010041:ℝ)/100000000000))
      (((497832143112578739:ℝ)/50000000000) + ((1:ℝ)/20)*((14906158135306309:ℝ)/500000000) - (((13622364173350551:ℝ)/12500000000000) + ((208226583249375023:ℝ)/10000000000000) + ((61320942659881339:ℝ)/200000000000) + ((441150507779066629:ℝ)/100000000000)))
      (((-67147227807925983:ℝ)/20000000000) + ((1:ℝ)/20)*((-175804712376142503:ℝ)/10000000000))
      (((167338186373161907:ℝ)/500000000) + ((1:ℝ)/20)*((23540592448596987:ℝ)/25000000) - (((111715460936349221:ℝ)/10000000000000) + ((128330161197032867:ℝ)/1000000000000) + ((441150507779066629:ℝ)/100000000000) + ((29445423716394271:ℝ)/200000000))) i j :=
  quadForm_nonneg_of_ldl ((243924667038774824749:ℝ)/100000000000000) ((5411335904663343315544718822244232473961:ℝ)/3049058337984685309362500000000000) ((116033529289952589831345726159674971230992852831733937418845531:ℝ)/17316274894922698609743100231181543916675200000000000000) ((262877322091732484434310197755890632551773036393855868787802610831901089581505575229:ℝ)/1160335292899525898313457261596749712309928528317339374188455310000000000000) ((-59430349596151518835:ℝ)/243924667038774824749) ((1440870135730298867:ℝ)/487849334077549649498) ((-15167111685522308800:ℝ)/243924667038774824749) ((5190569546381249020491334001545752901205:ℝ)/86581374474613493048715501155907719583376) ((13168667611991382401804920626026826732775:ℝ)/21645343618653373262178875288976929895844) ((-74471534509813290630749270692688804588483122460173664581487100:ℝ)/116033529289952589831345726159674971230992852831733937418845531)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece10_minus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((54798896558359531:ℝ)/25000000000) - ((1:ℝ)/20)*((70549480059238571:ℝ)/12500000000) - (((44273611092566819:ℝ)/2500000000000) + ((493633251905758273:ℝ)/100000000000000) + ((13622364173350551:ℝ)/12500000000000) + ((111715460936349221:ℝ)/10000000000000)))
      (((-546481712166114717:ℝ)/1000000000000) - ((1:ℝ)/20)*((-956435675908009427:ℝ)/1000000000000))
      (((121534471818195159:ℝ)/10000000000000) - ((1:ℝ)/20)*((-989819300633604313:ℝ)/10000000000000))
      (((-123568888338666059:ℝ)/1000000000000) - ((1:ℝ)/20)*((-28102228516557029:ℝ)/50000000000))
      (((93886126428934261:ℝ)/50000000000) - ((1:ℝ)/20)*((422362164317891599:ℝ)/100000000000) - (((493633251905758273:ℝ)/100000000000000) + ((152605956596803991:ℝ)/10000000000000) + ((208226583249375023:ℝ)/10000000000000) + ((128330161197032867:ℝ)/1000000000000)))
      (((51757047620482177:ℝ)/625000000000) - ((1:ℝ)/20)*((43660837952370271:ℝ)/100000000000))
      (((905627934309187969:ℝ)/1000000000000) - ((1:ℝ)/20)*((422115795223010041:ℝ)/100000000000))
      (((497832143112578739:ℝ)/50000000000) - ((1:ℝ)/20)*((14906158135306309:ℝ)/500000000) - (((13622364173350551:ℝ)/12500000000000) + ((208226583249375023:ℝ)/10000000000000) + ((61320942659881339:ℝ)/200000000000) + ((441150507779066629:ℝ)/100000000000)))
      (((-67147227807925983:ℝ)/20000000000) - ((1:ℝ)/20)*((-175804712376142503:ℝ)/10000000000))
      (((167338186373161907:ℝ)/500000000) - ((1:ℝ)/20)*((23540592448596987:ℝ)/25000000) - (((111715460936349221:ℝ)/10000000000000) + ((128330161197032867:ℝ)/1000000000000) + ((441150507779066629:ℝ)/100000000000) + ((29445423716394271:ℝ)/200000000))) i j :=
  quadForm_nonneg_of_ldl ((187485082991383967949:ℝ)/100000000000000) ((6395873436802002395878383313496460530747:ℝ)/4687127074784599198725000000000000) ((38095888310355580229779440806434661023486938289725719202918711:ℝ)/10233397498883203833405413301594336849195200000000000000) ((50969337449447086166170398403606058055520072618341379280731126241766538584817027849:ℝ)/380958883103555802297794408064346610234869382897257192029187110000000000000) ((-49865992837071424565:ℝ)/187485082991383967949) ((3420508736997507493:ℝ)/374970165982767935898) ((-3182221994070301000:ℝ)/62495027663794655983) ((2457167279405743404866569869901325739005:ℝ)/51166987494416019167027066507971684245976) ((6273049059936263628024646389671874783825:ℝ)/12791746873604004791756766626992921061494) ((-25681761021742288275990146185156319202858864076696351929354500:ℝ)/38095888310355580229779440806434661023486938289725719202918711)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

/-- **Piece 10.** The piece matrix is positive semidefinite on `q ∈ [37/10, 19/5]`. -/
theorem piece_10 {q : ℝ} (h0 : ((37:ℝ)/10) ≤ q) (h1 : q ≤ ((19:ℝ)/5)) (y : Fin 4 → ℝ) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceW q pieceX_10 i j :=
  pieceForm_nonneg (pieceW_symm (sym4_symm _ _ _ _ _ _ _ _ _ _) q) (by norm_num : (0:ℝ) < ((1:ℝ)/20))
    (abs_le.mpr ⟨by linarith, by linarith⟩)
    (piece10_e00 h0 h1) (piece10_e01 h0 h1) (piece10_e02 h0 h1) (piece10_e03 h0 h1) (piece10_e11 h0 h1) (piece10_e12 h0 h1) (piece10_e13 h0 h1) (piece10_e22 h0 h1) (piece10_e23 h0 h1) (piece10_e33 h0 h1)
    piece10_plus piece10_minus y

/-! #### Piece 11 (seam), `q ∈ [19/5, 39/10]` -/

/-- The compensation matrix of piece 11. -/
def pieceX_11 : Fin 4 → Fin 4 → ℝ :=
  sym4 ((27843177323:ℝ)/2500000000000) ((-19650599607:ℝ)/31250000000000) ((774437674717:ℝ)/100000000000000) ((-108489430133:ℝ)/1000000000000) ((221557230021:ℝ)/10000000000000) ((848698446263:ℝ)/10000000000000) ((96829622447:ℝ)/125000000000) ((117640627701:ℝ)/50000000000) ((-66231917669:ℝ)/25000000000) ((971775550441:ℝ)/10000000000)

theorem piece11_L3 : ((103777023515170732568717557253:ℝ)/1000000000000000000000000) ≤ Real.exp ((3:ℝ)*((77:ℝ)/20)) := by
  have h := le_exp_nat_add 11 (f := ((11:ℝ)/20)) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((77:ℝ)/20) = ((11:ℕ):ℝ) + ((11:ℝ)/20) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece11_U3 : Real.exp ((3:ℝ)*((77:ℝ)/20)) ≤ ((103777037629710019882577736861:ℝ)/1000000000000000000000000) := by
  have h := exp_nat_add_le 11 (f := ((11:ℝ)/20)) (by norm_num) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((77:ℝ)/20) = ((11:ℕ):ℝ) + ((11:ℝ)/20) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem piece11_L8_at : ((79711732508562897109392033677:ℝ)/5000000000000000) ≤ Real.exp ((8:ℝ)*((19:ℝ)/5)) := by
  have h := le_exp_nat_add 30 (f := ((2:ℝ)/5)) (by norm_num)
  rw [show ((8:ℝ):ℝ)*((19:ℝ)/5) = ((30:ℕ):ℝ) + ((2:ℝ)/5) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece11_E8 {q : ℝ} (h0 : ((19:ℝ)/5) ≤ q) : Real.exp (-((8:ℝ))*q) ≤ 1/((79711732508562897109392033677:ℝ)/5000000000000000) := by
  have hm : Real.exp (-((8:ℝ))*q) ≤ Real.exp (-((8:ℝ)*((19:ℝ)/5))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece11_L8_at (le_refl _)).2

theorem piece11_L11_at : ((142399495980080563235442634613:ℝ)/100000000000) ≤ Real.exp ((11:ℝ)*((19:ℝ)/5)) := by
  have h := le_exp_nat_add 41 (f := ((4:ℝ)/5)) (by norm_num)
  rw [show ((11:ℝ):ℝ)*((19:ℝ)/5) = ((41:ℕ):ℝ) + ((4:ℝ)/5) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece11_E11 {q : ℝ} (h0 : ((19:ℝ)/5) ≤ q) : Real.exp (-((11:ℝ))*q) ≤ 1/((142399495980080563235442634613:ℝ)/100000000000) := by
  have hm : Real.exp (-((11:ℝ))*q) ≤ Real.exp (-((11:ℝ)*((19:ℝ)/5))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece11_L11_at (le_refl _)).2

theorem piece11_Lt_at : ((288652517379563037996819230889:ℝ)/1000000000000) ≤ Real.exp (((529:ℝ)/50)*((19:ℝ)/5)) := by
  have h := le_exp_nat_add 40 (f := ((51:ℝ)/250)) (by norm_num)
  rw [show (((529:ℝ)/50):ℝ)*((19:ℝ)/5) = ((40:ℕ):ℝ) + ((51:ℝ)/250) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece11_Et {q : ℝ} (h0 : ((19:ℝ)/5) ≤ q) : Real.exp (-(((529:ℝ)/50))*q) ≤ 1/((288652517379563037996819230889:ℝ)/1000000000000) := by
  have hm : Real.exp (-(((529:ℝ)/50))*q) ≤ Real.exp (-(((529:ℝ)/50)*((19:ℝ)/5))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece11_Lt_at (le_refl _)).2

theorem piece11_e00 {q : ℝ} (h0 : ((19:ℝ)/5) ≤ q) (h1 : q ≤ ((39:ℝ)/10)) :
    |pieceW q pieceX_11 0 0 - (((282572660038003097:ℝ)/100000000000) + (q - ((77:ℝ)/20)) * ((353907386706293197:ℝ)/50000000000))| ≤ ((53365846744793379:ℝ)/2500000000000) := by
  set t := q - ((77:ℝ)/20) with htd
  have hq : q = ((77:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece11_L3 piece11_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((77:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_00 q = ∑ e ∈ Finset.range 10, ([((45080301856590077:ℝ)/16000000000), ((5606770446774189:ℝ)/800000000), ((2444226093771:ℝ)/312500), ((1282277476557:ℝ)/250000), ((108690007041:ℝ)/50000), ((1541047893:ℝ)/2500), ((14598276:ℝ)/125), ((355968:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_00; ring
  have h12 : centralNum12_00 q = ∑ e ∈ Finset.range 11, ([((-68364606760245822257:ℝ)/320000000000), ((-1892527942070282517:ℝ)/3200000000), ((-59007198979071651:ℝ)/80000000), ((-1091138405453019:ℝ)/2000000), ((-52992432744867:ℝ)/200000), ((-4413176557251:ℝ)/50000), ((-2552419947:ℝ)/125), ((-80971398:ℝ)/25), ((-1685226:ℝ)/5), (-20776:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_00; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((45080301856590077:ℝ)/16000000000), ((5606770446774189:ℝ)/800000000), ((2444226093771:ℝ)/312500), ((1282277476557:ℝ)/250000), ((108690007041:ℝ)/50000), ((1541047893:ℝ)/2500), ((14598276:ℝ)/125), ((355968:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-68364606760245822257:ℝ)/320000000000), ((-1892527942070282517:ℝ)/3200000000), ((-59007198979071651:ℝ)/80000000), ((-1091138405453019:ℝ)/2000000), ((-52992432744867:ℝ)/200000), ((-4413176557251:ℝ)/50000), ((-2552419947:ℝ)/125), ((-80971398:ℝ)/25), ((-1685226:ℝ)/5), (-20776:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 9 ht
  have m12 := abs_poly_le (fun e => ([((-68364606760245822257:ℝ)/320000000000), ((-1892527942070282517:ℝ)/3200000000), ((-59007198979071651:ℝ)/80000000), ((-1091138405453019:ℝ)/2000000), ((-52992432744867:ℝ)/200000), ((-4413176557251:ℝ)/50000), ((-2552419947:ℝ)/125), ((-80971398:ℝ)/25), ((-1685226:ℝ)/5), (-20776:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 11 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((45080301856590077:ℝ)/16000000000), ((5606770446774189:ℝ)/800000000), ((2444226093771:ℝ)/312500), ((1282277476557:ℝ)/250000), ((108690007041:ℝ)/50000), ((1541047893:ℝ)/2500), ((14598276:ℝ)/125), ((355968:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - (((45080301856590077:ℝ)/16000000000) + ((5606770446774189:ℝ)/800000000)*t)| ≤ ((161669825650091:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 11, ([((-68364606760245822257:ℝ)/320000000000), ((-1892527942070282517:ℝ)/3200000000), ((-59007198979071651:ℝ)/80000000), ((-1091138405453019:ℝ)/2000000), ((-52992432744867:ℝ)/200000), ((-4413176557251:ℝ)/50000), ((-2552419947:ℝ)/125), ((-80971398:ℝ)/25), ((-1685226:ℝ)/5), (-20776:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e) - ((-68364606760245822257:ℝ)/320000000000) - ((-1892527942070282517:ℝ)/3200000000)*t| ≤ ((61243361149107799:ℝ)/32000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 11, ([((-68364606760245822257:ℝ)/320000000000), ((-1892527942070282517:ℝ)/3200000000), ((-59007198979071651:ℝ)/80000000), ((-1091138405453019:ℝ)/2000000), ((-52992432744867:ℝ)/200000), ((-4413176557251:ℝ)/50000), ((-2552419947:ℝ)/125), ((-80971398:ℝ)/25), ((-1685226:ℝ)/5), (-20776:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((4787578130010273:ℝ)/19531250) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((35451187896478277:ℝ)/16000000000) - ((4731396450400389:ℝ)/800000000)*t| ≤ ((144243147419291:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((39:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (600:ℝ), (-7776:ℝ), (16800:ℝ), (-9216:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m13' : |centralNum13_00 q| ≤ ((893221938755896347:ℝ)/78125000) := by
    rw [centralNum13_00_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((39:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (780:ℝ), (-6156:ℝ), (15288:ℝ), (-14400:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m23' : |centralNum23_00 q| ≤ ((953337353541699087:ℝ)/62500000) := by
    rw [centralNum23_00_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece11_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece11_E11 h0) m23'
  have c5 := scaled_affine (X := ((27843177323:ℝ)/2500000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0))| ≤ ((79580502896287744000000000:ℝ)/199836358185851333997797929077) := by
    rw [abs_neg, tailWeight_0, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((39:ℝ)/10)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((39:ℝ)/10)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece11_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((10465499600:ℝ)/59049)) ≤ ((39:ℝ)/10)^6*(8000*(2*((39:ℝ)/10)-3)^2*(1/((288652517379563037996819230889:ℝ)/1000000000000))*((10465499600:ℝ)/59049)) := by
          gcongr
      _ ≤ ((79580502896287744000000000:ℝ)/199836358185851333997797929077) := by norm_num
  have c7 := affine_round (α := ((45080301856590077:ℝ)/16000000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((-68364606760245822257:ℝ)/320000000000) + ((35451187896478277:ℝ)/16000000000)*((27843177323:ℝ)/2500000000000) - ((282572660038003097:ℝ)/100000000000)) (β := ((5606770446774189:ℝ)/800000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((-1892527942070282517:ℝ)/3200000000) - 3*((-68364606760245822257:ℝ)/320000000000)) + ((4731396450400389:ℝ)/800000000)*((27843177323:ℝ)/2500000000000) - ((353907386706293197:ℝ)/50000000000)) ht
  have hW : pieceW q pieceX_11 0 0 = centralNum11_00 q + 8*(Real.exp (-(3*((77:ℝ)/20)))*Real.exp (-3*t))*centralNum12_00 q + 18*Real.exp (-8*q)*centralNum13_00 q + 72*Real.exp (-11*q)*centralNum23_00 q + 8*q^7*(2*q-3)^2*((27843177323:ℝ)/2500000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0)) := by
    rw [pieceW_00, pieceX_11, sym4_00, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((777944501695093599864564583676107078245678218477397489622073236823:ℝ)/611913186047339472511011723174739499712637764344825909251875000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((45080301856590077:ℝ)/16000000000) + ((5606770446774189:ℝ)/800000000)*t) + (8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((-68364606760245822257:ℝ)/320000000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((-1892527942070282517:ℝ)/3200000000) - 3*((-68364606760245822257:ℝ)/320000000000))*t) + (((35451187896478277:ℝ)/16000000000) + ((4731396450400389:ℝ)/800000000)*t)*((27843177323:ℝ)/2500000000000) - (((282572660038003097:ℝ)/100000000000) + t * ((353907386706293197:ℝ)/50000000000)) = (((45080301856590077:ℝ)/16000000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((-68364606760245822257:ℝ)/320000000000) + ((35451187896478277:ℝ)/16000000000)*((27843177323:ℝ)/2500000000000) - ((282572660038003097:ℝ)/100000000000)) + t*(((5606770446774189:ℝ)/800000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((-1892527942070282517:ℝ)/3200000000) - 3*((-68364606760245822257:ℝ)/320000000000)) + ((4731396450400389:ℝ)/800000000)*((27843177323:ℝ)/2500000000000) - ((353907386706293197:ℝ)/50000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece11_e01 {q : ℝ} (h0 : ((19:ℝ)/5) ≤ q) (h1 : q ≤ ((39:ℝ)/10)) :
    |pieceW q pieceX_11 0 1 - (((-649133701077751467:ℝ)/1000000000000) + (q - ((77:ℝ)/20)) * ((-111140719468876623:ℝ)/100000000000))| ≤ ((521871343467821597:ℝ)/100000000000000) := by
  set t := q - ((77:ℝ)/20) with htd
  have hq : q = ((77:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece11_L3 piece11_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((77:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_01 q = ∑ e ∈ Finset.range 8, ([((-48145569800559:ℝ)/80000000), ((-4376869981869:ℝ)/4000000), ((-170527401891:ℝ)/200000), ((-738213861:ℝ)/2000), ((-9587193:ℝ)/100), ((-373527:ℝ)/25), ((-6468:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_01; ring
  have h12 : centralNum12_01 q = ∑ e ∈ Finset.range 12, ([((-7624839550903232527947:ℝ)/12800000000000), ((-627780969905133709203:ℝ)/320000000000), ((-18706986099850342833:ℝ)/6400000000), ((-416485814269154091:ℝ)/160000000), ((-12323451770696451:ℝ)/8000000), ((-636309806995863:ℝ)/1000000), ((-18725878756893:ℝ)/100000), ((-19633730091:ℝ)/500), ((-575056251:ℝ)/100), ((-2800806:ℝ)/5), ((-163332:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_01; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-48145569800559:ℝ)/80000000), ((-4376869981869:ℝ)/4000000), ((-170527401891:ℝ)/200000), ((-738213861:ℝ)/2000), ((-9587193:ℝ)/100), ((-373527:ℝ)/25), ((-6468:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0) 6 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-7624839550903232527947:ℝ)/12800000000000), ((-627780969905133709203:ℝ)/320000000000), ((-18706986099850342833:ℝ)/6400000000), ((-416485814269154091:ℝ)/160000000), ((-12323451770696451:ℝ)/8000000), ((-636309806995863:ℝ)/1000000), ((-18725878756893:ℝ)/100000), ((-19633730091:ℝ)/500), ((-575056251:ℝ)/100), ((-2800806:ℝ)/5), ((-163332:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0) 10 ht
  have m12 := abs_poly_le (fun e => ([((-7624839550903232527947:ℝ)/12800000000000), ((-627780969905133709203:ℝ)/320000000000), ((-18706986099850342833:ℝ)/6400000000), ((-416485814269154091:ℝ)/160000000), ((-12323451770696451:ℝ)/8000000), ((-636309806995863:ℝ)/1000000), ((-18725878756893:ℝ)/100000), ((-19633730091:ℝ)/500), ((-575056251:ℝ)/100), ((-2800806:ℝ)/5), ((-163332:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0) 12 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 8, ([((-48145569800559:ℝ)/80000000), ((-4376869981869:ℝ)/4000000), ((-170527401891:ℝ)/200000), ((-738213861:ℝ)/2000), ((-9587193:ℝ)/100), ((-373527:ℝ)/25), ((-6468:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0 * t^e) - (((-48145569800559:ℝ)/80000000) + ((-4376869981869:ℝ)/4000000)*t)| ≤ ((43566695577:ℝ)/20000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 12, ([((-7624839550903232527947:ℝ)/12800000000000), ((-627780969905133709203:ℝ)/320000000000), ((-18706986099850342833:ℝ)/6400000000), ((-416485814269154091:ℝ)/160000000), ((-12323451770696451:ℝ)/8000000), ((-636309806995863:ℝ)/1000000), ((-18725878756893:ℝ)/100000), ((-19633730091:ℝ)/500), ((-575056251:ℝ)/100), ((-2800806:ℝ)/5), ((-163332:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e) - ((-7624839550903232527947:ℝ)/12800000000000) - ((-627780969905133709203:ℝ)/320000000000)*t| ≤ ((19565121249239928963:ℝ)/2560000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 12, ([((-7624839550903232527947:ℝ)/12800000000000), ((-627780969905133709203:ℝ)/320000000000), ((-18706986099850342833:ℝ)/6400000000), ((-416485814269154091:ℝ)/160000000), ((-12323451770696451:ℝ)/8000000), ((-636309806995863:ℝ)/1000000), ((-18725878756893:ℝ)/100000), ((-19633730091:ℝ)/500), ((-575056251:ℝ)/100), ((-2800806:ℝ)/5), ((-163332:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((1095974987421838329:ℝ)/1562500000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((35451187896478277:ℝ)/16000000000) - ((4731396450400389:ℝ)/800000000)*t| ≤ ((144243147419291:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((39:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-6288:ℝ), (81024:ℝ), (-238720:ℝ), (246784:ℝ), (-98304:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m13' : |centralNum13_01 q| ≤ ((221575774168088492841:ℝ)/390625000) := by
    rw [centralNum13_01_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((39:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-7368:ℝ), (59208:ℝ), (-155734:ℝ), (205300:ℝ), (-60000:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m23' : |centralNum23_01 q| ≤ ((98346017841957970929:ℝ)/250000000) := by
    rw [centralNum23_01_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece11_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece11_E11 h0) m23'
  have c5 := scaled_affine (X := ((-19650599607:ℝ)/31250000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-48145569800559:ℝ)/80000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((-7624839550903232527947:ℝ)/12800000000000) + ((35451187896478277:ℝ)/16000000000)*((-19650599607:ℝ)/31250000000000) - ((-649133701077751467:ℝ)/1000000000000)) (β := ((-4376869981869:ℝ)/4000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((-627780969905133709203:ℝ)/320000000000) - 3*((-7624839550903232527947:ℝ)/12800000000000)) + ((4731396450400389:ℝ)/800000000)*((-19650599607:ℝ)/31250000000000) - ((-111140719468876623:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_11 0 1 = centralNum11_01 q + 8*(Real.exp (-(3*((77:ℝ)/20)))*Real.exp (-3*t))*centralNum12_01 q + 18*Real.exp (-8*q)*centralNum13_01 q + 72*Real.exp (-11*q)*centralNum23_01 q + 8*q^7*(2*q-3)^2*((-19650599607:ℝ)/31250000000000) + (0:ℝ) := by
    rw [pieceW_01, pieceX_11, sym4_01, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((38047015127100644784912954403939726172201631225999443560036052201731:ℝ)/81588424806311929668134896423298599961685035245976787900250000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-48145569800559:ℝ)/80000000) + ((-4376869981869:ℝ)/4000000)*t) + (8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((-7624839550903232527947:ℝ)/12800000000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((-627780969905133709203:ℝ)/320000000000) - 3*((-7624839550903232527947:ℝ)/12800000000000))*t) + (((35451187896478277:ℝ)/16000000000) + ((4731396450400389:ℝ)/800000000)*t)*((-19650599607:ℝ)/31250000000000) - (((-649133701077751467:ℝ)/1000000000000) + t * ((-111140719468876623:ℝ)/100000000000)) = (((-48145569800559:ℝ)/80000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((-7624839550903232527947:ℝ)/12800000000000) + ((35451187896478277:ℝ)/16000000000)*((-19650599607:ℝ)/31250000000000) - ((-649133701077751467:ℝ)/1000000000000)) + t*(((-4376869981869:ℝ)/4000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((-627780969905133709203:ℝ)/320000000000) - 3*((-7624839550903232527947:ℝ)/12800000000000)) + ((4731396450400389:ℝ)/800000000)*((-19650599607:ℝ)/31250000000000) - ((-111140719468876623:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece11_e02 {q : ℝ} (h0 : ((19:ℝ)/5) ≤ q) (h1 : q ≤ ((39:ℝ)/10)) :
    |pieceW q pieceX_11 0 2 - (((162841766780541267:ℝ)/5000000000000) + (q - ((77:ℝ)/20)) * ((-280946594923039537:ℝ)/10000000000000))| ≤ ((128091007893879803:ℝ)/100000000000000) := by
  set t := q - ((77:ℝ)/20) with htd
  have hq : q = ((77:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece11_L3 piece11_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((77:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_02 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_02; ring
  have h12 : centralNum12_02 q = ∑ e ∈ Finset.range 13, ([((409373484099166412479269:ℝ)/2048000000000000), ((-36754502487176047735161:ℝ)/102400000000000), ((-11049881054574231876699:ℝ)/5120000000000), ((-181326475272074469183:ℝ)/51200000000), ((-2060139455563852971:ℝ)/640000000), ((-607789517495253093:ℝ)/320000000), ((-12409379432403723:ℝ)/16000000), ((-179967142666467:ℝ)/800000), ((-743483675799:ℝ)/16000), ((-5365728297:ℝ)/800), ((-128932479:ℝ)/200), ((-371439:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_02; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((409373484099166412479269:ℝ)/2048000000000000), ((-36754502487176047735161:ℝ)/102400000000000), ((-11049881054574231876699:ℝ)/5120000000000), ((-181326475272074469183:ℝ)/51200000000), ((-2060139455563852971:ℝ)/640000000), ((-607789517495253093:ℝ)/320000000), ((-12409379432403723:ℝ)/16000000), ((-179967142666467:ℝ)/800000), ((-743483675799:ℝ)/16000), ((-5365728297:ℝ)/800), ((-128932479:ℝ)/200), ((-371439:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((409373484099166412479269:ℝ)/2048000000000000), ((-36754502487176047735161:ℝ)/102400000000000), ((-11049881054574231876699:ℝ)/5120000000000), ((-181326475272074469183:ℝ)/51200000000), ((-2060139455563852971:ℝ)/640000000), ((-607789517495253093:ℝ)/320000000), ((-12409379432403723:ℝ)/16000000), ((-179967142666467:ℝ)/800000), ((-743483675799:ℝ)/16000), ((-5365728297:ℝ)/800), ((-128932479:ℝ)/200), ((-371439:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((409373484099166412479269:ℝ)/2048000000000000), ((-36754502487176047735161:ℝ)/102400000000000), ((-11049881054574231876699:ℝ)/5120000000000), ((-181326475272074469183:ℝ)/51200000000), ((-2060139455563852971:ℝ)/640000000), ((-607789517495253093:ℝ)/320000000), ((-12409379432403723:ℝ)/16000000), ((-179967142666467:ℝ)/800000), ((-743483675799:ℝ)/16000), ((-5365728297:ℝ)/800), ((-128932479:ℝ)/200), ((-371439:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e) - ((409373484099166412479269:ℝ)/2048000000000000) - ((-36754502487176047735161:ℝ)/102400000000000)*t| ≤ ((2999739245379599563371:ℝ)/512000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((409373484099166412479269:ℝ)/2048000000000000), ((-36754502487176047735161:ℝ)/102400000000000), ((-11049881054574231876699:ℝ)/5120000000000), ((-181326475272074469183:ℝ)/51200000000), ((-2060139455563852971:ℝ)/640000000), ((-607789517495253093:ℝ)/320000000), ((-12409379432403723:ℝ)/16000000), ((-179967142666467:ℝ)/800000), ((-743483675799:ℝ)/16000), ((-5365728297:ℝ)/800), ((-128932479:ℝ)/200), ((-371439:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((229063471783930429233957:ℝ)/1024000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((35451187896478277:ℝ)/16000000000) - ((4731396450400389:ℝ)/800000000)*t| ≤ ((144243147419291:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((39:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82080:ℝ), (-967680:ℝ), (3257600:ℝ), (-4474880:ℝ), (2908160:ℝ), (-786432:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_02 q| ≤ ((22798401097405400275653:ℝ)/976562500) := by
    rw [centralNum13_02_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((39:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (87660:ℝ), (-702180:ℝ), ((7421435:ℝ)/4), ((-10854125:ℝ)/4), ((2828125:ℝ)/2), (-187500:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_02 q| ≤ ((7556658519538624758093:ℝ)/800000000) := by
    rw [centralNum23_02_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece11_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece11_E11 h0) m23'
  have c5 := scaled_affine (X := ((774437674717:ℝ)/100000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((409373484099166412479269:ℝ)/2048000000000000) + ((35451187896478277:ℝ)/16000000000)*((774437674717:ℝ)/100000000000000) - ((162841766780541267:ℝ)/5000000000000)) (β := (0:ℝ) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((-36754502487176047735161:ℝ)/102400000000000) - 3*((409373484099166412479269:ℝ)/2048000000000000)) + ((4731396450400389:ℝ)/800000000)*((774437674717:ℝ)/100000000000000) - ((-280946594923039537:ℝ)/10000000000000)) ht
  have hW : pieceW q pieceX_11 0 2 = centralNum11_02 q + 8*(Real.exp (-(3*((77:ℝ)/20)))*Real.exp (-3*t))*centralNum12_02 q + 18*Real.exp (-8*q)*centralNum13_02 q + 72*Real.exp (-11*q)*centralNum23_02 q + 8*q^7*(2*q-3)^2*((774437674717:ℝ)/100000000000000) + (0:ℝ) := by
    rw [pieceW_02, pieceX_11, sym4_02, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((350056257242911674194473215130861380539265318132135166076361108261:ℝ)/8158842480631192966813489642329859996168503524597678790025000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((409373484099166412479269:ℝ)/2048000000000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((-36754502487176047735161:ℝ)/102400000000000) - 3*((409373484099166412479269:ℝ)/2048000000000000))*t) + (((35451187896478277:ℝ)/16000000000) + ((4731396450400389:ℝ)/800000000)*t)*((774437674717:ℝ)/100000000000000) - (((162841766780541267:ℝ)/5000000000000) + t * ((-280946594923039537:ℝ)/10000000000000)) = ((0:ℝ) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((409373484099166412479269:ℝ)/2048000000000000) + ((35451187896478277:ℝ)/16000000000)*((774437674717:ℝ)/100000000000000) - ((162841766780541267:ℝ)/5000000000000)) + t*((0:ℝ) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((-36754502487176047735161:ℝ)/102400000000000) - 3*((409373484099166412479269:ℝ)/2048000000000000)) + ((4731396450400389:ℝ)/800000000)*((774437674717:ℝ)/100000000000000) - ((-280946594923039537:ℝ)/10000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece11_e03 {q : ℝ} (h0 : ((19:ℝ)/5) ≤ q) (h1 : q ≤ ((39:ℝ)/10)) :
    |pieceW q pieceX_11 0 3 - (((-122964815780514959:ℝ)/1000000000000) + (q - ((77:ℝ)/20)) * ((-9035177173670353:ℝ)/15625000000))| ≤ ((1681318340316659:ℝ)/156250000000) := by
  set t := q - ((77:ℝ)/20) with htd
  have hq : q = ((77:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece11_L3 piece11_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((77:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_03 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_03; ring
  have h12 : centralNum12_03 q = ∑ e ∈ Finset.range 14, ([((124774336457946219309199011:ℝ)/81920000000000000), ((5520967106207476263158511:ℝ)/1024000000000000), ((413129334398755520679903:ℝ)/51200000000000), ((33458974299906223973751:ℝ)/5120000000000), ((290266450142419418283:ℝ)/102400000000), ((3634506328335353163:ℝ)/12800000000), ((-34148479433563341:ℝ)/80000000), ((-4806879128927037:ℝ)/16000000), ((-346578855998463:ℝ)/3200000), ((-100425874707:ℝ)/4000), ((-7773244299:ℝ)/2000), ((-547817499:ℝ)/1400), ((-3261789:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_03; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((124774336457946219309199011:ℝ)/81920000000000000), ((5520967106207476263158511:ℝ)/1024000000000000), ((413129334398755520679903:ℝ)/51200000000000), ((33458974299906223973751:ℝ)/5120000000000), ((290266450142419418283:ℝ)/102400000000), ((3634506328335353163:ℝ)/12800000000), ((-34148479433563341:ℝ)/80000000), ((-4806879128927037:ℝ)/16000000), ((-346578855998463:ℝ)/3200000), ((-100425874707:ℝ)/4000), ((-7773244299:ℝ)/2000), ((-547817499:ℝ)/1400), ((-3261789:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((124774336457946219309199011:ℝ)/81920000000000000), ((5520967106207476263158511:ℝ)/1024000000000000), ((413129334398755520679903:ℝ)/51200000000000), ((33458974299906223973751:ℝ)/5120000000000), ((290266450142419418283:ℝ)/102400000000), ((3634506328335353163:ℝ)/12800000000), ((-34148479433563341:ℝ)/80000000), ((-4806879128927037:ℝ)/16000000), ((-346578855998463:ℝ)/3200000), ((-100425874707:ℝ)/4000), ((-7773244299:ℝ)/2000), ((-547817499:ℝ)/1400), ((-3261789:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((124774336457946219309199011:ℝ)/81920000000000000), ((5520967106207476263158511:ℝ)/1024000000000000), ((413129334398755520679903:ℝ)/51200000000000), ((33458974299906223973751:ℝ)/5120000000000), ((290266450142419418283:ℝ)/102400000000), ((3634506328335353163:ℝ)/12800000000), ((-34148479433563341:ℝ)/80000000), ((-4806879128927037:ℝ)/16000000), ((-346578855998463:ℝ)/3200000), ((-100425874707:ℝ)/4000), ((-7773244299:ℝ)/2000), ((-547817499:ℝ)/1400), ((-3261789:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((124774336457946219309199011:ℝ)/81920000000000000) - ((5520967106207476263158511:ℝ)/1024000000000000)*t| ≤ ((12046261173884125244953947:ℝ)/573440000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((124774336457946219309199011:ℝ)/81920000000000000), ((5520967106207476263158511:ℝ)/1024000000000000), ((413129334398755520679903:ℝ)/51200000000000), ((33458974299906223973751:ℝ)/5120000000000), ((290266450142419418283:ℝ)/102400000000), ((3634506328335353163:ℝ)/12800000000), ((-34148479433563341:ℝ)/80000000), ((-4806879128927037:ℝ)/16000000), ((-346578855998463:ℝ)/3200000), ((-100425874707:ℝ)/4000), ((-7773244299:ℝ)/2000), ((-547817499:ℝ)/1400), ((-3261789:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((260013423838329248944446333:ℝ)/143360000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((35451187896478277:ℝ)/16000000000) - ((4731396450400389:ℝ)/800000000)*t| ≤ ((144243147419291:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((39:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-812160:ℝ), (8985600:ℝ), (-32225280:ℝ), (52019200:ℝ), ((-305233920:ℝ)/7), ((135528448:ℝ)/7), ((-25165824:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_03 q| ≤ ((5138251117622455674669633:ℝ)/8544921875) := by
    rw [centralNum13_03_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((39:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-833220:ℝ), (6469740:ℝ), ((-68603955:ℝ)/4), ((104396875:ℝ)/4), ((-1001334375:ℝ)/56), ((125828125:ℝ)/28), ((-2343750:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_03 q| ≤ ((3444225529281588402729417:ℝ)/22400000000) := by
    rw [centralNum23_03_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece11_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece11_E11 h0) m23'
  have c5 := scaled_affine (X := ((-108489430133:ℝ)/1000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((124774336457946219309199011:ℝ)/81920000000000000) + ((35451187896478277:ℝ)/16000000000)*((-108489430133:ℝ)/1000000000000) - ((-122964815780514959:ℝ)/1000000000000)) (β := (0:ℝ) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((5520967106207476263158511:ℝ)/1024000000000000) - 3*((124774336457946219309199011:ℝ)/81920000000000000)) + ((4731396450400389:ℝ)/800000000)*((-108489430133:ℝ)/1000000000000) - ((-9035177173670353:ℝ)/15625000000)) ht
  have hW : pieceW q pieceX_11 0 3 = centralNum11_03 q + 8*(Real.exp (-(3*((77:ℝ)/20)))*Real.exp (-3*t))*centralNum12_03 q + 18*Real.exp (-8*q)*centralNum13_03 q + 72*Real.exp (-11*q)*centralNum23_03 q + 8*q^7*(2*q-3)^2*((-108489430133:ℝ)/1000000000000) + (0:ℝ) := by
    rw [pieceW_03, pieceX_11, sym4_03, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((8654750444521774863551178857319233054133638275757373079521318211:ℝ)/81588424806311929668134896423298599961685035245976787900250000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((124774336457946219309199011:ℝ)/81920000000000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((5520967106207476263158511:ℝ)/1024000000000000) - 3*((124774336457946219309199011:ℝ)/81920000000000000))*t) + (((35451187896478277:ℝ)/16000000000) + ((4731396450400389:ℝ)/800000000)*t)*((-108489430133:ℝ)/1000000000000) - (((-122964815780514959:ℝ)/1000000000000) + t * ((-9035177173670353:ℝ)/15625000000)) = ((0:ℝ) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((124774336457946219309199011:ℝ)/81920000000000000) + ((35451187896478277:ℝ)/16000000000)*((-108489430133:ℝ)/1000000000000) - ((-122964815780514959:ℝ)/1000000000000)) + t*((0:ℝ) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((5520967106207476263158511:ℝ)/1024000000000000) - 3*((124774336457946219309199011:ℝ)/81920000000000000)) + ((4731396450400389:ℝ)/800000000)*((-108489430133:ℝ)/1000000000000) - ((-9035177173670353:ℝ)/15625000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece11_e11 {q : ℝ} (h0 : ((19:ℝ)/5) ≤ q) (h1 : q ≤ ((39:ℝ)/10)) :
    |pieceW q pieceX_11 1 1 - (((7352379756230599:ℝ)/3125000000) + (q - ((77:ℝ)/20)) * ((26230354021152059:ℝ)/5000000000))| ≤ ((10741120100109359:ℝ)/625000000000) := by
  set t := q - ((77:ℝ)/20) with htd
  have hq : q = ((77:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece11_L3 piece11_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((77:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_11 q = ∑ e ∈ Finset.range 10, ([((26840425685481331:ℝ)/12000000000), ((2077724812129043:ℝ)/400000000), ((27340242484709:ℝ)/5000000), ((856721153673:ℝ)/250000), ((4400480084:ℝ)/3125), ((490920661:ℝ)/1250), ((9268924:ℝ)/125), ((227792:ℝ)/25), ((3296:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_11; ring
  have h12 : centralNum12_11 q = ∑ e ∈ Finset.range 13, ([((1334369300005805043323189:ℝ)/1536000000000000), ((40392104464281340703933:ℝ)/25600000000000), ((367428357538888520567:ℝ)/1280000000000), ((-23291701506924009621:ℝ)/12800000000), ((-404349852837134897:ℝ)/160000000), ((-142787244356667911:ℝ)/80000000), ((-3235278173324281:ℝ)/4000000), ((-50325896164289:ℝ)/200000), ((-218914300013:ℝ)/4000), ((-4934538937:ℝ)/600), ((-40840533:ℝ)/50), ((-241866:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_11; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((26840425685481331:ℝ)/12000000000), ((2077724812129043:ℝ)/400000000), ((27340242484709:ℝ)/5000000), ((856721153673:ℝ)/250000), ((4400480084:ℝ)/3125), ((490920661:ℝ)/1250), ((9268924:ℝ)/125), ((227792:ℝ)/25), ((3296:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((1334369300005805043323189:ℝ)/1536000000000000), ((40392104464281340703933:ℝ)/25600000000000), ((367428357538888520567:ℝ)/1280000000000), ((-23291701506924009621:ℝ)/12800000000), ((-404349852837134897:ℝ)/160000000), ((-142787244356667911:ℝ)/80000000), ((-3235278173324281:ℝ)/4000000), ((-50325896164289:ℝ)/200000), ((-218914300013:ℝ)/4000), ((-4934538937:ℝ)/600), ((-40840533:ℝ)/50), ((-241866:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((1334369300005805043323189:ℝ)/1536000000000000), ((40392104464281340703933:ℝ)/25600000000000), ((367428357538888520567:ℝ)/1280000000000), ((-23291701506924009621:ℝ)/12800000000), ((-404349852837134897:ℝ)/160000000), ((-142787244356667911:ℝ)/80000000), ((-3235278173324281:ℝ)/4000000), ((-50325896164289:ℝ)/200000), ((-218914300013:ℝ)/4000), ((-4934538937:ℝ)/600), ((-40840533:ℝ)/50), ((-241866:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((26840425685481331:ℝ)/12000000000), ((2077724812129043:ℝ)/400000000), ((27340242484709:ℝ)/5000000), ((856721153673:ℝ)/250000), ((4400480084:ℝ)/3125), ((490920661:ℝ)/1250), ((9268924:ℝ)/125), ((227792:ℝ)/25), ((3296:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((26840425685481331:ℝ)/12000000000) + ((2077724812129043:ℝ)/400000000)*t)| ≤ ((338577760206817:ℝ)/24000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((1334369300005805043323189:ℝ)/1536000000000000), ((40392104464281340703933:ℝ)/25600000000000), ((367428357538888520567:ℝ)/1280000000000), ((-23291701506924009621:ℝ)/12800000000), ((-404349852837134897:ℝ)/160000000), ((-142787244356667911:ℝ)/80000000), ((-3235278173324281:ℝ)/4000000), ((-50325896164289:ℝ)/200000), ((-218914300013:ℝ)/4000), ((-4934538937:ℝ)/600), ((-40840533:ℝ)/50), ((-241866:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e) - ((1334369300005805043323189:ℝ)/1536000000000000) - ((40392104464281340703933:ℝ)/25600000000000)*t| ≤ ((738399013394910409243:ℝ)/768000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((1334369300005805043323189:ℝ)/1536000000000000), ((40392104464281340703933:ℝ)/25600000000000), ((367428357538888520567:ℝ)/1280000000000), ((-23291701506924009621:ℝ)/12800000000), ((-404349852837134897:ℝ)/160000000), ((-142787244356667911:ℝ)/80000000), ((-3235278173324281:ℝ)/4000000), ((-50325896164289:ℝ)/200000), ((-218914300013:ℝ)/4000), ((-4934538937:ℝ)/600), ((-40840533:ℝ)/50), ((-241866:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((728511205712719443126737:ℝ)/768000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((35451187896478277:ℝ)/16000000000) - ((4731396450400389:ℝ)/800000000)*t| ≤ ((144243147419291:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((39:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-3444:ℝ), (162624:ℝ), (-1531216:ℝ), (4800960:ℝ), (-6350848:ℝ), ((12025856:ℝ)/3), (-1048576:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_11 q| ≤ ((31216346881674393189699:ℝ)/976562500) := by
    rw [centralNum13_11_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((39:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-4074:ℝ), (159906:ℝ), (-1104799:ℝ), (2801499:ℝ), (-3931375:ℝ), ((5896250:ℝ)/3), (-250000:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_11 q| ≤ ((13181501311931633574231:ℝ)/1000000000) := by
    rw [centralNum23_11_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece11_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece11_E11 h0) m23'
  have c5 := scaled_affine (X := ((221557230021:ℝ)/10000000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1))| ≤ ((36611702674152759296000000000:ℝ)/1798527223672662005980181361693) := by
    rw [abs_neg, tailWeight_1, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((39:ℝ)/10)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((39:ℝ)/10)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece11_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((4814744136400:ℝ)/531441)) ≤ ((39:ℝ)/10)^6*(8000*(2*((39:ℝ)/10)-3)^2*(1/((288652517379563037996819230889:ℝ)/1000000000000))*((4814744136400:ℝ)/531441)) := by
          gcongr
      _ ≤ ((36611702674152759296000000000:ℝ)/1798527223672662005980181361693) := by norm_num
  have c7 := affine_round (α := ((26840425685481331:ℝ)/12000000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((1334369300005805043323189:ℝ)/1536000000000000) + ((35451187896478277:ℝ)/16000000000)*((221557230021:ℝ)/10000000000000) - ((7352379756230599:ℝ)/3125000000)) (β := ((2077724812129043:ℝ)/400000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((40392104464281340703933:ℝ)/25600000000000) - 3*((1334369300005805043323189:ℝ)/1536000000000000)) + ((4731396450400389:ℝ)/800000000)*((221557230021:ℝ)/10000000000000) - ((26230354021152059:ℝ)/5000000000)) ht
  have hW : pieceW q pieceX_11 1 1 = centralNum11_11 q + 8*(Real.exp (-(3*((77:ℝ)/20)))*Real.exp (-3*t))*centralNum12_11 q + 18*Real.exp (-8*q)*centralNum13_11 q + 72*Real.exp (-11*q)*centralNum23_11 q + 8*q^7*(2*q-3)^2*((221557230021:ℝ)/10000000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1)) := by
    rw [pieceW_11, pieceX_11, sym4_11, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((1027688603644873851547825394811317299082295316206249627426472328193137:ℝ)/234974663442178357444228501699099967889652901508413149152720000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((26840425685481331:ℝ)/12000000000) + ((2077724812129043:ℝ)/400000000)*t) + (8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((1334369300005805043323189:ℝ)/1536000000000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((40392104464281340703933:ℝ)/25600000000000) - 3*((1334369300005805043323189:ℝ)/1536000000000000))*t) + (((35451187896478277:ℝ)/16000000000) + ((4731396450400389:ℝ)/800000000)*t)*((221557230021:ℝ)/10000000000000) - (((7352379756230599:ℝ)/3125000000) + t * ((26230354021152059:ℝ)/5000000000)) = (((26840425685481331:ℝ)/12000000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((1334369300005805043323189:ℝ)/1536000000000000) + ((35451187896478277:ℝ)/16000000000)*((221557230021:ℝ)/10000000000000) - ((7352379756230599:ℝ)/3125000000)) + t*(((2077724812129043:ℝ)/400000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((40392104464281340703933:ℝ)/25600000000000) - 3*((1334369300005805043323189:ℝ)/1536000000000000)) + ((4731396450400389:ℝ)/800000000)*((221557230021:ℝ)/10000000000000) - ((26230354021152059:ℝ)/5000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece11_e12 {q : ℝ} (h0 : ((19:ℝ)/5) ≤ q) (h1 : q ≤ ((39:ℝ)/10)) :
    |pieceW q pieceX_11 1 2 - (((86391819684601793:ℝ)/250000000000000) + (q - ((77:ℝ)/20)) * ((162288122667626089:ℝ)/1000000000000))| ≤ ((41160417993376833:ℝ)/2000000000000) := by
  set t := q - ((77:ℝ)/20) with htd
  have hq : q = ((77:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece11_L3 piece11_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((77:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_12 q = ∑ e ∈ Finset.range 9, ([((-715097186085359:ℝ)/1920000000), ((-15285210134579:ℝ)/24000000), ((-505746800867:ℝ)/1200000), ((-7199068877:ℝ)/60000), ((-1523753:ℝ)/1200), ((1308307:ℝ)/150), ((36746:ℝ)/15), ((872:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_12; ring
  have h12 : centralNum12_12 q = ∑ e ∈ Finset.range 14, ([((588975757867251066690313397:ℝ)/245760000000000000), ((33931350224401217654631257:ℝ)/3072000000000000), ((3112476774306965060467241:ℝ)/153600000000000), ((312321696146451790378657:ℝ)/15360000000000), ((3786574743622112857261:ℝ)/307200000000), ((169844711576003873101:ℝ)/38400000000), ((156960925944178733:ℝ)/240000000), ((-9408087489278539:ℝ)/48000000), ((-1380037228134841:ℝ)/9600000), ((-169027216223:ℝ)/4000), ((-14893729791:ℝ)/2000), ((-163342953:ℝ)/200), ((-1035423:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_12; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-715097186085359:ℝ)/1920000000), ((-15285210134579:ℝ)/24000000), ((-505746800867:ℝ)/1200000), ((-7199068877:ℝ)/60000), ((-1523753:ℝ)/1200), ((1308307:ℝ)/150), ((36746:ℝ)/15), ((872:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((588975757867251066690313397:ℝ)/245760000000000000), ((33931350224401217654631257:ℝ)/3072000000000000), ((3112476774306965060467241:ℝ)/153600000000000), ((312321696146451790378657:ℝ)/15360000000000), ((3786574743622112857261:ℝ)/307200000000), ((169844711576003873101:ℝ)/38400000000), ((156960925944178733:ℝ)/240000000), ((-9408087489278539:ℝ)/48000000), ((-1380037228134841:ℝ)/9600000), ((-169027216223:ℝ)/4000), ((-14893729791:ℝ)/2000), ((-163342953:ℝ)/200), ((-1035423:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((588975757867251066690313397:ℝ)/245760000000000000), ((33931350224401217654631257:ℝ)/3072000000000000), ((3112476774306965060467241:ℝ)/153600000000000), ((312321696146451790378657:ℝ)/15360000000000), ((3786574743622112857261:ℝ)/307200000000), ((169844711576003873101:ℝ)/38400000000), ((156960925944178733:ℝ)/240000000), ((-9408087489278539:ℝ)/48000000), ((-1380037228134841:ℝ)/9600000), ((-169027216223:ℝ)/4000), ((-14893729791:ℝ)/2000), ((-163342953:ℝ)/200), ((-1035423:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((-715097186085359:ℝ)/1920000000), ((-15285210134579:ℝ)/24000000), ((-505746800867:ℝ)/1200000), ((-7199068877:ℝ)/60000), ((-1523753:ℝ)/1200), ((1308307:ℝ)/150), ((36746:ℝ)/15), ((872:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((-715097186085359:ℝ)/1920000000) + ((-15285210134579:ℝ)/24000000)*t)| ≤ ((2051804023663:ℝ)/1920000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((588975757867251066690313397:ℝ)/245760000000000000), ((33931350224401217654631257:ℝ)/3072000000000000), ((3112476774306965060467241:ℝ)/153600000000000), ((312321696146451790378657:ℝ)/15360000000000), ((3786574743622112857261:ℝ)/307200000000), ((169844711576003873101:ℝ)/38400000000), ((156960925944178733:ℝ)/240000000), ((-9408087489278539:ℝ)/48000000), ((-1380037228134841:ℝ)/9600000), ((-169027216223:ℝ)/4000), ((-14893729791:ℝ)/2000), ((-163342953:ℝ)/200), ((-1035423:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e) - ((588975757867251066690313397:ℝ)/245760000000000000) - ((33931350224401217654631257:ℝ)/3072000000000000)*t| ≤ ((4364608534356563886880041:ℝ)/81920000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((588975757867251066690313397:ℝ)/245760000000000000), ((33931350224401217654631257:ℝ)/3072000000000000), ((3112476774306965060467241:ℝ)/153600000000000), ((312321696146451790378657:ℝ)/15360000000000), ((3786574743622112857261:ℝ)/307200000000), ((169844711576003873101:ℝ)/38400000000), ((156960925944178733:ℝ)/240000000), ((-9408087489278539:ℝ)/48000000), ((-1380037228134841:ℝ)/9600000), ((-169027216223:ℝ)/4000), ((-14893729791:ℝ)/2000), ((-163342953:ℝ)/200), ((-1035423:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((184448746091981407242369637:ℝ)/61440000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((35451187896478277:ℝ)/16000000000) - ((4731396450400389:ℝ)/800000000)*t| ≤ ((144243147419291:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((39:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (122790:ℝ), (-3586680:ℝ), (28529720:ℝ), (-90761600:ℝ), (137804800:ℝ), ((-332136448:ℝ)/3), ((141819904:ℝ)/3), (-8388608:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_12 q| ≤ ((14400106925355209873742993:ℝ)/9765625000) := by
    rw [centralNum13_12_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((39:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (132555:ℝ), (-3252375:ℝ), ((39743695:ℝ)/2), ((-197111615:ℝ)/4), ((281947375:ℝ)/4), ((-1100234375:ℝ)/24), ((131828125:ℝ)/12), (-781250:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_12 q| ≤ ((1241789140582954628422563:ℝ)/3200000000) := by
    rw [centralNum23_12_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece11_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece11_E11 h0) m23'
  have c5 := scaled_affine (X := ((848698446263:ℝ)/10000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-715097186085359:ℝ)/1920000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((588975757867251066690313397:ℝ)/245760000000000000) + ((35451187896478277:ℝ)/16000000000)*((848698446263:ℝ)/10000000000000) - ((86391819684601793:ℝ)/250000000000000)) (β := ((-15285210134579:ℝ)/24000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((33931350224401217654631257:ℝ)/3072000000000000) - 3*((588975757867251066690313397:ℝ)/245760000000000000)) + ((4731396450400389:ℝ)/800000000)*((848698446263:ℝ)/10000000000000) - ((162288122667626089:ℝ)/1000000000000)) ht
  have hW : pieceW q pieceX_11 1 2 = centralNum11_12 q + 8*(Real.exp (-(3*((77:ℝ)/20)))*Real.exp (-3*t))*centralNum12_12 q + 18*Real.exp (-8*q)*centralNum13_12 q + 72*Real.exp (-11*q)*centralNum23_12 q + 8*q^7*(2*q-3)^2*((848698446263:ℝ)/10000000000000) + (0:ℝ) := by
    rw [pieceW_12, pieceX_11, sym4_12, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((4389937372776867819458738707055088309427628578731484676154760649189:ℝ)/234974663442178357444228501699099967889652901508413149152720000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-715097186085359:ℝ)/1920000000) + ((-15285210134579:ℝ)/24000000)*t) + (8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((588975757867251066690313397:ℝ)/245760000000000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((33931350224401217654631257:ℝ)/3072000000000000) - 3*((588975757867251066690313397:ℝ)/245760000000000000))*t) + (((35451187896478277:ℝ)/16000000000) + ((4731396450400389:ℝ)/800000000)*t)*((848698446263:ℝ)/10000000000000) - (((86391819684601793:ℝ)/250000000000000) + t * ((162288122667626089:ℝ)/1000000000000)) = (((-715097186085359:ℝ)/1920000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((588975757867251066690313397:ℝ)/245760000000000000) + ((35451187896478277:ℝ)/16000000000)*((848698446263:ℝ)/10000000000000) - ((86391819684601793:ℝ)/250000000000000)) + t*(((-15285210134579:ℝ)/24000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((33931350224401217654631257:ℝ)/3072000000000000) - 3*((588975757867251066690313397:ℝ)/245760000000000000)) + ((4731396450400389:ℝ)/800000000)*((848698446263:ℝ)/10000000000000) - ((162288122667626089:ℝ)/1000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece11_e13 {q : ℝ} (h0 : ((19:ℝ)/5) ≤ q) (h1 : q ≤ ((39:ℝ)/10)) :
    |pieceW q pieceX_11 1 3 - (((460665468697026169:ℝ)/500000000000) + (q - ((77:ℝ)/20)) * ((429898918841471289:ℝ)/100000000000))| ≤ ((968056574082606027:ℝ)/10000000000000) := by
  set t := q - ((77:ℝ)/20) with htd
  have hq : q = ((77:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece11_L3 piece11_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((77:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_13 q = ∑ e ∈ Finset.range 7, ([((-625267140267:ℝ)/3200000), ((-24361057413:ℝ)/80000), ((-316377369:ℝ)/1600), ((-1369599:ℝ)/20), ((-53361:ℝ)/4), (-1386:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_13; ring
  have h12 : centralNum12_13 q = ∑ e ∈ Finset.range 15, ([((-25488755621404013619394155519:ℝ)/3276800000000000000), ((-3776323716541363093010994243:ℝ)/163840000000000000), ((-26470941249235862198442777:ℝ)/1024000000000000), ((-2063110331330290351454961:ℝ)/204800000000000), ((122689508450209867560471:ℝ)/20480000000000), ((10049680785404926179591:ℝ)/1024000000000), ((152628889845702464601:ℝ)/25600000000), ((1338909549535927581:ℝ)/640000000), ((54156102485640783:ℝ)/128000000), ((188056088476731:ℝ)/6400000), ((-697422289239:ℝ)/80000), ((-165018027087:ℝ)/56000), ((-2326892913:ℝ)/5600), ((-8492121:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_13; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-625267140267:ℝ)/3200000), ((-24361057413:ℝ)/80000), ((-316377369:ℝ)/1600), ((-1369599:ℝ)/20), ((-53361:ℝ)/4), (-1386:ℝ), (-60:ℝ)] : List ℝ).getD e 0) 5 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-25488755621404013619394155519:ℝ)/3276800000000000000), ((-3776323716541363093010994243:ℝ)/163840000000000000), ((-26470941249235862198442777:ℝ)/1024000000000000), ((-2063110331330290351454961:ℝ)/204800000000000), ((122689508450209867560471:ℝ)/20480000000000), ((10049680785404926179591:ℝ)/1024000000000), ((152628889845702464601:ℝ)/25600000000), ((1338909549535927581:ℝ)/640000000), ((54156102485640783:ℝ)/128000000), ((188056088476731:ℝ)/6400000), ((-697422289239:ℝ)/80000), ((-165018027087:ℝ)/56000), ((-2326892913:ℝ)/5600), ((-8492121:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-25488755621404013619394155519:ℝ)/3276800000000000000), ((-3776323716541363093010994243:ℝ)/163840000000000000), ((-26470941249235862198442777:ℝ)/1024000000000000), ((-2063110331330290351454961:ℝ)/204800000000000), ((122689508450209867560471:ℝ)/20480000000000), ((10049680785404926179591:ℝ)/1024000000000), ((152628889845702464601:ℝ)/25600000000), ((1338909549535927581:ℝ)/640000000), ((54156102485640783:ℝ)/128000000), ((188056088476731:ℝ)/6400000), ((-697422289239:ℝ)/80000), ((-165018027087:ℝ)/56000), ((-2326892913:ℝ)/5600), ((-8492121:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 7, ([((-625267140267:ℝ)/3200000), ((-24361057413:ℝ)/80000), ((-316377369:ℝ)/1600), ((-1369599:ℝ)/20), ((-53361:ℝ)/4), (-1386:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e) - (((-625267140267:ℝ)/3200000) + ((-24361057413:ℝ)/80000)*t)| ≤ ((1609547019:ℝ)/3200000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-25488755621404013619394155519:ℝ)/3276800000000000000), ((-3776323716541363093010994243:ℝ)/163840000000000000), ((-26470941249235862198442777:ℝ)/1024000000000000), ((-2063110331330290351454961:ℝ)/204800000000000), ((122689508450209867560471:ℝ)/20480000000000), ((10049680785404926179591:ℝ)/1024000000000), ((152628889845702464601:ℝ)/25600000000), ((1338909549535927581:ℝ)/640000000), ((54156102485640783:ℝ)/128000000), ((188056088476731:ℝ)/6400000), ((-697422289239:ℝ)/80000), ((-165018027087:ℝ)/56000), ((-2326892913:ℝ)/5600), ((-8492121:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((-25488755621404013619394155519:ℝ)/3276800000000000000) - ((-3776323716541363093010994243:ℝ)/163840000000000000)*t| ≤ ((756093801797417924322097851:ℝ)/11468800000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-25488755621404013619394155519:ℝ)/3276800000000000000), ((-3776323716541363093010994243:ℝ)/163840000000000000), ((-26470941249235862198442777:ℝ)/1024000000000000), ((-2063110331330290351454961:ℝ)/204800000000000), ((122689508450209867560471:ℝ)/20480000000000), ((10049680785404926179591:ℝ)/1024000000000), ((152628889845702464601:ℝ)/25600000000), ((1338909549535927581:ℝ)/640000000), ((54156102485640783:ℝ)/128000000), ((188056088476731:ℝ)/6400000), ((-697422289239:ℝ)/80000), ((-165018027087:ℝ)/56000), ((-2326892913:ℝ)/5600), ((-8492121:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((51591935742303118208870061009:ℝ)/5734400000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((35451187896478277:ℝ)/16000000000) - ((4731396450400389:ℝ)/800000000)*t| ≤ ((144243147419291:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((39:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2325540:ℝ), (52589280:ℝ), (-375655200:ℝ), (1192958720:ℝ), (-1965096960:ℝ), ((12857851904:ℝ)/7), ((-21171273728:ℝ)/21), ((914358272:ℝ)/3), ((-268435456:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_13 q| ≤ ((28794955915075598283529971009:ℝ)/683593750000) := by
    rw [centralNum13_13_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((39:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2399070:ℝ), (45666930:ℝ), (-251781675:ℝ), ((2452738385:ℝ)/4), ((-14104310625:ℝ)/16), ((74345740625:ℝ)/112), ((-74899765625:ℝ)/336), ((5161328125:ℝ)/168), ((-9765625:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_13 q| ≤ ((669615851687193179737198191:ℝ)/89600000000) := by
    rw [centralNum23_13_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece11_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece11_E11 h0) m23'
  have c5 := scaled_affine (X := ((96829622447:ℝ)/125000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-625267140267:ℝ)/3200000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((-25488755621404013619394155519:ℝ)/3276800000000000000) + ((35451187896478277:ℝ)/16000000000)*((96829622447:ℝ)/125000000000) - ((460665468697026169:ℝ)/500000000000)) (β := ((-24361057413:ℝ)/80000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((-3776323716541363093010994243:ℝ)/163840000000000000) - 3*((-25488755621404013619394155519:ℝ)/3276800000000000000)) + ((4731396450400389:ℝ)/800000000)*((96829622447:ℝ)/125000000000) - ((429898918841471289:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_11 1 3 = centralNum11_13 q + 8*(Real.exp (-(3*((77:ℝ)/20)))*Real.exp (-3*t))*centralNum12_13 q + 18*Real.exp (-8*q)*centralNum13_13 q + 72*Real.exp (-11*q)*centralNum23_13 q + 8*q^7*(2*q-3)^2*((96829622447:ℝ)/125000000000) + (0:ℝ) := by
    rw [pieceW_13, pieceX_11, sym4_13, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((5757690042573465191547861817479374388380448955352235062094052351:ℝ)/10198553100788991208516862052912324995210629405747098487531250000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-625267140267:ℝ)/3200000) + ((-24361057413:ℝ)/80000)*t) + (8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((-25488755621404013619394155519:ℝ)/3276800000000000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((-3776323716541363093010994243:ℝ)/163840000000000000) - 3*((-25488755621404013619394155519:ℝ)/3276800000000000000))*t) + (((35451187896478277:ℝ)/16000000000) + ((4731396450400389:ℝ)/800000000)*t)*((96829622447:ℝ)/125000000000) - (((460665468697026169:ℝ)/500000000000) + t * ((429898918841471289:ℝ)/100000000000)) = (((-625267140267:ℝ)/3200000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((-25488755621404013619394155519:ℝ)/3276800000000000000) + ((35451187896478277:ℝ)/16000000000)*((96829622447:ℝ)/125000000000) - ((460665468697026169:ℝ)/500000000000)) + t*(((-24361057413:ℝ)/80000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((-3776323716541363093010994243:ℝ)/163840000000000000) - 3*((-25488755621404013619394155519:ℝ)/3276800000000000000)) + ((4731396450400389:ℝ)/800000000)*((96829622447:ℝ)/125000000000) - ((429898918841471289:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece11_e22 {q : ℝ} (h0 : ((19:ℝ)/5) ≤ q) (h1 : q ≤ ((39:ℝ)/10)) :
    |pieceW q pieceX_11 2 2 - (((586492667553574753:ℝ)/100000000000) + (q - ((77:ℝ)/20)) * ((45567918684710643:ℝ)/2500000000))| ≤ ((106609783898677289:ℝ)/500000000000) := by
  set t := q - ((77:ℝ)/20) with htd
  have hq : q = ((77:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece11_L3 piece11_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((77:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_22 q = ∑ e ∈ Finset.range 10, ([((34738897645563727:ℝ)/19200000000), ((1459443284169563:ℝ)/320000000), ((60990461763847:ℝ)/12000000), ((1990992534839:ℝ)/600000), ((28187968347:ℝ)/20000), ((1217903243:ℝ)/3000), ((5962763:ℝ)/75), ((51028:ℝ)/5), ((2332:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_22; ring
  have h12 : centralNum12_22 q = ∑ e ∈ Finset.range 15, ([((-590431339777971783791673253819:ℝ)/39321600000000000000), ((-31635902719335077027137934661:ℝ)/655360000000000000), ((-756780170657642571598012547:ℝ)/12288000000000000), ((-87556020099006670042902301:ℝ)/2457600000000000), ((-126271411125974918722303:ℝ)/81920000000000), ((149857459192451204272691:ℝ)/12288000000000), ((2860561125551023921181:ℝ)/307200000000), ((9369297005141777347:ℝ)/2560000000), ((1277357326915553003:ℝ)/1536000000), ((6485575323818951:ℝ)/76800000), ((-2832741751413:ℝ)/320000), ((-141093801207:ℝ)/32000), ((-2167770033:ℝ)/3200), ((-8258841:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_22; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((34738897645563727:ℝ)/19200000000), ((1459443284169563:ℝ)/320000000), ((60990461763847:ℝ)/12000000), ((1990992534839:ℝ)/600000), ((28187968347:ℝ)/20000), ((1217903243:ℝ)/3000), ((5962763:ℝ)/75), ((51028:ℝ)/5), ((2332:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-590431339777971783791673253819:ℝ)/39321600000000000000), ((-31635902719335077027137934661:ℝ)/655360000000000000), ((-756780170657642571598012547:ℝ)/12288000000000000), ((-87556020099006670042902301:ℝ)/2457600000000000), ((-126271411125974918722303:ℝ)/81920000000000), ((149857459192451204272691:ℝ)/12288000000000), ((2860561125551023921181:ℝ)/307200000000), ((9369297005141777347:ℝ)/2560000000), ((1277357326915553003:ℝ)/1536000000), ((6485575323818951:ℝ)/76800000), ((-2832741751413:ℝ)/320000), ((-141093801207:ℝ)/32000), ((-2167770033:ℝ)/3200), ((-8258841:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-590431339777971783791673253819:ℝ)/39321600000000000000), ((-31635902719335077027137934661:ℝ)/655360000000000000), ((-756780170657642571598012547:ℝ)/12288000000000000), ((-87556020099006670042902301:ℝ)/2457600000000000), ((-126271411125974918722303:ℝ)/81920000000000), ((149857459192451204272691:ℝ)/12288000000000), ((2860561125551023921181:ℝ)/307200000000), ((9369297005141777347:ℝ)/2560000000), ((1277357326915553003:ℝ)/1536000000), ((6485575323818951:ℝ)/76800000), ((-2832741751413:ℝ)/320000), ((-141093801207:ℝ)/32000), ((-2167770033:ℝ)/3200), ((-8258841:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((34738897645563727:ℝ)/19200000000), ((1459443284169563:ℝ)/320000000), ((60990461763847:ℝ)/12000000), ((1990992534839:ℝ)/600000), ((28187968347:ℝ)/20000), ((1217903243:ℝ)/3000), ((5962763:ℝ)/75), ((51028:ℝ)/5), ((2332:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((34738897645563727:ℝ)/19200000000) + ((1459443284169563:ℝ)/320000000)*t)| ≤ ((7878043900501:ℝ)/600000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-590431339777971783791673253819:ℝ)/39321600000000000000), ((-31635902719335077027137934661:ℝ)/655360000000000000), ((-756780170657642571598012547:ℝ)/12288000000000000), ((-87556020099006670042902301:ℝ)/2457600000000000), ((-126271411125974918722303:ℝ)/81920000000000), ((149857459192451204272691:ℝ)/12288000000000), ((2860561125551023921181:ℝ)/307200000000), ((9369297005141777347:ℝ)/2560000000), ((1277357326915553003:ℝ)/1536000000), ((6485575323818951:ℝ)/76800000), ((-2832741751413:ℝ)/320000), ((-141093801207:ℝ)/32000), ((-2167770033:ℝ)/3200), ((-8258841:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e) - ((-590431339777971783791673253819:ℝ)/39321600000000000000) - ((-31635902719335077027137934661:ℝ)/655360000000000000)*t| ≤ ((1557471977997354300202709311:ℝ)/9830400000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-590431339777971783791673253819:ℝ)/39321600000000000000), ((-31635902719335077027137934661:ℝ)/655360000000000000), ((-756780170657642571598012547:ℝ)/12288000000000000), ((-87556020099006670042902301:ℝ)/2457600000000000), ((-126271411125974918722303:ℝ)/81920000000000), ((149857459192451204272691:ℝ)/12288000000000), ((2860561125551023921181:ℝ)/307200000000), ((9369297005141777347:ℝ)/2560000000), ((1277357326915553003:ℝ)/1536000000), ((6485575323818951:ℝ)/76800000), ((-2832741751413:ℝ)/320000), ((-141093801207:ℝ)/32000), ((-2167770033:ℝ)/3200), ((-8258841:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e)| ≤ ((345784467923983216036948947523:ℝ)/19660800000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((35451187896478277:ℝ)/16000000000) - ((4731396450400389:ℝ)/800000000)*t| ≤ ((144243147419291:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((39:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82125:ℝ), (-6663750:ℝ), (115666200:ℝ), (-750437000:ℝ), (2277262000:ℝ), (-3656824320:ℝ), (3359621120:ℝ), (-1817706496:ℝ), ((1625292800:ℝ)/3), (-67108864:ℝ)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_22 q| ≤ ((7369615143904697330818942251:ℝ)/97656250000) := by
    rw [centralNum13_22_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((39:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((178425:ℝ)/2), ((-13176075:ℝ)/2), ((777815145:ℝ)/8), ((-3968389015:ℝ)/8), ((9393350195:ℝ)/8), ((-26366634375:ℝ)/16), ((77851609375:ℝ)/64), ((-25714921875:ℝ)/64), ((5236328125:ℝ)/96), ((-9765625:ℝ)/4)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_22 q| ≤ ((693495856807206800114120067:ℝ)/51200000000) := by
    rw [centralNum23_22_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece11_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece11_E11 h0) m23'
  have c5 := scaled_affine (X := ((117640627701:ℝ)/50000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2))| ≤ ((19545764156698239150080000000000:ℝ)/16186745013053958053821632255237) := by
    rw [abs_neg, tailWeight_2, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((39:ℝ)/10)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((39:ℝ)/10)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece11_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((2570430941234500:ℝ)/4782969)) ≤ ((39:ℝ)/10)^6*(8000*(2*((39:ℝ)/10)-3)^2*(1/((288652517379563037996819230889:ℝ)/1000000000000))*((2570430941234500:ℝ)/4782969)) := by
          gcongr
      _ ≤ ((19545764156698239150080000000000:ℝ)/16186745013053958053821632255237) := by norm_num
  have c7 := affine_round (α := ((34738897645563727:ℝ)/19200000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((-590431339777971783791673253819:ℝ)/39321600000000000000) + ((35451187896478277:ℝ)/16000000000)*((117640627701:ℝ)/50000000000) - ((586492667553574753:ℝ)/100000000000)) (β := ((1459443284169563:ℝ)/320000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((-31635902719335077027137934661:ℝ)/655360000000000000) - 3*((-590431339777971783791673253819:ℝ)/39321600000000000000)) + ((4731396450400389:ℝ)/800000000)*((117640627701:ℝ)/50000000000) - ((45567918684710643:ℝ)/2500000000)) ht
  have hW : pieceW q pieceX_11 2 2 = centralNum11_22 q + 8*(Real.exp (-(3*((77:ℝ)/20)))*Real.exp (-3*t))*centralNum12_22 q + 18*Real.exp (-8*q)*centralNum13_22 q + 72*Real.exp (-11*q)*centralNum23_22 q + 8*q^7*(2*q-3)^2*((117640627701:ℝ)/50000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2)) := by
    rw [pieceW_22, pieceX_11, sym4_22, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((96758895614231857936896257248500051666289701112053029352203637397:ℝ)/36714791162840368350660703390484369982758265860689554555112500000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((34738897645563727:ℝ)/19200000000) + ((1459443284169563:ℝ)/320000000)*t) + (8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((-590431339777971783791673253819:ℝ)/39321600000000000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((-31635902719335077027137934661:ℝ)/655360000000000000) - 3*((-590431339777971783791673253819:ℝ)/39321600000000000000))*t) + (((35451187896478277:ℝ)/16000000000) + ((4731396450400389:ℝ)/800000000)*t)*((117640627701:ℝ)/50000000000) - (((586492667553574753:ℝ)/100000000000) + t * ((45567918684710643:ℝ)/2500000000)) = (((34738897645563727:ℝ)/19200000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((-590431339777971783791673253819:ℝ)/39321600000000000000) + ((35451187896478277:ℝ)/16000000000)*((117640627701:ℝ)/50000000000) - ((586492667553574753:ℝ)/100000000000)) + t*(((1459443284169563:ℝ)/320000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((-31635902719335077027137934661:ℝ)/655360000000000000) - 3*((-590431339777971783791673253819:ℝ)/39321600000000000000)) + ((4731396450400389:ℝ)/800000000)*((117640627701:ℝ)/50000000000) - ((45567918684710643:ℝ)/2500000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece11_e23 {q : ℝ} (h0 : ((19:ℝ)/5) ≤ q) (h1 : q ≤ ((39:ℝ)/10)) :
    |pieceW q pieceX_11 2 3 - (((-323507740970011761:ℝ)/100000000000) + (q - ((77:ℝ)/20)) * ((-168550400417640437:ℝ)/10000000000))| ≤ ((140522466535326013:ℝ)/50000000000) := by
  set t := q - ((77:ℝ)/20) with htd
  have hq : q = ((77:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece11_L3 piece11_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((77:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_23 q = ∑ e ∈ Finset.range 9, ([((44366899117387:ℝ)/80000000), ((33487806294789:ℝ)/32000000), ((1509352425427:ℝ)/1600000), ((43205648717:ℝ)/80000), ((169509879:ℝ)/800), ((11280343:ℝ)/200), ((96257:ℝ)/10), (942:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_23; ring
  have h12 : centralNum12_23 q = ∑ e ∈ Finset.range 16, ([((14148643725792691914141353908513:ℝ)/524288000000000000000), ((136292949284627347167305678559:ℝ)/2621440000000000000), ((251875018847151782652150889:ℝ)/262144000000000000), ((-113988234145090744383877933:ℝ)/1310720000000000), ((-74357666989304048980160223:ℝ)/655360000000000), ((-6018979719076928807296109:ℝ)/81920000000000), ((-43833460504506829875187:ℝ)/1638400000000), ((-174428957269528373313:ℝ)/40960000000), ((610200853719728507:ℝ)/819200000), ((58814585896216821:ℝ)/102400000), ((7100197224800391:ℝ)/51200000), ((26919456506307:ℝ)/1792000), ((-30704002803:ℝ)/179200), ((-222888105:ℝ)/896), ((-12328119:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_23; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((44366899117387:ℝ)/80000000), ((33487806294789:ℝ)/32000000), ((1509352425427:ℝ)/1600000), ((43205648717:ℝ)/80000), ((169509879:ℝ)/800), ((11280343:ℝ)/200), ((96257:ℝ)/10), (942:ℝ), (40:ℝ)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((14148643725792691914141353908513:ℝ)/524288000000000000000), ((136292949284627347167305678559:ℝ)/2621440000000000000), ((251875018847151782652150889:ℝ)/262144000000000000), ((-113988234145090744383877933:ℝ)/1310720000000000), ((-74357666989304048980160223:ℝ)/655360000000000), ((-6018979719076928807296109:ℝ)/81920000000000), ((-43833460504506829875187:ℝ)/1638400000000), ((-174428957269528373313:ℝ)/40960000000), ((610200853719728507:ℝ)/819200000), ((58814585896216821:ℝ)/102400000), ((7100197224800391:ℝ)/51200000), ((26919456506307:ℝ)/1792000), ((-30704002803:ℝ)/179200), ((-222888105:ℝ)/896), ((-12328119:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 14 ht
  have m12 := abs_poly_le (fun e => ([((14148643725792691914141353908513:ℝ)/524288000000000000000), ((136292949284627347167305678559:ℝ)/2621440000000000000), ((251875018847151782652150889:ℝ)/262144000000000000), ((-113988234145090744383877933:ℝ)/1310720000000000), ((-74357666989304048980160223:ℝ)/655360000000000), ((-6018979719076928807296109:ℝ)/81920000000000), ((-43833460504506829875187:ℝ)/1638400000000), ((-174428957269528373313:ℝ)/40960000000), ((610200853719728507:ℝ)/819200000), ((58814585896216821:ℝ)/102400000), ((7100197224800391:ℝ)/51200000), ((26919456506307:ℝ)/1792000), ((-30704002803:ℝ)/179200), ((-222888105:ℝ)/896), ((-12328119:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 16 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((44366899117387:ℝ)/80000000), ((33487806294789:ℝ)/32000000), ((1509352425427:ℝ)/1600000), ((43205648717:ℝ)/80000), ((169509879:ℝ)/800), ((11280343:ℝ)/200), ((96257:ℝ)/10), (942:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e) - (((44366899117387:ℝ)/80000000) + ((33487806294789:ℝ)/32000000)*t)| ≤ ((1553417000611:ℝ)/640000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 16, ([((14148643725792691914141353908513:ℝ)/524288000000000000000), ((136292949284627347167305678559:ℝ)/2621440000000000000), ((251875018847151782652150889:ℝ)/262144000000000000), ((-113988234145090744383877933:ℝ)/1310720000000000), ((-74357666989304048980160223:ℝ)/655360000000000), ((-6018979719076928807296109:ℝ)/81920000000000), ((-43833460504506829875187:ℝ)/1638400000000), ((-174428957269528373313:ℝ)/40960000000), ((610200853719728507:ℝ)/819200000), ((58814585896216821:ℝ)/102400000), ((7100197224800391:ℝ)/51200000), ((26919456506307:ℝ)/1792000), ((-30704002803:ℝ)/179200), ((-222888105:ℝ)/896), ((-12328119:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e) - ((14148643725792691914141353908513:ℝ)/524288000000000000000) - ((136292949284627347167305678559:ℝ)/2621440000000000000)*t| ≤ ((51399838163221599404374584411:ℝ)/3670016000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 16, ([((14148643725792691914141353908513:ℝ)/524288000000000000000), ((136292949284627347167305678559:ℝ)/2621440000000000000), ((251875018847151782652150889:ℝ)/262144000000000000), ((-113988234145090744383877933:ℝ)/1310720000000000), ((-74357666989304048980160223:ℝ)/655360000000000), ((-6018979719076928807296109:ℝ)/81920000000000), ((-43833460504506829875187:ℝ)/1638400000000), ((-174428957269528373313:ℝ)/40960000000), ((610200853719728507:ℝ)/819200000), ((58814585896216821:ℝ)/102400000), ((7100197224800391:ℝ)/51200000), ((26919456506307:ℝ)/1792000), ((-30704002803:ℝ)/179200), ((-222888105:ℝ)/896), ((-12328119:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e)| ≤ ((27158103092158994825026312360783:ℝ)/917504000000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((35451187896478277:ℝ)/16000000000) - ((4731396450400389:ℝ)/800000000)*t| ≤ ((144243147419291:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((39:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-7627725:ℝ)/2), (173988600:ℝ), (-2299614450:ℝ), (13088188200:ℝ), (-38221499200:ℝ), (63366115840:ℝ), ((-445610508288:ℝ)/7), ((841540698112:ℝ)/21), ((-326820167680:ℝ)/21), ((10133438464:ℝ)/3), ((-2147483648:ℝ)/7)] : List ℝ).getD e 0) 16 hq1'
  have m13' : |centralNum13_23 q| ≤ ((8105738823872830958897152289619:ℝ)/3417968750000) := by
    rw [centralNum13_23_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((39:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-15801525:ℝ)/4), ((655493865:ℝ)/4), ((-7334421225:ℝ)/4), ((16442962485:ℝ)/2), ((-598626108395:ℝ)/32), ((414013307125:ℝ)/16), ((-4611984703125:ℝ)/224), ((399923828125:ℝ)/48), ((-4353201171875:ℝ)/2688), ((189736328125:ℝ)/1344), ((-244140625:ℝ)/56)] : List ℝ).getD e 0) 16 hq1'
  have m23' : |centralNum23_23 q| ≤ ((432876459590361411377515123959:ℝ)/1433600000000) := by
    rw [centralNum23_23_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece11_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece11_E11 h0) m23'
  have c5 := scaled_affine (X := ((-66231917669:ℝ)/25000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((44366899117387:ℝ)/80000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((14148643725792691914141353908513:ℝ)/524288000000000000000) + ((35451187896478277:ℝ)/16000000000)*((-66231917669:ℝ)/25000000000) - ((-323507740970011761:ℝ)/100000000000)) (β := ((33487806294789:ℝ)/32000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((136292949284627347167305678559:ℝ)/2621440000000000000) - 3*((14148643725792691914141353908513:ℝ)/524288000000000000000)) + ((4731396450400389:ℝ)/800000000)*((-66231917669:ℝ)/25000000000) - ((-168550400417640437:ℝ)/10000000000)) ht
  have hW : pieceW q pieceX_11 2 3 = centralNum11_23 q + 8*(Real.exp (-(3*((77:ℝ)/20)))*Real.exp (-3*t))*centralNum12_23 q + 18*Real.exp (-8*q)*centralNum13_23 q + 72*Real.exp (-11*q)*centralNum23_23 q + 8*q^7*(2*q-3)^2*((-66231917669:ℝ)/25000000000) + (0:ℝ) := by
    rw [pieceW_23, pieceX_11, sym4_23, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((390656615099448179134691413001807829482840207222735895591632987:ℝ)/470702450805645748085393633211338076702029049496019930193750000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((44366899117387:ℝ)/80000000) + ((33487806294789:ℝ)/32000000)*t) + (8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((14148643725792691914141353908513:ℝ)/524288000000000000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((136292949284627347167305678559:ℝ)/2621440000000000000) - 3*((14148643725792691914141353908513:ℝ)/524288000000000000000))*t) + (((35451187896478277:ℝ)/16000000000) + ((4731396450400389:ℝ)/800000000)*t)*((-66231917669:ℝ)/25000000000) - (((-323507740970011761:ℝ)/100000000000) + t * ((-168550400417640437:ℝ)/10000000000)) = (((44366899117387:ℝ)/80000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((14148643725792691914141353908513:ℝ)/524288000000000000000) + ((35451187896478277:ℝ)/16000000000)*((-66231917669:ℝ)/25000000000) - ((-323507740970011761:ℝ)/100000000000)) + t*(((33487806294789:ℝ)/32000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((136292949284627347167305678559:ℝ)/2621440000000000000) - 3*((14148643725792691914141353908513:ℝ)/524288000000000000000)) + ((4731396450400389:ℝ)/800000000)*((-66231917669:ℝ)/25000000000) - ((-168550400417640437:ℝ)/10000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece11_e33 {q : ℝ} (h0 : ((19:ℝ)/5) ≤ q) (h1 : q ≤ ((39:ℝ)/10)) :
    |pieceW q pieceX_11 3 3 - (((213466558195247209:ℝ)/1000000000) + (q - ((77:ℝ)/20)) * ((293497180261575647:ℝ)/500000000))| ≤ ((469300638587169287:ℝ)/5000000000) := by
  set t := q - ((77:ℝ)/20) with htd
  have hq : q = ((77:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece11_L3 piece11_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((77:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_33 q = ∑ e ∈ Finset.range 10, ([((793869245255471:ℝ)/3200000000), ((99667744866921:ℝ)/80000000), ((15708742320579:ℝ)/8000000), ((632852269203:ℝ)/400000), ((15427658301:ℝ)/20000), ((245206203:ℝ)/1000), ((2605281:ℝ)/50), ((253758:ℝ)/35), ((4224:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_33; ring
  have h12 : centralNum12_33 q = ∑ e ∈ Finset.range 17, ([((-570685973569756818087279614309353:ℝ)/20971520000000000000000), ((64247657555274348647547483515241:ℝ)/1048576000000000000000), ((3610700283302820843682261491777:ℝ)/10485760000000000000), ((277150920037791147812124789513:ℝ)/524288000000000000), ((10665023150882358186334236633:ℝ)/26214400000000000), ((1054251863973499242452855253:ℝ)/6553600000000000), ((4211728863673847556807969:ℝ)/327680000000000), ((-446695476033546202847901:ℝ)/22937600000000), ((-12145793467593709854699:ℝ)/1146880000000), ((-143951821262405635639:ℝ)/57344000000), ((-405186389095083201:ℝ)/2048000000), ((33247359800985249:ℝ)/716800000), ((103065178210821:ℝ)/7168000), ((69754804587:ℝ)/51200), ((-2300135697:ℝ)/125440), ((-393325389:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_33; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((793869245255471:ℝ)/3200000000), ((99667744866921:ℝ)/80000000), ((15708742320579:ℝ)/8000000), ((632852269203:ℝ)/400000), ((15427658301:ℝ)/20000), ((245206203:ℝ)/1000), ((2605281:ℝ)/50), ((253758:ℝ)/35), ((4224:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-570685973569756818087279614309353:ℝ)/20971520000000000000000), ((64247657555274348647547483515241:ℝ)/1048576000000000000000), ((3610700283302820843682261491777:ℝ)/10485760000000000000), ((277150920037791147812124789513:ℝ)/524288000000000000), ((10665023150882358186334236633:ℝ)/26214400000000000), ((1054251863973499242452855253:ℝ)/6553600000000000), ((4211728863673847556807969:ℝ)/327680000000000), ((-446695476033546202847901:ℝ)/22937600000000), ((-12145793467593709854699:ℝ)/1146880000000), ((-143951821262405635639:ℝ)/57344000000), ((-405186389095083201:ℝ)/2048000000), ((33247359800985249:ℝ)/716800000), ((103065178210821:ℝ)/7168000), ((69754804587:ℝ)/51200), ((-2300135697:ℝ)/125440), ((-393325389:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 15 ht
  have m12 := abs_poly_le (fun e => ([((-570685973569756818087279614309353:ℝ)/20971520000000000000000), ((64247657555274348647547483515241:ℝ)/1048576000000000000000), ((3610700283302820843682261491777:ℝ)/10485760000000000000), ((277150920037791147812124789513:ℝ)/524288000000000000), ((10665023150882358186334236633:ℝ)/26214400000000000), ((1054251863973499242452855253:ℝ)/6553600000000000), ((4211728863673847556807969:ℝ)/327680000000000), ((-446695476033546202847901:ℝ)/22937600000000), ((-12145793467593709854699:ℝ)/1146880000000), ((-143951821262405635639:ℝ)/57344000000), ((-405186389095083201:ℝ)/2048000000), ((33247359800985249:ℝ)/716800000), ((103065178210821:ℝ)/7168000), ((69754804587:ℝ)/51200), ((-2300135697:ℝ)/125440), ((-393325389:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 17 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((793869245255471:ℝ)/3200000000), ((99667744866921:ℝ)/80000000), ((15708742320579:ℝ)/8000000), ((632852269203:ℝ)/400000), ((15427658301:ℝ)/20000), ((245206203:ℝ)/1000), ((2605281:ℝ)/50), ((253758:ℝ)/35), ((4224:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e) - (((793869245255471:ℝ)/3200000000) + ((99667744866921:ℝ)/80000000)*t)| ≤ ((114500890544377:ℝ)/22400000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 17, ([((-570685973569756818087279614309353:ℝ)/20971520000000000000000), ((64247657555274348647547483515241:ℝ)/1048576000000000000000), ((3610700283302820843682261491777:ℝ)/10485760000000000000), ((277150920037791147812124789513:ℝ)/524288000000000000), ((10665023150882358186334236633:ℝ)/26214400000000000), ((1054251863973499242452855253:ℝ)/6553600000000000), ((4211728863673847556807969:ℝ)/327680000000000), ((-446695476033546202847901:ℝ)/22937600000000), ((-12145793467593709854699:ℝ)/1146880000000), ((-143951821262405635639:ℝ)/57344000000), ((-405186389095083201:ℝ)/2048000000), ((33247359800985249:ℝ)/716800000), ((103065178210821:ℝ)/7168000), ((69754804587:ℝ)/51200), ((-2300135697:ℝ)/125440), ((-393325389:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e) - ((-570685973569756818087279614309353:ℝ)/20971520000000000000000) - ((64247657555274348647547483515241:ℝ)/1048576000000000000000)*t| ≤ ((238797089067741993481558866942569:ℝ)/256901120000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 17, ([((-570685973569756818087279614309353:ℝ)/20971520000000000000000), ((64247657555274348647547483515241:ℝ)/1048576000000000000000), ((3610700283302820843682261491777:ℝ)/10485760000000000000), ((277150920037791147812124789513:ℝ)/524288000000000000), ((10665023150882358186334236633:ℝ)/26214400000000000), ((1054251863973499242452855253:ℝ)/6553600000000000), ((4211728863673847556807969:ℝ)/327680000000000), ((-446695476033546202847901:ℝ)/22937600000000), ((-12145793467593709854699:ℝ)/1146880000000), ((-143951821262405635639:ℝ)/57344000000), ((-405186389095083201:ℝ)/2048000000), ((33247359800985249:ℝ)/716800000), ((103065178210821:ℝ)/7168000), ((69754804587:ℝ)/51200), ((-2300135697:ℝ)/125440), ((-393325389:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e)| ≤ ((16033468140698747571966381630587691:ℝ)/513802240000000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((35451187896478277:ℝ)/16000000000), ((4731396450400389:ℝ)/800000000), ((34844432453061:ℝ)/5000000), ((297500185983:ℝ)/62500), ((103896410541:ℝ)/50000), ((1503695193:ℝ)/2500), ((14436576:ℝ)/125), ((354768:ℝ)/25), ((5064:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((35451187896478277:ℝ)/16000000000) - ((4731396450400389:ℝ)/800000000)*t| ≤ ((144243147419291:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((39:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-8120475:ℝ)/4), ((464861025:ℝ)/2), (-5906535975:ℝ), ((411904731750:ℝ)/7), ((-2024051769000:ℝ)/7), ((5554394637600:ℝ)/7), (-1314913862656:ℝ), ((9709155336192:ℝ)/7), ((-6724555112448:ℝ)/7), ((1313173667840:ℝ)/3), ((-6168244125696:ℝ)/49), ((3004329623552:ℝ)/147), ((-68719476736:ℝ)/49)] : List ℝ).getD e 0) 17 hq1'
  have m13' : |centralNum13_33 q| ≤ ((19480714813574607646437720171906447:ℝ)/239257812500000) := by
    rw [centralNum13_33_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((39:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-16872075:ℝ)/8), ((1833754545:ℝ)/8), ((-83998007145:ℝ)/16), ((4929124002765:ℝ)/112), ((-76723155584685:ℝ)/448), ((164888745653055:ℝ)/448), ((-63358359907625:ℝ)/128), ((364713160040625:ℝ)/896), ((-334937462578125:ℝ)/1792), ((245466998046875:ℝ)/5376), ((-72144521484375:ℝ)/12544), ((6518798828125:ℝ)/18816), ((-6103515625:ℝ)/784)] : List ℝ).getD e 0) 17 hq1'
  have m23' : |centralNum23_33 q| ≤ ((307507009741254954032516730962307:ℝ)/40140800000000) := by
    rw [centralNum23_33_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece11_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece11_E11 h0) m23'
  have c5 := scaled_affine (X := ((971775550441:ℝ)/10000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3))| ≤ ((25158646867041556875868160000000000:ℝ)/437042115352456867453184070891399) := by
    rw [abs_neg, tailWeight_3, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((39:ℝ)/10)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((39:ℝ)/10)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece11_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((3308571812705231500:ℝ)/129140163)) ≤ ((39:ℝ)/10)^6*(8000*(2*((39:ℝ)/10)-3)^2*(1/((288652517379563037996819230889:ℝ)/1000000000000))*((3308571812705231500:ℝ)/129140163)) := by
          gcongr
      _ ≤ ((25158646867041556875868160000000000:ℝ)/437042115352456867453184070891399) := by norm_num
  have c7 := affine_round (α := ((793869245255471:ℝ)/3200000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((-570685973569756818087279614309353:ℝ)/20971520000000000000000) + ((35451187896478277:ℝ)/16000000000)*((971775550441:ℝ)/10000000000) - ((213466558195247209:ℝ)/1000000000)) (β := ((99667744866921:ℝ)/80000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((64247657555274348647547483515241:ℝ)/1048576000000000000000) - 3*((-570685973569756818087279614309353:ℝ)/20971520000000000000000)) + ((4731396450400389:ℝ)/800000000)*((971775550441:ℝ)/10000000000) - ((293497180261575647:ℝ)/500000000)) ht
  have hW : pieceW q pieceX_11 3 3 = centralNum11_33 q + 8*(Real.exp (-(3*((77:ℝ)/20)))*Real.exp (-3*t))*centralNum12_33 q + 18*Real.exp (-8*q)*centralNum13_33 q + 72*Real.exp (-11*q)*centralNum23_33 q + 8*q^7*(2*q-3)^2*((971775550441:ℝ)/10000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3)) := by
    rw [pieceW_33, pieceX_11, sym4_33, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((33452140686637204472471899565794556718134273651633017695012768368041:ℝ)/78324887814059452481409500566366655963217633836137716384240000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((793869245255471:ℝ)/3200000000) + ((99667744866921:ℝ)/80000000)*t) + (8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((-570685973569756818087279614309353:ℝ)/20971520000000000000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((64247657555274348647547483515241:ℝ)/1048576000000000000000) - 3*((-570685973569756818087279614309353:ℝ)/20971520000000000000000))*t) + (((35451187896478277:ℝ)/16000000000) + ((4731396450400389:ℝ)/800000000)*t)*((971775550441:ℝ)/10000000000) - (((213466558195247209:ℝ)/1000000000) + t * ((293497180261575647:ℝ)/500000000)) = (((793869245255471:ℝ)/3200000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*((-570685973569756818087279614309353:ℝ)/20971520000000000000000) + ((35451187896478277:ℝ)/16000000000)*((971775550441:ℝ)/10000000000) - ((213466558195247209:ℝ)/1000000000)) + t*(((99667744866921:ℝ)/80000000) + 8*(((1/((103777037629710019882577736861:ℝ)/1000000000000000000000000))+(1/((103777023515170732568717557253:ℝ)/1000000000000000000000000)))/2)*(((64247657555274348647547483515241:ℝ)/1048576000000000000000) - 3*((-570685973569756818087279614309353:ℝ)/20971520000000000000000)) + ((4731396450400389:ℝ)/800000000)*((971775550441:ℝ)/10000000000) - ((293497180261575647:ℝ)/500000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece11_plus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((282572660038003097:ℝ)/100000000000) + ((1:ℝ)/20)*((353907386706293197:ℝ)/50000000000) - (((53365846744793379:ℝ)/2500000000000) + ((521871343467821597:ℝ)/100000000000000) + ((128091007893879803:ℝ)/100000000000000) + ((1681318340316659:ℝ)/156250000000)))
      (((-649133701077751467:ℝ)/1000000000000) + ((1:ℝ)/20)*((-111140719468876623:ℝ)/100000000000))
      (((162841766780541267:ℝ)/5000000000000) + ((1:ℝ)/20)*((-280946594923039537:ℝ)/10000000000000))
      (((-122964815780514959:ℝ)/1000000000000) + ((1:ℝ)/20)*((-9035177173670353:ℝ)/15625000000))
      (((7352379756230599:ℝ)/3125000000) + ((1:ℝ)/20)*((26230354021152059:ℝ)/5000000000) - (((521871343467821597:ℝ)/100000000000000) + ((10741120100109359:ℝ)/625000000000) + ((41160417993376833:ℝ)/2000000000000) + ((968056574082606027:ℝ)/10000000000000)))
      (((86391819684601793:ℝ)/250000000000000) + ((1:ℝ)/20)*((162288122667626089:ℝ)/1000000000000))
      (((460665468697026169:ℝ)/500000000000) + ((1:ℝ)/20)*((429898918841471289:ℝ)/100000000000))
      (((586492667553574753:ℝ)/100000000000) + ((1:ℝ)/20)*((45567918684710643:ℝ)/2500000000) - (((128091007893879803:ℝ)/100000000000000) + ((41160417993376833:ℝ)/2000000000000) + ((106609783898677289:ℝ)/500000000000) + ((140522466535326013:ℝ)/50000000000)))
      (((-323507740970011761:ℝ)/100000000000) + ((1:ℝ)/20)*((-168550400417640437:ℝ)/10000000000))
      (((213466558195247209:ℝ)/1000000000) + ((1:ℝ)/20)*((293497180261575647:ℝ)/500000000) - (((1681318340316659:ℝ)/156250000000) + ((968056574082606027:ℝ)/10000000000000) + ((140522466535326013:ℝ)/50000000000) + ((469300638587169287:ℝ)/5000000000))) i j :=
  quadForm_nonneg_of_ldl ((15705137937483815919:ℝ)/5000000000000) ((9476950879222422741724168333375336113:ℝ)/4089879671219743728906250000000) ((60334550241178783939587084483456529279284037775356691692496809:ℝ)/16173996167206268145875913955627240299520000000000000000) ((17018691563759332091183138220478944018653214705477953370849542746002437901244900563:ℝ)/120669100482357567879174168966913058558568075550713383384993618000000000000) ((-2349013536040632595:ℝ)/10470091958322543946) ((890389153756944449:ℝ)/89743645357050376680) ((-108483844811614349:ℝ)/2243591133926259417) ((161780465698016056124413622955121970837:ℝ)/24260994250809402218813870933440860449280) ((72126238857651012472994003402713631425:ℝ)/151631214067558763867586693334005377808) ((-66049302467234078365572457309755376409438672432194917482674400:ℝ)/60334550241178783939587084483456529279284037775356691692496809)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece11_minus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((282572660038003097:ℝ)/100000000000) - ((1:ℝ)/20)*((353907386706293197:ℝ)/50000000000) - (((53365846744793379:ℝ)/2500000000000) + ((521871343467821597:ℝ)/100000000000000) + ((128091007893879803:ℝ)/100000000000000) + ((1681318340316659:ℝ)/156250000000)))
      (((-649133701077751467:ℝ)/1000000000000) - ((1:ℝ)/20)*((-111140719468876623:ℝ)/100000000000))
      (((162841766780541267:ℝ)/5000000000000) - ((1:ℝ)/20)*((-280946594923039537:ℝ)/10000000000000))
      (((-122964815780514959:ℝ)/1000000000000) - ((1:ℝ)/20)*((-9035177173670353:ℝ)/15625000000))
      (((7352379756230599:ℝ)/3125000000) - ((1:ℝ)/20)*((26230354021152059:ℝ)/5000000000) - (((521871343467821597:ℝ)/100000000000000) + ((10741120100109359:ℝ)/625000000000) + ((41160417993376833:ℝ)/2000000000000) + ((968056574082606027:ℝ)/10000000000000)))
      (((86391819684601793:ℝ)/250000000000000) - ((1:ℝ)/20)*((162288122667626089:ℝ)/1000000000000))
      (((460665468697026169:ℝ)/500000000000) - ((1:ℝ)/20)*((429898918841471289:ℝ)/100000000000))
      (((586492667553574753:ℝ)/100000000000) - ((1:ℝ)/20)*((45567918684710643:ℝ)/2500000000) - (((128091007893879803:ℝ)/100000000000000) + ((41160417993376833:ℝ)/2000000000000) + ((106609783898677289:ℝ)/500000000000) + ((140522466535326013:ℝ)/50000000000)))
      (((-323507740970011761:ℝ)/100000000000) - ((1:ℝ)/20)*((-168550400417640437:ℝ)/10000000000))
      (((213466558195247209:ℝ)/1000000000) - ((1:ℝ)/20)*((293497180261575647:ℝ)/500000000) - (((1681318340316659:ℝ)/156250000000) + ((968056574082606027:ℝ)/10000000000000) + ((140522466535326013:ℝ)/50000000000) + ((469300638587169287:ℝ)/5000000000))) i j :=
  quadForm_nonneg_of_ldl ((12166064070420883949:ℝ)/5000000000000) ((1098517995988754370370827040738407565841:ℝ)/608303203521044197450000000000000) ((167639452596574243778501110441370852565599518606655633390706001:ℝ)/87881439679100349629666163259072605267280000000000000000) ((28189893439421952895025126284296847559032051988500875328072640114346227998981137819:ℝ)/335278905193148487557002220882741705131199037213311266781412002000000000000) ((-5935633413433131555:ℝ)/24332128140841767898) ((6794617266144690217:ℝ)/486642562816835357960) ((-470261244123849147:ℝ)/12166064070420883949) ((12619403865369130771645913646080505531:ℝ)/43940719839550174814833081629536302633640) ((415737624190777694018429199056267463650:ℝ)/1098517995988754370370827040738407565841) ((-210142846061848139688237319899566828485257702432658944951617600:ℝ)/167639452596574243778501110441370852565599518606655633390706001)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

/-- **Piece 11.** The piece matrix is positive semidefinite on `q ∈ [19/5, 39/10]`. -/
theorem piece_11 {q : ℝ} (h0 : ((19:ℝ)/5) ≤ q) (h1 : q ≤ ((39:ℝ)/10)) (y : Fin 4 → ℝ) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceW q pieceX_11 i j :=
  pieceForm_nonneg (pieceW_symm (sym4_symm _ _ _ _ _ _ _ _ _ _) q) (by norm_num : (0:ℝ) < ((1:ℝ)/20))
    (abs_le.mpr ⟨by linarith, by linarith⟩)
    (piece11_e00 h0 h1) (piece11_e01 h0 h1) (piece11_e02 h0 h1) (piece11_e03 h0 h1) (piece11_e11 h0 h1) (piece11_e12 h0 h1) (piece11_e13 h0 h1) (piece11_e22 h0 h1) (piece11_e23 h0 h1) (piece11_e33 h0 h1)
    piece11_plus piece11_minus y

/-! #### Piece 12 (seam), `q ∈ [39/10, 4]` -/

/-- The compensation matrix of piece 12. -/
def pieceX_12 : Fin 4 → Fin 4 → ℝ :=
  sym4 ((111973133929:ℝ)/10000000000000) ((-634629436629:ℝ)/1000000000000000) ((867738853991:ℝ)/100000000000000) ((-408111547811:ℝ)/5000000000000) ((107968838179:ℝ)/5000000000000) ((158770955539:ℝ)/10000000000000) ((297892288439:ℝ)/500000000000) ((126875021731:ℝ)/200000000000) ((-38654993997:ℝ)/20000000000) ((93812695481:ℝ)/2000000000)

theorem piece12_L3 : ((140083900709778466732471974383:ℝ)/1000000000000000000000000) ≤ Real.exp ((3:ℝ)*((79:ℝ)/20)) := by
  have h := le_exp_nat_add 11 (f := ((17:ℝ)/20)) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((79:ℝ)/20) = ((11:ℕ):ℝ) + ((17:ℝ)/20) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece12_U3 : Real.exp ((3:ℝ)*((79:ℝ)/20)) ≤ ((70042178050639083684723132989:ℝ)/500000000000000000000000) := by
  have h := exp_nat_add_le 11 (f := ((17:ℝ)/20)) (by norm_num) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((79:ℝ)/20) = ((11:ℕ):ℝ) + ((17:ℝ)/20) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem piece12_L8_at : ((22175215647670696722875420569:ℝ)/625000000000000) ≤ Real.exp ((8:ℝ)*((39:ℝ)/10)) := by
  have h := le_exp_nat_add 31 (f := ((1:ℝ)/5)) (by norm_num)
  rw [show ((8:ℝ):ℝ)*((39:ℝ)/10) = ((31:ℕ):ℝ) + ((1:ℝ)/5) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece12_E8 {q : ℝ} (h0 : ((39:ℝ)/10) ≤ q) : Real.exp (-((8:ℝ))*q) ≤ 1/((22175215647670696722875420569:ℝ)/625000000000000) := by
  have hm : Real.exp (-((8:ℝ))*q) ≤ Real.exp (-((8:ℝ)*((39:ℝ)/10))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece12_L8_at (le_refl _)).2

theorem piece12_L11_at : ((427790543904709206650549836381:ℝ)/100000000000) ≤ Real.exp ((11:ℝ)*((39:ℝ)/10)) := by
  have h := le_exp_nat_add 42 (f := ((9:ℝ)/10)) (by norm_num)
  rw [show ((11:ℝ):ℝ)*((39:ℝ)/10) = ((42:ℕ):ℝ) + ((9:ℝ)/10) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece12_E11 {q : ℝ} (h0 : ((39:ℝ)/10) ≤ q) : Real.exp (-((11:ℝ))*q) ≤ 1/((427790543904709206650549836381:ℝ)/100000000000) := by
  have hm : Real.exp (-((11:ℝ))*q) ≤ Real.exp (-((11:ℝ)*((39:ℝ)/10))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece12_L11_at (le_refl _)).2

theorem piece12_Lt_at : ((831493600485514841979407800409:ℝ)/1000000000000) ≤ Real.exp (((529:ℝ)/50)*((39:ℝ)/10)) := by
  have h := le_exp_nat_add 41 (f := ((131:ℝ)/500)) (by norm_num)
  rw [show (((529:ℝ)/50):ℝ)*((39:ℝ)/10) = ((41:ℕ):ℝ) + ((131:ℝ)/500) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece12_Et {q : ℝ} (h0 : ((39:ℝ)/10) ≤ q) : Real.exp (-(((529:ℝ)/50))*q) ≤ 1/((831493600485514841979407800409:ℝ)/1000000000000) := by
  have hm : Real.exp (-(((529:ℝ)/50))*q) ≤ Real.exp (-(((529:ℝ)/50)*((39:ℝ)/10))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece12_Lt_at (le_refl _)).2

theorem piece12_e00 {q : ℝ} (h0 : ((39:ℝ)/10) ≤ q) (h1 : q ≤ (4:ℝ)) :
    |pieceW q pieceX_12 0 0 - (((72363387600466157:ℝ)/20000000000) + (q - ((79:ℝ)/20)) * ((882407628736461083:ℝ)/100000000000))| ≤ ((256557593094336537:ℝ)/10000000000000) := by
  set t := q - ((79:ℝ)/20) with htd
  have hq : q = ((79:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece12_L3 piece12_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((79:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_00 q = ∑ e ∈ Finset.range 10, ([((57630930867463159:ℝ)/16000000000), ((6988521258773229:ℝ)/800000000), ((5935641793671:ℝ)/625000), ((1515664501953:ℝ)/250000), ((125001656787:ℝ)/50000), ((1723845333:ℝ)/2500), ((15879948:ℝ)/125), ((376512:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_00; ring
  have h12 : centralNum12_00 q = ∑ e ∈ Finset.range 11, ([((-89833524156446504443:ℝ)/320000000000), ((-2420496908646352989:ℝ)/3200000000), ((-73445794552214751:ℝ)/80000000), ((-1321600670030787:ℝ)/2000000), ((-62454515761113:ℝ)/200000), ((-5060722219707:ℝ)/50000), ((-2847836082:ℝ)/125), ((-87901014:ℝ)/25), ((-1780014:ℝ)/5), (-21352:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_00; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((57630930867463159:ℝ)/16000000000), ((6988521258773229:ℝ)/800000000), ((5935641793671:ℝ)/625000), ((1515664501953:ℝ)/250000), ((125001656787:ℝ)/50000), ((1723845333:ℝ)/2500), ((15879948:ℝ)/125), ((376512:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-89833524156446504443:ℝ)/320000000000), ((-2420496908646352989:ℝ)/3200000000), ((-73445794552214751:ℝ)/80000000), ((-1321600670030787:ℝ)/2000000), ((-62454515761113:ℝ)/200000), ((-5060722219707:ℝ)/50000), ((-2847836082:ℝ)/125), ((-87901014:ℝ)/25), ((-1780014:ℝ)/5), (-21352:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 9 ht
  have m12 := abs_poly_le (fun e => ([((-89833524156446504443:ℝ)/320000000000), ((-2420496908646352989:ℝ)/3200000000), ((-73445794552214751:ℝ)/80000000), ((-1321600670030787:ℝ)/2000000), ((-62454515761113:ℝ)/200000), ((-5060722219707:ℝ)/50000), ((-2847836082:ℝ)/125), ((-87901014:ℝ)/25), ((-1780014:ℝ)/5), (-21352:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 11 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((57630930867463159:ℝ)/16000000000), ((6988521258773229:ℝ)/800000000), ((5935641793671:ℝ)/625000), ((1515664501953:ℝ)/250000), ((125001656787:ℝ)/50000), ((1723845333:ℝ)/2500), ((15879948:ℝ)/125), ((376512:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - (((57630930867463159:ℝ)/16000000000) + ((6988521258773229:ℝ)/800000000)*t)| ≤ ((98064968440903:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 11, ([((-89833524156446504443:ℝ)/320000000000), ((-2420496908646352989:ℝ)/3200000000), ((-73445794552214751:ℝ)/80000000), ((-1321600670030787:ℝ)/2000000), ((-62454515761113:ℝ)/200000), ((-5060722219707:ℝ)/50000), ((-2847836082:ℝ)/125), ((-87901014:ℝ)/25), ((-1780014:ℝ)/5), (-21352:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e) - ((-89833524156446504443:ℝ)/320000000000) - ((-2420496908646352989:ℝ)/3200000000)*t| ≤ ((190381185080432653:ℝ)/80000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 11, ([((-89833524156446504443:ℝ)/320000000000), ((-2420496908646352989:ℝ)/3200000000), ((-73445794552214751:ℝ)/80000000), ((-1321600670030787:ℝ)/2000000), ((-62454515761113:ℝ)/200000), ((-5060722219707:ℝ)/50000), ((-2847836082:ℝ)/125), ((-87901014:ℝ)/25), ((-1780014:ℝ)/5), (-21352:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ (320929792:ℝ) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((46108585475767759:ℝ)/16000000000) - ((5967553945585029:ℝ)/800000000)*t| ≤ ((88165144661803:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (4:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (600:ℝ), (-7776:ℝ), (16800:ℝ), (-9216:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m13' : |centralNum13_00 q| ≤ (14587133952:ℝ) := by
    rw [centralNum13_00_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (4:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (780:ℝ), (-6156:ℝ), (15288:ℝ), (-14400:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m23' : |centralNum23_00 q| ≤ (19523371008:ℝ) := by
    rw [centralNum23_00_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((70042178050639083684723132989:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece12_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece12_E11 h0) m23'
  have c5 := scaled_affine (X := ((111973133929:ℝ)/10000000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0))| ≤ ((8573337272320000000000000000000:ℝ)/49098865615069165904042051206351041) := by
    rw [abs_neg, tailWeight_0, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ (4:ℝ)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*(4:ℝ)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece12_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((10465499600:ℝ)/59049)) ≤ (4:ℝ)^6*(8000*(2*(4:ℝ)-3)^2*(1/((831493600485514841979407800409:ℝ)/1000000000000))*((10465499600:ℝ)/59049)) := by
          gcongr
      _ ≤ ((8573337272320000000000000000000:ℝ)/49098865615069165904042051206351041) := by norm_num
  have c7 := affine_round (α := ((57630930867463159:ℝ)/16000000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((-89833524156446504443:ℝ)/320000000000) + ((46108585475767759:ℝ)/16000000000)*((111973133929:ℝ)/10000000000000) - ((72363387600466157:ℝ)/20000000000)) (β := ((6988521258773229:ℝ)/800000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((-2420496908646352989:ℝ)/3200000000) - 3*((-89833524156446504443:ℝ)/320000000000)) + ((5967553945585029:ℝ)/800000000)*((111973133929:ℝ)/10000000000000) - ((882407628736461083:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_12 0 0 = centralNum11_00 q + 8*(Real.exp (-(3*((79:ℝ)/20)))*Real.exp (-3*t))*centralNum12_00 q + 18*Real.exp (-8*q)*centralNum13_00 q + 72*Real.exp (-11*q)*centralNum23_00 q + 8*q^7*(2*q-3)^2*((111973133929:ℝ)/10000000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0)) := by
    rw [pieceW_00, pieceX_12, sym4_00, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((130487806970672214761898605105912310287916081770804153954907259266421:ℝ)/156988504248677601253884775576694813586264492626660963532592000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((57630930867463159:ℝ)/16000000000) + ((6988521258773229:ℝ)/800000000)*t) + (8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((-89833524156446504443:ℝ)/320000000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((-2420496908646352989:ℝ)/3200000000) - 3*((-89833524156446504443:ℝ)/320000000000))*t) + (((46108585475767759:ℝ)/16000000000) + ((5967553945585029:ℝ)/800000000)*t)*((111973133929:ℝ)/10000000000000) - (((72363387600466157:ℝ)/20000000000) + t * ((882407628736461083:ℝ)/100000000000)) = (((57630930867463159:ℝ)/16000000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((-89833524156446504443:ℝ)/320000000000) + ((46108585475767759:ℝ)/16000000000)*((111973133929:ℝ)/10000000000000) - ((72363387600466157:ℝ)/20000000000)) + t*(((6988521258773229:ℝ)/800000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((-2420496908646352989:ℝ)/3200000000) - 3*((-89833524156446504443:ℝ)/320000000000)) + ((5967553945585029:ℝ)/800000000)*((111973133929:ℝ)/10000000000000) - ((882407628736461083:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece12_e01 {q : ℝ} (h0 : ((39:ℝ)/10) ≤ q) (h1 : q ≤ (4:ℝ)) :
    |pieceW q pieceX_12 0 1 - (((-769025205870522981:ℝ)/1000000000000) + (q - ((79:ℝ)/20)) * ((-129004593917967179:ℝ)/100000000000))| ≤ ((550890165796614907:ℝ)/100000000000000) := by
  set t := q - ((79:ℝ)/20) with htd
  have hq : q = ((79:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece12_L3 piece12_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((79:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_01 q = ∑ e ∈ Finset.range 8, ([((-57611726958477:ℝ)/80000000), ((-5104836565941:ℝ)/4000000), ((-193854553137:ℝ)/200000), ((-817951701:ℝ)/2000), ((-10353819:ℝ)/100), ((-393183:ℝ)/25), ((-6636:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_01; ring
  have h12 : centralNum12_01 q = ∑ e ∈ Finset.range 12, ([((-10545477665519027354811:ℝ)/12800000000000), ((-841917226428430766097:ℝ)/320000000000), ((-24338916887049802341:ℝ)/6400000000), ((-525876126086497011:ℝ)/160000000), ((-15104724165646683:ℝ)/8000000), ((-757240418425617:ℝ)/1000000), ((-21640391072601:ℝ)/100000), ((-22036758351:ℝ)/500), ((-626955003:ℝ)/100), ((-2966514:ℝ)/5), ((-168084:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_01; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-57611726958477:ℝ)/80000000), ((-5104836565941:ℝ)/4000000), ((-193854553137:ℝ)/200000), ((-817951701:ℝ)/2000), ((-10353819:ℝ)/100), ((-393183:ℝ)/25), ((-6636:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0) 6 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-10545477665519027354811:ℝ)/12800000000000), ((-841917226428430766097:ℝ)/320000000000), ((-24338916887049802341:ℝ)/6400000000), ((-525876126086497011:ℝ)/160000000), ((-15104724165646683:ℝ)/8000000), ((-757240418425617:ℝ)/1000000), ((-21640391072601:ℝ)/100000), ((-22036758351:ℝ)/500), ((-626955003:ℝ)/100), ((-2966514:ℝ)/5), ((-168084:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0) 10 ht
  have m12 := abs_poly_le (fun e => ([((-10545477665519027354811:ℝ)/12800000000000), ((-841917226428430766097:ℝ)/320000000000), ((-24338916887049802341:ℝ)/6400000000), ((-525876126086497011:ℝ)/160000000), ((-15104724165646683:ℝ)/8000000), ((-757240418425617:ℝ)/1000000), ((-21640391072601:ℝ)/100000), ((-22036758351:ℝ)/500), ((-626955003:ℝ)/100), ((-2966514:ℝ)/5), ((-168084:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0) 12 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 8, ([((-57611726958477:ℝ)/80000000), ((-5104836565941:ℝ)/4000000), ((-193854553137:ℝ)/200000), ((-817951701:ℝ)/2000), ((-10353819:ℝ)/100), ((-393183:ℝ)/25), ((-6636:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0 * t^e) - (((-57611726958477:ℝ)/80000000) + ((-5104836565941:ℝ)/4000000)*t)| ≤ ((98998237791:ℝ)/40000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 12, ([((-10545477665519027354811:ℝ)/12800000000000), ((-841917226428430766097:ℝ)/320000000000), ((-24338916887049802341:ℝ)/6400000000), ((-525876126086497011:ℝ)/160000000), ((-15104724165646683:ℝ)/8000000), ((-757240418425617:ℝ)/1000000), ((-21640391072601:ℝ)/100000), ((-22036758351:ℝ)/500), ((-626955003:ℝ)/100), ((-2966514:ℝ)/5), ((-168084:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e) - ((-10545477665519027354811:ℝ)/12800000000000) - ((-841917226428430766097:ℝ)/320000000000)*t| ≤ ((25421493124822222599:ℝ)/2560000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 12, ([((-10545477665519027354811:ℝ)/12800000000000), ((-841917226428430766097:ℝ)/320000000000), ((-24338916887049802341:ℝ)/6400000000), ((-525876126086497011:ℝ)/160000000), ((-15104724165646683:ℝ)/8000000), ((-757240418425617:ℝ)/1000000), ((-21640391072601:ℝ)/100000), ((-22036758351:ℝ)/500), ((-626955003:ℝ)/100), ((-2966514:ℝ)/5), ((-168084:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ (965345280:ℝ) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((46108585475767759:ℝ)/16000000000) - ((5967553945585029:ℝ)/800000000)*t| ≤ ((88165144661803:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (4:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-6288:ℝ), (81024:ℝ), (-238720:ℝ), (246784:ℝ), (-98304:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m13' : |centralNum13_01 q| ≤ (739080667136:ℝ) := by
    rw [centralNum13_01_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (4:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-7368:ℝ), (59208:ℝ), (-155734:ℝ), (205300:ℝ), (-60000:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m23' : |centralNum23_01 q| ≤ (511756599296:ℝ) := by
    rw [centralNum23_01_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((70042178050639083684723132989:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece12_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece12_E11 h0) m23'
  have c5 := scaled_affine (X := ((-634629436629:ℝ)/1000000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-57611726958477:ℝ)/80000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((-10545477665519027354811:ℝ)/12800000000000) + ((46108585475767759:ℝ)/16000000000)*((-634629436629:ℝ)/1000000000000000) - ((-769025205870522981:ℝ)/1000000000000)) (β := ((-5104836565941:ℝ)/4000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((-841917226428430766097:ℝ)/320000000000) - 3*((-10545477665519027354811:ℝ)/12800000000000)) + ((5967553945585029:ℝ)/800000000)*((-634629436629:ℝ)/1000000000000000) - ((-129004593917967179:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_12 0 1 = centralNum11_01 q + 8*(Real.exp (-(3*((79:ℝ)/20)))*Real.exp (-3*t))*centralNum12_01 q + 18*Real.exp (-8*q)*centralNum13_01 q + 72*Real.exp (-11*q)*centralNum23_01 q + 8*q^7*(2*q-3)^2*((-634629436629:ℝ)/1000000000000000) + (0:ℝ) := by
    rw [pieceW_01, pieceX_12, sym4_01, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((7438363724622348679565462922174095367769812709359318645618780942331279:ℝ)/15698850424867760125388477557669481358626449262666096353259200000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-57611726958477:ℝ)/80000000) + ((-5104836565941:ℝ)/4000000)*t) + (8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((-10545477665519027354811:ℝ)/12800000000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((-841917226428430766097:ℝ)/320000000000) - 3*((-10545477665519027354811:ℝ)/12800000000000))*t) + (((46108585475767759:ℝ)/16000000000) + ((5967553945585029:ℝ)/800000000)*t)*((-634629436629:ℝ)/1000000000000000) - (((-769025205870522981:ℝ)/1000000000000) + t * ((-129004593917967179:ℝ)/100000000000)) = (((-57611726958477:ℝ)/80000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((-10545477665519027354811:ℝ)/12800000000000) + ((46108585475767759:ℝ)/16000000000)*((-634629436629:ℝ)/1000000000000000) - ((-769025205870522981:ℝ)/1000000000000)) + t*(((-5104836565941:ℝ)/4000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((-841917226428430766097:ℝ)/320000000000) - 3*((-10545477665519027354811:ℝ)/12800000000000)) + ((5967553945585029:ℝ)/800000000)*((-634629436629:ℝ)/1000000000000000) - ((-129004593917967179:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece12_e02 {q : ℝ} (h0 : ((39:ℝ)/10) ≤ q) (h1 : q ≤ (4:ℝ)) :
    |pieceW q pieceX_12 0 2 - (((329177026029719493:ℝ)/10000000000000) + (q - ((79:ℝ)/20)) * ((-27533621446419653:ℝ)/2500000000000))| ≤ ((145242632663487421:ℝ)/100000000000000) := by
  set t := q - ((79:ℝ)/20) with htd
  have hq : q = ((79:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece12_L3 piece12_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((79:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_02 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_02; ring
  have h12 : centralNum12_02 q = ∑ e ∈ Finset.range 13, ([((283712117303050252274799:ℝ)/2048000000000000), ((-93254281117533362170953:ℝ)/102400000000000), ((-17581993738909563239901:ℝ)/5120000000000), ((-257811444621804737871:ℝ)/51200000000), ((-1373819000580860463:ℝ)/320000000), ((-772679581027336629:ℝ)/320000000), ((-15146328649108797:ℝ)/16000000), ((-211701026232819:ℝ)/800000), ((-844807184109:ℝ)/16000), ((-5897972601:ℝ)/800), ((-137232441:ℝ)/200), ((-383103:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_02; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((283712117303050252274799:ℝ)/2048000000000000), ((-93254281117533362170953:ℝ)/102400000000000), ((-17581993738909563239901:ℝ)/5120000000000), ((-257811444621804737871:ℝ)/51200000000), ((-1373819000580860463:ℝ)/320000000), ((-772679581027336629:ℝ)/320000000), ((-15146328649108797:ℝ)/16000000), ((-211701026232819:ℝ)/800000), ((-844807184109:ℝ)/16000), ((-5897972601:ℝ)/800), ((-137232441:ℝ)/200), ((-383103:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((283712117303050252274799:ℝ)/2048000000000000), ((-93254281117533362170953:ℝ)/102400000000000), ((-17581993738909563239901:ℝ)/5120000000000), ((-257811444621804737871:ℝ)/51200000000), ((-1373819000580860463:ℝ)/320000000), ((-772679581027336629:ℝ)/320000000), ((-15146328649108797:ℝ)/16000000), ((-211701026232819:ℝ)/800000), ((-844807184109:ℝ)/16000), ((-5897972601:ℝ)/800), ((-137232441:ℝ)/200), ((-383103:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((283712117303050252274799:ℝ)/2048000000000000), ((-93254281117533362170953:ℝ)/102400000000000), ((-17581993738909563239901:ℝ)/5120000000000), ((-257811444621804737871:ℝ)/51200000000), ((-1373819000580860463:ℝ)/320000000), ((-772679581027336629:ℝ)/320000000), ((-15146328649108797:ℝ)/16000000), ((-211701026232819:ℝ)/800000), ((-844807184109:ℝ)/16000), ((-5897972601:ℝ)/800), ((-137232441:ℝ)/200), ((-383103:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e) - ((283712117303050252274799:ℝ)/2048000000000000) - ((-93254281117533362170953:ℝ)/102400000000000)*t| ≤ ((9463789900758445051923:ℝ)/1024000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((283712117303050252274799:ℝ)/2048000000000000), ((-93254281117533362170953:ℝ)/102400000000000), ((-17581993738909563239901:ℝ)/5120000000000), ((-257811444621804737871:ℝ)/51200000000), ((-1373819000580860463:ℝ)/320000000), ((-772679581027336629:ℝ)/320000000), ((-15146328649108797:ℝ)/16000000), ((-211701026232819:ℝ)/800000), ((-844807184109:ℝ)/16000), ((-5897972601:ℝ)/800), ((-137232441:ℝ)/200), ((-383103:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((197946989111050252274799:ℝ)/1024000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((46108585475767759:ℝ)/16000000000) - ((5967553945585029:ℝ)/800000000)*t| ≤ ((88165144661803:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (4:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82080:ℝ), (-967680:ℝ), (3257600:ℝ), (-4474880:ℝ), (2908160:ℝ), (-786432:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_02 q| ≤ (31002821394432:ℝ) := by
    rw [centralNum13_02_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (4:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (87660:ℝ), (-702180:ℝ), ((7421435:ℝ)/4), ((-10854125:ℝ)/4), ((2828125:ℝ)/2), (-187500:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_02 q| ≤ (12455905198080:ℝ) := by
    rw [centralNum23_02_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((70042178050639083684723132989:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece12_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece12_E11 h0) m23'
  have c5 := scaled_affine (X := ((867738853991:ℝ)/100000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((283712117303050252274799:ℝ)/2048000000000000) + ((46108585475767759:ℝ)/16000000000)*((867738853991:ℝ)/100000000000000) - ((329177026029719493:ℝ)/10000000000000)) (β := (0:ℝ) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((-93254281117533362170953:ℝ)/102400000000000) - 3*((283712117303050252274799:ℝ)/2048000000000000)) + ((5967553945585029:ℝ)/800000000)*((867738853991:ℝ)/100000000000000) - ((-27533621446419653:ℝ)/2500000000000)) ht
  have hW : pieceW q pieceX_12 0 2 = centralNum11_02 q + 8*(Real.exp (-(3*((79:ℝ)/20)))*Real.exp (-3*t))*centralNum12_02 q + 18*Real.exp (-8*q)*centralNum13_02 q + 72*Real.exp (-11*q)*centralNum23_02 q + 8*q^7*(2*q-3)^2*((867738853991:ℝ)/100000000000000) + (0:ℝ) := by
    rw [pieceW_02, pieceX_12, sym4_02, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((21555953529135826982585401521445757684502032645668838958167645786341:ℝ)/1569885042486776012538847755766948135862644926266609635325920000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((283712117303050252274799:ℝ)/2048000000000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((-93254281117533362170953:ℝ)/102400000000000) - 3*((283712117303050252274799:ℝ)/2048000000000000))*t) + (((46108585475767759:ℝ)/16000000000) + ((5967553945585029:ℝ)/800000000)*t)*((867738853991:ℝ)/100000000000000) - (((329177026029719493:ℝ)/10000000000000) + t * ((-27533621446419653:ℝ)/2500000000000)) = ((0:ℝ) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((283712117303050252274799:ℝ)/2048000000000000) + ((46108585475767759:ℝ)/16000000000)*((867738853991:ℝ)/100000000000000) - ((329177026029719493:ℝ)/10000000000000)) + t*((0:ℝ) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((-93254281117533362170953:ℝ)/102400000000000) - 3*((283712117303050252274799:ℝ)/2048000000000000)) + ((5967553945585029:ℝ)/800000000)*((867738853991:ℝ)/100000000000000) - ((-27533621446419653:ℝ)/2500000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece12_e03 {q : ℝ} (h0 : ((39:ℝ)/10) ≤ q) (h1 : q ≤ (4:ℝ)) :
    |pieceW q pieceX_12 0 3 - (((-112446636098754597:ℝ)/1000000000000) + (q - ((79:ℝ)/20)) * ((-565255496982561493:ℝ)/1000000000000))| ≤ ((103000287559184559:ℝ)/10000000000000) := by
  set t := q - ((79:ℝ)/20) with htd
  have hq : q = ((79:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece12_L3 piece12_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((79:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_03 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_03; ring
  have h12 : centralNum12_03 q = ∑ e ∈ Finset.range 14, ([((1232776318558560297494027949:ℝ)/573440000000000000), ((51701761000879284507860547:ℝ)/7168000000000000), ((1828132104075339886652709:ℝ)/179200000000000), ((275521877561122898254893:ℝ)/35840000000000), ((2079631879967781249057:ℝ)/716800000000), ((-3731797513818488619:ℝ)/89600000000), ((-750035996165938977:ℝ)/1120000000), ((-44418357914167071:ℝ)/112000000), ((-2972847803484537:ℝ)/22400000), ((-102247163163:ℝ)/3500), ((-7582060323:ℝ)/1750), ((-587641311:ℝ)/1400), ((-3375513:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_03; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((1232776318558560297494027949:ℝ)/573440000000000000), ((51701761000879284507860547:ℝ)/7168000000000000), ((1828132104075339886652709:ℝ)/179200000000000), ((275521877561122898254893:ℝ)/35840000000000), ((2079631879967781249057:ℝ)/716800000000), ((-3731797513818488619:ℝ)/89600000000), ((-750035996165938977:ℝ)/1120000000), ((-44418357914167071:ℝ)/112000000), ((-2972847803484537:ℝ)/22400000), ((-102247163163:ℝ)/3500), ((-7582060323:ℝ)/1750), ((-587641311:ℝ)/1400), ((-3375513:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((1232776318558560297494027949:ℝ)/573440000000000000), ((51701761000879284507860547:ℝ)/7168000000000000), ((1828132104075339886652709:ℝ)/179200000000000), ((275521877561122898254893:ℝ)/35840000000000), ((2079631879967781249057:ℝ)/716800000000), ((-3731797513818488619:ℝ)/89600000000), ((-750035996165938977:ℝ)/1120000000), ((-44418357914167071:ℝ)/112000000), ((-2972847803484537:ℝ)/22400000), ((-102247163163:ℝ)/3500), ((-7582060323:ℝ)/1750), ((-587641311:ℝ)/1400), ((-3375513:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((1232776318558560297494027949:ℝ)/573440000000000000), ((51701761000879284507860547:ℝ)/7168000000000000), ((1828132104075339886652709:ℝ)/179200000000000), ((275521877561122898254893:ℝ)/35840000000000), ((2079631879967781249057:ℝ)/716800000000), ((-3731797513818488619:ℝ)/89600000000), ((-750035996165938977:ℝ)/1120000000), ((-44418357914167071:ℝ)/112000000), ((-2972847803484537:ℝ)/22400000), ((-102247163163:ℝ)/3500), ((-7582060323:ℝ)/1750), ((-587641311:ℝ)/1400), ((-3375513:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((1232776318558560297494027949:ℝ)/573440000000000000) - ((51701761000879284507860547:ℝ)/7168000000000000)*t| ≤ ((15186512391687043117423623:ℝ)/573440000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((1232776318558560297494027949:ℝ)/573440000000000000), ((51701761000879284507860547:ℝ)/7168000000000000), ((1828132104075339886652709:ℝ)/179200000000000), ((275521877561122898254893:ℝ)/35840000000000), ((2079631879967781249057:ℝ)/716800000000), ((-3731797513818488619:ℝ)/89600000000), ((-750035996165938977:ℝ)/1120000000), ((-44418357914167071:ℝ)/112000000), ((-2972847803484537:ℝ)/22400000), ((-102247163163:ℝ)/3500), ((-7582060323:ℝ)/1750), ((-587641311:ℝ)/1400), ((-3375513:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((4546155859230513995759043:ℝ)/1792000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((46108585475767759:ℝ)/16000000000) - ((5967553945585029:ℝ)/800000000)*t| ≤ ((88165144661803:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (4:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-812160:ℝ), (8985600:ℝ), (-32225280:ℝ), (52019200:ℝ), ((-305233920:ℝ)/7), ((135528448:ℝ)/7), ((-25165824:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_03 q| ≤ ((5688055304290304:ℝ)/7) := by
    rw [centralNum13_03_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (4:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-833220:ℝ), (6469740:ℝ), ((-68603955:ℝ)/4), ((104396875:ℝ)/4), ((-1001334375:ℝ)/56), ((125828125:ℝ)/28), ((-2343750:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_03 q| ≤ ((1436140273664000:ℝ)/7) := by
    rw [centralNum23_03_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((70042178050639083684723132989:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece12_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece12_E11 h0) m23'
  have c5 := scaled_affine (X := ((-408111547811:ℝ)/5000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((1232776318558560297494027949:ℝ)/573440000000000000) + ((46108585475767759:ℝ)/16000000000)*((-408111547811:ℝ)/5000000000000) - ((-112446636098754597:ℝ)/1000000000000)) (β := (0:ℝ) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((51701761000879284507860547:ℝ)/7168000000000000) - 3*((1232776318558560297494027949:ℝ)/573440000000000000)) + ((5967553945585029:ℝ)/800000000)*((-408111547811:ℝ)/5000000000000) - ((-565255496982561493:ℝ)/1000000000000)) ht
  have hW : pieceW q pieceX_12 0 3 = centralNum11_03 q + 8*(Real.exp (-(3*((79:ℝ)/20)))*Real.exp (-3*t))*centralNum12_03 q + 18*Real.exp (-8*q)*centralNum13_03 q + 72*Real.exp (-11*q)*centralNum23_03 q + 8*q^7*(2*q-3)^2*((-408111547811:ℝ)/5000000000000) + (0:ℝ) := by
    rw [pieceW_03, pieceX_12, sym4_03, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((633076156356472783232748043541667645330189635021101766221749926270597:ℝ)/1373649412175929010971491786296079618879814310483283430910180000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((1232776318558560297494027949:ℝ)/573440000000000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((51701761000879284507860547:ℝ)/7168000000000000) - 3*((1232776318558560297494027949:ℝ)/573440000000000000))*t) + (((46108585475767759:ℝ)/16000000000) + ((5967553945585029:ℝ)/800000000)*t)*((-408111547811:ℝ)/5000000000000) - (((-112446636098754597:ℝ)/1000000000000) + t * ((-565255496982561493:ℝ)/1000000000000)) = ((0:ℝ) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((1232776318558560297494027949:ℝ)/573440000000000000) + ((46108585475767759:ℝ)/16000000000)*((-408111547811:ℝ)/5000000000000) - ((-112446636098754597:ℝ)/1000000000000)) + t*((0:ℝ) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((51701761000879284507860547:ℝ)/7168000000000000) - 3*((1232776318558560297494027949:ℝ)/573440000000000000)) + ((5967553945585029:ℝ)/800000000)*((-408111547811:ℝ)/5000000000000) - ((-565255496982561493:ℝ)/1000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece12_e11 {q : ℝ} (h0 : ((39:ℝ)/10) ≤ q) (h1 : q ≤ (4:ℝ)) :
    |pieceW q pieceX_12 1 1 - (((73382031441816239:ℝ)/25000000000) + (q - ((79:ℝ)/20)) * ((323563734773396967:ℝ)/50000000000))| ≤ ((49163115552066389:ℝ)/2500000000000) := by
  set t := q - ((79:ℝ)/20) with htd
  have hq : q = ((79:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece12_L3 piece12_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((79:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_11 q = ∑ e ∈ Finset.range 10, ([((8443156592610893:ℝ)/3000000000), ((2558624705727283:ℝ)/400000000), ((32923218116627:ℝ)/5000000), ((1007733751997:ℝ)/250000), ((20199601877:ℝ)/12500), ((548972501:ℝ)/1250), ((10089492:ℝ)/125), ((241168:ℝ)/25), ((3392:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_11; ring
  have h12 : centralNum12_11 q = ∑ e ∈ Finset.range 13, ([((1577919190040992389352159:ℝ)/1536000000000000), ((40181397360286785998029:ℝ)/25600000000000), ((-549879147498650358367:ℝ)/1280000000000), ((-38734224774859374917:ℝ)/12800000000), ((-284010436518355081:ℝ)/80000000), ((-186091598220902263:ℝ)/80000000), ((-4003969576254879:ℝ)/4000000), ((-59694537609073:ℝ)/200000), ((-250023975743:ℝ)/4000), ((-5440759561:ℝ)/600), ((-43543827:ℝ)/50), ((-249642:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_11; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((8443156592610893:ℝ)/3000000000), ((2558624705727283:ℝ)/400000000), ((32923218116627:ℝ)/5000000), ((1007733751997:ℝ)/250000), ((20199601877:ℝ)/12500), ((548972501:ℝ)/1250), ((10089492:ℝ)/125), ((241168:ℝ)/25), ((3392:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((1577919190040992389352159:ℝ)/1536000000000000), ((40181397360286785998029:ℝ)/25600000000000), ((-549879147498650358367:ℝ)/1280000000000), ((-38734224774859374917:ℝ)/12800000000), ((-284010436518355081:ℝ)/80000000), ((-186091598220902263:ℝ)/80000000), ((-4003969576254879:ℝ)/4000000), ((-59694537609073:ℝ)/200000), ((-250023975743:ℝ)/4000), ((-5440759561:ℝ)/600), ((-43543827:ℝ)/50), ((-249642:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((1577919190040992389352159:ℝ)/1536000000000000), ((40181397360286785998029:ℝ)/25600000000000), ((-549879147498650358367:ℝ)/1280000000000), ((-38734224774859374917:ℝ)/12800000000), ((-284010436518355081:ℝ)/80000000), ((-186091598220902263:ℝ)/80000000), ((-4003969576254879:ℝ)/4000000), ((-59694537609073:ℝ)/200000), ((-250023975743:ℝ)/4000), ((-5440759561:ℝ)/600), ((-43543827:ℝ)/50), ((-249642:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((8443156592610893:ℝ)/3000000000), ((2558624705727283:ℝ)/400000000), ((32923218116627:ℝ)/5000000), ((1007733751997:ℝ)/250000), ((20199601877:ℝ)/12500), ((548972501:ℝ)/1250), ((10089492:ℝ)/125), ((241168:ℝ)/25), ((3392:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((8443156592610893:ℝ)/3000000000) + ((2558624705727283:ℝ)/400000000)*t)| ≤ ((407417141931007:ℝ)/24000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((1577919190040992389352159:ℝ)/1536000000000000), ((40181397360286785998029:ℝ)/25600000000000), ((-549879147498650358367:ℝ)/1280000000000), ((-38734224774859374917:ℝ)/12800000000), ((-284010436518355081:ℝ)/80000000), ((-186091598220902263:ℝ)/80000000), ((-4003969576254879:ℝ)/4000000), ((-59694537609073:ℝ)/200000), ((-250023975743:ℝ)/4000), ((-5440759561:ℝ)/600), ((-43543827:ℝ)/50), ((-249642:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e) - ((1577919190040992389352159:ℝ)/1536000000000000) - ((40181397360286785998029:ℝ)/25600000000000)*t| ≤ ((1132936500926373673123:ℝ)/768000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((1577919190040992389352159:ℝ)/1536000000000000), ((40181397360286785998029:ℝ)/25600000000000), ((-549879147498650358367:ℝ)/1280000000000), ((-38734224774859374917:ℝ)/12800000000), ((-284010436518355081:ℝ)/80000000), ((-186091598220902263:ℝ)/80000000), ((-4003969576254879:ℝ)/4000000), ((-59694537609073:ℝ)/200000), ((-250023975743:ℝ)/4000), ((-5440759561:ℝ)/600), ((-43543827:ℝ)/50), ((-249642:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((141727437926975457891041:ℝ)/128000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((46108585475767759:ℝ)/16000000000) - ((5967553945585029:ℝ)/800000000)*t| ≤ ((88165144661803:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (4:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-3444:ℝ), (162624:ℝ), (-1531216:ℝ), (4800960:ℝ), (-6350848:ℝ), ((12025856:ℝ)/3), (-1048576:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_11 q| ≤ ((127279407939584:ℝ)/3) := by
    rw [centralNum13_11_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (4:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-4074:ℝ), (159906:ℝ), (-1104799:ℝ), (2801499:ℝ), (-3931375:ℝ), ((5896250:ℝ)/3), (-250000:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_11 q| ≤ ((52108923920384:ℝ)/3) := by
    rw [centralNum23_11_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((70042178050639083684723132989:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece12_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece12_E11 h0) m23'
  have c5 := scaled_affine (X := ((107968838179:ℝ)/5000000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1))| ≤ ((358567126958080000000000000000000:ℝ)/40171799139602044830579860077923579) := by
    rw [abs_neg, tailWeight_1, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ (4:ℝ)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*(4:ℝ)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece12_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((4814744136400:ℝ)/531441)) ≤ (4:ℝ)^6*(8000*(2*(4:ℝ)-3)^2*(1/((831493600485514841979407800409:ℝ)/1000000000000))*((4814744136400:ℝ)/531441)) := by
          gcongr
      _ ≤ ((358567126958080000000000000000000:ℝ)/40171799139602044830579860077923579) := by norm_num
  have c7 := affine_round (α := ((8443156592610893:ℝ)/3000000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((1577919190040992389352159:ℝ)/1536000000000000) + ((46108585475767759:ℝ)/16000000000)*((107968838179:ℝ)/5000000000000) - ((73382031441816239:ℝ)/25000000000)) (β := ((2558624705727283:ℝ)/400000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((40181397360286785998029:ℝ)/25600000000000) - 3*((1577919190040992389352159:ℝ)/1536000000000000)) + ((5967553945585029:ℝ)/800000000)*((107968838179:ℝ)/5000000000000) - ((323563734773396967:ℝ)/50000000000)) ht
  have hW : pieceW q pieceX_12 1 1 = centralNum11_11 q + 8*(Real.exp (-(3*((79:ℝ)/20)))*Real.exp (-3*t))*centralNum12_11 q + 18*Real.exp (-8*q)*centralNum13_11 q + 72*Real.exp (-11*q)*centralNum23_11 q + 8*q^7*(2*q-3)^2*((107968838179:ℝ)/5000000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1)) := by
    rw [pieceW_11, pieceX_12, sym4_11, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((1118627709816561379464016162458769019457723713584887007314153115150987:ℝ)/235482756373016401880827163365042220379396738939991445298888000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((8443156592610893:ℝ)/3000000000) + ((2558624705727283:ℝ)/400000000)*t) + (8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((1577919190040992389352159:ℝ)/1536000000000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((40181397360286785998029:ℝ)/25600000000000) - 3*((1577919190040992389352159:ℝ)/1536000000000000))*t) + (((46108585475767759:ℝ)/16000000000) + ((5967553945585029:ℝ)/800000000)*t)*((107968838179:ℝ)/5000000000000) - (((73382031441816239:ℝ)/25000000000) + t * ((323563734773396967:ℝ)/50000000000)) = (((8443156592610893:ℝ)/3000000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((1577919190040992389352159:ℝ)/1536000000000000) + ((46108585475767759:ℝ)/16000000000)*((107968838179:ℝ)/5000000000000) - ((73382031441816239:ℝ)/25000000000)) + t*(((2558624705727283:ℝ)/400000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((40181397360286785998029:ℝ)/25600000000000) - 3*((1577919190040992389352159:ℝ)/1536000000000000)) + ((5967553945585029:ℝ)/800000000)*((107968838179:ℝ)/5000000000000) - ((323563734773396967:ℝ)/50000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece12_e12 {q : ℝ} (h0 : ((39:ℝ)/10) ≤ q) (h1 : q ≤ (4:ℝ)) :
    |pieceW q pieceX_12 1 2 - (((-90983402398200443:ℝ)/500000000000) + (q - ((79:ℝ)/20)) * ((-43072035642634809:ℝ)/125000000000))| ≤ ((19834445401425567:ℝ)/1000000000000) := by
  set t := q - ((79:ℝ)/20) with htd
  have hq : q = ((79:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece12_L3 piece12_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((79:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_12 q = ∑ e ∈ Finset.range 9, ([((-845701257757559:ℝ)/1920000000), ((-17394599823547:ℝ)/24000000), ((-548923491533:ℝ)/1200000), ((-7174210489:ℝ)/60000), ((4162747:ℝ)/1200), ((1538051:ℝ)/150), ((39854:ℝ)/15), ((904:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_12; ring
  have h12 : centralNum12_12 q = ∑ e ∈ Finset.range 14, ([((915537286777933886509519469:ℝ)/245760000000000000), ((48413560242679404977347987:ℝ)/3072000000000000), ((2084988305813728723730749:ℝ)/76800000000000), ((395036059980898943447693:ℝ)/15360000000000), ((4493656702574329333537:ℝ)/307200000000), ((183002092631703069461:ℝ)/38400000000), ((226964025303549583:ℝ)/480000000), ((-15702641395300031:ℝ)/48000000), ((-1778624929502137:ℝ)/9600000), ((-12541088993:ℝ)/250), ((-2094959271:ℝ)/250), ((-175995477:ℝ)/200), ((-1073331:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_12; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-845701257757559:ℝ)/1920000000), ((-17394599823547:ℝ)/24000000), ((-548923491533:ℝ)/1200000), ((-7174210489:ℝ)/60000), ((4162747:ℝ)/1200), ((1538051:ℝ)/150), ((39854:ℝ)/15), ((904:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((915537286777933886509519469:ℝ)/245760000000000000), ((48413560242679404977347987:ℝ)/3072000000000000), ((2084988305813728723730749:ℝ)/76800000000000), ((395036059980898943447693:ℝ)/15360000000000), ((4493656702574329333537:ℝ)/307200000000), ((183002092631703069461:ℝ)/38400000000), ((226964025303549583:ℝ)/480000000), ((-15702641395300031:ℝ)/48000000), ((-1778624929502137:ℝ)/9600000), ((-12541088993:ℝ)/250), ((-2094959271:ℝ)/250), ((-175995477:ℝ)/200), ((-1073331:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((915537286777933886509519469:ℝ)/245760000000000000), ((48413560242679404977347987:ℝ)/3072000000000000), ((2084988305813728723730749:ℝ)/76800000000000), ((395036059980898943447693:ℝ)/15360000000000), ((4493656702574329333537:ℝ)/307200000000), ((183002092631703069461:ℝ)/38400000000), ((226964025303549583:ℝ)/480000000), ((-15702641395300031:ℝ)/48000000), ((-1778624929502137:ℝ)/9600000), ((-12541088993:ℝ)/250), ((-2094959271:ℝ)/250), ((-175995477:ℝ)/200), ((-1073331:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((-845701257757559:ℝ)/1920000000), ((-17394599823547:ℝ)/24000000), ((-548923491533:ℝ)/1200000), ((-7174210489:ℝ)/60000), ((4162747:ℝ)/1200), ((1538051:ℝ)/150), ((39854:ℝ)/15), ((904:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((-845701257757559:ℝ)/1920000000) + ((-17394599823547:ℝ)/24000000)*t)| ≤ ((2224438667923:ℝ)/1920000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((915537286777933886509519469:ℝ)/245760000000000000), ((48413560242679404977347987:ℝ)/3072000000000000), ((2084988305813728723730749:ℝ)/76800000000000), ((395036059980898943447693:ℝ)/15360000000000), ((4493656702574329333537:ℝ)/307200000000), ((183002092631703069461:ℝ)/38400000000), ((226964025303549583:ℝ)/480000000), ((-15702641395300031:ℝ)/48000000), ((-1778624929502137:ℝ)/9600000), ((-12541088993:ℝ)/250), ((-2094959271:ℝ)/250), ((-175995477:ℝ)/200), ((-1073331:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e) - ((915537286777933886509519469:ℝ)/245760000000000000) - ((48413560242679404977347987:ℝ)/3072000000000000)*t| ≤ ((3498562946899087346960143:ℝ)/49152000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((915537286777933886509519469:ℝ)/245760000000000000), ((48413560242679404977347987:ℝ)/3072000000000000), ((2084988305813728723730749:ℝ)/76800000000000), ((395036059980898943447693:ℝ)/15360000000000), ((4493656702574329333537:ℝ)/307200000000), ((183002092631703069461:ℝ)/38400000000), ((226964025303549583:ℝ)/480000000), ((-15702641395300031:ℝ)/48000000), ((-1778624929502137:ℝ)/9600000), ((-12541088993:ℝ)/250), ((-2094959271:ℝ)/250), ((-175995477:ℝ)/200), ((-1073331:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((281671085620786735788428033:ℝ)/61440000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((46108585475767759:ℝ)/16000000000) - ((5967553945585029:ℝ)/800000000)*t| ≤ ((88165144661803:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (4:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (122790:ℝ), (-3586680:ℝ), (28529720:ℝ), (-90761600:ℝ), (137804800:ℝ), ((-332136448:ℝ)/3), ((141819904:ℝ)/3), (-8388608:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_12 q| ≤ ((5971935472197632:ℝ)/3) := by
    rw [centralNum13_12_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (4:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (132555:ℝ), (-3252375:ℝ), ((39743695:ℝ)/2), ((-197111615:ℝ)/4), ((281947375:ℝ)/4), ((-1100234375:ℝ)/24), ((131828125:ℝ)/12), (-781250:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_12 q| ≤ ((1551607924183040:ℝ)/3) := by
    rw [centralNum23_12_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((70042178050639083684723132989:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece12_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece12_E11 h0) m23'
  have c5 := scaled_affine (X := ((158770955539:ℝ)/10000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-845701257757559:ℝ)/1920000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((915537286777933886509519469:ℝ)/245760000000000000) + ((46108585475767759:ℝ)/16000000000)*((158770955539:ℝ)/10000000000000) - ((-90983402398200443:ℝ)/500000000000)) (β := ((-17394599823547:ℝ)/24000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((48413560242679404977347987:ℝ)/3072000000000000) - 3*((915537286777933886509519469:ℝ)/245760000000000000)) + ((5967553945585029:ℝ)/800000000)*((158770955539:ℝ)/10000000000000) - ((-43072035642634809:ℝ)/125000000000)) ht
  have hW : pieceW q pieceX_12 1 2 = centralNum11_12 q + 8*(Real.exp (-(3*((79:ℝ)/20)))*Real.exp (-3*t))*centralNum12_12 q + 18*Real.exp (-8*q)*centralNum13_12 q + 72*Real.exp (-11*q)*centralNum23_12 q + 8*q^7*(2*q-3)^2*((158770955539:ℝ)/10000000000000) + (0:ℝ) := by
    rw [pieceW_12, pieceX_12, sym4_12, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((170519408452168052575877372936636452555489263998353198636501764028933:ℝ)/470965512746032803761654326730084440758793477879982890597776000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-845701257757559:ℝ)/1920000000) + ((-17394599823547:ℝ)/24000000)*t) + (8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((915537286777933886509519469:ℝ)/245760000000000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((48413560242679404977347987:ℝ)/3072000000000000) - 3*((915537286777933886509519469:ℝ)/245760000000000000))*t) + (((46108585475767759:ℝ)/16000000000) + ((5967553945585029:ℝ)/800000000)*t)*((158770955539:ℝ)/10000000000000) - (((-90983402398200443:ℝ)/500000000000) + t * ((-43072035642634809:ℝ)/125000000000)) = (((-845701257757559:ℝ)/1920000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((915537286777933886509519469:ℝ)/245760000000000000) + ((46108585475767759:ℝ)/16000000000)*((158770955539:ℝ)/10000000000000) - ((-90983402398200443:ℝ)/500000000000)) + t*(((-17394599823547:ℝ)/24000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((48413560242679404977347987:ℝ)/3072000000000000) - 3*((915537286777933886509519469:ℝ)/245760000000000000)) + ((5967553945585029:ℝ)/800000000)*((158770955539:ℝ)/10000000000000) - ((-43072035642634809:ℝ)/125000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece12_e13 {q : ℝ} (h0 : ((39:ℝ)/10) ≤ q) (h1 : q ≤ (4:ℝ)) :
    |pieceW q pieceX_12 1 3 - (((897881223093624777:ℝ)/1000000000000) + (q - ((79:ℝ)/20)) * ((53054555286123291:ℝ)/12500000000))| ≤ ((37573053742016169:ℝ)/500000000000) := by
  set t := q - ((79:ℝ)/20) with htd
  have hq : q = ((79:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece12_L3 piece12_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((79:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_13 q = ∑ e ∈ Finset.range 7, ([((-729262366563:ℝ)/3200000), ((-27693507591:ℝ)/80000), ((-350550729:ℝ)/1600), ((-1479117:ℝ)/20), ((-56169:ℝ)/4), (-1422:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_13; ring
  have h12 : centralNum12_13 q = ∑ e ∈ Finset.range 15, ([((-237434246573064476126006351427:ℝ)/22937600000000000000), ((-32676821667291741579565328877:ℝ)/1146880000000000000), ((-407223901992962807308991073:ℝ)/14336000000000000), ((-9417726316792116913872831:ℝ)/1433600000000000), ((1701439147314429308302803:ℝ)/143360000000000), ((14187264881107786861647:ℝ)/1024000000000), ((1352464684613177024427:ℝ)/179200000000), ((10930990547476093971:ℝ)/4480000000), ((398818347364953699:ℝ)/896000000), ((849034883406069:ℝ)/44800000), ((-1713909822147:ℝ)/140000), ((-194284618551:ℝ)/56000), ((-364637781:ℝ)/800), ((-8859537:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_13; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-729262366563:ℝ)/3200000), ((-27693507591:ℝ)/80000), ((-350550729:ℝ)/1600), ((-1479117:ℝ)/20), ((-56169:ℝ)/4), (-1422:ℝ), (-60:ℝ)] : List ℝ).getD e 0) 5 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-237434246573064476126006351427:ℝ)/22937600000000000000), ((-32676821667291741579565328877:ℝ)/1146880000000000000), ((-407223901992962807308991073:ℝ)/14336000000000000), ((-9417726316792116913872831:ℝ)/1433600000000000), ((1701439147314429308302803:ℝ)/143360000000000), ((14187264881107786861647:ℝ)/1024000000000), ((1352464684613177024427:ℝ)/179200000000), ((10930990547476093971:ℝ)/4480000000), ((398818347364953699:ℝ)/896000000), ((849034883406069:ℝ)/44800000), ((-1713909822147:ℝ)/140000), ((-194284618551:ℝ)/56000), ((-364637781:ℝ)/800), ((-8859537:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-237434246573064476126006351427:ℝ)/22937600000000000000), ((-32676821667291741579565328877:ℝ)/1146880000000000000), ((-407223901992962807308991073:ℝ)/14336000000000000), ((-9417726316792116913872831:ℝ)/1433600000000000), ((1701439147314429308302803:ℝ)/143360000000000), ((14187264881107786861647:ℝ)/1024000000000), ((1352464684613177024427:ℝ)/179200000000), ((10930990547476093971:ℝ)/4480000000), ((398818347364953699:ℝ)/896000000), ((849034883406069:ℝ)/44800000), ((-1713909822147:ℝ)/140000), ((-194284618551:ℝ)/56000), ((-364637781:ℝ)/800), ((-8859537:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 7, ([((-729262366563:ℝ)/3200000), ((-27693507591:ℝ)/80000), ((-350550729:ℝ)/1600), ((-1479117:ℝ)/20), ((-56169:ℝ)/4), (-1422:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e) - (((-729262366563:ℝ)/3200000) + ((-27693507591:ℝ)/80000)*t)| ≤ ((356523651:ℝ)/640000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-237434246573064476126006351427:ℝ)/22937600000000000000), ((-32676821667291741579565328877:ℝ)/1146880000000000000), ((-407223901992962807308991073:ℝ)/14336000000000000), ((-9417726316792116913872831:ℝ)/1433600000000000), ((1701439147314429308302803:ℝ)/143360000000000), ((14187264881107786861647:ℝ)/1024000000000), ((1352464684613177024427:ℝ)/179200000000), ((10930990547476093971:ℝ)/4480000000), ((398818347364953699:ℝ)/896000000), ((849034883406069:ℝ)/44800000), ((-1713909822147:ℝ)/140000), ((-194284618551:ℝ)/56000), ((-364637781:ℝ)/800), ((-8859537:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((-237434246573064476126006351427:ℝ)/22937600000000000000) - ((-32676821667291741579565328877:ℝ)/1146880000000000000)*t| ≤ ((58911948559283723538377049:ℝ)/819200000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-237434246573064476126006351427:ℝ)/22937600000000000000), ((-32676821667291741579565328877:ℝ)/1146880000000000000), ((-407223901992962807308991073:ℝ)/14336000000000000), ((-9417726316792116913872831:ℝ)/1433600000000000), ((1701439147314429308302803:ℝ)/143360000000000), ((14187264881107786861647:ℝ)/1024000000000), ((1352464684613177024427:ℝ)/179200000000), ((10930990547476093971:ℝ)/4480000000), ((398818347364953699:ℝ)/896000000), ((849034883406069:ℝ)/44800000), ((-1713909822147:ℝ)/140000), ((-194284618551:ℝ)/56000), ((-364637781:ℝ)/800), ((-8859537:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((67940150700004040491161559419:ℝ)/5734400000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((46108585475767759:ℝ)/16000000000) - ((5967553945585029:ℝ)/800000000)*t| ≤ ((88165144661803:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (4:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2325540:ℝ), (52589280:ℝ), (-375655200:ℝ), (1192958720:ℝ), (-1965096960:ℝ), ((12857851904:ℝ)/7), ((-21171273728:ℝ)/21), ((914358272:ℝ)/3), ((-268435456:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_13 q| ≤ ((1213062029848821760:ℝ)/21) := by
    rw [centralNum13_13_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (4:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2399070:ℝ), (45666930:ℝ), (-251781675:ℝ), ((2452738385:ℝ)/4), ((-14104310625:ℝ)/16), ((74345740625:ℝ)/112), ((-74899765625:ℝ)/336), ((5161328125:ℝ)/168), ((-9765625:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_13 q| ≤ ((211315817319424000:ℝ)/21) := by
    rw [centralNum23_13_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((70042178050639083684723132989:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece12_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece12_E11 h0) m23'
  have c5 := scaled_affine (X := ((297892288439:ℝ)/500000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-729262366563:ℝ)/3200000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((-237434246573064476126006351427:ℝ)/22937600000000000000) + ((46108585475767759:ℝ)/16000000000)*((297892288439:ℝ)/500000000000) - ((897881223093624777:ℝ)/1000000000000)) (β := ((-27693507591:ℝ)/80000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((-32676821667291741579565328877:ℝ)/1146880000000000000) - 3*((-237434246573064476126006351427:ℝ)/22937600000000000000)) + ((5967553945585029:ℝ)/800000000)*((297892288439:ℝ)/500000000000) - ((53054555286123291:ℝ)/12500000000)) ht
  have hW : pieceW q pieceX_12 1 3 = centralNum11_13 q + 8*(Real.exp (-(3*((79:ℝ)/20)))*Real.exp (-3*t))*centralNum12_13 q + 18*Real.exp (-8*q)*centralNum13_13 q + 72*Real.exp (-11*q)*centralNum23_13 q + 8*q^7*(2*q-3)^2*((297892288439:ℝ)/500000000000) + (0:ℝ) := by
    rw [pieceW_13, pieceX_12, sym4_13, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((30798624475549608625542109078216084631016987684043212750146370648877:ℝ)/54945976487037160438859671451843184755192572419331337236407200000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-729262366563:ℝ)/3200000) + ((-27693507591:ℝ)/80000)*t) + (8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((-237434246573064476126006351427:ℝ)/22937600000000000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((-32676821667291741579565328877:ℝ)/1146880000000000000) - 3*((-237434246573064476126006351427:ℝ)/22937600000000000000))*t) + (((46108585475767759:ℝ)/16000000000) + ((5967553945585029:ℝ)/800000000)*t)*((297892288439:ℝ)/500000000000) - (((897881223093624777:ℝ)/1000000000000) + t * ((53054555286123291:ℝ)/12500000000)) = (((-729262366563:ℝ)/3200000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((-237434246573064476126006351427:ℝ)/22937600000000000000) + ((46108585475767759:ℝ)/16000000000)*((297892288439:ℝ)/500000000000) - ((897881223093624777:ℝ)/1000000000000)) + t*(((-27693507591:ℝ)/80000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((-32676821667291741579565328877:ℝ)/1146880000000000000) - 3*((-237434246573064476126006351427:ℝ)/22937600000000000000)) + ((5967553945585029:ℝ)/800000000)*((297892288439:ℝ)/500000000000) - ((53054555286123291:ℝ)/12500000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece12_e22 {q : ℝ} (h0 : ((39:ℝ)/10) ≤ q) (h1 : q ≤ (4:ℝ)) :
    |pieceW q pieceX_12 2 2 - (((148871056600675261:ℝ)/50000000000) + (q - ((79:ℝ)/20)) * ((104047213136618921:ℝ)/10000000000))| ≤ ((75736086379010643:ℝ)/500000000000) := by
  set t := q - ((79:ℝ)/20) with htd
  have hq : q = ((79:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece12_L3 piece12_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((79:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_22 q = ∑ e ∈ Finset.range 10, ([((44537902036898209:ℝ)/19200000000), ((5455356485426929:ℝ)/960000000), ((74001357006661:ℝ)/12000000), ((784860652077:ℝ)/200000), ((97480229287:ℝ)/60000), ((1367570683:ℝ)/3000), ((2171683:ℝ)/25), ((162556:ℝ)/15), ((2404:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_22; ring
  have h12 : centralNum12_22 q = ∑ e ∈ Finset.range 15, ([((-805865502592299011971319865721:ℝ)/39321600000000000000), ((-121225001412572811892281183511:ℝ)/1966080000000000000), ((-1775141402367400188038182999:ℝ)/24576000000000000), ((-28527931854855771164966791:ℝ)/819200000000000), ((1495964828139224944190809:ℝ)/245760000000000), ((228540208771763705155867:ℝ)/12288000000000), ((1240409892235655401787:ℝ)/102400000000), ((33441483386035063073:ℝ)/7680000000), ((1386808963477545017:ℝ)/1536000000), ((5607741694745807:ℝ)/76800000), ((-566577873051:ℝ)/40000), ((-168414526431:ℝ)/32000), ((-2387276307:ℝ)/3200), ((-8626257:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_22; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((44537902036898209:ℝ)/19200000000), ((5455356485426929:ℝ)/960000000), ((74001357006661:ℝ)/12000000), ((784860652077:ℝ)/200000), ((97480229287:ℝ)/60000), ((1367570683:ℝ)/3000), ((2171683:ℝ)/25), ((162556:ℝ)/15), ((2404:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-805865502592299011971319865721:ℝ)/39321600000000000000), ((-121225001412572811892281183511:ℝ)/1966080000000000000), ((-1775141402367400188038182999:ℝ)/24576000000000000), ((-28527931854855771164966791:ℝ)/819200000000000), ((1495964828139224944190809:ℝ)/245760000000000), ((228540208771763705155867:ℝ)/12288000000000), ((1240409892235655401787:ℝ)/102400000000), ((33441483386035063073:ℝ)/7680000000), ((1386808963477545017:ℝ)/1536000000), ((5607741694745807:ℝ)/76800000), ((-566577873051:ℝ)/40000), ((-168414526431:ℝ)/32000), ((-2387276307:ℝ)/3200), ((-8626257:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-805865502592299011971319865721:ℝ)/39321600000000000000), ((-121225001412572811892281183511:ℝ)/1966080000000000000), ((-1775141402367400188038182999:ℝ)/24576000000000000), ((-28527931854855771164966791:ℝ)/819200000000000), ((1495964828139224944190809:ℝ)/245760000000000), ((228540208771763705155867:ℝ)/12288000000000), ((1240409892235655401787:ℝ)/102400000000), ((33441483386035063073:ℝ)/7680000000), ((1386808963477545017:ℝ)/1536000000), ((5607741694745807:ℝ)/76800000), ((-566577873051:ℝ)/40000), ((-168414526431:ℝ)/32000), ((-2387276307:ℝ)/3200), ((-8626257:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((44537902036898209:ℝ)/19200000000), ((5455356485426929:ℝ)/960000000), ((74001357006661:ℝ)/12000000), ((784860652077:ℝ)/200000), ((97480229287:ℝ)/60000), ((1367570683:ℝ)/3000), ((2171683:ℝ)/25), ((162556:ℝ)/15), ((2404:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((44537902036898209:ℝ)/19200000000) + ((5455356485426929:ℝ)/960000000)*t)| ≤ ((152810738837431:ℝ)/9600000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-805865502592299011971319865721:ℝ)/39321600000000000000), ((-121225001412572811892281183511:ℝ)/1966080000000000000), ((-1775141402367400188038182999:ℝ)/24576000000000000), ((-28527931854855771164966791:ℝ)/819200000000000), ((1495964828139224944190809:ℝ)/245760000000000), ((228540208771763705155867:ℝ)/12288000000000), ((1240409892235655401787:ℝ)/102400000000), ((33441483386035063073:ℝ)/7680000000), ((1386808963477545017:ℝ)/1536000000), ((5607741694745807:ℝ)/76800000), ((-566577873051:ℝ)/40000), ((-168414526431:ℝ)/32000), ((-2387276307:ℝ)/3200), ((-8626257:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e) - ((-805865502592299011971319865721:ℝ)/39321600000000000000) - ((-121225001412572811892281183511:ℝ)/1966080000000000000)*t| ≤ ((606122106937783786682295983:ℝ)/3276800000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-805865502592299011971319865721:ℝ)/39321600000000000000), ((-121225001412572811892281183511:ℝ)/1966080000000000000), ((-1775141402367400188038182999:ℝ)/24576000000000000), ((-28527931854855771164966791:ℝ)/819200000000000), ((1495964828139224944190809:ℝ)/245760000000000), ((228540208771763705155867:ℝ)/12288000000000), ((1240409892235655401787:ℝ)/102400000000), ((33441483386035063073:ℝ)/7680000000), ((1386808963477545017:ℝ)/1536000000), ((5607741694745807:ℝ)/76800000), ((-566577873051:ℝ)/40000), ((-168414526431:ℝ)/32000), ((-2387276307:ℝ)/3200), ((-8626257:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e)| ≤ ((233590992322031307325947150257:ℝ)/9830400000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((46108585475767759:ℝ)/16000000000) - ((5967553945585029:ℝ)/800000000)*t| ≤ ((88165144661803:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (4:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82125:ℝ), (-6663750:ℝ), (115666200:ℝ), (-750437000:ℝ), (2277262000:ℝ), (-3656824320:ℝ), (3359621120:ℝ), (-1817706496:ℝ), ((1625292800:ℝ)/3), (-67108864:ℝ)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_22 q| ≤ ((310324325077007360:ℝ)/3) := by
    rw [centralNum13_22_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (4:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((178425:ℝ)/2), ((-13176075:ℝ)/2), ((777815145:ℝ)/8), ((-3968389015:ℝ)/8), ((9393350195:ℝ)/8), ((-26366634375:ℝ)/16), ((77851609375:ℝ)/64), ((-25714921875:ℝ)/64), ((5236328125:ℝ)/96), ((-9765625:ℝ)/4)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_22 q| ≤ ((54686425057318400:ℝ)/3) := by
    rw [centralNum23_22_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((70042178050639083684723132989:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece12_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece12_E11 h0) m23'
  have c5 := scaled_affine (X := ((126875021731:ℝ)/200000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2))| ≤ ((2105697027059302400000000000000000000:ℝ)/3977008114820602438227406147714434321) := by
    rw [abs_neg, tailWeight_2, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ (4:ℝ)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*(4:ℝ)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece12_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((2570430941234500:ℝ)/4782969)) ≤ (4:ℝ)^6*(8000*(2*(4:ℝ)-3)^2*(1/((831493600485514841979407800409:ℝ)/1000000000000))*((2570430941234500:ℝ)/4782969)) := by
          gcongr
      _ ≤ ((2105697027059302400000000000000000000:ℝ)/3977008114820602438227406147714434321) := by norm_num
  have c7 := affine_round (α := ((44537902036898209:ℝ)/19200000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((-805865502592299011971319865721:ℝ)/39321600000000000000) + ((46108585475767759:ℝ)/16000000000)*((126875021731:ℝ)/200000000000) - ((148871056600675261:ℝ)/50000000000)) (β := ((5455356485426929:ℝ)/960000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((-121225001412572811892281183511:ℝ)/1966080000000000000) - 3*((-805865502592299011971319865721:ℝ)/39321600000000000000)) + ((5967553945585029:ℝ)/800000000)*((126875021731:ℝ)/200000000000) - ((104047213136618921:ℝ)/10000000000)) ht
  have hW : pieceW q pieceX_12 2 2 = centralNum11_22 q + 8*(Real.exp (-(3*((79:ℝ)/20)))*Real.exp (-3*t))*centralNum12_22 q + 18*Real.exp (-8*q)*centralNum13_22 q + 72*Real.exp (-11*q)*centralNum23_22 q + 8*q^7*(2*q-3)^2*((126875021731:ℝ)/200000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2)) := by
    rw [pieceW_22, pieceX_12, sym4_22, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((48479230398138725704001889562779585919538725607038444259536471235527:ℝ)/23548275637301640188082716336504222037939673893999144529888800000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((44537902036898209:ℝ)/19200000000) + ((5455356485426929:ℝ)/960000000)*t) + (8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((-805865502592299011971319865721:ℝ)/39321600000000000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((-121225001412572811892281183511:ℝ)/1966080000000000000) - 3*((-805865502592299011971319865721:ℝ)/39321600000000000000))*t) + (((46108585475767759:ℝ)/16000000000) + ((5967553945585029:ℝ)/800000000)*t)*((126875021731:ℝ)/200000000000) - (((148871056600675261:ℝ)/50000000000) + t * ((104047213136618921:ℝ)/10000000000)) = (((44537902036898209:ℝ)/19200000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((-805865502592299011971319865721:ℝ)/39321600000000000000) + ((46108585475767759:ℝ)/16000000000)*((126875021731:ℝ)/200000000000) - ((148871056600675261:ℝ)/50000000000)) + t*(((5455356485426929:ℝ)/960000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((-121225001412572811892281183511:ℝ)/1966080000000000000) - 3*((-805865502592299011971319865721:ℝ)/39321600000000000000)) + ((5967553945585029:ℝ)/800000000)*((126875021731:ℝ)/200000000000) - ((104047213136618921:ℝ)/10000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece12_e23 {q : ℝ} (h0 : ((39:ℝ)/10) ≤ q) (h1 : q ≤ (4:ℝ)) :
    |pieceW q pieceX_12 2 3 - (((-61351604094839123:ℝ)/20000000000) + (q - ((79:ℝ)/20)) * ((-158608411254540717:ℝ)/10000000000))| ≤ ((89519003511913993:ℝ)/50000000000) := by
  set t := q - ((79:ℝ)/20) with htd
  have hq : q = ((79:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece12_L3 piece12_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((79:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_23 q = ∑ e ∈ Finset.range 9, ([((214153894201203:ℝ)/320000000), ((40071726482557:ℝ)/32000000), ((1789853350633:ℝ)/1600000), ((50452924269:ℝ)/80000), ((193252249:ℝ)/800), ((12475439:ℝ)/200), ((102963:ℝ)/10), (974:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_23; ring
  have h12 : centralNum12_23 q = ∑ e ∈ Finset.range 16, ([((117793177910662233014115143375943:ℝ)/3670016000000000000000), ((180133932259683315481064202631:ℝ)/3670016000000000000), ((-60027511779492166136314220573:ℝ)/1835008000000000000), ((-6433874807756410559135918787:ℝ)/45875200000000000), ((-708101540277714081391713697:ℝ)/4587520000000000), ((-51822431677121056605583117:ℝ)/573440000000000), ((-67608558243653230365957:ℝ)/2293760000000), ((-985948406197110323407:ℝ)/286720000000), ((38038285233103283713:ℝ)/28672000000), ((516986975452815177:ℝ)/716800000), ((55556634737563389:ℝ)/358400000), ((1047403814463:ℝ)/71680), ((-93228320763:ℝ)/179200), ((-1291994307:ℝ)/4480), ((-13036707:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_23; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((214153894201203:ℝ)/320000000), ((40071726482557:ℝ)/32000000), ((1789853350633:ℝ)/1600000), ((50452924269:ℝ)/80000), ((193252249:ℝ)/800), ((12475439:ℝ)/200), ((102963:ℝ)/10), (974:ℝ), (40:ℝ)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((117793177910662233014115143375943:ℝ)/3670016000000000000000), ((180133932259683315481064202631:ℝ)/3670016000000000000), ((-60027511779492166136314220573:ℝ)/1835008000000000000), ((-6433874807756410559135918787:ℝ)/45875200000000000), ((-708101540277714081391713697:ℝ)/4587520000000000), ((-51822431677121056605583117:ℝ)/573440000000000), ((-67608558243653230365957:ℝ)/2293760000000), ((-985948406197110323407:ℝ)/286720000000), ((38038285233103283713:ℝ)/28672000000), ((516986975452815177:ℝ)/716800000), ((55556634737563389:ℝ)/358400000), ((1047403814463:ℝ)/71680), ((-93228320763:ℝ)/179200), ((-1291994307:ℝ)/4480), ((-13036707:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 14 ht
  have m12 := abs_poly_le (fun e => ([((117793177910662233014115143375943:ℝ)/3670016000000000000000), ((180133932259683315481064202631:ℝ)/3670016000000000000), ((-60027511779492166136314220573:ℝ)/1835008000000000000), ((-6433874807756410559135918787:ℝ)/45875200000000000), ((-708101540277714081391713697:ℝ)/4587520000000000), ((-51822431677121056605583117:ℝ)/573440000000000), ((-67608558243653230365957:ℝ)/2293760000000), ((-985948406197110323407:ℝ)/286720000000), ((38038285233103283713:ℝ)/28672000000), ((516986975452815177:ℝ)/716800000), ((55556634737563389:ℝ)/358400000), ((1047403814463:ℝ)/71680), ((-93228320763:ℝ)/179200), ((-1291994307:ℝ)/4480), ((-13036707:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 16 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((214153894201203:ℝ)/320000000), ((40071726482557:ℝ)/32000000), ((1789853350633:ℝ)/1600000), ((50452924269:ℝ)/80000), ((193252249:ℝ)/800), ((12475439:ℝ)/200), ((102963:ℝ)/10), (974:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e) - (((214153894201203:ℝ)/320000000) + ((40071726482557:ℝ)/32000000)*t)| ≤ ((1841285115037:ℝ)/640000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 16, ([((117793177910662233014115143375943:ℝ)/3670016000000000000000), ((180133932259683315481064202631:ℝ)/3670016000000000000), ((-60027511779492166136314220573:ℝ)/1835008000000000000), ((-6433874807756410559135918787:ℝ)/45875200000000000), ((-708101540277714081391713697:ℝ)/4587520000000000), ((-51822431677121056605583117:ℝ)/573440000000000), ((-67608558243653230365957:ℝ)/2293760000000), ((-985948406197110323407:ℝ)/286720000000), ((38038285233103283713:ℝ)/28672000000), ((516986975452815177:ℝ)/716800000), ((55556634737563389:ℝ)/358400000), ((1047403814463:ℝ)/71680), ((-93228320763:ℝ)/179200), ((-1291994307:ℝ)/4480), ((-13036707:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e) - ((117793177910662233014115143375943:ℝ)/3670016000000000000000) - ((180133932259683315481064202631:ℝ)/3670016000000000000)*t| ≤ ((368122159808625016979825006441:ℝ)/3670016000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 16, ([((117793177910662233014115143375943:ℝ)/3670016000000000000000), ((180133932259683315481064202631:ℝ)/3670016000000000000), ((-60027511779492166136314220573:ℝ)/1835008000000000000), ((-6433874807756410559135918787:ℝ)/45875200000000000), ((-708101540277714081391713697:ℝ)/4587520000000000), ((-51822431677121056605583117:ℝ)/573440000000000), ((-67608558243653230365957:ℝ)/2293760000000), ((-985948406197110323407:ℝ)/286720000000), ((38038285233103283713:ℝ)/28672000000), ((516986975452815177:ℝ)/716800000), ((55556634737563389:ℝ)/358400000), ((1047403814463:ℝ)/71680), ((-93228320763:ℝ)/179200), ((-1291994307:ℝ)/4480), ((-13036707:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e)| ≤ ((63583998341727511902574089256967:ℝ)/1835008000000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((46108585475767759:ℝ)/16000000000) - ((5967553945585029:ℝ)/800000000)*t| ≤ ((88165144661803:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (4:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-7627725:ℝ)/2), (173988600:ℝ), (-2299614450:ℝ), (13088188200:ℝ), (-38221499200:ℝ), (63366115840:ℝ), ((-445610508288:ℝ)/7), ((841540698112:ℝ)/21), ((-326820167680:ℝ)/21), ((10133438464:ℝ)/3), ((-2147483648:ℝ)/7)] : List ℝ).getD e 0) 16 hq1'
  have m13' : |centralNum13_23 q| ≤ ((23080541166264989184:ℝ)/7) := by
    rw [centralNum13_23_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (4:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-15801525:ℝ)/4), ((655493865:ℝ)/4), ((-7334421225:ℝ)/4), ((16442962485:ℝ)/2), ((-598626108395:ℝ)/32), ((414013307125:ℝ)/16), ((-4611984703125:ℝ)/224), ((399923828125:ℝ)/48), ((-4353201171875:ℝ)/2688), ((189736328125:ℝ)/1344), ((-244140625:ℝ)/56)] : List ℝ).getD e 0) 16 hq1'
  have m23' : |centralNum23_23 q| ≤ (410006567374670080:ℝ) := by
    rw [centralNum23_23_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((70042178050639083684723132989:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece12_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece12_E11 h0) m23'
  have c5 := scaled_affine (X := ((-38654993997:ℝ)/20000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((214153894201203:ℝ)/320000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((117793177910662233014115143375943:ℝ)/3670016000000000000000) + ((46108585475767759:ℝ)/16000000000)*((-38654993997:ℝ)/20000000000) - ((-61351604094839123:ℝ)/20000000000)) (β := ((40071726482557:ℝ)/32000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((180133932259683315481064202631:ℝ)/3670016000000000000) - 3*((117793177910662233014115143375943:ℝ)/3670016000000000000000)) + ((5967553945585029:ℝ)/800000000)*((-38654993997:ℝ)/20000000000) - ((-158608411254540717:ℝ)/10000000000)) ht
  have hW : pieceW q pieceX_12 2 3 = centralNum11_23 q + 8*(Real.exp (-(3*((79:ℝ)/20)))*Real.exp (-3*t))*centralNum12_23 q + 18*Real.exp (-8*q)*centralNum13_23 q + 72*Real.exp (-11*q)*centralNum23_23 q + 8*q^7*(2*q-3)^2*((-38654993997:ℝ)/20000000000) + (0:ℝ) := by
    rw [pieceW_23, pieceX_12, sym4_23, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((10015622330801826073442489670801846930463458859561185677503456840181:ℝ)/5494597648703716043885967145184318475519257241933133723640720000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((214153894201203:ℝ)/320000000) + ((40071726482557:ℝ)/32000000)*t) + (8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((117793177910662233014115143375943:ℝ)/3670016000000000000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((180133932259683315481064202631:ℝ)/3670016000000000000) - 3*((117793177910662233014115143375943:ℝ)/3670016000000000000000))*t) + (((46108585475767759:ℝ)/16000000000) + ((5967553945585029:ℝ)/800000000)*t)*((-38654993997:ℝ)/20000000000) - (((-61351604094839123:ℝ)/20000000000) + t * ((-158608411254540717:ℝ)/10000000000)) = (((214153894201203:ℝ)/320000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((117793177910662233014115143375943:ℝ)/3670016000000000000000) + ((46108585475767759:ℝ)/16000000000)*((-38654993997:ℝ)/20000000000) - ((-61351604094839123:ℝ)/20000000000)) + t*(((40071726482557:ℝ)/32000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((180133932259683315481064202631:ℝ)/3670016000000000000) - 3*((117793177910662233014115143375943:ℝ)/3670016000000000000000)) + ((5967553945585029:ℝ)/800000000)*((-38654993997:ℝ)/20000000000) - ((-158608411254540717:ℝ)/10000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece12_e33 {q : ℝ} (h0 : ((39:ℝ)/10) ≤ q) (h1 : q ≤ (4:ℝ)) :
    |pieceW q pieceX_12 3 3 - (((134593154371669777:ℝ)/1000000000) + (q - ((79:ℝ)/20)) * ((14517778658149711:ℝ)/40000000))| ≤ ((148519468068319549:ℝ)/2500000000) := by
  set t := q - ((79:ℝ)/20) with htd
  have hq : q = ((79:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece12_L3 piece12_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((79:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_33 q = ∑ e ∈ Finset.range 10, ([((1260692870367847:ℝ)/3200000000), ((135139248110121:ℝ)/80000000), ((139274616704379:ℝ)/56000000), ((766508914947:ℝ)/400000), ((18041197407:ℝ)/20000), ((278026203:ℝ)/1000), ((2867583:ℝ)/50), ((38706:ℝ)/5), (624:ℝ), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_33; ring
  have h12 : centralNum12_33 q = ∑ e ∈ Finset.range 17, ([((-2506024161507996412863278915493101:ℝ)/146800640000000000000000), ((7589223824313637670373099789266937:ℝ)/51380224000000000000000), ((271782932745982715688653166250047:ℝ)/513802240000000000000), ((2597006571327962752886323523007:ℝ)/3670016000000000000), ((89629207610763072167108284881:ℝ)/183500800000000000), ((7517256724844114727897134643:ℝ)/45875200000000000), ((-9080911183673455035938583:ℝ)/2293760000000000), ((-662264029525727054698077:ℝ)/22937600000000), ((-103805937229441754620923:ℝ)/8028160000000), ((-1075530402397126584289:ℝ)/401408000000), ((-1963262598997578633:ℝ)/14336000000), ((46370870971282593:ℝ)/716800000), ((115599155431131:ℝ)/7168000), ((474227135757:ℝ)/358400), ((-680303529:ℝ)/17920), ((-427337613:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_33; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((1260692870367847:ℝ)/3200000000), ((135139248110121:ℝ)/80000000), ((139274616704379:ℝ)/56000000), ((766508914947:ℝ)/400000), ((18041197407:ℝ)/20000), ((278026203:ℝ)/1000), ((2867583:ℝ)/50), ((38706:ℝ)/5), (624:ℝ), ((160:ℝ)/7)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-2506024161507996412863278915493101:ℝ)/146800640000000000000000), ((7589223824313637670373099789266937:ℝ)/51380224000000000000000), ((271782932745982715688653166250047:ℝ)/513802240000000000000), ((2597006571327962752886323523007:ℝ)/3670016000000000000), ((89629207610763072167108284881:ℝ)/183500800000000000), ((7517256724844114727897134643:ℝ)/45875200000000000), ((-9080911183673455035938583:ℝ)/2293760000000000), ((-662264029525727054698077:ℝ)/22937600000000), ((-103805937229441754620923:ℝ)/8028160000000), ((-1075530402397126584289:ℝ)/401408000000), ((-1963262598997578633:ℝ)/14336000000), ((46370870971282593:ℝ)/716800000), ((115599155431131:ℝ)/7168000), ((474227135757:ℝ)/358400), ((-680303529:ℝ)/17920), ((-427337613:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 15 ht
  have m12 := abs_poly_le (fun e => ([((-2506024161507996412863278915493101:ℝ)/146800640000000000000000), ((7589223824313637670373099789266937:ℝ)/51380224000000000000000), ((271782932745982715688653166250047:ℝ)/513802240000000000000), ((2597006571327962752886323523007:ℝ)/3670016000000000000), ((89629207610763072167108284881:ℝ)/183500800000000000), ((7517256724844114727897134643:ℝ)/45875200000000000), ((-9080911183673455035938583:ℝ)/2293760000000000), ((-662264029525727054698077:ℝ)/22937600000000), ((-103805937229441754620923:ℝ)/8028160000000), ((-1075530402397126584289:ℝ)/401408000000), ((-1963262598997578633:ℝ)/14336000000), ((46370870971282593:ℝ)/716800000), ((115599155431131:ℝ)/7168000), ((474227135757:ℝ)/358400), ((-680303529:ℝ)/17920), ((-427337613:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 17 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((1260692870367847:ℝ)/3200000000), ((135139248110121:ℝ)/80000000), ((139274616704379:ℝ)/56000000), ((766508914947:ℝ)/400000), ((18041197407:ℝ)/20000), ((278026203:ℝ)/1000), ((2867583:ℝ)/50), ((38706:ℝ)/5), (624:ℝ), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e) - (((1260692870367847:ℝ)/3200000000) + ((135139248110121:ℝ)/80000000)*t)| ≤ ((144768433883377:ℝ)/22400000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 17, ([((-2506024161507996412863278915493101:ℝ)/146800640000000000000000), ((7589223824313637670373099789266937:ℝ)/51380224000000000000000), ((271782932745982715688653166250047:ℝ)/513802240000000000000), ((2597006571327962752886323523007:ℝ)/3670016000000000000), ((89629207610763072167108284881:ℝ)/183500800000000000), ((7517256724844114727897134643:ℝ)/45875200000000000), ((-9080911183673455035938583:ℝ)/2293760000000000), ((-662264029525727054698077:ℝ)/22937600000000), ((-103805937229441754620923:ℝ)/8028160000000), ((-1075530402397126584289:ℝ)/401408000000), ((-1963262598997578633:ℝ)/14336000000), ((46370870971282593:ℝ)/716800000), ((115599155431131:ℝ)/7168000), ((474227135757:ℝ)/358400), ((-680303529:ℝ)/17920), ((-427337613:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e) - ((-2506024161507996412863278915493101:ℝ)/146800640000000000000000) - ((7589223824313637670373099789266937:ℝ)/51380224000000000000000)*t| ≤ ((363249906014970904973485051847831:ℝ)/256901120000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 17, ([((-2506024161507996412863278915493101:ℝ)/146800640000000000000000), ((7589223824313637670373099789266937:ℝ)/51380224000000000000000), ((271782932745982715688653166250047:ℝ)/513802240000000000000), ((2597006571327962752886323523007:ℝ)/3670016000000000000), ((89629207610763072167108284881:ℝ)/183500800000000000), ((7517256724844114727897134643:ℝ)/45875200000000000), ((-9080911183673455035938583:ℝ)/2293760000000000), ((-662264029525727054698077:ℝ)/22937600000000), ((-103805937229441754620923:ℝ)/8028160000000), ((-1075530402397126584289:ℝ)/401408000000), ((-1963262598997578633:ℝ)/14336000000), ((46370870971282593:ℝ)/716800000), ((115599155431131:ℝ)/7168000), ((474227135757:ℝ)/358400), ((-680303529:ℝ)/17920), ((-427337613:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e)| ≤ ((1661524536183093511269374525319373:ℝ)/64225280000000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((46108585475767759:ℝ)/16000000000), ((5967553945585029:ℝ)/800000000), ((42638770520943:ℝ)/5000000), ((88338783708:ℝ)/15625), ((119824747287:ℝ)/50000), ((1684527033:ℝ)/2500), ((15714048:ℝ)/125), ((375312:ℝ)/25), ((5208:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((46108585475767759:ℝ)/16000000000) - ((5967553945585029:ℝ)/800000000)*t| ≤ ((88165144661803:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (4:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-8120475:ℝ)/4), ((464861025:ℝ)/2), (-5906535975:ℝ), ((411904731750:ℝ)/7), ((-2024051769000:ℝ)/7), ((5554394637600:ℝ)/7), (-1314913862656:ℝ), ((9709155336192:ℝ)/7), ((-6724555112448:ℝ)/7), ((1313173667840:ℝ)/3), ((-6168244125696:ℝ)/49), ((3004329623552:ℝ)/147), ((-68719476736:ℝ)/49)] : List ℝ).getD e 0) 17 hq1'
  have m13' : |centralNum13_33 q| ≤ ((16857379845418980177472:ℝ)/147) := by
    rw [centralNum13_33_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (4:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-16872075:ℝ)/8), ((1833754545:ℝ)/8), ((-83998007145:ℝ)/16), ((4929124002765:ℝ)/112), ((-76723155584685:ℝ)/448), ((164888745653055:ℝ)/448), ((-63358359907625:ℝ)/128), ((364713160040625:ℝ)/896), ((-334937462578125:ℝ)/1792), ((245466998046875:ℝ)/5376), ((-72144521484375:ℝ)/12544), ((6518798828125:ℝ)/18816), ((-6103515625:ℝ)/784)] : List ℝ).getD e 0) 17 hq1'
  have m23' : |centralNum23_33 q| ≤ ((220164085498056193120:ℝ)/21) := by
    rw [centralNum23_33_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((70042178050639083684723132989:ℝ)/500000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece12_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece12_E11 h0) m23'
  have c5 := scaled_affine (X := ((93812695481:ℝ)/2000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3))| ≤ ((2710382028968125644800000000000000000000:ℝ)/107379219100156265832139965988289726667) := by
    rw [abs_neg, tailWeight_3, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ (4:ℝ)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*(4:ℝ)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece12_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((3308571812705231500:ℝ)/129140163)) ≤ (4:ℝ)^6*(8000*(2*(4:ℝ)-3)^2*(1/((831493600485514841979407800409:ℝ)/1000000000000))*((3308571812705231500:ℝ)/129140163)) := by
          gcongr
      _ ≤ ((2710382028968125644800000000000000000000:ℝ)/107379219100156265832139965988289726667) := by norm_num
  have c7 := affine_round (α := ((1260692870367847:ℝ)/3200000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((-2506024161507996412863278915493101:ℝ)/146800640000000000000000) + ((46108585475767759:ℝ)/16000000000)*((93812695481:ℝ)/2000000000) - ((134593154371669777:ℝ)/1000000000)) (β := ((135139248110121:ℝ)/80000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((7589223824313637670373099789266937:ℝ)/51380224000000000000000) - 3*((-2506024161507996412863278915493101:ℝ)/146800640000000000000000)) + ((5967553945585029:ℝ)/800000000)*((93812695481:ℝ)/2000000000) - ((14517778658149711:ℝ)/40000000)) ht
  have hW : pieceW q pieceX_12 3 3 = centralNum11_33 q + 8*(Real.exp (-(3*((79:ℝ)/20)))*Real.exp (-3*t))*centralNum12_33 q + 18*Real.exp (-8*q)*centralNum13_33 q + 72*Real.exp (-11*q)*centralNum23_33 q + 8*q^7*(2*q-3)^2*((93812695481:ℝ)/2000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3)) := by
    rw [pieceW_33, pieceX_12, sym4_33, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((762697130322121717589044405106003857757197933263290128760737769866809:ℝ)/3846218354092601230720177001629022932863480069353193606548504000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((1260692870367847:ℝ)/3200000000) + ((135139248110121:ℝ)/80000000)*t) + (8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((-2506024161507996412863278915493101:ℝ)/146800640000000000000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((7589223824313637670373099789266937:ℝ)/51380224000000000000000) - 3*((-2506024161507996412863278915493101:ℝ)/146800640000000000000000))*t) + (((46108585475767759:ℝ)/16000000000) + ((5967553945585029:ℝ)/800000000)*t)*((93812695481:ℝ)/2000000000) - (((134593154371669777:ℝ)/1000000000) + t * ((14517778658149711:ℝ)/40000000)) = (((1260692870367847:ℝ)/3200000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*((-2506024161507996412863278915493101:ℝ)/146800640000000000000000) + ((46108585475767759:ℝ)/16000000000)*((93812695481:ℝ)/2000000000) - ((134593154371669777:ℝ)/1000000000)) + t*(((135139248110121:ℝ)/80000000) + 8*(((1/((70042178050639083684723132989:ℝ)/500000000000000000000000))+(1/((140083900709778466732471974383:ℝ)/1000000000000000000000000)))/2)*(((7589223824313637670373099789266937:ℝ)/51380224000000000000000) - 3*((-2506024161507996412863278915493101:ℝ)/146800640000000000000000)) + ((5967553945585029:ℝ)/800000000)*((93812695481:ℝ)/2000000000) - ((14517778658149711:ℝ)/40000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece12_plus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((72363387600466157:ℝ)/20000000000) + ((1:ℝ)/20)*((882407628736461083:ℝ)/100000000000) - (((256557593094336537:ℝ)/10000000000000) + ((550890165796614907:ℝ)/100000000000000) + ((145242632663487421:ℝ)/100000000000000) + ((103000287559184559:ℝ)/10000000000000)))
      (((-769025205870522981:ℝ)/1000000000000) + ((1:ℝ)/20)*((-129004593917967179:ℝ)/100000000000))
      (((329177026029719493:ℝ)/10000000000000) + ((1:ℝ)/20)*((-27533621446419653:ℝ)/2500000000000))
      (((-112446636098754597:ℝ)/1000000000000) + ((1:ℝ)/20)*((-565255496982561493:ℝ)/1000000000000))
      (((73382031441816239:ℝ)/25000000000) + ((1:ℝ)/20)*((323563734773396967:ℝ)/50000000000) - (((550890165796614907:ℝ)/100000000000000) + ((49163115552066389:ℝ)/2500000000000) + ((19834445401425567:ℝ)/1000000000000) + ((37573053742016169:ℝ)/500000000000)))
      (((-90983402398200443:ℝ)/500000000000) + ((1:ℝ)/20)*((-43072035642634809:ℝ)/125000000000))
      (((897881223093624777:ℝ)/1000000000000) + ((1:ℝ)/20)*((53054555286123291:ℝ)/12500000000))
      (((148871056600675261:ℝ)/50000000000) + ((1:ℝ)/20)*((104047213136618921:ℝ)/10000000000) - (((145242632663487421:ℝ)/100000000000000) + ((19834445401425567:ℝ)/1000000000000) + ((75736086379010643:ℝ)/500000000000) + ((89519003511913993:ℝ)/50000000000)))
      (((-61351604094839123:ℝ)/20000000000) + ((1:ℝ)/20)*((-158608411254540717:ℝ)/10000000000))
      (((134593154371669777:ℝ)/1000000000) + ((1:ℝ)/20)*((14517778658149711:ℝ)/40000000) - (((103000287559184559:ℝ)/10000000000000) + ((37573053742016169:ℝ)/500000000000) + ((89519003511913993:ℝ)/50000000000) + ((148519468068319549:ℝ)/2500000000))) i j :=
  quadForm_nonneg_of_ldl ((200822803917079262931:ℝ)/50000000000000) ((59558218010419396526184442962022783598173:ℝ)/20082280391707926293100000000000000) ((9063361959938894395320409653890055245162906182985579346803863:ℝ)/5955821801041939652618444296202278359817300000000000000) ((29590819877333987521620451989679272415842696737796111177542938074957887301582896257:ℝ)/362534478397555775812816386155602209806516247319423173872154520000000000000) ((-41676375141475328525:ℝ)/200822803917079262931) ((1618351508702177812:ℝ)/200822803917079262931) ((-14070941094788267165:ℝ)/401645607834158525862) ((-3865408225456428245488667543037162919160:ℝ)/59558218010419396526184442962022783598173) ((21706902482209025063811635781208889125475:ℝ)/59558218010419396526184442962022783598173) ((-22568613480478161965248850514822791303862770824963371743835160:ℝ)/9063361959938894395320409653890055245162906182985579346803863)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece12_minus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((72363387600466157:ℝ)/20000000000) - ((1:ℝ)/20)*((882407628736461083:ℝ)/100000000000) - (((256557593094336537:ℝ)/10000000000000) + ((550890165796614907:ℝ)/100000000000000) + ((145242632663487421:ℝ)/100000000000000) + ((103000287559184559:ℝ)/10000000000000)))
      (((-769025205870522981:ℝ)/1000000000000) - ((1:ℝ)/20)*((-129004593917967179:ℝ)/100000000000))
      (((329177026029719493:ℝ)/10000000000000) - ((1:ℝ)/20)*((-27533621446419653:ℝ)/2500000000000))
      (((-112446636098754597:ℝ)/1000000000000) - ((1:ℝ)/20)*((-565255496982561493:ℝ)/1000000000000))
      (((73382031441816239:ℝ)/25000000000) - ((1:ℝ)/20)*((323563734773396967:ℝ)/50000000000) - (((550890165796614907:ℝ)/100000000000000) + ((49163115552066389:ℝ)/2500000000000) + ((19834445401425567:ℝ)/1000000000000) + ((37573053742016169:ℝ)/500000000000)))
      (((-90983402398200443:ℝ)/500000000000) - ((1:ℝ)/20)*((-43072035642634809:ℝ)/125000000000))
      (((897881223093624777:ℝ)/1000000000000) - ((1:ℝ)/20)*((53054555286123291:ℝ)/12500000000))
      (((148871056600675261:ℝ)/50000000000) - ((1:ℝ)/20)*((104047213136618921:ℝ)/10000000000) - (((145242632663487421:ℝ)/100000000000000) + ((19834445401425567:ℝ)/1000000000000) + ((75736086379010643:ℝ)/500000000000) + ((89519003511913993:ℝ)/50000000000)))
      (((-61351604094839123:ℝ)/20000000000) - ((1:ℝ)/20)*((-158608411254540717:ℝ)/10000000000))
      (((134593154371669777:ℝ)/1000000000) - ((1:ℝ)/20)*((14517778658149711:ℝ)/40000000) - (((103000287559184559:ℝ)/10000000000000) + ((37573053742016169:ℝ)/500000000000) + ((89519003511913993:ℝ)/50000000000) + ((148519468068319549:ℝ)/2500000000))) i j :=
  quadForm_nonneg_of_ldl ((156702422480256208781:ℝ)/50000000000000) ((36561630353123967513370145462117204800823:ℝ)/15670242248025620878100000000000000) ((1766274650048556145848085950043300442126784394273899634608133:ℝ)/3656163035312396751337014546211720480082300000000000000) ((3157221115038763352104665853784764519680775788238961714824261377458058656974710937:ℝ)/70650986001942245833923438001732017685071375770955985384325320000000000000) ((-35226145445576969575:ℝ)/156702422480256208781) ((1673418751595017118:ℝ)/156702422480256208781) ((-8418386124962652235:ℝ)/313404844960512417562) ((-2463588034534435987621319966759875313740:ℝ)/36561630353123967513370145462117204800823) ((10447958046996394351647834869531628625175:ℝ)/36561630353123967513370145462117204800823) ((-8148538459202856747837634874610290197404842266005559664070410:ℝ)/1766274650048556145848085950043300442126784394273899634608133)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

/-- **Piece 12.** The piece matrix is positive semidefinite on `q ∈ [39/10, 4]`. -/
theorem piece_12 {q : ℝ} (h0 : ((39:ℝ)/10) ≤ q) (h1 : q ≤ (4:ℝ)) (y : Fin 4 → ℝ) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceW q pieceX_12 i j :=
  pieceForm_nonneg (pieceW_symm (sym4_symm _ _ _ _ _ _ _ _ _ _) q) (by norm_num : (0:ℝ) < ((1:ℝ)/20))
    (abs_le.mpr ⟨by linarith, by linarith⟩)
    (piece12_e00 h0 h1) (piece12_e01 h0 h1) (piece12_e02 h0 h1) (piece12_e03 h0 h1) (piece12_e11 h0 h1) (piece12_e12 h0 h1) (piece12_e13 h0 h1) (piece12_e22 h0 h1) (piece12_e23 h0 h1) (piece12_e33 h0 h1)
    piece12_plus piece12_minus y

/-! #### Piece 13 (seam), `q ∈ [4, 41/10]` -/

/-- The compensation matrix of piece 13. -/
def pieceX_13 : Fin 4 → Fin 4 → ℝ :=
  sym4 ((11148000359:ℝ)/1000000000000) ((-4578848991:ℝ)/4000000000000) ((71271091163:ℝ)/20000000000000) ((-573662206417:ℝ)/10000000000000) ((198552705423:ℝ)/10000000000000) ((-137767972523:ℝ)/5000000000000) ((110924610021:ℝ)/250000000000) ((968561291969:ℝ)/10000000000000) ((-138127623807:ℝ)/100000000000) ((27808308009:ℝ)/1250000000)

theorem piece13_L3 : ((9454704485244025628860692337:ℝ)/50000000000000000000000) ≤ Real.exp ((3:ℝ)*((81:ℝ)/20)) := by
  have h := le_exp_nat_add 12 (f := ((3:ℝ)/20)) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((81:ℝ)/20) = ((12:ℕ):ℝ) + ((3:ℝ)/20) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece13_U3 : Real.exp ((3:ℝ)*((81:ℝ)/20)) ≤ ((189094089956474140623031291221:ℝ)/1000000000000000000000000) := by
  have h := exp_nat_add_le 12 (f := ((3:ℝ)/20)) (by norm_num) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((81:ℝ)/20) = ((12:ℕ):ℝ) + ((3:ℝ)/20) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem piece13_L8_at : ((789629600348380990724996935799:ℝ)/10000000000000000) ≤ Real.exp ((8:ℝ)*(4:ℝ)) := by
  have h := le_exp_nat_add 32 (f := (0:ℝ)) (by norm_num)
  rw [show ((8:ℝ):ℝ)*(4:ℝ) = ((32:ℕ):ℝ) + (0:ℝ) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece13_E8 {q : ℝ} (h0 : (4:ℝ) ≤ q) : Real.exp (-((8:ℝ))*q) ≤ 1/((789629600348380990724996935799:ℝ)/10000000000000000) := by
  have hm : Real.exp (-((8:ℝ))*q) ≤ Real.exp (-((8:ℝ)*(4:ℝ))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece13_L8_at (le_refl _)).2

theorem piece13_L11_at : ((128516000812739333147406854669:ℝ)/10000000000) ≤ Real.exp ((11:ℝ)*(4:ℝ)) := by
  have h := le_exp_nat_add 44 (f := (0:ℝ)) (by norm_num)
  rw [show ((11:ℝ):ℝ)*(4:ℝ) = ((44:ℕ):ℝ) + (0:ℝ) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece13_E11 {q : ℝ} (h0 : (4:ℝ) ≤ q) : Real.exp (-((11:ℝ))*q) ≤ 1/((128516000812739333147406854669:ℝ)/10000000000) := by
  have hm : Real.exp (-((11:ℝ))*q) ≤ Real.exp (-((11:ℝ)*(4:ℝ))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece13_L11_at (le_refl _)).2

theorem piece13_Lt_at : ((239520380097857689497853293383:ℝ)/100000000000) ≤ Real.exp (((529:ℝ)/50)*(4:ℝ)) := by
  have h := le_exp_nat_add 42 (f := ((8:ℝ)/25)) (by norm_num)
  rw [show (((529:ℝ)/50):ℝ)*(4:ℝ) = ((42:ℕ):ℝ) + ((8:ℝ)/25) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece13_Et {q : ℝ} (h0 : (4:ℝ) ≤ q) : Real.exp (-(((529:ℝ)/50))*q) ≤ 1/((239520380097857689497853293383:ℝ)/100000000000) := by
  have hm : Real.exp (-(((529:ℝ)/50))*q) ≤ Real.exp (-(((529:ℝ)/50)*(4:ℝ))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece13_Lt_at (le_refl _)).2

theorem piece13_e00 {q : ℝ} (h0 : (4:ℝ) ≤ q) (h1 : q ≤ ((41:ℝ)/10)) :
    |pieceW q pieceX_13 0 0 - (((92055040069721673:ℝ)/20000000000) + (q - ((81:ℝ)/20)) * ((109372830951384483:ℝ)/10000000000))| ≤ ((153680921241767561:ℝ)/5000000000000) := by
  set t := q - ((81:ℝ)/20) with htd
  have hq : q = ((81:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece13_L3 piece13_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((81:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_00 q = ∑ e ∈ Finset.range 10, ([((73228612648330161:ℝ)/16000000000), ((8661831454335789:ℝ)/800000000), ((14341144241313:ℝ)/1250000), ((1783554791193:ℝ)/250000), ((143219629413:ℝ)/50000), ((1922458293:ℝ)/2500), ((17234532:ℝ)/125), ((397632:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_00; ring
  have h12 : centralNum12_00 q = ∑ e ∈ Finset.range 11, ([((-117198105145067117493:ℝ)/320000000000), ((-3075663583298356101:ℝ)/3200000000), ((-90887676322102731:ℝ)/80000000), ((-1592597944108323:ℝ)/2000000), ((-73284556952943:ℝ)/200000), ((-5782131637443:ℝ)/50000), ((-3168175437:ℝ)/125), ((-95214966:ℝ)/25), ((-1877394:ℝ)/5), (-21928:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_00; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((73228612648330161:ℝ)/16000000000), ((8661831454335789:ℝ)/800000000), ((14341144241313:ℝ)/1250000), ((1783554791193:ℝ)/250000), ((143219629413:ℝ)/50000), ((1922458293:ℝ)/2500), ((17234532:ℝ)/125), ((397632:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-117198105145067117493:ℝ)/320000000000), ((-3075663583298356101:ℝ)/3200000000), ((-90887676322102731:ℝ)/80000000), ((-1592597944108323:ℝ)/2000000), ((-73284556952943:ℝ)/200000), ((-5782131637443:ℝ)/50000), ((-3168175437:ℝ)/125), ((-95214966:ℝ)/25), ((-1877394:ℝ)/5), (-21928:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 9 ht
  have m12 := abs_poly_le (fun e => ([((-117198105145067117493:ℝ)/320000000000), ((-3075663583298356101:ℝ)/3200000000), ((-90887676322102731:ℝ)/80000000), ((-1592597944108323:ℝ)/2000000), ((-73284556952943:ℝ)/200000), ((-5782131637443:ℝ)/50000), ((-3168175437:ℝ)/125), ((-95214966:ℝ)/25), ((-1877394:ℝ)/5), (-21928:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 11 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((73228612648330161:ℝ)/16000000000), ((8661831454335789:ℝ)/800000000), ((14341144241313:ℝ)/1250000), ((1783554791193:ℝ)/250000), ((143219629413:ℝ)/50000), ((1922458293:ℝ)/2500), ((17234532:ℝ)/125), ((397632:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - (((73228612648330161:ℝ)/16000000000) + ((8661831454335789:ℝ)/800000000)*t)| ≤ ((236737686447761:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 11, ([((-117198105145067117493:ℝ)/320000000000), ((-3075663583298356101:ℝ)/3200000000), ((-90887676322102731:ℝ)/80000000), ((-1592597944108323:ℝ)/2000000), ((-73284556952943:ℝ)/200000), ((-5782131637443:ℝ)/50000), ((-3168175437:ℝ)/125), ((-95214966:ℝ)/25), ((-1877394:ℝ)/5), (-21928:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e) - ((-117198105145067117493:ℝ)/320000000000) - ((-3075663583298356101:ℝ)/3200000000)*t| ≤ ((470736629809936217:ℝ)/160000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 11, ([((-117198105145067117493:ℝ)/320000000000), ((-3075663583298356101:ℝ)/3200000000), ((-90887676322102731:ℝ)/80000000), ((-1592597944108323:ℝ)/2000000), ((-73284556952943:ℝ)/200000), ((-5782131637443:ℝ)/50000), ((-3168175437:ℝ)/125), ((-95214966:ℝ)/25), ((-1877394:ℝ)/5), (-21928:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((130388570626151143:ℝ)/312500000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((59502537175353561:ℝ)/16000000000) - ((7475627401115589:ℝ)/800000000)*t| ≤ ((214313332515761:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((41:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (600:ℝ), (-7776:ℝ), (16800:ℝ), (-9216:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m13' : |centralNum13_00 q| ≤ ((1445541590648773947:ℝ)/78125000) := by
    rw [centralNum13_00_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((41:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (780:ℝ), (-6156:ℝ), (15288:ℝ), (-14400:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m23' : |centralNum23_00 q| ≤ ((388131050782839687:ℝ)/15625000) := by
    rw [centralNum23_00_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece13_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece13_E11 h0) m23'
  have c5 := scaled_affine (X := ((11148000359:ℝ)/1000000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0))| ≤ ((1075374613986598759475200000000:ℝ)/14143438924398398707158739120972767) := by
    rw [abs_neg, tailWeight_0, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((41:ℝ)/10)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((41:ℝ)/10)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece13_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((10465499600:ℝ)/59049)) ≤ ((41:ℝ)/10)^6*(8000*(2*((41:ℝ)/10)-3)^2*(1/((239520380097857689497853293383:ℝ)/100000000000))*((10465499600:ℝ)/59049)) := by
          gcongr
      _ ≤ ((1075374613986598759475200000000:ℝ)/14143438924398398707158739120972767) := by norm_num
  have c7 := affine_round (α := ((73228612648330161:ℝ)/16000000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((-117198105145067117493:ℝ)/320000000000) + ((59502537175353561:ℝ)/16000000000)*((11148000359:ℝ)/1000000000000) - ((92055040069721673:ℝ)/20000000000)) (β := ((8661831454335789:ℝ)/800000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((-3075663583298356101:ℝ)/3200000000) - 3*((-117198105145067117493:ℝ)/320000000000)) + ((7475627401115589:ℝ)/800000000)*((11148000359:ℝ)/1000000000000) - ((109372830951384483:ℝ)/10000000000)) ht
  have hW : pieceW q pieceX_13 0 0 = centralNum11_00 q + 8*(Real.exp (-(3*((81:ℝ)/20)))*Real.exp (-3*t))*centralNum12_00 q + 18*Real.exp (-8*q)*centralNum13_00 q + 72*Real.exp (-11*q)*centralNum23_00 q + 8*q^7*(2*q-3)^2*((11148000359:ℝ)/1000000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0)) := by
    rw [pieceW_00, pieceX_13, sym4_00, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((395079735381679781795089674874739736471764775394140105094877856651:ℝ)/140221861995655946380436358622066768993079125478676868508000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((73228612648330161:ℝ)/16000000000) + ((8661831454335789:ℝ)/800000000)*t) + (8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((-117198105145067117493:ℝ)/320000000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((-3075663583298356101:ℝ)/3200000000) - 3*((-117198105145067117493:ℝ)/320000000000))*t) + (((59502537175353561:ℝ)/16000000000) + ((7475627401115589:ℝ)/800000000)*t)*((11148000359:ℝ)/1000000000000) - (((92055040069721673:ℝ)/20000000000) + t * ((109372830951384483:ℝ)/10000000000)) = (((73228612648330161:ℝ)/16000000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((-117198105145067117493:ℝ)/320000000000) + ((59502537175353561:ℝ)/16000000000)*((11148000359:ℝ)/1000000000000) - ((92055040069721673:ℝ)/20000000000)) + t*(((8661831454335789:ℝ)/800000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((-3075663583298356101:ℝ)/3200000000) - 3*((-117198105145067117493:ℝ)/320000000000)) + ((7475627401115589:ℝ)/800000000)*((11148000359:ℝ)/1000000000000) - ((109372830951384483:ℝ)/10000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece13_e01 {q : ℝ} (h0 : (4:ℝ) ≤ q) (h1 : q ≤ ((41:ℝ)/10)) :
    |pieceW q pieceX_13 0 1 - (((-181975854277918413:ℝ)/200000000000) + (q - ((81:ℝ)/20)) * ((-29964394066923543:ℝ)/20000000000))| ≤ ((581980739421157441:ℝ)/100000000000000) := by
  set t := q - ((81:ℝ)/20) with htd
  have hq : q = ((81:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece13_L3 piece13_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((81:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_01 q = ∑ e ∈ Finset.range 8, ([((-68630377364883:ℝ)/80000000), ((-5931020266101:ℝ)/4000000), ((-219667417263:ℝ)/200000), ((-903981141:ℝ)/2000), ((-11160261:ℝ)/100), ((-413343:ℝ)/25), ((-6804:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_01; ring
  have h12 : centralNum12_01 q = ∑ e ∈ Finset.range 12, ([((-14444511508895026666419:ℝ)/12800000000000), ((-1119401132499533336247:ℝ)/320000000000), ((-31425058396437646329:ℝ)/6400000000), ((-659547509580601371:ℝ)/160000000), ((-18406068248895147:ℝ)/8000000), ((-896696858899107:ℝ)/1000000), ((-24906139380549:ℝ)/100000), ((-24653404131:ℝ)/500), ((-681879267:ℝ)/100), ((-3136974:ℝ)/5), ((-172836:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_01; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-68630377364883:ℝ)/80000000), ((-5931020266101:ℝ)/4000000), ((-219667417263:ℝ)/200000), ((-903981141:ℝ)/2000), ((-11160261:ℝ)/100), ((-413343:ℝ)/25), ((-6804:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0) 6 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-14444511508895026666419:ℝ)/12800000000000), ((-1119401132499533336247:ℝ)/320000000000), ((-31425058396437646329:ℝ)/6400000000), ((-659547509580601371:ℝ)/160000000), ((-18406068248895147:ℝ)/8000000), ((-896696858899107:ℝ)/1000000), ((-24906139380549:ℝ)/100000), ((-24653404131:ℝ)/500), ((-681879267:ℝ)/100), ((-3136974:ℝ)/5), ((-172836:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0) 10 ht
  have m12 := abs_poly_le (fun e => ([((-14444511508895026666419:ℝ)/12800000000000), ((-1119401132499533336247:ℝ)/320000000000), ((-31425058396437646329:ℝ)/6400000000), ((-659547509580601371:ℝ)/160000000), ((-18406068248895147:ℝ)/8000000), ((-896696858899107:ℝ)/1000000), ((-24906139380549:ℝ)/100000), ((-24653404131:ℝ)/500), ((-681879267:ℝ)/100), ((-3136974:ℝ)/5), ((-172836:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0) 12 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 8, ([((-68630377364883:ℝ)/80000000), ((-5931020266101:ℝ)/4000000), ((-219667417263:ℝ)/200000), ((-903981141:ℝ)/2000), ((-11160261:ℝ)/100), ((-413343:ℝ)/25), ((-6804:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0 * t^e) - (((-68630377364883:ℝ)/80000000) + ((-5931020266101:ℝ)/4000000)*t)| ≤ ((5606088483:ℝ)/2000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 12, ([((-14444511508895026666419:ℝ)/12800000000000), ((-1119401132499533336247:ℝ)/320000000000), ((-31425058396437646329:ℝ)/6400000000), ((-659547509580601371:ℝ)/160000000), ((-18406068248895147:ℝ)/8000000), ((-896696858899107:ℝ)/1000000), ((-24906139380549:ℝ)/100000), ((-24653404131:ℝ)/500), ((-681879267:ℝ)/100), ((-3136974:ℝ)/5), ((-172836:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e) - ((-14444511508895026666419:ℝ)/12800000000000) - ((-1119401132499533336247:ℝ)/320000000000)*t| ≤ ((163908464856690761439:ℝ)/12800000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 12, ([((-14444511508895026666419:ℝ)/12800000000000), ((-1119401132499533336247:ℝ)/320000000000), ((-31425058396437646329:ℝ)/6400000000), ((-659547509580601371:ℝ)/160000000), ((-18406068248895147:ℝ)/8000000), ((-896696858899107:ℝ)/1000000), ((-24906139380549:ℝ)/100000), ((-24653404131:ℝ)/500), ((-681879267:ℝ)/100), ((-3136974:ℝ)/5), ((-172836:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((8226182733765031299:ℝ)/6250000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((59502537175353561:ℝ)/16000000000) - ((7475627401115589:ℝ)/800000000)*t| ≤ ((214313332515761:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((41:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-6288:ℝ), (81024:ℝ), (-238720:ℝ), (246784:ℝ), (-98304:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m13' : |centralNum13_01 q| ≤ ((373824214664684227359:ℝ)/390625000) := by
    rw [centralNum13_01_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((41:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-7368:ℝ), (59208:ℝ), (-155734:ℝ), (205300:ℝ), (-60000:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m23' : |centralNum23_01 q| ≤ ((20675635072398139437:ℝ)/31250000) := by
    rw [centralNum23_01_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece13_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece13_E11 h0) m23'
  have c5 := scaled_affine (X := ((-4578848991:ℝ)/4000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-68630377364883:ℝ)/80000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((-14444511508895026666419:ℝ)/12800000000000) + ((59502537175353561:ℝ)/16000000000)*((-4578848991:ℝ)/4000000000000) - ((-181975854277918413:ℝ)/200000000000)) (β := ((-5931020266101:ℝ)/4000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((-1119401132499533336247:ℝ)/320000000000) - 3*((-14444511508895026666419:ℝ)/12800000000000)) + ((7475627401115589:ℝ)/800000000)*((-4578848991:ℝ)/4000000000000) - ((-29964394066923543:ℝ)/20000000000)) ht
  have hW : pieceW q pieceX_13 0 1 = centralNum11_01 q + 8*(Real.exp (-(3*((81:ℝ)/20)))*Real.exp (-3*t))*centralNum12_01 q + 18*Real.exp (-8*q)*centralNum13_01 q + 72*Real.exp (-11*q)*centralNum23_01 q + 8*q^7*(2*q-3)^2*((-4578848991:ℝ)/4000000000000) + (0:ℝ) := by
    rw [pieceW_01, pieceX_13, sym4_01, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((5390731735318231278600684827673587721622893797841122528082559961517:ℝ)/9535086615704604353869672386300540291529380532550027058544000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-68630377364883:ℝ)/80000000) + ((-5931020266101:ℝ)/4000000)*t) + (8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((-14444511508895026666419:ℝ)/12800000000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((-1119401132499533336247:ℝ)/320000000000) - 3*((-14444511508895026666419:ℝ)/12800000000000))*t) + (((59502537175353561:ℝ)/16000000000) + ((7475627401115589:ℝ)/800000000)*t)*((-4578848991:ℝ)/4000000000000) - (((-181975854277918413:ℝ)/200000000000) + t * ((-29964394066923543:ℝ)/20000000000)) = (((-68630377364883:ℝ)/80000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((-14444511508895026666419:ℝ)/12800000000000) + ((59502537175353561:ℝ)/16000000000)*((-4578848991:ℝ)/4000000000000) - ((-181975854277918413:ℝ)/200000000000)) + t*(((-5931020266101:ℝ)/4000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((-1119401132499533336247:ℝ)/320000000000) - 3*((-14444511508895026666419:ℝ)/12800000000000)) + ((7475627401115589:ℝ)/800000000)*((-4578848991:ℝ)/4000000000000) - ((-29964394066923543:ℝ)/20000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece13_e02 {q : ℝ} (h0 : (4:ℝ) ≤ q) (h1 : q ≤ ((41:ℝ)/10)) :
    |pieceW q pieceX_13 0 2 - (((135754637866512603:ℝ)/10000000000000) + (q - ((81:ℝ)/20)) * ((-424247530263613113:ℝ)/10000000000000))| ≤ ((4532588873584341:ℝ)/3125000000000) := by
  set t := q - ((81:ℝ)/20) with htd
  have hq : q = ((81:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece13_L3 piece13_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((81:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_02 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_02; ring
  have h12 : centralNum12_02 q = ∑ e ∈ Finset.range 13, ([((15632432651792465566929:ℝ)/2048000000000000), ((-180939070072572921355617:ℝ)/102400000000000), ((-26766394521969931502751:ℝ)/5120000000000), ((-359117066045636395839:ℝ)/51200000000), ((-3617365767018554781:ℝ)/640000000), ((-973194879857941341:ℝ)/320000000), ((-18356831018656767:ℝ)/16000000), ((-247683472855731:ℝ)/800000), ((-956012967819:ℝ)/16000), ((-6463929969:ℝ)/800), ((-145789011:ℝ)/200), ((-394767:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_02; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((15632432651792465566929:ℝ)/2048000000000000), ((-180939070072572921355617:ℝ)/102400000000000), ((-26766394521969931502751:ℝ)/5120000000000), ((-359117066045636395839:ℝ)/51200000000), ((-3617365767018554781:ℝ)/640000000), ((-973194879857941341:ℝ)/320000000), ((-18356831018656767:ℝ)/16000000), ((-247683472855731:ℝ)/800000), ((-956012967819:ℝ)/16000), ((-6463929969:ℝ)/800), ((-145789011:ℝ)/200), ((-394767:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((15632432651792465566929:ℝ)/2048000000000000), ((-180939070072572921355617:ℝ)/102400000000000), ((-26766394521969931502751:ℝ)/5120000000000), ((-359117066045636395839:ℝ)/51200000000), ((-3617365767018554781:ℝ)/640000000), ((-973194879857941341:ℝ)/320000000), ((-18356831018656767:ℝ)/16000000), ((-247683472855731:ℝ)/800000), ((-956012967819:ℝ)/16000), ((-6463929969:ℝ)/800), ((-145789011:ℝ)/200), ((-394767:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((15632432651792465566929:ℝ)/2048000000000000), ((-180939070072572921355617:ℝ)/102400000000000), ((-26766394521969931502751:ℝ)/5120000000000), ((-359117066045636395839:ℝ)/51200000000), ((-3617365767018554781:ℝ)/640000000), ((-973194879857941341:ℝ)/320000000), ((-18356831018656767:ℝ)/16000000), ((-247683472855731:ℝ)/800000), ((-956012967819:ℝ)/16000), ((-6463929969:ℝ)/800), ((-145789011:ℝ)/200), ((-394767:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e) - ((15632432651792465566929:ℝ)/2048000000000000) - ((-180939070072572921355617:ℝ)/102400000000000)*t| ≤ ((1789769423196232134903:ℝ)/128000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((15632432651792465566929:ℝ)/2048000000000000), ((-180939070072572921355617:ℝ)/102400000000000), ((-26766394521969931502751:ℝ)/5120000000000), ((-359117066045636395839:ℝ)/51200000000), ((-3617365767018554781:ℝ)/640000000), ((-973194879857941341:ℝ)/320000000), ((-18356831018656767:ℝ)/16000000), ((-247683472855731:ℝ)/800000), ((-956012967819:ℝ)/16000), ((-6463929969:ℝ)/800), ((-145789011:ℝ)/200), ((-394767:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((112603906747752550540497:ℝ)/1024000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((59502537175353561:ℝ)/16000000000) - ((7475627401115589:ℝ)/800000000)*t| ≤ ((214313332515761:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((41:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82080:ℝ), (-967680:ℝ), (3257600:ℝ), (-4474880:ℝ), (2908160:ℝ), (-786432:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_02 q| ≤ ((39942309569391845143483:ℝ)/976562500) := by
    rw [centralNum13_02_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((41:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (87660:ℝ), (-702180:ℝ), ((7421435:ℝ)/4), ((-10854125:ℝ)/4), ((2828125:ℝ)/2), (-187500:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_02 q| ≤ ((3264023629111975582223:ℝ)/200000000) := by
    rw [centralNum23_02_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece13_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece13_E11 h0) m23'
  have c5 := scaled_affine (X := ((71271091163:ℝ)/20000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((15632432651792465566929:ℝ)/2048000000000000) + ((59502537175353561:ℝ)/16000000000)*((71271091163:ℝ)/20000000000000) - ((135754637866512603:ℝ)/10000000000000)) (β := (0:ℝ) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((-180939070072572921355617:ℝ)/102400000000000) - 3*((15632432651792465566929:ℝ)/2048000000000000)) + ((7475627401115589:ℝ)/800000000)*((71271091163:ℝ)/20000000000000) - ((-424247530263613113:ℝ)/10000000000000)) ht
  have hW : pieceW q pieceX_13 0 2 = centralNum11_02 q + 8*(Real.exp (-(3*((81:ℝ)/20)))*Real.exp (-3*t))*centralNum12_02 q + 18*Real.exp (-8*q)*centralNum13_02 q + 72*Real.exp (-11*q)*centralNum23_02 q + 8*q^7*(2*q-3)^2*((71271091163:ℝ)/20000000000000) + (0:ℝ) := by
    rw [pieceW_02, pieceX_13, sym4_02, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((32079126123146742965189704495200215406525507252544444476316914789:ℝ)/3814034646281841741547868954520216116611752213020010823417600000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((15632432651792465566929:ℝ)/2048000000000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((-180939070072572921355617:ℝ)/102400000000000) - 3*((15632432651792465566929:ℝ)/2048000000000000))*t) + (((59502537175353561:ℝ)/16000000000) + ((7475627401115589:ℝ)/800000000)*t)*((71271091163:ℝ)/20000000000000) - (((135754637866512603:ℝ)/10000000000000) + t * ((-424247530263613113:ℝ)/10000000000000)) = ((0:ℝ) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((15632432651792465566929:ℝ)/2048000000000000) + ((59502537175353561:ℝ)/16000000000)*((71271091163:ℝ)/20000000000000) - ((135754637866512603:ℝ)/10000000000000)) + t*((0:ℝ) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((-180939070072572921355617:ℝ)/102400000000000) - 3*((15632432651792465566929:ℝ)/2048000000000000)) + ((7475627401115589:ℝ)/800000000)*((71271091163:ℝ)/20000000000000) - ((-424247530263613113:ℝ)/10000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece13_e03 {q : ℝ} (h0 : (4:ℝ) ≤ q) (h1 : q ≤ ((41:ℝ)/10)) :
    |pieceW q pieceX_13 0 3 - (((-872196643197672363:ℝ)/10000000000000) + (q - ((81:ℝ)/20)) * ((-32043823522873429:ℝ)/62500000000))| ≤ ((7590681969674379:ℝ)/781250000000) := by
  set t := q - ((81:ℝ)/20) with htd
  have hq : q = ((81:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece13_L3 piece13_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((81:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_03 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_03; ring
  have h12 : centralNum12_03 q = ∑ e ∈ Finset.range 14, ([((1709464708113658582706159301:ℝ)/573440000000000000), ((68062676408690899843296297:ℝ)/7168000000000000), ((4544678288682547129161207:ℝ)/358400000000000), ((316432718152584063852393:ℝ)/35840000000000), ((1982058557330705724693:ℝ)/716800000000), ((-47895704027241977619:ℝ)/89600000000), ((-138179609305578081:ℝ)/140000000), ((-57547439551427571:ℝ)/112000000), ((-3607042418026713:ℝ)/22400000), ((-945904098429:ℝ)/28000), ((-67345822791:ℝ)/14000), ((-628829811:ℝ)/1400), ((-3489237:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_03; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((1709464708113658582706159301:ℝ)/573440000000000000), ((68062676408690899843296297:ℝ)/7168000000000000), ((4544678288682547129161207:ℝ)/358400000000000), ((316432718152584063852393:ℝ)/35840000000000), ((1982058557330705724693:ℝ)/716800000000), ((-47895704027241977619:ℝ)/89600000000), ((-138179609305578081:ℝ)/140000000), ((-57547439551427571:ℝ)/112000000), ((-3607042418026713:ℝ)/22400000), ((-945904098429:ℝ)/28000), ((-67345822791:ℝ)/14000), ((-628829811:ℝ)/1400), ((-3489237:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((1709464708113658582706159301:ℝ)/573440000000000000), ((68062676408690899843296297:ℝ)/7168000000000000), ((4544678288682547129161207:ℝ)/358400000000000), ((316432718152584063852393:ℝ)/35840000000000), ((1982058557330705724693:ℝ)/716800000000), ((-47895704027241977619:ℝ)/89600000000), ((-138179609305578081:ℝ)/140000000), ((-57547439551427571:ℝ)/112000000), ((-3607042418026713:ℝ)/22400000), ((-945904098429:ℝ)/28000), ((-67345822791:ℝ)/14000), ((-628829811:ℝ)/1400), ((-3489237:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((1709464708113658582706159301:ℝ)/573440000000000000), ((68062676408690899843296297:ℝ)/7168000000000000), ((4544678288682547129161207:ℝ)/358400000000000), ((316432718152584063852393:ℝ)/35840000000000), ((1982058557330705724693:ℝ)/716800000000), ((-47895704027241977619:ℝ)/89600000000), ((-138179609305578081:ℝ)/140000000), ((-57547439551427571:ℝ)/112000000), ((-3607042418026713:ℝ)/22400000), ((-945904098429:ℝ)/28000), ((-67345822791:ℝ)/14000), ((-628829811:ℝ)/1400), ((-3489237:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((1709464708113658582706159301:ℝ)/573440000000000000) - ((68062676408690899843296297:ℝ)/7168000000000000)*t| ≤ ((3764318750511993529208811:ℝ)/114688000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((1709464708113658582706159301:ℝ)/573440000000000000), ((68062676408690899843296297:ℝ)/7168000000000000), ((4544678288682547129161207:ℝ)/358400000000000), ((316432718152584063852393:ℝ)/35840000000000), ((1982058557330705724693:ℝ)/716800000000), ((-47895704027241977619:ℝ)/89600000000), ((-138179609305578081:ℝ)/140000000), ((-57547439551427571:ℝ)/112000000), ((-3607042418026713:ℝ)/22400000), ((-945904098429:ℝ)/28000), ((-67345822791:ℝ)/14000), ((-628829811:ℝ)/1400), ((-3489237:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((7814597685550711522364799:ℝ)/2240000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((59502537175353561:ℝ)/16000000000) - ((7475627401115589:ℝ)/800000000)*t| ≤ ((214313332515761:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((41:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-812160:ℝ), (8985600:ℝ), (-32225280:ℝ), (52019200:ℝ), ((-305233920:ℝ)/7), ((135528448:ℝ)/7), ((-25165824:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_03 q| ≤ ((9318398533850399048415127:ℝ)/8544921875) := by
    rw [centralNum13_03_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((41:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-833220:ℝ), (6469740:ℝ), ((-68603955:ℝ)/4), ((104396875:ℝ)/4), ((-1001334375:ℝ)/56), ((125828125:ℝ)/28), ((-2343750:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_03 q| ≤ ((95184480554048691124117:ℝ)/350000000) := by
    rw [centralNum23_03_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece13_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece13_E11 h0) m23'
  have c5 := scaled_affine (X := ((-573662206417:ℝ)/10000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((1709464708113658582706159301:ℝ)/573440000000000000) + ((59502537175353561:ℝ)/16000000000)*((-573662206417:ℝ)/10000000000000) - ((-872196643197672363:ℝ)/10000000000000)) (β := (0:ℝ) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((68062676408690899843296297:ℝ)/7168000000000000) - 3*((1709464708113658582706159301:ℝ)/573440000000000000)) + ((7475627401115589:ℝ)/800000000)*((-573662206417:ℝ)/10000000000000) - ((-32043823522873429:ℝ)/62500000000)) ht
  have hW : pieceW q pieceX_13 0 3 = centralNum11_03 q + 8*(Real.exp (-(3*((81:ℝ)/20)))*Real.exp (-3*t))*centralNum12_03 q + 18*Real.exp (-8*q)*centralNum13_03 q + 72*Real.exp (-11*q)*centralNum23_03 q + 8*q^7*(2*q-3)^2*((-573662206417:ℝ)/10000000000000) + (0:ℝ) := by
    rw [pieceW_03, pieceX_13, sym4_03, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((7609489228654042997086484840188198437180026491896410637215913801653:ℝ)/166864015774830576192719266760259455101764159319625473524520000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((1709464708113658582706159301:ℝ)/573440000000000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((68062676408690899843296297:ℝ)/7168000000000000) - 3*((1709464708113658582706159301:ℝ)/573440000000000000))*t) + (((59502537175353561:ℝ)/16000000000) + ((7475627401115589:ℝ)/800000000)*t)*((-573662206417:ℝ)/10000000000000) - (((-872196643197672363:ℝ)/10000000000000) + t * ((-32043823522873429:ℝ)/62500000000)) = ((0:ℝ) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((1709464708113658582706159301:ℝ)/573440000000000000) + ((59502537175353561:ℝ)/16000000000)*((-573662206417:ℝ)/10000000000000) - ((-872196643197672363:ℝ)/10000000000000)) + t*((0:ℝ) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((68062676408690899843296297:ℝ)/7168000000000000) - 3*((1709464708113658582706159301:ℝ)/573440000000000000)) + ((7475627401115589:ℝ)/800000000)*((-573662206417:ℝ)/10000000000000) - ((-32043823522873429:ℝ)/62500000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece13_e11 {q : ℝ} (h0 : (4:ℝ) ≤ q) (h1 : q ≤ ((41:ℝ)/10)) :
    |pieceW q pieceX_13 1 1 - (((72954025879958907:ℝ)/20000000000) + (q - ((81:ℝ)/20)) * ((793559263205429469:ℝ)/100000000000))| ≤ ((227338920235692897:ℝ)/10000000000000) := by
  set t := q - ((81:ℝ)/20) with htd
  have hq : q = ((81:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece13_L3 piece13_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((81:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_11 q = ∑ e ∈ Finset.range 10, ([((14096340595303191:ℝ)/4000000000), ((3136442764740723:ℝ)/400000000), ((39476985567633:ℝ)/5000000), ((1180722133017:ℝ)/250000), ((11550043449:ℝ)/6250), ((612089541:ℝ)/1250), ((10957548:ℝ)/125), ((254928:ℝ)/25), ((3488:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_11; ring
  have h12 : centralNum12_11 q = ∑ e ∈ Finset.range 13, ([((602392767830298469520523:ℝ)/512000000000000), ((35262926957479176723141:ℝ)/25600000000000), ((-2016334982877552662517:ℝ)/1280000000000), ((-60158441840503719573:ℝ)/12800000000), ((-779879600102716407:ℝ)/160000000), ((-239442919046293167:ℝ)/80000000), ((-4912820722440309:ℝ)/4000000), ((-70369620403377:ℝ)/200000), ((-284269320233:ℝ)/4000), ((-5979932929:ℝ)/600), ((-46332657:ℝ)/50), ((-257418:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_11; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((14096340595303191:ℝ)/4000000000), ((3136442764740723:ℝ)/400000000), ((39476985567633:ℝ)/5000000), ((1180722133017:ℝ)/250000), ((11550043449:ℝ)/6250), ((612089541:ℝ)/1250), ((10957548:ℝ)/125), ((254928:ℝ)/25), ((3488:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((602392767830298469520523:ℝ)/512000000000000), ((35262926957479176723141:ℝ)/25600000000000), ((-2016334982877552662517:ℝ)/1280000000000), ((-60158441840503719573:ℝ)/12800000000), ((-779879600102716407:ℝ)/160000000), ((-239442919046293167:ℝ)/80000000), ((-4912820722440309:ℝ)/4000000), ((-70369620403377:ℝ)/200000), ((-284269320233:ℝ)/4000), ((-5979932929:ℝ)/600), ((-46332657:ℝ)/50), ((-257418:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((602392767830298469520523:ℝ)/512000000000000), ((35262926957479176723141:ℝ)/25600000000000), ((-2016334982877552662517:ℝ)/1280000000000), ((-60158441840503719573:ℝ)/12800000000), ((-779879600102716407:ℝ)/160000000), ((-239442919046293167:ℝ)/80000000), ((-4912820722440309:ℝ)/4000000), ((-70369620403377:ℝ)/200000), ((-284269320233:ℝ)/4000), ((-5979932929:ℝ)/600), ((-46332657:ℝ)/50), ((-257418:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((14096340595303191:ℝ)/4000000000), ((3136442764740723:ℝ)/400000000), ((39476985567633:ℝ)/5000000), ((1180722133017:ℝ)/250000), ((11550043449:ℝ)/6250), ((612089541:ℝ)/1250), ((10957548:ℝ)/125), ((254928:ℝ)/25), ((3488:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((14096340595303191:ℝ)/4000000000) + ((3136442764740723:ℝ)/400000000)*t)| ≤ ((488173399052317:ℝ)/24000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((602392767830298469520523:ℝ)/512000000000000), ((35262926957479176723141:ℝ)/25600000000000), ((-2016334982877552662517:ℝ)/1280000000000), ((-60158441840503719573:ℝ)/12800000000), ((-779879600102716407:ℝ)/160000000), ((-239442919046293167:ℝ)/80000000), ((-4912820722440309:ℝ)/4000000), ((-70369620403377:ℝ)/200000), ((-284269320233:ℝ)/4000), ((-5979932929:ℝ)/600), ((-46332657:ℝ)/50), ((-257418:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e) - ((602392767830298469520523:ℝ)/512000000000000) - ((35262926957479176723141:ℝ)/25600000000000)*t| ≤ ((437477557074799402463:ℝ)/96000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((602392767830298469520523:ℝ)/512000000000000), ((35262926957479176723141:ℝ)/25600000000000), ((-2016334982877552662517:ℝ)/1280000000000), ((-60158441840503719573:ℝ)/12800000000), ((-779879600102716407:ℝ)/160000000), ((-239442919046293167:ℝ)/80000000), ((-4912820722440309:ℝ)/4000000), ((-70369620403377:ℝ)/200000), ((-284269320233:ℝ)/4000), ((-5979932929:ℝ)/600), ((-46332657:ℝ)/50), ((-257418:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((2399958406595662161463:ℝ)/1920000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((59502537175353561:ℝ)/16000000000) - ((7475627401115589:ℝ)/800000000)*t| ≤ ((214313332515761:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((41:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-3444:ℝ), (162624:ℝ), (-1531216:ℝ), (4800960:ℝ), (-6350848:ℝ), ((12025856:ℝ)/3), (-1048576:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_11 q| ≤ ((81946071031967932118111:ℝ)/1464843750) := by
    rw [centralNum13_11_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((41:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-4074:ℝ), (159906:ℝ), (-1104799:ℝ), (2801499:ℝ), (-3931375:ℝ), ((5896250:ℝ)/3), (-250000:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_11 q| ≤ ((17056944702010831639603:ℝ)/750000000) := by
    rw [centralNum23_11_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece13_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece13_E11 h0) m23'
  have c5 := scaled_affine (X := ((198552705423:ℝ)/10000000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1))| ≤ ((494735446468832678122956800000000:ℝ)/127290950319585588364428652088754903) := by
    rw [abs_neg, tailWeight_1, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((41:ℝ)/10)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((41:ℝ)/10)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece13_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((4814744136400:ℝ)/531441)) ≤ ((41:ℝ)/10)^6*(8000*(2*((41:ℝ)/10)-3)^2*(1/((239520380097857689497853293383:ℝ)/100000000000))*((4814744136400:ℝ)/531441)) := by
          gcongr
      _ ≤ ((494735446468832678122956800000000:ℝ)/127290950319585588364428652088754903) := by norm_num
  have c7 := affine_round (α := ((14096340595303191:ℝ)/4000000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((602392767830298469520523:ℝ)/512000000000000) + ((59502537175353561:ℝ)/16000000000)*((198552705423:ℝ)/10000000000000) - ((72954025879958907:ℝ)/20000000000)) (β := ((3136442764740723:ℝ)/400000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((35262926957479176723141:ℝ)/25600000000000) - 3*((602392767830298469520523:ℝ)/512000000000000)) + ((7475627401115589:ℝ)/800000000)*((198552705423:ℝ)/10000000000000) - ((793559263205429469:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_13 1 1 = centralNum11_11 q + 8*(Real.exp (-(3*((81:ℝ)/20)))*Real.exp (-3*t))*centralNum12_11 q + 18*Real.exp (-8*q)*centralNum13_11 q + 72*Real.exp (-11*q)*centralNum23_11 q + 8*q^7*(2*q-3)^2*((198552705423:ℝ)/10000000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1)) := by
    rw [pieceW_11, pieceX_13, sym4_11, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((116759285414770773214406480496532415668167003538443053805982439104701:ℝ)/23837716539261510884674180965751350728823451331375067646360000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((14096340595303191:ℝ)/4000000000) + ((3136442764740723:ℝ)/400000000)*t) + (8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((602392767830298469520523:ℝ)/512000000000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((35262926957479176723141:ℝ)/25600000000000) - 3*((602392767830298469520523:ℝ)/512000000000000))*t) + (((59502537175353561:ℝ)/16000000000) + ((7475627401115589:ℝ)/800000000)*t)*((198552705423:ℝ)/10000000000000) - (((72954025879958907:ℝ)/20000000000) + t * ((793559263205429469:ℝ)/100000000000)) = (((14096340595303191:ℝ)/4000000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((602392767830298469520523:ℝ)/512000000000000) + ((59502537175353561:ℝ)/16000000000)*((198552705423:ℝ)/10000000000000) - ((72954025879958907:ℝ)/20000000000)) + t*(((3136442764740723:ℝ)/400000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((35262926957479176723141:ℝ)/25600000000000) - 3*((602392767830298469520523:ℝ)/512000000000000)) + ((7475627401115589:ℝ)/800000000)*((198552705423:ℝ)/10000000000000) - ((793559263205429469:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece13_e12 {q : ℝ} (h0 : (4:ℝ) ≤ q) (h1 : q ≤ ((41:ℝ)/10)) :
    |pieceW q pieceX_13 1 2 - (((-191595185500352119:ℝ)/500000000000) + (q - ((81:ℝ)/20)) * ((-856389696952104163:ℝ)/1000000000000))| ≤ ((103013135444032431:ℝ)/5000000000000) := by
  set t := q - ((81:ℝ)/20) with htd
  have hq : q = ((81:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece13_L3 piece13_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((81:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_12 q = ∑ e ∈ Finset.range 9, ([((-331289846292213:ℝ)/640000000), ((-6558641458281:ℝ)/8000000), ((-197197028901:ℝ)/400000), ((-2342060487:ℝ)/20000), ((3601989:ℝ)/400), ((595593:ℝ)/50), ((14358:ℝ)/5), (312:ℝ), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_12; ring
  have h12 : centralNum12_12 q = ∑ e ∈ Finset.range 14, ([((458752427944400424046667607:ℝ)/81920000000000000), ((22550276350275798681425619:ℝ)/1024000000000000), ((1832437380586742226552429:ℝ)/51200000000000), ((164118429272144665566531:ℝ)/5120000000000), ((1747839283017698480391:ℝ)/102400000000), ((63611603970049258767:ℝ)/12800000000), ((3751488148862163:ℝ)/20000000), ((-7911221150751537:ℝ)/16000000), ((-2249665427964313:ℝ)/9600000), ((-236160366023:ℝ)/4000), ((-18767298237:ℝ)/2000), ((-189102897:ℝ)/200), ((-1111239:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_12; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-331289846292213:ℝ)/640000000), ((-6558641458281:ℝ)/8000000), ((-197197028901:ℝ)/400000), ((-2342060487:ℝ)/20000), ((3601989:ℝ)/400), ((595593:ℝ)/50), ((14358:ℝ)/5), (312:ℝ), ((40:ℝ)/3)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((458752427944400424046667607:ℝ)/81920000000000000), ((22550276350275798681425619:ℝ)/1024000000000000), ((1832437380586742226552429:ℝ)/51200000000000), ((164118429272144665566531:ℝ)/5120000000000), ((1747839283017698480391:ℝ)/102400000000), ((63611603970049258767:ℝ)/12800000000), ((3751488148862163:ℝ)/20000000), ((-7911221150751537:ℝ)/16000000), ((-2249665427964313:ℝ)/9600000), ((-236160366023:ℝ)/4000), ((-18767298237:ℝ)/2000), ((-189102897:ℝ)/200), ((-1111239:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((458752427944400424046667607:ℝ)/81920000000000000), ((22550276350275798681425619:ℝ)/1024000000000000), ((1832437380586742226552429:ℝ)/51200000000000), ((164118429272144665566531:ℝ)/5120000000000), ((1747839283017698480391:ℝ)/102400000000), ((63611603970049258767:ℝ)/12800000000), ((3751488148862163:ℝ)/20000000), ((-7911221150751537:ℝ)/16000000), ((-2249665427964313:ℝ)/9600000), ((-236160366023:ℝ)/4000), ((-18767298237:ℝ)/2000), ((-189102897:ℝ)/200), ((-1111239:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((-331289846292213:ℝ)/640000000), ((-6558641458281:ℝ)/8000000), ((-197197028901:ℝ)/400000), ((-2342060487:ℝ)/20000), ((3601989:ℝ)/400), ((595593:ℝ)/50), ((14358:ℝ)/5), (312:ℝ), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((-331289846292213:ℝ)/640000000) + ((-6558641458281:ℝ)/8000000)*t)| ≤ ((2394584366059:ℝ)/1920000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((458752427944400424046667607:ℝ)/81920000000000000), ((22550276350275798681425619:ℝ)/1024000000000000), ((1832437380586742226552429:ℝ)/51200000000000), ((164118429272144665566531:ℝ)/5120000000000), ((1747839283017698480391:ℝ)/102400000000), ((63611603970049258767:ℝ)/12800000000), ((3751488148862163:ℝ)/20000000), ((-7911221150751537:ℝ)/16000000), ((-2249665427964313:ℝ)/9600000), ((-236160366023:ℝ)/4000), ((-18767298237:ℝ)/2000), ((-189102897:ℝ)/200), ((-1111239:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e) - ((458752427944400424046667607:ℝ)/81920000000000000) - ((22550276350275798681425619:ℝ)/1024000000000000)*t| ≤ ((23000559219041469892761931:ℝ)/245760000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((458752427944400424046667607:ℝ)/81920000000000000), ((22550276350275798681425619:ℝ)/1024000000000000), ((1832437380586742226552429:ℝ)/51200000000000), ((164118429272144665566531:ℝ)/5120000000000), ((1747839283017698480391:ℝ)/102400000000), ((63611603970049258767:ℝ)/12800000000), ((3751488148862163:ℝ)/20000000), ((-7911221150751537:ℝ)/16000000), ((-2249665427964313:ℝ)/9600000), ((-236160366023:ℝ)/4000), ((-18767298237:ℝ)/2000), ((-189102897:ℝ)/200), ((-1111239:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((83493057962777616310493609:ℝ)/12288000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((59502537175353561:ℝ)/16000000000) - ((7475627401115589:ℝ)/800000000)*t| ≤ ((214313332515761:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((41:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (122790:ℝ), (-3586680:ℝ), (28529720:ℝ), (-90761600:ℝ), (137804800:ℝ), ((-332136448:ℝ)/3), ((141819904:ℝ)/3), (-8388608:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_12 q| ≤ ((6516106964253248663593363:ℝ)/2441406250) := by
    rw [centralNum13_12_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((41:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (132555:ℝ), (-3252375:ℝ), ((39743695:ℝ)/2), ((-197111615:ℝ)/4), ((281947375:ℝ)/4), ((-1100234375:ℝ)/24), ((131828125:ℝ)/12), (-781250:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_12 q| ≤ ((34241614419896876479023:ℝ)/50000000) := by
    rw [centralNum23_12_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece13_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece13_E11 h0) m23'
  have c5 := scaled_affine (X := ((-137767972523:ℝ)/5000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-331289846292213:ℝ)/640000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((458752427944400424046667607:ℝ)/81920000000000000) + ((59502537175353561:ℝ)/16000000000)*((-137767972523:ℝ)/5000000000000) - ((-191595185500352119:ℝ)/500000000000)) (β := ((-6558641458281:ℝ)/8000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((22550276350275798681425619:ℝ)/1024000000000000) - 3*((458752427944400424046667607:ℝ)/81920000000000000)) + ((7475627401115589:ℝ)/800000000)*((-137767972523:ℝ)/5000000000000) - ((-856389696952104163:ℝ)/1000000000000)) ht
  have hW : pieceW q pieceX_13 1 2 = centralNum11_12 q + 8*(Real.exp (-(3*((81:ℝ)/20)))*Real.exp (-3*t))*centralNum12_12 q + 18*Real.exp (-8*q)*centralNum13_12 q + 72*Real.exp (-11*q)*centralNum23_12 q + 8*q^7*(2*q-3)^2*((-137767972523:ℝ)/5000000000000) + (0:ℝ) := by
    rw [pieceW_12, pieceX_13, sym4_12, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((67624203289256575867124508240941432767758521858174286295651099267:ℝ)/136215523081494347912423891232864861307562579036428957979200000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-331289846292213:ℝ)/640000000) + ((-6558641458281:ℝ)/8000000)*t) + (8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((458752427944400424046667607:ℝ)/81920000000000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((22550276350275798681425619:ℝ)/1024000000000000) - 3*((458752427944400424046667607:ℝ)/81920000000000000))*t) + (((59502537175353561:ℝ)/16000000000) + ((7475627401115589:ℝ)/800000000)*t)*((-137767972523:ℝ)/5000000000000) - (((-191595185500352119:ℝ)/500000000000) + t * ((-856389696952104163:ℝ)/1000000000000)) = (((-331289846292213:ℝ)/640000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((458752427944400424046667607:ℝ)/81920000000000000) + ((59502537175353561:ℝ)/16000000000)*((-137767972523:ℝ)/5000000000000) - ((-191595185500352119:ℝ)/500000000000)) + t*(((-6558641458281:ℝ)/8000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((22550276350275798681425619:ℝ)/1024000000000000) - 3*((458752427944400424046667607:ℝ)/81920000000000000)) + ((7475627401115589:ℝ)/800000000)*((-137767972523:ℝ)/5000000000000) - ((-856389696952104163:ℝ)/1000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece13_e13 {q : ℝ} (h0 : (4:ℝ) ≤ q) (h1 : q ≤ ((41:ℝ)/10)) :
    |pieceW q pieceX_13 1 3 - (((814583646033642191:ℝ)/1000000000000) + (q - ((81:ℝ)/20)) * ((20071271309439857:ℝ)/5000000000))| ≤ ((594628729131134503:ℝ)/10000000000000) := by
  set t := q - ((81:ℝ)/20) with htd
  have hq : q = ((81:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece13_L3 piece13_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((81:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_13 q = ∑ e ∈ Finset.range 7, ([((-847288609443:ℝ)/3200000), ((-31381059609:ℝ)/80000), ((-387420489:ℝ)/1600), ((-1594323:ℝ)/20), ((-59049:ℝ)/4), (-1458:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_13; ring
  have h12 : centralNum12_13 q = ∑ e ∈ Finset.range 15, ([((-309423576172263532495372099917:ℝ)/22937600000000000000), ((-5622214180679914590408182499:ℝ)/163840000000000000), ((-26444525501334010949351883:ℝ)/896000000000000), ((-396756180739900619410239:ℝ)/1433600000000000), ((2869535875117389721602453:ℝ)/143360000000000), ((135622968809960017211841:ℝ)/7168000000000), ((1681102504466646494007:ℝ)/179200000000), ((12549718450525086819:ℝ)/4480000000), ((58375917239115867:ℝ)/128000000), ((210503976943581:ℝ)/44800000), ((-9166352943123:ℝ)/560000), ((-226315385559:ℝ)/56000), ((-2787588837:ℝ)/5600), ((-9226953:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_13; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-847288609443:ℝ)/3200000), ((-31381059609:ℝ)/80000), ((-387420489:ℝ)/1600), ((-1594323:ℝ)/20), ((-59049:ℝ)/4), (-1458:ℝ), (-60:ℝ)] : List ℝ).getD e 0) 5 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-309423576172263532495372099917:ℝ)/22937600000000000000), ((-5622214180679914590408182499:ℝ)/163840000000000000), ((-26444525501334010949351883:ℝ)/896000000000000), ((-396756180739900619410239:ℝ)/1433600000000000), ((2869535875117389721602453:ℝ)/143360000000000), ((135622968809960017211841:ℝ)/7168000000000), ((1681102504466646494007:ℝ)/179200000000), ((12549718450525086819:ℝ)/4480000000), ((58375917239115867:ℝ)/128000000), ((210503976943581:ℝ)/44800000), ((-9166352943123:ℝ)/560000), ((-226315385559:ℝ)/56000), ((-2787588837:ℝ)/5600), ((-9226953:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-309423576172263532495372099917:ℝ)/22937600000000000000), ((-5622214180679914590408182499:ℝ)/163840000000000000), ((-26444525501334010949351883:ℝ)/896000000000000), ((-396756180739900619410239:ℝ)/1433600000000000), ((2869535875117389721602453:ℝ)/143360000000000), ((135622968809960017211841:ℝ)/7168000000000), ((1681102504466646494007:ℝ)/179200000000), ((12549718450525086819:ℝ)/4480000000), ((58375917239115867:ℝ)/128000000), ((210503976943581:ℝ)/44800000), ((-9166352943123:ℝ)/560000), ((-226315385559:ℝ)/56000), ((-2787588837:ℝ)/5600), ((-9226953:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 7, ([((-847288609443:ℝ)/3200000), ((-31381059609:ℝ)/80000), ((-387420489:ℝ)/1600), ((-1594323:ℝ)/20), ((-59049:ℝ)/4), (-1458:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e) - (((-847288609443:ℝ)/3200000) + ((-31381059609:ℝ)/80000)*t)| ≤ ((1969285611:ℝ)/3200000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-309423576172263532495372099917:ℝ)/22937600000000000000), ((-5622214180679914590408182499:ℝ)/163840000000000000), ((-26444525501334010949351883:ℝ)/896000000000000), ((-396756180739900619410239:ℝ)/1433600000000000), ((2869535875117389721602453:ℝ)/143360000000000), ((135622968809960017211841:ℝ)/7168000000000), ((1681102504466646494007:ℝ)/179200000000), ((12549718450525086819:ℝ)/4480000000), ((58375917239115867:ℝ)/128000000), ((210503976943581:ℝ)/44800000), ((-9166352943123:ℝ)/560000), ((-226315385559:ℝ)/56000), ((-2787588837:ℝ)/5600), ((-9226953:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((-309423576172263532495372099917:ℝ)/22937600000000000000) - ((-5622214180679914590408182499:ℝ)/163840000000000000)*t| ≤ ((848125858051772816309808873:ℝ)/11468800000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-309423576172263532495372099917:ℝ)/22937600000000000000), ((-5622214180679914590408182499:ℝ)/163840000000000000), ((-26444525501334010949351883:ℝ)/896000000000000), ((-396756180739900619410239:ℝ)/1433600000000000), ((2869535875117389721602453:ℝ)/143360000000000), ((135622968809960017211841:ℝ)/7168000000000), ((1681102504466646494007:ℝ)/179200000000), ((12549718450525086819:ℝ)/4480000000), ((58375917239115867:ℝ)/128000000), ((210503976943581:ℝ)/44800000), ((-9166352943123:ℝ)/560000), ((-226315385559:ℝ)/56000), ((-2787588837:ℝ)/5600), ((-9226953:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((87618831788281620065212248789:ℝ)/5734400000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((59502537175353561:ℝ)/16000000000) - ((7475627401115589:ℝ)/800000000)*t| ≤ ((214313332515761:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((41:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2325540:ℝ), (52589280:ℝ), (-375655200:ℝ), (1192958720:ℝ), (-1965096960:ℝ), ((12857851904:ℝ)/7), ((-21171273728:ℝ)/21), ((914358272:ℝ)/3), ((-268435456:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_13 q| ≤ ((53768989681501967693402899929:ℝ)/683593750000) := by
    rw [centralNum13_13_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((41:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2399070:ℝ), (45666930:ℝ), (-251781675:ℝ), ((2452738385:ℝ)/4), ((-14104310625:ℝ)/16), ((74345740625:ℝ)/112), ((-74899765625:ℝ)/336), ((5161328125:ℝ)/168), ((-9765625:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_13 q| ≤ ((301483923967523337369853991:ℝ)/22400000000) := by
    rw [centralNum23_13_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece13_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece13_E11 h0) m23'
  have c5 := scaled_affine (X := ((110924610021:ℝ)/250000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-847288609443:ℝ)/3200000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((-309423576172263532495372099917:ℝ)/22937600000000000000) + ((59502537175353561:ℝ)/16000000000)*((110924610021:ℝ)/250000000000) - ((814583646033642191:ℝ)/1000000000000)) (β := ((-31381059609:ℝ)/80000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((-5622214180679914590408182499:ℝ)/163840000000000000) - 3*((-309423576172263532495372099917:ℝ)/22937600000000000000)) + ((7475627401115589:ℝ)/800000000)*((110924610021:ℝ)/250000000000) - ((20071271309439857:ℝ)/5000000000)) ht
  have hW : pieceW q pieceX_13 1 3 = centralNum11_13 q + 8*(Real.exp (-(3*((81:ℝ)/20)))*Real.exp (-3*t))*centralNum12_13 q + 18*Real.exp (-8*q)*centralNum13_13 q + 72*Real.exp (-11*q)*centralNum23_13 q + 8*q^7*(2*q-3)^2*((110924610021:ℝ)/250000000000) + (0:ℝ) := by
    rw [pieceW_13, pieceX_13, sym4_13, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((137577609740954162663970418334594715985534198641709695959104550141:ℝ)/333728031549661152385438533520518910203528318639250947049040000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-847288609443:ℝ)/3200000) + ((-31381059609:ℝ)/80000)*t) + (8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((-309423576172263532495372099917:ℝ)/22937600000000000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((-5622214180679914590408182499:ℝ)/163840000000000000) - 3*((-309423576172263532495372099917:ℝ)/22937600000000000000))*t) + (((59502537175353561:ℝ)/16000000000) + ((7475627401115589:ℝ)/800000000)*t)*((110924610021:ℝ)/250000000000) - (((814583646033642191:ℝ)/1000000000000) + t * ((20071271309439857:ℝ)/5000000000)) = (((-847288609443:ℝ)/3200000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((-309423576172263532495372099917:ℝ)/22937600000000000000) + ((59502537175353561:ℝ)/16000000000)*((110924610021:ℝ)/250000000000) - ((814583646033642191:ℝ)/1000000000000)) + t*(((-31381059609:ℝ)/80000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((-5622214180679914590408182499:ℝ)/163840000000000000) - 3*((-309423576172263532495372099917:ℝ)/22937600000000000000)) + ((7475627401115589:ℝ)/800000000)*((110924610021:ℝ)/250000000000) - ((20071271309439857:ℝ)/5000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece13_e22 {q : ℝ} (h0 : (4:ℝ) ≤ q) (h1 : q ≤ ((41:ℝ)/10)) :
    |pieceW q pieceX_13 2 2 - (((3365630231395661:ℝ)/1562500000) + (q - ((81:ℝ)/20)) * ((204069426137267099:ℝ)/25000000000))| ≤ ((59253559510500257:ℝ)/500000000000) := by
  set t := q - ((81:ℝ)/20) with htd
  have hq : q = ((81:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece13_L3 piece13_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((81:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_22 q = ∑ e ∈ Finset.range 10, ([((18903730641044337:ℝ)/6400000000), ((2252953584805563:ℝ)/320000000), ((29784968504793:ℝ)/4000000), ((924306574437:ℝ)/200000), ((37320279471:ℝ)/20000), ((510298281:ℝ)/1000), ((2366997:ℝ)/25), ((172316:ℝ)/15), ((2476:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_22; ring
  have h12 : centralNum12_22 q = ∑ e ∈ Finset.range 15, ([((-359351788687716872366526627837:ℝ)/13107200000000000000), ((-50537876846913993096572777253:ℝ)/655360000000000000), ((-168156379007678375526847617:ℝ)/2048000000000000), ((-24798341217314631928328199:ℝ)/819200000000000), ((1422314666762063920033653:ℝ)/81920000000000), ((109906061942594570832801:ℝ)/4096000000000), ((1579012550953827935847:ℝ)/102400000000), ((39176164051512752017:ℝ)/7680000000), ((1476566210245125287:ℝ)/1536000000), ((4284701609614343:ℝ)/76800000), ((-6547729770903:ℝ)/320000), ((-198426643839:ℝ)/32000), ((-2616335397:ℝ)/3200), ((-8993673:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_22; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((18903730641044337:ℝ)/6400000000), ((2252953584805563:ℝ)/320000000), ((29784968504793:ℝ)/4000000), ((924306574437:ℝ)/200000), ((37320279471:ℝ)/20000), ((510298281:ℝ)/1000), ((2366997:ℝ)/25), ((172316:ℝ)/15), ((2476:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-359351788687716872366526627837:ℝ)/13107200000000000000), ((-50537876846913993096572777253:ℝ)/655360000000000000), ((-168156379007678375526847617:ℝ)/2048000000000000), ((-24798341217314631928328199:ℝ)/819200000000000), ((1422314666762063920033653:ℝ)/81920000000000), ((109906061942594570832801:ℝ)/4096000000000), ((1579012550953827935847:ℝ)/102400000000), ((39176164051512752017:ℝ)/7680000000), ((1476566210245125287:ℝ)/1536000000), ((4284701609614343:ℝ)/76800000), ((-6547729770903:ℝ)/320000), ((-198426643839:ℝ)/32000), ((-2616335397:ℝ)/3200), ((-8993673:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-359351788687716872366526627837:ℝ)/13107200000000000000), ((-50537876846913993096572777253:ℝ)/655360000000000000), ((-168156379007678375526847617:ℝ)/2048000000000000), ((-24798341217314631928328199:ℝ)/819200000000000), ((1422314666762063920033653:ℝ)/81920000000000), ((109906061942594570832801:ℝ)/4096000000000), ((1579012550953827935847:ℝ)/102400000000), ((39176164051512752017:ℝ)/7680000000), ((1476566210245125287:ℝ)/1536000000), ((4284701609614343:ℝ)/76800000), ((-6547729770903:ℝ)/320000), ((-198426643839:ℝ)/32000), ((-2616335397:ℝ)/3200), ((-8993673:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((18903730641044337:ℝ)/6400000000), ((2252953584805563:ℝ)/320000000), ((29784968504793:ℝ)/4000000), ((924306574437:ℝ)/200000), ((37320279471:ℝ)/20000), ((510298281:ℝ)/1000), ((2366997:ℝ)/25), ((172316:ℝ)/15), ((2476:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((18903730641044337:ℝ)/6400000000) + ((2252953584805563:ℝ)/320000000)*t)| ≤ ((92184578248543:ℝ)/4800000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-359351788687716872366526627837:ℝ)/13107200000000000000), ((-50537876846913993096572777253:ℝ)/655360000000000000), ((-168156379007678375526847617:ℝ)/2048000000000000), ((-24798341217314631928328199:ℝ)/819200000000000), ((1422314666762063920033653:ℝ)/81920000000000), ((109906061942594570832801:ℝ)/4096000000000), ((1579012550953827935847:ℝ)/102400000000), ((39176164051512752017:ℝ)/7680000000), ((1476566210245125287:ℝ)/1536000000), ((4284701609614343:ℝ)/76800000), ((-6547729770903:ℝ)/320000), ((-198426643839:ℝ)/32000), ((-2616335397:ℝ)/3200), ((-8993673:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e) - ((-359351788687716872366526627837:ℝ)/13107200000000000000) - ((-50537876846913993096572777253:ℝ)/655360000000000000)*t| ≤ ((4112451267059728202198878699:ℝ)/19660800000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-359351788687716872366526627837:ℝ)/13107200000000000000), ((-50537876846913993096572777253:ℝ)/655360000000000000), ((-168156379007678375526847617:ℝ)/2048000000000000), ((-24798341217314631928328199:ℝ)/819200000000000), ((1422314666762063920033653:ℝ)/81920000000000), ((109906061942594570832801:ℝ)/4096000000000), ((1579012550953827935847:ℝ)/102400000000), ((39176164051512752017:ℝ)/7680000000), ((1476566210245125287:ℝ)/1536000000), ((4284701609614343:ℝ)/76800000), ((-6547729770903:ℝ)/320000), ((-198426643839:ℝ)/32000), ((-2616335397:ℝ)/3200), ((-8993673:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e)| ≤ ((309473474784503013198423993167:ℝ)/9830400000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((59502537175353561:ℝ)/16000000000) - ((7475627401115589:ℝ)/800000000)*t| ≤ ((214313332515761:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((41:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82125:ℝ), (-6663750:ℝ), (115666200:ℝ), (-750437000:ℝ), (2277262000:ℝ), (-3656824320:ℝ), (3359621120:ℝ), (-1817706496:ℝ), ((1625292800:ℝ)/3), (-67108864:ℝ)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_22 q| ≤ ((41247538627852190055293470963:ℝ)/292968750000) := by
    rw [centralNum13_22_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((41:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((178425:ℝ)/2), ((-13176075:ℝ)/2), ((777815145:ℝ)/8), ((-3968389015:ℝ)/8), ((9393350195:ℝ)/8), ((-26366634375:ℝ)/16), ((77851609375:ℝ)/64), ((-25714921875:ℝ)/64), ((5236328125:ℝ)/96), ((-9765625:ℝ)/4)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_22 q| ≤ ((935813839784287953371742341:ℝ)/38400000000) := by
    rw [centralNum23_22_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece13_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece13_E11 h0) m23'
  have c5 := scaled_affine (X := ((968561291969:ℝ)/10000000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2))| ≤ ((264122716244646376718329664000000000:ℝ)/1145618552876270295279857868798794127) := by
    rw [abs_neg, tailWeight_2, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((41:ℝ)/10)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((41:ℝ)/10)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece13_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((2570430941234500:ℝ)/4782969)) ≤ ((41:ℝ)/10)^6*(8000*(2*((41:ℝ)/10)-3)^2*(1/((239520380097857689497853293383:ℝ)/100000000000))*((2570430941234500:ℝ)/4782969)) := by
          gcongr
      _ ≤ ((264122716244646376718329664000000000:ℝ)/1145618552876270295279857868798794127) := by norm_num
  have c7 := affine_round (α := ((18903730641044337:ℝ)/6400000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((-359351788687716872366526627837:ℝ)/13107200000000000000) + ((59502537175353561:ℝ)/16000000000)*((968561291969:ℝ)/10000000000000) - ((3365630231395661:ℝ)/1562500000)) (β := ((2252953584805563:ℝ)/320000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((-50537876846913993096572777253:ℝ)/655360000000000000) - 3*((-359351788687716872366526627837:ℝ)/13107200000000000000)) + ((7475627401115589:ℝ)/800000000)*((968561291969:ℝ)/10000000000000) - ((204069426137267099:ℝ)/25000000000)) ht
  have hW : pieceW q pieceX_13 2 2 = centralNum11_22 q + 8*(Real.exp (-(3*((81:ℝ)/20)))*Real.exp (-3*t))*centralNum12_22 q + 18*Real.exp (-8*q)*centralNum13_22 q + 72*Real.exp (-11*q)*centralNum23_22 q + 8*q^7*(2*q-3)^2*((968561291969:ℝ)/10000000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2)) := by
    rw [pieceW_22, pieceX_13, sym4_22, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((1662201676999114349625349743155755262317473868262370074619033101429:ℝ)/3405388077037358697810597280821621532689064475910723949480000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((18903730641044337:ℝ)/6400000000) + ((2252953584805563:ℝ)/320000000)*t) + (8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((-359351788687716872366526627837:ℝ)/13107200000000000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((-50537876846913993096572777253:ℝ)/655360000000000000) - 3*((-359351788687716872366526627837:ℝ)/13107200000000000000))*t) + (((59502537175353561:ℝ)/16000000000) + ((7475627401115589:ℝ)/800000000)*t)*((968561291969:ℝ)/10000000000000) - (((3365630231395661:ℝ)/1562500000) + t * ((204069426137267099:ℝ)/25000000000)) = (((18903730641044337:ℝ)/6400000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((-359351788687716872366526627837:ℝ)/13107200000000000000) + ((59502537175353561:ℝ)/16000000000)*((968561291969:ℝ)/10000000000000) - ((3365630231395661:ℝ)/1562500000)) + t*(((2252953584805563:ℝ)/320000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((-50537876846913993096572777253:ℝ)/655360000000000000) - 3*((-359351788687716872366526627837:ℝ)/13107200000000000000)) + ((7475627401115589:ℝ)/800000000)*((968561291969:ℝ)/10000000000000) - ((204069426137267099:ℝ)/25000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece13_e23 {q : ℝ} (h0 : (4:ℝ) ≤ q) (h1 : q ≤ ((41:ℝ)/10)) :
    |pieceW q pieceX_13 2 3 - (((-139273302231040331:ℝ)/50000000000) + (q - ((81:ℝ)/20)) * ((-36132725881604467:ℝ)/2500000000))| ≤ ((113829670428556599:ℝ)/100000000000) := by
  set t := q - ((81:ℝ)/20) with htd
  have hq : q = ((81:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece13_L3 piece13_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((81:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_23 q = ∑ e ∈ Finset.range 9, ([((129007536052599:ℝ)/160000000), ((47868513359373:ℝ)/32000000), ((2116784241423:ℝ)/1600000), ((58698780381:ℝ)/80000), ((219466179:ℝ)/800), ((13752351:ℝ)/200), ((109893:ℝ)/10), (1006:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_23; ring
  have h12 : centralNum12_23 q = ∑ e ∈ Finset.range 16, ([((134031236773256908404347378914047:ℝ)/3670016000000000000000), ((691216483377713787914859219141:ℝ)/18350080000000000000), ((-22281306654117543043167723087:ℝ)/262144000000000000), ((-9708419028628202610533843151:ℝ)/45875200000000000), ((-187235808433751153826974061:ℝ)/917504000000000), ((-62329771786332181610303127:ℝ)/573440000000000), ((-360656125942026433402221:ℝ)/11468800000000), ((-601725631792968558839:ℝ)/286720000000), ((58718136539418164281:ℝ)/28672000000), ((3621506989689321:ℝ)/4096000), ((61163678175716601:ℝ)/358400000), ((24644013917211:ℝ)/1792000), ((-165243361419:ℝ)/179200), ((-1479468321:ℝ)/4480), ((-13745295:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_23; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((129007536052599:ℝ)/160000000), ((47868513359373:ℝ)/32000000), ((2116784241423:ℝ)/1600000), ((58698780381:ℝ)/80000), ((219466179:ℝ)/800), ((13752351:ℝ)/200), ((109893:ℝ)/10), (1006:ℝ), (40:ℝ)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((134031236773256908404347378914047:ℝ)/3670016000000000000000), ((691216483377713787914859219141:ℝ)/18350080000000000000), ((-22281306654117543043167723087:ℝ)/262144000000000000), ((-9708419028628202610533843151:ℝ)/45875200000000000), ((-187235808433751153826974061:ℝ)/917504000000000), ((-62329771786332181610303127:ℝ)/573440000000000), ((-360656125942026433402221:ℝ)/11468800000000), ((-601725631792968558839:ℝ)/286720000000), ((58718136539418164281:ℝ)/28672000000), ((3621506989689321:ℝ)/4096000), ((61163678175716601:ℝ)/358400000), ((24644013917211:ℝ)/1792000), ((-165243361419:ℝ)/179200), ((-1479468321:ℝ)/4480), ((-13745295:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 14 ht
  have m12 := abs_poly_le (fun e => ([((134031236773256908404347378914047:ℝ)/3670016000000000000000), ((691216483377713787914859219141:ℝ)/18350080000000000000), ((-22281306654117543043167723087:ℝ)/262144000000000000), ((-9708419028628202610533843151:ℝ)/45875200000000000), ((-187235808433751153826974061:ℝ)/917504000000000), ((-62329771786332181610303127:ℝ)/573440000000000), ((-360656125942026433402221:ℝ)/11468800000000), ((-601725631792968558839:ℝ)/286720000000), ((58718136539418164281:ℝ)/28672000000), ((3621506989689321:ℝ)/4096000), ((61163678175716601:ℝ)/358400000), ((24644013917211:ℝ)/1792000), ((-165243361419:ℝ)/179200), ((-1479468321:ℝ)/4480), ((-13745295:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 16 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((129007536052599:ℝ)/160000000), ((47868513359373:ℝ)/32000000), ((2116784241423:ℝ)/1600000), ((58698780381:ℝ)/80000), ((219466179:ℝ)/800), ((13752351:ℝ)/200), ((109893:ℝ)/10), (1006:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e) - (((129007536052599:ℝ)/160000000) + ((47868513359373:ℝ)/32000000)*t)| ≤ ((2176594215447:ℝ)/640000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 16, ([((134031236773256908404347378914047:ℝ)/3670016000000000000000), ((691216483377713787914859219141:ℝ)/18350080000000000000), ((-22281306654117543043167723087:ℝ)/262144000000000000), ((-9708419028628202610533843151:ℝ)/45875200000000000), ((-187235808433751153826974061:ℝ)/917504000000000), ((-62329771786332181610303127:ℝ)/573440000000000), ((-360656125942026433402221:ℝ)/11468800000000), ((-601725631792968558839:ℝ)/286720000000), ((58718136539418164281:ℝ)/28672000000), ((3621506989689321:ℝ)/4096000), ((61163678175716601:ℝ)/358400000), ((24644013917211:ℝ)/1792000), ((-165243361419:ℝ)/179200), ((-1479468321:ℝ)/4480), ((-13745295:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e) - ((134031236773256908404347378914047:ℝ)/3670016000000000000000) - ((691216483377713787914859219141:ℝ)/18350080000000000000)*t| ≤ ((881737287532688234775398653573:ℝ)/3670016000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 16, ([((134031236773256908404347378914047:ℝ)/3670016000000000000000), ((691216483377713787914859219141:ℝ)/18350080000000000000), ((-22281306654117543043167723087:ℝ)/262144000000000000), ((-9708419028628202610533843151:ℝ)/45875200000000000), ((-187235808433751153826974061:ℝ)/917504000000000), ((-62329771786332181610303127:ℝ)/573440000000000), ((-360656125942026433402221:ℝ)/11468800000000), ((-601725631792968558839:ℝ)/286720000000), ((58718136539418164281:ℝ)/28672000000), ((3621506989689321:ℝ)/4096000), ((61163678175716601:ℝ)/358400000), ((24644013917211:ℝ)/1792000), ((-165243361419:ℝ)/179200), ((-1479468321:ℝ)/4480), ((-13745295:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e)| ≤ ((14182513889456673451827136975903:ℝ)/367001600000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((59502537175353561:ℝ)/16000000000) - ((7475627401115589:ℝ)/800000000)*t| ≤ ((214313332515761:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((41:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-7627725:ℝ)/2), (173988600:ℝ), (-2299614450:ℝ), (13088188200:ℝ), (-38221499200:ℝ), (63366115840:ℝ), ((-445610508288:ℝ)/7), ((841540698112:ℝ)/21), ((-326820167680:ℝ)/21), ((10133438464:ℝ)/3), ((-2147483648:ℝ)/7)] : List ℝ).getD e 0) 16 hq1'
  have m13' : |centralNum13_23 q| ≤ ((5833404991380377337971080671361:ℝ)/1281738281250) := by
    rw [centralNum13_23_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((41:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-15801525:ℝ)/4), ((655493865:ℝ)/4), ((-7334421225:ℝ)/4), ((16442962485:ℝ)/2), ((-598626108395:ℝ)/32), ((414013307125:ℝ)/16), ((-4611984703125:ℝ)/224), ((399923828125:ℝ)/48), ((-4353201171875:ℝ)/2688), ((189736328125:ℝ)/1344), ((-244140625:ℝ)/56)] : List ℝ).getD e 0) 16 hq1'
  have m23' : |centralNum23_23 q| ≤ ((297291025513295244300661043191:ℝ)/537600000000) := by
    rw [centralNum23_23_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece13_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece13_E11 h0) m23'
  have c5 := scaled_affine (X := ((-138127623807:ℝ)/100000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((129007536052599:ℝ)/160000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((134031236773256908404347378914047:ℝ)/3670016000000000000000) + ((59502537175353561:ℝ)/16000000000)*((-138127623807:ℝ)/100000000000) - ((-139273302231040331:ℝ)/50000000000)) (β := ((47868513359373:ℝ)/32000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((691216483377713787914859219141:ℝ)/18350080000000000000) - 3*((134031236773256908404347378914047:ℝ)/3670016000000000000000)) + ((7475627401115589:ℝ)/800000000)*((-138127623807:ℝ)/100000000000) - ((-36132725881604467:ℝ)/2500000000)) ht
  have hW : pieceW q pieceX_13 2 3 = centralNum11_23 q + 8*(Real.exp (-(3*((81:ℝ)/20)))*Real.exp (-3*t))*centralNum12_23 q + 18*Real.exp (-8*q)*centralNum13_23 q + 72*Real.exp (-11*q)*centralNum23_23 q + 8*q^7*(2*q-3)^2*((-138127623807:ℝ)/100000000000) + (0:ℝ) := by
    rw [pieceW_23, pieceX_13, sym4_23, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((426081496362855374066946829401093809658672051383284267263455339847:ℝ)/133491212619864460954175413408207564081411327455700378819616000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((129007536052599:ℝ)/160000000) + ((47868513359373:ℝ)/32000000)*t) + (8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((134031236773256908404347378914047:ℝ)/3670016000000000000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((691216483377713787914859219141:ℝ)/18350080000000000000) - 3*((134031236773256908404347378914047:ℝ)/3670016000000000000000))*t) + (((59502537175353561:ℝ)/16000000000) + ((7475627401115589:ℝ)/800000000)*t)*((-138127623807:ℝ)/100000000000) - (((-139273302231040331:ℝ)/50000000000) + t * ((-36132725881604467:ℝ)/2500000000)) = (((129007536052599:ℝ)/160000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((134031236773256908404347378914047:ℝ)/3670016000000000000000) + ((59502537175353561:ℝ)/16000000000)*((-138127623807:ℝ)/100000000000) - ((-139273302231040331:ℝ)/50000000000)) + t*(((47868513359373:ℝ)/32000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((691216483377713787914859219141:ℝ)/18350080000000000000) - 3*((134031236773256908404347378914047:ℝ)/3670016000000000000000)) + ((7475627401115589:ℝ)/800000000)*((-138127623807:ℝ)/100000000000) - ((-36132725881604467:ℝ)/2500000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece13_e33 {q : ℝ} (h0 : (4:ℝ) ≤ q) (h1 : q ≤ ((41:ℝ)/10)) :
    |pieceW q pieceX_13 3 3 - (((834815606652567061:ℝ)/10000000000) + (q - ((81:ℝ)/20)) * ((110682924395723923:ℝ)/500000000))| ≤ ((93391711494618103:ℝ)/2500000000) := by
  set t := q - ((81:ℝ)/20) with htd
  have hq : q = ((81:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece13_L3 piece13_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((81:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_33 q = ∑ e ∈ Finset.range 10, ([((13210856199849681:ℝ)/22400000000), ((1258817763695787:ℝ)/560000000), ((174659516529201:ℝ)/56000000), ((922429333827:ℝ)/400000), ((20999021193:ℝ)/20000), ((314098083:ℝ)/1000), ((3147357:ℝ)/50), ((288702:ℝ)/35), ((4512:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_33; ring
  have h12 : centralNum12_33 q = ∑ e ∈ Finset.range 17, ([((550138294843109358138247183425549:ℝ)/146800640000000000000000), ((14220196482493274248179796734155313:ℝ)/51380224000000000000000), ((396750490891331518606347989414397:ℝ)/513802240000000000000), ((3373489423044886368979249292943:ℝ)/3670016000000000000), ((104352082871824375381359056331:ℝ)/183500800000000000), ((7095353833263116239195787307:ℝ)/45875200000000000), ((-64265999138955677756481333:ℝ)/2293760000000000), ((-921984937314226644720573:ℝ)/22937600000000), ((-123567988733153417355873:ℝ)/8028160000000), ((-1114757701974954479161:ℝ)/401408000000), ((-785147817044530683:ℝ)/14336000000), ((60971304218436657:ℝ)/716800000), ((127636103046681:ℝ)/7168000), ((449914536693:ℝ)/358400), ((-1061169579:ℝ)/17920), ((-461349837:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_33; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((13210856199849681:ℝ)/22400000000), ((1258817763695787:ℝ)/560000000), ((174659516529201:ℝ)/56000000), ((922429333827:ℝ)/400000), ((20999021193:ℝ)/20000), ((314098083:ℝ)/1000), ((3147357:ℝ)/50), ((288702:ℝ)/35), ((4512:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((550138294843109358138247183425549:ℝ)/146800640000000000000000), ((14220196482493274248179796734155313:ℝ)/51380224000000000000000), ((396750490891331518606347989414397:ℝ)/513802240000000000000), ((3373489423044886368979249292943:ℝ)/3670016000000000000), ((104352082871824375381359056331:ℝ)/183500800000000000), ((7095353833263116239195787307:ℝ)/45875200000000000), ((-64265999138955677756481333:ℝ)/2293760000000000), ((-921984937314226644720573:ℝ)/22937600000000), ((-123567988733153417355873:ℝ)/8028160000000), ((-1114757701974954479161:ℝ)/401408000000), ((-785147817044530683:ℝ)/14336000000), ((60971304218436657:ℝ)/716800000), ((127636103046681:ℝ)/7168000), ((449914536693:ℝ)/358400), ((-1061169579:ℝ)/17920), ((-461349837:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 15 ht
  have m12 := abs_poly_le (fun e => ([((550138294843109358138247183425549:ℝ)/146800640000000000000000), ((14220196482493274248179796734155313:ℝ)/51380224000000000000000), ((396750490891331518606347989414397:ℝ)/513802240000000000000), ((3373489423044886368979249292943:ℝ)/3670016000000000000), ((104352082871824375381359056331:ℝ)/183500800000000000), ((7095353833263116239195787307:ℝ)/45875200000000000), ((-64265999138955677756481333:ℝ)/2293760000000000), ((-921984937314226644720573:ℝ)/22937600000000), ((-123567988733153417355873:ℝ)/8028160000000), ((-1114757701974954479161:ℝ)/401408000000), ((-785147817044530683:ℝ)/14336000000), ((60971304218436657:ℝ)/716800000), ((127636103046681:ℝ)/7168000), ((449914536693:ℝ)/358400), ((-1061169579:ℝ)/17920), ((-461349837:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 17 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((13210856199849681:ℝ)/22400000000), ((1258817763695787:ℝ)/560000000), ((174659516529201:ℝ)/56000000), ((922429333827:ℝ)/400000), ((20999021193:ℝ)/20000), ((314098083:ℝ)/1000), ((3147357:ℝ)/50), ((288702:ℝ)/35), ((4512:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e) - (((13210856199849681:ℝ)/22400000000) + ((1258817763695787:ℝ)/560000000)*t)| ≤ ((181265735877337:ℝ)/22400000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 17, ([((550138294843109358138247183425549:ℝ)/146800640000000000000000), ((14220196482493274248179796734155313:ℝ)/51380224000000000000000), ((396750490891331518606347989414397:ℝ)/513802240000000000000), ((3373489423044886368979249292943:ℝ)/3670016000000000000), ((104352082871824375381359056331:ℝ)/183500800000000000), ((7095353833263116239195787307:ℝ)/45875200000000000), ((-64265999138955677756481333:ℝ)/2293760000000000), ((-921984937314226644720573:ℝ)/22937600000000), ((-123567988733153417355873:ℝ)/8028160000000), ((-1114757701974954479161:ℝ)/401408000000), ((-785147817044530683:ℝ)/14336000000), ((60971304218436657:ℝ)/716800000), ((127636103046681:ℝ)/7168000), ((449914536693:ℝ)/358400), ((-1061169579:ℝ)/17920), ((-461349837:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e) - ((550138294843109358138247183425549:ℝ)/146800640000000000000000) - ((14220196482493274248179796734155313:ℝ)/51380224000000000000000)*t| ≤ ((1052763528697730874539125694554867:ℝ)/513802240000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 17, ([((550138294843109358138247183425549:ℝ)/146800640000000000000000), ((14220196482493274248179796734155313:ℝ)/51380224000000000000000), ((396750490891331518606347989414397:ℝ)/513802240000000000000), ((3373489423044886368979249292943:ℝ)/3670016000000000000), ((104352082871824375381359056331:ℝ)/183500800000000000), ((7095353833263116239195787307:ℝ)/45875200000000000), ((-64265999138955677756481333:ℝ)/2293760000000000), ((-921984937314226644720573:ℝ)/22937600000000), ((-123567988733153417355873:ℝ)/8028160000000), ((-1114757701974954479161:ℝ)/401408000000), ((-785147817044530683:ℝ)/14336000000), ((60971304218436657:ℝ)/716800000), ((127636103046681:ℝ)/7168000), ((449914536693:ℝ)/358400), ((-1061169579:ℝ)/17920), ((-461349837:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e)| ≤ ((288238451482721450060368262960627:ℝ)/14680064000000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((59502537175353561:ℝ)/16000000000), ((7475627401115589:ℝ)/800000000), ((51872891533677:ℝ)/5000000), ((208819643571:ℝ)/31250), ((137639498913:ℝ)/50000), ((1881123993:ℝ)/2500), ((17064432:ℝ)/125), ((396432:ℝ)/25), ((5352:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((59502537175353561:ℝ)/16000000000) - ((7475627401115589:ℝ)/800000000)*t| ≤ ((214313332515761:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((41:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-8120475:ℝ)/4), ((464861025:ℝ)/2), (-5906535975:ℝ), ((411904731750:ℝ)/7), ((-2024051769000:ℝ)/7), ((5554394637600:ℝ)/7), (-1314913862656:ℝ), ((9709155336192:ℝ)/7), ((-6724555112448:ℝ)/7), ((1313173667840:ℝ)/3), ((-6168244125696:ℝ)/49), ((3004329623552:ℝ)/147), ((-68719476736:ℝ)/49)] : List ℝ).getD e 0) 17 hq1'
  have m13' : |centralNum13_33 q| ≤ ((16439312576341655828796607788981493:ℝ)/102539062500000) := by
    rw [centralNum13_33_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((41:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-16872075:ℝ)/8), ((1833754545:ℝ)/8), ((-83998007145:ℝ)/16), ((4929124002765:ℝ)/112), ((-76723155584685:ℝ)/448), ((164888745653055:ℝ)/448), ((-63358359907625:ℝ)/128), ((364713160040625:ℝ)/896), ((-334937462578125:ℝ)/1792), ((245466998046875:ℝ)/5376), ((-72144521484375:ℝ)/12544), ((6518798828125:ℝ)/18816), ((-6103515625:ℝ)/784)] : List ℝ).getD e 0) 17 hq1'
  have m23' : |centralNum23_33 q| ≤ ((429024526453618482418043101187491:ℝ)/30105600000000) := by
    rw [centralNum23_33_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece13_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece13_E11 h0) m23'
  have c5 := scaled_affine (X := ((27808308009:ℝ)/1250000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3))| ≤ ((339969831534352134840987873728000000000:ℝ)/30931700927659297972556162457567441429) := by
    rw [abs_neg, tailWeight_3, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((41:ℝ)/10)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((41:ℝ)/10)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece13_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((3308571812705231500:ℝ)/129140163)) ≤ ((41:ℝ)/10)^6*(8000*(2*((41:ℝ)/10)-3)^2*(1/((239520380097857689497853293383:ℝ)/100000000000))*((3308571812705231500:ℝ)/129140163)) := by
          gcongr
      _ ≤ ((339969831534352134840987873728000000000:ℝ)/30931700927659297972556162457567441429) := by norm_num
  have c7 := affine_round (α := ((13210856199849681:ℝ)/22400000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((550138294843109358138247183425549:ℝ)/146800640000000000000000) + ((59502537175353561:ℝ)/16000000000)*((27808308009:ℝ)/1250000000) - ((834815606652567061:ℝ)/10000000000)) (β := ((1258817763695787:ℝ)/560000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((14220196482493274248179796734155313:ℝ)/51380224000000000000000) - 3*((550138294843109358138247183425549:ℝ)/146800640000000000000000)) + ((7475627401115589:ℝ)/800000000)*((27808308009:ℝ)/1250000000) - ((110682924395723923:ℝ)/500000000)) ht
  have hW : pieceW q pieceX_13 3 3 = centralNum11_33 q + 8*(Real.exp (-(3*((81:ℝ)/20)))*Real.exp (-3*t))*centralNum12_33 q + 18*Real.exp (-8*q)*centralNum13_33 q + 72*Real.exp (-11*q)*centralNum23_33 q + 8*q^7*(2*q-3)^2*((27808308009:ℝ)/1250000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3)) := by
    rw [pieceW_33, pieceX_13, sym4_33, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((5911198527643400469798149988590669990774083705647012194955874548333:ℝ)/146006013802976754168629358415227023214043639404672289333955000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((13210856199849681:ℝ)/22400000000) + ((1258817763695787:ℝ)/560000000)*t) + (8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((550138294843109358138247183425549:ℝ)/146800640000000000000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((14220196482493274248179796734155313:ℝ)/51380224000000000000000) - 3*((550138294843109358138247183425549:ℝ)/146800640000000000000000))*t) + (((59502537175353561:ℝ)/16000000000) + ((7475627401115589:ℝ)/800000000)*t)*((27808308009:ℝ)/1250000000) - (((834815606652567061:ℝ)/10000000000) + t * ((110682924395723923:ℝ)/500000000)) = (((13210856199849681:ℝ)/22400000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*((550138294843109358138247183425549:ℝ)/146800640000000000000000) + ((59502537175353561:ℝ)/16000000000)*((27808308009:ℝ)/1250000000) - ((834815606652567061:ℝ)/10000000000)) + t*(((1258817763695787:ℝ)/560000000) + 8*(((1/((189094089956474140623031291221:ℝ)/1000000000000000000000000))+(1/((9454704485244025628860692337:ℝ)/50000000000000000000000)))/2)*(((14220196482493274248179796734155313:ℝ)/51380224000000000000000) - 3*((550138294843109358138247183425549:ℝ)/146800640000000000000000)) + ((7475627401115589:ℝ)/800000000)*((27808308009:ℝ)/1250000000) - ((110682924395723923:ℝ)/500000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece13_plus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((92055040069721673:ℝ)/20000000000) + ((1:ℝ)/20)*((109372830951384483:ℝ)/10000000000) - (((153680921241767561:ℝ)/5000000000000) + ((581980739421157441:ℝ)/100000000000000) + ((4532588873584341:ℝ)/3125000000000) + ((7590681969674379:ℝ)/781250000000)))
      (((-181975854277918413:ℝ)/200000000000) + ((1:ℝ)/20)*((-29964394066923543:ℝ)/20000000000))
      (((135754637866512603:ℝ)/10000000000000) + ((1:ℝ)/20)*((-424247530263613113:ℝ)/10000000000000))
      (((-872196643197672363:ℝ)/10000000000000) + ((1:ℝ)/20)*((-32043823522873429:ℝ)/62500000000))
      (((72954025879958907:ℝ)/20000000000) + ((1:ℝ)/20)*((793559263205429469:ℝ)/100000000000) - (((581980739421157441:ℝ)/100000000000000) + ((227338920235692897:ℝ)/10000000000000) + ((103013135444032431:ℝ)/5000000000000) + ((594628729131134503:ℝ)/10000000000000)))
      (((-191595185500352119:ℝ)/500000000000) + ((1:ℝ)/20)*((-856389696952104163:ℝ)/1000000000000))
      (((814583646033642191:ℝ)/1000000000000) + ((1:ℝ)/20)*((20071271309439857:ℝ)/5000000000))
      (((3365630231395661:ℝ)/1562500000) + ((1:ℝ)/20)*((204069426137267099:ℝ)/25000000000) - (((4532588873584341:ℝ)/3125000000000) + ((103013135444032431:ℝ)/5000000000000) + ((59253559510500257:ℝ)/500000000000) + ((113829670428556599:ℝ)/100000000000)))
      (((-139273302231040331:ℝ)/50000000000) + ((1:ℝ)/20)*((-36132725881604467:ℝ)/2500000000))
      (((834815606652567061:ℝ)/10000000000) + ((1:ℝ)/20)*((110682924395723923:ℝ)/500000000) - (((7590681969674379:ℝ)/781250000000) + ((594628729131134503:ℝ)/10000000000000) + ((113829670428556599:ℝ)/100000000000) + ((93391711494618103:ℝ)/2500000000))) i j :=
  quadForm_nonneg_of_ldl ((102037873304794215683:ℝ)/20000000000000) ((38221072317305325148818353868218286712187:ℝ)/10203787330479421568300000000000000) ((13489971914873903146100469026399418522177987327601360186277017:ℝ)/10920306376372950042519529676633796203482000000000000000) ((219014270499606315314269979124251846215196716383487929973628242341377938962100490751:ℝ)/4721490170205866101135164159239796482762295564660476065196955950000000000000) ((-19695805131138018450:ℝ)/102037873304794215683) ((2290845227066638947:ℝ)/1020378733047942156830) ((-2257094462761319590:ℝ)/102037873304794215683) ((-617764849882199081223914626395907158710:ℝ)/5460153188186475021259764838316898101741) ((10137591662446999100156269870446113298800:ℝ)/38221072317305325148818353868218286712187) ((-37079470103414542418223143962289566703562667920328175437502900:ℝ)/13489971914873903146100469026399418522177987327601360186277017)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece13_minus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((92055040069721673:ℝ)/20000000000) - ((1:ℝ)/20)*((109372830951384483:ℝ)/10000000000) - (((153680921241767561:ℝ)/5000000000000) + ((581980739421157441:ℝ)/100000000000000) + ((4532588873584341:ℝ)/3125000000000) + ((7590681969674379:ℝ)/781250000000)))
      (((-181975854277918413:ℝ)/200000000000) - ((1:ℝ)/20)*((-29964394066923543:ℝ)/20000000000))
      (((135754637866512603:ℝ)/10000000000000) - ((1:ℝ)/20)*((-424247530263613113:ℝ)/10000000000000))
      (((-872196643197672363:ℝ)/10000000000000) - ((1:ℝ)/20)*((-32043823522873429:ℝ)/62500000000))
      (((72954025879958907:ℝ)/20000000000) - ((1:ℝ)/20)*((793559263205429469:ℝ)/100000000000) - (((581980739421157441:ℝ)/100000000000000) + ((227338920235692897:ℝ)/10000000000000) + ((103013135444032431:ℝ)/5000000000000) + ((594628729131134503:ℝ)/10000000000000)))
      (((-191595185500352119:ℝ)/500000000000) - ((1:ℝ)/20)*((-856389696952104163:ℝ)/1000000000000))
      (((814583646033642191:ℝ)/1000000000000) - ((1:ℝ)/20)*((20071271309439857:ℝ)/5000000000))
      (((3365630231395661:ℝ)/1562500000) - ((1:ℝ)/20)*((204069426137267099:ℝ)/25000000000) - (((4532588873584341:ℝ)/3125000000000) + ((103013135444032431:ℝ)/5000000000000) + ((59253559510500257:ℝ)/500000000000) + ((113829670428556599:ℝ)/100000000000)))
      (((-139273302231040331:ℝ)/50000000000) - ((1:ℝ)/20)*((-36132725881604467:ℝ)/2500000000))
      (((834815606652567061:ℝ)/10000000000) - ((1:ℝ)/20)*((110682924395723923:ℝ)/500000000) - (((7590681969674379:ℝ)/781250000000) + ((594628729131134503:ℝ)/10000000000000) + ((113829670428556599:ℝ)/100000000000) + ((93391711494618103:ℝ)/2500000000))) i j :=
  quadForm_nonneg_of_ldl ((80163307114517319083:ℝ)/20000000000000) ((23795391660627205077464329237600829342087:ℝ)/8016330711451731908300000000000000) ((20400427963596942873243977757890339235445292309959674778573539:ℝ)/47590783321254410154928658475201658684174000000000000000) ((24937605473973638179080842898238839508453468337697812713576702045608059512509778531:ℝ)/1020021398179847143662198887894516961772264615497983738928676950000000000000) ((-16699365724445664150:ℝ)/80163307114517319083) ((3139340287593865173:ℝ)/801633071145173190830) ((-1231692110029369862:ℝ)/80163307114517319083) ((-2702313092155120597780809791203249338780:ℝ)/23795391660627205077464329237600829342087) ((4818150027561912140499293601460012717800:ℝ)/23795391660627205077464329237600829342087) ((-94910932259990009696953273337712744153750582665314137642093860:ℝ)/20400427963596942873243977757890339235445292309959674778573539)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

/-- **Piece 13.** The piece matrix is positive semidefinite on `q ∈ [4, 41/10]`. -/
theorem piece_13 {q : ℝ} (h0 : (4:ℝ) ≤ q) (h1 : q ≤ ((41:ℝ)/10)) (y : Fin 4 → ℝ) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceW q pieceX_13 i j :=
  pieceForm_nonneg (pieceW_symm (sym4_symm _ _ _ _ _ _ _ _ _ _) q) (by norm_num : (0:ℝ) < ((1:ℝ)/20))
    (abs_le.mpr ⟨by linarith, by linarith⟩)
    (piece13_e00 h0 h1) (piece13_e01 h0 h1) (piece13_e02 h0 h1) (piece13_e03 h0 h1) (piece13_e11 h0 h1) (piece13_e12 h0 h1) (piece13_e13 h0 h1) (piece13_e22 h0 h1) (piece13_e23 h0 h1) (piece13_e33 h0 h1)
    piece13_plus piece13_minus y

/-! #### Piece 14 (seam), `q ∈ [41/10, 21/5]` -/

/-- The compensation matrix of piece 14. -/
def pieceX_14 : Fin 4 → Fin 4 → ℝ :=
  sym4 ((111214274551:ℝ)/10000000000000) ((-108101808163:ℝ)/100000000000000) ((162533601993:ℝ)/50000000000000) ((-175486873537:ℝ)/5000000000000) ((103176780923:ℝ)/5000000000000) ((-14470057141:ℝ)/500000000000) ((39090608763:ℝ)/125000000000) ((98022118669:ℝ)/1000000000000) ((-939590876347:ℝ)/1000000000000) ((25404409743:ℝ)/2500000000)

theorem piece14_L3 : ((127625157653632984343797997311:ℝ)/500000000000000000000000) ≤ Real.exp ((3:ℝ)*((83:ℝ)/20)) := by
  have h := le_exp_nat_add 12 (f := ((9:ℝ)/20)) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((83:ℝ)/20) = ((12:ℕ):ℝ) + ((9:ℝ)/20) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece14_U3 : Real.exp ((3:ℝ)*((83:ℝ)/20)) ≤ ((255250323281310323230844226733:ℝ)/1000000000000000000000000) := by
  have h := exp_nat_add_le 12 (f := ((9:ℝ)/20)) (by norm_num) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((83:ℝ)/20) = ((12:ℕ):ℝ) + ((9:ℝ)/20) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem piece14_L8_at : ((43933734775493992670979870427:ℝ)/250000000000000) ≤ Real.exp ((8:ℝ)*((41:ℝ)/10)) := by
  have h := le_exp_nat_add 32 (f := ((4:ℝ)/5)) (by norm_num)
  rw [show ((8:ℝ):ℝ)*((41:ℝ)/10) = ((32:ℕ):ℝ) + ((4:ℝ)/5) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece14_E8 {q : ℝ} (h0 : ((41:ℝ)/10) ≤ q) : Real.exp (-((8:ℝ))*q) ≤ 1/((43933734775493992670979870427:ℝ)/250000000000000) := by
  have hm : Real.exp (-((8:ℝ))*q) ≤ Real.exp (-((8:ℝ)*((41:ℝ)/10))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece14_L8_at (le_refl _)).2

theorem piece14_L11_at : ((193041701576213268831412776967:ℝ)/5000000000) ≤ Real.exp ((11:ℝ)*((41:ℝ)/10)) := by
  have h := le_exp_nat_add 45 (f := ((1:ℝ)/10)) (by norm_num)
  rw [show ((11:ℝ):ℝ)*((41:ℝ)/10) = ((45:ℕ):ℝ) + ((1:ℝ)/10) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece14_E11 {q : ℝ} (h0 : ((41:ℝ)/10) ≤ q) : Real.exp (-((11:ℝ))*q) ≤ 1/((193041701576213268831412776967:ℝ)/5000000000) := by
  have hm : Real.exp (-((11:ℝ))*q) ≤ Real.exp (-((11:ℝ)*((41:ℝ)/10))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece14_L11_at (le_refl _)).2

theorem piece14_Lt_at : ((172490841285844495920402488413:ℝ)/25000000000) ≤ Real.exp (((529:ℝ)/50)*((41:ℝ)/10)) := by
  have h := le_exp_nat_add 43 (f := ((189:ℝ)/500)) (by norm_num)
  rw [show (((529:ℝ)/50):ℝ)*((41:ℝ)/10) = ((43:ℕ):ℝ) + ((189:ℝ)/500) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece14_Et {q : ℝ} (h0 : ((41:ℝ)/10) ≤ q) : Real.exp (-(((529:ℝ)/50))*q) ≤ 1/((172490841285844495920402488413:ℝ)/25000000000) := by
  have hm : Real.exp (-(((529:ℝ)/50))*q) ≤ Real.exp (-(((529:ℝ)/50)*((41:ℝ)/10))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece14_Lt_at (le_refl _)).2

theorem piece14_e00 {q : ℝ} (h0 : ((41:ℝ)/10) ≤ q) (h1 : q ≤ ((21:ℝ)/5)) :
    |pieceW q pieceX_14 0 0 - (((581978479844851799:ℝ)/100000000000) + (q - ((83:ℝ)/20)) * ((134836843187854117:ℝ)/10000000000))| ≤ ((183519573022389503:ℝ)/5000000000000) := by
  set t := q - ((83:ℝ)/20) with htd
  have hq : q = ((83:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece14_L3 piece14_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((83:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_00 q = ∑ e ∈ Finset.range 10, ([((92506797823638443:ℝ)/16000000000), ((10678199534604909:ℝ)/800000000), ((17241180894411:ℝ)/1250000), ((2089922081877:ℝ)/250000), ((163506495159:ℝ)/50000), ((2137773813:ℝ)/2500), ((18664044:ℝ)/125), ((419328:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_00; ring
  have h12 : centralNum12_00 q = ∑ e ∈ Finset.range 11, ([((-151857167521142229407:ℝ)/320000000000), ((-3884089887647404173:ℝ)/3200000000), ((-111853301404757511:ℝ)/80000000), ((-1909905599034171:ℝ)/2000000), ((-85636373743557:ℝ)/200000), ((-6583549255899:ℝ)/50000), ((-3514801332:ℝ)/125), ((-102923622:ℝ)/25), ((-1977366:ℝ)/5), (-22504:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_00; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((92506797823638443:ℝ)/16000000000), ((10678199534604909:ℝ)/800000000), ((17241180894411:ℝ)/1250000), ((2089922081877:ℝ)/250000), ((163506495159:ℝ)/50000), ((2137773813:ℝ)/2500), ((18664044:ℝ)/125), ((419328:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-151857167521142229407:ℝ)/320000000000), ((-3884089887647404173:ℝ)/3200000000), ((-111853301404757511:ℝ)/80000000), ((-1909905599034171:ℝ)/2000000), ((-85636373743557:ℝ)/200000), ((-6583549255899:ℝ)/50000), ((-3514801332:ℝ)/125), ((-102923622:ℝ)/25), ((-1977366:ℝ)/5), (-22504:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 9 ht
  have m12 := abs_poly_le (fun e => ([((-151857167521142229407:ℝ)/320000000000), ((-3884089887647404173:ℝ)/3200000000), ((-111853301404757511:ℝ)/80000000), ((-1909905599034171:ℝ)/2000000), ((-85636373743557:ℝ)/200000), ((-6583549255899:ℝ)/50000), ((-3514801332:ℝ)/125), ((-102923622:ℝ)/25), ((-1977366:ℝ)/5), (-22504:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 11 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((92506797823638443:ℝ)/16000000000), ((10678199534604909:ℝ)/800000000), ((17241180894411:ℝ)/1250000), ((2089922081877:ℝ)/250000), ((163506495159:ℝ)/50000), ((2137773813:ℝ)/2500), ((18664044:ℝ)/125), ((419328:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - (((92506797823638443:ℝ)/16000000000) + ((10678199534604909:ℝ)/800000000)*t)| ≤ ((71096061419069:ℝ)/2000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 11, ([((-151857167521142229407:ℝ)/320000000000), ((-3884089887647404173:ℝ)/3200000000), ((-111853301404757511:ℝ)/80000000), ((-1909905599034171:ℝ)/2000000), ((-85636373743557:ℝ)/200000), ((-6583549255899:ℝ)/50000), ((-3514801332:ℝ)/125), ((-102923622:ℝ)/25), ((-1977366:ℝ)/5), (-22504:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e) - ((-151857167521142229407:ℝ)/320000000000) - ((-3884089887647404173:ℝ)/3200000000)*t| ≤ ((36175024952826653:ℝ)/10000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 11, ([((-151857167521142229407:ℝ)/320000000000), ((-3884089887647404173:ℝ)/3200000000), ((-111853301404757511:ℝ)/80000000), ((-1909905599034171:ℝ)/2000000), ((-85636373743557:ℝ)/200000), ((-6583549255899:ℝ)/50000), ((-3514801332:ℝ)/125), ((-102923622:ℝ)/25), ((-1977366:ℝ)/5), (-22504:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((5262305229427176:ℝ)/9765625) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((76225167229862243:ℝ)/16000000000) - ((9305049966455109:ℝ)/800000000)*t| ≤ ((64765982479019:ℝ)/2000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (600:ℝ), (-7776:ℝ), (16800:ℝ), (-9216:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m13' : |centralNum13_00 q| ≤ ((227929152508257816:ℝ)/9765625) := by
    rw [centralNum13_00_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (780:ℝ), (-6156:ℝ), (15288:ℝ), (-14400:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m23' : |centralNum23_00 q| ≤ ((61380319407030288:ℝ)/1953125) := by
    rw [centralNum23_00_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece14_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece14_E11 h0) m23'
  have c5 := scaled_affine (X := ((111214274551:ℝ)/10000000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0))| ≤ ((5673625631725363200000000:ℝ)/172490841285844495920402488413) := by
    rw [abs_neg, tailWeight_0, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((21:ℝ)/5)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((21:ℝ)/5)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece14_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((10465499600:ℝ)/59049)) ≤ ((21:ℝ)/5)^6*(8000*(2*((21:ℝ)/5)-3)^2*(1/((172490841285844495920402488413:ℝ)/25000000000))*((10465499600:ℝ)/59049)) := by
          gcongr
      _ ≤ ((5673625631725363200000000:ℝ)/172490841285844495920402488413) := by norm_num
  have c7 := affine_round (α := ((92506797823638443:ℝ)/16000000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((-151857167521142229407:ℝ)/320000000000) + ((76225167229862243:ℝ)/16000000000)*((111214274551:ℝ)/10000000000000) - ((581978479844851799:ℝ)/100000000000)) (β := ((10678199534604909:ℝ)/800000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((-3884089887647404173:ℝ)/3200000000) - 3*((-151857167521142229407:ℝ)/320000000000)) + ((9305049966455109:ℝ)/800000000)*((111214274551:ℝ)/10000000000000) - ((134836843187854117:ℝ)/10000000000)) ht
  have hW : pieceW q pieceX_14 0 0 = centralNum11_00 q + 8*(Real.exp (-(3*((83:ℝ)/20)))*Real.exp (-3*t))*centralNum12_00 q + 18*Real.exp (-8*q)*centralNum13_00 q + 72*Real.exp (-11*q)*centralNum23_00 q + 8*q^7*(2*q-3)^2*((111214274551:ℝ)/10000000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0)) := by
    rw [pieceW_00, pieceX_14, sym4_00, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((8510609599141173660526945596407948439422686747510692498099572496511429:ℝ)/2606109019993441258331146371185900963387014845328944665197040000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((92506797823638443:ℝ)/16000000000) + ((10678199534604909:ℝ)/800000000)*t) + (8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((-151857167521142229407:ℝ)/320000000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((-3884089887647404173:ℝ)/3200000000) - 3*((-151857167521142229407:ℝ)/320000000000))*t) + (((76225167229862243:ℝ)/16000000000) + ((9305049966455109:ℝ)/800000000)*t)*((111214274551:ℝ)/10000000000000) - (((581978479844851799:ℝ)/100000000000) + t * ((134836843187854117:ℝ)/10000000000)) = (((92506797823638443:ℝ)/16000000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((-151857167521142229407:ℝ)/320000000000) + ((76225167229862243:ℝ)/16000000000)*((111214274551:ℝ)/10000000000000) - ((581978479844851799:ℝ)/100000000000)) + t*(((10678199534604909:ℝ)/800000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((-3884089887647404173:ℝ)/3200000000) - 3*((-151857167521142229407:ℝ)/320000000000)) + ((9305049966455109:ℝ)/800000000)*((111214274551:ℝ)/10000000000000) - ((134836843187854117:ℝ)/10000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece14_e01 {q : ℝ} (h0 : ((41:ℝ)/10) ≤ q) (h1 : q ≤ ((21:ℝ)/5)) :
    |pieceW q pieceX_14 0 1 - (((-5353799221362511:ℝ)/5000000000) + (q - ((83:ℝ)/20)) * ((-172958207820686779:ℝ)/100000000000))| ≤ ((612999379887766889:ℝ)/100000000000000) := by
  set t := q - ((83:ℝ)/20) with htd
  have hq : q = ((83:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece14_L3 piece14_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((83:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_01 q = ∑ e ∈ Finset.range 8, ([((-81408152968881:ℝ)/80000000), ((-6865747840749:ℝ)/4000000), ((-248159560509:ℝ)/200000), ((-996624741:ℝ)/2000), ((-12007527:ℝ)/100), ((-434007:ℝ)/25), ((-6972:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_01; ring
  have h12 : centralNum12_01 q = ∑ e ∈ Finset.range 12, ([((-19606444007685559114323:ℝ)/12800000000000), ((-1476317903645795347653:ℝ)/320000000000), ((-40282966880534889837:ℝ)/6400000000), ((-821968433049559011:ℝ)/160000000), ((-22305923498201619:ℝ)/8000000), ((-1056877969989933:ℝ)/1000000), ((-28553885260257:ℝ)/100000), ((-27495940551:ℝ)/500), ((-739914579:ℝ)/100), ((-3312186:ℝ)/5), ((-177588:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_01; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-81408152968881:ℝ)/80000000), ((-6865747840749:ℝ)/4000000), ((-248159560509:ℝ)/200000), ((-996624741:ℝ)/2000), ((-12007527:ℝ)/100), ((-434007:ℝ)/25), ((-6972:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0) 6 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-19606444007685559114323:ℝ)/12800000000000), ((-1476317903645795347653:ℝ)/320000000000), ((-40282966880534889837:ℝ)/6400000000), ((-821968433049559011:ℝ)/160000000), ((-22305923498201619:ℝ)/8000000), ((-1056877969989933:ℝ)/1000000), ((-28553885260257:ℝ)/100000), ((-27495940551:ℝ)/500), ((-739914579:ℝ)/100), ((-3312186:ℝ)/5), ((-177588:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0) 10 ht
  have m12 := abs_poly_le (fun e => ([((-19606444007685559114323:ℝ)/12800000000000), ((-1476317903645795347653:ℝ)/320000000000), ((-40282966880534889837:ℝ)/6400000000), ((-821968433049559011:ℝ)/160000000), ((-22305923498201619:ℝ)/8000000), ((-1056877969989933:ℝ)/1000000), ((-28553885260257:ℝ)/100000), ((-27495940551:ℝ)/500), ((-739914579:ℝ)/100), ((-3312186:ℝ)/5), ((-177588:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0) 12 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 8, ([((-81408152968881:ℝ)/80000000), ((-6865747840749:ℝ)/4000000), ((-248159560509:ℝ)/200000), ((-996624741:ℝ)/2000), ((-12007527:ℝ)/100), ((-434007:ℝ)/25), ((-6972:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0 * t^e) - (((-81408152968881:ℝ)/80000000) + ((-6865747840749:ℝ)/4000000)*t)| ≤ ((126601578801:ℝ)/40000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 12, ([((-19606444007685559114323:ℝ)/12800000000000), ((-1476317903645795347653:ℝ)/320000000000), ((-40282966880534889837:ℝ)/6400000000), ((-821968433049559011:ℝ)/160000000), ((-22305923498201619:ℝ)/8000000), ((-1056877969989933:ℝ)/1000000), ((-28553885260257:ℝ)/100000), ((-27495940551:ℝ)/500), ((-739914579:ℝ)/100), ((-3312186:ℝ)/5), ((-177588:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e) - ((-19606444007685559114323:ℝ)/12800000000000) - ((-1476317903645795347653:ℝ)/320000000000)*t| ≤ ((209861863141437525027:ℝ)/12800000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 12, ([((-19606444007685559114323:ℝ)/12800000000000), ((-1476317903645795347653:ℝ)/320000000000), ((-40282966880534889837:ℝ)/6400000000), ((-821968433049559011:ℝ)/160000000), ((-22305923498201619:ℝ)/8000000), ((-1056877969989933:ℝ)/1000000), ((-28553885260257:ℝ)/100000), ((-27495940551:ℝ)/500), ((-739914579:ℝ)/100), ((-3312186:ℝ)/5), ((-177588:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((86856619560694074:ℝ)/48828125) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((76225167229862243:ℝ)/16000000000) - ((9305049966455109:ℝ)/800000000)*t| ≤ ((64765982479019:ℝ)/2000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-6288:ℝ), (81024:ℝ), (-238720:ℝ), (246784:ℝ), (-98304:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m13' : |centralNum13_01 q| ≤ ((60145729665494017104:ℝ)/48828125) := by
    rw [centralNum13_01_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-7368:ℝ), (59208:ℝ), (-155734:ℝ), (205300:ℝ), (-60000:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m23' : |centralNum23_01 q| ≤ ((1660767162834991554:ℝ)/1953125) := by
    rw [centralNum23_01_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece14_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece14_E11 h0) m23'
  have c5 := scaled_affine (X := ((-108101808163:ℝ)/100000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-81408152968881:ℝ)/80000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((-19606444007685559114323:ℝ)/12800000000000) + ((76225167229862243:ℝ)/16000000000)*((-108101808163:ℝ)/100000000000000) - ((-5353799221362511:ℝ)/5000000000)) (β := ((-6865747840749:ℝ)/4000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((-1476317903645795347653:ℝ)/320000000000) - 3*((-19606444007685559114323:ℝ)/12800000000000)) + ((9305049966455109:ℝ)/800000000)*((-108101808163:ℝ)/100000000000000) - ((-172958207820686779:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_14 0 1 = centralNum11_01 q + 8*(Real.exp (-(3*((83:ℝ)/20)))*Real.exp (-3*t))*centralNum12_01 q + 18*Real.exp (-8*q)*centralNum13_01 q + 72*Real.exp (-11*q)*centralNum23_01 q + 8*q^7*(2*q-3)^2*((-108101808163:ℝ)/100000000000000) + (0:ℝ) := by
    rw [pieceW_01, pieceX_14, sym4_01, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((7314799889329492593492776513366962198741008262051133112073325133370423:ℝ)/26061090199934412583311463711859009633870148453289446651970400000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-81408152968881:ℝ)/80000000) + ((-6865747840749:ℝ)/4000000)*t) + (8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((-19606444007685559114323:ℝ)/12800000000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((-1476317903645795347653:ℝ)/320000000000) - 3*((-19606444007685559114323:ℝ)/12800000000000))*t) + (((76225167229862243:ℝ)/16000000000) + ((9305049966455109:ℝ)/800000000)*t)*((-108101808163:ℝ)/100000000000000) - (((-5353799221362511:ℝ)/5000000000) + t * ((-172958207820686779:ℝ)/100000000000)) = (((-81408152968881:ℝ)/80000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((-19606444007685559114323:ℝ)/12800000000000) + ((76225167229862243:ℝ)/16000000000)*((-108101808163:ℝ)/100000000000000) - ((-5353799221362511:ℝ)/5000000000)) + t*(((-6865747840749:ℝ)/4000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((-1476317903645795347653:ℝ)/320000000000) - 3*((-19606444007685559114323:ℝ)/12800000000000)) + ((9305049966455109:ℝ)/800000000)*((-108101808163:ℝ)/100000000000000) - ((-172958207820686779:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece14_e02 {q : ℝ} (h0 : ((41:ℝ)/10) ≤ q) (h1 : q ≤ ((21:ℝ)/5)) :
    |pieceW q pieceX_14 0 2 - (((207765141230859569:ℝ)/25000000000000) + (q - ((83:ℝ)/20)) * ((-45208156226968049:ℝ)/1250000000000))| ≤ ((184949203468018519:ℝ)/100000000000000) := by
  set t := q - ((83:ℝ)/20) with htd
  have hq : q = ((83:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece14_L3 piece14_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((83:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_02 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_02; ring
  have h12 : centralNum12_02 q = ∑ e ∈ Finset.range 13, ([((-468898224062549201847621:ℝ)/2048000000000000), ((-312029773312364586536769:ℝ)/102400000000000), ((-39441106134257450673249:ℝ)/5120000000000), ((-491675955327606554127:ℝ)/51200000000), ((-147122220884619933:ℝ)/20000000), ((-1215386170214867037:ℝ)/320000000), ((-22103190530000433:ℝ)/16000000), ((-288322033426083:ℝ)/800000), ((-1077717099969:ℝ)/16000), ((-7064626833:ℝ)/800), ((-154602189:ℝ)/200), ((-406431:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_02; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-468898224062549201847621:ℝ)/2048000000000000), ((-312029773312364586536769:ℝ)/102400000000000), ((-39441106134257450673249:ℝ)/5120000000000), ((-491675955327606554127:ℝ)/51200000000), ((-147122220884619933:ℝ)/20000000), ((-1215386170214867037:ℝ)/320000000), ((-22103190530000433:ℝ)/16000000), ((-288322033426083:ℝ)/800000), ((-1077717099969:ℝ)/16000), ((-7064626833:ℝ)/800), ((-154602189:ℝ)/200), ((-406431:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((-468898224062549201847621:ℝ)/2048000000000000), ((-312029773312364586536769:ℝ)/102400000000000), ((-39441106134257450673249:ℝ)/5120000000000), ((-491675955327606554127:ℝ)/51200000000), ((-147122220884619933:ℝ)/20000000), ((-1215386170214867037:ℝ)/320000000), ((-22103190530000433:ℝ)/16000000), ((-288322033426083:ℝ)/800000), ((-1077717099969:ℝ)/16000), ((-7064626833:ℝ)/800), ((-154602189:ℝ)/200), ((-406431:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((-468898224062549201847621:ℝ)/2048000000000000), ((-312029773312364586536769:ℝ)/102400000000000), ((-39441106134257450673249:ℝ)/5120000000000), ((-491675955327606554127:ℝ)/51200000000), ((-147122220884619933:ℝ)/20000000), ((-1215386170214867037:ℝ)/320000000), ((-22103190530000433:ℝ)/16000000), ((-288322033426083:ℝ)/800000), ((-1077717099969:ℝ)/16000), ((-7064626833:ℝ)/800), ((-154602189:ℝ)/200), ((-406431:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e) - ((-468898224062549201847621:ℝ)/2048000000000000) - ((-312029773312364586536769:ℝ)/102400000000000)*t| ≤ ((20998059846525630215613:ℝ)/1024000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((-468898224062549201847621:ℝ)/2048000000000000), ((-312029773312364586536769:ℝ)/102400000000000), ((-39441106134257450673249:ℝ)/5120000000000), ((-491675955327606554127:ℝ)/51200000000), ((-147122220884619933:ℝ)/20000000), ((-1215386170214867037:ℝ)/320000000), ((-22103190530000433:ℝ)/16000000), ((-288322033426083:ℝ)/800000), ((-1077717099969:ℝ)/16000), ((-7064626833:ℝ)/800), ((-154602189:ℝ)/200), ((-406431:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((98100199349876052:ℝ)/244140625) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((76225167229862243:ℝ)/16000000000) - ((9305049966455109:ℝ)/800000000)*t| ≤ ((64765982479019:ℝ)/2000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82080:ℝ), (-967680:ℝ), (3257600:ℝ), (-4474880:ℝ), (2908160:ℝ), (-786432:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_02 q| ≤ ((13090952945632530743712:ℝ)/244140625) := by
    rw [centralNum13_02_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (87660:ℝ), (-702180:ℝ), ((7421435:ℝ)/4), ((-10854125:ℝ)/4), ((2828125:ℝ)/2), (-187500:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_02 q| ≤ ((16603600737787094241:ℝ)/781250) := by
    rw [centralNum23_02_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece14_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece14_E11 h0) m23'
  have c5 := scaled_affine (X := ((162533601993:ℝ)/50000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((-468898224062549201847621:ℝ)/2048000000000000) + ((76225167229862243:ℝ)/16000000000)*((162533601993:ℝ)/50000000000000) - ((207765141230859569:ℝ)/25000000000000)) (β := (0:ℝ) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((-312029773312364586536769:ℝ)/102400000000000) - 3*((-468898224062549201847621:ℝ)/2048000000000000)) + ((9305049966455109:ℝ)/800000000)*((162533601993:ℝ)/50000000000000) - ((-45208156226968049:ℝ)/1250000000000)) ht
  have hW : pieceW q pieceX_14 0 2 = centralNum11_02 q + 8*(Real.exp (-(3*((83:ℝ)/20)))*Real.exp (-3*t))*centralNum12_02 q + 18*Real.exp (-8*q)*centralNum13_02 q + 72*Real.exp (-11*q)*centralNum23_02 q + 8*q^7*(2*q-3)^2*((162533601993:ℝ)/50000000000000) + (0:ℝ) := by
    rw [pieceW_02, pieceX_14, sym4_02, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((78119436817818679129423375958329078116393029991288852245759554369147:ℝ)/13030545099967206291655731855929504816935074226644723325985200000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((-468898224062549201847621:ℝ)/2048000000000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((-312029773312364586536769:ℝ)/102400000000000) - 3*((-468898224062549201847621:ℝ)/2048000000000000))*t) + (((76225167229862243:ℝ)/16000000000) + ((9305049966455109:ℝ)/800000000)*t)*((162533601993:ℝ)/50000000000000) - (((207765141230859569:ℝ)/25000000000000) + t * ((-45208156226968049:ℝ)/1250000000000)) = ((0:ℝ) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((-468898224062549201847621:ℝ)/2048000000000000) + ((76225167229862243:ℝ)/16000000000)*((162533601993:ℝ)/50000000000000) - ((207765141230859569:ℝ)/25000000000000)) + t*((0:ℝ) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((-312029773312364586536769:ℝ)/102400000000000) - 3*((-468898224062549201847621:ℝ)/2048000000000000)) + ((9305049966455109:ℝ)/800000000)*((162533601993:ℝ)/50000000000000) - ((-45208156226968049:ℝ)/1250000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece14_e03 {q : ℝ} (h0 : ((41:ℝ)/10) ≤ q) (h1 : q ≤ ((21:ℝ)/5)) :
    |pieceW q pieceX_14 0 3 - (((-79509638909429079:ℝ)/2000000000000) + (q - ((83:ℝ)/20)) * ((-404858694398523533:ℝ)/1000000000000))| ≤ ((223719447480223761:ℝ)/25000000000000) := by
  set t := q - ((83:ℝ)/20) with htd
  have hq : q = ((83:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece14_L3 piece14_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((83:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_03 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_03; ring
  have h12 : centralNum12_03 q = ∑ e ∈ Finset.range 14, ([((2331898798461054414077950173:ℝ)/573440000000000000), ((88216901171911162396594827:ℝ)/7168000000000000), ((346934464362063610718769:ℝ)/22400000000000), ((353382792696928523888757:ℝ)/35840000000000), ((238660564487935793967:ℝ)/102400000000), ((-111471865124363258859:ℝ)/89600000000), ((-1562061273977515851:ℝ)/1120000000), ((-73404045453750759:ℝ)/112000000), ((-4338270286902009:ℝ)/22400000), ((-271916912331:ℝ)/7000), ((-37247871141:ℝ)/7000), ((-95911857:ℝ)/200), ((-3602961:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_03; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((2331898798461054414077950173:ℝ)/573440000000000000), ((88216901171911162396594827:ℝ)/7168000000000000), ((346934464362063610718769:ℝ)/22400000000000), ((353382792696928523888757:ℝ)/35840000000000), ((238660564487935793967:ℝ)/102400000000), ((-111471865124363258859:ℝ)/89600000000), ((-1562061273977515851:ℝ)/1120000000), ((-73404045453750759:ℝ)/112000000), ((-4338270286902009:ℝ)/22400000), ((-271916912331:ℝ)/7000), ((-37247871141:ℝ)/7000), ((-95911857:ℝ)/200), ((-3602961:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((2331898798461054414077950173:ℝ)/573440000000000000), ((88216901171911162396594827:ℝ)/7168000000000000), ((346934464362063610718769:ℝ)/22400000000000), ((353382792696928523888757:ℝ)/35840000000000), ((238660564487935793967:ℝ)/102400000000), ((-111471865124363258859:ℝ)/89600000000), ((-1562061273977515851:ℝ)/1120000000), ((-73404045453750759:ℝ)/112000000), ((-4338270286902009:ℝ)/22400000), ((-271916912331:ℝ)/7000), ((-37247871141:ℝ)/7000), ((-95911857:ℝ)/200), ((-3602961:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((2331898798461054414077950173:ℝ)/573440000000000000), ((88216901171911162396594827:ℝ)/7168000000000000), ((346934464362063610718769:ℝ)/22400000000000), ((353382792696928523888757:ℝ)/35840000000000), ((238660564487935793967:ℝ)/102400000000), ((-111471865124363258859:ℝ)/89600000000), ((-1562061273977515851:ℝ)/1120000000), ((-73404045453750759:ℝ)/112000000), ((-4338270286902009:ℝ)/22400000), ((-271916912331:ℝ)/7000), ((-37247871141:ℝ)/7000), ((-95911857:ℝ)/200), ((-3602961:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((2331898798461054414077950173:ℝ)/573440000000000000) - ((88216901171911162396594827:ℝ)/7168000000000000)*t| ≤ ((3274165737505957795776081:ℝ)/81920000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((2331898798461054414077950173:ℝ)/573440000000000000), ((88216901171911162396594827:ℝ)/7168000000000000), ((346934464362063610718769:ℝ)/22400000000000), ((353382792696928523888757:ℝ)/35840000000000), ((238660564487935793967:ℝ)/102400000000), ((-111471865124363258859:ℝ)/89600000000), ((-1562061273977515851:ℝ)/1120000000), ((-73404045453750759:ℝ)/112000000), ((-4338270286902009:ℝ)/22400000), ((-271916912331:ℝ)/7000), ((-37247871141:ℝ)/7000), ((-95911857:ℝ)/200), ((-3602961:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((42307586926738137003668157:ℝ)/8960000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((76225167229862243:ℝ)/16000000000) - ((9305049966455109:ℝ)/800000000)*t| ≤ ((64765982479019:ℝ)/2000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-812160:ℝ), (8985600:ℝ), (-32225280:ℝ), (52019200:ℝ), ((-305233920:ℝ)/7), ((135528448:ℝ)/7), ((-25165824:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_03 q| ≤ ((1774821396392342559660672:ℝ)/1220703125) := by
    rw [centralNum13_03_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-833220:ℝ), (6469740:ℝ), ((-68603955:ℝ)/4), ((104396875:ℝ)/4), ((-1001334375:ℝ)/56), ((125828125:ℝ)/28), ((-2343750:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_03 q| ≤ ((1119494076287735984787:ℝ)/3125000) := by
    rw [centralNum23_03_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece14_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece14_E11 h0) m23'
  have c5 := scaled_affine (X := ((-175486873537:ℝ)/5000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((2331898798461054414077950173:ℝ)/573440000000000000) + ((76225167229862243:ℝ)/16000000000)*((-175486873537:ℝ)/5000000000000) - ((-79509638909429079:ℝ)/2000000000000)) (β := (0:ℝ) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((88216901171911162396594827:ℝ)/7168000000000000) - 3*((2331898798461054414077950173:ℝ)/573440000000000000)) + ((9305049966455109:ℝ)/800000000)*((-175486873537:ℝ)/5000000000000) - ((-404858694398523533:ℝ)/1000000000000)) ht
  have hW : pieceW q pieceX_14 0 3 = centralNum11_03 q + 8*(Real.exp (-(3*((83:ℝ)/20)))*Real.exp (-3*t))*centralNum12_03 q + 18*Real.exp (-8*q)*centralNum13_03 q + 72*Real.exp (-11*q)*centralNum23_03 q + 8*q^7*(2*q-3)^2*((-175486873537:ℝ)/5000000000000) + (0:ℝ) := by
    rw [pieceW_03, pieceX_14, sym4_03, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((479466409025119290457534367451167256244434872436263937056306698683061:ℝ)/9121381569977044404159012299150653371854551958651306328189640000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((2331898798461054414077950173:ℝ)/573440000000000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((88216901171911162396594827:ℝ)/7168000000000000) - 3*((2331898798461054414077950173:ℝ)/573440000000000000))*t) + (((76225167229862243:ℝ)/16000000000) + ((9305049966455109:ℝ)/800000000)*t)*((-175486873537:ℝ)/5000000000000) - (((-79509638909429079:ℝ)/2000000000000) + t * ((-404858694398523533:ℝ)/1000000000000)) = ((0:ℝ) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((2331898798461054414077950173:ℝ)/573440000000000000) + ((76225167229862243:ℝ)/16000000000)*((-175486873537:ℝ)/5000000000000) - ((-79509638909429079:ℝ)/2000000000000)) + t*((0:ℝ) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((88216901171911162396594827:ℝ)/7168000000000000) - 3*((2331898798461054414077950173:ℝ)/573440000000000000)) + ((9305049966455109:ℝ)/800000000)*((-175486873537:ℝ)/5000000000000) - ((-404858694398523533:ℝ)/1000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece14_e11 {q : ℝ} (h0 : ((41:ℝ)/10) ≤ q) (h1 : q ≤ ((21:ℝ)/5)) :
    |pieceW q pieceX_14 1 1 - (((113272646959838049:ℝ)/25000000000) + (q - ((83:ℝ)/20)) * ((971614456034509961:ℝ)/100000000000))| ≤ ((66104277705211601:ℝ)/2500000000000) := by
  set t := q - ((83:ℝ)/20) with htd
  have hq : q = ((83:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece14_L3 piece14_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((83:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_11 q = ∑ e ∈ Finset.range 10, ([((26352374914661507:ℝ)/6000000000), ((3827806074282323:ℝ)/400000000), ((47140872290831:ℝ)/5000000), ((1378211941533:ℝ)/250000), ((26329420439:ℝ)/12500), ((680560741:ℝ)/1250), ((11874436:ℝ)/125), ((269072:ℝ)/25), ((3584:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_11; ring
  have h12 : centralNum12_11 q = ∑ e ∈ Finset.range 13, ([((1986544233289752062996459:ℝ)/1536000000000000), ((23048695651427759983397:ℝ)/25600000000000), ((-4236196637422350303883:ℝ)/1280000000000), ((-89276379339824443269:ℝ)/12800000000), ((-131356428616310089:ℝ)/20000000), ((-304636432479760559:ℝ)/80000000), ((-5981018375263771:ℝ)/4000000), ((-82480566684161:ℝ)/200000), ((-321851129243:ℝ)/4000), ((-6553085473:ℝ)/600), ((-49207023:ℝ)/50), ((-265194:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_11; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((26352374914661507:ℝ)/6000000000), ((3827806074282323:ℝ)/400000000), ((47140872290831:ℝ)/5000000), ((1378211941533:ℝ)/250000), ((26329420439:ℝ)/12500), ((680560741:ℝ)/1250), ((11874436:ℝ)/125), ((269072:ℝ)/25), ((3584:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((1986544233289752062996459:ℝ)/1536000000000000), ((23048695651427759983397:ℝ)/25600000000000), ((-4236196637422350303883:ℝ)/1280000000000), ((-89276379339824443269:ℝ)/12800000000), ((-131356428616310089:ℝ)/20000000), ((-304636432479760559:ℝ)/80000000), ((-5981018375263771:ℝ)/4000000), ((-82480566684161:ℝ)/200000), ((-321851129243:ℝ)/4000), ((-6553085473:ℝ)/600), ((-49207023:ℝ)/50), ((-265194:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((1986544233289752062996459:ℝ)/1536000000000000), ((23048695651427759983397:ℝ)/25600000000000), ((-4236196637422350303883:ℝ)/1280000000000), ((-89276379339824443269:ℝ)/12800000000), ((-131356428616310089:ℝ)/20000000), ((-304636432479760559:ℝ)/80000000), ((-5981018375263771:ℝ)/4000000), ((-82480566684161:ℝ)/200000), ((-321851129243:ℝ)/4000), ((-6553085473:ℝ)/600), ((-49207023:ℝ)/50), ((-265194:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((26352374914661507:ℝ)/6000000000), ((3827806074282323:ℝ)/400000000), ((47140872290831:ℝ)/5000000), ((1378211941533:ℝ)/250000), ((26329420439:ℝ)/12500), ((680560741:ℝ)/1250), ((11874436:ℝ)/125), ((269072:ℝ)/25), ((3584:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((26352374914661507:ℝ)/6000000000) + ((3827806074282323:ℝ)/400000000)*t)| ≤ ((582549083023867:ℝ)/24000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((1986544233289752062996459:ℝ)/1536000000000000), ((23048695651427759983397:ℝ)/25600000000000), ((-4236196637422350303883:ℝ)/1280000000000), ((-89276379339824443269:ℝ)/12800000000), ((-131356428616310089:ℝ)/20000000), ((-304636432479760559:ℝ)/80000000), ((-5981018375263771:ℝ)/4000000), ((-82480566684161:ℝ)/200000), ((-321851129243:ℝ)/4000), ((-6553085473:ℝ)/600), ((-49207023:ℝ)/50), ((-265194:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e) - ((1986544233289752062996459:ℝ)/1536000000000000) - ((23048695651427759983397:ℝ)/25600000000000)*t| ≤ ((7056325446274728519853:ℝ)/768000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((1986544233289752062996459:ℝ)/1536000000000000), ((23048695651427759983397:ℝ)/25600000000000), ((-4236196637422350303883:ℝ)/1280000000000), ((-89276379339824443269:ℝ)/12800000000), ((-131356428616310089:ℝ)/20000000), ((-304636432479760559:ℝ)/80000000), ((-5981018375263771:ℝ)/4000000), ((-82480566684161:ℝ)/200000), ((-321851129243:ℝ)/4000), ((-6553085473:ℝ)/600), ((-49207023:ℝ)/50), ((-265194:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((517450742784146199996589:ℝ)/384000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((76225167229862243:ℝ)/16000000000) - ((9305049966455109:ℝ)/800000000)*t| ≤ ((64765982479019:ℝ)/2000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-3444:ℝ), (162624:ℝ), (-1531216:ℝ), (4800960:ℝ), (-6350848:ℝ), ((12025856:ℝ)/3), (-1048576:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_11 q| ≤ ((17895853667957540703876:ℝ)/244140625) := by
    rw [centralNum13_11_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-4074:ℝ), (159906:ℝ), (-1104799:ℝ), (2801499:ℝ), (-3931375:ℝ), ((5896250:ℝ)/3), (-250000:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_11 q| ≤ ((57805629780084754239:ℝ)/1953125) := by
    rw [centralNum23_11_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece14_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece14_E11 h0) m23'
  have c5 := scaled_affine (X := ((103176780923:ℝ)/5000000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1))| ≤ ((290022314446501683200000000:ℝ)/172490841285844495920402488413) := by
    rw [abs_neg, tailWeight_1, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((21:ℝ)/5)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((21:ℝ)/5)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece14_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((4814744136400:ℝ)/531441)) ≤ ((21:ℝ)/5)^6*(8000*(2*((21:ℝ)/5)-3)^2*(1/((172490841285844495920402488413:ℝ)/25000000000))*((4814744136400:ℝ)/531441)) := by
          gcongr
      _ ≤ ((290022314446501683200000000:ℝ)/172490841285844495920402488413) := by norm_num
  have c7 := affine_round (α := ((26352374914661507:ℝ)/6000000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((1986544233289752062996459:ℝ)/1536000000000000) + ((76225167229862243:ℝ)/16000000000)*((103176780923:ℝ)/5000000000000) - ((113272646959838049:ℝ)/25000000000)) (β := ((3827806074282323:ℝ)/400000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((23048695651427759983397:ℝ)/25600000000000) - 3*((1986544233289752062996459:ℝ)/1536000000000000)) + ((9305049966455109:ℝ)/800000000)*((103176780923:ℝ)/5000000000000) - ((971614456034509961:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_14 1 1 = centralNum11_11 q + 8*(Real.exp (-(3*((83:ℝ)/20)))*Real.exp (-3*t))*centralNum12_11 q + 18*Real.exp (-8*q)*centralNum13_11 q + 72*Real.exp (-11*q)*centralNum23_11 q + 8*q^7*(2*q-3)^2*((103176780923:ℝ)/5000000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1)) := by
    rw [pieceW_11, pieceX_14, sym4_11, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((3822087298047328422692576032957838931296047112864336557347659377835149:ℝ)/3909163529990161887496719556778851445080522267993416997795560000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((26352374914661507:ℝ)/6000000000) + ((3827806074282323:ℝ)/400000000)*t) + (8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((1986544233289752062996459:ℝ)/1536000000000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((23048695651427759983397:ℝ)/25600000000000) - 3*((1986544233289752062996459:ℝ)/1536000000000000))*t) + (((76225167229862243:ℝ)/16000000000) + ((9305049966455109:ℝ)/800000000)*t)*((103176780923:ℝ)/5000000000000) - (((113272646959838049:ℝ)/25000000000) + t * ((971614456034509961:ℝ)/100000000000)) = (((26352374914661507:ℝ)/6000000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((1986544233289752062996459:ℝ)/1536000000000000) + ((76225167229862243:ℝ)/16000000000)*((103176780923:ℝ)/5000000000000) - ((113272646959838049:ℝ)/25000000000)) + t*(((3827806074282323:ℝ)/400000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((23048695651427759983397:ℝ)/25600000000000) - 3*((1986544233289752062996459:ℝ)/1536000000000000)) + ((9305049966455109:ℝ)/800000000)*((103176780923:ℝ)/5000000000000) - ((971614456034509961:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece14_e12 {q : ℝ} (h0 : ((41:ℝ)/10) ≤ q) (h1 : q ≤ ((21:ℝ)/5)) :
    |pieceW q pieceX_14 1 2 - (((-485731117039720241:ℝ)/1000000000000) + (q - ((83:ℝ)/20)) * ((-10820430413015879:ℝ)/10000000000))| ≤ ((13146875289862143:ℝ)/625000000000) := by
  set t := q - ((83:ℝ)/20) with htd
  have hq : q = ((83:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece14_L3 piece14_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((83:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_12 q = ∑ e ∈ Finset.range 9, ([((-1160965265833319:ℝ)/1920000000), ((-22125591291731:ℝ)/24000000), ((-632951627177:ℝ)/1200000), ((-6735079073:ℝ)/60000), ((18483187:ℝ)/1200), ((2055163:ℝ)/150), ((46406:ℝ)/15), ((968:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_12; ring
  have h12 : centralNum12_12 q = ∑ e ∈ Finset.range 14, ([((2013730323324927201677614493:ℝ)/245760000000000000), ((92811606799709754393005147:ℝ)/3072000000000000), ((55776118438481247339283:ℝ)/1200000000000), ((604887984798944973766357:ℝ)/15360000000000), ((6009656791925167071049:ℝ)/307200000000), ((190635854803078788181:ℝ)/38400000000), ((-110072449793067611:ℝ)/480000000), ((-33808106701721479:ℝ)/48000000), ((-2801833460887609:ℝ)/9600000), ((-68956101467:ℝ)/1000), ((-10460802927:ℝ)/1000), ((-202665213:ℝ)/200), ((-1149147:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_12; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-1160965265833319:ℝ)/1920000000), ((-22125591291731:ℝ)/24000000), ((-632951627177:ℝ)/1200000), ((-6735079073:ℝ)/60000), ((18483187:ℝ)/1200), ((2055163:ℝ)/150), ((46406:ℝ)/15), ((968:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((2013730323324927201677614493:ℝ)/245760000000000000), ((92811606799709754393005147:ℝ)/3072000000000000), ((55776118438481247339283:ℝ)/1200000000000), ((604887984798944973766357:ℝ)/15360000000000), ((6009656791925167071049:ℝ)/307200000000), ((190635854803078788181:ℝ)/38400000000), ((-110072449793067611:ℝ)/480000000), ((-33808106701721479:ℝ)/48000000), ((-2801833460887609:ℝ)/9600000), ((-68956101467:ℝ)/1000), ((-10460802927:ℝ)/1000), ((-202665213:ℝ)/200), ((-1149147:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((2013730323324927201677614493:ℝ)/245760000000000000), ((92811606799709754393005147:ℝ)/3072000000000000), ((55776118438481247339283:ℝ)/1200000000000), ((604887984798944973766357:ℝ)/15360000000000), ((6009656791925167071049:ℝ)/307200000000), ((190635854803078788181:ℝ)/38400000000), ((-110072449793067611:ℝ)/480000000), ((-33808106701721479:ℝ)/48000000), ((-2801833460887609:ℝ)/9600000), ((-68956101467:ℝ)/1000), ((-10460802927:ℝ)/1000), ((-202665213:ℝ)/200), ((-1149147:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((-1160965265833319:ℝ)/1920000000), ((-22125591291731:ℝ)/24000000), ((-632951627177:ℝ)/1200000), ((-6735079073:ℝ)/60000), ((18483187:ℝ)/1200), ((2055163:ℝ)/150), ((46406:ℝ)/15), ((968:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((-1160965265833319:ℝ)/1920000000) + ((-22125591291731:ℝ)/24000000)*t)| ≤ ((852979990273:ℝ)/640000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((2013730323324927201677614493:ℝ)/245760000000000000), ((92811606799709754393005147:ℝ)/3072000000000000), ((55776118438481247339283:ℝ)/1200000000000), ((604887984798944973766357:ℝ)/15360000000000), ((6009656791925167071049:ℝ)/307200000000), ((190635854803078788181:ℝ)/38400000000), ((-110072449793067611:ℝ)/480000000), ((-33808106701721479:ℝ)/48000000), ((-2801833460887609:ℝ)/9600000), ((-68956101467:ℝ)/1000), ((-10460802927:ℝ)/1000), ((-202665213:ℝ)/200), ((-1149147:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e) - ((2013730323324927201677614493:ℝ)/245760000000000000) - ((92811606799709754393005147:ℝ)/3072000000000000)*t| ≤ ((29797579184416730397909131:ℝ)/245760000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((2013730323324927201677614493:ℝ)/245760000000000000), ((92811606799709754393005147:ℝ)/3072000000000000), ((55776118438481247339283:ℝ)/1200000000000), ((604887984798944973766357:ℝ)/15360000000000), ((6009656791925167071049:ℝ)/307200000000), ((190635854803078788181:ℝ)/38400000000), ((-110072449793067611:ℝ)/480000000), ((-33808106701721479:ℝ)/48000000), ((-2801833460887609:ℝ)/9600000), ((-68956101467:ℝ)/1000), ((-10460802927:ℝ)/1000), ((-202665213:ℝ)/200), ((-1149147:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((201231194142348579137295351:ℝ)/20480000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((76225167229862243:ℝ)/16000000000) - ((9305049966455109:ℝ)/800000000)*t| ≤ ((64765982479019:ℝ)/2000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (122790:ℝ), (-3586680:ℝ), (28529720:ℝ), (-90761600:ℝ), (137804800:ℝ), ((-332136448:ℝ)/3), ((141819904:ℝ)/3), (-8388608:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_12 q| ≤ ((4339830007934800337164878:ℝ)/1220703125) := by
    rw [centralNum13_12_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (132555:ℝ), (-3252375:ℝ), ((39743695:ℝ)/2), ((-197111615:ℝ)/4), ((281947375:ℝ)/4), ((-1100234375:ℝ)/24), ((131828125:ℝ)/12), (-781250:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_12 q| ≤ ((2816098381171510842771:ℝ)/3125000) := by
    rw [centralNum23_12_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece14_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece14_E11 h0) m23'
  have c5 := scaled_affine (X := ((-14470057141:ℝ)/500000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-1160965265833319:ℝ)/1920000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((2013730323324927201677614493:ℝ)/245760000000000000) + ((76225167229862243:ℝ)/16000000000)*((-14470057141:ℝ)/500000000000) - ((-485731117039720241:ℝ)/1000000000000)) (β := ((-22125591291731:ℝ)/24000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((92811606799709754393005147:ℝ)/3072000000000000) - 3*((2013730323324927201677614493:ℝ)/245760000000000000)) + ((9305049966455109:ℝ)/800000000)*((-14470057141:ℝ)/500000000000) - ((-10820430413015879:ℝ)/10000000000)) ht
  have hW : pieceW q pieceX_14 1 2 = centralNum11_12 q + 8*(Real.exp (-(3*((83:ℝ)/20)))*Real.exp (-3*t))*centralNum12_12 q + 18*Real.exp (-8*q)*centralNum13_12 q + 72*Real.exp (-11*q)*centralNum23_12 q + 8*q^7*(2*q-3)^2*((-14470057141:ℝ)/500000000000) + (0:ℝ) := by
    rw [pieceW_12, pieceX_14, sym4_12, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((56596938500500573504519283582425124778163445751142472403591784217519:ℝ)/97729088249754047187417988919471286127013056699835424944889000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-1160965265833319:ℝ)/1920000000) + ((-22125591291731:ℝ)/24000000)*t) + (8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((2013730323324927201677614493:ℝ)/245760000000000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((92811606799709754393005147:ℝ)/3072000000000000) - 3*((2013730323324927201677614493:ℝ)/245760000000000000))*t) + (((76225167229862243:ℝ)/16000000000) + ((9305049966455109:ℝ)/800000000)*t)*((-14470057141:ℝ)/500000000000) - (((-485731117039720241:ℝ)/1000000000000) + t * ((-10820430413015879:ℝ)/10000000000)) = (((-1160965265833319:ℝ)/1920000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((2013730323324927201677614493:ℝ)/245760000000000000) + ((76225167229862243:ℝ)/16000000000)*((-14470057141:ℝ)/500000000000) - ((-485731117039720241:ℝ)/1000000000000)) + t*(((-22125591291731:ℝ)/24000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((92811606799709754393005147:ℝ)/3072000000000000) - 3*((2013730323324927201677614493:ℝ)/245760000000000000)) + ((9305049966455109:ℝ)/800000000)*((-14470057141:ℝ)/500000000000) - ((-10820430413015879:ℝ)/10000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece14_e13 {q : ℝ} (h0 : ((41:ℝ)/10) ≤ q) (h1 : q ≤ ((21:ℝ)/5)) :
    |pieceW q pieceX_14 1 3 - (((25752124246234523:ℝ)/40000000000) + (q - ((83:ℝ)/20)) * ((177745988348358287:ℝ)/50000000000))| ≤ ((473333999364526031:ℝ)/10000000000000) := by
  set t := q - ((83:ℝ)/20) with htd
  have hq : q = ((83:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece14_L3 piece14_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((83:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_13 q = ∑ e ∈ Finset.range 7, ([((-980821120107:ℝ)/3200000), ((-35451365787:ℝ)/80000), ((-427124889:ℝ)/1600), ((-1715361:ℝ)/20), ((-62001:ℝ)/4), (-1494:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_13; ring
  have h12 : centralNum12_13 q = ∑ e ∈ Finset.range 15, ([((-394860247108756528752888798903:ℝ)/22937600000000000000), ((-6575925214963179022015025067:ℝ)/163840000000000000), ((-404162653024778919974814963:ℝ)/14336000000000000), ((14077245189587446592304297:ℝ)/1433600000000000), ((4442011552101872770094247:ℝ)/143360000000000), ((180369316230100095101433:ℝ)/7168000000000), ((2055383682795085991667:ℝ)/179200000000), ((14182407188007822843:ℝ)/4480000000), ((57885826470500913:ℝ)/128000000), ((-627395581495467:ℝ)/44800000), ((-5922566702559:ℝ)/280000), ((-261224961903:ℝ)/56000), ((-3032266023:ℝ)/5600), ((-9594369:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_13; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-980821120107:ℝ)/3200000), ((-35451365787:ℝ)/80000), ((-427124889:ℝ)/1600), ((-1715361:ℝ)/20), ((-62001:ℝ)/4), (-1494:ℝ), (-60:ℝ)] : List ℝ).getD e 0) 5 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-394860247108756528752888798903:ℝ)/22937600000000000000), ((-6575925214963179022015025067:ℝ)/163840000000000000), ((-404162653024778919974814963:ℝ)/14336000000000000), ((14077245189587446592304297:ℝ)/1433600000000000), ((4442011552101872770094247:ℝ)/143360000000000), ((180369316230100095101433:ℝ)/7168000000000), ((2055383682795085991667:ℝ)/179200000000), ((14182407188007822843:ℝ)/4480000000), ((57885826470500913:ℝ)/128000000), ((-627395581495467:ℝ)/44800000), ((-5922566702559:ℝ)/280000), ((-261224961903:ℝ)/56000), ((-3032266023:ℝ)/5600), ((-9594369:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-394860247108756528752888798903:ℝ)/22937600000000000000), ((-6575925214963179022015025067:ℝ)/163840000000000000), ((-404162653024778919974814963:ℝ)/14336000000000000), ((14077245189587446592304297:ℝ)/1433600000000000), ((4442011552101872770094247:ℝ)/143360000000000), ((180369316230100095101433:ℝ)/7168000000000), ((2055383682795085991667:ℝ)/179200000000), ((14182407188007822843:ℝ)/4480000000), ((57885826470500913:ℝ)/128000000), ((-627395581495467:ℝ)/44800000), ((-5922566702559:ℝ)/280000), ((-261224961903:ℝ)/56000), ((-3032266023:ℝ)/5600), ((-9594369:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 7, ([((-980821120107:ℝ)/3200000), ((-35451365787:ℝ)/80000), ((-427124889:ℝ)/1600), ((-1715361:ℝ)/20), ((-62001:ℝ)/4), (-1494:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e) - (((-980821120107:ℝ)/3200000) + ((-35451365787:ℝ)/80000)*t)| ≤ ((2170243167:ℝ)/3200000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-394860247108756528752888798903:ℝ)/22937600000000000000), ((-6575925214963179022015025067:ℝ)/163840000000000000), ((-404162653024778919974814963:ℝ)/14336000000000000), ((14077245189587446592304297:ℝ)/1433600000000000), ((4442011552101872770094247:ℝ)/143360000000000), ((180369316230100095101433:ℝ)/7168000000000), ((2055383682795085991667:ℝ)/179200000000), ((14182407188007822843:ℝ)/4480000000), ((57885826470500913:ℝ)/128000000), ((-627395581495467:ℝ)/44800000), ((-5922566702559:ℝ)/280000), ((-261224961903:ℝ)/56000), ((-3032266023:ℝ)/5600), ((-9594369:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((-394860247108756528752888798903:ℝ)/22937600000000000000) - ((-6575925214963179022015025067:ℝ)/163840000000000000)*t| ≤ ((824715825624746487526379241:ℝ)/11468800000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-394860247108756528752888798903:ℝ)/22937600000000000000), ((-6575925214963179022015025067:ℝ)/163840000000000000), ((-404162653024778919974814963:ℝ)/14336000000000000), ((14077245189587446592304297:ℝ)/1433600000000000), ((4442011552101872770094247:ℝ)/143360000000000), ((180369316230100095101433:ℝ)/7168000000000), ((2055383682795085991667:ℝ)/179200000000), ((14182407188007822843:ℝ)/4480000000), ((57885826470500913:ℝ)/128000000), ((-627395581495467:ℝ)/44800000), ((-5922566702559:ℝ)/280000), ((-261224961903:ℝ)/56000), ((-3032266023:ℝ)/5600), ((-9594369:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((31610082518910591063003338061:ℝ)/1638400000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((76225167229862243:ℝ)/16000000000) - ((9305049966455109:ℝ)/800000000)*t| ≤ ((64765982479019:ℝ)/2000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2325540:ℝ), (52589280:ℝ), (-375655200:ℝ), (1192958720:ℝ), (-1965096960:ℝ), ((12857851904:ℝ)/7), ((-21171273728:ℝ)/21), ((914358272:ℝ)/3), ((-268435456:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_13 q| ≤ ((649300106742842122597753668:ℝ)/6103515625) := by
    rw [centralNum13_13_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2399070:ℝ), (45666930:ℝ), (-251781675:ℝ), ((2452738385:ℝ)/4), ((-14104310625:ℝ)/16), ((74345740625:ℝ)/112), ((-74899765625:ℝ)/336), ((5161328125:ℝ)/168), ((-9765625:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_13 q| ≤ ((111799197178329957573123:ℝ)/6250000) := by
    rw [centralNum23_13_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece14_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece14_E11 h0) m23'
  have c5 := scaled_affine (X := ((39090608763:ℝ)/125000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-980821120107:ℝ)/3200000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((-394860247108756528752888798903:ℝ)/22937600000000000000) + ((76225167229862243:ℝ)/16000000000)*((39090608763:ℝ)/125000000000) - ((25752124246234523:ℝ)/40000000000)) (β := ((-35451365787:ℝ)/80000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((-6575925214963179022015025067:ℝ)/163840000000000000) - 3*((-394860247108756528752888798903:ℝ)/22937600000000000000)) + ((9305049966455109:ℝ)/800000000)*((39090608763:ℝ)/125000000000) - ((177745988348358287:ℝ)/50000000000)) ht
  have hW : pieceW q pieceX_14 1 3 = centralNum11_13 q + 8*(Real.exp (-(3*((83:ℝ)/20)))*Real.exp (-3*t))*centralNum12_13 q + 18*Real.exp (-8*q)*centralNum13_13 q + 72*Real.exp (-11*q)*centralNum23_13 q + 8*q^7*(2*q-3)^2*((39090608763:ℝ)/125000000000) + (0:ℝ) := by
    rw [pieceW_13, pieceX_14, sym4_13, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((17184325069339987827359744235609081635023289009464932126531385098227:ℝ)/57008634812356527525993826869691583574090949741570664551185250000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-980821120107:ℝ)/3200000) + ((-35451365787:ℝ)/80000)*t) + (8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((-394860247108756528752888798903:ℝ)/22937600000000000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((-6575925214963179022015025067:ℝ)/163840000000000000) - 3*((-394860247108756528752888798903:ℝ)/22937600000000000000))*t) + (((76225167229862243:ℝ)/16000000000) + ((9305049966455109:ℝ)/800000000)*t)*((39090608763:ℝ)/125000000000) - (((25752124246234523:ℝ)/40000000000) + t * ((177745988348358287:ℝ)/50000000000)) = (((-980821120107:ℝ)/3200000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((-394860247108756528752888798903:ℝ)/22937600000000000000) + ((76225167229862243:ℝ)/16000000000)*((39090608763:ℝ)/125000000000) - ((25752124246234523:ℝ)/40000000000)) + t*(((-35451365787:ℝ)/80000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((-6575925214963179022015025067:ℝ)/163840000000000000) - 3*((-394860247108756528752888798903:ℝ)/22937600000000000000)) + ((9305049966455109:ℝ)/800000000)*((39090608763:ℝ)/125000000000) - ((177745988348358287:ℝ)/50000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece14_e22 {q : ℝ} (h0 : ((41:ℝ)/10) ≤ q) (h1 : q ≤ ((21:ℝ)/5)) :
    |pieceW q pieceX_14 2 2 - (((307642783852511279:ℝ)/100000000000) + (q - ((83:ℝ)/20)) * ((12801954321983373:ℝ)/1250000000))| ≤ ((52485629278576793:ℝ)/500000000000) := by
  set t := q - ((83:ℝ)/20) with htd
  have hq : q = ((83:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece14_L3 piece14_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((83:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_22 q = ∑ e ∈ Finset.range 10, ([((71751007915510693:ℝ)/19200000000), ((2776351785864603:ℝ)/320000000), ((107398923174313:ℝ)/12000000), ((3252541535279:ℝ)/600000), ((42715459553:ℝ)/20000), ((1708695563:ℝ)/3000), ((7721597:ℝ)/75), ((60788:ℝ)/5), ((2548:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_22; ring
  have h12 : centralNum12_22 q = ∑ e ∈ Finset.range 15, ([((-1414679523427461509415665651989:ℝ)/39321600000000000000), ((-61840108489127655485997968029:ℝ)/655360000000000000), ((-2208270154226279710457465629:ℝ)/24576000000000000), ((-49929746714475038107611229:ℝ)/2457600000000000), ((2726039201135272012251847:ℝ)/81920000000000), ((457239750620583213264779:ℝ)/12288000000000), ((5917956575909999200841:ℝ)/307200000000), ((15072066224420849523:ℝ)/2560000000), ((1537912921012678613:ℝ)/1536000000), ((2437197859033199:ℝ)/76800000), ((-4454148955389:ℝ)/160000), ((-231244787223:ℝ)/32000), ((-2854947303:ℝ)/3200), ((-9361089:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_22; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((71751007915510693:ℝ)/19200000000), ((2776351785864603:ℝ)/320000000), ((107398923174313:ℝ)/12000000), ((3252541535279:ℝ)/600000), ((42715459553:ℝ)/20000), ((1708695563:ℝ)/3000), ((7721597:ℝ)/75), ((60788:ℝ)/5), ((2548:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-1414679523427461509415665651989:ℝ)/39321600000000000000), ((-61840108489127655485997968029:ℝ)/655360000000000000), ((-2208270154226279710457465629:ℝ)/24576000000000000), ((-49929746714475038107611229:ℝ)/2457600000000000), ((2726039201135272012251847:ℝ)/81920000000000), ((457239750620583213264779:ℝ)/12288000000000), ((5917956575909999200841:ℝ)/307200000000), ((15072066224420849523:ℝ)/2560000000), ((1537912921012678613:ℝ)/1536000000), ((2437197859033199:ℝ)/76800000), ((-4454148955389:ℝ)/160000), ((-231244787223:ℝ)/32000), ((-2854947303:ℝ)/3200), ((-9361089:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-1414679523427461509415665651989:ℝ)/39321600000000000000), ((-61840108489127655485997968029:ℝ)/655360000000000000), ((-2208270154226279710457465629:ℝ)/24576000000000000), ((-49929746714475038107611229:ℝ)/2457600000000000), ((2726039201135272012251847:ℝ)/81920000000000), ((457239750620583213264779:ℝ)/12288000000000), ((5917956575909999200841:ℝ)/307200000000), ((15072066224420849523:ℝ)/2560000000), ((1537912921012678613:ℝ)/1536000000), ((2437197859033199:ℝ)/76800000), ((-4454148955389:ℝ)/160000), ((-231244787223:ℝ)/32000), ((-2854947303:ℝ)/3200), ((-9361089:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((71751007915510693:ℝ)/19200000000), ((2776351785864603:ℝ)/320000000), ((107398923174313:ℝ)/12000000), ((3252541535279:ℝ)/600000), ((42715459553:ℝ)/20000), ((1708695563:ℝ)/3000), ((7721597:ℝ)/75), ((60788:ℝ)/5), ((2548:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((71751007915510693:ℝ)/19200000000) + ((2776351785864603:ℝ)/320000000)*t)| ≤ ((221432800028101:ℝ)/9600000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-1414679523427461509415665651989:ℝ)/39321600000000000000), ((-61840108489127655485997968029:ℝ)/655360000000000000), ((-2208270154226279710457465629:ℝ)/24576000000000000), ((-49929746714475038107611229:ℝ)/2457600000000000), ((2726039201135272012251847:ℝ)/81920000000000), ((457239750620583213264779:ℝ)/12288000000000), ((5917956575909999200841:ℝ)/307200000000), ((15072066224420849523:ℝ)/2560000000), ((1537912921012678613:ℝ)/1536000000), ((2437197859033199:ℝ)/76800000), ((-4454148955389:ℝ)/160000), ((-231244787223:ℝ)/32000), ((-2854947303:ℝ)/3200), ((-9361089:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e) - ((-1414679523427461509415665651989:ℝ)/39321600000000000000) - ((-61840108489127655485997968029:ℝ)/655360000000000000)*t| ≤ ((223539687150162506121300757:ℝ)/983040000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-1414679523427461509415665651989:ℝ)/39321600000000000000), ((-61840108489127655485997968029:ℝ)/655360000000000000), ((-2208270154226279710457465629:ℝ)/24576000000000000), ((-49929746714475038107611229:ℝ)/2457600000000000), ((2726039201135272012251847:ℝ)/81920000000000), ((457239750620583213264779:ℝ)/12288000000000), ((5917956575909999200841:ℝ)/307200000000), ((15072066224420849523:ℝ)/2560000000), ((1537912921012678613:ℝ)/1536000000), ((2437197859033199:ℝ)/76800000), ((-4454148955389:ℝ)/160000), ((-231244787223:ℝ)/32000), ((-2854947303:ℝ)/3200), ((-9361089:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e)| ≤ ((402285359095212744029627896589:ℝ)/9830400000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((76225167229862243:ℝ)/16000000000) - ((9305049966455109:ℝ)/800000000)*t| ≤ ((64765982479019:ℝ)/2000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82125:ℝ), (-6663750:ℝ), (115666200:ℝ), (-750437000:ℝ), (2277262000:ℝ), (-3656824320:ℝ), (3359621120:ℝ), (-1817706496:ℝ), ((1625292800:ℝ)/3), (-67108864:ℝ)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_22 q| ≤ ((1161736766144808267475951659:ℝ)/6103515625) := by
    rw [centralNum13_22_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((178425:ℝ)/2), ((-13176075:ℝ)/2), ((777815145:ℝ)/8), ((-3968389015:ℝ)/8), ((9393350195:ℝ)/8), ((-26366634375:ℝ)/16), ((77851609375:ℝ)/64), ((-25714921875:ℝ)/64), ((5236328125:ℝ)/96), ((-9765625:ℝ)/4)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_22 q| ≤ ((202341076390664468086473:ℝ)/6250000) := by
    rw [centralNum23_22_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece14_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece14_E11 h0) m23'
  have c5 := scaled_affine (X := ((98022118669:ℝ)/1000000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2))| ≤ ((154833218460312417536000000000:ℝ)/1552417571572600463283622395717) := by
    rw [abs_neg, tailWeight_2, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((21:ℝ)/5)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((21:ℝ)/5)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece14_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((2570430941234500:ℝ)/4782969)) ≤ ((21:ℝ)/5)^6*(8000*(2*((21:ℝ)/5)-3)^2*(1/((172490841285844495920402488413:ℝ)/25000000000))*((2570430941234500:ℝ)/4782969)) := by
          gcongr
      _ ≤ ((154833218460312417536000000000:ℝ)/1552417571572600463283622395717) := by norm_num
  have c7 := affine_round (α := ((71751007915510693:ℝ)/19200000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((-1414679523427461509415665651989:ℝ)/39321600000000000000) + ((76225167229862243:ℝ)/16000000000)*((98022118669:ℝ)/1000000000000) - ((307642783852511279:ℝ)/100000000000)) (β := ((2776351785864603:ℝ)/320000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((-61840108489127655485997968029:ℝ)/655360000000000000) - 3*((-1414679523427461509415665651989:ℝ)/39321600000000000000)) + ((9305049966455109:ℝ)/800000000)*((98022118669:ℝ)/1000000000000) - ((12801954321983373:ℝ)/1250000000)) ht
  have hW : pieceW q pieceX_14 2 2 = centralNum11_22 q + 8*(Real.exp (-(3*((83:ℝ)/20)))*Real.exp (-3*t))*centralNum12_22 q + 18*Real.exp (-8*q)*centralNum13_22 q + 72*Real.exp (-11*q)*centralNum23_22 q + 8*q^7*(2*q-3)^2*((98022118669:ℝ)/1000000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2)) := by
    rw [pieceW_22, pieceX_14, sym4_22, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((535281793546268448983544510673662828489243408018156739547671912512853:ℝ)/781832705998032377499343911355770289016104453598683399559112000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((71751007915510693:ℝ)/19200000000) + ((2776351785864603:ℝ)/320000000)*t) + (8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((-1414679523427461509415665651989:ℝ)/39321600000000000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((-61840108489127655485997968029:ℝ)/655360000000000000) - 3*((-1414679523427461509415665651989:ℝ)/39321600000000000000))*t) + (((76225167229862243:ℝ)/16000000000) + ((9305049966455109:ℝ)/800000000)*t)*((98022118669:ℝ)/1000000000000) - (((307642783852511279:ℝ)/100000000000) + t * ((12801954321983373:ℝ)/1250000000)) = (((71751007915510693:ℝ)/19200000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((-1414679523427461509415665651989:ℝ)/39321600000000000000) + ((76225167229862243:ℝ)/16000000000)*((98022118669:ℝ)/1000000000000) - ((307642783852511279:ℝ)/100000000000)) + t*(((2776351785864603:ℝ)/320000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((-61840108489127655485997968029:ℝ)/655360000000000000) - 3*((-1414679523427461509415665651989:ℝ)/39321600000000000000)) + ((9305049966455109:ℝ)/800000000)*((98022118669:ℝ)/1000000000000) - ((12801954321983373:ℝ)/1250000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece14_e23 {q : ℝ} (h0 : ((41:ℝ)/10) ≤ q) (h1 : q ≤ ((21:ℝ)/5)) :
    |pieceW q pieceX_14 2 3 - (((-113883399459166089:ℝ)/50000000000) + (q - ((83:ℝ)/20)) * ((-62048837984003871:ℝ)/5000000000))| ≤ ((360526448407087881:ℝ)/500000000000) := by
  set t := q - ((83:ℝ)/20) with htd
  have hq : q = ((83:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece14_L3 piece14_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((83:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_23 q = ∑ e ∈ Finset.range 9, ([((310360951302613:ℝ)/320000000), ((57076271792181:ℝ)/32000000), ((2496439767397:ℝ)/1600000), ((68045387933:ℝ)/80000), ((248317989:ℝ)/800), ((15113767:ℝ)/200), ((117047:ℝ)/10), (1038:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_23; ring
  have h12 : centralNum12_23 q = ∑ e ∈ Finset.range 16, ([((143880510456474753905707950620719:ℝ)/3670016000000000000000), ((246766159847543678727959087391:ℝ)/18350080000000000000), ((-59404055923016929125509340097:ℝ)/367001600000000000), ((-13980906714480306207370237163:ℝ)/45875200000000000), ((-1207403421772965915578412537:ℝ)/4587520000000000), ((-73329777467722538265429593:ℝ)/573440000000000), ((-370034413662285610705057:ℝ)/11468800000000), ((-1388759572907480919:ℝ)/11468800000), ((83799149936068289881:ℝ)/28672000000), ((761349979261005261:ℝ)/716800000), ((66332277693276453:ℝ)/358400000), ((22179228388479:ℝ)/1792000), ((-49452995367:ℝ)/35840), ((-1676862567:ℝ)/4480), ((-14453883:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_23; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((310360951302613:ℝ)/320000000), ((57076271792181:ℝ)/32000000), ((2496439767397:ℝ)/1600000), ((68045387933:ℝ)/80000), ((248317989:ℝ)/800), ((15113767:ℝ)/200), ((117047:ℝ)/10), (1038:ℝ), (40:ℝ)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((143880510456474753905707950620719:ℝ)/3670016000000000000000), ((246766159847543678727959087391:ℝ)/18350080000000000000), ((-59404055923016929125509340097:ℝ)/367001600000000000), ((-13980906714480306207370237163:ℝ)/45875200000000000), ((-1207403421772965915578412537:ℝ)/4587520000000000), ((-73329777467722538265429593:ℝ)/573440000000000), ((-370034413662285610705057:ℝ)/11468800000000), ((-1388759572907480919:ℝ)/11468800000), ((83799149936068289881:ℝ)/28672000000), ((761349979261005261:ℝ)/716800000), ((66332277693276453:ℝ)/358400000), ((22179228388479:ℝ)/1792000), ((-49452995367:ℝ)/35840), ((-1676862567:ℝ)/4480), ((-14453883:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 14 ht
  have m12 := abs_poly_le (fun e => ([((143880510456474753905707950620719:ℝ)/3670016000000000000000), ((246766159847543678727959087391:ℝ)/18350080000000000000), ((-59404055923016929125509340097:ℝ)/367001600000000000), ((-13980906714480306207370237163:ℝ)/45875200000000000), ((-1207403421772965915578412537:ℝ)/4587520000000000), ((-73329777467722538265429593:ℝ)/573440000000000), ((-370034413662285610705057:ℝ)/11468800000000), ((-1388759572907480919:ℝ)/11468800000), ((83799149936068289881:ℝ)/28672000000), ((761349979261005261:ℝ)/716800000), ((66332277693276453:ℝ)/358400000), ((22179228388479:ℝ)/1792000), ((-49452995367:ℝ)/35840), ((-1676862567:ℝ)/4480), ((-14453883:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 16 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((310360951302613:ℝ)/320000000), ((57076271792181:ℝ)/32000000), ((2496439767397:ℝ)/1600000), ((68045387933:ℝ)/80000), ((248317989:ℝ)/800), ((15113767:ℝ)/200), ((117047:ℝ)/10), (1038:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e) - (((310360951302613:ℝ)/320000000) + ((57076271792181:ℝ)/32000000)*t)| ≤ ((2565741976609:ℝ)/640000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 16, ([((143880510456474753905707950620719:ℝ)/3670016000000000000000), ((246766159847543678727959087391:ℝ)/18350080000000000000), ((-59404055923016929125509340097:ℝ)/367001600000000000), ((-13980906714480306207370237163:ℝ)/45875200000000000), ((-1207403421772965915578412537:ℝ)/4587520000000000), ((-73329777467722538265429593:ℝ)/573440000000000), ((-370034413662285610705057:ℝ)/11468800000000), ((-1388759572907480919:ℝ)/11468800000), ((83799149936068289881:ℝ)/28672000000), ((761349979261005261:ℝ)/716800000), ((66332277693276453:ℝ)/358400000), ((22179228388479:ℝ)/1792000), ((-49452995367:ℝ)/35840), ((-1676862567:ℝ)/4480), ((-14453883:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e) - ((143880510456474753905707950620719:ℝ)/3670016000000000000000) - ((246766159847543678727959087391:ℝ)/18350080000000000000)*t| ≤ ((1631095992829960574316877111577:ℝ)/3670016000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 16, ([((143880510456474753905707950620719:ℝ)/3670016000000000000000), ((246766159847543678727959087391:ℝ)/18350080000000000000), ((-59404055923016929125509340097:ℝ)/367001600000000000), ((-13980906714480306207370237163:ℝ)/45875200000000000), ((-1207403421772965915578412537:ℝ)/4587520000000000), ((-73329777467722538265429593:ℝ)/573440000000000), ((-370034413662285610705057:ℝ)/11468800000000), ((-1388759572907480919:ℝ)/11468800000), ((83799149936068289881:ℝ)/28672000000), ((761349979261005261:ℝ)/716800000), ((66332277693276453:ℝ)/358400000), ((22179228388479:ℝ)/1792000), ((-49452995367:ℝ)/35840), ((-1676862567:ℝ)/4480), ((-14453883:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e)| ≤ ((73989634023890075633652209303103:ℝ)/1835008000000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((76225167229862243:ℝ)/16000000000) - ((9305049966455109:ℝ)/800000000)*t| ≤ ((64765982479019:ℝ)/2000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-7627725:ℝ)/2), (173988600:ℝ), (-2299614450:ℝ), (13088188200:ℝ), (-38221499200:ℝ), (63366115840:ℝ), ((-445610508288:ℝ)/7), ((841540698112:ℝ)/21), ((-326820167680:ℝ)/21), ((10133438464:ℝ)/3), ((-2147483648:ℝ)/7)] : List ℝ).getD e 0) 16 hq1'
  have m13' : |centralNum13_23 q| ≤ ((380773923104941638768958133133:ℝ)/61035156250) := by
    rw [centralNum13_23_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-15801525:ℝ)/4), ((655493865:ℝ)/4), ((-7334421225:ℝ)/4), ((16442962485:ℝ)/2), ((-598626108395:ℝ)/32), ((414013307125:ℝ)/16), ((-4611984703125:ℝ)/224), ((399923828125:ℝ)/48), ((-4353201171875:ℝ)/2688), ((189736328125:ℝ)/1344), ((-244140625:ℝ)/56)] : List ℝ).getD e 0) 16 hq1'
  have m23' : |centralNum23_23 q| ≤ ((37053735712633254441695841:ℝ)/50000000) := by
    rw [centralNum23_23_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece14_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece14_E11 h0) m23'
  have c5 := scaled_affine (X := ((-939590876347:ℝ)/1000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((310360951302613:ℝ)/320000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((143880510456474753905707950620719:ℝ)/3670016000000000000000) + ((76225167229862243:ℝ)/16000000000)*((-939590876347:ℝ)/1000000000000) - ((-113883399459166089:ℝ)/50000000000)) (β := ((57076271792181:ℝ)/32000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((246766159847543678727959087391:ℝ)/18350080000000000000) - 3*((143880510456474753905707950620719:ℝ)/3670016000000000000000)) + ((9305049966455109:ℝ)/800000000)*((-939590876347:ℝ)/1000000000000) - ((-62048837984003871:ℝ)/5000000000)) ht
  have hW : pieceW q pieceX_14 2 3 = centralNum11_23 q + 8*(Real.exp (-(3*((83:ℝ)/20)))*Real.exp (-3*t))*centralNum12_23 q + 18*Real.exp (-8*q)*centralNum13_23 q + 72*Real.exp (-11*q)*centralNum23_23 q + 8*q^7*(2*q-3)^2*((-939590876347:ℝ)/1000000000000) + (0:ℝ) := by
    rw [pieceW_23, pieceX_14, sym4_23, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((2530435657793126630018389587309734459136802676193402579401207261753037:ℝ)/456069078498852220207950614957532668592727597932565316409482000000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((310360951302613:ℝ)/320000000) + ((57076271792181:ℝ)/32000000)*t) + (8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((143880510456474753905707950620719:ℝ)/3670016000000000000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((246766159847543678727959087391:ℝ)/18350080000000000000) - 3*((143880510456474753905707950620719:ℝ)/3670016000000000000000))*t) + (((76225167229862243:ℝ)/16000000000) + ((9305049966455109:ℝ)/800000000)*t)*((-939590876347:ℝ)/1000000000000) - (((-113883399459166089:ℝ)/50000000000) + t * ((-62048837984003871:ℝ)/5000000000)) = (((310360951302613:ℝ)/320000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((143880510456474753905707950620719:ℝ)/3670016000000000000000) + ((76225167229862243:ℝ)/16000000000)*((-939590876347:ℝ)/1000000000000) - ((-113883399459166089:ℝ)/50000000000)) + t*(((57076271792181:ℝ)/32000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((246766159847543678727959087391:ℝ)/18350080000000000000) - 3*((143880510456474753905707950620719:ℝ)/3670016000000000000000)) + ((9305049966455109:ℝ)/800000000)*((-939590876347:ℝ)/1000000000000) - ((-62048837984003871:ℝ)/5000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece14_e33 {q : ℝ} (h0 : ((41:ℝ)/10) ≤ q) (h1 : q ≤ ((21:ℝ)/5)) :
    |pieceW q pieceX_14 3 3 - (((3946647248306943:ℝ)/78125000) + (q - ((83:ℝ)/20)) * ((26363960431855923:ℝ)/200000000))| ≤ ((23393067092043699:ℝ)/1000000000) := by
  set t := q - ((83:ℝ)/20) with htd
  have hq : q = ((83:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece14_L3 piece14_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((83:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_33 q = ∑ e ∈ Finset.range 10, ([((18998845040425913:ℝ)/22400000000), ((1649320814260227:ℝ)/560000000), ((217110664615767:ℝ)/56000000), ((1103500697043:ℝ)/400000), ((24334708299:ℝ)/20000), ((353634963:ℝ)/1000), ((3445179:ℝ)/50), ((307038:ℝ)/35), ((4656:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_33; ring
  have h12 : centralNum12_33 q = ∑ e ∈ Finset.range 17, ([((41230941328148711003000578129438553:ℝ)/1027604480000000000000000), ((23692818113201835046023148133061441:ℝ)/51380224000000000000000), ((556736719237315346507385868141323:ℝ)/513802240000000000000), ((4262463601726832312011682259759:ℝ)/3670016000000000000), ((117493028208547386859310461581:ℝ)/183500800000000000), ((5895776699237462845556494779:ℝ)/45875200000000000), ((-139227166014147511202956467:ℝ)/2293760000000000), ((-8592089042670511783846443:ℝ)/160563200000000), ((-143711605302226719179343:ℝ)/8028160000000), ((-1116354678953860557577:ℝ)/401408000000), ((729756164392045443:ℝ)/14336000000), ((76972591997090001:ℝ)/716800000), ((138898750573071:ℝ)/7168000), ((414529541541:ℝ)/358400), ((-10298322747:ℝ)/125440), ((-495362061:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_33; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((18998845040425913:ℝ)/22400000000), ((1649320814260227:ℝ)/560000000), ((217110664615767:ℝ)/56000000), ((1103500697043:ℝ)/400000), ((24334708299:ℝ)/20000), ((353634963:ℝ)/1000), ((3445179:ℝ)/50), ((307038:ℝ)/35), ((4656:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((41230941328148711003000578129438553:ℝ)/1027604480000000000000000), ((23692818113201835046023148133061441:ℝ)/51380224000000000000000), ((556736719237315346507385868141323:ℝ)/513802240000000000000), ((4262463601726832312011682259759:ℝ)/3670016000000000000), ((117493028208547386859310461581:ℝ)/183500800000000000), ((5895776699237462845556494779:ℝ)/45875200000000000), ((-139227166014147511202956467:ℝ)/2293760000000000), ((-8592089042670511783846443:ℝ)/160563200000000), ((-143711605302226719179343:ℝ)/8028160000000), ((-1116354678953860557577:ℝ)/401408000000), ((729756164392045443:ℝ)/14336000000), ((76972591997090001:ℝ)/716800000), ((138898750573071:ℝ)/7168000), ((414529541541:ℝ)/358400), ((-10298322747:ℝ)/125440), ((-495362061:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 15 ht
  have m12 := abs_poly_le (fun e => ([((41230941328148711003000578129438553:ℝ)/1027604480000000000000000), ((23692818113201835046023148133061441:ℝ)/51380224000000000000000), ((556736719237315346507385868141323:ℝ)/513802240000000000000), ((4262463601726832312011682259759:ℝ)/3670016000000000000), ((117493028208547386859310461581:ℝ)/183500800000000000), ((5895776699237462845556494779:ℝ)/45875200000000000), ((-139227166014147511202956467:ℝ)/2293760000000000), ((-8592089042670511783846443:ℝ)/160563200000000), ((-143711605302226719179343:ℝ)/8028160000000), ((-1116354678953860557577:ℝ)/401408000000), ((729756164392045443:ℝ)/14336000000), ((76972591997090001:ℝ)/716800000), ((138898750573071:ℝ)/7168000), ((414529541541:ℝ)/358400), ((-10298322747:ℝ)/125440), ((-495362061:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 17 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((18998845040425913:ℝ)/22400000000), ((1649320814260227:ℝ)/560000000), ((217110664615767:ℝ)/56000000), ((1103500697043:ℝ)/400000), ((24334708299:ℝ)/20000), ((353634963:ℝ)/1000), ((3445179:ℝ)/50), ((307038:ℝ)/35), ((4656:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e) - (((18998845040425913:ℝ)/22400000000) + ((1649320814260227:ℝ)/560000000)*t)| ≤ ((225008012168257:ℝ)/22400000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 17, ([((41230941328148711003000578129438553:ℝ)/1027604480000000000000000), ((23692818113201835046023148133061441:ℝ)/51380224000000000000000), ((556736719237315346507385868141323:ℝ)/513802240000000000000), ((4262463601726832312011682259759:ℝ)/3670016000000000000), ((117493028208547386859310461581:ℝ)/183500800000000000), ((5895776699237462845556494779:ℝ)/45875200000000000), ((-139227166014147511202956467:ℝ)/2293760000000000), ((-8592089042670511783846443:ℝ)/160563200000000), ((-143711605302226719179343:ℝ)/8028160000000), ((-1116354678953860557577:ℝ)/401408000000), ((729756164392045443:ℝ)/14336000000), ((76972591997090001:ℝ)/716800000), ((138898750573071:ℝ)/7168000), ((414529541541:ℝ)/358400), ((-10298322747:ℝ)/125440), ((-495362061:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e) - ((41230941328148711003000578129438553:ℝ)/1027604480000000000000000) - ((23692818113201835046023148133061441:ℝ)/51380224000000000000000)*t| ≤ ((1468512183472981224252842368013629:ℝ)/513802240000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 17, ([((41230941328148711003000578129438553:ℝ)/1027604480000000000000000), ((23692818113201835046023148133061441:ℝ)/51380224000000000000000), ((556736719237315346507385868141323:ℝ)/513802240000000000000), ((4262463601726832312011682259759:ℝ)/3670016000000000000), ((117493028208547386859310461581:ℝ)/183500800000000000), ((5895776699237462845556494779:ℝ)/45875200000000000), ((-139227166014147511202956467:ℝ)/2293760000000000), ((-8592089042670511783846443:ℝ)/160563200000000), ((-143711605302226719179343:ℝ)/8028160000000), ((-1116354678953860557577:ℝ)/401408000000), ((729756164392045443:ℝ)/14336000000), ((76972591997090001:ℝ)/716800000), ((138898750573071:ℝ)/7168000), ((414529541541:ℝ)/358400), ((-10298322747:ℝ)/125440), ((-495362061:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e)| ≤ ((16965195952074127124382352749631813:ℝ)/256901120000000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((76225167229862243:ℝ)/16000000000), ((9305049966455109:ℝ)/800000000), ((62760734564919:ℝ)/5000000), ((491335997313:ℝ)/62500), ((157502731659:ℝ)/50000), ((2094373113:ℝ)/2500), ((18489744:ℝ)/125), ((418128:ℝ)/25), ((5496:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((76225167229862243:ℝ)/16000000000) - ((9305049966455109:ℝ)/800000000)*t| ≤ ((64765982479019:ℝ)/2000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-8120475:ℝ)/4), ((464861025:ℝ)/2), (-5906535975:ℝ), ((411904731750:ℝ)/7), ((-2024051769000:ℝ)/7), ((5554394637600:ℝ)/7), (-1314913862656:ℝ), ((9709155336192:ℝ)/7), ((-6724555112448:ℝ)/7), ((1313173667840:ℝ)/3), ((-6168244125696:ℝ)/49), ((3004329623552:ℝ)/147), ((-68719476736:ℝ)/49)] : List ℝ).getD e 0) 17 hq1'
  have m13' : |centralNum13_33 q| ≤ ((135838419095360575735657118969121:ℝ)/610351562500) := by
    rw [centralNum13_33_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-16872075:ℝ)/8), ((1833754545:ℝ)/8), ((-83998007145:ℝ)/16), ((4929124002765:ℝ)/112), ((-76723155584685:ℝ)/448), ((164888745653055:ℝ)/448), ((-63358359907625:ℝ)/128), ((364713160040625:ℝ)/896), ((-334937462578125:ℝ)/1792), ((245466998046875:ℝ)/5376), ((-72144521484375:ℝ)/12544), ((6518798828125:ℝ)/18816), ((-6103515625:ℝ)/784)] : List ℝ).getD e 0) 17 hq1'
  have m23' : |centralNum23_33 q| ≤ ((1924521862703053679812195407:ℝ)/100000000) := by
    rw [centralNum23_33_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece14_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece14_E11 h0) m23'
  have c5 := scaled_affine (X := ((25404409743:ℝ)/2500000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3))| ≤ ((199296084578794383740672000000000:ℝ)/41915274432460212508657804684359) := by
    rw [abs_neg, tailWeight_3, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((21:ℝ)/5)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((21:ℝ)/5)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece14_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((3308571812705231500:ℝ)/129140163)) ≤ ((21:ℝ)/5)^6*(8000*(2*((21:ℝ)/5)-3)^2*(1/((172490841285844495920402488413:ℝ)/25000000000))*((3308571812705231500:ℝ)/129140163)) := by
          gcongr
      _ ≤ ((199296084578794383740672000000000:ℝ)/41915274432460212508657804684359) := by norm_num
  have c7 := affine_round (α := ((18998845040425913:ℝ)/22400000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((41230941328148711003000578129438553:ℝ)/1027604480000000000000000) + ((76225167229862243:ℝ)/16000000000)*((25404409743:ℝ)/2500000000) - ((3946647248306943:ℝ)/78125000)) (β := ((1649320814260227:ℝ)/560000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((23692818113201835046023148133061441:ℝ)/51380224000000000000000) - 3*((41230941328148711003000578129438553:ℝ)/1027604480000000000000000)) + ((9305049966455109:ℝ)/800000000)*((25404409743:ℝ)/2500000000) - ((26363960431855923:ℝ)/200000000)) ht
  have hW : pieceW q pieceX_14 3 3 = centralNum11_33 q + 8*(Real.exp (-(3*((83:ℝ)/20)))*Real.exp (-3*t))*centralNum12_33 q + 18*Real.exp (-8*q)*centralNum13_33 q + 72*Real.exp (-11*q)*centralNum23_33 q + 8*q^7*(2*q-3)^2*((25404409743:ℝ)/2500000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3)) := by
    rw [pieceW_33, pieceX_14, sym4_33, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((1302923988278535853652392406726125946077299201556193269335402968836547:ℝ)/31924835494919655414556543047027286801490931855279572148663740000000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((18998845040425913:ℝ)/22400000000) + ((1649320814260227:ℝ)/560000000)*t) + (8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((41230941328148711003000578129438553:ℝ)/1027604480000000000000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((23692818113201835046023148133061441:ℝ)/51380224000000000000000) - 3*((41230941328148711003000578129438553:ℝ)/1027604480000000000000000))*t) + (((76225167229862243:ℝ)/16000000000) + ((9305049966455109:ℝ)/800000000)*t)*((25404409743:ℝ)/2500000000) - (((3946647248306943:ℝ)/78125000) + t * ((26363960431855923:ℝ)/200000000)) = (((18998845040425913:ℝ)/22400000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*((41230941328148711003000578129438553:ℝ)/1027604480000000000000000) + ((76225167229862243:ℝ)/16000000000)*((25404409743:ℝ)/2500000000) - ((3946647248306943:ℝ)/78125000)) + t*(((1649320814260227:ℝ)/560000000) + 8*(((1/((255250323281310323230844226733:ℝ)/1000000000000000000000000))+(1/((127625157653632984343797997311:ℝ)/500000000000000000000000)))/2)*(((23692818113201835046023148133061441:ℝ)/51380224000000000000000) - 3*((41230941328148711003000578129438553:ℝ)/1027604480000000000000000)) + ((9305049966455109:ℝ)/800000000)*((25404409743:ℝ)/2500000000) - ((26363960431855923:ℝ)/200000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece14_plus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((581978479844851799:ℝ)/100000000000) + ((1:ℝ)/20)*((134836843187854117:ℝ)/10000000000) - (((183519573022389503:ℝ)/5000000000000) + ((612999379887766889:ℝ)/100000000000000) + ((184949203468018519:ℝ)/100000000000000) + ((223719447480223761:ℝ)/25000000000000)))
      (((-5353799221362511:ℝ)/5000000000) + ((1:ℝ)/20)*((-172958207820686779:ℝ)/100000000000))
      (((207765141230859569:ℝ)/25000000000000) + ((1:ℝ)/20)*((-45208156226968049:ℝ)/1250000000000))
      (((-79509638909429079:ℝ)/2000000000000) + ((1:ℝ)/20)*((-404858694398523533:ℝ)/1000000000000))
      (((113272646959838049:ℝ)/25000000000) + ((1:ℝ)/20)*((971614456034509961:ℝ)/100000000000) - (((612999379887766889:ℝ)/100000000000000) + ((66104277705211601:ℝ)/2500000000000) + ((13146875289862143:ℝ)/625000000000) + ((473333999364526031:ℝ)/10000000000000)))
      (((-485731117039720241:ℝ)/1000000000000) + ((1:ℝ)/20)*((-10820430413015879:ℝ)/10000000000))
      (((25752124246234523:ℝ)/40000000000) + ((1:ℝ)/20)*((177745988348358287:ℝ)/50000000000))
      (((307642783852511279:ℝ)/100000000000) + ((1:ℝ)/20)*((12801954321983373:ℝ)/1250000000) - (((184949203468018519:ℝ)/100000000000000) + ((13146875289862143:ℝ)/625000000000) + ((52485629278576793:ℝ)/500000000000) + ((360526448407087881:ℝ)/500000000000)))
      (((-113883399459166089:ℝ)/50000000000) + ((1:ℝ)/20)*((-62048837984003871:ℝ)/5000000000))
      (((3946647248306943:ℝ)/78125000) + ((1:ℝ)/20)*((26363960431855923:ℝ)/200000000) - (((223719447480223761:ℝ)/25000000000000) + ((473333999364526031:ℝ)/10000000000000) + ((360526448407087881:ℝ)/500000000000) + ((23393067092043699:ℝ)/1000000000))) i j :=
  quadForm_nonneg_of_ldl ((161008420901263596747:ℝ)/25000000000000) ((592188124094653199907368353466379576319:ℝ)/125787828829112184958593750000000) ((158585455526168568072430174108087880290970626110624320710569:ℝ)/59218812409465319990736835346637957631900000000000000) ((80813396525383884791973959308362405616678793017956146734028265882480805957120031271:ℝ)/2706525107646610228436141638111366490299232018954655073460377600000000000000) ((-57861947409142279475:ℝ)/322016841802527193494) ((54185661667963840:ℝ)/53669473633754532249) ((-5999775417464071615:ℝ)/644033683605054386988) ((-542059905838656247123479329108549581575:ℝ)/4737504992757225599258946827731036610552) ((26108105790125560551766064708682477280675:ℝ)/151600159768231219176286298487393171537664) ((-886017219237060835577241978477624341653559657342314260957675:ℝ)/845789096139565696386294261909802028218510005923329710456368)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece14_minus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((581978479844851799:ℝ)/100000000000) - ((1:ℝ)/20)*((134836843187854117:ℝ)/10000000000) - (((183519573022389503:ℝ)/5000000000000) + ((612999379887766889:ℝ)/100000000000000) + ((184949203468018519:ℝ)/100000000000000) + ((223719447480223761:ℝ)/25000000000000)))
      (((-5353799221362511:ℝ)/5000000000) - ((1:ℝ)/20)*((-172958207820686779:ℝ)/100000000000))
      (((207765141230859569:ℝ)/25000000000000) - ((1:ℝ)/20)*((-45208156226968049:ℝ)/1250000000000))
      (((-79509638909429079:ℝ)/2000000000000) - ((1:ℝ)/20)*((-404858694398523533:ℝ)/1000000000000))
      (((113272646959838049:ℝ)/25000000000) - ((1:ℝ)/20)*((971614456034509961:ℝ)/100000000000) - (((612999379887766889:ℝ)/100000000000000) + ((66104277705211601:ℝ)/2500000000000) + ((13146875289862143:ℝ)/625000000000) + ((473333999364526031:ℝ)/10000000000000)))
      (((-485731117039720241:ℝ)/1000000000000) - ((1:ℝ)/20)*((-10820430413015879:ℝ)/10000000000))
      (((25752124246234523:ℝ)/40000000000) - ((1:ℝ)/20)*((177745988348358287:ℝ)/50000000000))
      (((307642783852511279:ℝ)/100000000000) - ((1:ℝ)/20)*((12801954321983373:ℝ)/1250000000) - (((184949203468018519:ℝ)/100000000000000) + ((13146875289862143:ℝ)/625000000000) + ((52485629278576793:ℝ)/500000000000) + ((360526448407087881:ℝ)/500000000000)))
      (((-113883399459166089:ℝ)/50000000000) - ((1:ℝ)/20)*((-62048837984003871:ℝ)/5000000000))
      (((3946647248306943:ℝ)/78125000) - ((1:ℝ)/20)*((26363960431855923:ℝ)/200000000) - (((223719447480223761:ℝ)/25000000000000) + ((473333999364526031:ℝ)/10000000000000) + ((360526448407087881:ℝ)/500000000000) + ((23393067092043699:ℝ)/1000000000))) i j :=
  quadForm_nonneg_of_ldl ((127299210104300067497:ℝ)/25000000000000) ((23893402646026556855933108297864074762691:ℝ)/6364960505215003374850000000000000) ((568745010488249107452966889357341291854349337627524092562829:ℝ)/341334323514665097941901547112343925181300000000000000) ((8260072928686248379643559961653377121252588331737536752115925870012746209368429447:ℝ)/454996008390599285962373511485873033483479470102019274050263200000000000000) ((-49214037018107940525:ℝ)/254598420208600134994) ((252973297457827618:ℝ)/127299210104300067497) ((-1951188473478836285:ℝ)/509196840417200269988) ((-390693068249248090820813444907744671950:ℝ)/3413343235146650979419015471123439251813) ((1681387818616189016171678450859306168225:ℝ)/13653372940586603917676061884493757007252) ((-547577873368184786350843184646788539771467353598617236184605:ℝ)/568745010488249107452966889357341291854349337627524092562829)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

/-- **Piece 14.** The piece matrix is positive semidefinite on `q ∈ [41/10, 21/5]`. -/
theorem piece_14 {q : ℝ} (h0 : ((41:ℝ)/10) ≤ q) (h1 : q ≤ ((21:ℝ)/5)) (y : Fin 4 → ℝ) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceW q pieceX_14 i j :=
  pieceForm_nonneg (pieceW_symm (sym4_symm _ _ _ _ _ _ _ _ _ _) q) (by norm_num : (0:ℝ) < ((1:ℝ)/20))
    (abs_le.mpr ⟨by linarith, by linarith⟩)
    (piece14_e00 h0 h1) (piece14_e01 h0 h1) (piece14_e02 h0 h1) (piece14_e03 h0 h1) (piece14_e11 h0 h1) (piece14_e12 h0 h1) (piece14_e13 h0 h1) (piece14_e22 h0 h1) (piece14_e23 h0 h1) (piece14_e33 h0 h1)
    piece14_plus piece14_minus y

end
end RHTower.ThetaCuspOddFourPieces
