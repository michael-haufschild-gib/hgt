import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourPieceSetup

/-!
# Piece certificates 20–24 on `q ∈ [47/10, 11/2]`

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

/-! #### Piece 20 (seam), `q ∈ [47/10, 24/5]` -/

/-- The compensation matrix of piece 20. -/
def pieceX_20 : Fin 4 → Fin 4 → ℝ :=
  sym4 ((11:ℝ)/1000) (0:ℝ) (0:ℝ) (0:ℝ) ((11:ℝ)/1000) (0:ℝ) (0:ℝ) ((11:ℝ)/1000) (0:ℝ) ((11:ℝ)/1000)

theorem piece20_L3 : ((154417446535217520259464374759:ℝ)/100000000000000000000000) ≤ Real.exp ((3:ℝ)*((19:ℝ)/4)) := by
  have h := le_exp_nat_add 14 (f := ((1:ℝ)/4)) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((19:ℝ)/4) = ((14:ℕ):ℝ) + ((1:ℝ)/4) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece20_U3 : Real.exp ((3:ℝ)*((19:ℝ)/4)) ≤ ((77208723412503754641362627217:ℝ)/50000000000000000000000) := by
  have h := exp_nat_add_le 14 (f := ((1:ℝ)/4)) (by norm_num) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((19:ℝ)/4) = ((14:ℕ):ℝ) + ((1:ℝ)/4) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem piece20_L8_at : ((213536643677435843698409539857:ℝ)/10000000000000) ≤ Real.exp ((8:ℝ)*((47:ℝ)/10)) := by
  have h := le_exp_nat_add 37 (f := ((3:ℝ)/5)) (by norm_num)
  rw [show ((8:ℝ):ℝ)*((47:ℝ)/10) = ((37:ℕ):ℝ) + ((3:ℝ)/5) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece20_E8 {q : ℝ} (h0 : ((47:ℝ)/10) ≤ q) : Real.exp (-((8:ℝ))*q) ≤ 1/((213536643677435843698409539857:ℝ)/10000000000000) := by
  have hm : Real.exp (-((8:ℝ))*q) ≤ Real.exp (-((8:ℝ)*((47:ℝ)/10))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece20_L8_at (le_refl _)).2

theorem piece20_L11_at : ((141903916928437388736516488657:ℝ)/5000000) ≤ Real.exp ((11:ℝ)*((47:ℝ)/10)) := by
  have h := le_exp_nat_add 51 (f := ((7:ℝ)/10)) (by norm_num)
  rw [show ((11:ℝ):ℝ)*((47:ℝ)/10) = ((51:ℕ):ℝ) + ((7:ℝ)/10) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece20_E11 {q : ℝ} (h0 : ((47:ℝ)/10) ≤ q) : Real.exp (-((11:ℝ))*q) ≤ 1/((141903916928437388736516488657:ℝ)/5000000) := by
  have hm : Real.exp (-((11:ℝ))*q) ≤ Real.exp (-((11:ℝ)*((47:ℝ)/10))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece20_L11_at (le_refl _)).2

theorem piece20_Lt_at : ((394209393455736254577324892029:ℝ)/100000000) ≤ Real.exp (((529:ℝ)/50)*((47:ℝ)/10)) := by
  have h := le_exp_nat_add 49 (f := ((363:ℝ)/500)) (by norm_num)
  rw [show (((529:ℝ)/50):ℝ)*((47:ℝ)/10) = ((49:ℕ):ℝ) + ((363:ℝ)/500) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece20_Et {q : ℝ} (h0 : ((47:ℝ)/10) ≤ q) : Real.exp (-(((529:ℝ)/50))*q) ≤ 1/((394209393455736254577324892029:ℝ)/100000000) := by
  have hm : Real.exp (-(((529:ℝ)/50))*q) ≤ Real.exp (-(((529:ℝ)/50)*((47:ℝ)/10))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece20_Lt_at (le_refl _)).2

theorem piece20_e00 {q : ℝ} (h0 : ((47:ℝ)/10) ≤ q) (h1 : q ≤ ((24:ℝ)/5)) :
    |pieceW q pieceX_20 0 0 - (((212518234352967343:ℝ)/10000000000) + (q - ((19:ℝ)/4)) * ((428144089444091513:ℝ)/10000000000))| ≤ ((99221949172849951:ℝ)/1000000000000) := by
  set t := q - ((19:ℝ)/4) with htd
  have hq : q = ((19:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece20_L3 piece20_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((19:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_00 q = ∑ e ∈ Finset.range 10, ([((172517245627:ℝ)/8192), ((86799650445:ℝ)/2048), ((304560177:ℝ)/8), ((320198697:ℝ)/16), ((108461367:ℝ)/16), ((6133029:ℝ)/4), (231420:ℝ), (22464:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_00; ring
  have h12 : centralNum12_00 q = ∑ e ∈ Finset.range 11, ([((-64867378227491:ℝ)/32768), ((-35985441422781:ℝ)/8192), ((-4493607132507:ℝ)/1024), ((-332616072843:ℝ)/128), ((-64638221445:ℝ)/64), ((-4306940463:ℝ)/16), (-49819938:ℝ), (-6321798:ℝ), (-526326:ℝ), (-25960:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_00; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((172517245627:ℝ)/8192), ((86799650445:ℝ)/2048), ((304560177:ℝ)/8), ((320198697:ℝ)/16), ((108461367:ℝ)/16), ((6133029:ℝ)/4), (231420:ℝ), (22464:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-64867378227491:ℝ)/32768), ((-35985441422781:ℝ)/8192), ((-4493607132507:ℝ)/1024), ((-332616072843:ℝ)/128), ((-64638221445:ℝ)/64), ((-4306940463:ℝ)/16), (-49819938:ℝ), (-6321798:ℝ), (-526326:ℝ), (-25960:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 9 ht
  have m12 := abs_poly_le (fun e => ([((-64867378227491:ℝ)/32768), ((-35985441422781:ℝ)/8192), ((-4493607132507:ℝ)/1024), ((-332616072843:ℝ)/128), ((-64638221445:ℝ)/64), ((-4306940463:ℝ)/16), (-49819938:ℝ), (-6321798:ℝ), (-526326:ℝ), (-25960:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 11 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((172517245627:ℝ)/8192), ((86799650445:ℝ)/2048), ((304560177:ℝ)/8), ((320198697:ℝ)/16), ((108461367:ℝ)/16), ((6133029:ℝ)/4), (231420:ℝ), (22464:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - (((172517245627:ℝ)/8192) + ((86799650445:ℝ)/2048)*t)| ≤ ((390877832522899:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 11, ([((-64867378227491:ℝ)/32768), ((-35985441422781:ℝ)/8192), ((-4493607132507:ℝ)/1024), ((-332616072843:ℝ)/128), ((-64638221445:ℝ)/64), ((-4306940463:ℝ)/16), (-49819938:ℝ), (-6321798:ℝ), (-526326:ℝ), (-25960:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e) - ((-64867378227491:ℝ)/32768) - ((-35985441422781:ℝ)/8192)*t| ≤ ((904155052129829017:ℝ)/80000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 11, ([((-64867378227491:ℝ)/32768), ((-35985441422781:ℝ)/8192), ((-4493607132507:ℝ)/1024), ((-332616072843:ℝ)/128), ((-64638221445:ℝ)/64), ((-4306940463:ℝ)/16), (-49819938:ℝ), (-6321798:ℝ), (-526326:ℝ), (-25960:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((21587255126654976:ℝ)/9765625) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((151064323891:ℝ)/8192) - ((78895942437:ℝ)/2048)*t| ≤ ((366071587462999:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((24:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (600:ℝ), (-7776:ℝ), (16800:ℝ), (-9216:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m13' : |centralNum13_00 q| ≤ ((827980018788335616:ℝ)/9765625) := by
    rw [centralNum13_00_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((24:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (780:ℝ), (-6156:ℝ), (15288:ℝ), (-14400:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m23' : |centralNum23_00 q| ≤ ((226467245218332672:ℝ)/1953125) := by
    rw [centralNum23_00_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((77208723412503754641362627217:ℝ)/50000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece20_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece20_E11 h0) m23'
  have c5 := scaled_affine (X := ((11:ℝ)/1000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0))| ≤ ((679853300089303859200000:ℝ)/3547884541101626291195924028261) := by
    rw [abs_neg, tailWeight_0, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((24:ℝ)/5)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((24:ℝ)/5)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece20_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((10465499600:ℝ)/59049)) ≤ ((24:ℝ)/5)^6*(8000*(2*((24:ℝ)/5)-3)^2*(1/((394209393455736254577324892029:ℝ)/100000000))*((10465499600:ℝ)/59049)) := by
          gcongr
      _ ≤ ((679853300089303859200000:ℝ)/3547884541101626291195924028261) := by norm_num
  have c7 := affine_round (α := ((172517245627:ℝ)/8192) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((-64867378227491:ℝ)/32768) + ((151064323891:ℝ)/8192)*((11:ℝ)/1000) - ((212518234352967343:ℝ)/10000000000)) (β := ((86799650445:ℝ)/2048) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((-35985441422781:ℝ)/8192) - 3*((-64867378227491:ℝ)/32768)) + ((78895942437:ℝ)/2048)*((11:ℝ)/1000) - ((428144089444091513:ℝ)/10000000000)) ht
  have hW : pieceW q pieceX_20 0 0 = centralNum11_00 q + 8*(Real.exp (-(3*((19:ℝ)/4)))*Real.exp (-3*t))*centralNum12_00 q + 18*Real.exp (-8*q)*centralNum13_00 q + 72*Real.exp (-11*q)*centralNum23_00 q + 8*q^7*(2*q-3)^2*((11:ℝ)/1000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0)) := by
    rw [pieceW_00, pieceX_20, sym4_00, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((249614253908327075759172174346840845355808807861349130083403:ℝ)/19075798271364313190990356081125878532045344305037601945124800000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((172517245627:ℝ)/8192) + ((86799650445:ℝ)/2048)*t) + (8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((-64867378227491:ℝ)/32768) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((-35985441422781:ℝ)/8192) - 3*((-64867378227491:ℝ)/32768))*t) + (((151064323891:ℝ)/8192) + ((78895942437:ℝ)/2048)*t)*((11:ℝ)/1000) - (((212518234352967343:ℝ)/10000000000) + t * ((428144089444091513:ℝ)/10000000000)) = (((172517245627:ℝ)/8192) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((-64867378227491:ℝ)/32768) + ((151064323891:ℝ)/8192)*((11:ℝ)/1000) - ((212518234352967343:ℝ)/10000000000)) + t*(((86799650445:ℝ)/2048) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((-35985441422781:ℝ)/8192) - 3*((-64867378227491:ℝ)/32768)) + ((78895942437:ℝ)/2048)*((11:ℝ)/1000) - ((428144089444091513:ℝ)/10000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece20_e01 {q : ℝ} (h0 : ((47:ℝ)/10) ≤ q) (h1 : q ≤ ((24:ℝ)/5)) :
    |pieceW q pieceX_20 0 1 - (((-133045247229337619:ℝ)/50000000000) + (q - ((19:ℝ)/4)) * ((-24008810107406587:ℝ)/6250000000))| ≤ ((105897519968414071:ℝ)/12500000000000) := by
  set t := q - ((19:ℝ)/4) with htd
  have hq : q = ((19:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece20_L3 piece20_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((19:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_01 q = ∑ e ∈ Finset.range 8, ([((-2681615217:ℝ)/1024), ((-987963501:ℝ)/256), ((-155994237:ℝ)/64), ((-13683705:ℝ)/16), ((-720195:ℝ)/4), (-22743:ℝ), (-1596:ℝ), (-48:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_01; ring
  have h12 : centralNum12_01 q = ∑ e ∈ Finset.range 12, ([((-2132267568491031:ℝ)/262144), ((-686872167848169:ℝ)/32768), ((-401441786980389:ℝ)/16384), ((-35126782678623:ℝ)/2048), ((-4091133029475:ℝ)/512), ((-166501662201:ℝ)/64), ((-19331362869:ℝ)/32), ((-400202139:ℝ)/4), ((-46329939:ℝ)/4), (-892650:ℝ), (-41220:ℝ), (-864:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_01; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-2681615217:ℝ)/1024), ((-987963501:ℝ)/256), ((-155994237:ℝ)/64), ((-13683705:ℝ)/16), ((-720195:ℝ)/4), (-22743:ℝ), (-1596:ℝ), (-48:ℝ)] : List ℝ).getD e 0) 6 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-2132267568491031:ℝ)/262144), ((-686872167848169:ℝ)/32768), ((-401441786980389:ℝ)/16384), ((-35126782678623:ℝ)/2048), ((-4091133029475:ℝ)/512), ((-166501662201:ℝ)/64), ((-19331362869:ℝ)/32), ((-400202139:ℝ)/4), ((-46329939:ℝ)/4), (-892650:ℝ), (-41220:ℝ), (-864:ℝ)] : List ℝ).getD e 0) 10 ht
  have m12 := abs_poly_le (fun e => ([((-2132267568491031:ℝ)/262144), ((-686872167848169:ℝ)/32768), ((-401441786980389:ℝ)/16384), ((-35126782678623:ℝ)/2048), ((-4091133029475:ℝ)/512), ((-166501662201:ℝ)/64), ((-19331362869:ℝ)/32), ((-400202139:ℝ)/4), ((-46329939:ℝ)/4), (-892650:ℝ), (-41220:ℝ), (-864:ℝ)] : List ℝ).getD e 0) 12 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 8, ([((-2681615217:ℝ)/1024), ((-987963501:ℝ)/256), ((-155994237:ℝ)/64), ((-13683705:ℝ)/16), ((-720195:ℝ)/4), (-22743:ℝ), (-1596:ℝ), (-48:ℝ)] : List ℝ).getD e 0 * t^e) - (((-2681615217:ℝ)/1024) + ((-987963501:ℝ)/256)*t)| ≤ ((248062450599:ℝ)/40000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 12, ([((-2132267568491031:ℝ)/262144), ((-686872167848169:ℝ)/32768), ((-401441786980389:ℝ)/16384), ((-35126782678623:ℝ)/2048), ((-4091133029475:ℝ)/512), ((-166501662201:ℝ)/64), ((-19331362869:ℝ)/32), ((-400202139:ℝ)/4), ((-46329939:ℝ)/4), (-892650:ℝ), (-41220:ℝ), (-864:ℝ)] : List ℝ).getD e 0 * t^e) - ((-2132267568491031:ℝ)/262144) - ((-686872167848169:ℝ)/32768)*t| ≤ ((812158556880826404579:ℝ)/12800000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 12, ([((-2132267568491031:ℝ)/262144), ((-686872167848169:ℝ)/32768), ((-401441786980389:ℝ)/16384), ((-35126782678623:ℝ)/2048), ((-4091133029475:ℝ)/512), ((-166501662201:ℝ)/64), ((-19331362869:ℝ)/32), ((-400202139:ℝ)/4), ((-46329939:ℝ)/4), (-892650:ℝ), (-41220:ℝ), (-864:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((451439887820783616:ℝ)/48828125) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((151064323891:ℝ)/8192) - ((78895942437:ℝ)/2048)*t| ≤ ((366071587462999:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((24:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-6288:ℝ), (81024:ℝ), (-238720:ℝ), (246784:ℝ), (-98304:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m13' : |centralNum13_01 q| ≤ ((244721217953612169216:ℝ)/48828125) := by
    rw [centralNum13_01_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((24:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-7368:ℝ), (59208:ℝ), (-155734:ℝ), (205300:ℝ), (-60000:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m23' : |centralNum23_01 q| ≤ ((6700228345558204416:ℝ)/1953125) := by
    rw [centralNum23_01_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((77208723412503754641362627217:ℝ)/50000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece20_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece20_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-2681615217:ℝ)/1024) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((-2132267568491031:ℝ)/262144) + ((151064323891:ℝ)/8192)*(0:ℝ) - ((-133045247229337619:ℝ)/50000000000)) (β := ((-987963501:ℝ)/256) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((-686872167848169:ℝ)/32768) - 3*((-2132267568491031:ℝ)/262144)) + ((78895942437:ℝ)/2048)*(0:ℝ) - ((-24008810107406587:ℝ)/6250000000)) ht
  have hW : pieceW q pieceX_20 0 1 = centralNum11_01 q + 8*(Real.exp (-(3*((19:ℝ)/4)))*Real.exp (-3*t))*centralNum12_01 q + 18*Real.exp (-8*q)*centralNum13_01 q + 72*Real.exp (-11*q)*centralNum23_01 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_01, pieceX_20, sym4_01, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((3744835128648967534499797077488324082998879845859831211119:ℝ)/993531159966891312030747712558639506877361682554041767975250000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-2681615217:ℝ)/1024) + ((-987963501:ℝ)/256)*t) + (8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((-2132267568491031:ℝ)/262144) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((-686872167848169:ℝ)/32768) - 3*((-2132267568491031:ℝ)/262144))*t) + (((151064323891:ℝ)/8192) + ((78895942437:ℝ)/2048)*t)*(0:ℝ) - (((-133045247229337619:ℝ)/50000000000) + t * ((-24008810107406587:ℝ)/6250000000)) = (((-2681615217:ℝ)/1024) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((-2132267568491031:ℝ)/262144) + ((151064323891:ℝ)/8192)*(0:ℝ) - ((-133045247229337619:ℝ)/50000000000)) + t*(((-987963501:ℝ)/256) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((-686872167848169:ℝ)/32768) - 3*((-2132267568491031:ℝ)/262144)) + ((78895942437:ℝ)/2048)*(0:ℝ) - ((-24008810107406587:ℝ)/6250000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece20_e02 {q : ℝ} (h0 : ((47:ℝ)/10) ≤ q) (h1 : q ≤ ((24:ℝ)/5)) :
    |pieceW q pieceX_20 0 2 - (((-4263338068744913:ℝ)/100000000000) + (q - ((19:ℝ)/4)) * ((-49026316964314259:ℝ)/1250000000000))| ≤ ((5055772474767419:ℝ)/1562500000000) := by
  set t := q - ((19:ℝ)/4) with htd
  have hq : q = ((19:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece20_L3 piece20_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((19:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_02 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_02; ring
  have h12 : centralNum12_02 q = ∑ e ∈ Finset.range 13, ([((-69031300055402961:ℝ)/8388608), ((-67650003444429693:ℝ)/2097152), ((-27500709650789781:ℝ)/524288), ((-6404713487565615:ℝ)/131072), ((-121406960503215:ℝ)/4096), ((-51080992047369:ℝ)/4096), ((-3847032699237:ℝ)/1024), ((-209919783879:ℝ)/256), ((-16521881985:ℝ)/128), ((-458232705:ℝ)/32), ((-8514801:ℝ)/8), ((-95283:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_02; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-69031300055402961:ℝ)/8388608), ((-67650003444429693:ℝ)/2097152), ((-27500709650789781:ℝ)/524288), ((-6404713487565615:ℝ)/131072), ((-121406960503215:ℝ)/4096), ((-51080992047369:ℝ)/4096), ((-3847032699237:ℝ)/1024), ((-209919783879:ℝ)/256), ((-16521881985:ℝ)/128), ((-458232705:ℝ)/32), ((-8514801:ℝ)/8), ((-95283:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((-69031300055402961:ℝ)/8388608), ((-67650003444429693:ℝ)/2097152), ((-27500709650789781:ℝ)/524288), ((-6404713487565615:ℝ)/131072), ((-121406960503215:ℝ)/4096), ((-51080992047369:ℝ)/4096), ((-3847032699237:ℝ)/1024), ((-209919783879:ℝ)/256), ((-16521881985:ℝ)/128), ((-458232705:ℝ)/32), ((-8514801:ℝ)/8), ((-95283:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((-69031300055402961:ℝ)/8388608), ((-67650003444429693:ℝ)/2097152), ((-27500709650789781:ℝ)/524288), ((-6404713487565615:ℝ)/131072), ((-121406960503215:ℝ)/4096), ((-51080992047369:ℝ)/4096), ((-3847032699237:ℝ)/1024), ((-209919783879:ℝ)/256), ((-16521881985:ℝ)/128), ((-458232705:ℝ)/32), ((-8514801:ℝ)/8), ((-95283:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0 * t^e) - ((-69031300055402961:ℝ)/8388608) - ((-67650003444429693:ℝ)/2097152)*t| ≤ ((140729161706314832115963:ℝ)/1024000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((-69031300055402961:ℝ)/8388608), ((-67650003444429693:ℝ)/2097152), ((-27500709650789781:ℝ)/524288), ((-6404713487565615:ℝ)/131072), ((-121406960503215:ℝ)/4096), ((-51080992047369:ℝ)/4096), ((-3847032699237:ℝ)/1024), ((-209919783879:ℝ)/256), ((-16521881985:ℝ)/128), ((-458232705:ℝ)/32), ((-8514801:ℝ)/8), ((-95283:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((2436402545921359872:ℝ)/244140625) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((151064323891:ℝ)/8192) - ((78895942437:ℝ)/2048)*t| ≤ ((366071587462999:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((24:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82080:ℝ), (-967680:ℝ), (3257600:ℝ), (-4474880:ℝ), (2908160:ℝ), (-786432:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_02 q| ≤ ((59083788087096646828032:ℝ)/244140625) := by
    rw [centralNum13_02_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((24:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (87660:ℝ), (-702180:ℝ), ((7421435:ℝ)/4), ((-10854125:ℝ)/4), ((2828125:ℝ)/2), (-187500:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_02 q| ≤ ((36111607468772032512:ℝ)/390625) := by
    rw [centralNum23_02_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((77208723412503754641362627217:ℝ)/50000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece20_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece20_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((-69031300055402961:ℝ)/8388608) + ((151064323891:ℝ)/8192)*(0:ℝ) - ((-4263338068744913:ℝ)/100000000000)) (β := (0:ℝ) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((-67650003444429693:ℝ)/2097152) - 3*((-69031300055402961:ℝ)/8388608)) + ((78895942437:ℝ)/2048)*(0:ℝ) - ((-49026316964314259:ℝ)/1250000000000)) ht
  have hW : pieceW q pieceX_20 0 2 = centralNum11_02 q + 8*(Real.exp (-(3*((19:ℝ)/4)))*Real.exp (-3*t))*centralNum12_02 q + 18*Real.exp (-8*q)*centralNum13_02 q + 72*Real.exp (-11*q)*centralNum23_02 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_02, pieceX_20, sym4_02, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((1562335838978874562890869481803580756028036496651665133109:ℝ)/99353115996689131203074771255863950687736168255404176797525000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((-69031300055402961:ℝ)/8388608) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((-67650003444429693:ℝ)/2097152) - 3*((-69031300055402961:ℝ)/8388608))*t) + (((151064323891:ℝ)/8192) + ((78895942437:ℝ)/2048)*t)*(0:ℝ) - (((-4263338068744913:ℝ)/100000000000) + t * ((-49026316964314259:ℝ)/1250000000000)) = ((0:ℝ) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((-69031300055402961:ℝ)/8388608) + ((151064323891:ℝ)/8192)*(0:ℝ) - ((-4263338068744913:ℝ)/100000000000)) + t*((0:ℝ) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((-67650003444429693:ℝ)/2097152) - 3*((-69031300055402961:ℝ)/8388608)) + ((78895942437:ℝ)/2048)*(0:ℝ) - ((-49026316964314259:ℝ)/1250000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece20_e03 {q : ℝ} (h0 : ((47:ℝ)/10) ≤ q) (h1 : q ≤ ((24:ℝ)/5)) :
    |pieceW q pieceX_20 0 3 - (((998563213874764459:ℝ)/10000000000000) + (q - ((19:ℝ)/4)) * ((-828339741243509127:ℝ)/10000000000000))| ≤ ((460200736841276641:ℝ)/100000000000000) := by
  set t := q - ((19:ℝ)/4) with htd
  have hq : q = ((19:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece20_L3 piece20_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((19:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_03 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_03; ring
  have h12 : centralNum12_03 q = ∑ e ∈ Finset.range 14, ([((9054404039433551481:ℝ)/469762048), ((1228268615108855571:ℝ)/29360128), ((115624468417222773:ℝ)/3670016), ((3530628212334453:ℝ)/3670016), ((-29510905243760415:ℝ)/1835008), ((-3282823553021451:ℝ)/229376), ((-99887039922861:ℝ)/14336), ((-16117431898887:ℝ)/7168), ((-3644530021557:ℝ)/7168), ((-2283348015:ℝ)/28), ((-63954036:ℝ)/7), ((-38214423:ℝ)/56), ((-857061:ℝ)/28), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_03; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((9054404039433551481:ℝ)/469762048), ((1228268615108855571:ℝ)/29360128), ((115624468417222773:ℝ)/3670016), ((3530628212334453:ℝ)/3670016), ((-29510905243760415:ℝ)/1835008), ((-3282823553021451:ℝ)/229376), ((-99887039922861:ℝ)/14336), ((-16117431898887:ℝ)/7168), ((-3644530021557:ℝ)/7168), ((-2283348015:ℝ)/28), ((-63954036:ℝ)/7), ((-38214423:ℝ)/56), ((-857061:ℝ)/28), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((9054404039433551481:ℝ)/469762048), ((1228268615108855571:ℝ)/29360128), ((115624468417222773:ℝ)/3670016), ((3530628212334453:ℝ)/3670016), ((-29510905243760415:ℝ)/1835008), ((-3282823553021451:ℝ)/229376), ((-99887039922861:ℝ)/14336), ((-16117431898887:ℝ)/7168), ((-3644530021557:ℝ)/7168), ((-2283348015:ℝ)/28), ((-63954036:ℝ)/7), ((-38214423:ℝ)/56), ((-857061:ℝ)/28), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((9054404039433551481:ℝ)/469762048), ((1228268615108855571:ℝ)/29360128), ((115624468417222773:ℝ)/3670016), ((3530628212334453:ℝ)/3670016), ((-29510905243760415:ℝ)/1835008), ((-3282823553021451:ℝ)/229376), ((-99887039922861:ℝ)/14336), ((-16117431898887:ℝ)/7168), ((-3644530021557:ℝ)/7168), ((-2283348015:ℝ)/28), ((-63954036:ℝ)/7), ((-38214423:ℝ)/56), ((-857061:ℝ)/28), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((9054404039433551481:ℝ)/469762048) - ((1228268615108855571:ℝ)/29360128)*t| ≤ ((45295032198675269811248829:ℝ)/573440000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((9054404039433551481:ℝ)/469762048), ((1228268615108855571:ℝ)/29360128), ((115624468417222773:ℝ)/3670016), ((3530628212334453:ℝ)/3670016), ((-29510905243760415:ℝ)/1835008), ((-3282823553021451:ℝ)/229376), ((-99887039922861:ℝ)/14336), ((-16117431898887:ℝ)/7168), ((-3644530021557:ℝ)/7168), ((-2283348015:ℝ)/28), ((-63954036:ℝ)/7), ((-38214423:ℝ)/56), ((-857061:ℝ)/28), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((6148757703795038280535507227:ℝ)/286720000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((151064323891:ℝ)/8192) - ((78895942437:ℝ)/2048)*t| ≤ ((366071587462999:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((24:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-812160:ℝ), (8985600:ℝ), (-32225280:ℝ), (52019200:ℝ), ((-305233920:ℝ)/7), ((135528448:ℝ)/7), ((-25165824:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_03 q| ≤ ((61697418465887180046729216:ℝ)/8544921875) := by
    rw [centralNum13_03_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((24:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-833220:ℝ), (6469740:ℝ), ((-68603955:ℝ)/4), ((104396875:ℝ)/4), ((-1001334375:ℝ)/56), ((125828125:ℝ)/28), ((-2343750:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_03 q| ≤ ((4551082986284884426752:ℝ)/2734375) := by
    rw [centralNum23_03_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((77208723412503754641362627217:ℝ)/50000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece20_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece20_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((9054404039433551481:ℝ)/469762048) + ((151064323891:ℝ)/8192)*(0:ℝ) - ((998563213874764459:ℝ)/10000000000000)) (β := (0:ℝ) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((1228268615108855571:ℝ)/29360128) - 3*((9054404039433551481:ℝ)/469762048)) + ((78895942437:ℝ)/2048)*(0:ℝ) - ((-828339741243509127:ℝ)/10000000000000)) ht
  have hW : pieceW q pieceX_20 0 3 = centralNum11_03 q + 8*(Real.exp (-(3*((19:ℝ)/4)))*Real.exp (-3*t))*centralNum12_03 q + 18*Real.exp (-8*q)*centralNum13_03 q + 72*Real.exp (-11*q)*centralNum23_03 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_03, pieceX_20, sym4_03, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((268596177652631015228813345693973209027892032262273242501249:ℝ)/5563774495814591347372187190328381238513225422302633900661400000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((9054404039433551481:ℝ)/469762048) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((1228268615108855571:ℝ)/29360128) - 3*((9054404039433551481:ℝ)/469762048))*t) + (((151064323891:ℝ)/8192) + ((78895942437:ℝ)/2048)*t)*(0:ℝ) - (((998563213874764459:ℝ)/10000000000000) + t * ((-828339741243509127:ℝ)/10000000000000)) = ((0:ℝ) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((9054404039433551481:ℝ)/469762048) + ((151064323891:ℝ)/8192)*(0:ℝ) - ((998563213874764459:ℝ)/10000000000000)) + t*((0:ℝ) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((1228268615108855571:ℝ)/29360128) - 3*((9054404039433551481:ℝ)/469762048)) + ((78895942437:ℝ)/2048)*(0:ℝ) - ((-828339741243509127:ℝ)/10000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece20_e11 {q : ℝ} (h0 : ((47:ℝ)/10) ≤ q) (h1 : q ≤ ((24:ℝ)/5)) :
    |pieceW q pieceX_20 1 1 - (((152307489150033389:ℝ)/10000000000) + (q - ((19:ℝ)/4)) * ((294126705808128273:ℝ)/10000000000))| ≤ ((676516298106621591:ℝ)/10000000000000) := by
  set t := q - ((19:ℝ)/4) with htd
  have hq : q = ((19:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece20_L3 piece20_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((19:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_11 q = ∑ e ∈ Finset.range 10, ([((23099527571:ℝ)/1536), ((29755281683:ℝ)/1024), ((1617935215:ℝ)/64), ((207848277:ℝ)/16), ((17363017:ℝ)/4), ((1953637:ℝ)/2), (147812:ℝ), (14480:ℝ), (832:ℝ), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_11; ring
  have h12 : centralNum12_11 q = ∑ e ∈ Finset.range 13, ([((-13177539647767393:ℝ)/6291456), ((-10275011300300207:ℝ)/524288), ((-5501459382001735:ℝ)/131072), ((-1480226461048293:ℝ)/32768), ((-30751681142105:ℝ)/1024), ((-13804257982675:ℝ)/1024), ((-1091922510679:ℝ)/256), ((-61953787789:ℝ)/64), ((-5035426267:ℝ)/32), ((-430521745:ℝ)/24), ((-2729979:ℝ)/2), (-62370:ℝ), (-1296:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_11; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((23099527571:ℝ)/1536), ((29755281683:ℝ)/1024), ((1617935215:ℝ)/64), ((207848277:ℝ)/16), ((17363017:ℝ)/4), ((1953637:ℝ)/2), (147812:ℝ), (14480:ℝ), (832:ℝ), ((64:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-13177539647767393:ℝ)/6291456), ((-10275011300300207:ℝ)/524288), ((-5501459382001735:ℝ)/131072), ((-1480226461048293:ℝ)/32768), ((-30751681142105:ℝ)/1024), ((-13804257982675:ℝ)/1024), ((-1091922510679:ℝ)/256), ((-61953787789:ℝ)/64), ((-5035426267:ℝ)/32), ((-430521745:ℝ)/24), ((-2729979:ℝ)/2), (-62370:ℝ), (-1296:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((-13177539647767393:ℝ)/6291456), ((-10275011300300207:ℝ)/524288), ((-5501459382001735:ℝ)/131072), ((-1480226461048293:ℝ)/32768), ((-30751681142105:ℝ)/1024), ((-13804257982675:ℝ)/1024), ((-1091922510679:ℝ)/256), ((-61953787789:ℝ)/64), ((-5035426267:ℝ)/32), ((-430521745:ℝ)/24), ((-2729979:ℝ)/2), (-62370:ℝ), (-1296:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((23099527571:ℝ)/1536), ((29755281683:ℝ)/1024), ((1617935215:ℝ)/64), ((207848277:ℝ)/16), ((17363017:ℝ)/4), ((1953637:ℝ)/2), (147812:ℝ), (14480:ℝ), (832:ℝ), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((23099527571:ℝ)/1536) + ((29755281683:ℝ)/1024)*t)| ≤ ((1556444310978031:ℝ)/24000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((-13177539647767393:ℝ)/6291456), ((-10275011300300207:ℝ)/524288), ((-5501459382001735:ℝ)/131072), ((-1480226461048293:ℝ)/32768), ((-30751681142105:ℝ)/1024), ((-13804257982675:ℝ)/1024), ((-1091922510679:ℝ)/256), ((-61953787789:ℝ)/64), ((-5035426267:ℝ)/32), ((-430521745:ℝ)/24), ((-2729979:ℝ)/2), (-62370:ℝ), (-1296:ℝ)] : List ℝ).getD e 0 * t^e) - ((-13177539647767393:ℝ)/6291456) - ((-10275011300300207:ℝ)/524288)*t| ≤ ((85071820523893938520843:ℝ)/768000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((-13177539647767393:ℝ)/6291456), ((-10275011300300207:ℝ)/524288), ((-5501459382001735:ℝ)/131072), ((-1480226461048293:ℝ)/32768), ((-30751681142105:ℝ)/1024), ((-13804257982675:ℝ)/1024), ((-1091922510679:ℝ)/256), ((-61953787789:ℝ)/64), ((-5035426267:ℝ)/32), ((-430521745:ℝ)/24), ((-2729979:ℝ)/2), (-62370:ℝ), (-1296:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((777633192548499456:ℝ)/244140625) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((151064323891:ℝ)/8192) - ((78895942437:ℝ)/2048)*t| ≤ ((366071587462999:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((24:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-3444:ℝ), (162624:ℝ), (-1531216:ℝ), (4800960:ℝ), (-6350848:ℝ), ((12025856:ℝ)/3), (-1048576:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_11 q| ≤ ((80553273735115850121216:ℝ)/244140625) := by
    rw [centralNum13_11_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((24:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-4074:ℝ), (159906:ℝ), (-1104799:ℝ), (2801499:ℝ), (-3931375:ℝ), ((5896250:ℝ)/3), (-250000:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_11 q| ≤ ((250550196540075933696:ℝ)/1953125) := by
    rw [centralNum23_11_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((77208723412503754641362627217:ℝ)/50000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece20_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece20_E11 h0) m23'
  have c5 := scaled_affine (X := ((11:ℝ)/1000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1))| ≤ ((312772425142242168012800000:ℝ)/31930960869914636620763316254349) := by
    rw [abs_neg, tailWeight_1, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((24:ℝ)/5)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((24:ℝ)/5)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece20_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((4814744136400:ℝ)/531441)) ≤ ((24:ℝ)/5)^6*(8000*(2*((24:ℝ)/5)-3)^2*(1/((394209393455736254577324892029:ℝ)/100000000))*((4814744136400:ℝ)/531441)) := by
          gcongr
      _ ≤ ((312772425142242168012800000:ℝ)/31930960869914636620763316254349) := by norm_num
  have c7 := affine_round (α := ((23099527571:ℝ)/1536) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((-13177539647767393:ℝ)/6291456) + ((151064323891:ℝ)/8192)*((11:ℝ)/1000) - ((152307489150033389:ℝ)/10000000000)) (β := ((29755281683:ℝ)/1024) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((-10275011300300207:ℝ)/524288) - 3*((-13177539647767393:ℝ)/6291456)) + ((78895942437:ℝ)/2048)*((11:ℝ)/1000) - ((294126705808128273:ℝ)/10000000000)) ht
  have hW : pieceW q pieceX_20 1 1 = centralNum11_11 q + 8*(Real.exp (-(3*((19:ℝ)/4)))*Real.exp (-3*t))*centralNum12_11 q + 18*Real.exp (-8*q)*centralNum13_11 q + 72*Real.exp (-11*q)*centralNum23_11 q + 8*q^7*(2*q-3)^2*((11:ℝ)/1000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1)) := by
    rw [pieceW_11, pieceX_20, sym4_11, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((1527888514867306474554134708196826940589025212002058309197729:ℝ)/57227394814092939572971068243377635596136032915112805835374400000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((23099527571:ℝ)/1536) + ((29755281683:ℝ)/1024)*t) + (8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((-13177539647767393:ℝ)/6291456) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((-10275011300300207:ℝ)/524288) - 3*((-13177539647767393:ℝ)/6291456))*t) + (((151064323891:ℝ)/8192) + ((78895942437:ℝ)/2048)*t)*((11:ℝ)/1000) - (((152307489150033389:ℝ)/10000000000) + t * ((294126705808128273:ℝ)/10000000000)) = (((23099527571:ℝ)/1536) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((-13177539647767393:ℝ)/6291456) + ((151064323891:ℝ)/8192)*((11:ℝ)/1000) - ((152307489150033389:ℝ)/10000000000)) + t*(((29755281683:ℝ)/1024) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((-10275011300300207:ℝ)/524288) - 3*((-13177539647767393:ℝ)/6291456)) + ((78895942437:ℝ)/2048)*((11:ℝ)/1000) - ((294126705808128273:ℝ)/10000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece20_e12 {q : ℝ} (h0 : ((47:ℝ)/10) ≤ q) (h1 : q ≤ ((24:ℝ)/5)) :
    |pieceW q pieceX_20 1 2 - (((-54332828275381757:ℝ)/50000000000) + (q - ((19:ℝ)/4)) * ((-86531794908020757:ℝ)/50000000000))| ≤ ((431702364701933:ℝ)/25000000000) := by
  set t := q - ((19:ℝ)/4) with htd
  have hq : q = ((19:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece20_L3 piece20_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((19:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_12 q = ∑ e ∈ Finset.range 9, ([((-33637804915:ℝ)/24576), ((-2538001475:ℝ)/1536), ((-253474345:ℝ)/384), ((-1063145:ℝ)/96), ((3637075:ℝ)/48), ((164635:ℝ)/6), ((13750:ℝ)/3), ((1160:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_12; ring
  have h12 : centralNum12_12 q = ∑ e ∈ Finset.range 14, ([((10961329180479321913:ℝ)/201326592), ((1865097429668373347:ℝ)/12582912), ((264695510626506221:ℝ)/1572864), ((154830418253578453:ℝ)/1572864), ((19234026605336545:ℝ)/786432), ((-596736058786763:ℝ)/98304), ((-47334873198397:ℝ)/6144), ((-10190010152359:ℝ)/3072), ((-2683798931957:ℝ)/3072), ((-309300505:ℝ)/2), (-18604011:ℝ), ((-11743677:ℝ)/8), ((-275319:ℝ)/4), (-1458:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_12; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-33637804915:ℝ)/24576), ((-2538001475:ℝ)/1536), ((-253474345:ℝ)/384), ((-1063145:ℝ)/96), ((3637075:ℝ)/48), ((164635:ℝ)/6), ((13750:ℝ)/3), ((1160:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((10961329180479321913:ℝ)/201326592), ((1865097429668373347:ℝ)/12582912), ((264695510626506221:ℝ)/1572864), ((154830418253578453:ℝ)/1572864), ((19234026605336545:ℝ)/786432), ((-596736058786763:ℝ)/98304), ((-47334873198397:ℝ)/6144), ((-10190010152359:ℝ)/3072), ((-2683798931957:ℝ)/3072), ((-309300505:ℝ)/2), (-18604011:ℝ), ((-11743677:ℝ)/8), ((-275319:ℝ)/4), (-1458:ℝ)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((10961329180479321913:ℝ)/201326592), ((1865097429668373347:ℝ)/12582912), ((264695510626506221:ℝ)/1572864), ((154830418253578453:ℝ)/1572864), ((19234026605336545:ℝ)/786432), ((-596736058786763:ℝ)/98304), ((-47334873198397:ℝ)/6144), ((-10190010152359:ℝ)/3072), ((-2683798931957:ℝ)/3072), ((-309300505:ℝ)/2), (-18604011:ℝ), ((-11743677:ℝ)/8), ((-275319:ℝ)/4), (-1458:ℝ)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((-33637804915:ℝ)/24576), ((-2538001475:ℝ)/1536), ((-253474345:ℝ)/384), ((-1063145:ℝ)/96), ((3637075:ℝ)/48), ((164635:ℝ)/6), ((13750:ℝ)/3), ((1160:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((-33637804915:ℝ)/24576) + ((-2538001475:ℝ)/1536)*t)| ≤ ((1057337681777:ℝ)/640000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((10961329180479321913:ℝ)/201326592), ((1865097429668373347:ℝ)/12582912), ((264695510626506221:ℝ)/1572864), ((154830418253578453:ℝ)/1572864), ((19234026605336545:ℝ)/786432), ((-596736058786763:ℝ)/98304), ((-47334873198397:ℝ)/6144), ((-10190010152359:ℝ)/3072), ((-2683798931957:ℝ)/3072), ((-309300505:ℝ)/2), (-18604011:ℝ), ((-11743677:ℝ)/8), ((-275319:ℝ)/4), (-1458:ℝ)] : List ℝ).getD e 0 * t^e) - ((10961329180479321913:ℝ)/201326592) - ((1865097429668373347:ℝ)/12582912)*t| ≤ ((106458778332886607402405959:ℝ)/245760000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((10961329180479321913:ℝ)/201326592), ((1865097429668373347:ℝ)/12582912), ((264695510626506221:ℝ)/1572864), ((154830418253578453:ℝ)/1572864), ((19234026605336545:ℝ)/786432), ((-596736058786763:ℝ)/98304), ((-47334873198397:ℝ)/6144), ((-10190010152359:ℝ)/3072), ((-2683798931957:ℝ)/3072), ((-309300505:ℝ)/2), (-18604011:ℝ), ((-11743677:ℝ)/8), ((-275319:ℝ)/4), (-1458:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((239193308933721948611908931:ℝ)/3840000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((151064323891:ℝ)/8192) - ((78895942437:ℝ)/2048)*t| ≤ ((366071587462999:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((24:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (122790:ℝ), (-3586680:ℝ), (28529720:ℝ), (-90761600:ℝ), (137804800:ℝ), ((-332136448:ℝ)/3), ((141819904:ℝ)/3), (-8388608:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_12 q| ≤ ((21448511909977660293906432:ℝ)/1220703125) := by
    rw [centralNum13_12_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((24:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (132555:ℝ), (-3252375:ℝ), ((39743695:ℝ)/2), ((-197111615:ℝ)/4), ((281947375:ℝ)/4), ((-1100234375:ℝ)/24), ((131828125:ℝ)/12), (-781250:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_12 q| ≤ ((1626175242301757718528:ℝ)/390625) := by
    rw [centralNum23_12_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((77208723412503754641362627217:ℝ)/50000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece20_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece20_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-33637804915:ℝ)/24576) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((10961329180479321913:ℝ)/201326592) + ((151064323891:ℝ)/8192)*(0:ℝ) - ((-54332828275381757:ℝ)/50000000000)) (β := ((-2538001475:ℝ)/1536) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((1865097429668373347:ℝ)/12582912) - 3*((10961329180479321913:ℝ)/201326592)) + ((78895942437:ℝ)/2048)*(0:ℝ) - ((-86531794908020757:ℝ)/50000000000)) ht
  have hW : pieceW q pieceX_20 1 2 = centralNum11_12 q + 8*(Real.exp (-(3*((19:ℝ)/4)))*Real.exp (-3*t))*centralNum12_12 q + 18*Real.exp (-8*q)*centralNum13_12 q + 72*Real.exp (-11*q)*centralNum23_12 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_12, pieceX_20, sym4_12, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((235352584065395873310812553102071123948499722805883127812079:ℝ)/71534243517616174466213835304222044495170041143891007294218000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-33637804915:ℝ)/24576) + ((-2538001475:ℝ)/1536)*t) + (8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((10961329180479321913:ℝ)/201326592) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((1865097429668373347:ℝ)/12582912) - 3*((10961329180479321913:ℝ)/201326592))*t) + (((151064323891:ℝ)/8192) + ((78895942437:ℝ)/2048)*t)*(0:ℝ) - (((-54332828275381757:ℝ)/50000000000) + t * ((-86531794908020757:ℝ)/50000000000)) = (((-33637804915:ℝ)/24576) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((10961329180479321913:ℝ)/201326592) + ((151064323891:ℝ)/8192)*(0:ℝ) - ((-54332828275381757:ℝ)/50000000000)) + t*(((-2538001475:ℝ)/1536) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((1865097429668373347:ℝ)/12582912) - 3*((10961329180479321913:ℝ)/201326592)) + ((78895942437:ℝ)/2048)*(0:ℝ) - ((-86531794908020757:ℝ)/50000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece20_e13 {q : ℝ} (h0 : ((47:ℝ)/10) ≤ q) (h1 : q ≤ ((24:ℝ)/5)) :
    |pieceW q pieceX_20 1 3 - (((-910476245963108891:ℝ)/1000000000000) + (q - ((19:ℝ)/4)) * ((-278031251937723577:ℝ)/1000000000000))| ≤ ((953961405043451083:ℝ)/100000000000000) := by
  set t := q - ((19:ℝ)/4) with htd
  have hq : q = ((19:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece20_L3 piece20_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((19:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_13 q = ∑ e ∈ Finset.range 7, ([((-705688215:ℝ)/1024), ((-111424455:ℝ)/128), ((-29322225:ℝ)/64), ((-514425:ℝ)/4), ((-81225:ℝ)/4), (-1710:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_13; ring
  have h12 : centralNum12_13 q = ∑ e ∈ Finset.range 15, ([((-160549835929968052635:ℝ)/3758096384), ((-1852618658150497407:ℝ)/134217728), ((8149640721872021511:ℝ)/58720256), ((7061377115818915221:ℝ)/29360128), ((2878090528043923323:ℝ)/14680064), ((349021674051244725:ℝ)/3670016), ((12983555271499179:ℝ)/458752), ((250650359919903:ℝ)/57344), ((-1397568878067:ℝ)/8192), ((-3760766258751:ℝ)/14336), ((-15017656365:ℝ)/224), ((-4300455267:ℝ)/448), ((-188037531:ℝ)/224), ((-2359773:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_13; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-705688215:ℝ)/1024), ((-111424455:ℝ)/128), ((-29322225:ℝ)/64), ((-514425:ℝ)/4), ((-81225:ℝ)/4), (-1710:ℝ), (-60:ℝ)] : List ℝ).getD e 0) 5 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-160549835929968052635:ℝ)/3758096384), ((-1852618658150497407:ℝ)/134217728), ((8149640721872021511:ℝ)/58720256), ((7061377115818915221:ℝ)/29360128), ((2878090528043923323:ℝ)/14680064), ((349021674051244725:ℝ)/3670016), ((12983555271499179:ℝ)/458752), ((250650359919903:ℝ)/57344), ((-1397568878067:ℝ)/8192), ((-3760766258751:ℝ)/14336), ((-15017656365:ℝ)/224), ((-4300455267:ℝ)/448), ((-188037531:ℝ)/224), ((-2359773:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-160549835929968052635:ℝ)/3758096384), ((-1852618658150497407:ℝ)/134217728), ((8149640721872021511:ℝ)/58720256), ((7061377115818915221:ℝ)/29360128), ((2878090528043923323:ℝ)/14680064), ((349021674051244725:ℝ)/3670016), ((12983555271499179:ℝ)/458752), ((250650359919903:ℝ)/57344), ((-1397568878067:ℝ)/8192), ((-3760766258751:ℝ)/14336), ((-15017656365:ℝ)/224), ((-4300455267:ℝ)/448), ((-188037531:ℝ)/224), ((-2359773:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 7, ([((-705688215:ℝ)/1024), ((-111424455:ℝ)/128), ((-29322225:ℝ)/64), ((-514425:ℝ)/4), ((-81225:ℝ)/4), (-1710:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e) - (((-705688215:ℝ)/1024) + ((-111424455:ℝ)/128)*t)| ≤ ((3717128463:ℝ)/3200000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-160549835929968052635:ℝ)/3758096384), ((-1852618658150497407:ℝ)/134217728), ((8149640721872021511:ℝ)/58720256), ((7061377115818915221:ℝ)/29360128), ((2878090528043923323:ℝ)/14680064), ((349021674051244725:ℝ)/3670016), ((12983555271499179:ℝ)/458752), ((250650359919903:ℝ)/57344), ((-1397568878067:ℝ)/8192), ((-3760766258751:ℝ)/14336), ((-15017656365:ℝ)/224), ((-4300455267:ℝ)/448), ((-188037531:ℝ)/224), ((-2359773:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((-160549835929968052635:ℝ)/3758096384) - ((-1852618658150497407:ℝ)/134217728)*t| ≤ ((1084627423010681662891509939:ℝ)/2867200000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-160549835929968052635:ℝ)/3758096384), ((-1852618658150497407:ℝ)/134217728), ((8149640721872021511:ℝ)/58720256), ((7061377115818915221:ℝ)/29360128), ((2878090528043923323:ℝ)/14680064), ((349021674051244725:ℝ)/3670016), ((12983555271499179:ℝ)/458752), ((250650359919903:ℝ)/57344), ((-1397568878067:ℝ)/8192), ((-3760766258751:ℝ)/14336), ((-15017656365:ℝ)/224), ((-4300455267:ℝ)/448), ((-188037531:ℝ)/224), ((-2359773:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((17936177379855271440122894277:ℝ)/409600000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((151064323891:ℝ)/8192) - ((78895942437:ℝ)/2048)*t| ≤ ((366071587462999:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((24:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2325540:ℝ), (52589280:ℝ), (-375655200:ℝ), (1192958720:ℝ), (-1965096960:ℝ), ((12857851904:ℝ)/7), ((-21171273728:ℝ)/21), ((914358272:ℝ)/3), ((-268435456:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_13 q| ≤ ((24504257659317431962268860416:ℝ)/42724609375) := by
    rw [centralNum13_13_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((24:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2399070:ℝ), (45666930:ℝ), (-251781675:ℝ), ((2452738385:ℝ)/4), ((-14104310625:ℝ)/16), ((74345740625:ℝ)/112), ((-74899765625:ℝ)/336), ((5161328125:ℝ)/168), ((-9765625:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_13 q| ≤ ((239328213212546462121984:ℝ)/2734375) := by
    rw [centralNum23_13_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((77208723412503754641362627217:ℝ)/50000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece20_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece20_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-705688215:ℝ)/1024) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((-160549835929968052635:ℝ)/3758096384) + ((151064323891:ℝ)/8192)*(0:ℝ) - ((-910476245963108891:ℝ)/1000000000000)) (β := ((-111424455:ℝ)/128) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((-1852618658150497407:ℝ)/134217728) - 3*((-160549835929968052635:ℝ)/3758096384)) + ((78895942437:ℝ)/2048)*(0:ℝ) - ((-278031251937723577:ℝ)/1000000000000)) ht
  have hW : pieceW q pieceX_20 1 3 = centralNum11_13 q + 8*(Real.exp (-(3*((19:ℝ)/4)))*Real.exp (-3*t))*centralNum12_13 q + 18*Real.exp (-8*q)*centralNum13_13 q + 72*Real.exp (-11*q)*centralNum23_13 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_13, pieceX_20, sym4_13, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((131727791254761417312034407602195045119102211979031646669879:ℝ)/556377449581459134737218719032838123851322542230263390066140000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-705688215:ℝ)/1024) + ((-111424455:ℝ)/128)*t) + (8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((-160549835929968052635:ℝ)/3758096384) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((-1852618658150497407:ℝ)/134217728) - 3*((-160549835929968052635:ℝ)/3758096384))*t) + (((151064323891:ℝ)/8192) + ((78895942437:ℝ)/2048)*t)*(0:ℝ) - (((-910476245963108891:ℝ)/1000000000000) + t * ((-278031251937723577:ℝ)/1000000000000)) = (((-705688215:ℝ)/1024) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((-160549835929968052635:ℝ)/3758096384) + ((151064323891:ℝ)/8192)*(0:ℝ) - ((-910476245963108891:ℝ)/1000000000000)) + t*(((-111424455:ℝ)/128) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((-1852618658150497407:ℝ)/134217728) - 3*((-160549835929968052635:ℝ)/3758096384)) + ((78895942437:ℝ)/2048)*(0:ℝ) - ((-278031251937723577:ℝ)/1000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece20_e22 {q : ℝ} (h0 : ((47:ℝ)/10) ≤ q) (h1 : q ≤ ((24:ℝ)/5)) :
    |pieceW q pieceX_20 2 2 - (((66187844150562971:ℝ)/5000000000) + (q - ((19:ℝ)/4)) * ((290126060217775353:ℝ)/10000000000))| ≤ ((220259201155980897:ℝ)/2500000000000) := by
  set t := q - ((19:ℝ)/4) with htd
  have hq : q = ((19:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece20_L3 piece20_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((19:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_22 q = ∑ e ∈ Finset.range 10, ([((671505668305:ℝ)/49152), ((112792173895:ℝ)/4096), ((19025048365:ℝ)/768), ((2515373995:ℝ)/192), ((144009645:ℝ)/32), ((25027735:ℝ)/24), ((489185:ℝ)/3), (16580:ℝ), ((2980:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_22; ring
  have h12 : centralNum12_22 q = ∑ e ∈ Finset.range 15, ([((-779812574629100070145:ℝ)/6442450944), ((-85968135558944166441:ℝ)/536870912), ((7469820546185377505:ℝ)/100663296), ((15492118140994830727:ℝ)/50331648), ((2537476609615913243:ℝ)/8388608), ((1025368517295949375:ℝ)/6291456), ((42153948133469873:ℝ)/786432), ((328150652797175:ℝ)/32768), ((39396295451297:ℝ)/98304), ((-8022877955213:ℝ)/24576), ((-201115515:ℝ)/2), ((-3947997483:ℝ)/256), ((-179489115:ℝ)/128), ((-2313117:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_22; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((671505668305:ℝ)/49152), ((112792173895:ℝ)/4096), ((19025048365:ℝ)/768), ((2515373995:ℝ)/192), ((144009645:ℝ)/32), ((25027735:ℝ)/24), ((489185:ℝ)/3), (16580:ℝ), ((2980:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-779812574629100070145:ℝ)/6442450944), ((-85968135558944166441:ℝ)/536870912), ((7469820546185377505:ℝ)/100663296), ((15492118140994830727:ℝ)/50331648), ((2537476609615913243:ℝ)/8388608), ((1025368517295949375:ℝ)/6291456), ((42153948133469873:ℝ)/786432), ((328150652797175:ℝ)/32768), ((39396295451297:ℝ)/98304), ((-8022877955213:ℝ)/24576), ((-201115515:ℝ)/2), ((-3947997483:ℝ)/256), ((-179489115:ℝ)/128), ((-2313117:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-779812574629100070145:ℝ)/6442450944), ((-85968135558944166441:ℝ)/536870912), ((7469820546185377505:ℝ)/100663296), ((15492118140994830727:ℝ)/50331648), ((2537476609615913243:ℝ)/8388608), ((1025368517295949375:ℝ)/6291456), ((42153948133469873:ℝ)/786432), ((328150652797175:ℝ)/32768), ((39396295451297:ℝ)/98304), ((-8022877955213:ℝ)/24576), ((-201115515:ℝ)/2), ((-3947997483:ℝ)/256), ((-179489115:ℝ)/128), ((-2313117:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((671505668305:ℝ)/49152), ((112792173895:ℝ)/4096), ((19025048365:ℝ)/768), ((2515373995:ℝ)/192), ((144009645:ℝ)/32), ((25027735:ℝ)/24), ((489185:ℝ)/3), (16580:ℝ), ((2980:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((671505668305:ℝ)/49152) + ((112792173895:ℝ)/4096)*t)| ≤ ((610527020010223:ℝ)/9600000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-779812574629100070145:ℝ)/6442450944), ((-85968135558944166441:ℝ)/536870912), ((7469820546185377505:ℝ)/100663296), ((15492118140994830727:ℝ)/50331648), ((2537476609615913243:ℝ)/8388608), ((1025368517295949375:ℝ)/6291456), ((42153948133469873:ℝ)/786432), ((328150652797175:ℝ)/32768), ((39396295451297:ℝ)/98304), ((-8022877955213:ℝ)/24576), ((-201115515:ℝ)/2), ((-3947997483:ℝ)/256), ((-179489115:ℝ)/128), ((-2313117:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e) - ((-779812574629100070145:ℝ)/6442450944) - ((-85968135558944166441:ℝ)/536870912)*t| ≤ ((1480670806387935502388991791:ℝ)/6553600000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-779812574629100070145:ℝ)/6442450944), ((-85968135558944166441:ℝ)/536870912), ((7469820546185377505:ℝ)/100663296), ((15492118140994830727:ℝ)/50331648), ((2537476609615913243:ℝ)/8388608), ((1025368517295949375:ℝ)/6291456), ((42153948133469873:ℝ)/786432), ((328150652797175:ℝ)/32768), ((39396295451297:ℝ)/98304), ((-8022877955213:ℝ)/24576), ((-201115515:ℝ)/2), ((-3947997483:ℝ)/256), ((-179489115:ℝ)/128), ((-2313117:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e)| ≤ ((2541653486920099383929041975373:ℝ)/19660800000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((151064323891:ℝ)/8192) - ((78895942437:ℝ)/2048)*t| ≤ ((366071587462999:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((24:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82125:ℝ), (-6663750:ℝ), (115666200:ℝ), (-750437000:ℝ), (2277262000:ℝ), (-3656824320:ℝ), (3359621120:ℝ), (-1817706496:ℝ), ((1625292800:ℝ)/3), (-67108864:ℝ)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_22 q| ≤ ((6249591729516383690356260864:ℝ)/6103515625) := by
    rw [centralNum13_22_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((24:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((178425:ℝ)/2), ((-13176075:ℝ)/2), ((777815145:ℝ)/8), ((-3968389015:ℝ)/8), ((9393350195:ℝ)/8), ((-26366634375:ℝ)/16), ((77851609375:ℝ)/64), ((-25714921875:ℝ)/64), ((5236328125:ℝ)/96), ((-9765625:ℝ)/4)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_22 q| ≤ ((61728129743824043753472:ℝ)/390625) := by
    rw [centralNum23_22_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((77208723412503754641362627217:ℝ)/50000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece20_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece20_E11 h0) m23'
  have c5 := scaled_affine (X := ((11:ℝ)/1000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2))| ≤ ((166978742042083714924544000000:ℝ)/287378647829231729586869846289141) := by
    rw [abs_neg, tailWeight_2, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((24:ℝ)/5)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((24:ℝ)/5)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece20_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((2570430941234500:ℝ)/4782969)) ≤ ((24:ℝ)/5)^6*(8000*(2*((24:ℝ)/5)-3)^2*(1/((394209393455736254577324892029:ℝ)/100000000))*((2570430941234500:ℝ)/4782969)) := by
          gcongr
      _ ≤ ((166978742042083714924544000000:ℝ)/287378647829231729586869846289141) := by norm_num
  have c7 := affine_round (α := ((671505668305:ℝ)/49152) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((-779812574629100070145:ℝ)/6442450944) + ((151064323891:ℝ)/8192)*((11:ℝ)/1000) - ((66187844150562971:ℝ)/5000000000)) (β := ((112792173895:ℝ)/4096) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((-85968135558944166441:ℝ)/536870912) - 3*((-779812574629100070145:ℝ)/6442450944)) + ((78895942437:ℝ)/2048)*((11:ℝ)/1000) - ((290126060217775353:ℝ)/10000000000)) ht
  have hW : pieceW q pieceX_20 2 2 = centralNum11_22 q + 8*(Real.exp (-(3*((19:ℝ)/4)))*Real.exp (-3*t))*centralNum12_22 q + 18*Real.exp (-8*q)*centralNum13_22 q + 72*Real.exp (-11*q)*centralNum23_22 q + 8*q^7*(2*q-3)^2*((11:ℝ)/1000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2)) := by
    rw [pieceW_22, pieceX_20, sym4_22, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((1675689542695292801285262572114574027744957587098075299673289:ℝ)/57227394814092939572971068243377635596136032915112805835374400000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((671505668305:ℝ)/49152) + ((112792173895:ℝ)/4096)*t) + (8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((-779812574629100070145:ℝ)/6442450944) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((-85968135558944166441:ℝ)/536870912) - 3*((-779812574629100070145:ℝ)/6442450944))*t) + (((151064323891:ℝ)/8192) + ((78895942437:ℝ)/2048)*t)*((11:ℝ)/1000) - (((66187844150562971:ℝ)/5000000000) + t * ((290126060217775353:ℝ)/10000000000)) = (((671505668305:ℝ)/49152) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((-779812574629100070145:ℝ)/6442450944) + ((151064323891:ℝ)/8192)*((11:ℝ)/1000) - ((66187844150562971:ℝ)/5000000000)) + t*(((112792173895:ℝ)/4096) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((-85968135558944166441:ℝ)/536870912) - 3*((-779812574629100070145:ℝ)/6442450944)) + ((78895942437:ℝ)/2048)*((11:ℝ)/1000) - ((290126060217775353:ℝ)/10000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece20_e23 {q : ℝ} (h0 : ((47:ℝ)/10) ≤ q) (h1 : q ≤ ((24:ℝ)/5)) :
    |pieceW q pieceX_20 2 3 - (((8793644584280179:ℝ)/4000000000) + (q - ((19:ℝ)/4)) * ((30946182672445383:ℝ)/12500000000))| ≤ ((117972920069802097:ℝ)/1000000000000) := by
  set t := q - ((19:ℝ)/4) with htd
  have hq : q = ((19:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece20_L3 piece20_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((19:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_23 q = ∑ e ∈ Finset.range 9, ([((11600523815:ℝ)/4096), ((10030155765:ℝ)/2048), ((2022136085:ℝ)/512), ((246146045:ℝ)/128), ((19472625:ℝ)/32), ((1008295:ℝ)/8), ((32935:ℝ)/2), (1230:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_23; ring
  have h12 : centralNum12_23 q = ∑ e ∈ Finset.range 16, ([((-14710954983350104865149:ℝ)/120259084288), ((-12543773271631897357113:ℝ)/15032385536), ((-1731974514911608893995:ℝ)/1073741824), ((-1427296595711561165503:ℝ)/939524096), ((-367886081076377630601:ℝ)/469762048), ((-11062484807216894885:ℝ)/58720256), ((627187849109422247:ℝ)/29360128), ((120676300507022805:ℝ)/3670016), ((21959537996004697:ℝ)/1835008), ((75764956610883:ℝ)/32768), ((23674660319817:ℝ)/114688), ((-154706646573:ℝ)/14336), ((-39136818195:ℝ)/7168), ((-613910583:ℝ)/896), ((-18705411:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_23; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((11600523815:ℝ)/4096), ((10030155765:ℝ)/2048), ((2022136085:ℝ)/512), ((246146045:ℝ)/128), ((19472625:ℝ)/32), ((1008295:ℝ)/8), ((32935:ℝ)/2), (1230:ℝ), (40:ℝ)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-14710954983350104865149:ℝ)/120259084288), ((-12543773271631897357113:ℝ)/15032385536), ((-1731974514911608893995:ℝ)/1073741824), ((-1427296595711561165503:ℝ)/939524096), ((-367886081076377630601:ℝ)/469762048), ((-11062484807216894885:ℝ)/58720256), ((627187849109422247:ℝ)/29360128), ((120676300507022805:ℝ)/3670016), ((21959537996004697:ℝ)/1835008), ((75764956610883:ℝ)/32768), ((23674660319817:ℝ)/114688), ((-154706646573:ℝ)/14336), ((-39136818195:ℝ)/7168), ((-613910583:ℝ)/896), ((-18705411:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 14 ht
  have m12 := abs_poly_le (fun e => ([((-14710954983350104865149:ℝ)/120259084288), ((-12543773271631897357113:ℝ)/15032385536), ((-1731974514911608893995:ℝ)/1073741824), ((-1427296595711561165503:ℝ)/939524096), ((-367886081076377630601:ℝ)/469762048), ((-11062484807216894885:ℝ)/58720256), ((627187849109422247:ℝ)/29360128), ((120676300507022805:ℝ)/3670016), ((21959537996004697:ℝ)/1835008), ((75764956610883:ℝ)/32768), ((23674660319817:ℝ)/114688), ((-154706646573:ℝ)/14336), ((-39136818195:ℝ)/7168), ((-613910583:ℝ)/896), ((-18705411:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 16 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((11600523815:ℝ)/4096), ((10030155765:ℝ)/2048), ((2022136085:ℝ)/512), ((246146045:ℝ)/128), ((19472625:ℝ)/32), ((1008295:ℝ)/8), ((32935:ℝ)/2), (1230:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e) - (((11600523815:ℝ)/4096) + ((10030155765:ℝ)/2048)*t)| ≤ ((6475475994541:ℝ)/640000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 16, ([((-14710954983350104865149:ℝ)/120259084288), ((-12543773271631897357113:ℝ)/15032385536), ((-1731974514911608893995:ℝ)/1073741824), ((-1427296595711561165503:ℝ)/939524096), ((-367886081076377630601:ℝ)/469762048), ((-11062484807216894885:ℝ)/58720256), ((627187849109422247:ℝ)/29360128), ((120676300507022805:ℝ)/3670016), ((21959537996004697:ℝ)/1835008), ((75764956610883:ℝ)/32768), ((23674660319817:ℝ)/114688), ((-154706646573:ℝ)/14336), ((-39136818195:ℝ)/7168), ((-613910583:ℝ)/896), ((-18705411:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e) - ((-14710954983350104865149:ℝ)/120259084288) - ((-12543773271631897357113:ℝ)/15032385536)*t| ≤ ((15514689657981318946326194749303:ℝ)/3670016000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 16, ([((-14710954983350104865149:ℝ)/120259084288), ((-12543773271631897357113:ℝ)/15032385536), ((-1731974514911608893995:ℝ)/1073741824), ((-1427296595711561165503:ℝ)/939524096), ((-367886081076377630601:ℝ)/469762048), ((-11062484807216894885:ℝ)/58720256), ((627187849109422247:ℝ)/29360128), ((120676300507022805:ℝ)/3670016), ((21959537996004697:ℝ)/1835008), ((75764956610883:ℝ)/32768), ((23674660319817:ℝ)/114688), ((-154706646573:ℝ)/14336), ((-39136818195:ℝ)/7168), ((-613910583:ℝ)/896), ((-18705411:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e)| ≤ ((308789819987725763965262096398089:ℝ)/1835008000000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((151064323891:ℝ)/8192) - ((78895942437:ℝ)/2048)*t| ≤ ((366071587462999:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((24:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-7627725:ℝ)/2), (173988600:ℝ), (-2299614450:ℝ), (13088188200:ℝ), (-38221499200:ℝ), (63366115840:ℝ), ((-445610508288:ℝ)/7), ((841540698112:ℝ)/21), ((-326820167680:ℝ)/21), ((10133438464:ℝ)/3), ((-2147483648:ℝ)/7)] : List ℝ).getD e 0) 16 hq1'
  have m13' : |centralNum13_23 q| ≤ ((7762306912395081549605432082432:ℝ)/213623046875) := by
    rw [centralNum13_23_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((24:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-15801525:ℝ)/4), ((655493865:ℝ)/4), ((-7334421225:ℝ)/4), ((16442962485:ℝ)/2), ((-598626108395:ℝ)/32), ((414013307125:ℝ)/16), ((-4611984703125:ℝ)/224), ((399923828125:ℝ)/48), ((-4353201171875:ℝ)/2688), ((189736328125:ℝ)/1344), ((-244140625:ℝ)/56)] : List ℝ).getD e 0) 16 hq1'
  have m23' : |centralNum23_23 q| ≤ ((10404836540614306655870976:ℝ)/2734375) := by
    rw [centralNum23_23_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((77208723412503754641362627217:ℝ)/50000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece20_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece20_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((11600523815:ℝ)/4096) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((-14710954983350104865149:ℝ)/120259084288) + ((151064323891:ℝ)/8192)*(0:ℝ) - ((8793644584280179:ℝ)/4000000000)) (β := ((10030155765:ℝ)/2048) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((-12543773271631897357113:ℝ)/15032385536) - 3*((-14710954983350104865149:ℝ)/120259084288)) + ((78895942437:ℝ)/2048)*(0:ℝ) - ((30946182672445383:ℝ)/12500000000)) ht
  have hW : pieceW q pieceX_20 2 3 = centralNum11_23 q + 8*(Real.exp (-(3*((19:ℝ)/4)))*Real.exp (-3*t))*centralNum12_23 q + 18*Real.exp (-8*q)*centralNum13_23 q + 72*Real.exp (-11*q)*centralNum23_23 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_23, pieceX_20, sym4_23, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((438475058540312568225308407574486675415238271493621234865681:ℝ)/166913234874437740421165615709851437155396762669079017019842000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((11600523815:ℝ)/4096) + ((10030155765:ℝ)/2048)*t) + (8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((-14710954983350104865149:ℝ)/120259084288) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((-12543773271631897357113:ℝ)/15032385536) - 3*((-14710954983350104865149:ℝ)/120259084288))*t) + (((151064323891:ℝ)/8192) + ((78895942437:ℝ)/2048)*t)*(0:ℝ) - (((8793644584280179:ℝ)/4000000000) + t * ((30946182672445383:ℝ)/12500000000)) = (((11600523815:ℝ)/4096) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((-14710954983350104865149:ℝ)/120259084288) + ((151064323891:ℝ)/8192)*(0:ℝ) - ((8793644584280179:ℝ)/4000000000)) + t*(((10030155765:ℝ)/2048) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((-12543773271631897357113:ℝ)/15032385536) - 3*((-14710954983350104865149:ℝ)/120259084288)) + ((78895942437:ℝ)/2048)*(0:ℝ) - ((30946182672445383:ℝ)/12500000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece20_e33 {q : ℝ} (h0 : ((47:ℝ)/10) ≤ q) (h1 : q ≤ ((24:ℝ)/5)) :
    |pieceW q pieceX_20 3 3 - (((20835650067047371:ℝ)/2000000000) + (q - ((19:ℝ)/4)) * ((147193039839859713:ℝ)/10000000000))| ≤ ((78145739826661681:ℝ)/50000000000) := by
  set t := q - ((19:ℝ)/4) with htd
  have hq : q = ((19:ℝ)/4) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece20_L3 piece20_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((19:ℝ)/4))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_33 q = ∑ e ∈ Finset.range 10, ([((274996206545:ℝ)/57344), ((85246292715:ℝ)/7168), ((44383879635:ℝ)/3584), ((933432855:ℝ)/128), ((87113535:ℝ)/32), ((5411415:ℝ)/8), ((225735:ℝ)/2), ((85830:ℝ)/7), ((5520:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_33; ring
  have h12 : centralNum12_33 q = ∑ e ∈ Finset.range 17, ([((1006392979855611261034691:ℝ)/962072674304), ((6064458750894691785225981:ℝ)/1683627180032), ((1937555501711617059589491:ℝ)/420906795008), ((38595582437947239369039:ℝ)/15032385536), ((396593930114371352949:ℝ)/3758096384), ((-707205362460404890065:ℝ)/939524096), ((-119841468021504093567:ℝ)/234881024), ((-9882113992068184701:ℝ)/58720256), ((-2766588936453847191:ℝ)/102760448), ((17002631089418759:ℝ)/25690112), ((1171566750175407:ℝ)/917504), ((61908735900285:ℝ)/229376), ((1376104077063:ℝ)/57344), ((-3040527051:ℝ)/14336), ((-908705061:ℝ)/3584), ((-139887081:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_33; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((274996206545:ℝ)/57344), ((85246292715:ℝ)/7168), ((44383879635:ℝ)/3584), ((933432855:ℝ)/128), ((87113535:ℝ)/32), ((5411415:ℝ)/8), ((225735:ℝ)/2), ((85830:ℝ)/7), ((5520:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((1006392979855611261034691:ℝ)/962072674304), ((6064458750894691785225981:ℝ)/1683627180032), ((1937555501711617059589491:ℝ)/420906795008), ((38595582437947239369039:ℝ)/15032385536), ((396593930114371352949:ℝ)/3758096384), ((-707205362460404890065:ℝ)/939524096), ((-119841468021504093567:ℝ)/234881024), ((-9882113992068184701:ℝ)/58720256), ((-2766588936453847191:ℝ)/102760448), ((17002631089418759:ℝ)/25690112), ((1171566750175407:ℝ)/917504), ((61908735900285:ℝ)/229376), ((1376104077063:ℝ)/57344), ((-3040527051:ℝ)/14336), ((-908705061:ℝ)/3584), ((-139887081:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 15 ht
  have m12 := abs_poly_le (fun e => ([((1006392979855611261034691:ℝ)/962072674304), ((6064458750894691785225981:ℝ)/1683627180032), ((1937555501711617059589491:ℝ)/420906795008), ((38595582437947239369039:ℝ)/15032385536), ((396593930114371352949:ℝ)/3758096384), ((-707205362460404890065:ℝ)/939524096), ((-119841468021504093567:ℝ)/234881024), ((-9882113992068184701:ℝ)/58720256), ((-2766588936453847191:ℝ)/102760448), ((17002631089418759:ℝ)/25690112), ((1171566750175407:ℝ)/917504), ((61908735900285:ℝ)/229376), ((1376104077063:ℝ)/57344), ((-3040527051:ℝ)/14336), ((-908705061:ℝ)/3584), ((-139887081:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 17 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((274996206545:ℝ)/57344), ((85246292715:ℝ)/7168), ((44383879635:ℝ)/3584), ((933432855:ℝ)/128), ((87113535:ℝ)/32), ((5411415:ℝ)/8), ((225735:ℝ)/2), ((85830:ℝ)/7), ((5520:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e) - (((274996206545:ℝ)/57344) + ((85246292715:ℝ)/7168)*t)| ≤ ((714302859422641:ℝ)/22400000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 17, ([((1006392979855611261034691:ℝ)/962072674304), ((6064458750894691785225981:ℝ)/1683627180032), ((1937555501711617059589491:ℝ)/420906795008), ((38595582437947239369039:ℝ)/15032385536), ((396593930114371352949:ℝ)/3758096384), ((-707205362460404890065:ℝ)/939524096), ((-119841468021504093567:ℝ)/234881024), ((-9882113992068184701:ℝ)/58720256), ((-2766588936453847191:ℝ)/102760448), ((17002631089418759:ℝ)/25690112), ((1171566750175407:ℝ)/917504), ((61908735900285:ℝ)/229376), ((1376104077063:ℝ)/57344), ((-3040527051:ℝ)/14336), ((-908705061:ℝ)/3584), ((-139887081:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e) - ((1006392979855611261034691:ℝ)/962072674304) - ((6064458750894691785225981:ℝ)/1683627180032)*t| ≤ ((3039156084385911144092275226519803:ℝ)/256901120000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 17, ([((1006392979855611261034691:ℝ)/962072674304), ((6064458750894691785225981:ℝ)/1683627180032), ((1937555501711617059589491:ℝ)/420906795008), ((38595582437947239369039:ℝ)/15032385536), ((396593930114371352949:ℝ)/3758096384), ((-707205362460404890065:ℝ)/939524096), ((-119841468021504093567:ℝ)/234881024), ((-9882113992068184701:ℝ)/58720256), ((-2766588936453847191:ℝ)/102760448), ((17002631089418759:ℝ)/25690112), ((1171566750175407:ℝ)/917504), ((61908735900285:ℝ)/229376), ((1376104077063:ℝ)/57344), ((-3040527051:ℝ)/14336), ((-908705061:ℝ)/3584), ((-139887081:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e)| ≤ ((636086445802821595259378489662023981:ℝ)/513802240000000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((151064323891:ℝ)/8192), ((78895942437:ℝ)/2048), ((2280487179:ℝ)/64), (19157187:ℝ), ((105580587:ℝ)/16), ((6042057:ℝ)/4), (229824:ℝ), (22416:ℝ), (1272:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((151064323891:ℝ)/8192) - ((78895942437:ℝ)/2048)*t| ≤ ((366071587462999:ℝ)/4000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((24:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-8120475:ℝ)/4), ((464861025:ℝ)/2), (-5906535975:ℝ), ((411904731750:ℝ)/7), ((-2024051769000:ℝ)/7), ((5554394637600:ℝ)/7), (-1314913862656:ℝ), ((9709155336192:ℝ)/7), ((-6724555112448:ℝ)/7), ((1313173667840:ℝ)/3), ((-6168244125696:ℝ)/49), ((3004329623552:ℝ)/147), ((-68719476736:ℝ)/49)] : List ℝ).getD e 0) 17 hq1'
  have m13' : |centralNum13_33 q| ≤ ((1489204832182560184133151375602688:ℝ)/1068115234375) := by
    rw [centralNum13_33_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((24:ℝ)/5) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-16872075:ℝ)/8), ((1833754545:ℝ)/8), ((-83998007145:ℝ)/16), ((4929124002765:ℝ)/112), ((-76723155584685:ℝ)/448), ((164888745653055:ℝ)/448), ((-63358359907625:ℝ)/128), ((364713160040625:ℝ)/896), ((-334937462578125:ℝ)/1792), ((245466998046875:ℝ)/5376), ((-72144521484375:ℝ)/12544), ((6518798828125:ℝ)/18816), ((-6103515625:ℝ)/784)] : List ℝ).getD e 0) 17 hq1'
  have m23' : |centralNum23_33 q| ≤ ((1978425022774788463495767552:ℝ)/19140625) := by
    rw [centralNum23_33_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((77208723412503754641362627217:ℝ)/50000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece20_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece20_E11 h0) m23'
  have c5 := scaled_affine (X := ((11:ℝ)/1000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3))| ≤ ((214929391947050649531711488000000:ℝ)/7759223491389256698845485849806807) := by
    rw [abs_neg, tailWeight_3, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((24:ℝ)/5)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((24:ℝ)/5)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece20_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((3308571812705231500:ℝ)/129140163)) ≤ ((24:ℝ)/5)^6*(8000*(2*((24:ℝ)/5)-3)^2*(1/((394209393455736254577324892029:ℝ)/100000000))*((3308571812705231500:ℝ)/129140163)) := by
          gcongr
      _ ≤ ((214929391947050649531711488000000:ℝ)/7759223491389256698845485849806807) := by norm_num
  have c7 := affine_round (α := ((274996206545:ℝ)/57344) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((1006392979855611261034691:ℝ)/962072674304) + ((151064323891:ℝ)/8192)*((11:ℝ)/1000) - ((20835650067047371:ℝ)/2000000000)) (β := ((85246292715:ℝ)/7168) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((6064458750894691785225981:ℝ)/1683627180032) - 3*((1006392979855611261034691:ℝ)/962072674304)) + ((78895942437:ℝ)/2048)*((11:ℝ)/1000) - ((147193039839859713:ℝ)/10000000000)) ht
  have hW : pieceW q pieceX_20 3 3 = centralNum11_33 q + 8*(Real.exp (-(3*((19:ℝ)/4)))*Real.exp (-3*t))*centralNum12_33 q + 18*Real.exp (-8*q)*centralNum13_33 q + 72*Real.exp (-11*q)*centralNum23_33 q + 8*q^7*(2*q-3)^2*((11:ℝ)/1000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3)) := by
    rw [pieceW_33, pieceX_20, sym4_33, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((46550079221899273754494613155568578443322572052328603922057413:ℝ)/934714115296851346358527447975168048070221870946842495311115200000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((274996206545:ℝ)/57344) + ((85246292715:ℝ)/7168)*t) + (8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((1006392979855611261034691:ℝ)/962072674304) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((6064458750894691785225981:ℝ)/1683627180032) - 3*((1006392979855611261034691:ℝ)/962072674304))*t) + (((151064323891:ℝ)/8192) + ((78895942437:ℝ)/2048)*t)*((11:ℝ)/1000) - (((20835650067047371:ℝ)/2000000000) + t * ((147193039839859713:ℝ)/10000000000)) = (((274996206545:ℝ)/57344) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*((1006392979855611261034691:ℝ)/962072674304) + ((151064323891:ℝ)/8192)*((11:ℝ)/1000) - ((20835650067047371:ℝ)/2000000000)) + t*(((85246292715:ℝ)/7168) + 8*(((1/((77208723412503754641362627217:ℝ)/50000000000000000000000))+(1/((154417446535217520259464374759:ℝ)/100000000000000000000000)))/2)*(((6064458750894691785225981:ℝ)/1683627180032) - 3*((1006392979855611261034691:ℝ)/962072674304)) + ((78895942437:ℝ)/2048)*((11:ℝ)/1000) - ((147193039839859713:ℝ)/10000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece20_plus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((212518234352967343:ℝ)/10000000000) + ((1:ℝ)/20)*((428144089444091513:ℝ)/10000000000) - (((99221949172849951:ℝ)/1000000000000) + ((105897519968414071:ℝ)/12500000000000) + ((5055772474767419:ℝ)/1562500000000) + ((460200736841276641:ℝ)/100000000000000)))
      (((-133045247229337619:ℝ)/50000000000) + ((1:ℝ)/20)*((-24008810107406587:ℝ)/6250000000))
      (((-4263338068744913:ℝ)/100000000000) + ((1:ℝ)/20)*((-49026316964314259:ℝ)/1250000000000))
      (((998563213874764459:ℝ)/10000000000000) + ((1:ℝ)/20)*((-828339741243509127:ℝ)/10000000000000))
      (((152307489150033389:ℝ)/10000000000) + ((1:ℝ)/20)*((294126705808128273:ℝ)/10000000000) - (((105897519968414071:ℝ)/12500000000000) + ((676516298106621591:ℝ)/10000000000000) + ((431702364701933:ℝ)/25000000000) + ((953961405043451083:ℝ)/100000000000000)))
      (((-54332828275381757:ℝ)/50000000000) + ((1:ℝ)/20)*((-86531794908020757:ℝ)/50000000000))
      (((-910476245963108891:ℝ)/1000000000000) + ((1:ℝ)/20)*((-278031251937723577:ℝ)/1000000000000))
      (((66187844150562971:ℝ)/5000000000) + ((1:ℝ)/20)*((290126060217775353:ℝ)/10000000000) - (((5055772474767419:ℝ)/1562500000000) + ((431702364701933:ℝ)/25000000000) + ((220259201155980897:ℝ)/2500000000000) + ((117972920069802097:ℝ)/1000000000000)))
      (((8793644584280179:ℝ)/4000000000) + ((1:ℝ)/20)*((30946182672445383:ℝ)/12500000000))
      (((20835650067047371:ℝ)/2000000000) + ((1:ℝ)/20)*((147193039839859713:ℝ)/10000000000) - (((460200736841276641:ℝ)/100000000000000) + ((953961405043451083:ℝ)/100000000000000) + ((117972920069802097:ℝ)/1000000000000) + ((78145739826661681:ℝ)/50000000000))) i j :=
  quadForm_nonneg_of_ldl ((18621609943995683899:ℝ)/800000000000) ((30257831083488581439772567923830237205081:ℝ)/1862160994399568389900000000000000) ((679668234936191753949811356273019370249364364738402082551680257:ℝ)/47277861067950908499644637380984745632939062500000000000) ((492244101841976611251687087638826184793021760788986670879549097262707159951546858103:ℝ)/54373458794895340315984908501841549619949149179072166604134420560000000000000) ((-11411901701784020304:ℝ)/93108049719978419495) ((-4459443336602170036:ℝ)/2327701242999460487375) ((19142924536251780053:ℝ)/4655402485998920974750) ((-10974218748250064826615483936498335612444:ℝ)/151289155417442907198862839619151186025405) ((-8497472909398684019430180617674165574519:ℝ)/151289155417442907198862839619151186025405) ((426669016834107555500654880331755254479388698803278693074139153:ℝ)/2718672939744767015799245425092077480997457458953608330206721028)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece20_minus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((212518234352967343:ℝ)/10000000000) - ((1:ℝ)/20)*((428144089444091513:ℝ)/10000000000) - (((99221949172849951:ℝ)/1000000000000) + ((105897519968414071:ℝ)/12500000000000) + ((5055772474767419:ℝ)/1562500000000) + ((460200736841276641:ℝ)/100000000000000)))
      (((-133045247229337619:ℝ)/50000000000) - ((1:ℝ)/20)*((-24008810107406587:ℝ)/6250000000))
      (((-4263338068744913:ℝ)/100000000000) - ((1:ℝ)/20)*((-49026316964314259:ℝ)/1250000000000))
      (((998563213874764459:ℝ)/10000000000000) - ((1:ℝ)/20)*((-828339741243509127:ℝ)/10000000000000))
      (((152307489150033389:ℝ)/10000000000) - ((1:ℝ)/20)*((294126705808128273:ℝ)/10000000000) - (((105897519968414071:ℝ)/12500000000000) + ((676516298106621591:ℝ)/10000000000000) + ((431702364701933:ℝ)/25000000000) + ((953961405043451083:ℝ)/100000000000000)))
      (((-54332828275381757:ℝ)/50000000000) - ((1:ℝ)/20)*((-86531794908020757:ℝ)/50000000000))
      (((-910476245963108891:ℝ)/1000000000000) - ((1:ℝ)/20)*((-278031251937723577:ℝ)/1000000000000))
      (((66187844150562971:ℝ)/5000000000) - ((1:ℝ)/20)*((290126060217775353:ℝ)/10000000000) - (((5055772474767419:ℝ)/1562500000000) + ((431702364701933:ℝ)/25000000000) + ((220259201155980897:ℝ)/2500000000000) + ((117972920069802097:ℝ)/1000000000000)))
      (((8793644584280179:ℝ)/4000000000) - ((1:ℝ)/20)*((30946182672445383:ℝ)/12500000000))
      (((20835650067047371:ℝ)/2000000000) - ((1:ℝ)/20)*((147193039839859713:ℝ)/10000000000) - (((460200736841276641:ℝ)/100000000000000) + ((953961405043451083:ℝ)/100000000000000) + ((117972920069802097:ℝ)/1000000000000) + ((78145739826661681:ℝ)/50000000000))) i j :=
  quadForm_nonneg_of_ldl ((3039291445688590359:ℝ)/160000000000) ((810658805466388989564052530656492893681:ℝ)/60785828913771807180000000000000) ((45458936043009402842873186682193779674235061469560064164020079:ℝ)/3958294948566352488105725247346156707426757812500000000) ((110215807886218618470263342507687894262566261696873641554922628947801945637823875771:ℝ)/14546859533763008909719419738302009495755219670259220532486425280000000000000) ((-9875337854909998736:ℝ)/75982286142214758975) ((-1355744266962551988:ℝ)/633185717851789658125) ((20799604018738798307:ℝ)/3799114307110737948750) ((-7639341947805016963907529938490076604004:ℝ)/101332350683298623695506566332061611710125) ((-6709677855473098238416157436482540934649:ℝ)/101332350683298623695506566332061611710125) ((254379190418894434557184909243248085648362527196719731012758293:ℝ)/1454685953376300890971941973830200949575521967025922053248642528)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

/-- **Piece 20.** The piece matrix is positive semidefinite on `q ∈ [47/10, 24/5]`. -/
theorem piece_20 {q : ℝ} (h0 : ((47:ℝ)/10) ≤ q) (h1 : q ≤ ((24:ℝ)/5)) (y : Fin 4 → ℝ) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceW q pieceX_20 i j :=
  pieceForm_nonneg (pieceW_symm (sym4_symm _ _ _ _ _ _ _ _ _ _) q) (by norm_num : (0:ℝ) < ((1:ℝ)/20))
    (abs_le.mpr ⟨by linarith, by linarith⟩)
    (piece20_e00 h0 h1) (piece20_e01 h0 h1) (piece20_e02 h0 h1) (piece20_e03 h0 h1) (piece20_e11 h0 h1) (piece20_e12 h0 h1) (piece20_e13 h0 h1) (piece20_e22 h0 h1) (piece20_e23 h0 h1) (piece20_e33 h0 h1)
    piece20_plus piece20_minus y

/-! #### Piece 21 (seam), `q ∈ [24/5, 49/10]` -/

/-- The compensation matrix of piece 21. -/
def pieceX_21 : Fin 4 → Fin 4 → ℝ :=
  sym4 ((11:ℝ)/1000) (0:ℝ) (0:ℝ) (0:ℝ) ((11:ℝ)/1000) (0:ℝ) (0:ℝ) ((11:ℝ)/1000) (0:ℝ) ((11:ℝ)/1000)

theorem piece21_L3 : ((52110430930665053533393903587:ℝ)/25000000000000000000000) ≤ Real.exp ((3:ℝ)*((97:ℝ)/20)) := by
  have h := le_exp_nat_add 14 (f := ((11:ℝ)/20)) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((97:ℝ)/20) = ((14:ℕ):ℝ) + ((11:ℝ)/20) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece21_U3 : Real.exp ((3:ℝ)*((97:ℝ)/20)) ≤ ((41688350428296700364775326827:ℝ)/20000000000000000000000) := by
  have h := exp_nat_add_le 14 (f := ((11:ℝ)/20)) (by norm_num) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((97:ℝ)/20) = ((14:ℕ):ℝ) + ((11:ℝ)/20) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem piece21_L8_at : ((23761732557111143243707921359:ℝ)/500000000000) ≤ Real.exp ((8:ℝ)*((24:ℝ)/5)) := by
  have h := le_exp_nat_add 38 (f := ((2:ℝ)/5)) (by norm_num)
  rw [show ((8:ℝ):ℝ)*((24:ℝ)/5) = ((38:ℕ):ℝ) + ((2:ℝ)/5) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece21_E8 {q : ℝ} (h0 : ((24:ℝ)/5) ≤ q) : Real.exp (-((8:ℝ))*q) ≤ 1/((23761732557111143243707921359:ℝ)/500000000000) := by
  have hm : Real.exp (-((8:ℝ))*q) ≤ Real.exp (-((8:ℝ)*((24:ℝ)/5))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece21_L8_at (le_refl _)).2

theorem piece21_L11_at : ((426302379849834285171489424927:ℝ)/5000000) ≤ Real.exp ((11:ℝ)*((24:ℝ)/5)) := by
  have h := le_exp_nat_add 52 (f := ((4:ℝ)/5)) (by norm_num)
  rw [show ((11:ℝ):ℝ)*((24:ℝ)/5) = ((52:ℕ):ℝ) + ((4:ℝ)/5) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece21_E11 {q : ℝ} (h0 : ((24:ℝ)/5) ≤ q) : Real.exp (-((11:ℝ))*q) ≤ 1/((426302379849834285171489424927:ℝ)/5000000) := by
  have hm : Real.exp (-((11:ℝ))*q) ≤ Real.exp (-((11:ℝ)*((24:ℝ)/5))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece21_L11_at (le_refl _)).2

theorem piece21_Lt_at : ((22711205925439889067307176219:ℝ)/2000000) ≤ Real.exp (((529:ℝ)/50)*((24:ℝ)/5)) := by
  have h := le_exp_nat_add 50 (f := ((98:ℝ)/125)) (by norm_num)
  rw [show (((529:ℝ)/50):ℝ)*((24:ℝ)/5) = ((50:ℕ):ℝ) + ((98:ℝ)/125) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece21_Et {q : ℝ} (h0 : ((24:ℝ)/5) ≤ q) : Real.exp (-(((529:ℝ)/50))*q) ≤ 1/((22711205925439889067307176219:ℝ)/2000000) := by
  have hm : Real.exp (-(((529:ℝ)/50))*q) ≤ Real.exp (-(((529:ℝ)/50)*((24:ℝ)/5))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece21_Lt_at (le_refl _)).2

theorem piece21_e00 {q : ℝ} (h0 : ((24:ℝ)/5) ≤ q) (h1 : q ≤ ((49:ℝ)/10)) :
    |pieceW q pieceX_21 0 0 - (((10375520234213723:ℝ)/400000000) + (q - ((97:ℝ)/20)) * ((51141528937126551:ℝ)/1000000000))| ≤ ((57889656422598533:ℝ)/500000000000) := by
  set t := q - ((97:ℝ)/20) with htd
  have hq : q = ((97:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece21_L3 piece21_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((97:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_00 q = ∑ e ∈ Finset.range 10, ([((411182469709117057:ℝ)/16000000000), ((40499931851652909:ℝ)/800000000), ((55620202844589:ℝ)/1250000), ((5720496550377:ℝ)/250000), ((379048612341:ℝ)/50000), ((4192245813:ℝ)/2500), ((30937956:ℝ)/125), ((587328:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_00; ring
  have h12 : centralNum12_00 q = ∑ e ∈ Finset.range 11, ([((-788945880176957317957:ℝ)/320000000000), ((-17128147614949513797:ℝ)/3200000000), ((-418497870301930731:ℝ)/80000000), ((-6060978305988099:ℝ)/2000000), ((-230452414057887:ℝ)/200000), ((-15021656106051:ℝ)/50000), ((-6799345077:ℝ)/125), ((-168806838:ℝ)/25), ((-2749746:ℝ)/5), (-26536:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_00; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((411182469709117057:ℝ)/16000000000), ((40499931851652909:ℝ)/800000000), ((55620202844589:ℝ)/1250000), ((5720496550377:ℝ)/250000), ((379048612341:ℝ)/50000), ((4192245813:ℝ)/2500), ((30937956:ℝ)/125), ((587328:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-788945880176957317957:ℝ)/320000000000), ((-17128147614949513797:ℝ)/3200000000), ((-418497870301930731:ℝ)/80000000), ((-6060978305988099:ℝ)/2000000), ((-230452414057887:ℝ)/200000), ((-15021656106051:ℝ)/50000), ((-6799345077:ℝ)/125), ((-168806838:ℝ)/25), ((-2749746:ℝ)/5), (-26536:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 9 ht
  have m12 := abs_poly_le (fun e => ([((-788945880176957317957:ℝ)/320000000000), ((-17128147614949513797:ℝ)/3200000000), ((-418497870301930731:ℝ)/80000000), ((-6060978305988099:ℝ)/2000000), ((-230452414057887:ℝ)/200000), ((-15021656106051:ℝ)/50000), ((-6799345077:ℝ)/125), ((-168806838:ℝ)/25), ((-2749746:ℝ)/5), (-26536:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 11 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((411182469709117057:ℝ)/16000000000), ((40499931851652909:ℝ)/800000000), ((55620202844589:ℝ)/1250000), ((5720496550377:ℝ)/250000), ((379048612341:ℝ)/50000), ((4192245813:ℝ)/2500), ((30937956:ℝ)/125), ((587328:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - (((411182469709117057:ℝ)/16000000000) + ((40499931851652909:ℝ)/800000000)*t)| ≤ ((913188503658281:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 11, ([((-788945880176957317957:ℝ)/320000000000), ((-17128147614949513797:ℝ)/3200000000), ((-418497870301930731:ℝ)/80000000), ((-6060978305988099:ℝ)/2000000), ((-230452414057887:ℝ)/200000), ((-15021656106051:ℝ)/50000), ((-6799345077:ℝ)/125), ((-168806838:ℝ)/25), ((-2749746:ℝ)/5), (-26536:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e) - ((-788945880176957317957:ℝ)/320000000000) - ((-17128147614949513797:ℝ)/3200000000)*t| ≤ ((430853311026062269:ℝ)/32000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 11, ([((-788945880176957317957:ℝ)/320000000000), ((-17128147614949513797:ℝ)/3200000000), ((-418497870301930731:ℝ)/80000000), ((-6060978305988099:ℝ)/2000000), ((-230452414057887:ℝ)/200000), ((-15021656106051:ℝ)/50000), ((-6799345077:ℝ)/125), ((-168806838:ℝ)/25), ((-2749746:ℝ)/5), (-26536:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((858296046251919443:ℝ)/312500000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((362703499022249257:ℝ)/16000000000) - ((37001449430951109:ℝ)/800000000)*t| ≤ ((858149060041481:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((49:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (600:ℝ), (-7776:ℝ), (16800:ℝ), (-9216:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m13' : |centralNum13_00 q| ≤ ((8087405244549834147:ℝ)/78125000) := by
    rw [centralNum13_00_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((49:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (780:ℝ), (-6156:ℝ), (15288:ℝ), (-14400:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m23' : |centralNum23_00 q| ≤ ((277138224919849776:ℝ)/1953125) := by
    rw [centralNum23_00_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((41688350428296700364775326827:ℝ)/20000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece21_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece21_E11 h0) m23'
  have c5 := scaled_affine (X := ((11:ℝ)/1000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0))| ≤ ((15310036062114424343552000:ℝ)/191581999813042858505060206936533) := by
    rw [abs_neg, tailWeight_0, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((49:ℝ)/10)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((49:ℝ)/10)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece21_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((10465499600:ℝ)/59049)) ≤ ((49:ℝ)/10)^6*(8000*(2*((49:ℝ)/10)-3)^2*(1/((22711205925439889067307176219:ℝ)/2000000))*((10465499600:ℝ)/59049)) := by
          gcongr
      _ ≤ ((15310036062114424343552000:ℝ)/191581999813042858505060206936533) := by norm_num
  have c7 := affine_round (α := ((411182469709117057:ℝ)/16000000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((-788945880176957317957:ℝ)/320000000000) + ((362703499022249257:ℝ)/16000000000)*((11:ℝ)/1000) - ((10375520234213723:ℝ)/400000000)) (β := ((40499931851652909:ℝ)/800000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((-17128147614949513797:ℝ)/3200000000) - 3*((-788945880176957317957:ℝ)/320000000000)) + ((37001449430951109:ℝ)/800000000)*((11:ℝ)/1000) - ((51141528937126551:ℝ)/1000000000)) ht
  have hW : pieceW q pieceX_21 0 0 = centralNum11_00 q + 8*(Real.exp (-(3*((97:ℝ)/20)))*Real.exp (-3*t))*centralNum12_00 q + 18*Real.exp (-8*q)*centralNum13_00 q + 72*Real.exp (-11*q)*centralNum23_00 q + 8*q^7*(2*q-3)^2*((11:ℝ)/1000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0)) := by
    rw [pieceW_00, pieceX_21, sym4_00, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((49115359465806632784369736236228343781760012632612752464763:ℝ)/17379183244856928853273859584849718684331801915818021027592000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((411182469709117057:ℝ)/16000000000) + ((40499931851652909:ℝ)/800000000)*t) + (8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((-788945880176957317957:ℝ)/320000000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((-17128147614949513797:ℝ)/3200000000) - 3*((-788945880176957317957:ℝ)/320000000000))*t) + (((362703499022249257:ℝ)/16000000000) + ((37001449430951109:ℝ)/800000000)*t)*((11:ℝ)/1000) - (((10375520234213723:ℝ)/400000000) + t * ((51141528937126551:ℝ)/1000000000)) = (((411182469709117057:ℝ)/16000000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((-788945880176957317957:ℝ)/320000000000) + ((362703499022249257:ℝ)/16000000000)*((11:ℝ)/1000) - ((10375520234213723:ℝ)/400000000)) + t*(((40499931851652909:ℝ)/800000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((-17128147614949513797:ℝ)/3200000000) - 3*((-788945880176957317957:ℝ)/320000000000)) + ((37001449430951109:ℝ)/800000000)*((11:ℝ)/1000) - ((51141528937126551:ℝ)/1000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece21_e01 {q : ℝ} (h0 : ((24:ℝ)/5) ≤ q) (h1 : q ≤ ((49:ℝ)/10)) :
    |pieceW q pieceX_21 0 1 - (((-76755207408217499:ℝ)/25000000000) + (q - ((97:ℝ)/20)) * ((-87072931329524881:ℝ)/20000000000))| ≤ ((901142578634677493:ℝ)/100000000000000) := by
  set t := q - ((97:ℝ)/20) with htd
  have hq : q = ((97:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece21_L3 piece21_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((97:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_01 q = ∑ e ∈ Finset.range 8, ([((-242394853434339:ℝ)/80000000), ((-17492412103509:ℝ)/4000000), ((-541002436191:ℝ)/200000), ((-1859114901:ℝ)/2000), ((-19166133:ℝ)/100), ((-592767:ℝ)/25), ((-8148:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_01; ring
  have h12 : centralNum12_01 q = ∑ e ∈ Finset.range 12, ([((-134311946474822865842067:ℝ)/12800000000000), ((-8451180700991531098503:ℝ)/320000000000), ((-192985344207777110553:ℝ)/6400000000), ((-3299287155455626971:ℝ)/160000000), ((-75083905416962571:ℝ)/8000000), ((-2985722108791443:ℝ)/1000000), ((-67745941192293:ℝ)/100000), ((-54821425731:ℝ)/500), ((-1240456131:ℝ)/100), ((-4671726:ℝ)/5), ((-210852:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_01; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-242394853434339:ℝ)/80000000), ((-17492412103509:ℝ)/4000000), ((-541002436191:ℝ)/200000), ((-1859114901:ℝ)/2000), ((-19166133:ℝ)/100), ((-592767:ℝ)/25), ((-8148:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0) 6 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-134311946474822865842067:ℝ)/12800000000000), ((-8451180700991531098503:ℝ)/320000000000), ((-192985344207777110553:ℝ)/6400000000), ((-3299287155455626971:ℝ)/160000000), ((-75083905416962571:ℝ)/8000000), ((-2985722108791443:ℝ)/1000000), ((-67745941192293:ℝ)/100000), ((-54821425731:ℝ)/500), ((-1240456131:ℝ)/100), ((-4671726:ℝ)/5), ((-210852:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0) 10 ht
  have m12 := abs_poly_le (fun e => ([((-134311946474822865842067:ℝ)/12800000000000), ((-8451180700991531098503:ℝ)/320000000000), ((-192985344207777110553:ℝ)/6400000000), ((-3299287155455626971:ℝ)/160000000), ((-75083905416962571:ℝ)/8000000), ((-2985722108791443:ℝ)/1000000), ((-67745941192293:ℝ)/100000), ((-54821425731:ℝ)/500), ((-1240456131:ℝ)/100), ((-4671726:ℝ)/5), ((-210852:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0) 12 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 8, ([((-242394853434339:ℝ)/80000000), ((-17492412103509:ℝ)/4000000), ((-541002436191:ℝ)/200000), ((-1859114901:ℝ)/2000), ((-19166133:ℝ)/100), ((-592767:ℝ)/25), ((-8148:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0 * t^e) - (((-242394853434339:ℝ)/80000000) + ((-17492412103509:ℝ)/4000000)*t)| ≤ ((68799304521:ℝ)/10000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 12, ([((-134311946474822865842067:ℝ)/12800000000000), ((-8451180700991531098503:ℝ)/320000000000), ((-192985344207777110553:ℝ)/6400000000), ((-3299287155455626971:ℝ)/160000000), ((-75083905416962571:ℝ)/8000000), ((-2985722108791443:ℝ)/1000000), ((-67745941192293:ℝ)/100000), ((-54821425731:ℝ)/500), ((-1240456131:ℝ)/100), ((-4671726:ℝ)/5), ((-210852:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e) - ((-134311946474822865842067:ℝ)/12800000000000) - ((-8451180700991531098503:ℝ)/320000000000)*t| ≤ ((199736502226116641043:ℝ)/2560000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 12, ([((-134311946474822865842067:ℝ)/12800000000000), ((-8451180700991531098503:ℝ)/320000000000), ((-192985344207777110553:ℝ)/6400000000), ((-3299287155455626971:ℝ)/160000000), ((-75083905416962571:ℝ)/8000000), ((-2985722108791443:ℝ)/1000000), ((-67745941192293:ℝ)/100000), ((-54821425731:ℝ)/500), ((-1240456131:ℝ)/100), ((-4671726:ℝ)/5), ((-210852:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((74322749212859624631:ℝ)/6250000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((362703499022249257:ℝ)/16000000000) - ((37001449430951109:ℝ)/800000000)*t| ≤ ((858149060041481:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((49:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-6288:ℝ), (81024:ℝ), (-238720:ℝ), (246784:ℝ), (-98304:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m13' : |centralNum13_01 q| ≤ ((2433103108837543721831:ℝ)/390625000) := by
    rw [centralNum13_01_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((49:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-7368:ℝ), (59208:ℝ), (-155734:ℝ), (205300:ℝ), (-60000:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m23' : |centralNum23_01 q| ≤ ((266112717986779848611:ℝ)/62500000) := by
    rw [centralNum23_01_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((41688350428296700364775326827:ℝ)/20000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece21_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece21_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-242394853434339:ℝ)/80000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((-134311946474822865842067:ℝ)/12800000000000) + ((362703499022249257:ℝ)/16000000000)*(0:ℝ) - ((-76755207408217499:ℝ)/25000000000)) (β := ((-17492412103509:ℝ)/4000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((-8451180700991531098503:ℝ)/320000000000) - 3*((-134311946474822865842067:ℝ)/12800000000000)) + ((37001449430951109:ℝ)/800000000)*(0:ℝ) - ((-87072931329524881:ℝ)/20000000000)) ht
  have hW : pieceW q pieceX_21 0 1 = centralNum11_01 q + 8*(Real.exp (-(3*((97:ℝ)/20)))*Real.exp (-3*t))*centralNum12_01 q + 18*Real.exp (-8*q)*centralNum13_01 q + 72*Real.exp (-11*q)*centralNum23_01 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_01, pieceX_21, sym4_01, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((139582879084021359280704685486935074198127748618295842959:ℝ)/57930610816189762844246198616165728947772673052726736758640000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-242394853434339:ℝ)/80000000) + ((-17492412103509:ℝ)/4000000)*t) + (8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((-134311946474822865842067:ℝ)/12800000000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((-8451180700991531098503:ℝ)/320000000000) - 3*((-134311946474822865842067:ℝ)/12800000000000))*t) + (((362703499022249257:ℝ)/16000000000) + ((37001449430951109:ℝ)/800000000)*t)*(0:ℝ) - (((-76755207408217499:ℝ)/25000000000) + t * ((-87072931329524881:ℝ)/20000000000)) = (((-242394853434339:ℝ)/80000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((-134311946474822865842067:ℝ)/12800000000000) + ((362703499022249257:ℝ)/16000000000)*(0:ℝ) - ((-76755207408217499:ℝ)/25000000000)) + t*(((-17492412103509:ℝ)/4000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((-8451180700991531098503:ℝ)/320000000000) - 3*((-134311946474822865842067:ℝ)/12800000000000)) + ((37001449430951109:ℝ)/800000000)*(0:ℝ) - ((-87072931329524881:ℝ)/20000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece21_e02 {q : ℝ} (h0 : ((24:ℝ)/5) ≤ q) (h1 : q ≤ ((49:ℝ)/10)) :
    |pieceW q pieceX_21 0 2 - (((-461768050010095133:ℝ)/10000000000000) + (q - ((97:ℝ)/20)) * ((-316453849931450013:ℝ)/10000000000000))| ≤ ((66386381693315307:ℝ)/20000000000000) := by
  set t := q - ((97:ℝ)/20) with htd
  have hq : q = ((97:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece21_L3 piece21_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((97:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_02 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_02; ring
  have h12 : centralNum12_02 q = ∑ e ∈ Finset.range 13, ([((-24640444125595559426623551:ℝ)/2048000000000000), ((-4540382656663413183341121:ℝ)/102400000000000), ((-353390641483488885319599:ℝ)/5120000000000), ((-3176724988349569520703:ℝ)/51200000000), ((-23340157336362493701:ℝ)/640000000), ((-4769496744234502653:ℝ)/320000000), ((-69891749271041103:ℝ)/16000000), ((-742836270398067:ℝ)/800000), ((-2279229829659:ℝ)/16000), ((-12328431057:ℝ)/800), ((-223479459:ℝ)/200), ((-488079:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_02; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-24640444125595559426623551:ℝ)/2048000000000000), ((-4540382656663413183341121:ℝ)/102400000000000), ((-353390641483488885319599:ℝ)/5120000000000), ((-3176724988349569520703:ℝ)/51200000000), ((-23340157336362493701:ℝ)/640000000), ((-4769496744234502653:ℝ)/320000000), ((-69891749271041103:ℝ)/16000000), ((-742836270398067:ℝ)/800000), ((-2279229829659:ℝ)/16000), ((-12328431057:ℝ)/800), ((-223479459:ℝ)/200), ((-488079:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((-24640444125595559426623551:ℝ)/2048000000000000), ((-4540382656663413183341121:ℝ)/102400000000000), ((-353390641483488885319599:ℝ)/5120000000000), ((-3176724988349569520703:ℝ)/51200000000), ((-23340157336362493701:ℝ)/640000000), ((-4769496744234502653:ℝ)/320000000), ((-69891749271041103:ℝ)/16000000), ((-742836270398067:ℝ)/800000), ((-2279229829659:ℝ)/16000), ((-12328431057:ℝ)/800), ((-223479459:ℝ)/200), ((-488079:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((-24640444125595559426623551:ℝ)/2048000000000000), ((-4540382656663413183341121:ℝ)/102400000000000), ((-353390641483488885319599:ℝ)/5120000000000), ((-3176724988349569520703:ℝ)/51200000000), ((-23340157336362493701:ℝ)/640000000), ((-4769496744234502653:ℝ)/320000000), ((-69891749271041103:ℝ)/16000000), ((-742836270398067:ℝ)/800000), ((-2279229829659:ℝ)/16000), ((-12328431057:ℝ)/800), ((-223479459:ℝ)/200), ((-488079:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e) - ((-24640444125595559426623551:ℝ)/2048000000000000) - ((-4540382656663413183341121:ℝ)/102400000000000)*t| ≤ ((2888677733172512109003:ℝ)/16000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((-24640444125595559426623551:ℝ)/2048000000000000), ((-4540382656663413183341121:ℝ)/102400000000000), ((-353390641483488885319599:ℝ)/5120000000000), ((-3176724988349569520703:ℝ)/51200000000), ((-23340157336362493701:ℝ)/640000000), ((-4769496744234502653:ℝ)/320000000), ((-69891749271041103:ℝ)/16000000), ((-742836270398067:ℝ)/800000), ((-2279229829659:ℝ)/16000), ((-12328431057:ℝ)/800), ((-223479459:ℝ)/200), ((-488079:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((7214496467799085488261:ℝ)/500000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((362703499022249257:ℝ)/16000000000) - ((37001449430951109:ℝ)/800000000)*t| ≤ ((858149060041481:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((49:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82080:ℝ), (-967680:ℝ), (3257600:ℝ), (-4474880:ℝ), (2908160:ℝ), (-786432:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_02 q| ≤ ((298542402186141961885443:ℝ)/976562500) := by
    rw [centralNum13_02_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((49:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (87660:ℝ), (-702180:ℝ), ((7421435:ℝ)/4), ((-10854125:ℝ)/4), ((2828125:ℝ)/2), (-187500:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_02 q| ≤ ((11612126667249656649381:ℝ)/100000000) := by
    rw [centralNum23_02_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((41688350428296700364775326827:ℝ)/20000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece21_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece21_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((-24640444125595559426623551:ℝ)/2048000000000000) + ((362703499022249257:ℝ)/16000000000)*(0:ℝ) - ((-461768050010095133:ℝ)/10000000000000)) (β := (0:ℝ) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((-4540382656663413183341121:ℝ)/102400000000000) - 3*((-24640444125595559426623551:ℝ)/2048000000000000)) + ((37001449430951109:ℝ)/800000000)*(0:ℝ) - ((-316453849931450013:ℝ)/10000000000000)) ht
  have hW : pieceW q pieceX_21 0 2 = centralNum11_02 q + 8*(Real.exp (-(3*((97:ℝ)/20)))*Real.exp (-3*t))*centralNum12_02 q + 18*Real.exp (-8*q)*centralNum13_02 q + 72*Real.exp (-11*q)*centralNum23_02 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_02, pieceX_21, sym4_02, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((5992053149077323350720437257871767234221463726116649998059:ℝ)/144826527040474407110615496540414322369431682631816841896600000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((-24640444125595559426623551:ℝ)/2048000000000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((-4540382656663413183341121:ℝ)/102400000000000) - 3*((-24640444125595559426623551:ℝ)/2048000000000000))*t) + (((362703499022249257:ℝ)/16000000000) + ((37001449430951109:ℝ)/800000000)*t)*(0:ℝ) - (((-461768050010095133:ℝ)/10000000000000) + t * ((-316453849931450013:ℝ)/10000000000000)) = ((0:ℝ) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((-24640444125595559426623551:ℝ)/2048000000000000) + ((362703499022249257:ℝ)/16000000000)*(0:ℝ) - ((-461768050010095133:ℝ)/10000000000000)) + t*((0:ℝ) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((-4540382656663413183341121:ℝ)/102400000000000) - 3*((-24640444125595559426623551:ℝ)/2048000000000000)) + ((37001449430951109:ℝ)/800000000)*(0:ℝ) - ((-316453849931450013:ℝ)/10000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece21_e03 {q : ℝ} (h0 : ((24:ℝ)/5) ≤ q) (h1 : q ≤ ((49:ℝ)/10)) :
    |pieceW q pieceX_21 0 3 - (((912376229289570983:ℝ)/10000000000000) + (q - ((97:ℝ)/20)) * ((-891335023035063943:ℝ)/10000000000000))| ≤ ((9995341624331629:ℝ)/2500000000000) := by
  set t := q - ((97:ℝ)/20) with htd
  have hq : q = ((97:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece21_L3 piece21_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((97:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_03 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_03; ring
  have h12 : centralNum12_03 q = ∑ e ∈ Finset.range 14, ([((13631907923632070919327384837:ℝ)/573440000000000000), ((344727433668291213184276617:ℝ)/7168000000000000), ((10993843122358592460830031:ℝ)/358400000000000), ((-252656135310704667783543:ℝ)/35840000000000), ((-2495042741102063210397:ℝ)/102400000000), ((-1701882935818786914579:ℝ)/89600000000), ((-608366112128657019:ℝ)/70000000), ((-300804861003994899:ℝ)/112000000), ((-13127816971678041:ℝ)/22400000), ((-2549862929709:ℝ)/28000), ((-138702370383:ℝ)/14000), ((-143923797:ℝ)/200), ((-4399029:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_03; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((13631907923632070919327384837:ℝ)/573440000000000000), ((344727433668291213184276617:ℝ)/7168000000000000), ((10993843122358592460830031:ℝ)/358400000000000), ((-252656135310704667783543:ℝ)/35840000000000), ((-2495042741102063210397:ℝ)/102400000000), ((-1701882935818786914579:ℝ)/89600000000), ((-608366112128657019:ℝ)/70000000), ((-300804861003994899:ℝ)/112000000), ((-13127816971678041:ℝ)/22400000), ((-2549862929709:ℝ)/28000), ((-138702370383:ℝ)/14000), ((-143923797:ℝ)/200), ((-4399029:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((13631907923632070919327384837:ℝ)/573440000000000000), ((344727433668291213184276617:ℝ)/7168000000000000), ((10993843122358592460830031:ℝ)/358400000000000), ((-252656135310704667783543:ℝ)/35840000000000), ((-2495042741102063210397:ℝ)/102400000000), ((-1701882935818786914579:ℝ)/89600000000), ((-608366112128657019:ℝ)/70000000), ((-300804861003994899:ℝ)/112000000), ((-13127816971678041:ℝ)/22400000), ((-2549862929709:ℝ)/28000), ((-138702370383:ℝ)/14000), ((-143923797:ℝ)/200), ((-4399029:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((13631907923632070919327384837:ℝ)/573440000000000000), ((344727433668291213184276617:ℝ)/7168000000000000), ((10993843122358592460830031:ℝ)/358400000000000), ((-252656135310704667783543:ℝ)/35840000000000), ((-2495042741102063210397:ℝ)/102400000000), ((-1701882935818786914579:ℝ)/89600000000), ((-608366112128657019:ℝ)/70000000), ((-300804861003994899:ℝ)/112000000), ((-13127816971678041:ℝ)/22400000), ((-2549862929709:ℝ)/28000), ((-138702370383:ℝ)/14000), ((-143923797:ℝ)/200), ((-4399029:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((13631907923632070919327384837:ℝ)/573440000000000000) - ((344727433668291213184276617:ℝ)/7168000000000000)*t| ≤ ((8914298821835630753368557:ℝ)/114688000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((13631907923632070919327384837:ℝ)/573440000000000000), ((344727433668291213184276617:ℝ)/7168000000000000), ((10993843122358592460830031:ℝ)/358400000000000), ((-252656135310704667783543:ℝ)/35840000000000), ((-2495042741102063210397:ℝ)/102400000000), ((-1701882935818786914579:ℝ)/89600000000), ((-608366112128657019:ℝ)/70000000), ((-300804861003994899:ℝ)/112000000), ((-13127816971678041:ℝ)/22400000), ((-2549862929709:ℝ)/28000), ((-138702370383:ℝ)/14000), ((-143923797:ℝ)/200), ((-4399029:ℝ)/140), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((1505538915241441392583133409:ℝ)/57344000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((362703499022249257:ℝ)/16000000000) - ((37001449430951109:ℝ)/800000000)*t| ≤ ((858149060041481:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((49:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-812160:ℝ), (8985600:ℝ), (-32225280:ℝ), (52019200:ℝ), ((-305233920:ℝ)/7), ((135528448:ℝ)/7), ((-25165824:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_03 q| ≤ ((11303241336553826459112649:ℝ)/1220703125) := by
    rw [centralNum13_03_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((49:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-833220:ℝ), (6469740:ℝ), ((-68603955:ℝ)/4), ((104396875:ℝ)/4), ((-1001334375:ℝ)/56), ((125828125:ℝ)/28), ((-2343750:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_03 q| ≤ ((1690202835923232635617879:ℝ)/800000000) := by
    rw [centralNum23_03_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((41688350428296700364775326827:ℝ)/20000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece21_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece21_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((13631907923632070919327384837:ℝ)/573440000000000000) + ((362703499022249257:ℝ)/16000000000)*(0:ℝ) - ((912376229289570983:ℝ)/10000000000000)) (β := (0:ℝ) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((344727433668291213184276617:ℝ)/7168000000000000) - 3*((13631907923632070919327384837:ℝ)/573440000000000000)) + ((37001449430951109:ℝ)/800000000)*(0:ℝ) - ((-891335023035063943:ℝ)/10000000000000)) ht
  have hW : pieceW q pieceX_21 0 3 = centralNum11_03 q + 8*(Real.exp (-(3*((97:ℝ)/20)))*Real.exp (-3*t))*centralNum12_03 q + 18*Real.exp (-8*q)*centralNum13_03 q + 72*Real.exp (-11*q)*centralNum23_03 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_03, pieceX_21, sym4_03, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((8313401221236454183108486251207324533936398327335416250743:ℝ)/1013785689283320849774308475782900256586021778422717893276200000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((13631907923632070919327384837:ℝ)/573440000000000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((344727433668291213184276617:ℝ)/7168000000000000) - 3*((13631907923632070919327384837:ℝ)/573440000000000000))*t) + (((362703499022249257:ℝ)/16000000000) + ((37001449430951109:ℝ)/800000000)*t)*(0:ℝ) - (((912376229289570983:ℝ)/10000000000000) + t * ((-891335023035063943:ℝ)/10000000000000)) = ((0:ℝ) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((13631907923632070919327384837:ℝ)/573440000000000000) + ((362703499022249257:ℝ)/16000000000)*(0:ℝ) - ((912376229289570983:ℝ)/10000000000000)) + t*((0:ℝ) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((344727433668291213184276617:ℝ)/7168000000000000) - 3*((13631907923632070919327384837:ℝ)/573440000000000000)) + ((37001449430951109:ℝ)/800000000)*(0:ℝ) - ((-891335023035063943:ℝ)/10000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece21_e11 {q : ℝ} (h0 : ((24:ℝ)/5) ≤ q) (h1 : q ≤ ((49:ℝ)/10)) :
    |pieceW q pieceX_21 1 1 - (((36885565739046663:ℝ)/2000000000) + (q - ((97:ℝ)/20)) * ((174846156904578203:ℝ)/5000000000))| ≤ ((787306746876959571:ℝ)/10000000000000) := by
  set t := q - ((97:ℝ)/20) with htd
  have hq : q = ((97:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece21_L3 piece21_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((97:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_11 q = ∑ e ∈ Finset.range 10, ([((218529372521118221:ℝ)/12000000000), ((13808606292720883:ℝ)/400000000), ((147239155751489:ℝ)/5000000), ((3706877062553:ℝ)/250000), ((30324049693:ℝ)/6250), ((1335741701:ℝ)/1250), ((19772844:ℝ)/125), ((378832:ℝ)/25), ((4256:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_11; ring
  have h12 : centralNum12_11 q = ∑ e ∈ Finset.range 13, ([((-6946344387852983770680431:ℝ)/1536000000000000), ((-754557550546751102279387:ℝ)/25600000000000), ((-73558977776078725581733:ℝ)/1280000000000), ((-750363627131830778261:ℝ)/12800000000), ((-5991376427654074607:ℝ)/160000000), ((-1300179314029369231:ℝ)/80000000), ((-19954150485408741:ℝ)/4000000), ((-220107456853489:ℝ)/200000), ((-696504947033:ℝ)/4000), ((-11602790497:ℝ)/600), ((-71722593:ℝ)/50), ((-319626:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_11; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((218529372521118221:ℝ)/12000000000), ((13808606292720883:ℝ)/400000000), ((147239155751489:ℝ)/5000000), ((3706877062553:ℝ)/250000), ((30324049693:ℝ)/6250), ((1335741701:ℝ)/1250), ((19772844:ℝ)/125), ((378832:ℝ)/25), ((4256:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-6946344387852983770680431:ℝ)/1536000000000000), ((-754557550546751102279387:ℝ)/25600000000000), ((-73558977776078725581733:ℝ)/1280000000000), ((-750363627131830778261:ℝ)/12800000000), ((-5991376427654074607:ℝ)/160000000), ((-1300179314029369231:ℝ)/80000000), ((-19954150485408741:ℝ)/4000000), ((-220107456853489:ℝ)/200000), ((-696504947033:ℝ)/4000), ((-11602790497:ℝ)/600), ((-71722593:ℝ)/50), ((-319626:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((-6946344387852983770680431:ℝ)/1536000000000000), ((-754557550546751102279387:ℝ)/25600000000000), ((-73558977776078725581733:ℝ)/1280000000000), ((-750363627131830778261:ℝ)/12800000000), ((-5991376427654074607:ℝ)/160000000), ((-1300179314029369231:ℝ)/80000000), ((-19954150485408741:ℝ)/4000000), ((-220107456853489:ℝ)/200000), ((-696504947033:ℝ)/4000), ((-11602790497:ℝ)/600), ((-71722593:ℝ)/50), ((-319626:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((218529372521118221:ℝ)/12000000000), ((13808606292720883:ℝ)/400000000), ((147239155751489:ℝ)/5000000), ((3706877062553:ℝ)/250000), ((30324049693:ℝ)/6250), ((1335741701:ℝ)/1250), ((19772844:ℝ)/125), ((378832:ℝ)/25), ((4256:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((218529372521118221:ℝ)/12000000000) + ((13808606292720883:ℝ)/400000000)*t)| ≤ ((1812088245014797:ℝ)/24000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((-6946344387852983770680431:ℝ)/1536000000000000), ((-754557550546751102279387:ℝ)/25600000000000), ((-73558977776078725581733:ℝ)/1280000000000), ((-750363627131830778261:ℝ)/12800000000), ((-5991376427654074607:ℝ)/160000000), ((-1300179314029369231:ℝ)/80000000), ((-19954150485408741:ℝ)/4000000), ((-220107456853489:ℝ)/200000), ((-696504947033:ℝ)/4000), ((-11602790497:ℝ)/600), ((-71722593:ℝ)/50), ((-319626:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e) - ((-6946344387852983770680431:ℝ)/1536000000000000) - ((-754557550546751102279387:ℝ)/25600000000000)*t| ≤ ((907421064268791080039:ℝ)/6000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((-6946344387852983770680431:ℝ)/1536000000000000), ((-754557550546751102279387:ℝ)/25600000000000), ((-73558977776078725581733:ℝ)/1280000000000), ((-750363627131830778261:ℝ)/12800000000), ((-5991376427654074607:ℝ)/160000000), ((-1300179314029369231:ℝ)/80000000), ((-19954150485408741:ℝ)/4000000), ((-220107456853489:ℝ)/200000), ((-696504947033:ℝ)/4000), ((-11602790497:ℝ)/600), ((-71722593:ℝ)/50), ((-319626:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((2305253132799328025881:ℝ)/375000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((362703499022249257:ℝ)/16000000000) - ((37001449430951109:ℝ)/800000000)*t| ≤ ((858149060041481:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((49:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-3444:ℝ), (162624:ℝ), (-1531216:ℝ), (4800960:ℝ), (-6350848:ℝ), ((12025856:ℝ)/3), (-1048576:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_11 q| ≤ ((610297920186770974321891:ℝ)/1464843750) := by
    rw [centralNum13_11_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((49:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-4074:ℝ), (159906:ℝ), (-1104799:ℝ), (2801499:ℝ), (-3931375:ℝ), ((5896250:ℝ)/3), (-250000:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_11 q| ≤ ((60393364573657292424331:ℝ)/375000000) := by
    rw [centralNum23_11_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((41688350428296700364775326827:ℝ)/20000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece21_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece21_E11 h0) m23'
  have c5 := scaled_affine (X := ((11:ℝ)/1000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1))| ≤ ((7043515281213901225888768000:ℝ)/1724237998317385726545541862428797) := by
    rw [abs_neg, tailWeight_1, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((49:ℝ)/10)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((49:ℝ)/10)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece21_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((4814744136400:ℝ)/531441)) ≤ ((49:ℝ)/10)^6*(8000*(2*((49:ℝ)/10)-3)^2*(1/((22711205925439889067307176219:ℝ)/2000000))*((4814744136400:ℝ)/531441)) := by
          gcongr
      _ ≤ ((7043515281213901225888768000:ℝ)/1724237998317385726545541862428797) := by norm_num
  have c7 := affine_round (α := ((218529372521118221:ℝ)/12000000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((-6946344387852983770680431:ℝ)/1536000000000000) + ((362703499022249257:ℝ)/16000000000)*((11:ℝ)/1000) - ((36885565739046663:ℝ)/2000000000)) (β := ((13808606292720883:ℝ)/400000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((-754557550546751102279387:ℝ)/25600000000000) - 3*((-6946344387852983770680431:ℝ)/1536000000000000)) + ((37001449430951109:ℝ)/800000000)*((11:ℝ)/1000) - ((174846156904578203:ℝ)/5000000000)) ht
  have hW : pieceW q pieceX_21 1 1 = centralNum11_11 q + 8*(Real.exp (-(3*((97:ℝ)/20)))*Real.exp (-3*t))*centralNum12_11 q + 18*Real.exp (-8*q)*centralNum13_11 q + 72*Real.exp (-11*q)*centralNum23_11 q + 8*q^7*(2*q-3)^2*((11:ℝ)/1000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1)) := by
    rw [pieceW_11, pieceX_21, sym4_11, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((843131069219098601679203063157073231983473131573546436296769:ℝ)/52137549734570786559821578754549156052995405747454063082776000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((218529372521118221:ℝ)/12000000000) + ((13808606292720883:ℝ)/400000000)*t) + (8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((-6946344387852983770680431:ℝ)/1536000000000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((-754557550546751102279387:ℝ)/25600000000000) - 3*((-6946344387852983770680431:ℝ)/1536000000000000))*t) + (((362703499022249257:ℝ)/16000000000) + ((37001449430951109:ℝ)/800000000)*t)*((11:ℝ)/1000) - (((36885565739046663:ℝ)/2000000000) + t * ((174846156904578203:ℝ)/5000000000)) = (((218529372521118221:ℝ)/12000000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((-6946344387852983770680431:ℝ)/1536000000000000) + ((362703499022249257:ℝ)/16000000000)*((11:ℝ)/1000) - ((36885565739046663:ℝ)/2000000000)) + t*(((13808606292720883:ℝ)/400000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((-754557550546751102279387:ℝ)/25600000000000) - 3*((-6946344387852983770680431:ℝ)/1536000000000000)) + ((37001449430951109:ℝ)/800000000)*((11:ℝ)/1000) - ((174846156904578203:ℝ)/5000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece21_e12 {q : ℝ} (h0 : ((24:ℝ)/5) ≤ q) (h1 : q ≤ ((49:ℝ)/10)) :
    |pieceW q pieceX_21 1 2 - (((-126786782192424301:ℝ)/100000000000) + (q - ((97:ℝ)/20)) * ((-189270602460902181:ℝ)/100000000000))| ≤ ((40544866253825709:ℝ)/2500000000000) := by
  set t := q - ((97:ℝ)/20) with htd
  have hq : q = ((97:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece21_L3 piece21_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((97:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_12 q = ∑ e ∈ Finset.range 9, ([((-2957883589502879:ℝ)/1920000000), ((-42825065861659:ℝ)/24000000), ((-790300891487:ℝ)/1200000), ((1324288523:ℝ)/60000), ((108231727:ℝ)/1200), ((4540667:ℝ)/150), ((72866:ℝ)/15), ((1192:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_12; ring
  have h12 : centralNum12_12 q = ∑ e ∈ Finset.range 14, ([((17461660358121307668834111557:ℝ)/245760000000000000), ((568104544921304290093755097:ℝ)/3072000000000000), ((30599407220771470315649951:ℝ)/153600000000000), ((1650404848716184762074857:ℝ)/15360000000000), ((6188275231130600478901:ℝ)/307200000000), ((-439309885863815582419:ℝ)/38400000000), ((-154262870153704927:ℝ)/15000000), ((-195548262281088179:ℝ)/48000000), ((-9805777307567641:ℝ)/9600000), ((-696307552343:ℝ)/4000), ((-40529222421:ℝ)/2000), ((-310338513:ℝ)/200), ((-1414503:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_12; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-2957883589502879:ℝ)/1920000000), ((-42825065861659:ℝ)/24000000), ((-790300891487:ℝ)/1200000), ((1324288523:ℝ)/60000), ((108231727:ℝ)/1200), ((4540667:ℝ)/150), ((72866:ℝ)/15), ((1192:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((17461660358121307668834111557:ℝ)/245760000000000000), ((568104544921304290093755097:ℝ)/3072000000000000), ((30599407220771470315649951:ℝ)/153600000000000), ((1650404848716184762074857:ℝ)/15360000000000), ((6188275231130600478901:ℝ)/307200000000), ((-439309885863815582419:ℝ)/38400000000), ((-154262870153704927:ℝ)/15000000), ((-195548262281088179:ℝ)/48000000), ((-9805777307567641:ℝ)/9600000), ((-696307552343:ℝ)/4000), ((-40529222421:ℝ)/2000), ((-310338513:ℝ)/200), ((-1414503:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((17461660358121307668834111557:ℝ)/245760000000000000), ((568104544921304290093755097:ℝ)/3072000000000000), ((30599407220771470315649951:ℝ)/153600000000000), ((1650404848716184762074857:ℝ)/15360000000000), ((6188275231130600478901:ℝ)/307200000000), ((-439309885863815582419:ℝ)/38400000000), ((-154262870153704927:ℝ)/15000000), ((-195548262281088179:ℝ)/48000000), ((-9805777307567641:ℝ)/9600000), ((-696307552343:ℝ)/4000), ((-40529222421:ℝ)/2000), ((-310338513:ℝ)/200), ((-1414503:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((-2957883589502879:ℝ)/1920000000), ((-42825065861659:ℝ)/24000000), ((-790300891487:ℝ)/1200000), ((1324288523:ℝ)/60000), ((108231727:ℝ)/1200), ((4540667:ℝ)/150), ((72866:ℝ)/15), ((1192:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((-2957883589502879:ℝ)/1920000000) + ((-42825065861659:ℝ)/24000000)*t)| ≤ ((3167601346307:ℝ)/1920000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((17461660358121307668834111557:ℝ)/245760000000000000), ((568104544921304290093755097:ℝ)/3072000000000000), ((30599407220771470315649951:ℝ)/153600000000000), ((1650404848716184762074857:ℝ)/15360000000000), ((6188275231130600478901:ℝ)/307200000000), ((-439309885863815582419:ℝ)/38400000000), ((-154262870153704927:ℝ)/15000000), ((-195548262281088179:ℝ)/48000000), ((-9805777307567641:ℝ)/9600000), ((-696307552343:ℝ)/4000), ((-40529222421:ℝ)/2000), ((-310338513:ℝ)/200), ((-1414503:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e) - ((17461660358121307668834111557:ℝ)/245760000000000000) - ((568104544921304290093755097:ℝ)/3072000000000000)*t| ≤ ((125730298859823262323919703:ℝ)/245760000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((17461660358121307668834111557:ℝ)/245760000000000000), ((568104544921304290093755097:ℝ)/3072000000000000), ((30599407220771470315649951:ℝ)/153600000000000), ((1650404848716184762074857:ℝ)/15360000000000), ((6188275231130600478901:ℝ)/307200000000), ((-439309885863815582419:ℝ)/38400000000), ((-154262870153704927:ℝ)/15000000), ((-195548262281088179:ℝ)/48000000), ((-9805777307567641:ℝ)/9600000), ((-696307552343:ℝ)/4000), ((-40529222421:ℝ)/2000), ((-310338513:ℝ)/200), ((-1414503:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((77577378268227922232550983:ℝ)/960000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((362703499022249257:ℝ)/16000000000) - ((37001449430951109:ℝ)/800000000)*t| ≤ ((858149060041481:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((49:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (122790:ℝ), (-3586680:ℝ), (28529720:ℝ), (-90761600:ℝ), (137804800:ℝ), ((-332136448:ℝ)/3), ((141819904:ℝ)/3), (-8388608:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_12 q| ≤ ((164920992457488348498100271:ℝ)/7324218750) := by
    rw [centralNum13_12_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((49:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (132555:ℝ), (-3252375:ℝ), ((39743695:ℝ)/2), ((-197111615:ℝ)/4), ((281947375:ℝ)/4), ((-1100234375:ℝ)/24), ((131828125:ℝ)/12), (-781250:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_12 q| ≤ ((12671835124273289030860801:ℝ)/2400000000) := by
    rw [centralNum23_12_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((41688350428296700364775326827:ℝ)/20000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece21_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece21_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-2957883589502879:ℝ)/1920000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((17461660358121307668834111557:ℝ)/245760000000000000) + ((362703499022249257:ℝ)/16000000000)*(0:ℝ) - ((-126786782192424301:ℝ)/100000000000)) (β := ((-42825065861659:ℝ)/24000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((568104544921304290093755097:ℝ)/3072000000000000) - 3*((17461660358121307668834111557:ℝ)/245760000000000000)) + ((37001449430951109:ℝ)/800000000)*(0:ℝ) - ((-189270602460902181:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_21 1 2 = centralNum11_12 q + 8*(Real.exp (-(3*((97:ℝ)/20)))*Real.exp (-3*t))*centralNum12_12 q + 18*Real.exp (-8*q)*centralNum13_12 q + 72*Real.exp (-11*q)*centralNum23_12 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_12, pieceX_21, sym4_12, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((11331141995039472493410737348554558743800990454261879323879:ℝ)/6517193716821348319977697344318644506624425718431757885347000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-2957883589502879:ℝ)/1920000000) + ((-42825065861659:ℝ)/24000000)*t) + (8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((17461660358121307668834111557:ℝ)/245760000000000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((568104544921304290093755097:ℝ)/3072000000000000) - 3*((17461660358121307668834111557:ℝ)/245760000000000000))*t) + (((362703499022249257:ℝ)/16000000000) + ((37001449430951109:ℝ)/800000000)*t)*(0:ℝ) - (((-126786782192424301:ℝ)/100000000000) + t * ((-189270602460902181:ℝ)/100000000000)) = (((-2957883589502879:ℝ)/1920000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((17461660358121307668834111557:ℝ)/245760000000000000) + ((362703499022249257:ℝ)/16000000000)*(0:ℝ) - ((-126786782192424301:ℝ)/100000000000)) + t*(((-42825065861659:ℝ)/24000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((568104544921304290093755097:ℝ)/3072000000000000) - 3*((17461660358121307668834111557:ℝ)/245760000000000000)) + ((37001449430951109:ℝ)/800000000)*(0:ℝ) - ((-189270602460902181:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece21_e13 {q : ℝ} (h0 : ((24:ℝ)/5) ≤ q) (h1 : q ≤ ((49:ℝ)/10)) :
    |pieceW q pieceX_21 1 3 - (((-235960914797393777:ℝ)/250000000000) + (q - ((97:ℝ)/20)) * ((-9820755980322201:ℝ)/25000000000))| ≤ ((172953316742143789:ℝ)/20000000000000) := by
  set t := q - ((97:ℝ)/20) with htd
  have hq : q = ((97:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece21_L3 piece21_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((97:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_13 q = ∑ e ∈ Finset.range 7, ([((-2498916014787:ℝ)/3200000), ((-77286062313:ℝ)/80000), ((-796763529:ℝ)/1600), ((-2738019:ℝ)/20), ((-84681:ℝ)/4), (-1746:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_13; ring
  have h12 : centralNum12_13 q = ∑ e ∈ Finset.range 15, ([((-973755985986219087151670199453:ℝ)/22937600000000000000), ((3605003435126932571753682717:ℝ)/163840000000000000), ((400866656208872481048972189:ℝ)/1792000000000000), ((471686109260134135668141153:ℝ)/1433600000000000), ((35553497791858545541760997:ℝ)/143360000000000), ((809889942753846424246017:ℝ)/7168000000000), ((5607229642137854916567:ℝ)/179200000000), ((18510045144428853507:ℝ)/4480000000), ((-56127264237995637:ℝ)/128000000), ((-15000860342309283:ℝ)/44800000), ((-43774330322043:ℝ)/560000), ((-595827896247:ℝ)/56000), ((-5012485173:ℝ)/5600), ((-12166281:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_13; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-2498916014787:ℝ)/3200000), ((-77286062313:ℝ)/80000), ((-796763529:ℝ)/1600), ((-2738019:ℝ)/20), ((-84681:ℝ)/4), (-1746:ℝ), (-60:ℝ)] : List ℝ).getD e 0) 5 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-973755985986219087151670199453:ℝ)/22937600000000000000), ((3605003435126932571753682717:ℝ)/163840000000000000), ((400866656208872481048972189:ℝ)/1792000000000000), ((471686109260134135668141153:ℝ)/1433600000000000), ((35553497791858545541760997:ℝ)/143360000000000), ((809889942753846424246017:ℝ)/7168000000000), ((5607229642137854916567:ℝ)/179200000000), ((18510045144428853507:ℝ)/4480000000), ((-56127264237995637:ℝ)/128000000), ((-15000860342309283:ℝ)/44800000), ((-43774330322043:ℝ)/560000), ((-595827896247:ℝ)/56000), ((-5012485173:ℝ)/5600), ((-12166281:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-973755985986219087151670199453:ℝ)/22937600000000000000), ((3605003435126932571753682717:ℝ)/163840000000000000), ((400866656208872481048972189:ℝ)/1792000000000000), ((471686109260134135668141153:ℝ)/1433600000000000), ((35553497791858545541760997:ℝ)/143360000000000), ((809889942753846424246017:ℝ)/7168000000000), ((5607229642137854916567:ℝ)/179200000000), ((18510045144428853507:ℝ)/4480000000), ((-56127264237995637:ℝ)/128000000), ((-15000860342309283:ℝ)/44800000), ((-43774330322043:ℝ)/560000), ((-595827896247:ℝ)/56000), ((-5012485173:ℝ)/5600), ((-12166281:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 7, ([((-2498916014787:ℝ)/3200000), ((-77286062313:ℝ)/80000), ((-796763529:ℝ)/1600), ((-2738019:ℝ)/20), ((-84681:ℝ)/4), (-1746:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e) - (((-2498916014787:ℝ)/3200000) + ((-77286062313:ℝ)/80000)*t)| ≤ ((4039003179:ℝ)/3200000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-973755985986219087151670199453:ℝ)/22937600000000000000), ((3605003435126932571753682717:ℝ)/163840000000000000), ((400866656208872481048972189:ℝ)/1792000000000000), ((471686109260134135668141153:ℝ)/1433600000000000), ((35553497791858545541760997:ℝ)/143360000000000), ((809889942753846424246017:ℝ)/7168000000000), ((5607229642137854916567:ℝ)/179200000000), ((18510045144428853507:ℝ)/4480000000), ((-56127264237995637:ℝ)/128000000), ((-15000860342309283:ℝ)/44800000), ((-43774330322043:ℝ)/560000), ((-595827896247:ℝ)/56000), ((-5012485173:ℝ)/5600), ((-12166281:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((-973755985986219087151670199453:ℝ)/22937600000000000000) - ((3605003435126932571753682717:ℝ)/163840000000000000)*t| ≤ ((6903739946923166457152335257:ℝ)/11468800000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-973755985986219087151670199453:ℝ)/22937600000000000000), ((3605003435126932571753682717:ℝ)/163840000000000000), ((400866656208872481048972189:ℝ)/1792000000000000), ((471686109260134135668141153:ℝ)/1433600000000000), ((35553497791858545541760997:ℝ)/143360000000000), ((809889942753846424246017:ℝ)/7168000000000), ((5607229642137854916567:ℝ)/179200000000), ((18510045144428853507:ℝ)/4480000000), ((-56127264237995637:ℝ)/128000000), ((-15000860342309283:ℝ)/44800000), ((-43774330322043:ℝ)/560000), ((-595827896247:ℝ)/56000), ((-5012485173:ℝ)/5600), ((-12166281:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((506399244962976974034125324493:ℝ)/11468800000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((362703499022249257:ℝ)/16000000000) - ((37001449430951109:ℝ)/800000000)*t| ≤ ((858149060041481:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((49:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2325540:ℝ), (52589280:ℝ), (-375655200:ℝ), (1192958720:ℝ), (-1965096960:ℝ), ((12857851904:ℝ)/7), ((-21171273728:ℝ)/21), ((914358272:ℝ)/3), ((-268435456:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_13 q| ≤ ((218327459305242124106054947021:ℝ)/292968750000) := by
    rw [centralNum13_13_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((49:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2399070:ℝ), (45666930:ℝ), (-251781675:ℝ), ((2452738385:ℝ)/4), ((-14104310625:ℝ)/16), ((74345740625:ℝ)/112), ((-74899765625:ℝ)/336), ((5161328125:ℝ)/168), ((-9765625:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_13 q| ≤ ((16805511412223100765809009:ℝ)/150000000) := by
    rw [centralNum23_13_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((41688350428296700364775326827:ℝ)/20000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece21_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece21_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-2498916014787:ℝ)/3200000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((-973755985986219087151670199453:ℝ)/22937600000000000000) + ((362703499022249257:ℝ)/16000000000)*(0:ℝ) - ((-235960914797393777:ℝ)/250000000000)) (β := ((-77286062313:ℝ)/80000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((3605003435126932571753682717:ℝ)/163840000000000000) - 3*((-973755985986219087151670199453:ℝ)/22937600000000000000)) + ((37001449430951109:ℝ)/800000000)*(0:ℝ) - ((-9820755980322201:ℝ)/25000000000)) ht
  have hW : pieceW q pieceX_21 1 3 = centralNum11_13 q + 8*(Real.exp (-(3*((97:ℝ)/20)))*Real.exp (-3*t))*centralNum12_13 q + 18*Real.exp (-8*q)*centralNum13_13 q + 72*Real.exp (-11*q)*centralNum23_13 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_13, pieceX_21, sym4_13, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((707247033379053781891645680873986288200889112008188891243:ℝ)/2534464223208302124435771189457250641465054446056794733190500000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-2498916014787:ℝ)/3200000) + ((-77286062313:ℝ)/80000)*t) + (8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((-973755985986219087151670199453:ℝ)/22937600000000000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((3605003435126932571753682717:ℝ)/163840000000000000) - 3*((-973755985986219087151670199453:ℝ)/22937600000000000000))*t) + (((362703499022249257:ℝ)/16000000000) + ((37001449430951109:ℝ)/800000000)*t)*(0:ℝ) - (((-235960914797393777:ℝ)/250000000000) + t * ((-9820755980322201:ℝ)/25000000000)) = (((-2498916014787:ℝ)/3200000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((-973755985986219087151670199453:ℝ)/22937600000000000000) + ((362703499022249257:ℝ)/16000000000)*(0:ℝ) - ((-235960914797393777:ℝ)/250000000000)) + t*(((-77286062313:ℝ)/80000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((3605003435126932571753682717:ℝ)/163840000000000000) - 3*((-973755985986219087151670199453:ℝ)/22937600000000000000)) + ((37001449430951109:ℝ)/800000000)*(0:ℝ) - ((-9820755980322201:ℝ)/25000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece21_e22 {q : ℝ} (h0 : ((24:ℝ)/5) ≤ q) (h1 : q ≤ ((49:ℝ)/10)) :
    |pieceW q pieceX_21 2 2 - (((20505383837684273:ℝ)/1250000000) + (q - ((97:ℝ)/20)) * ((172301615617606159:ℝ)/5000000000))| ≤ ((473060344230871171:ℝ)/5000000000000) := by
  set t := q - ((97:ℝ)/20) with htd
  have hq : q = ((97:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece21_L3 piece21_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((97:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_22 q = ∑ e ∈ Finset.range 10, ([((320194876649060707:ℝ)/19200000000), ((31587025163775409:ℝ)/960000000), ((347797976023387:ℝ)/12000000), ((3001725767493:ℝ)/200000), ((302805545341:ℝ)/60000), ((3432591163:ℝ)/3000), ((4373701:ℝ)/25), ((260764:ℝ)/15), ((3052:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_22; ring
  have h12 : centralNum12_22 q = ∑ e ∈ Finset.range 15, ([((-5346709785464442095824232539879:ℝ)/39321600000000000000), ((-264945343088263468222989229423:ℝ)/1966080000000000000), ((1145290515972341554676745119:ℝ)/6144000000000000), ((365528773810431739686921113:ℝ)/819200000000000), ((96429552796264731847994191:ℝ)/245760000000000), ((2423930040165409285037731:ℝ)/12288000000000), ((6215083792507027348487:ℝ)/102400000000), ((78373335148077435761:ℝ)/7680000000), ((90758138902316183:ℝ)/1536000000), ((-33469840986736249:ℝ)/76800000), ((-37909804033983:ℝ)/320000), ((-549169756767:ℝ)/32000), ((-4792709493:ℝ)/3200), ((-11933001:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_22; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((320194876649060707:ℝ)/19200000000), ((31587025163775409:ℝ)/960000000), ((347797976023387:ℝ)/12000000), ((3001725767493:ℝ)/200000), ((302805545341:ℝ)/60000), ((3432591163:ℝ)/3000), ((4373701:ℝ)/25), ((260764:ℝ)/15), ((3052:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-5346709785464442095824232539879:ℝ)/39321600000000000000), ((-264945343088263468222989229423:ℝ)/1966080000000000000), ((1145290515972341554676745119:ℝ)/6144000000000000), ((365528773810431739686921113:ℝ)/819200000000000), ((96429552796264731847994191:ℝ)/245760000000000), ((2423930040165409285037731:ℝ)/12288000000000), ((6215083792507027348487:ℝ)/102400000000), ((78373335148077435761:ℝ)/7680000000), ((90758138902316183:ℝ)/1536000000), ((-33469840986736249:ℝ)/76800000), ((-37909804033983:ℝ)/320000), ((-549169756767:ℝ)/32000), ((-4792709493:ℝ)/3200), ((-11933001:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-5346709785464442095824232539879:ℝ)/39321600000000000000), ((-264945343088263468222989229423:ℝ)/1966080000000000000), ((1145290515972341554676745119:ℝ)/6144000000000000), ((365528773810431739686921113:ℝ)/819200000000000), ((96429552796264731847994191:ℝ)/245760000000000), ((2423930040165409285037731:ℝ)/12288000000000), ((6215083792507027348487:ℝ)/102400000000), ((78373335148077435761:ℝ)/7680000000), ((90758138902316183:ℝ)/1536000000), ((-33469840986736249:ℝ)/76800000), ((-37909804033983:ℝ)/320000), ((-549169756767:ℝ)/32000), ((-4792709493:ℝ)/3200), ((-11933001:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((320194876649060707:ℝ)/19200000000), ((31587025163775409:ℝ)/960000000), ((347797976023387:ℝ)/12000000), ((3001725767493:ℝ)/200000), ((302805545341:ℝ)/60000), ((3432591163:ℝ)/3000), ((4373701:ℝ)/25), ((260764:ℝ)/15), ((3052:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((320194876649060707:ℝ)/19200000000) + ((31587025163775409:ℝ)/960000000)*t)| ≤ ((356956285580603:ℝ)/4800000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-5346709785464442095824232539879:ℝ)/39321600000000000000), ((-264945343088263468222989229423:ℝ)/1966080000000000000), ((1145290515972341554676745119:ℝ)/6144000000000000), ((365528773810431739686921113:ℝ)/819200000000000), ((96429552796264731847994191:ℝ)/245760000000000), ((2423930040165409285037731:ℝ)/12288000000000), ((6215083792507027348487:ℝ)/102400000000), ((78373335148077435761:ℝ)/7680000000), ((90758138902316183:ℝ)/1536000000), ((-33469840986736249:ℝ)/76800000), ((-37909804033983:ℝ)/320000), ((-549169756767:ℝ)/32000), ((-4792709493:ℝ)/3200), ((-11933001:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e) - ((-5346709785464442095824232539879:ℝ)/39321600000000000000) - ((-264945343088263468222989229423:ℝ)/1966080000000000000)*t| ≤ ((1718059332114772274627190179:ℝ)/3276800000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-5346709785464442095824232539879:ℝ)/39321600000000000000), ((-264945343088263468222989229423:ℝ)/1966080000000000000), ((1145290515972341554676745119:ℝ)/6144000000000000), ((365528773810431739686921113:ℝ)/819200000000000), ((96429552796264731847994191:ℝ)/245760000000000), ((2423930040165409285037731:ℝ)/12288000000000), ((6215083792507027348487:ℝ)/102400000000), ((78373335148077435761:ℝ)/7680000000), ((90758138902316183:ℝ)/1536000000), ((-33469840986736249:ℝ)/76800000), ((-37909804033983:ℝ)/320000), ((-549169756767:ℝ)/32000), ((-4792709493:ℝ)/3200), ((-11933001:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e)| ≤ ((112645436810761656626854961029:ℝ)/786432000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((362703499022249257:ℝ)/16000000000) - ((37001449430951109:ℝ)/800000000)*t| ≤ ((858149060041481:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((49:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82125:ℝ), (-6663750:ℝ), (115666200:ℝ), (-750437000:ℝ), (2277262000:ℝ), (-3656824320:ℝ), (3359621120:ℝ), (-1817706496:ℝ), ((1625292800:ℝ)/3), (-67108864:ℝ)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_22 q| ≤ ((389651304387863607772884312083:ℝ)/292968750000) := by
    rw [centralNum13_22_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((49:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((178425:ℝ)/2), ((-13176075:ℝ)/2), ((777815145:ℝ)/8), ((-3968389015:ℝ)/8), ((9393350195:ℝ)/8), ((-26366634375:ℝ)/16), ((77851609375:ℝ)/64), ((-25714921875:ℝ)/64), ((5236328125:ℝ)/96), ((-9765625:ℝ)/4)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_22 q| ≤ ((1941155346547118041133987221:ℝ)/9600000000) := by
    rw [centralNum23_22_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((41688350428296700364775326827:ℝ)/20000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece21_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece21_E11 h0) m23'
  have c5 := scaled_affine (X := ((11:ℝ)/1000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2))| ≤ ((3760297349347270308207312640000:ℝ)/15518141984856471538909876761859173) := by
    rw [abs_neg, tailWeight_2, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((49:ℝ)/10)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((49:ℝ)/10)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece21_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((2570430941234500:ℝ)/4782969)) ≤ ((49:ℝ)/10)^6*(8000*(2*((49:ℝ)/10)-3)^2*(1/((22711205925439889067307176219:ℝ)/2000000))*((2570430941234500:ℝ)/4782969)) := by
          gcongr
      _ ≤ ((3760297349347270308207312640000:ℝ)/15518141984856471538909876761859173) := by norm_num
  have c7 := affine_round (α := ((320194876649060707:ℝ)/19200000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((-5346709785464442095824232539879:ℝ)/39321600000000000000) + ((362703499022249257:ℝ)/16000000000)*((11:ℝ)/1000) - ((20505383837684273:ℝ)/1250000000)) (β := ((31587025163775409:ℝ)/960000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((-264945343088263468222989229423:ℝ)/1966080000000000000) - 3*((-5346709785464442095824232539879:ℝ)/39321600000000000000)) + ((37001449430951109:ℝ)/800000000)*((11:ℝ)/1000) - ((172301615617606159:ℝ)/5000000000)) ht
  have hW : pieceW q pieceX_21 2 2 = centralNum11_22 q + 8*(Real.exp (-(3*((97:ℝ)/20)))*Real.exp (-3*t))*centralNum12_22 q + 18*Real.exp (-8*q)*centralNum13_22 q + 72*Real.exp (-11*q)*centralNum23_22 q + 8*q^7*(2*q-3)^2*((11:ℝ)/1000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2)) := by
    rw [pieceW_22, pieceX_21, sym4_22, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((1041219185326869429236912399389842673610069619717017926643729:ℝ)/52137549734570786559821578754549156052995405747454063082776000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((320194876649060707:ℝ)/19200000000) + ((31587025163775409:ℝ)/960000000)*t) + (8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((-5346709785464442095824232539879:ℝ)/39321600000000000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((-264945343088263468222989229423:ℝ)/1966080000000000000) - 3*((-5346709785464442095824232539879:ℝ)/39321600000000000000))*t) + (((362703499022249257:ℝ)/16000000000) + ((37001449430951109:ℝ)/800000000)*t)*((11:ℝ)/1000) - (((20505383837684273:ℝ)/1250000000) + t * ((172301615617606159:ℝ)/5000000000)) = (((320194876649060707:ℝ)/19200000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((-5346709785464442095824232539879:ℝ)/39321600000000000000) + ((362703499022249257:ℝ)/16000000000)*((11:ℝ)/1000) - ((20505383837684273:ℝ)/1250000000)) + t*(((31587025163775409:ℝ)/960000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((-264945343088263468222989229423:ℝ)/1966080000000000000) - 3*((-5346709785464442095824232539879:ℝ)/39321600000000000000)) + ((37001449430951109:ℝ)/800000000)*((11:ℝ)/1000) - ((172301615617606159:ℝ)/5000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece21_e23 {q : ℝ} (h0 : ((24:ℝ)/5) ≤ q) (h1 : q ≤ ((49:ℝ)/10)) :
    |pieceW q pieceX_21 2 3 - (((125279615204833441:ℝ)/50000000000) + (q - ((97:ℝ)/20)) * ((184647328852151293:ℝ)/50000000000))| ≤ ((113899173350059451:ℝ)/1000000000000) := by
  set t := q - ((97:ℝ)/20) with htd
  have hq : q = ((97:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece21_L3 piece21_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((97:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_23 q = ∑ e ∈ Finset.range 9, ([((538142851885419:ℝ)/160000000), ((183923919212269:ℝ)/32000000), ((7302697336447:ℝ)/1600000), ((174348892317:ℝ)/80000), ((539241139:ℝ)/800), ((27235583:ℝ)/200), ((173397:ℝ)/10), (1262:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_23; ring
  have h12 : centralNum12_23 q = ∑ e ∈ Finset.range 16, ([((-820255141781819150010657284611809:ℝ)/3670016000000000000000), ((-22127547389458507107864953767627:ℝ)/18350080000000000000), ((-3885832209503430570303394424777:ℝ)/1835008000000000000), ((-16980365518080038519713824099:ℝ)/9175040000000000), ((-4004388665972257266468046081:ℝ)/4587520000000000), ((-96321236201811432532587463:ℝ)/573440000000000), ((549680427902999528132211:ℝ)/11468800000000), ((12418425391862587515209:ℝ)/286720000000), ((81077405014766323973:ℝ)/5734400000), ((1800173891440886487:ℝ)/716800000), ((68365625069482137:ℝ)/358400000), ((-32064569794053:ℝ)/1792000), ((-1144931951403:ℝ)/179200), ((-667277757:ℝ)/896), ((-19413999:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_23; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((538142851885419:ℝ)/160000000), ((183923919212269:ℝ)/32000000), ((7302697336447:ℝ)/1600000), ((174348892317:ℝ)/80000), ((539241139:ℝ)/800), ((27235583:ℝ)/200), ((173397:ℝ)/10), (1262:ℝ), (40:ℝ)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-820255141781819150010657284611809:ℝ)/3670016000000000000000), ((-22127547389458507107864953767627:ℝ)/18350080000000000000), ((-3885832209503430570303394424777:ℝ)/1835008000000000000), ((-16980365518080038519713824099:ℝ)/9175040000000000), ((-4004388665972257266468046081:ℝ)/4587520000000000), ((-96321236201811432532587463:ℝ)/573440000000000), ((549680427902999528132211:ℝ)/11468800000000), ((12418425391862587515209:ℝ)/286720000000), ((81077405014766323973:ℝ)/5734400000), ((1800173891440886487:ℝ)/716800000), ((68365625069482137:ℝ)/358400000), ((-32064569794053:ℝ)/1792000), ((-1144931951403:ℝ)/179200), ((-667277757:ℝ)/896), ((-19413999:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 14 ht
  have m12 := abs_poly_le (fun e => ([((-820255141781819150010657284611809:ℝ)/3670016000000000000000), ((-22127547389458507107864953767627:ℝ)/18350080000000000000), ((-3885832209503430570303394424777:ℝ)/1835008000000000000), ((-16980365518080038519713824099:ℝ)/9175040000000000), ((-4004388665972257266468046081:ℝ)/4587520000000000), ((-96321236201811432532587463:ℝ)/573440000000000), ((549680427902999528132211:ℝ)/11468800000000), ((12418425391862587515209:ℝ)/286720000000), ((81077405014766323973:ℝ)/5734400000), ((1800173891440886487:ℝ)/716800000), ((68365625069482137:ℝ)/358400000), ((-32064569794053:ℝ)/1792000), ((-1144931951403:ℝ)/179200), ((-667277757:ℝ)/896), ((-19413999:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 16 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((538142851885419:ℝ)/160000000), ((183923919212269:ℝ)/32000000), ((7302697336447:ℝ)/1600000), ((174348892317:ℝ)/80000), ((539241139:ℝ)/800), ((27235583:ℝ)/200), ((173397:ℝ)/10), (1262:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e) - (((538142851885419:ℝ)/160000000) + ((183923919212269:ℝ)/32000000)*t)| ≤ ((7479769844071:ℝ)/640000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 16, ([((-820255141781819150010657284611809:ℝ)/3670016000000000000000), ((-22127547389458507107864953767627:ℝ)/18350080000000000000), ((-3885832209503430570303394424777:ℝ)/1835008000000000000), ((-16980365518080038519713824099:ℝ)/9175040000000000), ((-4004388665972257266468046081:ℝ)/4587520000000000), ((-96321236201811432532587463:ℝ)/573440000000000), ((549680427902999528132211:ℝ)/11468800000000), ((12418425391862587515209:ℝ)/286720000000), ((81077405014766323973:ℝ)/5734400000), ((1800173891440886487:ℝ)/716800000), ((68365625069482137:ℝ)/358400000), ((-32064569794053:ℝ)/1792000), ((-1144931951403:ℝ)/179200), ((-667277757:ℝ)/896), ((-19413999:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e) - ((-820255141781819150010657284611809:ℝ)/3670016000000000000000) - ((-22127547389458507107864953767627:ℝ)/18350080000000000000)*t| ≤ ((20298396783854818676636039767131:ℝ)/3670016000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 16, ([((-820255141781819150010657284611809:ℝ)/3670016000000000000000), ((-22127547389458507107864953767627:ℝ)/18350080000000000000), ((-3885832209503430570303394424777:ℝ)/1835008000000000000), ((-16980365518080038519713824099:ℝ)/9175040000000000), ((-4004388665972257266468046081:ℝ)/4587520000000000), ((-96321236201811432532587463:ℝ)/573440000000000), ((549680427902999528132211:ℝ)/11468800000000), ((12418425391862587515209:ℝ)/286720000000), ((81077405014766323973:ℝ)/5734400000), ((1800173891440886487:ℝ)/716800000), ((68365625069482137:ℝ)/358400000), ((-32064569794053:ℝ)/1792000), ((-1144931951403:ℝ)/179200), ((-667277757:ℝ)/896), ((-19413999:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e)| ≤ ((106182901246025903976594286205521:ℝ)/367001600000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((362703499022249257:ℝ)/16000000000) - ((37001449430951109:ℝ)/800000000)*t| ≤ ((858149060041481:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((49:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-7627725:ℝ)/2), (173988600:ℝ), (-2299614450:ℝ), (13088188200:ℝ), (-38221499200:ℝ), (63366115840:ℝ), ((-445610508288:ℝ)/7), ((841540698112:ℝ)/21), ((-326820167680:ℝ)/21), ((10133438464:ℝ)/3), ((-2147483648:ℝ)/7)] : List ℝ).getD e 0) 16 hq1'
  have m13' : |centralNum13_23 q| ≤ ((2917504465560759139960486336899:ℝ)/61035156250) := by
    rw [centralNum13_23_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((49:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-15801525:ℝ)/4), ((655493865:ℝ)/4), ((-7334421225:ℝ)/4), ((16442962485:ℝ)/2), ((-598626108395:ℝ)/32), ((414013307125:ℝ)/16), ((-4611984703125:ℝ)/224), ((399923828125:ℝ)/48), ((-4353201171875:ℝ)/2688), ((189736328125:ℝ)/1344), ((-244140625:ℝ)/56)] : List ℝ).getD e 0) 16 hq1'
  have m23' : |centralNum23_23 q| ≤ ((251337512467037651598261422783:ℝ)/51200000000) := by
    rw [centralNum23_23_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((41688350428296700364775326827:ℝ)/20000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece21_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece21_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((538142851885419:ℝ)/160000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((-820255141781819150010657284611809:ℝ)/3670016000000000000000) + ((362703499022249257:ℝ)/16000000000)*(0:ℝ) - ((125279615204833441:ℝ)/50000000000)) (β := ((183923919212269:ℝ)/32000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((-22127547389458507107864953767627:ℝ)/18350080000000000000) - 3*((-820255141781819150010657284611809:ℝ)/3670016000000000000000)) + ((37001449430951109:ℝ)/800000000)*(0:ℝ) - ((184647328852151293:ℝ)/50000000000)) ht
  have hW : pieceW q pieceX_21 2 3 = centralNum11_23 q + 8*(Real.exp (-(3*((97:ℝ)/20)))*Real.exp (-3*t))*centralNum12_23 q + 18*Real.exp (-8*q)*centralNum13_23 q + 72*Real.exp (-11*q)*centralNum23_23 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_23, pieceX_21, sym4_23, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((57314766587667952894451447647008617553573433174686660824341:ℝ)/15206785339249812746614627136743503848790326676340768399143000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((538142851885419:ℝ)/160000000) + ((183923919212269:ℝ)/32000000)*t) + (8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((-820255141781819150010657284611809:ℝ)/3670016000000000000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((-22127547389458507107864953767627:ℝ)/18350080000000000000) - 3*((-820255141781819150010657284611809:ℝ)/3670016000000000000000))*t) + (((362703499022249257:ℝ)/16000000000) + ((37001449430951109:ℝ)/800000000)*t)*(0:ℝ) - (((125279615204833441:ℝ)/50000000000) + t * ((184647328852151293:ℝ)/50000000000)) = (((538142851885419:ℝ)/160000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((-820255141781819150010657284611809:ℝ)/3670016000000000000000) + ((362703499022249257:ℝ)/16000000000)*(0:ℝ) - ((125279615204833441:ℝ)/50000000000)) + t*(((183923919212269:ℝ)/32000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((-22127547389458507107864953767627:ℝ)/18350080000000000000) - 3*((-820255141781819150010657284611809:ℝ)/3670016000000000000000)) + ((37001449430951109:ℝ)/800000000)*(0:ℝ) - ((184647328852151293:ℝ)/50000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece21_e33 {q : ℝ} (h0 : ((24:ℝ)/5) ≤ q) (h1 : q ≤ ((49:ℝ)/10)) :
    |pieceW q pieceX_21 3 3 - (((29873472152694593:ℝ)/2500000000) + (q - ((97:ℝ)/20)) * ((160104873981625721:ℝ)/10000000000))| ≤ ((21634407515385881:ℝ)/20000000000) := by
  set t := q - ((97:ℝ)/20) with htd
  have hq : q = ((97:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece21_L3 piece21_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((97:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_33 q = ∑ e ∈ Finset.range 10, ([((137003454904835377:ℝ)/22400000000), ((8175667106914107:ℝ)/560000000), ((825546528046113:ℝ)/56000000), ((3380522705283:ℝ)/400000), ((61557524601:ℝ)/20000), ((746766723:ℝ)/1000), ((6083661:ℝ)/50), ((451518:ℝ)/35), ((5664:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_33; ring
  have h12 : centralNum12_33 q = ∑ e ∈ Finset.range 17, ([((1495033399424251340765351108051403883:ℝ)/1027604480000000000000000), ((236334466205907268255786490504003409:ℝ)/51380224000000000000000), ((2759909546043460948569679545138093:ℝ)/513802240000000000000), ((9261749786828596933199610113871:ℝ)/3670016000000000000), ((-64857242411627379817255548549:ℝ)/183500800000000000), ((-50265346938873631483432921269:ℝ)/45875200000000000), ((-1457640133540194342579658917:ℝ)/2293760000000000), ((-30415322260280420689737387:ℝ)/160563200000000), ((-206377695378877568792433:ℝ)/8028160000000), ((839924752766708265767:ℝ)/401408000000), ((22787770121438504373:ℝ)/14336000000), ((213919423098814449:ℝ)/716800000), ((168309198238761:ℝ)/7168000), ((-211761158571:ℝ)/358400), ((-36103326237:ℝ)/125440), ((-733447629:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_33; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((137003454904835377:ℝ)/22400000000), ((8175667106914107:ℝ)/560000000), ((825546528046113:ℝ)/56000000), ((3380522705283:ℝ)/400000), ((61557524601:ℝ)/20000), ((746766723:ℝ)/1000), ((6083661:ℝ)/50), ((451518:ℝ)/35), ((5664:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((1495033399424251340765351108051403883:ℝ)/1027604480000000000000000), ((236334466205907268255786490504003409:ℝ)/51380224000000000000000), ((2759909546043460948569679545138093:ℝ)/513802240000000000000), ((9261749786828596933199610113871:ℝ)/3670016000000000000), ((-64857242411627379817255548549:ℝ)/183500800000000000), ((-50265346938873631483432921269:ℝ)/45875200000000000), ((-1457640133540194342579658917:ℝ)/2293760000000000), ((-30415322260280420689737387:ℝ)/160563200000000), ((-206377695378877568792433:ℝ)/8028160000000), ((839924752766708265767:ℝ)/401408000000), ((22787770121438504373:ℝ)/14336000000), ((213919423098814449:ℝ)/716800000), ((168309198238761:ℝ)/7168000), ((-211761158571:ℝ)/358400), ((-36103326237:ℝ)/125440), ((-733447629:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 15 ht
  have m12 := abs_poly_le (fun e => ([((1495033399424251340765351108051403883:ℝ)/1027604480000000000000000), ((236334466205907268255786490504003409:ℝ)/51380224000000000000000), ((2759909546043460948569679545138093:ℝ)/513802240000000000000), ((9261749786828596933199610113871:ℝ)/3670016000000000000), ((-64857242411627379817255548549:ℝ)/183500800000000000), ((-50265346938873631483432921269:ℝ)/45875200000000000), ((-1457640133540194342579658917:ℝ)/2293760000000000), ((-30415322260280420689737387:ℝ)/160563200000000), ((-206377695378877568792433:ℝ)/8028160000000), ((839924752766708265767:ℝ)/401408000000), ((22787770121438504373:ℝ)/14336000000), ((213919423098814449:ℝ)/716800000), ((168309198238761:ℝ)/7168000), ((-211761158571:ℝ)/358400), ((-36103326237:ℝ)/125440), ((-733447629:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 17 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((137003454904835377:ℝ)/22400000000), ((8175667106914107:ℝ)/560000000), ((825546528046113:ℝ)/56000000), ((3380522705283:ℝ)/400000), ((61557524601:ℝ)/20000), ((746766723:ℝ)/1000), ((6083661:ℝ)/50), ((451518:ℝ)/35), ((5664:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e) - (((137003454904835377:ℝ)/22400000000) + ((8175667106914107:ℝ)/560000000)*t)| ≤ ((849646359834457:ℝ)/22400000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 17, ([((1495033399424251340765351108051403883:ℝ)/1027604480000000000000000), ((236334466205907268255786490504003409:ℝ)/51380224000000000000000), ((2759909546043460948569679545138093:ℝ)/513802240000000000000), ((9261749786828596933199610113871:ℝ)/3670016000000000000), ((-64857242411627379817255548549:ℝ)/183500800000000000), ((-50265346938873631483432921269:ℝ)/45875200000000000), ((-1457640133540194342579658917:ℝ)/2293760000000000), ((-30415322260280420689737387:ℝ)/160563200000000), ((-206377695378877568792433:ℝ)/8028160000000), ((839924752766708265767:ℝ)/401408000000), ((22787770121438504373:ℝ)/14336000000), ((213919423098814449:ℝ)/716800000), ((168309198238761:ℝ)/7168000), ((-211761158571:ℝ)/358400), ((-36103326237:ℝ)/125440), ((-733447629:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e) - ((1495033399424251340765351108051403883:ℝ)/1027604480000000000000000) - ((236334466205907268255786490504003409:ℝ)/51380224000000000000000)*t| ≤ ((1765792648782884988796290192149309:ℝ)/128450560000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 17, ([((1495033399424251340765351108051403883:ℝ)/1027604480000000000000000), ((236334466205907268255786490504003409:ℝ)/51380224000000000000000), ((2759909546043460948569679545138093:ℝ)/513802240000000000000), ((9261749786828596933199610113871:ℝ)/3670016000000000000), ((-64857242411627379817255548549:ℝ)/183500800000000000), ((-50265346938873631483432921269:ℝ)/45875200000000000), ((-1457640133540194342579658917:ℝ)/2293760000000000), ((-30415322260280420689737387:ℝ)/160563200000000), ((-206377695378877568792433:ℝ)/8028160000000), ((839924752766708265767:ℝ)/401408000000), ((22787770121438504373:ℝ)/14336000000), ((213919423098814449:ℝ)/716800000), ((168309198238761:ℝ)/7168000), ((-211761158571:ℝ)/358400), ((-36103326237:ℝ)/125440), ((-733447629:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e)| ≤ ((436373551705105422232876980023150441:ℝ)/256901120000000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((362703499022249257:ℝ)/16000000000), ((37001449430951109:ℝ)/800000000), ((208955750473581:ℝ)/5000000), ((686013398469:ℝ)/31250), ((369465545841:ℝ)/50000), ((4132969113:ℝ)/2500), ((30734256:ℝ)/125), ((586128:ℝ)/25), ((6504:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((362703499022249257:ℝ)/16000000000) - ((37001449430951109:ℝ)/800000000)*t| ≤ ((858149060041481:ℝ)/8000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((49:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-8120475:ℝ)/4), ((464861025:ℝ)/2), (-5906535975:ℝ), ((411904731750:ℝ)/7), ((-2024051769000:ℝ)/7), ((5554394637600:ℝ)/7), (-1314913862656:ℝ), ((9709155336192:ℝ)/7), ((-6724555112448:ℝ)/7), ((1313173667840:ℝ)/3), ((-6168244125696:ℝ)/49), ((3004329623552:ℝ)/147), ((-68719476736:ℝ)/49)] : List ℝ).getD e 0) 17 hq1'
  have m13' : |centralNum13_33 q| ≤ ((27182407466682738094842661283180219:ℝ)/14648437500000) := by
    rw [centralNum13_33_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((49:ℝ)/10) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-16872075:ℝ)/8), ((1833754545:ℝ)/8), ((-83998007145:ℝ)/16), ((4929124002765:ℝ)/112), ((-76723155584685:ℝ)/448), ((164888745653055:ℝ)/448), ((-63358359907625:ℝ)/128), ((364713160040625:ℝ)/896), ((-334937462578125:ℝ)/1792), ((245466998046875:ℝ)/5376), ((-72144521484375:ℝ)/12544), ((6518798828125:ℝ)/18816), ((-6103515625:ℝ)/784)] : List ℝ).getD e 0) 17 hq1'
  have m23' : |centralNum23_33 q| ≤ ((41262630917991737236103690823793:ℝ)/307200000000) := by
    rw [centralNum23_33_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((41688350428296700364775326827:ℝ)/20000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece21_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece21_E11 h0) m23'
  have c5 := scaled_affine (X := ((11:ℝ)/1000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3))| ≤ ((4840127629130326964880090369280000:ℝ)/418989833591124731550566672570197671) := by
    rw [abs_neg, tailWeight_3, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((49:ℝ)/10)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((49:ℝ)/10)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece21_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((3308571812705231500:ℝ)/129140163)) ≤ ((49:ℝ)/10)^6*(8000*(2*((49:ℝ)/10)-3)^2*(1/((22711205925439889067307176219:ℝ)/2000000))*((3308571812705231500:ℝ)/129140163)) := by
          gcongr
      _ ≤ ((4840127629130326964880090369280000:ℝ)/418989833591124731550566672570197671) := by norm_num
  have c7 := affine_round (α := ((137003454904835377:ℝ)/22400000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((1495033399424251340765351108051403883:ℝ)/1027604480000000000000000) + ((362703499022249257:ℝ)/16000000000)*((11:ℝ)/1000) - ((29873472152694593:ℝ)/2500000000)) (β := ((8175667106914107:ℝ)/560000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((236334466205907268255786490504003409:ℝ)/51380224000000000000000) - 3*((1495033399424251340765351108051403883:ℝ)/1027604480000000000000000)) + ((37001449430951109:ℝ)/800000000)*((11:ℝ)/1000) - ((160104873981625721:ℝ)/10000000000)) ht
  have hW : pieceW q pieceX_21 3 3 = centralNum11_33 q + 8*(Real.exp (-(3*((97:ℝ)/20)))*Real.exp (-3*t))*centralNum12_33 q + 18*Real.exp (-8*q)*centralNum13_33 q + 72*Real.exp (-11*q)*centralNum23_33 q + 8*q^7*(2*q-3)^2*((11:ℝ)/1000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3)) := by
    rw [pieceW_33, pieceX_21, sym4_33, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((62831180186879219665715870788500553473007842749489175505973483:ℝ)/1703159957995979027620838239315272431064516587750166060704016000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((137003454904835377:ℝ)/22400000000) + ((8175667106914107:ℝ)/560000000)*t) + (8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((1495033399424251340765351108051403883:ℝ)/1027604480000000000000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((236334466205907268255786490504003409:ℝ)/51380224000000000000000) - 3*((1495033399424251340765351108051403883:ℝ)/1027604480000000000000000))*t) + (((362703499022249257:ℝ)/16000000000) + ((37001449430951109:ℝ)/800000000)*t)*((11:ℝ)/1000) - (((29873472152694593:ℝ)/2500000000) + t * ((160104873981625721:ℝ)/10000000000)) = (((137003454904835377:ℝ)/22400000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*((1495033399424251340765351108051403883:ℝ)/1027604480000000000000000) + ((362703499022249257:ℝ)/16000000000)*((11:ℝ)/1000) - ((29873472152694593:ℝ)/2500000000)) + t*(((8175667106914107:ℝ)/560000000) + 8*(((1/((41688350428296700364775326827:ℝ)/20000000000000000000000))+(1/((52110430930665053533393903587:ℝ)/25000000000000000000000)))/2)*(((236334466205907268255786490504003409:ℝ)/51380224000000000000000) - 3*((1495033399424251340765351108051403883:ℝ)/1027604480000000000000000)) + ((37001449430951109:ℝ)/800000000)*((11:ℝ)/1000) - ((160104873981625721:ℝ)/10000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece21_plus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((10375520234213723:ℝ)/400000000) + ((1:ℝ)/20)*((51141528937126551:ℝ)/1000000000) - (((57889656422598533:ℝ)/500000000000) + ((901142578634677493:ℝ)/100000000000000) + ((66386381693315307:ℝ)/20000000000000) + ((9995341624331629:ℝ)/2500000000000)))
      (((-76755207408217499:ℝ)/25000000000) + ((1:ℝ)/20)*((-87072931329524881:ℝ)/20000000000))
      (((-461768050010095133:ℝ)/10000000000000) + ((1:ℝ)/20)*((-316453849931450013:ℝ)/10000000000000))
      (((912376229289570983:ℝ)/10000000000000) + ((1:ℝ)/20)*((-891335023035063943:ℝ)/10000000000000))
      (((36885565739046663:ℝ)/2000000000) + ((1:ℝ)/20)*((174846156904578203:ℝ)/5000000000) - (((901142578634677493:ℝ)/100000000000000) + ((787306746876959571:ℝ)/10000000000000) + ((40544866253825709:ℝ)/2500000000000) + ((172953316742143789:ℝ)/20000000000000)))
      (((-126786782192424301:ℝ)/100000000000) + ((1:ℝ)/20)*((-189270602460902181:ℝ)/100000000000))
      (((-235960914797393777:ℝ)/250000000000) + ((1:ℝ)/20)*((-9820755980322201:ℝ)/25000000000))
      (((20505383837684273:ℝ)/1250000000) + ((1:ℝ)/20)*((172301615617606159:ℝ)/5000000000) - (((66386381693315307:ℝ)/20000000000000) + ((40544866253825709:ℝ)/2500000000000) + ((473060344230871171:ℝ)/5000000000000) + ((113899173350059451:ℝ)/1000000000000)))
      (((125279615204833441:ℝ)/50000000000) + ((1:ℝ)/20)*((184647328852151293:ℝ)/50000000000))
      (((29873472152694593:ℝ)/2500000000) + ((1:ℝ)/20)*((160104873981625721:ℝ)/10000000000) - (((9995341624331629:ℝ)/2500000000000) + ((172953316742143789:ℝ)/20000000000000) + ((113899173350059451:ℝ)/1000000000000) + ((21634407515385881:ℝ)/20000000000))) i j :=
  quadForm_nonneg_of_ldl ((709094220950617319803:ℝ)/25000000000000) ((23673541775947058750145234109262477269889:ℝ)/1201854611780707321700000000000000) ((9947117160695994937453470903465106920501674427842351427562649573:ℝ)/558695585912350586503427524978594463569380400000000000000) ((2209942221918280011192483729629863012874512761176922955604835820238750354963247947373:ℝ)/198942343213919898749069418069302138410033488556847028551252991460000000000000) ((-2786347986993654375:ℝ)/24037092235614146434) ((-9551814850133352673:ℝ)/5672753767604938558424) ((17356189562756355717:ℝ)/5672753767604938558424) ((-6576737328596149701932501807731526917775:ℝ)/94694167103788235000580936437049909079556) ((-4583516001466795230834933642197492156125:ℝ)/94694167103788235000580936437049909079556) ((1466111108917537054439686274896021878902118144803324672686573993:ℝ)/9947117160695994937453470903465106920501674427842351427562649573)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece21_minus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((10375520234213723:ℝ)/400000000) - ((1:ℝ)/20)*((51141528937126551:ℝ)/1000000000) - (((57889656422598533:ℝ)/500000000000) + ((901142578634677493:ℝ)/100000000000000) + ((66386381693315307:ℝ)/20000000000000) + ((9995341624331629:ℝ)/2500000000000)))
      (((-76755207408217499:ℝ)/25000000000) - ((1:ℝ)/20)*((-87072931329524881:ℝ)/20000000000))
      (((-461768050010095133:ℝ)/10000000000000) - ((1:ℝ)/20)*((-316453849931450013:ℝ)/10000000000000))
      (((912376229289570983:ℝ)/10000000000000) - ((1:ℝ)/20)*((-891335023035063943:ℝ)/10000000000000))
      (((36885565739046663:ℝ)/2000000000) - ((1:ℝ)/20)*((174846156904578203:ℝ)/5000000000) - (((901142578634677493:ℝ)/100000000000000) + ((787306746876959571:ℝ)/10000000000000) + ((40544866253825709:ℝ)/2500000000000) + ((172953316742143789:ℝ)/20000000000000)))
      (((-126786782192424301:ℝ)/100000000000) - ((1:ℝ)/20)*((-189270602460902181:ℝ)/100000000000))
      (((-235960914797393777:ℝ)/250000000000) - ((1:ℝ)/20)*((-9820755980322201:ℝ)/25000000000))
      (((20505383837684273:ℝ)/1250000000) - ((1:ℝ)/20)*((172301615617606159:ℝ)/5000000000) - (((66386381693315307:ℝ)/20000000000000) + ((40544866253825709:ℝ)/2500000000000) + ((473060344230871171:ℝ)/5000000000000) + ((113899173350059451:ℝ)/1000000000000)))
      (((125279615204833441:ℝ)/50000000000) - ((1:ℝ)/20)*((184647328852151293:ℝ)/50000000000))
      (((29873472152694593:ℝ)/2500000000) - ((1:ℝ)/20)*((160104873981625721:ℝ)/10000000000) - (((9995341624331629:ℝ)/2500000000000) + ((172953316742143789:ℝ)/20000000000000) + ((113899173350059451:ℝ)/1000000000000) + ((21634407515385881:ℝ)/20000000000))) i j :=
  quadForm_nonneg_of_ldl ((581240398607800942303:ℝ)/25000000000000) ((943453920534116209738153213949334447175451:ℝ)/58124039860780094230300000000000000) ((5422053317884900771700330781340499768944576816732174162042669433:ℝ)/377381568213646483895261285579733778870180400000000000000) ((1033988711598067635962225261525780013453257070135117792854951675479700238617193094813:ℝ)/108441066357698015434006615626809995378891536334643483240853388660000000000000) ((-142626298400244387875:ℝ)/1162480797215601884606) ((-8918907150270452647:ℝ)/4649923188862407538424) ((19138859608826483603:ℝ)/4649923188862407538424) ((-274044125907696420107729723564120536698525:ℝ)/3773815682136464838952612855797337788701804) ((-212143745078202816024210494977184962853575:ℝ)/3773815682136464838952612855797337788701804) ((850945656882387820754201236453215180144847115250045814784964393:ℝ)/5422053317884900771700330781340499768944576816732174162042669433)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

/-- **Piece 21.** The piece matrix is positive semidefinite on `q ∈ [24/5, 49/10]`. -/
theorem piece_21 {q : ℝ} (h0 : ((24:ℝ)/5) ≤ q) (h1 : q ≤ ((49:ℝ)/10)) (y : Fin 4 → ℝ) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceW q pieceX_21 i j :=
  pieceForm_nonneg (pieceW_symm (sym4_symm _ _ _ _ _ _ _ _ _ _) q) (by norm_num : (0:ℝ) < ((1:ℝ)/20))
    (abs_le.mpr ⟨by linarith, by linarith⟩)
    (piece21_e00 h0 h1) (piece21_e01 h0 h1) (piece21_e02 h0 h1) (piece21_e03 h0 h1) (piece21_e11 h0 h1) (piece21_e12 h0 h1) (piece21_e13 h0 h1) (piece21_e22 h0 h1) (piece21_e23 h0 h1) (piece21_e33 h0 h1)
    piece21_plus piece21_minus y

/-! #### Piece 22 (seam), `q ∈ [49/10, 5]` -/

/-- The compensation matrix of piece 22. -/
def pieceX_22 : Fin 4 → Fin 4 → ℝ :=
  sym4 ((11:ℝ)/1000) (0:ℝ) (0:ℝ) (0:ℝ) ((11:ℝ)/1000) (0:ℝ) (0:ℝ) ((11:ℝ)/1000) (0:ℝ) ((11:ℝ)/1000)

theorem piece22_L3 : ((281366035955653318118208556173:ℝ)/100000000000000000000000) ≤ Real.exp ((3:ℝ)*((99:ℝ)/20)) := by
  have h := le_exp_nat_add 14 (f := ((17:ℝ)/20)) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((99:ℝ)/20) = ((14:ℕ):ℝ) + ((17:ℝ)/20) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece22_U3 : Real.exp ((3:ℝ)*((99:ℝ)/20)) ≤ ((28136695072708953678387022961:ℝ)/10000000000000000000000) := by
  have h := exp_nat_add_le 14 (f := ((17:ℝ)/20)) (by norm_num) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((99:ℝ)/20) = ((14:ℕ):ℝ) + ((17:ℝ)/20) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem piece22_L8_at : ((42306167147747379767273151:ℝ)/400000000) ≤ Real.exp ((8:ℝ)*((49:ℝ)/10)) := by
  have h := le_exp_nat_add 39 (f := ((1:ℝ)/5)) (by norm_num)
  rw [show ((8:ℝ):ℝ)*((49:ℝ)/10) = ((39:ℕ):ℝ) + ((1:ℝ)/5) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece22_E8 {q : ℝ} (h0 : ((49:ℝ)/10) ≤ q) : Real.exp (-((8:ℝ))*q) ≤ 1/((42306167147747379767273151:ℝ)/400000000) := by
  have hm : Real.exp (-((8:ℝ))*q) ≤ Real.exp (-((8:ℝ)*((49:ℝ)/10))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece22_L8_at (le_refl _)).2

theorem piece22_L11_at : ((128067958168435491600149002539:ℝ)/500000) ≤ Real.exp ((11:ℝ)*((49:ℝ)/10)) := by
  have h := le_exp_nat_add 53 (f := ((9:ℝ)/10)) (by norm_num)
  rw [show ((11:ℝ):ℝ)*((49:ℝ)/10) = ((53:ℕ):ℝ) + ((9:ℝ)/10) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece22_E11 {q : ℝ} (h0 : ((49:ℝ)/10) ≤ q) : Real.exp (-((11:ℝ))*q) ≤ 1/((128067958168435491600149002539:ℝ)/500000) := by
  have hm : Real.exp (-((11:ℝ))*q) ≤ Real.exp (-((11:ℝ)*((49:ℝ)/10))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece22_L11_at (le_refl _)).2

theorem piece22_Lt_at : ((65421912084606566554581293153:ℝ)/2000000) ≤ Real.exp (((529:ℝ)/50)*((49:ℝ)/10)) := by
  have h := le_exp_nat_add 51 (f := ((421:ℝ)/500)) (by norm_num)
  rw [show (((529:ℝ)/50):ℝ)*((49:ℝ)/10) = ((51:ℕ):ℝ) + ((421:ℝ)/500) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece22_Et {q : ℝ} (h0 : ((49:ℝ)/10) ≤ q) : Real.exp (-(((529:ℝ)/50))*q) ≤ 1/((65421912084606566554581293153:ℝ)/2000000) := by
  have hm : Real.exp (-(((529:ℝ)/50))*q) ≤ Real.exp (-(((529:ℝ)/50)*((49:ℝ)/10))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece22_Lt_at (le_refl _)).2

theorem piece22_e00 {q : ℝ} (h0 : ((49:ℝ)/10) ≤ q) (h1 : q ≤ (5:ℝ)) :
    |pieceW q pieceX_22 0 0 - (((78816018792626097:ℝ)/2500000000) + (q - ((99:ℝ)/20)) * ((304288381923254047:ℝ)/5000000000))| ≤ ((67341254832187491:ℝ)/500000000000) := by
  set t := q - ((99:ℝ)/20) with htd
  have hq : q = ((99:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece22_L3 piece22_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((99:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_00 q = ∑ e ∈ Finset.range 10, ([((499680233012937339:ℝ)/16000000000), ((48193427367687789:ℝ)/800000000), ((64790952099687:ℝ)/1250000), ((6521774490693:ℝ)/250000), ((422868918087:ℝ)/50000), ((4576018293:ℝ)/2500), ((33039468:ℝ)/125), ((613632:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_00; ring
  have h12 : centralNum12_00 q = ∑ e ∈ Finset.range 11, ([((-977974879063892327343:ℝ)/320000000000), ((-20782297780007982669:ℝ)/3200000000), ((-497007456457892391:ℝ)/80000000), ((-7045098263398107:ℝ)/2000000), ((-262175611643253:ℝ)/200000), ((-16725954444507:ℝ)/50000), ((-7409697372:ℝ)/125), ((-180046374:ℝ)/25), ((-2870454:ℝ)/5), (-27112:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_00; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((499680233012937339:ℝ)/16000000000), ((48193427367687789:ℝ)/800000000), ((64790952099687:ℝ)/1250000), ((6521774490693:ℝ)/250000), ((422868918087:ℝ)/50000), ((4576018293:ℝ)/2500), ((33039468:ℝ)/125), ((613632:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-977974879063892327343:ℝ)/320000000000), ((-20782297780007982669:ℝ)/3200000000), ((-497007456457892391:ℝ)/80000000), ((-7045098263398107:ℝ)/2000000), ((-262175611643253:ℝ)/200000), ((-16725954444507:ℝ)/50000), ((-7409697372:ℝ)/125), ((-180046374:ℝ)/25), ((-2870454:ℝ)/5), (-27112:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 9 ht
  have m12 := abs_poly_le (fun e => ([((-977974879063892327343:ℝ)/320000000000), ((-20782297780007982669:ℝ)/3200000000), ((-497007456457892391:ℝ)/80000000), ((-7045098263398107:ℝ)/2000000), ((-262175611643253:ℝ)/200000), ((-16725954444507:ℝ)/50000), ((-7409697372:ℝ)/125), ((-180046374:ℝ)/25), ((-2870454:ℝ)/5), (-27112:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 11 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((499680233012937339:ℝ)/16000000000), ((48193427367687789:ℝ)/800000000), ((64790952099687:ℝ)/1250000), ((6521774490693:ℝ)/250000), ((422868918087:ℝ)/50000), ((4576018293:ℝ)/2500), ((33039468:ℝ)/125), ((613632:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - (((499680233012937339:ℝ)/16000000000) + ((48193427367687789:ℝ)/800000000)*t)| ≤ ((265792452421859:ℝ)/2000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 11, ([((-977974879063892327343:ℝ)/320000000000), ((-20782297780007982669:ℝ)/3200000000), ((-497007456457892391:ℝ)/80000000), ((-7045098263398107:ℝ)/2000000), ((-262175611643253:ℝ)/200000), ((-16725954444507:ℝ)/50000), ((-7409697372:ℝ)/125), ((-180046374:ℝ)/25), ((-2870454:ℝ)/5), (-27112:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e) - ((-977974879063892327343:ℝ)/320000000000) - ((-20782297780007982669:ℝ)/3200000000)*t| ≤ ((319602002254234957:ℝ)/20000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 11, ([((-977974879063892327343:ℝ)/320000000000), ((-20782297780007982669:ℝ)/3200000000), ((-497007456457892391:ℝ)/80000000), ((-7045098263398107:ℝ)/2000000), ((-262175611643253:ℝ)/200000), ((-16725954444507:ℝ)/50000), ((-7409697372:ℝ)/125), ((-180046374:ℝ)/25), ((-2870454:ℝ)/5), (-27112:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ (3396875000:ℝ) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((443756312138517939:ℝ)/16000000000) - ((44239210740203589:ℝ)/800000000)*t| ≤ ((250559640159809:ℝ)/2000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (5:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (600:ℝ), (-7776:ℝ), (16800:ℝ), (-9216:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m13' : |centralNum13_00 q| ≤ (125896875000:ℝ) := by
    rw [centralNum13_00_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (5:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (780:ℝ), (-6156:ℝ), (15288:ℝ), (-14400:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m23' : |centralNum23_00 q| ≤ (172950000000:ℝ) := by
    rw [centralNum23_00_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((28136695072708953678387022961:ℝ)/10000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece22_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece22_E11 h0) m23'
  have c5 := scaled_affine (X := ((11:ℝ)/1000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0))| ≤ ((128202370100000000000000000:ℝ)/3863098486683933148481470779391497) := by
    rw [abs_neg, tailWeight_0, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ (5:ℝ)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*(5:ℝ)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece22_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((10465499600:ℝ)/59049)) ≤ (5:ℝ)^6*(8000*(2*(5:ℝ)-3)^2*(1/((65421912084606566554581293153:ℝ)/2000000))*((10465499600:ℝ)/59049)) := by
          gcongr
      _ ≤ ((128202370100000000000000000:ℝ)/3863098486683933148481470779391497) := by norm_num
  have c7 := affine_round (α := ((499680233012937339:ℝ)/16000000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((-977974879063892327343:ℝ)/320000000000) + ((443756312138517939:ℝ)/16000000000)*((11:ℝ)/1000) - ((78816018792626097:ℝ)/2500000000)) (β := ((48193427367687789:ℝ)/800000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((-20782297780007982669:ℝ)/3200000000) - 3*((-977974879063892327343:ℝ)/320000000000)) + ((44239210740203589:ℝ)/800000000)*((11:ℝ)/1000) - ((304288381923254047:ℝ)/5000000000)) ht
  have hW : pieceW q pieceX_22 0 0 = centralNum11_00 q + 8*(Real.exp (-(3*((99:ℝ)/20)))*Real.exp (-3*t))*centralNum12_00 q + 18*Real.exp (-8*q)*centralNum13_00 q + 72*Real.exp (-11*q)*centralNum23_00 q + 8*q^7*(2*q-3)^2*((11:ℝ)/1000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0)) := by
    rw [pieceW_00, pieceX_22, sym4_00, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((36145215962687987189656495156579020140023860651802103569931:ℝ)/1407415174666858846684619160368761188621067018261263873467200000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((499680233012937339:ℝ)/16000000000) + ((48193427367687789:ℝ)/800000000)*t) + (8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((-977974879063892327343:ℝ)/320000000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((-20782297780007982669:ℝ)/3200000000) - 3*((-977974879063892327343:ℝ)/320000000000))*t) + (((443756312138517939:ℝ)/16000000000) + ((44239210740203589:ℝ)/800000000)*t)*((11:ℝ)/1000) - (((78816018792626097:ℝ)/2500000000) + t * ((304288381923254047:ℝ)/5000000000)) = (((499680233012937339:ℝ)/16000000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((-977974879063892327343:ℝ)/320000000000) + ((443756312138517939:ℝ)/16000000000)*((11:ℝ)/1000) - ((78816018792626097:ℝ)/2500000000)) + t*(((48193427367687789:ℝ)/800000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((-20782297780007982669:ℝ)/3200000000) - 3*((-977974879063892327343:ℝ)/320000000000)) + ((44239210740203589:ℝ)/800000000)*((11:ℝ)/1000) - ((304288381923254047:ℝ)/5000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece22_e01 {q : ℝ} (h0 : ((49:ℝ)/10) ≤ q) (h1 : q ≤ (5:ℝ)) :
    |pieceW q pieceX_22 0 1 - (((-176675379468763363:ℝ)/50000000000) + (q - ((99:ℝ)/20)) * ((-246104541499386427:ℝ)/50000000000))| ≤ ((120092828055707963:ℝ)/12500000000000) := by
  set t := q - ((99:ℝ)/20) with htd
  have hq : q = ((99:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece22_L3 piece22_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((99:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_01 q = ∑ e ∈ Finset.range 8, ([((-279619604372097:ℝ)/80000000), ((-19771083137421:ℝ)/4000000), ((-599123731437:ℝ)/200000), ((-2017251621:ℝ)/2000), ((-20376279:ℝ)/100), ((-617463:ℝ)/25), ((-8316:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_01; ring
  have h12 : centralNum12_01 q = ∑ e ∈ Finset.range 12, ([((-172252723546100741960691:ℝ)/12800000000000), ((-10591495768824068746197:ℝ)/320000000000), ((-236378556963114770061:ℝ)/6400000000), ((-3949960346734450851:ℝ)/160000000), ((-87871149289552563:ℝ)/8000000), ((-3415929289603677:ℝ)/1000000), ((-75776205968001:ℝ)/100000), ((-59953976871:ℝ)/500), ((-1326459123:ℝ)/100), ((-4884954:ℝ)/5), ((-215604:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_01; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-279619604372097:ℝ)/80000000), ((-19771083137421:ℝ)/4000000), ((-599123731437:ℝ)/200000), ((-2017251621:ℝ)/2000), ((-20376279:ℝ)/100), ((-617463:ℝ)/25), ((-8316:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0) 6 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-172252723546100741960691:ℝ)/12800000000000), ((-10591495768824068746197:ℝ)/320000000000), ((-236378556963114770061:ℝ)/6400000000), ((-3949960346734450851:ℝ)/160000000), ((-87871149289552563:ℝ)/8000000), ((-3415929289603677:ℝ)/1000000), ((-75776205968001:ℝ)/100000), ((-59953976871:ℝ)/500), ((-1326459123:ℝ)/100), ((-4884954:ℝ)/5), ((-215604:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0) 10 ht
  have m12 := abs_poly_le (fun e => ([((-172252723546100741960691:ℝ)/12800000000000), ((-10591495768824068746197:ℝ)/320000000000), ((-236378556963114770061:ℝ)/6400000000), ((-3949960346734450851:ℝ)/160000000), ((-87871149289552563:ℝ)/8000000), ((-3415929289603677:ℝ)/1000000), ((-75776205968001:ℝ)/100000), ((-59953976871:ℝ)/500), ((-1326459123:ℝ)/100), ((-4884954:ℝ)/5), ((-215604:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0) 12 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 8, ([((-279619604372097:ℝ)/80000000), ((-19771083137421:ℝ)/4000000), ((-599123731437:ℝ)/200000), ((-2017251621:ℝ)/2000), ((-20376279:ℝ)/100), ((-617463:ℝ)/25), ((-8316:ℝ)/5), (-48:ℝ)] : List ℝ).getD e 0 * t^e) - (((-279619604372097:ℝ)/80000000) + ((-19771083137421:ℝ)/4000000)*t)| ≤ ((304656245241:ℝ)/40000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 12, ([((-172252723546100741960691:ℝ)/12800000000000), ((-10591495768824068746197:ℝ)/320000000000), ((-236378556963114770061:ℝ)/6400000000), ((-3949960346734450851:ℝ)/160000000), ((-87871149289552563:ℝ)/8000000), ((-3415929289603677:ℝ)/1000000), ((-75776205968001:ℝ)/100000), ((-59953976871:ℝ)/500), ((-1326459123:ℝ)/100), ((-4884954:ℝ)/5), ((-215604:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e) - ((-172252723546100741960691:ℝ)/12800000000000) - ((-10591495768824068746197:ℝ)/320000000000)*t| ≤ ((244456983250224109383:ℝ)/2560000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 12, ([((-172252723546100741960691:ℝ)/12800000000000), ((-10591495768824068746197:ℝ)/320000000000), ((-236378556963114770061:ℝ)/6400000000), ((-3949960346734450851:ℝ)/160000000), ((-87871149289552563:ℝ)/8000000), ((-3415929289603677:ℝ)/1000000), ((-75776205968001:ℝ)/100000), ((-59953976871:ℝ)/500), ((-1326459123:ℝ)/100), ((-4884954:ℝ)/5), ((-215604:ℝ)/5), (-864:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ (15207656250:ℝ) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((443756312138517939:ℝ)/16000000000) - ((44239210740203589:ℝ)/800000000)*t| ≤ ((250559640159809:ℝ)/2000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (5:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-6288:ℝ), (81024:ℝ), (-238720:ℝ), (246784:ℝ), (-98304:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m13' : |centralNum13_01 q| ≤ (7708391250000:ℝ) := by
    rw [centralNum13_01_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (5:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-7368:ℝ), (59208:ℝ), (-155734:ℝ), (205300:ℝ), (-60000:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m23' : |centralNum23_01 q| ≤ (5262442031250:ℝ) := by
    rw [centralNum23_01_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((28136695072708953678387022961:ℝ)/10000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece22_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece22_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-279619604372097:ℝ)/80000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((-172252723546100741960691:ℝ)/12800000000000) + ((443756312138517939:ℝ)/16000000000)*(0:ℝ) - ((-176675379468763363:ℝ)/50000000000)) (β := ((-19771083137421:ℝ)/4000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((-10591495768824068746197:ℝ)/320000000000) - 3*((-172252723546100741960691:ℝ)/12800000000000)) + ((44239210740203589:ℝ)/800000000)*(0:ℝ) - ((-246104541499386427:ℝ)/50000000000)) ht
  have hW : pieceW q pieceX_22 0 1 = centralNum11_01 q + 8*(Real.exp (-(3*((99:ℝ)/20)))*Real.exp (-3*t))*centralNum12_01 q + 18*Real.exp (-8*q)*centralNum13_01 q + 72*Real.exp (-11*q)*centralNum23_01 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_01, pieceX_22, sym4_01, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((4324356165585673562083520953400000313583041234530142395979:ℝ)/879634484166786779177886975230475742888166886413289920917000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-279619604372097:ℝ)/80000000) + ((-19771083137421:ℝ)/4000000)*t) + (8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((-172252723546100741960691:ℝ)/12800000000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((-10591495768824068746197:ℝ)/320000000000) - 3*((-172252723546100741960691:ℝ)/12800000000000))*t) + (((443756312138517939:ℝ)/16000000000) + ((44239210740203589:ℝ)/800000000)*t)*(0:ℝ) - (((-176675379468763363:ℝ)/50000000000) + t * ((-246104541499386427:ℝ)/50000000000)) = (((-279619604372097:ℝ)/80000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((-172252723546100741960691:ℝ)/12800000000000) + ((443756312138517939:ℝ)/16000000000)*(0:ℝ) - ((-176675379468763363:ℝ)/50000000000)) + t*(((-19771083137421:ℝ)/4000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((-10591495768824068746197:ℝ)/320000000000) - 3*((-172252723546100741960691:ℝ)/12800000000000)) + ((44239210740203589:ℝ)/800000000)*(0:ℝ) - ((-246104541499386427:ℝ)/50000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece22_e02 {q : ℝ} (h0 : ((49:ℝ)/10) ≤ q) (h1 : q ≤ (5:ℝ)) :
    |pieceW q pieceX_22 0 2 - (((-12241326966364999:ℝ)/250000000000) + (q - ((99:ℝ)/20)) * ((-241520357516744413:ℝ)/10000000000000))| ≤ ((336064482491146427:ℝ)/100000000000000) := by
  set t := q - ((99:ℝ)/20) with htd
  have hq : q = ((99:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece22_L3 piece22_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((99:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_02 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_02; ring
  have h12 : centralNum12_02 q = ∑ e ∈ Finset.range 13, ([((-35269624241788787846744661:ℝ)/2048000000000000), ((-6160277057898540746832993:ℝ)/102400000000000), ((-460693353254639588889201:ℝ)/5120000000000), ((-4004565589647000408591:ℝ)/51200000000), ((-3568806844302162177:ℝ)/80000000), ((-5673211763211751869:ℝ)/320000000), ((-80950732240835457:ℝ)/16000000), ((-838552263592419:ℝ)/800000), ((-2509316471889:ℝ)/16000), ((-13243995441:ℝ)/800), ((-234345501:ℝ)/200), ((-499743:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_02; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-35269624241788787846744661:ℝ)/2048000000000000), ((-6160277057898540746832993:ℝ)/102400000000000), ((-460693353254639588889201:ℝ)/5120000000000), ((-4004565589647000408591:ℝ)/51200000000), ((-3568806844302162177:ℝ)/80000000), ((-5673211763211751869:ℝ)/320000000), ((-80950732240835457:ℝ)/16000000), ((-838552263592419:ℝ)/800000), ((-2509316471889:ℝ)/16000), ((-13243995441:ℝ)/800), ((-234345501:ℝ)/200), ((-499743:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((-35269624241788787846744661:ℝ)/2048000000000000), ((-6160277057898540746832993:ℝ)/102400000000000), ((-460693353254639588889201:ℝ)/5120000000000), ((-4004565589647000408591:ℝ)/51200000000), ((-3568806844302162177:ℝ)/80000000), ((-5673211763211751869:ℝ)/320000000), ((-80950732240835457:ℝ)/16000000), ((-838552263592419:ℝ)/800000), ((-2509316471889:ℝ)/16000), ((-13243995441:ℝ)/800), ((-234345501:ℝ)/200), ((-499743:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((-35269624241788787846744661:ℝ)/2048000000000000), ((-6160277057898540746832993:ℝ)/102400000000000), ((-460693353254639588889201:ℝ)/5120000000000), ((-4004565589647000408591:ℝ)/51200000000), ((-3568806844302162177:ℝ)/80000000), ((-5673211763211751869:ℝ)/320000000), ((-80950732240835457:ℝ)/16000000), ((-838552263592419:ℝ)/800000), ((-2509316471889:ℝ)/16000), ((-13243995441:ℝ)/800), ((-234345501:ℝ)/200), ((-499743:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e) - ((-35269624241788787846744661:ℝ)/2048000000000000) - ((-6160277057898540746832993:ℝ)/102400000000000)*t| ≤ ((240649350156335703211173:ℝ)/1024000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((-35269624241788787846744661:ℝ)/2048000000000000), ((-6160277057898540746832993:ℝ)/102400000000000), ((-460693353254639588889201:ℝ)/5120000000000), ((-4004565589647000408591:ℝ)/51200000000), ((-3568806844302162177:ℝ)/80000000), ((-5673211763211751869:ℝ)/320000000), ((-80950732240835457:ℝ)/16000000), ((-838552263592419:ℝ)/800000), ((-2509316471889:ℝ)/16000), ((-13243995441:ℝ)/800), ((-234345501:ℝ)/200), ((-499743:ℝ)/10), (-972:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ (20464453125:ℝ) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((443756312138517939:ℝ)/16000000000) - ((44239210740203589:ℝ)/800000000)*t| ≤ ((250559640159809:ℝ)/2000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (5:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82080:ℝ), (-967680:ℝ), (3257600:ℝ), (-4474880:ℝ), (2908160:ℝ), (-786432:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_02 q| ≤ (384446912500000:ℝ) := by
    rw [centralNum13_02_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (5:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (87660:ℝ), (-702180:ℝ), ((7421435:ℝ)/4), ((-10854125:ℝ)/4), ((2828125:ℝ)/2), (-187500:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_02 q| ≤ ((290453202734375:ℝ)/2) := by
    rw [centralNum23_02_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((28136695072708953678387022961:ℝ)/10000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece22_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece22_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((-35269624241788787846744661:ℝ)/2048000000000000) + ((443756312138517939:ℝ)/16000000000)*(0:ℝ) - ((-12241326966364999:ℝ)/250000000000)) (β := (0:ℝ) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((-6160277057898540746832993:ℝ)/102400000000000) - 3*((-35269624241788787846744661:ℝ)/2048000000000000)) + ((44239210740203589:ℝ)/800000000)*(0:ℝ) - ((-241520357516744413:ℝ)/10000000000000)) ht
  have hW : pieceW q pieceX_22 0 2 = centralNum11_02 q + 8*(Real.exp (-(3*((99:ℝ)/20)))*Real.exp (-3*t))*centralNum12_02 q + 18*Real.exp (-8*q)*centralNum13_02 q + 72*Real.exp (-11*q)*centralNum23_02 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_02, pieceX_22, sym4_02, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((2976642763889963687434964610702819971200143552514501146879:ℝ)/175926896833357355835577395046095148577633377282657984183400000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((-35269624241788787846744661:ℝ)/2048000000000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((-6160277057898540746832993:ℝ)/102400000000000) - 3*((-35269624241788787846744661:ℝ)/2048000000000000))*t) + (((443756312138517939:ℝ)/16000000000) + ((44239210740203589:ℝ)/800000000)*t)*(0:ℝ) - (((-12241326966364999:ℝ)/250000000000) + t * ((-241520357516744413:ℝ)/10000000000000)) = ((0:ℝ) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((-35269624241788787846744661:ℝ)/2048000000000000) + ((443756312138517939:ℝ)/16000000000)*(0:ℝ) - ((-12241326966364999:ℝ)/250000000000)) + t*((0:ℝ) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((-6160277057898540746832993:ℝ)/102400000000000) - 3*((-35269624241788787846744661:ℝ)/2048000000000000)) + ((44239210740203589:ℝ)/800000000)*(0:ℝ) - ((-241520357516744413:ℝ)/10000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece22_e03 {q : ℝ} (h0 : ((49:ℝ)/10) ≤ q) (h1 : q ≤ (5:ℝ)) :
    |pieceW q pieceX_22 0 3 - (((164218440278201667:ℝ)/2000000000000) + (q - ((99:ℝ)/20)) * ((-930513432452652089:ℝ)/10000000000000))| ≤ ((68088543599475511:ℝ)/20000000000000) := by
  set t := q - ((99:ℝ)/20) with htd
  have hq : q = ((99:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece22_L3 piece22_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((99:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_03 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_03; ring
  have h12 : centralNum12_03 q = ∑ e ∈ Finset.range 14, ([((16560075099167463272629828509:ℝ)/573440000000000000), ((386416306078763533662893067:ℝ)/7168000000000000), ((172124286256834872974343:ℝ)/6400000000000), ((-676616047919276342089707:ℝ)/35840000000000), ((-25277685955926269658903:ℝ)/716800000000), ((-317527005008792611197:ℝ)/12800000000), ((-12032085574350225747:ℝ)/1120000000), ((-357123773489164551:ℝ)/112000000), ((-15066278719961337:ℝ)/22400000), ((-101376593253:ℝ)/1000), ((-75038670297:ℝ)/7000), ((-1060937271:ℝ)/1400), ((-644679:ℝ)/20), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_03; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((16560075099167463272629828509:ℝ)/573440000000000000), ((386416306078763533662893067:ℝ)/7168000000000000), ((172124286256834872974343:ℝ)/6400000000000), ((-676616047919276342089707:ℝ)/35840000000000), ((-25277685955926269658903:ℝ)/716800000000), ((-317527005008792611197:ℝ)/12800000000), ((-12032085574350225747:ℝ)/1120000000), ((-357123773489164551:ℝ)/112000000), ((-15066278719961337:ℝ)/22400000), ((-101376593253:ℝ)/1000), ((-75038670297:ℝ)/7000), ((-1060937271:ℝ)/1400), ((-644679:ℝ)/20), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((16560075099167463272629828509:ℝ)/573440000000000000), ((386416306078763533662893067:ℝ)/7168000000000000), ((172124286256834872974343:ℝ)/6400000000000), ((-676616047919276342089707:ℝ)/35840000000000), ((-25277685955926269658903:ℝ)/716800000000), ((-317527005008792611197:ℝ)/12800000000), ((-12032085574350225747:ℝ)/1120000000), ((-357123773489164551:ℝ)/112000000), ((-15066278719961337:ℝ)/22400000), ((-101376593253:ℝ)/1000), ((-75038670297:ℝ)/7000), ((-1060937271:ℝ)/1400), ((-644679:ℝ)/20), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((16560075099167463272629828509:ℝ)/573440000000000000), ((386416306078763533662893067:ℝ)/7168000000000000), ((172124286256834872974343:ℝ)/6400000000000), ((-676616047919276342089707:ℝ)/35840000000000), ((-25277685955926269658903:ℝ)/716800000000), ((-317527005008792611197:ℝ)/12800000000), ((-12032085574350225747:ℝ)/1120000000), ((-357123773489164551:ℝ)/112000000), ((-15066278719961337:ℝ)/22400000), ((-101376593253:ℝ)/1000), ((-75038670297:ℝ)/7000), ((-1060937271:ℝ)/1400), ((-644679:ℝ)/20), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((16560075099167463272629828509:ℝ)/573440000000000000) - ((386416306078763533662893067:ℝ)/7168000000000000)*t| ≤ ((5720000532225632910558063:ℝ)/81920000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((16560075099167463272629828509:ℝ)/573440000000000000), ((386416306078763533662893067:ℝ)/7168000000000000), ((172124286256834872974343:ℝ)/6400000000000), ((-676616047919276342089707:ℝ)/35840000000000), ((-25277685955926269658903:ℝ)/716800000000), ((-317527005008792611197:ℝ)/12800000000), ((-12032085574350225747:ℝ)/1120000000), ((-357123773489164551:ℝ)/112000000), ((-15066278719961337:ℝ)/22400000), ((-101376593253:ℝ)/1000), ((-75038670297:ℝ)/7000), ((-1060937271:ℝ)/1400), ((-644679:ℝ)/20), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((9072890163604048418827653609:ℝ)/286720000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((443756312138517939:ℝ)/16000000000) - ((44239210740203589:ℝ)/800000000)*t| ≤ ((250559640159809:ℝ)/2000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (5:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-812160:ℝ), (8985600:ℝ), (-32225280:ℝ), (52019200:ℝ), ((-305233920:ℝ)/7), ((135528448:ℝ)/7), ((-25165824:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_03 q| ≤ ((82733594150000000:ℝ)/7) := by
    rw [centralNum13_03_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (5:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-833220:ℝ), (6469740:ℝ), ((-68603955:ℝ)/4), ((104396875:ℝ)/4), ((-1001334375:ℝ)/56), ((125828125:ℝ)/28), ((-2343750:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_03 q| ≤ ((149515048331640625:ℝ)/56) := by
    rw [centralNum23_03_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((28136695072708953678387022961:ℝ)/10000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece22_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece22_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((16560075099167463272629828509:ℝ)/573440000000000000) + ((443756312138517939:ℝ)/16000000000)*(0:ℝ) - ((164218440278201667:ℝ)/2000000000000)) (β := (0:ℝ) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((386416306078763533662893067:ℝ)/7168000000000000) - 3*((16560075099167463272629828509:ℝ)/573440000000000000)) + ((44239210740203589:ℝ)/800000000)*(0:ℝ) - ((-930513432452652089:ℝ)/10000000000000)) ht
  have hW : pieceW q pieceX_22 0 3 = centralNum11_03 q + 8*(Real.exp (-(3*((99:ℝ)/20)))*Real.exp (-3*t))*centralNum12_03 q + 18*Real.exp (-8*q)*centralNum13_03 q + 72*Real.exp (-11*q)*centralNum23_03 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_03, pieceX_22, sym4_03, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((33265194675150707891035702240388974559071586041353371966591:ℝ)/1231488277833501490849041765322666040043433640978605889283800000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((16560075099167463272629828509:ℝ)/573440000000000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((386416306078763533662893067:ℝ)/7168000000000000) - 3*((16560075099167463272629828509:ℝ)/573440000000000000))*t) + (((443756312138517939:ℝ)/16000000000) + ((44239210740203589:ℝ)/800000000)*t)*(0:ℝ) - (((164218440278201667:ℝ)/2000000000000) + t * ((-930513432452652089:ℝ)/10000000000000)) = ((0:ℝ) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((16560075099167463272629828509:ℝ)/573440000000000000) + ((443756312138517939:ℝ)/16000000000)*(0:ℝ) - ((164218440278201667:ℝ)/2000000000000)) + t*((0:ℝ) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((386416306078763533662893067:ℝ)/7168000000000000) - 3*((16560075099167463272629828509:ℝ)/573440000000000000)) + ((44239210740203589:ℝ)/800000000)*(0:ℝ) - ((-930513432452652089:ℝ)/10000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece22_e11 {q : ℝ} (h0 : ((49:ℝ)/10) ≤ q) (h1 : q ≤ (5:ℝ)) :
    |pieceW q pieceX_22 1 1 - (((222547663858379939:ℝ)/10000000000) + (q - ((99:ℝ)/20)) * ((207156823562862707:ℝ)/5000000000))| ≤ ((456329821502365173:ℝ)/5000000000000) := by
  set t := q - ((99:ℝ)/20) with htd
  have hq : q = ((99:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece22_L3 piece22_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((99:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_11 q = ∑ e ∈ Finset.range 10, ([((43945468933590477:ℝ)/2000000000), ((16350343398229203:ℝ)/400000000), ((170990604581247:ℝ)/5000000), ((4219580984157:ℝ)/250000), ((67630104927:ℝ)/12500), ((1458416421:ℝ)/1250), ((21128772:ℝ)/125), ((396048:ℝ)/25), ((4352:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_11; ring
  have h12 : centralNum12_11 q = ∑ e ∈ Finset.range 13, ([((-4150816749880637683882167:ℝ)/512000000000000), ((-1097865652104015963918651:ℝ)/25600000000000), ((-99163656112831823089467:ℝ)/1280000000000), ((-964218180693383623557:ℝ)/12800000000), ((-115900665966354753:ℝ)/2500000), ((-1558918016015060943:ℝ)/80000000), ((-23237295509289099:ℝ)/4000000), ((-249394840398273:ℝ)/200000), ((-768746150603:ℝ)/4000), ((-12484728001:ℝ)/600), ((-75281247:ℝ)/50), ((-327402:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_11; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((43945468933590477:ℝ)/2000000000), ((16350343398229203:ℝ)/400000000), ((170990604581247:ℝ)/5000000), ((4219580984157:ℝ)/250000), ((67630104927:ℝ)/12500), ((1458416421:ℝ)/1250), ((21128772:ℝ)/125), ((396048:ℝ)/25), ((4352:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-4150816749880637683882167:ℝ)/512000000000000), ((-1097865652104015963918651:ℝ)/25600000000000), ((-99163656112831823089467:ℝ)/1280000000000), ((-964218180693383623557:ℝ)/12800000000), ((-115900665966354753:ℝ)/2500000), ((-1558918016015060943:ℝ)/80000000), ((-23237295509289099:ℝ)/4000000), ((-249394840398273:ℝ)/200000), ((-768746150603:ℝ)/4000), ((-12484728001:ℝ)/600), ((-75281247:ℝ)/50), ((-327402:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((-4150816749880637683882167:ℝ)/512000000000000), ((-1097865652104015963918651:ℝ)/25600000000000), ((-99163656112831823089467:ℝ)/1280000000000), ((-964218180693383623557:ℝ)/12800000000), ((-115900665966354753:ℝ)/2500000), ((-1558918016015060943:ℝ)/80000000), ((-23237295509289099:ℝ)/4000000), ((-249394840398273:ℝ)/200000), ((-768746150603:ℝ)/4000), ((-12484728001:ℝ)/600), ((-75281247:ℝ)/50), ((-327402:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((43945468933590477:ℝ)/2000000000), ((16350343398229203:ℝ)/400000000), ((170990604581247:ℝ)/5000000), ((4219580984157:ℝ)/250000), ((67630104927:ℝ)/12500), ((1458416421:ℝ)/1250), ((21128772:ℝ)/125), ((396048:ℝ)/25), ((4352:ℝ)/5), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((43945468933590477:ℝ)/2000000000) + ((16350343398229203:ℝ)/400000000)*t)| ≤ ((2103342602226667:ℝ)/24000000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((-4150816749880637683882167:ℝ)/512000000000000), ((-1097865652104015963918651:ℝ)/25600000000000), ((-99163656112831823089467:ℝ)/1280000000000), ((-964218180693383623557:ℝ)/12800000000), ((-115900665966354753:ℝ)/2500000), ((-1558918016015060943:ℝ)/80000000), ((-23237295509289099:ℝ)/4000000), ((-249394840398273:ℝ)/200000), ((-768746150603:ℝ)/4000), ((-12484728001:ℝ)/600), ((-75281247:ℝ)/50), ((-327402:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e) - ((-4150816749880637683882167:ℝ)/512000000000000) - ((-1097865652104015963918651:ℝ)/25600000000000)*t| ≤ ((156204397023019528298773:ℝ)/768000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((-4150816749880637683882167:ℝ)/512000000000000), ((-1097865652104015963918651:ℝ)/25600000000000), ((-99163656112831823089467:ℝ)/1280000000000), ((-964218180693383623557:ℝ)/12800000000), ((-115900665966354753:ℝ)/2500000), ((-1558918016015060943:ℝ)/80000000), ((-23237295509289099:ℝ)/4000000), ((-249394840398273:ℝ)/200000), ((-768746150603:ℝ)/4000), ((-12484728001:ℝ)/600), ((-75281247:ℝ)/50), ((-327402:ℝ)/5), (-1296:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((31364171875:ℝ)/3) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((443756312138517939:ℝ)/16000000000) - ((44239210740203589:ℝ)/800000000)*t| ≤ ((250559640159809:ℝ)/2000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (5:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-3444:ℝ), (162624:ℝ), (-1531216:ℝ), (4800960:ℝ), (-6350848:ℝ), ((12025856:ℝ)/3), (-1048576:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_11 q| ≤ ((1571223295187500:ℝ)/3) := by
    rw [centralNum13_11_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (5:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-4074:ℝ), (159906:ℝ), (-1104799:ℝ), (2801499:ℝ), (-3931375:ℝ), ((5896250:ℝ)/3), (-250000:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_11 q| ≤ ((603932691203125:ℝ)/3) := by
    rw [centralNum23_11_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((28136695072708953678387022961:ℝ)/10000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece22_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece22_E11 h0) m23'
  have c5 := scaled_affine (X := ((11:ℝ)/1000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1))| ≤ ((58980615670900000000000000000:ℝ)/34767886380155398336333237014523473) := by
    rw [abs_neg, tailWeight_1, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ (5:ℝ)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*(5:ℝ)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece22_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((4814744136400:ℝ)/531441)) ≤ (5:ℝ)^6*(8000*(2*(5:ℝ)-3)^2*(1/((65421912084606566554581293153:ℝ)/2000000))*((4814744136400:ℝ)/531441)) := by
          gcongr
      _ ≤ ((58980615670900000000000000000:ℝ)/34767886380155398336333237014523473) := by norm_num
  have c7 := affine_round (α := ((43945468933590477:ℝ)/2000000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((-4150816749880637683882167:ℝ)/512000000000000) + ((443756312138517939:ℝ)/16000000000)*((11:ℝ)/1000) - ((222547663858379939:ℝ)/10000000000)) (β := ((16350343398229203:ℝ)/400000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((-1097865652104015963918651:ℝ)/25600000000000) - 3*((-4150816749880637683882167:ℝ)/512000000000000)) + ((44239210740203589:ℝ)/800000000)*((11:ℝ)/1000) - ((207156823562862707:ℝ)/5000000000)) ht
  have hW : pieceW q pieceX_22 1 1 = centralNum11_11 q + 8*(Real.exp (-(3*((99:ℝ)/20)))*Real.exp (-3*t))*centralNum12_11 q + 18*Real.exp (-8*q)*centralNum13_11 q + 72*Real.exp (-11*q)*centralNum23_11 q + 8*q^7*(2*q-3)^2*((11:ℝ)/1000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1)) := by
    rw [pieceW_11, pieceX_22, sym4_11, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((46102944198179541629510649861749412337672575809698605535613:ℝ)/1759268968333573558355773950460951485776333772826579841834000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((43945468933590477:ℝ)/2000000000) + ((16350343398229203:ℝ)/400000000)*t) + (8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((-4150816749880637683882167:ℝ)/512000000000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((-1097865652104015963918651:ℝ)/25600000000000) - 3*((-4150816749880637683882167:ℝ)/512000000000000))*t) + (((443756312138517939:ℝ)/16000000000) + ((44239210740203589:ℝ)/800000000)*t)*((11:ℝ)/1000) - (((222547663858379939:ℝ)/10000000000) + t * ((207156823562862707:ℝ)/5000000000)) = (((43945468933590477:ℝ)/2000000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((-4150816749880637683882167:ℝ)/512000000000000) + ((443756312138517939:ℝ)/16000000000)*((11:ℝ)/1000) - ((222547663858379939:ℝ)/10000000000)) + t*(((16350343398229203:ℝ)/400000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((-1097865652104015963918651:ℝ)/25600000000000) - 3*((-4150816749880637683882167:ℝ)/512000000000000)) + ((44239210740203589:ℝ)/800000000)*((11:ℝ)/1000) - ((207156823562862707:ℝ)/5000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece22_e12 {q : ℝ} (h0 : ((49:ℝ)/10) ≤ q) (h1 : q ≤ (5:ℝ)) :
    |pieceW q pieceX_22 1 2 - (((-146498213131604141:ℝ)/100000000000) + (q - ((99:ℝ)/20)) * ((-8193257219737743:ℝ)/4000000000))| ≤ ((150711462124311413:ℝ)/10000000000000) := by
  set t := q - ((99:ℝ)/20) with htd
  have hq : q = ((99:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece22_L3 piece22_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((99:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_12 q = ∑ e ∈ Finset.range 9, ([((-1104356215247373:ℝ)/640000000), ((-15320449703889:ℝ)/8000000), ((-258496386291:ℝ)/400000), ((1225487637:ℝ)/20000), ((42428529:ℝ)/400), ((1663497:ℝ)/50), ((25698:ℝ)/5), (408:ℝ), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_12; ring
  have h12 : centralNum12_12 q = ∑ e ∈ Finset.range 14, ([((7507652675557400922584947743:ℝ)/81920000000000000), ((233544191921230811149834569:ℝ)/1024000000000000), ((1488174677151746494547637:ℝ)/6400000000000), ((584403541972523639573031:ℝ)/5120000000000), ((1303690714085722628259:ℝ)/102400000000), ((-237130823557178779833:ℝ)/12800000000), ((-2149919027707428129:ℝ)/160000000), ((-79299543062013837:ℝ)/16000000), ((-11399836410810937:ℝ)/9600000), ((-195210593987:ℝ)/1000), ((-22018568619:ℝ)/1000), ((-327539997:ℝ)/200), ((-1452411:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_12; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-1104356215247373:ℝ)/640000000), ((-15320449703889:ℝ)/8000000), ((-258496386291:ℝ)/400000), ((1225487637:ℝ)/20000), ((42428529:ℝ)/400), ((1663497:ℝ)/50), ((25698:ℝ)/5), (408:ℝ), ((40:ℝ)/3)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((7507652675557400922584947743:ℝ)/81920000000000000), ((233544191921230811149834569:ℝ)/1024000000000000), ((1488174677151746494547637:ℝ)/6400000000000), ((584403541972523639573031:ℝ)/5120000000000), ((1303690714085722628259:ℝ)/102400000000), ((-237130823557178779833:ℝ)/12800000000), ((-2149919027707428129:ℝ)/160000000), ((-79299543062013837:ℝ)/16000000), ((-11399836410810937:ℝ)/9600000), ((-195210593987:ℝ)/1000), ((-22018568619:ℝ)/1000), ((-327539997:ℝ)/200), ((-1452411:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((7507652675557400922584947743:ℝ)/81920000000000000), ((233544191921230811149834569:ℝ)/1024000000000000), ((1488174677151746494547637:ℝ)/6400000000000), ((584403541972523639573031:ℝ)/5120000000000), ((1303690714085722628259:ℝ)/102400000000), ((-237130823557178779833:ℝ)/12800000000), ((-2149919027707428129:ℝ)/160000000), ((-79299543062013837:ℝ)/16000000), ((-11399836410810937:ℝ)/9600000), ((-195210593987:ℝ)/1000), ((-22018568619:ℝ)/1000), ((-327539997:ℝ)/200), ((-1452411:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((-1104356215247373:ℝ)/640000000), ((-15320449703889:ℝ)/8000000), ((-258496386291:ℝ)/400000), ((1225487637:ℝ)/20000), ((42428529:ℝ)/400), ((1663497:ℝ)/50), ((25698:ℝ)/5), (408:ℝ), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((-1104356215247373:ℝ)/640000000) + ((-15320449703889:ℝ)/8000000)*t)| ≤ ((3117955459771:ℝ)/1920000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((7507652675557400922584947743:ℝ)/81920000000000000), ((233544191921230811149834569:ℝ)/1024000000000000), ((1488174677151746494547637:ℝ)/6400000000000), ((584403541972523639573031:ℝ)/5120000000000), ((1303690714085722628259:ℝ)/102400000000), ((-237130823557178779833:ℝ)/12800000000), ((-2149919027707428129:ℝ)/160000000), ((-79299543062013837:ℝ)/16000000), ((-11399836410810937:ℝ)/9600000), ((-195210593987:ℝ)/1000), ((-22018568619:ℝ)/1000), ((-327539997:ℝ)/200), ((-1452411:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e) - ((7507652675557400922584947743:ℝ)/81920000000000000) - ((233544191921230811149834569:ℝ)/1024000000000000)*t| ≤ ((146392220965200683859728503:ℝ)/245760000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((7507652675557400922584947743:ℝ)/81920000000000000), ((233544191921230811149834569:ℝ)/1024000000000000), ((1488174677151746494547637:ℝ)/6400000000000), ((584403541972523639573031:ℝ)/5120000000000), ((1303690714085722628259:ℝ)/102400000000), ((-237130823557178779833:ℝ)/12800000000), ((-2149919027707428129:ℝ)/160000000), ((-79299543062013837:ℝ)/16000000), ((-11399836410810937:ℝ)/9600000), ((-195210593987:ℝ)/1000), ((-22018568619:ℝ)/1000), ((-327539997:ℝ)/200), ((-1452411:ℝ)/20), (-1458:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((79599626720913041204414333:ℝ)/768000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((443756312138517939:ℝ)/16000000000) - ((44239210740203589:ℝ)/800000000)*t| ≤ ((250559640159809:ℝ)/2000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (5:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (122790:ℝ), (-3586680:ℝ), (28529720:ℝ), (-90761600:ℝ), (137804800:ℝ), ((-332136448:ℝ)/3), ((141819904:ℝ)/3), (-8388608:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_12 q| ≤ (28721645299843750:ℝ) := by
    rw [centralNum13_12_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (5:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (132555:ℝ), (-3252375:ℝ), ((39743695:ℝ)/2), ((-197111615:ℝ)/4), ((281947375:ℝ)/4), ((-1100234375:ℝ)/24), ((131828125:ℝ)/12), (-781250:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_12 q| ≤ ((53334156356484375:ℝ)/8) := by
    rw [centralNum23_12_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((28136695072708953678387022961:ℝ)/10000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece22_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece22_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-1104356215247373:ℝ)/640000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((7507652675557400922584947743:ℝ)/81920000000000000) + ((443756312138517939:ℝ)/16000000000)*(0:ℝ) - ((-146498213131604141:ℝ)/100000000000)) (β := ((-15320449703889:ℝ)/8000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((233544191921230811149834569:ℝ)/1024000000000000) - 3*((7507652675557400922584947743:ℝ)/81920000000000000)) + ((44239210740203589:ℝ)/800000000)*(0:ℝ) - ((-8193257219737743:ℝ)/4000000000)) ht
  have hW : pieceW q pieceX_22 1 2 = centralNum11_12 q + 8*(Real.exp (-(3*((99:ℝ)/20)))*Real.exp (-3*t))*centralNum12_12 q + 18*Real.exp (-8*q)*centralNum13_12 q + 72*Real.exp (-11*q)*centralNum23_12 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_12, pieceX_22, sym4_12, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((8105095660183939886370984696752018042235626346160208651:ℝ)/1691604777243820729188244183135530274784936320025557540225000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-1104356215247373:ℝ)/640000000) + ((-15320449703889:ℝ)/8000000)*t) + (8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((7507652675557400922584947743:ℝ)/81920000000000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((233544191921230811149834569:ℝ)/1024000000000000) - 3*((7507652675557400922584947743:ℝ)/81920000000000000))*t) + (((443756312138517939:ℝ)/16000000000) + ((44239210740203589:ℝ)/800000000)*t)*(0:ℝ) - (((-146498213131604141:ℝ)/100000000000) + t * ((-8193257219737743:ℝ)/4000000000)) = (((-1104356215247373:ℝ)/640000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((7507652675557400922584947743:ℝ)/81920000000000000) + ((443756312138517939:ℝ)/16000000000)*(0:ℝ) - ((-146498213131604141:ℝ)/100000000000)) + t*(((-15320449703889:ℝ)/8000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((233544191921230811149834569:ℝ)/1024000000000000) - 3*((7507652675557400922584947743:ℝ)/81920000000000000)) + ((44239210740203589:ℝ)/800000000)*(0:ℝ) - ((-8193257219737743:ℝ)/4000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece22_e13 {q : ℝ} (h0 : ((49:ℝ)/10) ≤ q) (h1 : q ≤ (5:ℝ)) :
    |pieceW q pieceX_22 1 3 - (((-989715377982179011:ℝ)/1000000000000) + (q - ((99:ℝ)/20)) * ((-105562312005048353:ℝ)/200000000000))| ≤ ((22145194768172623:ℝ)/2500000000000) := by
  set t := q - ((99:ℝ)/20) with htd
  have hq : q = ((99:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece22_L3 piece22_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((99:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_13 q = ∑ e ∈ Finset.range 7, ([((-2824440448203:ℝ)/3200000), ((-85589104491:ℝ)/80000), ((-864536409:ℝ)/1600), ((-2910897:ℝ)/20), ((-88209:ℝ)/4), (-1782:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_13; ring
  have h12 : centralNum12_13 q = ∑ e ∈ Finset.range 15, ([((-863832528614611298803746661767:ℝ)/22937600000000000000), ((89071111696018428538003001043:ℝ)/1146880000000000000), ((4852195475556157571082685797:ℝ)/14336000000000000), ((631015393553235875167217289:ℝ)/1433600000000000), ((44345493101511598421699703:ℝ)/143360000000000), ((950475124766737650711609:ℝ)/7168000000000), ((6098165607755815234707:ℝ)/179200000000), ((16354822336102010331:ℝ)/4480000000), ((-696037041766129881:ℝ)/896000000), ((-18773933039228331:ℝ)/44800000), ((-25333136427699:ℝ)/280000), ((-657894763791:ℝ)/56000), ((-5333584887:ℝ)/5600), ((-12533697:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_13; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-2824440448203:ℝ)/3200000), ((-85589104491:ℝ)/80000), ((-864536409:ℝ)/1600), ((-2910897:ℝ)/20), ((-88209:ℝ)/4), (-1782:ℝ), (-60:ℝ)] : List ℝ).getD e 0) 5 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-863832528614611298803746661767:ℝ)/22937600000000000000), ((89071111696018428538003001043:ℝ)/1146880000000000000), ((4852195475556157571082685797:ℝ)/14336000000000000), ((631015393553235875167217289:ℝ)/1433600000000000), ((44345493101511598421699703:ℝ)/143360000000000), ((950475124766737650711609:ℝ)/7168000000000), ((6098165607755815234707:ℝ)/179200000000), ((16354822336102010331:ℝ)/4480000000), ((-696037041766129881:ℝ)/896000000), ((-18773933039228331:ℝ)/44800000), ((-25333136427699:ℝ)/280000), ((-657894763791:ℝ)/56000), ((-5333584887:ℝ)/5600), ((-12533697:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-863832528614611298803746661767:ℝ)/22937600000000000000), ((89071111696018428538003001043:ℝ)/1146880000000000000), ((4852195475556157571082685797:ℝ)/14336000000000000), ((631015393553235875167217289:ℝ)/1433600000000000), ((44345493101511598421699703:ℝ)/143360000000000), ((950475124766737650711609:ℝ)/7168000000000), ((6098165607755815234707:ℝ)/179200000000), ((16354822336102010331:ℝ)/4480000000), ((-696037041766129881:ℝ)/896000000), ((-18773933039228331:ℝ)/44800000), ((-25333136427699:ℝ)/280000), ((-657894763791:ℝ)/56000), ((-5333584887:ℝ)/5600), ((-12533697:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 7, ([((-2824440448203:ℝ)/3200000), ((-85589104491:ℝ)/80000), ((-864536409:ℝ)/1600), ((-2910897:ℝ)/20), ((-88209:ℝ)/4), (-1782:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e) - (((-2824440448203:ℝ)/3200000) + ((-85589104491:ℝ)/80000)*t)| ≤ ((876268563:ℝ)/640000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-863832528614611298803746661767:ℝ)/22937600000000000000), ((89071111696018428538003001043:ℝ)/1146880000000000000), ((4852195475556157571082685797:ℝ)/14336000000000000), ((631015393553235875167217289:ℝ)/1433600000000000), ((44345493101511598421699703:ℝ)/143360000000000), ((950475124766737650711609:ℝ)/7168000000000), ((6098165607755815234707:ℝ)/179200000000), ((16354822336102010331:ℝ)/4480000000), ((-696037041766129881:ℝ)/896000000), ((-18773933039228331:ℝ)/44800000), ((-25333136427699:ℝ)/280000), ((-657894763791:ℝ)/56000), ((-5333584887:ℝ)/5600), ((-12533697:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((-863832528614611298803746661767:ℝ)/22937600000000000000) - ((89071111696018428538003001043:ℝ)/1146880000000000000)*t| ≤ ((5179030230005725046952134727:ℝ)/5734400000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-863832528614611298803746661767:ℝ)/22937600000000000000), ((89071111696018428538003001043:ℝ)/1146880000000000000), ((4852195475556157571082685797:ℝ)/14336000000000000), ((631015393553235875167217289:ℝ)/1433600000000000), ((44345493101511598421699703:ℝ)/143360000000000), ((950475124766737650711609:ℝ)/7168000000000), ((6098165607755815234707:ℝ)/179200000000), ((16354822336102010331:ℝ)/4480000000), ((-696037041766129881:ℝ)/896000000), ((-18773933039228331:ℝ)/44800000), ((-25333136427699:ℝ)/280000), ((-657894763791:ℝ)/56000), ((-5333584887:ℝ)/5600), ((-12533697:ℝ)/280), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((69544268659332330537825585837:ℝ)/1638400000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((443756312138517939:ℝ)/16000000000) - ((44239210740203589:ℝ)/800000000)*t| ≤ ((250559640159809:ℝ)/2000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (5:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2325540:ℝ), (52589280:ℝ), (-375655200:ℝ), (1192958720:ℝ), (-1965096960:ℝ), ((12857851904:ℝ)/7), ((-21171273728:ℝ)/21), ((914358272:ℝ)/3), ((-268435456:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_13 q| ≤ ((6745219778805937500:ℝ)/7) := by
    rw [centralNum13_13_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (5:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2399070:ℝ), (45666930:ℝ), (-251781675:ℝ), ((2452738385:ℝ)/4), ((-14104310625:ℝ)/16), ((74345740625:ℝ)/112), ((-74899765625:ℝ)/336), ((5161328125:ℝ)/168), ((-9765625:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_13 q| ≤ ((15989210766285390625:ℝ)/112) := by
    rw [centralNum23_13_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((28136695072708953678387022961:ℝ)/10000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece22_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece22_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-2824440448203:ℝ)/3200000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((-863832528614611298803746661767:ℝ)/22937600000000000000) + ((443756312138517939:ℝ)/16000000000)*(0:ℝ) - ((-989715377982179011:ℝ)/1000000000000)) (β := ((-85589104491:ℝ)/80000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((89071111696018428538003001043:ℝ)/1146880000000000000) - 3*((-863832528614611298803746661767:ℝ)/22937600000000000000)) + ((44239210740203589:ℝ)/800000000)*(0:ℝ) - ((-105562312005048353:ℝ)/200000000000)) ht
  have hW : pieceW q pieceX_22 1 3 = centralNum11_13 q + 8*(Real.exp (-(3*((99:ℝ)/20)))*Real.exp (-3*t))*centralNum12_13 q + 18*Real.exp (-8*q)*centralNum13_13 q + 72*Real.exp (-11*q)*centralNum23_13 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_13, pieceX_22, sym4_13, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((9803089681856112171205268267568665959016418644818402801471:ℝ)/24629765556670029816980835306453320800868672819572117785676000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-2824440448203:ℝ)/3200000) + ((-85589104491:ℝ)/80000)*t) + (8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((-863832528614611298803746661767:ℝ)/22937600000000000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((89071111696018428538003001043:ℝ)/1146880000000000000) - 3*((-863832528614611298803746661767:ℝ)/22937600000000000000))*t) + (((443756312138517939:ℝ)/16000000000) + ((44239210740203589:ℝ)/800000000)*t)*(0:ℝ) - (((-989715377982179011:ℝ)/1000000000000) + t * ((-105562312005048353:ℝ)/200000000000)) = (((-2824440448203:ℝ)/3200000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((-863832528614611298803746661767:ℝ)/22937600000000000000) + ((443756312138517939:ℝ)/16000000000)*(0:ℝ) - ((-989715377982179011:ℝ)/1000000000000)) + t*(((-85589104491:ℝ)/80000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((89071111696018428538003001043:ℝ)/1146880000000000000) - 3*((-863832528614611298803746661767:ℝ)/22937600000000000000)) + ((44239210740203589:ℝ)/800000000)*(0:ℝ) - ((-105562312005048353:ℝ)/200000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece22_e22 {q : ℝ} (h0 : ((49:ℝ)/10) ≤ q) (h1 : q ≤ (5:ℝ)) :
    |pieceW q pieceX_22 2 2 - (((10079665718838699:ℝ)/500000000) + (q - ((99:ℝ)/20)) * ((407994812508534671:ℝ)/10000000000))| ≤ ((102936067102964167:ℝ)/1000000000000) := by
  set t := q - ((99:ℝ)/20) with htd
  have hq : q = ((99:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece22_L3 piece22_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((99:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_22 q = ∑ e ∈ Finset.range 10, ([((129743924374175463:ℝ)/6400000000), ((12534660084923163:ℝ)/320000000), ((135201067748307:ℝ)/4000000), ((3429062511237:ℝ)/200000), ((112914308529:ℝ)/20000), ((1252873881:ℝ)/1000), ((4685103:ℝ)/25), ((273116:ℝ)/15), ((3124:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_22; ring
  have h12 : centralNum12_22 q = ∑ e ∈ Finset.range 15, ([((-1928044544048288040009323487447:ℝ)/13107200000000000000), ((-54013906007996031322597823517:ℝ)/655360000000000000), ((2833422347859818592647143737:ℝ)/8192000000000000), ((511284713187872690599675329:ℝ)/819200000000000), ((40998007314064664499556503:ℝ)/81920000000000), ((965906310310003669343769:ℝ)/4096000000000), ((6944250767789545037667:ℝ)/102400000000), ((77417831681029928953:ℝ)/7680000000), ((-598048956735457723:ℝ)/1536000000), ((-43318815602485393:ℝ)/76800000), ((-22136934201009:ℝ)/160000), ((-608562924471:ℝ)/32000), ((-5107743927:ℝ)/3200), ((-12300417:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_22; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((129743924374175463:ℝ)/6400000000), ((12534660084923163:ℝ)/320000000), ((135201067748307:ℝ)/4000000), ((3429062511237:ℝ)/200000), ((112914308529:ℝ)/20000), ((1252873881:ℝ)/1000), ((4685103:ℝ)/25), ((273116:ℝ)/15), ((3124:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-1928044544048288040009323487447:ℝ)/13107200000000000000), ((-54013906007996031322597823517:ℝ)/655360000000000000), ((2833422347859818592647143737:ℝ)/8192000000000000), ((511284713187872690599675329:ℝ)/819200000000000), ((40998007314064664499556503:ℝ)/81920000000000), ((965906310310003669343769:ℝ)/4096000000000), ((6944250767789545037667:ℝ)/102400000000), ((77417831681029928953:ℝ)/7680000000), ((-598048956735457723:ℝ)/1536000000), ((-43318815602485393:ℝ)/76800000), ((-22136934201009:ℝ)/160000), ((-608562924471:ℝ)/32000), ((-5107743927:ℝ)/3200), ((-12300417:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-1928044544048288040009323487447:ℝ)/13107200000000000000), ((-54013906007996031322597823517:ℝ)/655360000000000000), ((2833422347859818592647143737:ℝ)/8192000000000000), ((511284713187872690599675329:ℝ)/819200000000000), ((40998007314064664499556503:ℝ)/81920000000000), ((965906310310003669343769:ℝ)/4096000000000), ((6944250767789545037667:ℝ)/102400000000), ((77417831681029928953:ℝ)/7680000000), ((-598048956735457723:ℝ)/1536000000), ((-43318815602485393:ℝ)/76800000), ((-22136934201009:ℝ)/160000), ((-608562924471:ℝ)/32000), ((-5107743927:ℝ)/3200), ((-12300417:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((129743924374175463:ℝ)/6400000000), ((12534660084923163:ℝ)/320000000), ((135201067748307:ℝ)/4000000), ((3429062511237:ℝ)/200000), ((112914308529:ℝ)/20000), ((1252873881:ℝ)/1000), ((4685103:ℝ)/25), ((273116:ℝ)/15), ((3124:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((129743924374175463:ℝ)/6400000000) + ((12534660084923163:ℝ)/320000000)*t)| ≤ ((832123311352061:ℝ)/9600000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-1928044544048288040009323487447:ℝ)/13107200000000000000), ((-54013906007996031322597823517:ℝ)/655360000000000000), ((2833422347859818592647143737:ℝ)/8192000000000000), ((511284713187872690599675329:ℝ)/819200000000000), ((40998007314064664499556503:ℝ)/81920000000000), ((965906310310003669343769:ℝ)/4096000000000), ((6944250767789545037667:ℝ)/102400000000), ((77417831681029928953:ℝ)/7680000000), ((-598048956735457723:ℝ)/1536000000), ((-43318815602485393:ℝ)/76800000), ((-22136934201009:ℝ)/160000), ((-608562924471:ℝ)/32000), ((-5107743927:ℝ)/3200), ((-12300417:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e) - ((-1928044544048288040009323487447:ℝ)/13107200000000000000) - ((-54013906007996031322597823517:ℝ)/655360000000000000)*t| ≤ ((3099559180844668287229742167:ℝ)/3276800000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-1928044544048288040009323487447:ℝ)/13107200000000000000), ((-54013906007996031322597823517:ℝ)/655360000000000000), ((2833422347859818592647143737:ℝ)/8192000000000000), ((511284713187872690599675329:ℝ)/819200000000000), ((40998007314064664499556503:ℝ)/81920000000000), ((965906310310003669343769:ℝ)/4096000000000), ((6944250767789545037667:ℝ)/102400000000), ((77417831681029928953:ℝ)/7680000000), ((-598048956735457723:ℝ)/1536000000), ((-43318815602485393:ℝ)/76800000), ((-22136934201009:ℝ)/160000), ((-608562924471:ℝ)/32000), ((-5107743927:ℝ)/3200), ((-12300417:ℝ)/160), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e)| ≤ ((124653542923728921530052517477:ℝ)/819200000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((443756312138517939:ℝ)/16000000000) - ((44239210740203589:ℝ)/800000000)*t| ≤ ((250559640159809:ℝ)/2000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (5:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82125:ℝ), (-6663750:ℝ), (115666200:ℝ), (-750437000:ℝ), (2277262000:ℝ), (-3656824320:ℝ), (3359621120:ℝ), (-1817706496:ℝ), ((1625292800:ℝ)/3), (-67108864:ℝ)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_22 q| ≤ ((5157643697789453125:ℝ)/3) := by
    rw [centralNum13_22_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (5:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((178425:ℝ)/2), ((-13176075:ℝ)/2), ((777815145:ℝ)/8), ((-3968389015:ℝ)/8), ((9393350195:ℝ)/8), ((-26366634375:ℝ)/16), ((77851609375:ℝ)/64), ((-25714921875:ℝ)/64), ((5236328125:ℝ)/96), ((-9765625:ℝ)/4)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_22 q| ≤ ((772688717533046875:ℝ)/3) := by
    rw [centralNum23_22_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((28136695072708953678387022961:ℝ)/10000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece22_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece22_E11 h0) m23'
  have c5 := scaled_affine (X := ((11:ℝ)/1000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2))| ≤ ((31487779030122625000000000000000:ℝ)/312910977421398585026999133130711257) := by
    rw [abs_neg, tailWeight_2, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ (5:ℝ)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*(5:ℝ)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece22_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((2570430941234500:ℝ)/4782969)) ≤ (5:ℝ)^6*(8000*(2*(5:ℝ)-3)^2*(1/((65421912084606566554581293153:ℝ)/2000000))*((2570430941234500:ℝ)/4782969)) := by
          gcongr
      _ ≤ ((31487779030122625000000000000000:ℝ)/312910977421398585026999133130711257) := by norm_num
  have c7 := affine_round (α := ((129743924374175463:ℝ)/6400000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((-1928044544048288040009323487447:ℝ)/13107200000000000000) + ((443756312138517939:ℝ)/16000000000)*((11:ℝ)/1000) - ((10079665718838699:ℝ)/500000000)) (β := ((12534660084923163:ℝ)/320000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((-54013906007996031322597823517:ℝ)/655360000000000000) - 3*((-1928044544048288040009323487447:ℝ)/13107200000000000000)) + ((44239210740203589:ℝ)/800000000)*((11:ℝ)/1000) - ((407994812508534671:ℝ)/10000000000)) ht
  have hW : pieceW q pieceX_22 2 2 = centralNum11_22 q + 8*(Real.exp (-(3*((99:ℝ)/20)))*Real.exp (-3*t))*centralNum12_22 q + 18*Real.exp (-8*q)*centralNum13_22 q + 72*Real.exp (-11*q)*centralNum23_22 q + 8*q^7*(2*q-3)^2*((11:ℝ)/1000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2)) := by
    rw [pieceW_22, pieceX_22, sym4_22, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((565804467696109215069792744331227223955088553640599363271:ℝ)/54977155260424173698617935951904733930510430400830620057312500000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((129743924374175463:ℝ)/6400000000) + ((12534660084923163:ℝ)/320000000)*t) + (8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((-1928044544048288040009323487447:ℝ)/13107200000000000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((-54013906007996031322597823517:ℝ)/655360000000000000) - 3*((-1928044544048288040009323487447:ℝ)/13107200000000000000))*t) + (((443756312138517939:ℝ)/16000000000) + ((44239210740203589:ℝ)/800000000)*t)*((11:ℝ)/1000) - (((10079665718838699:ℝ)/500000000) + t * ((407994812508534671:ℝ)/10000000000)) = (((129743924374175463:ℝ)/6400000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((-1928044544048288040009323487447:ℝ)/13107200000000000000) + ((443756312138517939:ℝ)/16000000000)*((11:ℝ)/1000) - ((10079665718838699:ℝ)/500000000)) + t*(((12534660084923163:ℝ)/320000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((-54013906007996031322597823517:ℝ)/655360000000000000) - 3*((-1928044544048288040009323487447:ℝ)/13107200000000000000)) + ((44239210740203589:ℝ)/800000000)*((11:ℝ)/1000) - ((407994812508534671:ℝ)/10000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece22_e23 {q : ℝ} (h0 : ((49:ℝ)/10) ≤ q) (h1 : q ≤ (5:ℝ)) :
    |pieceW q pieceX_22 2 3 - (((294198874249156591:ℝ)/100000000000) + (q - ((99:ℝ)/20)) * ((50600000019380787:ℝ)/10000000000))| ≤ ((14085000065985981:ℝ)/125000000000) := by
  set t := q - ((99:ℝ)/20) with htd
  have hq : q = ((99:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece22_L3 piece22_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((99:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_23 q = ∑ e ∈ Finset.range 9, ([((1275534424229373:ℝ)/320000000), ((215315386270677:ℝ)/32000000), ((8415720514773:ℝ)/1600000), ((197036059869:ℝ)/80000), ((595828629:ℝ)/800), ((29369799:ℝ)/200), ((182343:ℝ)/10), (1294:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_23; ring
  have h12 : centralNum12_23 q = ∑ e ∈ Finset.range 16, ([((-1347641203299181576537702304499057:ℝ)/3670016000000000000000), ((-6196717310693783231147539162941:ℝ)/3670016000000000000), ((-714813198752002864482452270259:ℝ)/262144000000000000), ((-101638650383352997829456160267:ℝ)/45875200000000000), ((-4349269735905099887751268377:ℝ)/4587520000000000), ((-74142634865174180892652617:ℝ)/573440000000000), ((189052808764204235833971:ℝ)/2293760000000), ((15927125552621934666433:ℝ)/286720000000), ((472560450780551747833:ℝ)/28672000000), ((275543514595441851:ℝ)/102400000), ((59722206941752389:ℝ)/358400000), ((-9374646244077:ℝ)/358400), ((-1325576839203:ℝ)/179200), ((-3613144887:ℝ)/4480), ((-20122587:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_23; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((1275534424229373:ℝ)/320000000), ((215315386270677:ℝ)/32000000), ((8415720514773:ℝ)/1600000), ((197036059869:ℝ)/80000), ((595828629:ℝ)/800), ((29369799:ℝ)/200), ((182343:ℝ)/10), (1294:ℝ), (40:ℝ)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-1347641203299181576537702304499057:ℝ)/3670016000000000000000), ((-6196717310693783231147539162941:ℝ)/3670016000000000000), ((-714813198752002864482452270259:ℝ)/262144000000000000), ((-101638650383352997829456160267:ℝ)/45875200000000000), ((-4349269735905099887751268377:ℝ)/4587520000000000), ((-74142634865174180892652617:ℝ)/573440000000000), ((189052808764204235833971:ℝ)/2293760000000), ((15927125552621934666433:ℝ)/286720000000), ((472560450780551747833:ℝ)/28672000000), ((275543514595441851:ℝ)/102400000), ((59722206941752389:ℝ)/358400000), ((-9374646244077:ℝ)/358400), ((-1325576839203:ℝ)/179200), ((-3613144887:ℝ)/4480), ((-20122587:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 14 ht
  have m12 := abs_poly_le (fun e => ([((-1347641203299181576537702304499057:ℝ)/3670016000000000000000), ((-6196717310693783231147539162941:ℝ)/3670016000000000000), ((-714813198752002864482452270259:ℝ)/262144000000000000), ((-101638650383352997829456160267:ℝ)/45875200000000000), ((-4349269735905099887751268377:ℝ)/4587520000000000), ((-74142634865174180892652617:ℝ)/573440000000000), ((189052808764204235833971:ℝ)/2293760000000), ((15927125552621934666433:ℝ)/286720000000), ((472560450780551747833:ℝ)/28672000000), ((275543514595441851:ℝ)/102400000), ((59722206941752389:ℝ)/358400000), ((-9374646244077:ℝ)/358400), ((-1325576839203:ℝ)/179200), ((-3613144887:ℝ)/4480), ((-20122587:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 16 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((1275534424229373:ℝ)/320000000), ((215315386270677:ℝ)/32000000), ((8415720514773:ℝ)/1600000), ((197036059869:ℝ)/80000), ((595828629:ℝ)/800), ((29369799:ℝ)/200), ((182343:ℝ)/10), (1294:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e) - (((1275534424229373:ℝ)/320000000) + ((215315386270677:ℝ)/32000000)*t)| ≤ ((8615765270577:ℝ)/640000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 16, ([((-1347641203299181576537702304499057:ℝ)/3670016000000000000000), ((-6196717310693783231147539162941:ℝ)/3670016000000000000), ((-714813198752002864482452270259:ℝ)/262144000000000000), ((-101638650383352997829456160267:ℝ)/45875200000000000), ((-4349269735905099887751268377:ℝ)/4587520000000000), ((-74142634865174180892652617:ℝ)/573440000000000), ((189052808764204235833971:ℝ)/2293760000000), ((15927125552621934666433:ℝ)/286720000000), ((472560450780551747833:ℝ)/28672000000), ((275543514595441851:ℝ)/102400000), ((59722206941752389:ℝ)/358400000), ((-9374646244077:ℝ)/358400), ((-1325576839203:ℝ)/179200), ((-3613144887:ℝ)/4480), ((-20122587:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e) - ((-1347641203299181576537702304499057:ℝ)/3670016000000000000000) - ((-6196717310693783231147539162941:ℝ)/3670016000000000000)*t| ≤ ((26056747982076511211833985223351:ℝ)/3670016000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 16, ([((-1347641203299181576537702304499057:ℝ)/3670016000000000000000), ((-6196717310693783231147539162941:ℝ)/3670016000000000000), ((-714813198752002864482452270259:ℝ)/262144000000000000), ((-101638650383352997829456160267:ℝ)/45875200000000000), ((-4349269735905099887751268377:ℝ)/4587520000000000), ((-74142634865174180892652617:ℝ)/573440000000000), ((189052808764204235833971:ℝ)/2293760000000), ((15927125552621934666433:ℝ)/286720000000), ((472560450780551747833:ℝ)/28672000000), ((275543514595441851:ℝ)/102400000), ((59722206941752389:ℝ)/358400000), ((-9374646244077:ℝ)/358400), ((-1325576839203:ℝ)/179200), ((-3613144887:ℝ)/4480), ((-20122587:ℝ)/448), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e)| ≤ ((120252415486853374950493803419247:ℝ)/262144000000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((443756312138517939:ℝ)/16000000000) - ((44239210740203589:ℝ)/800000000)*t| ≤ ((250559640159809:ℝ)/2000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (5:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-7627725:ℝ)/2), (173988600:ℝ), (-2299614450:ℝ), (13088188200:ℝ), (-38221499200:ℝ), (63366115840:ℝ), ((-445610508288:ℝ)/7), ((841540698112:ℝ)/21), ((-326820167680:ℝ)/21), ((10133438464:ℝ)/3), ((-2147483648:ℝ)/7)] : List ℝ).getD e 0) 16 hq1'
  have m13' : |centralNum13_23 q| ≤ ((375402493112058359375:ℝ)/6) := by
    rw [centralNum13_23_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (5:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-15801525:ℝ)/4), ((655493865:ℝ)/4), ((-7334421225:ℝ)/4), ((16442962485:ℝ)/2), ((-598626108395:ℝ)/32), ((414013307125:ℝ)/16), ((-4611984703125:ℝ)/224), ((399923828125:ℝ)/48), ((-4353201171875:ℝ)/2688), ((189736328125:ℝ)/1344), ((-244140625:ℝ)/56)] : List ℝ).getD e 0) 16 hq1'
  have m23' : |centralNum23_23 q| ≤ ((16944232010427966640625:ℝ)/2688) := by
    rw [centralNum23_23_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((28136695072708953678387022961:ℝ)/10000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece22_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece22_E11 h0) m23'
  have c5 := scaled_affine (X := (0:ℝ)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((1275534424229373:ℝ)/320000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((-1347641203299181576537702304499057:ℝ)/3670016000000000000000) + ((443756312138517939:ℝ)/16000000000)*(0:ℝ) - ((294198874249156591:ℝ)/100000000000)) (β := ((215315386270677:ℝ)/32000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((-6196717310693783231147539162941:ℝ)/3670016000000000000) - 3*((-1347641203299181576537702304499057:ℝ)/3670016000000000000000)) + ((44239210740203589:ℝ)/800000000)*(0:ℝ) - ((50600000019380787:ℝ)/10000000000)) ht
  have hW : pieceW q pieceX_22 2 3 = centralNum11_23 q + 8*(Real.exp (-(3*((99:ℝ)/20)))*Real.exp (-3*t))*centralNum12_23 q + 18*Real.exp (-8*q)*centralNum13_23 q + 72*Real.exp (-11*q)*centralNum23_23 q + 8*q^7*(2*q-3)^2*(0:ℝ) + (0:ℝ) := by
    rw [pieceW_23, pieceX_22, sym4_23, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((11261339467723127557148748548191329739977377040635085839647:ℝ)/2462976555667002981698083530645332080086867281957211778567600000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((1275534424229373:ℝ)/320000000) + ((215315386270677:ℝ)/32000000)*t) + (8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((-1347641203299181576537702304499057:ℝ)/3670016000000000000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((-6196717310693783231147539162941:ℝ)/3670016000000000000) - 3*((-1347641203299181576537702304499057:ℝ)/3670016000000000000000))*t) + (((443756312138517939:ℝ)/16000000000) + ((44239210740203589:ℝ)/800000000)*t)*(0:ℝ) - (((294198874249156591:ℝ)/100000000000) + t * ((50600000019380787:ℝ)/10000000000)) = (((1275534424229373:ℝ)/320000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((-1347641203299181576537702304499057:ℝ)/3670016000000000000000) + ((443756312138517939:ℝ)/16000000000)*(0:ℝ) - ((294198874249156591:ℝ)/100000000000)) + t*(((215315386270677:ℝ)/32000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((-6196717310693783231147539162941:ℝ)/3670016000000000000) - 3*((-1347641203299181576537702304499057:ℝ)/3670016000000000000000)) + ((44239210740203589:ℝ)/800000000)*(0:ℝ) - ((50600000019380787:ℝ)/10000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece22_e33 {q : ℝ} (h0 : ((49:ℝ)/10) ≤ q) (h1 : q ≤ (5:ℝ)) :
    |pieceW q pieceX_22 3 3 - (((27283231853996969:ℝ)/2000000000) + (q - ((99:ℝ)/20)) * ((179520983814557453:ℝ)/10000000000))| ≤ ((783293048761265469:ℝ)/1000000000000) := by
  set t := q - ((99:ℝ)/20) with htd
  have hq : q = ((99:ℝ)/20) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/20) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece22_L3 piece22_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((99:ℝ)/20))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_33 q = ∑ e ∈ Finset.range 10, ([((173204683189232409:ℝ)/22400000000), ((9975849793219827:ℝ)/560000000), ((978298708699719:ℝ)/56000000), ((3903845199507:ℝ)/400000), ((69399355707:ℝ)/20000), ((822525363:ℝ)/1000), ((6546603:ℝ)/50), ((474462:ℝ)/35), ((5808:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_33; ring
  have h12 : centralNum12_33 q = ∑ e ∈ Finset.range 17, ([((2025445560453349402609237214871741033:ℝ)/1027604480000000000000000), ((295319775086652222959904295557890337:ℝ)/51380224000000000000000), ((3131866729744103591827356716249787:ℝ)/513802240000000000000), ((8291639246172786868564487371887:ℝ)/3670016000000000000), ((-184128704334908571158924081859:ℝ)/183500800000000000), ((-69646589077165321561218889317:ℝ)/45875200000000000), ((-1777820628886617252448296483:ℝ)/2293760000000000), ((-33564178486025199603387819:ℝ)/160563200000000), ((-185111945711134317480543:ℝ)/8028160000000), ((1545923749747783582871:ℝ)/401408000000), ((27713319854992363827:ℝ)/14336000000), ((233708774981291793:ℝ)/716800000), ((160848872280351:ℝ)/7168000), ((-365111883963:ℝ)/358400), ((-40606048683:ℝ)/125440), ((-767459853:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_33; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((173204683189232409:ℝ)/22400000000), ((9975849793219827:ℝ)/560000000), ((978298708699719:ℝ)/56000000), ((3903845199507:ℝ)/400000), ((69399355707:ℝ)/20000), ((822525363:ℝ)/1000), ((6546603:ℝ)/50), ((474462:ℝ)/35), ((5808:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((2025445560453349402609237214871741033:ℝ)/1027604480000000000000000), ((295319775086652222959904295557890337:ℝ)/51380224000000000000000), ((3131866729744103591827356716249787:ℝ)/513802240000000000000), ((8291639246172786868564487371887:ℝ)/3670016000000000000), ((-184128704334908571158924081859:ℝ)/183500800000000000), ((-69646589077165321561218889317:ℝ)/45875200000000000), ((-1777820628886617252448296483:ℝ)/2293760000000000), ((-33564178486025199603387819:ℝ)/160563200000000), ((-185111945711134317480543:ℝ)/8028160000000), ((1545923749747783582871:ℝ)/401408000000), ((27713319854992363827:ℝ)/14336000000), ((233708774981291793:ℝ)/716800000), ((160848872280351:ℝ)/7168000), ((-365111883963:ℝ)/358400), ((-40606048683:ℝ)/125440), ((-767459853:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 15 ht
  have m12 := abs_poly_le (fun e => ([((2025445560453349402609237214871741033:ℝ)/1027604480000000000000000), ((295319775086652222959904295557890337:ℝ)/51380224000000000000000), ((3131866729744103591827356716249787:ℝ)/513802240000000000000), ((8291639246172786868564487371887:ℝ)/3670016000000000000), ((-184128704334908571158924081859:ℝ)/183500800000000000), ((-69646589077165321561218889317:ℝ)/45875200000000000), ((-1777820628886617252448296483:ℝ)/2293760000000000), ((-33564178486025199603387819:ℝ)/160563200000000), ((-185111945711134317480543:ℝ)/8028160000000), ((1545923749747783582871:ℝ)/401408000000), ((27713319854992363827:ℝ)/14336000000), ((233708774981291793:ℝ)/716800000), ((160848872280351:ℝ)/7168000), ((-365111883963:ℝ)/358400), ((-40606048683:ℝ)/125440), ((-767459853:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 17 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((173204683189232409:ℝ)/22400000000), ((9975849793219827:ℝ)/560000000), ((978298708699719:ℝ)/56000000), ((3903845199507:ℝ)/400000), ((69399355707:ℝ)/20000), ((822525363:ℝ)/1000), ((6546603:ℝ)/50), ((474462:ℝ)/35), ((5808:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e) - (((173204683189232409:ℝ)/22400000000) + ((9975849793219827:ℝ)/560000000)*t)| ≤ ((1006117224327937:ℝ)/22400000000) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 17, ([((2025445560453349402609237214871741033:ℝ)/1027604480000000000000000), ((295319775086652222959904295557890337:ℝ)/51380224000000000000000), ((3131866729744103591827356716249787:ℝ)/513802240000000000000), ((8291639246172786868564487371887:ℝ)/3670016000000000000), ((-184128704334908571158924081859:ℝ)/183500800000000000), ((-69646589077165321561218889317:ℝ)/45875200000000000), ((-1777820628886617252448296483:ℝ)/2293760000000000), ((-33564178486025199603387819:ℝ)/160563200000000), ((-185111945711134317480543:ℝ)/8028160000000), ((1545923749747783582871:ℝ)/401408000000), ((27713319854992363827:ℝ)/14336000000), ((233708774981291793:ℝ)/716800000), ((160848872280351:ℝ)/7168000), ((-365111883963:ℝ)/358400), ((-40606048683:ℝ)/125440), ((-767459853:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e) - ((2025445560453349402609237214871741033:ℝ)/1027604480000000000000000) - ((295319775086652222959904295557890337:ℝ)/51380224000000000000000)*t| ≤ ((1595648566661060707537231023479329:ℝ)/102760448000000000000000) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 17, ([((2025445560453349402609237214871741033:ℝ)/1027604480000000000000000), ((295319775086652222959904295557890337:ℝ)/51380224000000000000000), ((3131866729744103591827356716249787:ℝ)/513802240000000000000), ((8291639246172786868564487371887:ℝ)/3670016000000000000), ((-184128704334908571158924081859:ℝ)/183500800000000000), ((-69646589077165321561218889317:ℝ)/45875200000000000), ((-1777820628886617252448296483:ℝ)/2293760000000000), ((-33564178486025199603387819:ℝ)/160563200000000), ((-185111945711134317480543:ℝ)/8028160000000), ((1545923749747783582871:ℝ)/401408000000), ((27713319854992363827:ℝ)/14336000000), ((233708774981291793:ℝ)/716800000), ((160848872280351:ℝ)/7168000), ((-365111883963:ℝ)/358400), ((-40606048683:ℝ)/125440), ((-767459853:ℝ)/31360), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e)| ≤ ((116836091060330611632225691033221233:ℝ)/51380224000000000000000) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((443756312138517939:ℝ)/16000000000), ((44239210740203589:ℝ)/800000000), ((244185715112823:ℝ)/5000000), ((1567404509517:ℝ)/62500), ((412680778587:ℝ)/50000), ((4514271993:ℝ)/2500), ((32831568:ℝ)/125), ((612432:ℝ)/25), ((6648:ℝ)/5), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((443756312138517939:ℝ)/16000000000) - ((44239210740203589:ℝ)/800000000)*t| ≤ ((250559640159809:ℝ)/2000000000) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (5:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-8120475:ℝ)/4), ((464861025:ℝ)/2), (-5906535975:ℝ), ((411904731750:ℝ)/7), ((-2024051769000:ℝ)/7), ((5554394637600:ℝ)/7), (-1314913862656:ℝ), ((9709155336192:ℝ)/7), ((-6724555112448:ℝ)/7), ((1313173667840:ℝ)/3), ((-6168244125696:ℝ)/49), ((3004329623552:ℝ)/147), ((-68719476736:ℝ)/49)] : List ℝ).getD e 0) 17 hq1'
  have m13' : |centralNum13_33 q| ≤ ((1444790872659160077546875:ℝ)/588) := by
    rw [centralNum13_33_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ (5:ℝ) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-16872075:ℝ)/8), ((1833754545:ℝ)/8), ((-83998007145:ℝ)/16), ((4929124002765:ℝ)/112), ((-76723155584685:ℝ)/448), ((164888745653055:ℝ)/448), ((-63358359907625:ℝ)/128), ((364713160040625:ℝ)/896), ((-334937462578125:ℝ)/1792), ((245466998046875:ℝ)/5376), ((-72144521484375:ℝ)/12544), ((6518798828125:ℝ)/18816), ((-6103515625:ℝ)/784)] : List ℝ).getD e 0) 17 hq1'
  have m23' : |centralNum23_33 q| ≤ ((6537846765872928631765625:ℝ)/37632) := by
    rw [centralNum23_33_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((28136695072708953678387022961:ℝ)/10000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece22_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece22_E11 h0) m23'
  have c5 := scaled_affine (X := ((11:ℝ)/1000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3))| ≤ ((40530004705639085875000000000000000:ℝ)/8448596390377761795728976594529203939) := by
    rw [abs_neg, tailWeight_3, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ (5:ℝ)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*(5:ℝ)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece22_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((3308571812705231500:ℝ)/129140163)) ≤ (5:ℝ)^6*(8000*(2*(5:ℝ)-3)^2*(1/((65421912084606566554581293153:ℝ)/2000000))*((3308571812705231500:ℝ)/129140163)) := by
          gcongr
      _ ≤ ((40530004705639085875000000000000000:ℝ)/8448596390377761795728976594529203939) := by norm_num
  have c7 := affine_round (α := ((173204683189232409:ℝ)/22400000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((2025445560453349402609237214871741033:ℝ)/1027604480000000000000000) + ((443756312138517939:ℝ)/16000000000)*((11:ℝ)/1000) - ((27283231853996969:ℝ)/2000000000)) (β := ((9975849793219827:ℝ)/560000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((295319775086652222959904295557890337:ℝ)/51380224000000000000000) - 3*((2025445560453349402609237214871741033:ℝ)/1027604480000000000000000)) + ((44239210740203589:ℝ)/800000000)*((11:ℝ)/1000) - ((179520983814557453:ℝ)/10000000000)) ht
  have hW : pieceW q pieceX_22 3 3 = centralNum11_33 q + 8*(Real.exp (-(3*((99:ℝ)/20)))*Real.exp (-3*t))*centralNum12_33 q + 18*Real.exp (-8*q)*centralNum13_33 q + 72*Real.exp (-11*q)*centralNum23_33 q + 8*q^7*(2*q-3)^2*((11:ℝ)/1000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3)) := by
    rw [pieceW_33, pieceX_22, sym4_33, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((669141915480706833665281688845779088458513634437387554113311:ℝ)/34481671779338041743773169429034649121216141947400964899946400000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((173204683189232409:ℝ)/22400000000) + ((9975849793219827:ℝ)/560000000)*t) + (8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((2025445560453349402609237214871741033:ℝ)/1027604480000000000000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((295319775086652222959904295557890337:ℝ)/51380224000000000000000) - 3*((2025445560453349402609237214871741033:ℝ)/1027604480000000000000000))*t) + (((443756312138517939:ℝ)/16000000000) + ((44239210740203589:ℝ)/800000000)*t)*((11:ℝ)/1000) - (((27283231853996969:ℝ)/2000000000) + t * ((179520983814557453:ℝ)/10000000000)) = (((173204683189232409:ℝ)/22400000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*((2025445560453349402609237214871741033:ℝ)/1027604480000000000000000) + ((443756312138517939:ℝ)/16000000000)*((11:ℝ)/1000) - ((27283231853996969:ℝ)/2000000000)) + t*(((9975849793219827:ℝ)/560000000) + 8*(((1/((28136695072708953678387022961:ℝ)/10000000000000000000000))+(1/((281366035955653318118208556173:ℝ)/100000000000000000000000)))/2)*(((295319775086652222959904295557890337:ℝ)/51380224000000000000000) - 3*((2025445560453349402609237214871741033:ℝ)/1027604480000000000000000)) + ((44239210740203589:ℝ)/800000000)*((11:ℝ)/1000) - ((179520983814557453:ℝ)/10000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece22_plus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((78816018792626097:ℝ)/2500000000) + ((1:ℝ)/20)*((304288381923254047:ℝ)/5000000000) - (((67341254832187491:ℝ)/500000000000) + ((120092828055707963:ℝ)/12500000000000) + ((336064482491146427:ℝ)/100000000000000) + ((68088543599475511:ℝ)/20000000000000)))
      (((-176675379468763363:ℝ)/50000000000) + ((1:ℝ)/20)*((-246104541499386427:ℝ)/50000000000))
      (((-12241326966364999:ℝ)/250000000000) + ((1:ℝ)/20)*((-241520357516744413:ℝ)/10000000000000))
      (((164218440278201667:ℝ)/2000000000000) + ((1:ℝ)/20)*((-930513432452652089:ℝ)/10000000000000))
      (((222547663858379939:ℝ)/10000000000) + ((1:ℝ)/20)*((207156823562862707:ℝ)/5000000000) - (((120092828055707963:ℝ)/12500000000000) + ((456329821502365173:ℝ)/5000000000000) + ((150711462124311413:ℝ)/10000000000000) + ((22145194768172623:ℝ)/2500000000000)))
      (((-146498213131604141:ℝ)/100000000000) + ((1:ℝ)/20)*((-8193257219737743:ℝ)/4000000000))
      (((-989715377982179011:ℝ)/1000000000000) + ((1:ℝ)/20)*((-105562312005048353:ℝ)/200000000000))
      (((10079665718838699:ℝ)/500000000) + ((1:ℝ)/20)*((407994812508534671:ℝ)/10000000000) - (((336064482491146427:ℝ)/100000000000000) + ((150711462124311413:ℝ)/10000000000000) + ((102936067102964167:ℝ)/1000000000000) + ((14085000065985981:ℝ)/125000000000)))
      (((294198874249156591:ℝ)/100000000000) + ((1:ℝ)/20)*((50600000019380787:ℝ)/10000000000))
      (((27283231853996969:ℝ)/2000000000) + ((1:ℝ)/20)*((179520983814557453:ℝ)/10000000000) - (((68088543599475511:ℝ)/20000000000000) + ((22145194768172623:ℝ)/2500000000000) + ((14085000065985981:ℝ)/125000000000) + ((783293048761265469:ℝ)/1000000000000))) i j :=
  quadForm_nonneg_of_ldl ((1720911816418463120557:ℝ)/50000000000000) ((2046721450647122273106899346907346323591401:ℝ)/86045590820923156027850000000000000) ((35794987371426520504827932033615434628765676536417081711007962927:ℝ)/1637377160517697818485519477525877058873120800000000000000) ((94072265557974149957053563950916192008426809811093016740894654494482346265991399361617:ℝ)/7158997474285304100965586406723086925753135307283416342201592585400000000000000) ((-188980606543732684350:ℝ)/1720911816418463120557) ((-49431438081816471:ℝ)/33909592441743115676) ((15491330595367514611:ℝ)/6883647265673852482228) ((-270683518207700846864638375934387233879025:ℝ)/4093442901294244546213798693814692647182802) ((-28899849018744539580556211715167116201550:ℝ)/682240483549040757702299782302448774530467) ((5122490177017299596814216313079208180538651216981293541652233899:ℝ)/35794987371426520504827932033615434628765676536417081711007962927)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece22_minus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((78816018792626097:ℝ)/2500000000) - ((1:ℝ)/20)*((304288381923254047:ℝ)/5000000000) - (((67341254832187491:ℝ)/500000000000) + ((120092828055707963:ℝ)/12500000000000) + ((336064482491146427:ℝ)/100000000000000) + ((68088543599475511:ℝ)/20000000000000)))
      (((-176675379468763363:ℝ)/50000000000) - ((1:ℝ)/20)*((-246104541499386427:ℝ)/50000000000))
      (((-12241326966364999:ℝ)/250000000000) - ((1:ℝ)/20)*((-241520357516744413:ℝ)/10000000000000))
      (((164218440278201667:ℝ)/2000000000000) - ((1:ℝ)/20)*((-930513432452652089:ℝ)/10000000000000))
      (((222547663858379939:ℝ)/10000000000) - ((1:ℝ)/20)*((207156823562862707:ℝ)/5000000000) - (((120092828055707963:ℝ)/12500000000000) + ((456329821502365173:ℝ)/5000000000000) + ((150711462124311413:ℝ)/10000000000000) + ((22145194768172623:ℝ)/2500000000000)))
      (((-146498213131604141:ℝ)/100000000000) - ((1:ℝ)/20)*((-8193257219737743:ℝ)/4000000000))
      (((-989715377982179011:ℝ)/1000000000000) - ((1:ℝ)/20)*((-105562312005048353:ℝ)/200000000000))
      (((10079665718838699:ℝ)/500000000) - ((1:ℝ)/20)*((407994812508534671:ℝ)/10000000000) - (((336064482491146427:ℝ)/100000000000000) + ((150711462124311413:ℝ)/10000000000000) + ((102936067102964167:ℝ)/1000000000000) + ((14085000065985981:ℝ)/125000000000)))
      (((294198874249156591:ℝ)/100000000000) - ((1:ℝ)/20)*((50600000019380787:ℝ)/10000000000))
      (((27283231853996969:ℝ)/2000000000) - ((1:ℝ)/20)*((179520983814557453:ℝ)/10000000000) - (((68088543599475511:ℝ)/20000000000000) + ((22145194768172623:ℝ)/2500000000000) + ((14085000065985981:ℝ)/125000000000) + ((783293048761265469:ℝ)/1000000000000))) i j :=
  quadForm_nonneg_of_ldl ((1416623434495209073557:ℝ)/50000000000000) ((1393742111703378613591194335582018059521401:ℝ)/70831171724760453677850000000000000) ((19835856659925216670867542912200314297533532716014971926963909127:ℝ)/1114993689362702890872955468465614447617120800000000000000) ((45236195126505129527031774821377733227670243622619411222357844059385760532238754610017:ℝ)/3967171331985043334173508582440062859506706543202994385392781825400000000000000) ((-164370152393794041650:ℝ)/1416623434495209073557) ((-9551541215575254787:ℝ)/5666493737980836294228) ((17352357460272818789:ℝ)/5666493737980836294228) ((-193809345748594614531133248843105217162525:ℝ)/2787484223406757227182388671164036119042802) ((-67520371924134684324829309067080949695625:ℝ)/1393742111703378613591194335582018059521401) ((2924468429546171462852973366826072606662263258938164911664218099:ℝ)/19835856659925216670867542912200314297533532716014971926963909127)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

/-- **Piece 22.** The piece matrix is positive semidefinite on `q ∈ [49/10, 5]`. -/
theorem piece_22 {q : ℝ} (h0 : ((49:ℝ)/10) ≤ q) (h1 : q ≤ (5:ℝ)) (y : Fin 4 → ℝ) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceW q pieceX_22 i j :=
  pieceForm_nonneg (pieceW_symm (sym4_symm _ _ _ _ _ _ _ _ _ _) q) (by norm_num : (0:ℝ) < ((1:ℝ)/20))
    (abs_le.mpr ⟨by linarith, by linarith⟩)
    (piece22_e00 h0 h1) (piece22_e01 h0 h1) (piece22_e02 h0 h1) (piece22_e03 h0 h1) (piece22_e11 h0 h1) (piece22_e12 h0 h1) (piece22_e13 h0 h1) (piece22_e22 h0 h1) (piece22_e23 h0 h1) (piece22_e33 h0 h1)
    piece22_plus piece22_minus y

/-! #### Piece 23 (bulk), `q ∈ [5, 21/4]` -/

/-- The compensation matrix of piece 23. -/
def pieceX_23 : Fin 4 → Fin 4 → ℝ :=
  sym4 ((-941127715633:ℝ)/1000000000000) ((103790491727:ℝ)/1000000000000) ((1217466811:ℝ)/500000000000) ((383491440859:ℝ)/1000000000000000) ((-324871849137:ℝ)/500000000000) ((443075421299:ℝ)/10000000000000) ((231174164601:ℝ)/10000000000000) ((-287792983157:ℝ)/500000000000) ((-902472723309:ℝ)/10000000000000) ((-145820380919:ℝ)/500000000000)

theorem piece23_L3 : ((23781960869657420254275816301:ℝ)/5000000000000000000000) ≤ Real.exp ((3:ℝ)*((41:ℝ)/8)) := by
  have h := le_exp_nat_add 15 (f := ((3:ℝ)/8)) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((41:ℝ)/8) = ((15:ℕ):ℝ) + ((3:ℝ)/8) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece23_U3 : Real.exp ((3:ℝ)*((41:ℝ)/8)) ≤ ((475639221747518193893788855829:ℝ)/100000000000000000000000) := by
  have h := exp_nat_add_le 15 (f := ((3:ℝ)/8)) (by norm_num) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((41:ℝ)/8) = ((15:ℕ):ℝ) + ((3:ℝ)/8) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem piece23_L8_at : ((58846316571532318998290536717:ℝ)/250000000000) ≤ Real.exp ((8:ℝ)*(5:ℝ)) := by
  have h := le_exp_nat_add 40 (f := (0:ℝ)) (by norm_num)
  rw [show ((8:ℝ):ℝ)*(5:ℝ) = ((40:ℕ):ℝ) + (0:ℝ) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece23_E8 {q : ℝ} (h0 : (5:ℝ) ≤ q) : Real.exp (-((8:ℝ))*q) ≤ 1/((58846316571532318998290536717:ℝ)/250000000000) := by
  have hm : Real.exp (-((8:ℝ))*q) ≤ Real.exp (-((8:ℝ)*(5:ℝ))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece23_L8_at (le_refl _)).2

theorem piece23_L11_at : ((769478524038003678215770643237:ℝ)/1000000) ≤ Real.exp ((11:ℝ)*(5:ℝ)) := by
  have h := le_exp_nat_add 55 (f := (0:ℝ)) (by norm_num)
  rw [show ((11:ℝ):ℝ)*(5:ℝ) = ((55:ℕ):ℝ) + (0:ℝ) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece23_E11 {q : ℝ} (h0 : (5:ℝ) ≤ q) : Real.exp (-((11:ℝ))*q) ≤ 1/((769478524038003678215770643237:ℝ)/1000000) := by
  have hm : Real.exp (-((11:ℝ))*q) ≤ Real.exp (-((11:ℝ)*(5:ℝ))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece23_L11_at (le_refl _)).2

theorem piece23_Lt_at : ((188454275542913162474969854897:ℝ)/2000000) ≤ Real.exp (((529:ℝ)/50)*(5:ℝ)) := by
  have h := le_exp_nat_add 52 (f := ((9:ℝ)/10)) (by norm_num)
  rw [show (((529:ℝ)/50):ℝ)*(5:ℝ) = ((52:ℕ):ℝ) + ((9:ℝ)/10) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece23_Et {q : ℝ} (h0 : (5:ℝ) ≤ q) : Real.exp (-(((529:ℝ)/50))*q) ≤ 1/((188454275542913162474969854897:ℝ)/2000000) := by
  have hm : Real.exp (-(((529:ℝ)/50))*q) ≤ Real.exp (-(((529:ℝ)/50)*(5:ℝ))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece23_Lt_at (le_refl _)).2

theorem piece23_e00 {q : ℝ} (h0 : (5:ℝ) ≤ q) (h1 : q ≤ ((21:ℝ)/4)) :
    |pieceW q pieceX_23 0 0 - (((674913930295742753:ℝ)/100000000000) + (q - ((41:ℝ)/8)) * ((21007787300673907:ℝ)/2000000000))| ≤ ((42280722753680473:ℝ)/20000000000) := by
  set t := q - ((41:ℝ)/8) with htd
  have hq : q = ((41:ℝ)/8) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/8) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece23_L3 piece23_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((41:ℝ)/8))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_00 q = ∑ e ∈ Finset.range 10, ([((182484754626497:ℝ)/4194304), ((42451681601817:ℝ)/524288), ((1100749765701:ℝ)/16384), ((66758603625:ℝ)/2048), ((5214769623:ℝ)/512), ((135944151:ℝ)/64), ((1182153:ℝ)/4), (26442:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_00; ring
  have h12 : centralNum12_00 q = ∑ e ∈ Finset.range 11, ([((-36936121812901055:ℝ)/8388608), ((-18921009471403203:ℝ)/2097152), ((-2181455597635593:ℝ)/262144), ((-37267094000979:ℝ)/8192), ((-835687456695:ℝ)/512), ((-102801348237:ℝ)/256), ((-2195342499:ℝ)/32), ((-16071687:ℝ)/2), (-617586:ℝ), (-28120:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_00; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((182484754626497:ℝ)/4194304), ((42451681601817:ℝ)/524288), ((1100749765701:ℝ)/16384), ((66758603625:ℝ)/2048), ((5214769623:ℝ)/512), ((135944151:ℝ)/64), ((1182153:ℝ)/4), (26442:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-36936121812901055:ℝ)/8388608), ((-18921009471403203:ℝ)/2097152), ((-2181455597635593:ℝ)/262144), ((-37267094000979:ℝ)/8192), ((-835687456695:ℝ)/512), ((-102801348237:ℝ)/256), ((-2195342499:ℝ)/32), ((-16071687:ℝ)/2), (-617586:ℝ), (-28120:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 9 ht
  have m12 := abs_poly_le (fun e => ([((-36936121812901055:ℝ)/8388608), ((-18921009471403203:ℝ)/2097152), ((-2181455597635593:ℝ)/262144), ((-37267094000979:ℝ)/8192), ((-835687456695:ℝ)/512), ((-102801348237:ℝ)/256), ((-2195342499:ℝ)/32), ((-16071687:ℝ)/2), (-617586:ℝ), (-28120:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 11 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((182484754626497:ℝ)/4194304), ((42451681601817:ℝ)/524288), ((1100749765701:ℝ)/16384), ((66758603625:ℝ)/2048), ((5214769623:ℝ)/512), ((135944151:ℝ)/64), ((1182153:ℝ)/4), (26442:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - (((182484754626497:ℝ)/4194304) + ((42451681601817:ℝ)/524288)*t)| ≤ ((2340369843347:ℝ)/2097152) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 11, ([((-36936121812901055:ℝ)/8388608), ((-18921009471403203:ℝ)/2097152), ((-2181455597635593:ℝ)/262144), ((-37267094000979:ℝ)/8192), ((-835687456695:ℝ)/512), ((-102801348237:ℝ)/256), ((-2195342499:ℝ)/32), ((-16071687:ℝ)/2), (-617586:ℝ), (-28120:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e) - ((-36936121812901055:ℝ)/8388608) - ((-18921009471403203:ℝ)/2097152)*t| ≤ ((2337419531582399:ℝ)/16777216) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 11, ([((-36936121812901055:ℝ)/8388608), ((-18921009471403203:ℝ)/2097152), ((-2181455597635593:ℝ)/262144), ((-37267094000979:ℝ)/8192), ((-835687456695:ℝ)/512), ((-102801348237:ℝ)/256), ((-2195342499:ℝ)/32), ((-16071687:ℝ)/2), (-617586:ℝ), (-28120:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((185802094978101:ℝ)/32768) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((163788344333921:ℝ)/4194304) - ((39259611551865:ℝ)/524288)*t| ≤ ((2218722018707:ℝ)/2097152) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/4) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (600:ℝ), (-7776:ℝ), (16800:ℝ), (-9216:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m13' : |centralNum13_00 q| ≤ ((1655252600746689:ℝ)/8192) := by
    rw [centralNum13_00_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/4) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (780:ℝ), (-6156:ℝ), (15288:ℝ), (-14400:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m23' : |centralNum23_00 q| ≤ ((9143044068443859:ℝ)/32768) := by
    rw [centralNum23_00_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((475639221747518193893788855829:ℝ)/100000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece23_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece23_E11 h0) m23'
  have c5 := scaled_affine (X := ((-941127715633:ℝ)/1000000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0))| ≤ ((30059950254892578125000:ℝ)/1696088479886218462274728694073) := by
    rw [abs_neg, tailWeight_0, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((21:ℝ)/4)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((21:ℝ)/4)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece23_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((10465499600:ℝ)/59049)) ≤ ((21:ℝ)/4)^6*(8000*(2*((21:ℝ)/4)-3)^2*(1/((188454275542913162474969854897:ℝ)/2000000))*((10465499600:ℝ)/59049)) := by
          gcongr
      _ ≤ ((30059950254892578125000:ℝ)/1696088479886218462274728694073) := by norm_num
  have c7 := affine_round (α := ((182484754626497:ℝ)/4194304) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((-36936121812901055:ℝ)/8388608) + ((163788344333921:ℝ)/4194304)*((-941127715633:ℝ)/1000000000000) - ((674913930295742753:ℝ)/100000000000)) (β := ((42451681601817:ℝ)/524288) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((-18921009471403203:ℝ)/2097152) - 3*((-36936121812901055:ℝ)/8388608)) + ((39259611551865:ℝ)/524288)*((-941127715633:ℝ)/1000000000000) - ((21007787300673907:ℝ)/2000000000)) ht
  have hW : pieceW q pieceX_23 0 0 = centralNum11_00 q + 8*(Real.exp (-(3*((41:ℝ)/8)))*Real.exp (-3*t))*centralNum12_00 q + 18*Real.exp (-8*q)*centralNum13_00 q + 72*Real.exp (-11*q)*centralNum23_00 q + 8*q^7*(2*q-3)^2*((-941127715633:ℝ)/1000000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0)) := by
    rw [pieceW_00, pieceX_23, sym4_00, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((12466367441363497388660338567006324056080251118967234394219993343:ℝ)/1824785732577430798239602972113805601075054298696076322370748416000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((182484754626497:ℝ)/4194304) + ((42451681601817:ℝ)/524288)*t) + (8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((-36936121812901055:ℝ)/8388608) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((-18921009471403203:ℝ)/2097152) - 3*((-36936121812901055:ℝ)/8388608))*t) + (((163788344333921:ℝ)/4194304) + ((39259611551865:ℝ)/524288)*t)*((-941127715633:ℝ)/1000000000000) - (((674913930295742753:ℝ)/100000000000) + t * ((21007787300673907:ℝ)/2000000000)) = (((182484754626497:ℝ)/4194304) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((-36936121812901055:ℝ)/8388608) + ((163788344333921:ℝ)/4194304)*((-941127715633:ℝ)/1000000000000) - ((674913930295742753:ℝ)/100000000000)) + t*(((42451681601817:ℝ)/524288) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((-18921009471403203:ℝ)/2097152) - 3*((-36936121812901055:ℝ)/8388608)) + ((39259611551865:ℝ)/524288)*((-941127715633:ℝ)/1000000000000) - ((21007787300673907:ℝ)/2000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece23_e01 {q : ℝ} (h0 : (5:ℝ) ≤ q) (h1 : q ≤ ((21:ℝ)/4)) :
    |pieceW q pieceX_23 0 1 - (((-439053637129836321:ℝ)/1000000000000) + (q - ((41:ℝ)/8)) * ((42638329277237611:ℝ)/25000000000))| ≤ ((3603643440639837:ℝ)/20000000000) := by
  set t := q - ((41:ℝ)/8) with htd
  have hq : q = ((41:ℝ)/8) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/8) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece23_L3 piece23_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((41:ℝ)/8))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_01 q = ∑ e ∈ Finset.range 8, ([((-584262821643:ℝ)/131072), ((-99752189061:ℝ)/16384), ((-7298940663:ℝ)/2048), ((-296704905:ℝ)/256), ((-7236705:ℝ)/32), ((-105903:ℝ)/4), (-1722:ℝ), (-48:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_01; ring
  have h12 : centralNum12_01 q = ∑ e ∈ Finset.range 12, ([((-2754653722604155893:ℝ)/134217728), ((-1628925901016014563:ℝ)/33554432), ((-54638573719897413:ℝ)/1048576), ((-17567522025526911:ℝ)/524288), ((-235017210471675:ℝ)/16384), ((-17583282342171:ℝ)/4096), ((-1832944155:ℝ)/2), ((-8933344851:ℝ)/64), ((-118908333:ℝ)/8), ((-2107815:ℝ)/2), (-44784:ℝ), (-864:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_01; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-584262821643:ℝ)/131072), ((-99752189061:ℝ)/16384), ((-7298940663:ℝ)/2048), ((-296704905:ℝ)/256), ((-7236705:ℝ)/32), ((-105903:ℝ)/4), (-1722:ℝ), (-48:ℝ)] : List ℝ).getD e 0) 6 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-2754653722604155893:ℝ)/134217728), ((-1628925901016014563:ℝ)/33554432), ((-54638573719897413:ℝ)/1048576), ((-17567522025526911:ℝ)/524288), ((-235017210471675:ℝ)/16384), ((-17583282342171:ℝ)/4096), ((-1832944155:ℝ)/2), ((-8933344851:ℝ)/64), ((-118908333:ℝ)/8), ((-2107815:ℝ)/2), (-44784:ℝ), (-864:ℝ)] : List ℝ).getD e 0) 10 ht
  have m12 := abs_poly_le (fun e => ([((-2754653722604155893:ℝ)/134217728), ((-1628925901016014563:ℝ)/33554432), ((-54638573719897413:ℝ)/1048576), ((-17567522025526911:ℝ)/524288), ((-235017210471675:ℝ)/16384), ((-17583282342171:ℝ)/4096), ((-1832944155:ℝ)/2), ((-8933344851:ℝ)/64), ((-118908333:ℝ)/8), ((-2107815:ℝ)/2), (-44784:ℝ), (-864:ℝ)] : List ℝ).getD e 0) 12 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 8, ([((-584262821643:ℝ)/131072), ((-99752189061:ℝ)/16384), ((-7298940663:ℝ)/2048), ((-296704905:ℝ)/256), ((-7236705:ℝ)/32), ((-105903:ℝ)/4), (-1722:ℝ), (-48:ℝ)] : List ℝ).getD e 0 * t^e) - (((-584262821643:ℝ)/131072) + ((-99752189061:ℝ)/16384)*t)| ≤ ((475186815:ℝ)/8192) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 12, ([((-2754653722604155893:ℝ)/134217728), ((-1628925901016014563:ℝ)/33554432), ((-54638573719897413:ℝ)/1048576), ((-17567522025526911:ℝ)/524288), ((-235017210471675:ℝ)/16384), ((-17583282342171:ℝ)/4096), ((-1832944155:ℝ)/2), ((-8933344851:ℝ)/64), ((-118908333:ℝ)/8), ((-2107815:ℝ)/2), (-44784:ℝ), (-864:ℝ)] : List ℝ).getD e 0 * t^e) - ((-2754653722604155893:ℝ)/134217728) - ((-1628925901016014563:ℝ)/33554432)*t| ≤ ((237098008885720371:ℝ)/268435456) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 12, ([((-2754653722604155893:ℝ)/134217728), ((-1628925901016014563:ℝ)/33554432), ((-54638573719897413:ℝ)/1048576), ((-17567522025526911:ℝ)/524288), ((-235017210471675:ℝ)/16384), ((-17583282342171:ℝ)/4096), ((-1832944155:ℝ)/2), ((-8933344851:ℝ)/64), ((-118908333:ℝ)/8), ((-2107815:ℝ)/2), (-44784:ℝ), (-864:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((7202472026474655:ℝ)/262144) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((163788344333921:ℝ)/4194304) - ((39259611551865:ℝ)/524288)*t| ≤ ((2218722018707:ℝ)/2097152) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/4) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-6288:ℝ), (81024:ℝ), (-238720:ℝ), (246784:ℝ), (-98304:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m13' : |centralNum13_01 q| ≤ ((26431538079888333:ℝ)/2048) := by
    rw [centralNum13_01_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/4) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-7368:ℝ), (59208:ℝ), (-155734:ℝ), (205300:ℝ), (-60000:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m23' : |centralNum23_01 q| ≤ ((2302501917167846289:ℝ)/262144) := by
    rw [centralNum23_01_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((475639221747518193893788855829:ℝ)/100000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece23_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece23_E11 h0) m23'
  have c5 := scaled_affine (X := ((103790491727:ℝ)/1000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-584262821643:ℝ)/131072) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((-2754653722604155893:ℝ)/134217728) + ((163788344333921:ℝ)/4194304)*((103790491727:ℝ)/1000000000000) - ((-439053637129836321:ℝ)/1000000000000)) (β := ((-99752189061:ℝ)/16384) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((-1628925901016014563:ℝ)/33554432) - 3*((-2754653722604155893:ℝ)/134217728)) + ((39259611551865:ℝ)/524288)*((103790491727:ℝ)/1000000000000) - ((42638329277237611:ℝ)/25000000000)) ht
  have hW : pieceW q pieceX_23 0 1 = centralNum11_01 q + 8*(Real.exp (-(3*((41:ℝ)/8)))*Real.exp (-3*t))*centralNum12_01 q + 18*Real.exp (-8*q)*centralNum13_01 q + 72*Real.exp (-11*q)*centralNum23_01 q + 8*q^7*(2*q-3)^2*((103790491727:ℝ)/1000000000000) + (0:ℝ) := by
    rw [pieceW_01, pieceX_23, sym4_01, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((10106920169481172514202600548512132866766817594611957696935699853:ℝ)/23722214523506600377114838637479472813975705883048992190819729408000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-584262821643:ℝ)/131072) + ((-99752189061:ℝ)/16384)*t) + (8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((-2754653722604155893:ℝ)/134217728) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((-1628925901016014563:ℝ)/33554432) - 3*((-2754653722604155893:ℝ)/134217728))*t) + (((163788344333921:ℝ)/4194304) + ((39259611551865:ℝ)/524288)*t)*((103790491727:ℝ)/1000000000000) - (((-439053637129836321:ℝ)/1000000000000) + t * ((42638329277237611:ℝ)/25000000000)) = (((-584262821643:ℝ)/131072) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((-2754653722604155893:ℝ)/134217728) + ((163788344333921:ℝ)/4194304)*((103790491727:ℝ)/1000000000000) - ((-439053637129836321:ℝ)/1000000000000)) + t*(((-99752189061:ℝ)/16384) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((-1628925901016014563:ℝ)/33554432) - 3*((-2754653722604155893:ℝ)/134217728)) + ((39259611551865:ℝ)/524288)*((103790491727:ℝ)/1000000000000) - ((42638329277237611:ℝ)/25000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece23_e02 {q : ℝ} (h0 : (5:ℝ) ≤ q) (h1 : q ≤ ((21:ℝ)/4)) :
    |pieceW q pieceX_23 0 2 - (((429963797225000197:ℝ)/10000000000000) + (q - ((41:ℝ)/8)) * ((42650034308382509:ℝ)/250000000000))| ≤ ((269315814664545349:ℝ)/10000000000000) := by
  set t := q - ((41:ℝ)/8) with htd
  have hq : q = ((41:ℝ)/8) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/8) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece23_L3 piece23_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((41:ℝ)/8))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_02 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_02; ring
  have h12 : centralNum12_02 q = ∑ e ∈ Finset.range 13, ([((-266021723692372453749:ℝ)/8589934592), ((-214495517962195227621:ℝ)/2147483648), ((-37651773312971222463:ℝ)/268435456), ((-3873821237708279355:ℝ)/33554432), ((-262790798932489635:ℝ)/4194304), ((-6229687208828553:ℝ)/262144), ((-212520961477251:ℝ)/32768), ((-5270636801403:ℝ)/4096), ((-11812212855:ℝ)/64), ((-2392427385:ℝ)/128), ((-20318283:ℝ)/16), ((-104031:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_02; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-266021723692372453749:ℝ)/8589934592), ((-214495517962195227621:ℝ)/2147483648), ((-37651773312971222463:ℝ)/268435456), ((-3873821237708279355:ℝ)/33554432), ((-262790798932489635:ℝ)/4194304), ((-6229687208828553:ℝ)/262144), ((-212520961477251:ℝ)/32768), ((-5270636801403:ℝ)/4096), ((-11812212855:ℝ)/64), ((-2392427385:ℝ)/128), ((-20318283:ℝ)/16), ((-104031:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((-266021723692372453749:ℝ)/8589934592), ((-214495517962195227621:ℝ)/2147483648), ((-37651773312971222463:ℝ)/268435456), ((-3873821237708279355:ℝ)/33554432), ((-262790798932489635:ℝ)/4194304), ((-6229687208828553:ℝ)/262144), ((-212520961477251:ℝ)/32768), ((-5270636801403:ℝ)/4096), ((-11812212855:ℝ)/64), ((-2392427385:ℝ)/128), ((-20318283:ℝ)/16), ((-104031:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((-266021723692372453749:ℝ)/8589934592), ((-214495517962195227621:ℝ)/2147483648), ((-37651773312971222463:ℝ)/268435456), ((-3873821237708279355:ℝ)/33554432), ((-262790798932489635:ℝ)/4194304), ((-6229687208828553:ℝ)/262144), ((-212520961477251:ℝ)/32768), ((-5270636801403:ℝ)/4096), ((-11812212855:ℝ)/64), ((-2392427385:ℝ)/128), ((-20318283:ℝ)/16), ((-104031:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0 * t^e) - ((-266021723692372453749:ℝ)/8589934592) - ((-214495517962195227621:ℝ)/2147483648)*t| ≤ ((41801280498634461489:ℝ)/17179869184) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((-266021723692372453749:ℝ)/8589934592), ((-214495517962195227621:ℝ)/2147483648), ((-37651773312971222463:ℝ)/268435456), ((-3873821237708279355:ℝ)/33554432), ((-262790798932489635:ℝ)/4194304), ((-6229687208828553:ℝ)/262144), ((-212520961477251:ℝ)/32768), ((-5270636801403:ℝ)/4096), ((-11812212855:ℝ)/64), ((-2392427385:ℝ)/128), ((-20318283:ℝ)/16), ((-104031:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((384931760666784471:ℝ)/8388608) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((163788344333921:ℝ)/4194304) - ((39259611551865:ℝ)/524288)*t| ≤ ((2218722018707:ℝ)/2097152) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/4) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82080:ℝ), (-967680:ℝ), (3257600:ℝ), (-4474880:ℝ), (2908160:ℝ), (-786432:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_02 q| ≤ ((685356160616770923:ℝ)/1024) := by
    rw [centralNum13_02_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/4) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (87660:ℝ), (-702180:ℝ), ((7421435:ℝ)/4), ((-10854125:ℝ)/4), ((2828125:ℝ)/2), (-187500:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_02 q| ≤ ((2092966312159712899665:ℝ)/8388608) := by
    rw [centralNum23_02_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((475639221747518193893788855829:ℝ)/100000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece23_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece23_E11 h0) m23'
  have c5 := scaled_affine (X := ((1217466811:ℝ)/500000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((-266021723692372453749:ℝ)/8589934592) + ((163788344333921:ℝ)/4194304)*((1217466811:ℝ)/500000000000) - ((429963797225000197:ℝ)/10000000000000)) (β := (0:ℝ) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((-214495517962195227621:ℝ)/2147483648) - 3*((-266021723692372453749:ℝ)/8589934592)) + ((39259611551865:ℝ)/524288)*((1217466811:ℝ)/500000000000) - ((42650034308382509:ℝ)/250000000000)) ht
  have hW : pieceW q pieceX_23 0 2 = centralNum11_02 q + 8*(Real.exp (-(3*((41:ℝ)/8)))*Real.exp (-3*t))*centralNum12_02 q + 18*Real.exp (-8*q)*centralNum13_02 q + 72*Real.exp (-11*q)*centralNum23_02 q + 8*q^7*(2*q-3)^2*((1217466811:ℝ)/500000000000) + (0:ℝ) := by
    rw [pieceW_02, pieceX_23, sym4_02, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((4699227774338718053627200109094590723968122840494268801374060651:ℝ)/59305536308766500942787096593698682034939264707622480477049323520000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((-266021723692372453749:ℝ)/8589934592) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((-214495517962195227621:ℝ)/2147483648) - 3*((-266021723692372453749:ℝ)/8589934592))*t) + (((163788344333921:ℝ)/4194304) + ((39259611551865:ℝ)/524288)*t)*((1217466811:ℝ)/500000000000) - (((429963797225000197:ℝ)/10000000000000) + t * ((42650034308382509:ℝ)/250000000000)) = ((0:ℝ) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((-266021723692372453749:ℝ)/8589934592) + ((163788344333921:ℝ)/4194304)*((1217466811:ℝ)/500000000000) - ((429963797225000197:ℝ)/10000000000000)) + t*((0:ℝ) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((-214495517962195227621:ℝ)/2147483648) - 3*((-266021723692372453749:ℝ)/8589934592)) + ((39259611551865:ℝ)/524288)*((1217466811:ℝ)/500000000000) - ((42650034308382509:ℝ)/250000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece23_e03 {q : ℝ} (h0 : (5:ℝ) ≤ q) (h1 : q ≤ ((21:ℝ)/4)) :
    |pieceW q pieceX_23 0 3 - (((10070885085285511:ℝ)/125000000000) + (q - ((41:ℝ)/8)) * ((-659583856830948193:ℝ)/10000000000000))| ≤ ((168738692681523943:ℝ)/10000000000000) := by
  set t := q - ((41:ℝ)/8) with htd
  have hq : q = ((41:ℝ)/8) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/8) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece23_L3 piece23_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((41:ℝ)/8))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_03 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_03; ring
  have h12 : centralNum12_03 q = ∑ e ∈ Finset.range 14, ([((37518393473664295241835:ℝ)/962072674304), ((14600299005392949059193:ℝ)/240518168576), ((9675489207332911617:ℝ)/1073741824), ((-98506713190552730181:ℝ)/1879048192), ((-14691818491616593935:ℝ)/234881024), ((-321718614089227515:ℝ)/8388608), ((-14013533076163443:ℝ)/917504), ((-974652612741207:ℝ)/229376), ((-48612133299987:ℝ)/57344), ((-248731905735:ℝ)/2048), ((-5485629825:ℝ)/448), ((-92623581:ℝ)/112), ((-67311:ℝ)/2), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_03; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((37518393473664295241835:ℝ)/962072674304), ((14600299005392949059193:ℝ)/240518168576), ((9675489207332911617:ℝ)/1073741824), ((-98506713190552730181:ℝ)/1879048192), ((-14691818491616593935:ℝ)/234881024), ((-321718614089227515:ℝ)/8388608), ((-14013533076163443:ℝ)/917504), ((-974652612741207:ℝ)/229376), ((-48612133299987:ℝ)/57344), ((-248731905735:ℝ)/2048), ((-5485629825:ℝ)/448), ((-92623581:ℝ)/112), ((-67311:ℝ)/2), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((37518393473664295241835:ℝ)/962072674304), ((14600299005392949059193:ℝ)/240518168576), ((9675489207332911617:ℝ)/1073741824), ((-98506713190552730181:ℝ)/1879048192), ((-14691818491616593935:ℝ)/234881024), ((-321718614089227515:ℝ)/8388608), ((-14013533076163443:ℝ)/917504), ((-974652612741207:ℝ)/229376), ((-48612133299987:ℝ)/57344), ((-248731905735:ℝ)/2048), ((-5485629825:ℝ)/448), ((-92623581:ℝ)/112), ((-67311:ℝ)/2), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((37518393473664295241835:ℝ)/962072674304), ((14600299005392949059193:ℝ)/240518168576), ((9675489207332911617:ℝ)/1073741824), ((-98506713190552730181:ℝ)/1879048192), ((-14691818491616593935:ℝ)/234881024), ((-321718614089227515:ℝ)/8388608), ((-14013533076163443:ℝ)/917504), ((-974652612741207:ℝ)/229376), ((-48612133299987:ℝ)/57344), ((-248731905735:ℝ)/2048), ((-5485629825:ℝ)/448), ((-92623581:ℝ)/112), ((-67311:ℝ)/2), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((37518393473664295241835:ℝ)/962072674304) - ((14600299005392949059193:ℝ)/240518168576)*t| ≤ ((71382699618694812801:ℝ)/274877906944) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((37518393473664295241835:ℝ)/962072674304), ((14600299005392949059193:ℝ)/240518168576), ((9675489207332911617:ℝ)/1073741824), ((-98506713190552730181:ℝ)/1879048192), ((-14691818491616593935:ℝ)/234881024), ((-321718614089227515:ℝ)/8388608), ((-14013533076163443:ℝ)/917504), ((-974652612741207:ℝ)/229376), ((-48612133299987:ℝ)/57344), ((-248731905735:ℝ)/2048), ((-5485629825:ℝ)/448), ((-92623581:ℝ)/112), ((-67311:ℝ)/2), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((6438340346432314516605:ℝ)/137438953472) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((163788344333921:ℝ)/4194304) - ((39259611551865:ℝ)/524288)*t| ≤ ((2218722018707:ℝ)/2097152) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/4) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-812160:ℝ), (8985600:ℝ), (-32225280:ℝ), (52019200:ℝ), ((-305233920:ℝ)/7), ((135528448:ℝ)/7), ((-25165824:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_03 q| ≤ ((2731009702090579371:ℝ)/128) := by
    rw [centralNum13_03_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/4) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-833220:ℝ), (6469740:ℝ), ((-68603955:ℝ)/4), ((104396875:ℝ)/4), ((-1001334375:ℝ)/56), ((125828125:ℝ)/28), ((-2343750:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_03 q| ≤ ((315763145924253284478375:ℝ)/67108864) := by
    rw [centralNum23_03_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((475639221747518193893788855829:ℝ)/100000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece23_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece23_E11 h0) m23'
  have c5 := scaled_affine (X := ((383491440859:ℝ)/1000000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((37518393473664295241835:ℝ)/962072674304) + ((163788344333921:ℝ)/4194304)*((383491440859:ℝ)/1000000000000000) - ((10070885085285511:ℝ)/125000000000)) (β := (0:ℝ) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((14600299005392949059193:ℝ)/240518168576) - 3*((37518393473664295241835:ℝ)/962072674304)) + ((39259611551865:ℝ)/524288)*((383491440859:ℝ)/1000000000000000) - ((-659583856830948193:ℝ)/10000000000000)) ht
  have hW : pieceW q pieceX_23 0 3 = centralNum11_03 q + 8*(Real.exp (-(3*((41:ℝ)/8)))*Real.exp (-3*t))*centralNum12_03 q + 18*Real.exp (-8*q)*centralNum13_03 q + 72*Real.exp (-11*q)*centralNum23_03 q + 8*q^7*(2*q-3)^2*((383491440859:ℝ)/1000000000000000) + (0:ℝ) := by
    rw [pieceW_03, pieceX_23, sym4_03, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((2557668288297291925731605533878214706169149212394092175126096478761:ℝ)/166055501664546202639803870462356309697829941181342945335738105856000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((37518393473664295241835:ℝ)/962072674304) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((14600299005392949059193:ℝ)/240518168576) - 3*((37518393473664295241835:ℝ)/962072674304))*t) + (((163788344333921:ℝ)/4194304) + ((39259611551865:ℝ)/524288)*t)*((383491440859:ℝ)/1000000000000000) - (((10070885085285511:ℝ)/125000000000) + t * ((-659583856830948193:ℝ)/10000000000000)) = ((0:ℝ) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((37518393473664295241835:ℝ)/962072674304) + ((163788344333921:ℝ)/4194304)*((383491440859:ℝ)/1000000000000000) - ((10070885085285511:ℝ)/125000000000)) + t*((0:ℝ) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((14600299005392949059193:ℝ)/240518168576) - 3*((37518393473664295241835:ℝ)/962072674304)) + ((39259611551865:ℝ)/524288)*((383491440859:ℝ)/1000000000000000) - ((-659583856830948193:ℝ)/10000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece23_e11 {q : ℝ} (h0 : (5:ℝ) ≤ q) (h1 : q ≤ ((21:ℝ)/4)) :
    |pieceW q pieceX_23 1 1 - (((486543710518857781:ℝ)/100000000000) + (q - ((41:ℝ)/8)) * ((58253754636779589:ℝ)/10000000000))| ≤ ((143796435305291509:ℝ)/100000000000) := by
  set t := q - ((41:ℝ)/8) with htd
  have hq : q = ((41:ℝ)/8) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/8) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece23_L3 piece23_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((41:ℝ)/8))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_11 q = ∑ e ∈ Finset.range 10, ([((190436429125931:ℝ)/6291456), ((14291441674355:ℝ)/262144), ((361417657661:ℝ)/8192), ((21546565467:ℝ)/1024), ((1667066191:ℝ)/256), ((43349341:ℝ)/32), ((378385:ℝ)/2), (17084:ℝ), (904:ℝ), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_11; ring
  have h12 : centralNum12_11 q = ∑ e ∈ Finset.range 13, ([((-118767515143930497013:ℝ)/6442450944), ((-41882668815012723191:ℝ)/536870912), ((-8500602891835597397:ℝ)/67108864), ((-959781768366734121:ℝ)/8388608), ((-69548431041006305:ℝ)/1048576), ((-1733324153999107:ℝ)/65536), ((-61532866325441:ℝ)/8192), ((-1576923937129:ℝ)/1024), ((-3633478301:ℝ)/16), ((-2261236345:ℝ)/96), ((-6537177:ℝ)/4), (-68202:ℝ), (-1296:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_11; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((190436429125931:ℝ)/6291456), ((14291441674355:ℝ)/262144), ((361417657661:ℝ)/8192), ((21546565467:ℝ)/1024), ((1667066191:ℝ)/256), ((43349341:ℝ)/32), ((378385:ℝ)/2), (17084:ℝ), (904:ℝ), ((64:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-118767515143930497013:ℝ)/6442450944), ((-41882668815012723191:ℝ)/536870912), ((-8500602891835597397:ℝ)/67108864), ((-959781768366734121:ℝ)/8388608), ((-69548431041006305:ℝ)/1048576), ((-1733324153999107:ℝ)/65536), ((-61532866325441:ℝ)/8192), ((-1576923937129:ℝ)/1024), ((-3633478301:ℝ)/16), ((-2261236345:ℝ)/96), ((-6537177:ℝ)/4), (-68202:ℝ), (-1296:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((-118767515143930497013:ℝ)/6442450944), ((-41882668815012723191:ℝ)/536870912), ((-8500602891835597397:ℝ)/67108864), ((-959781768366734121:ℝ)/8388608), ((-69548431041006305:ℝ)/1048576), ((-1733324153999107:ℝ)/65536), ((-61532866325441:ℝ)/8192), ((-1576923937129:ℝ)/1024), ((-3633478301:ℝ)/16), ((-2261236345:ℝ)/96), ((-6537177:ℝ)/4), (-68202:ℝ), (-1296:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((190436429125931:ℝ)/6291456), ((14291441674355:ℝ)/262144), ((361417657661:ℝ)/8192), ((21546565467:ℝ)/1024), ((1667066191:ℝ)/256), ((43349341:ℝ)/32), ((378385:ℝ)/2), (17084:ℝ), (904:ℝ), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((190436429125931:ℝ)/6291456) + ((14291441674355:ℝ)/262144)*t)| ≤ ((1151459440735:ℝ)/1572864) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((-118767515143930497013:ℝ)/6442450944), ((-41882668815012723191:ℝ)/536870912), ((-8500602891835597397:ℝ)/67108864), ((-959781768366734121:ℝ)/8388608), ((-69548431041006305:ℝ)/1048576), ((-1733324153999107:ℝ)/65536), ((-61532866325441:ℝ)/8192), ((-1576923937129:ℝ)/1024), ((-3633478301:ℝ)/16), ((-2261236345:ℝ)/96), ((-6537177:ℝ)/4), (-68202:ℝ), (-1296:ℝ)] : List ℝ).getD e 0 * t^e) - ((-118767515143930497013:ℝ)/6442450944) - ((-41882668815012723191:ℝ)/536870912)*t| ≤ ((28600578054083492401:ℝ)/12884901888) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((-118767515143930497013:ℝ)/6442450944), ((-41882668815012723191:ℝ)/536870912), ((-8500602891835597397:ℝ)/67108864), ((-959781768366734121:ℝ)/8388608), ((-69548431041006305:ℝ)/1048576), ((-1733324153999107:ℝ)/65536), ((-61532866325441:ℝ)/8192), ((-1576923937129:ℝ)/1024), ((-3633478301:ℝ)/16), ((-2261236345:ℝ)/96), ((-6537177:ℝ)/4), (-68202:ℝ), (-1296:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((63766864385902125:ℝ)/2097152) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((163788344333921:ℝ)/4194304) - ((39259611551865:ℝ)/524288)*t| ≤ ((2218722018707:ℝ)/2097152) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/4) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-3444:ℝ), (162624:ℝ), (-1531216:ℝ), (4800960:ℝ), (-6350848:ℝ), ((12025856:ℝ)/3), (-1048576:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_11 q| ≤ ((932845527317590677:ℝ)/1024) := by
    rw [centralNum13_11_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/4) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-4074:ℝ), (159906:ℝ), (-1104799:ℝ), (2801499:ℝ), (-3931375:ℝ), ((5896250:ℝ)/3), (-250000:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_11 q| ≤ ((724415577255445710411:ℝ)/2097152) := by
    rw [centralNum23_11_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((475639221747518193893788855829:ℝ)/100000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece23_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece23_E11 h0) m23'
  have c5 := scaled_affine (X := ((-324871849137:ℝ)/500000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1))| ≤ ((13829341623616298828125000:ℝ)/15264796318975966160472558246657) := by
    rw [abs_neg, tailWeight_1, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((21:ℝ)/4)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((21:ℝ)/4)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece23_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((4814744136400:ℝ)/531441)) ≤ ((21:ℝ)/4)^6*(8000*(2*((21:ℝ)/4)-3)^2*(1/((188454275542913162474969854897:ℝ)/2000000))*((4814744136400:ℝ)/531441)) := by
          gcongr
      _ ≤ ((13829341623616298828125000:ℝ)/15264796318975966160472558246657) := by norm_num
  have c7 := affine_round (α := ((190436429125931:ℝ)/6291456) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((-118767515143930497013:ℝ)/6442450944) + ((163788344333921:ℝ)/4194304)*((-324871849137:ℝ)/500000000000) - ((486543710518857781:ℝ)/100000000000)) (β := ((14291441674355:ℝ)/262144) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((-41882668815012723191:ℝ)/536870912) - 3*((-118767515143930497013:ℝ)/6442450944)) + ((39259611551865:ℝ)/524288)*((-324871849137:ℝ)/500000000000) - ((58253754636779589:ℝ)/10000000000)) ht
  have hW : pieceW q pieceX_23 1 1 = centralNum11_11 q + 8*(Real.exp (-(3*((41:ℝ)/8)))*Real.exp (-3*t))*centralNum12_11 q + 18*Real.exp (-8*q)*centralNum13_11 q + 72*Real.exp (-11*q)*centralNum23_11 q + 8*q^7*(2*q-3)^2*((-324871849137:ℝ)/500000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1)) := by
    rw [pieceW_11, pieceX_23, sym4_11, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((13423497342335402154515707660351971439251063767618581818152101501:ℝ)/2737178598866146197359404458170708401612581448044114483556122624000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((190436429125931:ℝ)/6291456) + ((14291441674355:ℝ)/262144)*t) + (8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((-118767515143930497013:ℝ)/6442450944) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((-41882668815012723191:ℝ)/536870912) - 3*((-118767515143930497013:ℝ)/6442450944))*t) + (((163788344333921:ℝ)/4194304) + ((39259611551865:ℝ)/524288)*t)*((-324871849137:ℝ)/500000000000) - (((486543710518857781:ℝ)/100000000000) + t * ((58253754636779589:ℝ)/10000000000)) = (((190436429125931:ℝ)/6291456) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((-118767515143930497013:ℝ)/6442450944) + ((163788344333921:ℝ)/4194304)*((-324871849137:ℝ)/500000000000) - ((486543710518857781:ℝ)/100000000000)) + t*(((14291441674355:ℝ)/262144) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((-41882668815012723191:ℝ)/536870912) - 3*((-118767515143930497013:ℝ)/6442450944)) + ((39259611551865:ℝ)/524288)*((-324871849137:ℝ)/500000000000) - ((58253754636779589:ℝ)/10000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece23_e12 {q : ℝ} (h0 : (5:ℝ) ≤ q) (h1 : q ≤ ((21:ℝ)/4)) :
    |pieceW q pieceX_23 1 2 - (((-115536401476607073:ℝ)/1000000000000) + (q - ((41:ℝ)/8)) * ((102018025382534407:ℝ)/100000000000))| ≤ ((136392280253143861:ℝ)/1000000000000) := by
  set t := q - ((41:ℝ)/8) with htd
  have hq : q = ((41:ℝ)/8) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/8) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece23_L3 piece23_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((41:ℝ)/8))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_12 q = ∑ e ∈ Finset.range 9, ([((-13086537183955:ℝ)/6291456), ((-104849861905:ℝ)/49152), ((-14566797955:ℝ)/24576), ((56170615:ℝ)/384), ((105692875:ℝ)/768), ((467195:ℝ)/12), ((33905:ℝ)/6), ((1280:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_12; ring
  have h12 : centralNum12_12 q = ∑ e ∈ Finset.range 14, ([((57435677140920846675179:ℝ)/412316860416), ((32997054509762894296825:ℝ)/103079215104), ((945722456301425953255:ℝ)/3221225472), ((93226576931968407419:ℝ)/805306368), ((-1073392024449590095:ℝ)/100663296), ((-911067103305086429:ℝ)/25165824), ((-8107711279385875:ℝ)/393216), ((-673244218284695:ℝ)/98304), ((-37521806631187:ℝ)/24576), ((-484532616955:ℝ)/2048), ((-1620490251:ℝ)/64), ((-28698975:ℝ)/16), ((-151875:ℝ)/2), (-1458:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_12; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-13086537183955:ℝ)/6291456), ((-104849861905:ℝ)/49152), ((-14566797955:ℝ)/24576), ((56170615:ℝ)/384), ((105692875:ℝ)/768), ((467195:ℝ)/12), ((33905:ℝ)/6), ((1280:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((57435677140920846675179:ℝ)/412316860416), ((32997054509762894296825:ℝ)/103079215104), ((945722456301425953255:ℝ)/3221225472), ((93226576931968407419:ℝ)/805306368), ((-1073392024449590095:ℝ)/100663296), ((-911067103305086429:ℝ)/25165824), ((-8107711279385875:ℝ)/393216), ((-673244218284695:ℝ)/98304), ((-37521806631187:ℝ)/24576), ((-484532616955:ℝ)/2048), ((-1620490251:ℝ)/64), ((-28698975:ℝ)/16), ((-151875:ℝ)/2), (-1458:ℝ)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((57435677140920846675179:ℝ)/412316860416), ((32997054509762894296825:ℝ)/103079215104), ((945722456301425953255:ℝ)/3221225472), ((93226576931968407419:ℝ)/805306368), ((-1073392024449590095:ℝ)/100663296), ((-911067103305086429:ℝ)/25165824), ((-8107711279385875:ℝ)/393216), ((-673244218284695:ℝ)/98304), ((-37521806631187:ℝ)/24576), ((-484532616955:ℝ)/2048), ((-1620490251:ℝ)/64), ((-28698975:ℝ)/16), ((-151875:ℝ)/2), (-1458:ℝ)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((-13086537183955:ℝ)/6291456), ((-104849861905:ℝ)/49152), ((-14566797955:ℝ)/24576), ((56170615:ℝ)/384), ((105692875:ℝ)/768), ((467195:ℝ)/12), ((33905:ℝ)/6), ((1280:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((-13086537183955:ℝ)/6291456) + ((-104849861905:ℝ)/49152)*t)| ≤ ((60283649275:ℝ)/6291456) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((57435677140920846675179:ℝ)/412316860416), ((32997054509762894296825:ℝ)/103079215104), ((945722456301425953255:ℝ)/3221225472), ((93226576931968407419:ℝ)/805306368), ((-1073392024449590095:ℝ)/100663296), ((-911067103305086429:ℝ)/25165824), ((-8107711279385875:ℝ)/393216), ((-673244218284695:ℝ)/98304), ((-37521806631187:ℝ)/24576), ((-484532616955:ℝ)/2048), ((-1620490251:ℝ)/64), ((-28698975:ℝ)/16), ((-151875:ℝ)/2), (-1458:ℝ)] : List ℝ).getD e 0 * t^e) - ((57435677140920846675179:ℝ)/412316860416) - ((32997054509762894296825:ℝ)/103079215104)*t| ≤ ((1324156153801927741265:ℝ)/274877906944) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((57435677140920846675179:ℝ)/412316860416), ((32997054509762894296825:ℝ)/103079215104), ((945722456301425953255:ℝ)/3221225472), ((93226576931968407419:ℝ)/805306368), ((-1073392024449590095:ℝ)/100663296), ((-911067103305086429:ℝ)/25165824), ((-8107711279385875:ℝ)/393216), ((-673244218284695:ℝ)/98304), ((-37521806631187:ℝ)/24576), ((-484532616955:ℝ)/2048), ((-1620490251:ℝ)/64), ((-28698975:ℝ)/16), ((-151875:ℝ)/2), (-1458:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((75920438626505185435489:ℝ)/412316860416) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((163788344333921:ℝ)/4194304) - ((39259611551865:ℝ)/524288)*t| ≤ ((2218722018707:ℝ)/2097152) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/4) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (122790:ℝ), (-3586680:ℝ), (28529720:ℝ), (-90761600:ℝ), (137804800:ℝ), ((-332136448:ℝ)/3), ((141819904:ℝ)/3), (-8388608:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_12 q| ≤ ((424062479710485764883:ℝ)/8192) := by
    rw [centralNum13_12_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/4) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (132555:ℝ), (-3252375:ℝ), ((39743695:ℝ)/2), ((-197111615:ℝ)/4), ((281947375:ℝ)/4), ((-1100234375:ℝ)/24), ((131828125:ℝ)/12), (-781250:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_12 q| ≤ ((786900789697443444384795:ℝ)/67108864) := by
    rw [centralNum23_12_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((475639221747518193893788855829:ℝ)/100000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece23_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece23_E11 h0) m23'
  have c5 := scaled_affine (X := ((443075421299:ℝ)/10000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-13086537183955:ℝ)/6291456) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((57435677140920846675179:ℝ)/412316860416) + ((163788344333921:ℝ)/4194304)*((443075421299:ℝ)/10000000000000) - ((-115536401476607073:ℝ)/1000000000000)) (β := ((-104849861905:ℝ)/49152) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((32997054509762894296825:ℝ)/103079215104) - 3*((57435677140920846675179:ℝ)/412316860416)) + ((39259611551865:ℝ)/524288)*((443075421299:ℝ)/10000000000000) - ((102018025382534407:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_23 1 2 = centralNum11_12 q + 8*(Real.exp (-(3*((41:ℝ)/8)))*Real.exp (-3*t))*centralNum12_12 q + 18*Real.exp (-8*q)*centralNum13_12 q + 72*Real.exp (-11*q)*centralNum23_12 q + 8*q^7*(2*q-3)^2*((443075421299:ℝ)/10000000000000) + (0:ℝ) := by
    rw [pieceW_12, pieceX_23, sym4_12, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((165174605503362967124115601742310952154762303247513231717505380971:ℝ)/711666435705198011313445159124384184419271176491469765724591882240000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-13086537183955:ℝ)/6291456) + ((-104849861905:ℝ)/49152)*t) + (8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((57435677140920846675179:ℝ)/412316860416) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((32997054509762894296825:ℝ)/103079215104) - 3*((57435677140920846675179:ℝ)/412316860416))*t) + (((163788344333921:ℝ)/4194304) + ((39259611551865:ℝ)/524288)*t)*((443075421299:ℝ)/10000000000000) - (((-115536401476607073:ℝ)/1000000000000) + t * ((102018025382534407:ℝ)/100000000000)) = (((-13086537183955:ℝ)/6291456) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((57435677140920846675179:ℝ)/412316860416) + ((163788344333921:ℝ)/4194304)*((443075421299:ℝ)/10000000000000) - ((-115536401476607073:ℝ)/1000000000000)) + t*(((-104849861905:ℝ)/49152) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((32997054509762894296825:ℝ)/103079215104) - 3*((57435677140920846675179:ℝ)/412316860416)) + ((39259611551865:ℝ)/524288)*((443075421299:ℝ)/10000000000000) - ((102018025382534407:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece23_e13 {q : ℝ} (h0 : (5:ℝ) ≤ q) (h1 : q ≤ ((21:ℝ)/4)) :
    |pieceW q pieceX_23 1 3 - (((-101513939131995057:ℝ)/500000000000) + (q - ((41:ℝ)/8)) * ((924050204773504973:ℝ)/1000000000000))| ≤ ((463467965146501679:ℝ)/5000000000000) := by
  set t := q - ((41:ℝ)/8) with htd
  have hq : q = ((41:ℝ)/8) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/8) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece23_L3 piece23_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((41:ℝ)/8))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_13 q = ∑ e ∈ Finset.range 7, ([((-71251563615:ℝ)/65536), ((-5213529045:ℝ)/4096), ((-635796225:ℝ)/1024), ((-5169075:ℝ)/32), ((-378225:ℝ)/16), (-1845:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_13; ring
  have h12 : centralNum12_13 q = ∑ e ∈ Finset.range 15, ([((-169812177308253229009479:ℝ)/15393162788864), ((938416324392587845228413:ℝ)/3848290697216), ((304969097612956724809887:ℝ)/481036337152), ((21077209217958418764075:ℝ)/30064771072), ((414904605276931912563:ℝ)/939524096), ((160087810189664652159:ℝ)/939524096), ((4419103520368099041:ℝ)/117440512), ((7483559656250361:ℝ)/3670016), ((-1442660537389755:ℝ)/917504), ((-137243607395157:ℝ)/229376), ((-3299722931583:ℝ)/28672), ((-24831693261:ℝ)/1792), ((-118369917:ℝ)/112), ((-2635335:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_13; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-71251563615:ℝ)/65536), ((-5213529045:ℝ)/4096), ((-635796225:ℝ)/1024), ((-5169075:ℝ)/32), ((-378225:ℝ)/16), (-1845:ℝ), (-60:ℝ)] : List ℝ).getD e 0) 5 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-169812177308253229009479:ℝ)/15393162788864), ((938416324392587845228413:ℝ)/3848290697216), ((304969097612956724809887:ℝ)/481036337152), ((21077209217958418764075:ℝ)/30064771072), ((414904605276931912563:ℝ)/939524096), ((160087810189664652159:ℝ)/939524096), ((4419103520368099041:ℝ)/117440512), ((7483559656250361:ℝ)/3670016), ((-1442660537389755:ℝ)/917504), ((-137243607395157:ℝ)/229376), ((-3299722931583:ℝ)/28672), ((-24831693261:ℝ)/1792), ((-118369917:ℝ)/112), ((-2635335:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-169812177308253229009479:ℝ)/15393162788864), ((938416324392587845228413:ℝ)/3848290697216), ((304969097612956724809887:ℝ)/481036337152), ((21077209217958418764075:ℝ)/30064771072), ((414904605276931912563:ℝ)/939524096), ((160087810189664652159:ℝ)/939524096), ((4419103520368099041:ℝ)/117440512), ((7483559656250361:ℝ)/3670016), ((-1442660537389755:ℝ)/917504), ((-137243607395157:ℝ)/229376), ((-3299722931583:ℝ)/28672), ((-24831693261:ℝ)/1792), ((-118369917:ℝ)/112), ((-2635335:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 7, ([((-71251563615:ℝ)/65536), ((-5213529045:ℝ)/4096), ((-635796225:ℝ)/1024), ((-5169075:ℝ)/32), ((-378225:ℝ)/16), (-1845:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e) - (((-71251563615:ℝ)/65536) + ((-5213529045:ℝ)/4096)*t)| ≤ ((656854455:ℝ)/65536) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-169812177308253229009479:ℝ)/15393162788864), ((938416324392587845228413:ℝ)/3848290697216), ((304969097612956724809887:ℝ)/481036337152), ((21077209217958418764075:ℝ)/30064771072), ((414904605276931912563:ℝ)/939524096), ((160087810189664652159:ℝ)/939524096), ((4419103520368099041:ℝ)/117440512), ((7483559656250361:ℝ)/3670016), ((-1442660537389755:ℝ)/917504), ((-137243607395157:ℝ)/229376), ((-3299722931583:ℝ)/28672), ((-24831693261:ℝ)/1792), ((-118369917:ℝ)/112), ((-2635335:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((-169812177308253229009479:ℝ)/15393162788864) - ((938416324392587845228413:ℝ)/3848290697216)*t| ≤ ((350607292764952220005521:ℝ)/30786325577728) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-169812177308253229009479:ℝ)/15393162788864), ((938416324392587845228413:ℝ)/3848290697216), ((304969097612956724809887:ℝ)/481036337152), ((21077209217958418764075:ℝ)/30064771072), ((414904605276931912563:ℝ)/939524096), ((160087810189664652159:ℝ)/939524096), ((4419103520368099041:ℝ)/117440512), ((7483559656250361:ℝ)/3670016), ((-1442660537389755:ℝ)/917504), ((-137243607395157:ℝ)/229376), ((-3299722931583:ℝ)/28672), ((-24831693261:ℝ)/1792), ((-118369917:ℝ)/112), ((-2635335:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((407161992943511630813223:ℝ)/7696581394432) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((163788344333921:ℝ)/4194304) - ((39259611551865:ℝ)/524288)*t| ≤ ((2218722018707:ℝ)/2097152) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/4) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2325540:ℝ), (52589280:ℝ), (-375655200:ℝ), (1192958720:ℝ), (-1965096960:ℝ), ((12857851904:ℝ)/7), ((-21171273728:ℝ)/21), ((914358272:ℝ)/3), ((-268435456:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_13 q| ≤ ((3677167571311773702765:ℝ)/2048) := by
    rw [centralNum13_13_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/4) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2399070:ℝ), (45666930:ℝ), (-251781675:ℝ), ((2452738385:ℝ)/4), ((-14104310625:ℝ)/16), ((74345740625:ℝ)/112), ((-74899765625:ℝ)/336), ((5161328125:ℝ)/168), ((-9765625:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_13 q| ≤ ((137856692241123819001408125:ℝ)/536870912) := by
    rw [centralNum23_13_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((475639221747518193893788855829:ℝ)/100000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece23_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece23_E11 h0) m23'
  have c5 := scaled_affine (X := ((231174164601:ℝ)/10000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-71251563615:ℝ)/65536) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((-169812177308253229009479:ℝ)/15393162788864) + ((163788344333921:ℝ)/4194304)*((231174164601:ℝ)/10000000000000) - ((-101513939131995057:ℝ)/500000000000)) (β := ((-5213529045:ℝ)/4096) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((938416324392587845228413:ℝ)/3848290697216) - 3*((-169812177308253229009479:ℝ)/15393162788864)) + ((39259611551865:ℝ)/524288)*((231174164601:ℝ)/10000000000000) - ((924050204773504973:ℝ)/1000000000000)) ht
  have hW : pieceW q pieceX_23 1 3 = centralNum11_13 q + 8*(Real.exp (-(3*((41:ℝ)/8)))*Real.exp (-3*t))*centralNum12_13 q + 18*Real.exp (-8*q)*centralNum13_13 q + 72*Real.exp (-11*q)*centralNum23_13 q + 8*q^7*(2*q-3)^2*((231174164601:ℝ)/10000000000000) + (0:ℝ) := by
    rw [pieceW_13, pieceX_23, sym4_13, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((44551522036623551467471706788190736181628487956862627755437473571:ℝ)/415138754161365506599509676155890774244574852953357363339345264640000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-71251563615:ℝ)/65536) + ((-5213529045:ℝ)/4096)*t) + (8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((-169812177308253229009479:ℝ)/15393162788864) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((938416324392587845228413:ℝ)/3848290697216) - 3*((-169812177308253229009479:ℝ)/15393162788864))*t) + (((163788344333921:ℝ)/4194304) + ((39259611551865:ℝ)/524288)*t)*((231174164601:ℝ)/10000000000000) - (((-101513939131995057:ℝ)/500000000000) + t * ((924050204773504973:ℝ)/1000000000000)) = (((-71251563615:ℝ)/65536) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((-169812177308253229009479:ℝ)/15393162788864) + ((163788344333921:ℝ)/4194304)*((231174164601:ℝ)/10000000000000) - ((-101513939131995057:ℝ)/500000000000)) + t*(((-5213529045:ℝ)/4096) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((938416324392587845228413:ℝ)/3848290697216) - 3*((-169812177308253229009479:ℝ)/15393162788864)) + ((39259611551865:ℝ)/524288)*((231174164601:ℝ)/10000000000000) - ((924050204773504973:ℝ)/1000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece23_e22 {q : ℝ} (h0 : (5:ℝ) ≤ q) (h1 : q ≤ ((21:ℝ)/4)) :
    |pieceW q pieceX_23 2 2 - (((110715986345691769:ℝ)/20000000000) + (q - ((41:ℝ)/8)) * ((13157371059420097:ℝ)/1250000000))| ≤ ((142223237700095477:ℝ)/100000000000) := by
  set t := q - ((41:ℝ)/8) with htd
  have hq : q = ((41:ℝ)/8) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/8) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece23_L3 piece23_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((41:ℝ)/8))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_22 q = ∑ e ∈ Finset.range 10, ([((711183869119505:ℝ)/25165824), ((55263337232975:ℝ)/1048576), ((4316410922585:ℝ)/98304), ((264212898025:ℝ)/12288), ((6995510405:ℝ)/1024), ((561282715:ℝ)/384), ((5054725:ℝ)/24), (19695:ℝ), ((3250:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_22; ring
  have h12 : centralNum12_22 q = ∑ e ∈ Finset.range 15, ([((-3881027255543265316699093:ℝ)/26388279066624), ((237237611926232723259389:ℝ)/2199023255552), ((642497104238902221854749:ℝ)/824633720832), ((54336422668047542885089:ℝ)/51539607552), ((397181972981195116443:ℝ)/536870912), ((504631000498158972733:ℝ)/1610612736), ((16014918831777325859:ℝ)/201326592), ((18493547847272089:ℝ)/2097152), ((-2337236875983217:ℝ)/1572864), ((-330355164356351:ℝ)/393216), ((-2921436564927:ℝ)/16384), ((-23097742893:ℝ)/1024), ((-113640813:ℝ)/64), ((-2588679:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_22; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((711183869119505:ℝ)/25165824), ((55263337232975:ℝ)/1048576), ((4316410922585:ℝ)/98304), ((264212898025:ℝ)/12288), ((6995510405:ℝ)/1024), ((561282715:ℝ)/384), ((5054725:ℝ)/24), (19695:ℝ), ((3250:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-3881027255543265316699093:ℝ)/26388279066624), ((237237611926232723259389:ℝ)/2199023255552), ((642497104238902221854749:ℝ)/824633720832), ((54336422668047542885089:ℝ)/51539607552), ((397181972981195116443:ℝ)/536870912), ((504631000498158972733:ℝ)/1610612736), ((16014918831777325859:ℝ)/201326592), ((18493547847272089:ℝ)/2097152), ((-2337236875983217:ℝ)/1572864), ((-330355164356351:ℝ)/393216), ((-2921436564927:ℝ)/16384), ((-23097742893:ℝ)/1024), ((-113640813:ℝ)/64), ((-2588679:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-3881027255543265316699093:ℝ)/26388279066624), ((237237611926232723259389:ℝ)/2199023255552), ((642497104238902221854749:ℝ)/824633720832), ((54336422668047542885089:ℝ)/51539607552), ((397181972981195116443:ℝ)/536870912), ((504631000498158972733:ℝ)/1610612736), ((16014918831777325859:ℝ)/201326592), ((18493547847272089:ℝ)/2097152), ((-2337236875983217:ℝ)/1572864), ((-330355164356351:ℝ)/393216), ((-2921436564927:ℝ)/16384), ((-23097742893:ℝ)/1024), ((-113640813:ℝ)/64), ((-2588679:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((711183869119505:ℝ)/25165824), ((55263337232975:ℝ)/1048576), ((4316410922585:ℝ)/98304), ((264212898025:ℝ)/12288), ((6995510405:ℝ)/1024), ((561282715:ℝ)/384), ((5054725:ℝ)/24), (19695:ℝ), ((3250:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((711183869119505:ℝ)/25165824) + ((55263337232975:ℝ)/1048576)*t)| ≤ ((9182805683585:ℝ)/12582912) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-3881027255543265316699093:ℝ)/26388279066624), ((237237611926232723259389:ℝ)/2199023255552), ((642497104238902221854749:ℝ)/824633720832), ((54336422668047542885089:ℝ)/51539607552), ((397181972981195116443:ℝ)/536870912), ((504631000498158972733:ℝ)/1610612736), ((16014918831777325859:ℝ)/201326592), ((18493547847272089:ℝ)/2097152), ((-2337236875983217:ℝ)/1572864), ((-330355164356351:ℝ)/393216), ((-2921436564927:ℝ)/16384), ((-23097742893:ℝ)/1024), ((-113640813:ℝ)/64), ((-2588679:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e) - ((-3881027255543265316699093:ℝ)/26388279066624) - ((237237611926232723259389:ℝ)/2199023255552)*t| ≤ ((761223189782183277933619:ℝ)/52776558133248) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-3881027255543265316699093:ℝ)/26388279066624), ((237237611926232723259389:ℝ)/2199023255552), ((642497104238902221854749:ℝ)/824633720832), ((54336422668047542885089:ℝ)/51539607552), ((397181972981195116443:ℝ)/536870912), ((504631000498158972733:ℝ)/1610612736), ((16014918831777325859:ℝ)/201326592), ((18493547847272089:ℝ)/2097152), ((-2337236875983217:ℝ)/1572864), ((-330355164356351:ℝ)/393216), ((-2921436564927:ℝ)/16384), ((-23097742893:ℝ)/1024), ((-113640813:ℝ)/64), ((-2588679:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e)| ≤ ((769582544720617673425831:ℝ)/4398046511104) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((163788344333921:ℝ)/4194304) - ((39259611551865:ℝ)/524288)*t| ≤ ((2218722018707:ℝ)/2097152) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/4) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82125:ℝ), (-6663750:ℝ), (115666200:ℝ), (-750437000:ℝ), (2277262000:ℝ), (-3656824320:ℝ), (3359621120:ℝ), (-1817706496:ℝ), ((1625292800:ℝ)/3), (-67108864:ℝ)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_22 q| ≤ ((52446283719942944075265:ℝ)/16384) := by
    rw [centralNum13_22_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/4) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((178425:ℝ)/2), ((-13176075:ℝ)/2), ((777815145:ℝ)/8), ((-3968389015:ℝ)/8), ((9393350195:ℝ)/8), ((-26366634375:ℝ)/16), ((77851609375:ℝ)/64), ((-25714921875:ℝ)/64), ((5236328125:ℝ)/96), ((-9765625:ℝ)/4)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_22 q| ≤ ((994018366134162726540241275:ℝ)/2147483648) := by
    rw [centralNum23_22_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((475639221747518193893788855829:ℝ)/100000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece23_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece23_E11 h0) m23'
  have c5 := scaled_affine (X := ((-287792983157:ℝ)/500000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2))| ≤ ((7383023188605900646972656250:ℝ)/137383166870783695444253024219913) := by
    rw [abs_neg, tailWeight_2, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((21:ℝ)/4)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((21:ℝ)/4)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece23_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((2570430941234500:ℝ)/4782969)) ≤ ((21:ℝ)/4)^6*(8000*(2*((21:ℝ)/4)-3)^2*(1/((188454275542913162474969854897:ℝ)/2000000))*((2570430941234500:ℝ)/4782969)) := by
          gcongr
      _ ≤ ((7383023188605900646972656250:ℝ)/137383166870783695444253024219913) := by norm_num
  have c7 := affine_round (α := ((711183869119505:ℝ)/25165824) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((-3881027255543265316699093:ℝ)/26388279066624) + ((163788344333921:ℝ)/4194304)*((-287792983157:ℝ)/500000000000) - ((110715986345691769:ℝ)/20000000000)) (β := ((55263337232975:ℝ)/1048576) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((237237611926232723259389:ℝ)/2199023255552) - 3*((-3881027255543265316699093:ℝ)/26388279066624)) + ((39259611551865:ℝ)/524288)*((-287792983157:ℝ)/500000000000) - ((13157371059420097:ℝ)/1250000000)) ht
  have hW : pieceW q pieceX_23 2 2 = centralNum11_22 q + 8*(Real.exp (-(3*((41:ℝ)/8)))*Real.exp (-3*t))*centralNum12_22 q + 18*Real.exp (-8*q)*centralNum13_22 q + 72*Real.exp (-11*q)*centralNum23_22 q + 8*q^7*(2*q-3)^2*((-287792983157:ℝ)/500000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2)) := by
    rw [pieceW_22, pieceX_23, sym4_22, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((13156413021955044203851700641715767698376738990791918045926163599:ℝ)/2737178598866146197359404458170708401612581448044114483556122624000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((711183869119505:ℝ)/25165824) + ((55263337232975:ℝ)/1048576)*t) + (8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((-3881027255543265316699093:ℝ)/26388279066624) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((237237611926232723259389:ℝ)/2199023255552) - 3*((-3881027255543265316699093:ℝ)/26388279066624))*t) + (((163788344333921:ℝ)/4194304) + ((39259611551865:ℝ)/524288)*t)*((-287792983157:ℝ)/500000000000) - (((110715986345691769:ℝ)/20000000000) + t * ((13157371059420097:ℝ)/1250000000)) = (((711183869119505:ℝ)/25165824) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((-3881027255543265316699093:ℝ)/26388279066624) + ((163788344333921:ℝ)/4194304)*((-287792983157:ℝ)/500000000000) - ((110715986345691769:ℝ)/20000000000)) + t*(((55263337232975:ℝ)/1048576) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((237237611926232723259389:ℝ)/2199023255552) - 3*((-3881027255543265316699093:ℝ)/26388279066624)) + ((39259611551865:ℝ)/524288)*((-287792983157:ℝ)/500000000000) - ((13157371059420097:ℝ)/1250000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece23_e23 {q : ℝ} (h0 : (5:ℝ) ≤ q) (h1 : q ≤ ((21:ℝ)/4)) :
    |pieceW q pieceX_23 2 3 - (((26891359308561771:ℝ)/50000000000) + (q - ((41:ℝ)/8)) * ((106174832258629999:ℝ)/100000000000))| ≤ ((176603433976257373:ℝ)/200000000000) := by
  set t := q - ((41:ℝ)/8) with htd
  have hq : q = ((41:ℝ)/8) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/8) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece23_L3 piece23_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((41:ℝ)/8))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_23 q = ∑ e ∈ Finset.range 9, ([((11195763983635:ℝ)/2097152), ((1155072195165:ℝ)/131072), ((109737739225:ℝ)/16384), ((6208042265:ℝ)/2048), ((56441625:ℝ)/64), ((5338855:ℝ)/32), ((79415:ℝ)/4), (1350:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_23; ring
  have h12 : centralNum12_23 q = ∑ e ∈ Finset.range 16, ([((-747714047969508892918515815:ℝ)/985162418487296), ((-706174487111030649979337145:ℝ)/246290604621824), ((-4474715115772123212579179:ℝ)/1099511627776), ((-11190725789066648513922979:ℝ)/3848290697216), ((-243350948556789089325753:ℝ)/240518168576), ((-105631388851971017489:ℝ)/60129542144), ((77906982352536583475:ℝ)/469762048), ((76748204452107114861:ℝ)/939524096), ((1228580566207013111:ℝ)/58720256), ((6142833739849179:ℝ)/2097152), ((45899540602623:ℝ)/458752), ((-10025234614305:ℝ)/229376), ((-134181236151:ℝ)/14336), ((-3297070899:ℝ)/3584), ((-2670327:ℝ)/56), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_23; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((11195763983635:ℝ)/2097152), ((1155072195165:ℝ)/131072), ((109737739225:ℝ)/16384), ((6208042265:ℝ)/2048), ((56441625:ℝ)/64), ((5338855:ℝ)/32), ((79415:ℝ)/4), (1350:ℝ), (40:ℝ)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-747714047969508892918515815:ℝ)/985162418487296), ((-706174487111030649979337145:ℝ)/246290604621824), ((-4474715115772123212579179:ℝ)/1099511627776), ((-11190725789066648513922979:ℝ)/3848290697216), ((-243350948556789089325753:ℝ)/240518168576), ((-105631388851971017489:ℝ)/60129542144), ((77906982352536583475:ℝ)/469762048), ((76748204452107114861:ℝ)/939524096), ((1228580566207013111:ℝ)/58720256), ((6142833739849179:ℝ)/2097152), ((45899540602623:ℝ)/458752), ((-10025234614305:ℝ)/229376), ((-134181236151:ℝ)/14336), ((-3297070899:ℝ)/3584), ((-2670327:ℝ)/56), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 14 ht
  have m12 := abs_poly_le (fun e => ([((-747714047969508892918515815:ℝ)/985162418487296), ((-706174487111030649979337145:ℝ)/246290604621824), ((-4474715115772123212579179:ℝ)/1099511627776), ((-11190725789066648513922979:ℝ)/3848290697216), ((-243350948556789089325753:ℝ)/240518168576), ((-105631388851971017489:ℝ)/60129542144), ((77906982352536583475:ℝ)/469762048), ((76748204452107114861:ℝ)/939524096), ((1228580566207013111:ℝ)/58720256), ((6142833739849179:ℝ)/2097152), ((45899540602623:ℝ)/458752), ((-10025234614305:ℝ)/229376), ((-134181236151:ℝ)/14336), ((-3297070899:ℝ)/3584), ((-2670327:ℝ)/56), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 16 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((11195763983635:ℝ)/2097152), ((1155072195165:ℝ)/131072), ((109737739225:ℝ)/16384), ((6208042265:ℝ)/2048), ((56441625:ℝ)/64), ((5338855:ℝ)/32), ((79415:ℝ)/4), (1350:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e) - (((11195763983635:ℝ)/2097152) + ((1155072195165:ℝ)/131072)*t)| ≤ ((232353933875:ℝ)/2097152) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 16, ([((-747714047969508892918515815:ℝ)/985162418487296), ((-706174487111030649979337145:ℝ)/246290604621824), ((-4474715115772123212579179:ℝ)/1099511627776), ((-11190725789066648513922979:ℝ)/3848290697216), ((-243350948556789089325753:ℝ)/240518168576), ((-105631388851971017489:ℝ)/60129542144), ((77906982352536583475:ℝ)/469762048), ((76748204452107114861:ℝ)/939524096), ((1228580566207013111:ℝ)/58720256), ((6142833739849179:ℝ)/2097152), ((45899540602623:ℝ)/458752), ((-10025234614305:ℝ)/229376), ((-134181236151:ℝ)/14336), ((-3297070899:ℝ)/3584), ((-2670327:ℝ)/56), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e) - ((-747714047969508892918515815:ℝ)/985162418487296) - ((-706174487111030649979337145:ℝ)/246290604621824)*t| ≤ ((136970882319465484979219585:ℝ)/1970324836974592) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 16, ([((-747714047969508892918515815:ℝ)/985162418487296), ((-706174487111030649979337145:ℝ)/246290604621824), ((-4474715115772123212579179:ℝ)/1099511627776), ((-11190725789066648513922979:ℝ)/3848290697216), ((-243350948556789089325753:ℝ)/240518168576), ((-105631388851971017489:ℝ)/60129542144), ((77906982352536583475:ℝ)/469762048), ((76748204452107114861:ℝ)/939524096), ((1228580566207013111:ℝ)/58720256), ((6142833739849179:ℝ)/2097152), ((45899540602623:ℝ)/458752), ((-10025234614305:ℝ)/229376), ((-134181236151:ℝ)/14336), ((-3297070899:ℝ)/3584), ((-2670327:ℝ)/56), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e)| ≤ ((292321683171189240099448545:ℝ)/246290604621824) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((163788344333921:ℝ)/4194304) - ((39259611551865:ℝ)/524288)*t| ≤ ((2218722018707:ℝ)/2097152) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/4) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-7627725:ℝ)/2), (173988600:ℝ), (-2299614450:ℝ), (13088188200:ℝ), (-38221499200:ℝ), (63366115840:ℝ), ((-445610508288:ℝ)/7), ((841540698112:ℝ)/21), ((-326820167680:ℝ)/21), ((10133438464:ℝ)/3), ((-2147483648:ℝ)/7)] : List ℝ).getD e 0) 16 hq1'
  have m13' : |centralNum13_23 q| ≤ ((246012824343177901874781:ℝ)/2048) := by
    rw [centralNum13_23_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/4) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-15801525:ℝ)/4), ((655493865:ℝ)/4), ((-7334421225:ℝ)/4), ((16442962485:ℝ)/2), ((-598626108395:ℝ)/32), ((414013307125:ℝ)/16), ((-4611984703125:ℝ)/224), ((399923828125:ℝ)/48), ((-4353201171875:ℝ)/2688), ((189736328125:ℝ)/1344), ((-244140625:ℝ)/56)] : List ℝ).getD e 0) 16 hq1'
  have m23' : |centralNum23_23 q| ≤ ((198531775173953280556510380045:ℝ)/17179869184) := by
    rw [centralNum23_23_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((475639221747518193893788855829:ℝ)/100000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece23_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece23_E11 h0) m23'
  have c5 := scaled_affine (X := ((-902472723309:ℝ)/10000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((11195763983635:ℝ)/2097152) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((-747714047969508892918515815:ℝ)/985162418487296) + ((163788344333921:ℝ)/4194304)*((-902472723309:ℝ)/10000000000000) - ((26891359308561771:ℝ)/50000000000)) (β := ((1155072195165:ℝ)/131072) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((-706174487111030649979337145:ℝ)/246290604621824) - 3*((-747714047969508892918515815:ℝ)/985162418487296)) + ((39259611551865:ℝ)/524288)*((-902472723309:ℝ)/10000000000000) - ((106174832258629999:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_23 2 3 = centralNum11_23 q + 8*(Real.exp (-(3*((41:ℝ)/8)))*Real.exp (-3*t))*centralNum12_23 q + 18*Real.exp (-8*q)*centralNum13_23 q + 72*Real.exp (-11*q)*centralNum23_23 q + 8*q^7*(2*q-3)^2*((-902472723309:ℝ)/10000000000000) + (0:ℝ) := by
    rw [pieceW_23, pieceX_23, sym4_23, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((1429251934063383183619778633709472053634011685062934943062663270289:ℝ)/1660555016645462026398038704623563096978299411813429453357381058560000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((11195763983635:ℝ)/2097152) + ((1155072195165:ℝ)/131072)*t) + (8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((-747714047969508892918515815:ℝ)/985162418487296) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((-706174487111030649979337145:ℝ)/246290604621824) - 3*((-747714047969508892918515815:ℝ)/985162418487296))*t) + (((163788344333921:ℝ)/4194304) + ((39259611551865:ℝ)/524288)*t)*((-902472723309:ℝ)/10000000000000) - (((26891359308561771:ℝ)/50000000000) + t * ((106174832258629999:ℝ)/100000000000)) = (((11195763983635:ℝ)/2097152) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((-747714047969508892918515815:ℝ)/985162418487296) + ((163788344333921:ℝ)/4194304)*((-902472723309:ℝ)/10000000000000) - ((26891359308561771:ℝ)/50000000000)) + t*(((1155072195165:ℝ)/131072) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((-706174487111030649979337145:ℝ)/246290604621824) - 3*((-747714047969508892918515815:ℝ)/985162418487296)) + ((39259611551865:ℝ)/524288)*((-902472723309:ℝ)/10000000000000) - ((106174832258629999:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece23_e33 {q : ℝ} (h0 : (5:ℝ) ≤ q) (h1 : q ≤ ((21:ℝ)/4)) :
    |pieceW q pieceX_23 3 3 - (((269557773955570143:ℝ)/50000000000) + (q - ((41:ℝ)/8)) * ((602327243301125547:ℝ)/1000000000000))| ≤ ((74478884187809709:ℝ)/25000000000) := by
  set t := q - ((41:ℝ)/8) with htd
  have hq : q = ((41:ℝ)/8) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/8) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece23_L3 piece23_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((41:ℝ)/8))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_33 q = ∑ e ∈ Finset.range 10, ([((335894861543215:ℝ)/29360128), ((91395968898945:ℝ)/3670016), ((1334795990775:ℝ)/57344), ((12753895215:ℝ)/1024), ((2177240145:ℝ)/512), ((62014335:ℝ)/64), (148260:ℝ), ((103200:ℝ)/7), ((6060:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_33; ring
  have h12 : centralNum12_33 q = ∑ e ∈ Finset.range 17, ([((350263939423115185438294082201:ℝ)/110338190870577152), ((222311683788543614955012778353:ℝ)/27584547717644288), ((24151009356050335118092201755:ℝ)/3448068464705536), ((61684401775949044799261847:ℝ)/61572651155456), ((-21000163860298398217890507:ℝ)/7696581394432), ((-2379029316929339158986045:ℝ)/962072674304), ((-126124708507407051660735:ℝ)/120259084288), ((-24804903749111077995915:ℝ)/105226698752), ((-184535014134075845757:ℝ)/13153337344), ((12839421243297012947:ℝ)/1644167168), ((76460895887941287:ℝ)/29360128), ((1358168342054373:ℝ)/3670016), ((8789357532015:ℝ)/458752), ((-108526001823:ℝ)/57344), ((-19590745779:ℝ)/50176), ((-165396249:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_33; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((335894861543215:ℝ)/29360128), ((91395968898945:ℝ)/3670016), ((1334795990775:ℝ)/57344), ((12753895215:ℝ)/1024), ((2177240145:ℝ)/512), ((62014335:ℝ)/64), (148260:ℝ), ((103200:ℝ)/7), ((6060:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((350263939423115185438294082201:ℝ)/110338190870577152), ((222311683788543614955012778353:ℝ)/27584547717644288), ((24151009356050335118092201755:ℝ)/3448068464705536), ((61684401775949044799261847:ℝ)/61572651155456), ((-21000163860298398217890507:ℝ)/7696581394432), ((-2379029316929339158986045:ℝ)/962072674304), ((-126124708507407051660735:ℝ)/120259084288), ((-24804903749111077995915:ℝ)/105226698752), ((-184535014134075845757:ℝ)/13153337344), ((12839421243297012947:ℝ)/1644167168), ((76460895887941287:ℝ)/29360128), ((1358168342054373:ℝ)/3670016), ((8789357532015:ℝ)/458752), ((-108526001823:ℝ)/57344), ((-19590745779:ℝ)/50176), ((-165396249:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 15 ht
  have m12 := abs_poly_le (fun e => ([((350263939423115185438294082201:ℝ)/110338190870577152), ((222311683788543614955012778353:ℝ)/27584547717644288), ((24151009356050335118092201755:ℝ)/3448068464705536), ((61684401775949044799261847:ℝ)/61572651155456), ((-21000163860298398217890507:ℝ)/7696581394432), ((-2379029316929339158986045:ℝ)/962072674304), ((-126124708507407051660735:ℝ)/120259084288), ((-24804903749111077995915:ℝ)/105226698752), ((-184535014134075845757:ℝ)/13153337344), ((12839421243297012947:ℝ)/1644167168), ((76460895887941287:ℝ)/29360128), ((1358168342054373:ℝ)/3670016), ((8789357532015:ℝ)/458752), ((-108526001823:ℝ)/57344), ((-19590745779:ℝ)/50176), ((-165396249:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 17 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((335894861543215:ℝ)/29360128), ((91395968898945:ℝ)/3670016), ((1334795990775:ℝ)/57344), ((12753895215:ℝ)/1024), ((2177240145:ℝ)/512), ((62014335:ℝ)/64), (148260:ℝ), ((103200:ℝ)/7), ((6060:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e) - (((335894861543215:ℝ)/29360128) + ((91395968898945:ℝ)/3670016)*t)| ≤ ((713997027125:ℝ)/1835008) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 17, ([((350263939423115185438294082201:ℝ)/110338190870577152), ((222311683788543614955012778353:ℝ)/27584547717644288), ((24151009356050335118092201755:ℝ)/3448068464705536), ((61684401775949044799261847:ℝ)/61572651155456), ((-21000163860298398217890507:ℝ)/7696581394432), ((-2379029316929339158986045:ℝ)/962072674304), ((-126124708507407051660735:ℝ)/120259084288), ((-24804903749111077995915:ℝ)/105226698752), ((-184535014134075845757:ℝ)/13153337344), ((12839421243297012947:ℝ)/1644167168), ((76460895887941287:ℝ)/29360128), ((1358168342054373:ℝ)/3670016), ((8789357532015:ℝ)/458752), ((-108526001823:ℝ)/57344), ((-19590745779:ℝ)/50176), ((-165396249:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e) - ((350263939423115185438294082201:ℝ)/110338190870577152) - ((222311683788543614955012778353:ℝ)/27584547717644288)*t| ≤ ((24747362396505104685689030267:ℝ)/220676381741154304) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 17, ([((350263939423115185438294082201:ℝ)/110338190870577152), ((222311683788543614955012778353:ℝ)/27584547717644288), ((24151009356050335118092201755:ℝ)/3448068464705536), ((61684401775949044799261847:ℝ)/61572651155456), ((-21000163860298398217890507:ℝ)/7696581394432), ((-2379029316929339158986045:ℝ)/962072674304), ((-126124708507407051660735:ℝ)/120259084288), ((-24804903749111077995915:ℝ)/105226698752), ((-184535014134075845757:ℝ)/13153337344), ((12839421243297012947:ℝ)/1644167168), ((76460895887941287:ℝ)/29360128), ((1358168342054373:ℝ)/3670016), ((8789357532015:ℝ)/458752), ((-108526001823:ℝ)/57344), ((-19590745779:ℝ)/50176), ((-165396249:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e)| ≤ ((473793462515639545258644986511:ℝ)/110338190870577152) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((163788344333921:ℝ)/4194304), ((39259611551865:ℝ)/524288), ((1042358240397:ℝ)/16384), ((64384964385:ℝ)/2048), ((5098982343:ℝ)/512), ((134249703:ℝ)/64), ((1175265:ℝ)/4), (26394:ℝ), (1380:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((163788344333921:ℝ)/4194304) - ((39259611551865:ℝ)/524288)*t| ≤ ((2218722018707:ℝ)/2097152) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/4) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-8120475:ℝ)/4), ((464861025:ℝ)/2), (-5906535975:ℝ), ((411904731750:ℝ)/7), ((-2024051769000:ℝ)/7), ((5554394637600:ℝ)/7), (-1314913862656:ℝ), ((9709155336192:ℝ)/7), ((-6724555112448:ℝ)/7), ((1313173667840:ℝ)/3), ((-6168244125696:ℝ)/49), ((3004329623552:ℝ)/147), ((-68719476736:ℝ)/49)] : List ℝ).getD e 0) 17 hq1'
  have m13' : |centralNum13_33 q| ≤ ((39756415159325129485222737:ℝ)/8192) := by
    rw [centralNum13_33_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((21:ℝ)/4) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-16872075:ℝ)/8), ((1833754545:ℝ)/8), ((-83998007145:ℝ)/16), ((4929124002765:ℝ)/112), ((-76723155584685:ℝ)/448), ((164888745653055:ℝ)/448), ((-63358359907625:ℝ)/128), ((364713160040625:ℝ)/896), ((-334937462578125:ℝ)/1792), ((245466998046875:ℝ)/5376), ((-72144521484375:ℝ)/12544), ((6518798828125:ℝ)/18816), ((-6103515625:ℝ)/784)] : List ℝ).getD e 0) 17 hq1'
  have m23' : |centralNum23_33 q| ≤ ((44559060461519467868825707958715:ℝ)/137438953472) := by
    rw [centralNum23_33_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((475639221747518193893788855829:ℝ)/100000000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece23_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece23_E11 h0) m23'
  have c5 := scaled_affine (X := ((-145820380919:ℝ)/500000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3))| ≤ ((9503177861156195818933105468750:ℝ)/3709345505511159776994831653937651) := by
    rw [abs_neg, tailWeight_3, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((21:ℝ)/4)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((21:ℝ)/4)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece23_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((3308571812705231500:ℝ)/129140163)) ≤ ((21:ℝ)/4)^6*(8000*(2*((21:ℝ)/4)-3)^2*(1/((188454275542913162474969854897:ℝ)/2000000))*((3308571812705231500:ℝ)/129140163)) := by
          gcongr
      _ ≤ ((9503177861156195818933105468750:ℝ)/3709345505511159776994831653937651) := by norm_num
  have c7 := affine_round (α := ((335894861543215:ℝ)/29360128) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((350263939423115185438294082201:ℝ)/110338190870577152) + ((163788344333921:ℝ)/4194304)*((-145820380919:ℝ)/500000000000) - ((269557773955570143:ℝ)/50000000000)) (β := ((91395968898945:ℝ)/3670016) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((222311683788543614955012778353:ℝ)/27584547717644288) - 3*((350263939423115185438294082201:ℝ)/110338190870577152)) + ((39259611551865:ℝ)/524288)*((-145820380919:ℝ)/500000000000) - ((602327243301125547:ℝ)/1000000000000)) ht
  have hW : pieceW q pieceX_23 3 3 = centralNum11_33 q + 8*(Real.exp (-(3*((41:ℝ)/8)))*Real.exp (-3*t))*centralNum12_33 q + 18*Real.exp (-8*q)*centralNum13_33 q + 72*Real.exp (-11*q)*centralNum23_33 q + 8*q^7*(2*q-3)^2*((-145820380919:ℝ)/500000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3)) := by
    rw [pieceW_33, pieceX_23, sym4_33, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((301854352352270114231004661681869567698755794123178764074133092841:ℝ)/290597127912955854619656773309123541971202397067350154337541685248000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((335894861543215:ℝ)/29360128) + ((91395968898945:ℝ)/3670016)*t) + (8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((350263939423115185438294082201:ℝ)/110338190870577152) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((222311683788543614955012778353:ℝ)/27584547717644288) - 3*((350263939423115185438294082201:ℝ)/110338190870577152))*t) + (((163788344333921:ℝ)/4194304) + ((39259611551865:ℝ)/524288)*t)*((-145820380919:ℝ)/500000000000) - (((269557773955570143:ℝ)/50000000000) + t * ((602327243301125547:ℝ)/1000000000000)) = (((335894861543215:ℝ)/29360128) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*((350263939423115185438294082201:ℝ)/110338190870577152) + ((163788344333921:ℝ)/4194304)*((-145820380919:ℝ)/500000000000) - ((269557773955570143:ℝ)/50000000000)) + t*(((91395968898945:ℝ)/3670016) + 8*(((1/((475639221747518193893788855829:ℝ)/100000000000000000000000))+(1/((23781960869657420254275816301:ℝ)/5000000000000000000000)))/2)*(((222311683788543614955012778353:ℝ)/27584547717644288) - 3*((350263939423115185438294082201:ℝ)/110338190870577152)) + ((39259611551865:ℝ)/524288)*((-145820380919:ℝ)/500000000000) - ((602327243301125547:ℝ)/1000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece23_plus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((674913930295742753:ℝ)/100000000000) + ((1:ℝ)/8)*((21007787300673907:ℝ)/2000000000) - (((42280722753680473:ℝ)/20000000000) + ((3603643440639837:ℝ)/20000000000) + ((269315814664545349:ℝ)/10000000000000) + ((168738692681523943:ℝ)/10000000000000)))
      (((-439053637129836321:ℝ)/1000000000000) + ((1:ℝ)/8)*((42638329277237611:ℝ)/25000000000))
      (((429963797225000197:ℝ)/10000000000000) + ((1:ℝ)/8)*((42650034308382509:ℝ)/250000000000))
      (((10070885085285511:ℝ)/125000000000) + ((1:ℝ)/8)*((-659583856830948193:ℝ)/10000000000000))
      (((486543710518857781:ℝ)/100000000000) + ((1:ℝ)/8)*((58253754636779589:ℝ)/10000000000) - (((3603643440639837:ℝ)/20000000000) + ((143796435305291509:ℝ)/100000000000) + ((136392280253143861:ℝ)/1000000000000) + ((463467965146501679:ℝ)/5000000000000)))
      (((-115536401476607073:ℝ)/1000000000000) + ((1:ℝ)/8)*((102018025382534407:ℝ)/100000000000))
      (((-101513939131995057:ℝ)/500000000000) + ((1:ℝ)/8)*((924050204773504973:ℝ)/1000000000000))
      (((110715986345691769:ℝ)/20000000000) + ((1:ℝ)/8)*((13157371059420097:ℝ)/1250000000) - (((269315814664545349:ℝ)/10000000000000) + ((136392280253143861:ℝ)/1000000000000) + ((142223237700095477:ℝ)/100000000000) + ((176603433976257373:ℝ)/200000000000)))
      (((26891359308561771:ℝ)/50000000000) + ((1:ℝ)/8)*((106174832258629999:ℝ)/100000000000))
      (((269557773955570143:ℝ)/50000000000) + ((1:ℝ)/8)*((602327243301125547:ℝ)/1000000000000) - (((168738692681523943:ℝ)/10000000000000) + ((463467965146501679:ℝ)/5000000000000) + ((176603433976257373:ℝ)/200000000000) + ((74478884187809709:ℝ)/25000000000))) i j :=
  quadForm_nonneg_of_ldl ((57241022487989242883:ℝ)/10000000000000) ((2139362930975533283077450898211687378631:ℝ)/572410224879892428830000000000000) ((375003262865880206516566704600006447675781062232847451087817:ℝ)/85574517239021331323098035928467495145240000000000000) ((13338529526423490508510491847921756631128153839990174872038243550731274769446021:ℝ)/9600083529366533286824107637760165060499995193160894747848115200000000000) ((-2258619907436482660:ℝ)/57241022487989242883) ((643213968766912742:ℝ)/57241022487989242883) ((57284976215364147:ℝ)/4533942375286276664) ((16627518774667707895350985286862262785:ℝ)/4278725861951066566154901796423374757262) ((-193859099180864838444714337135812414175:ℝ)/8557451723902133132309803592846749514524) ((114680476749204113184026954498936124094156193978527887199207:ℝ)/750006525731760413033133409200012895351562124465694902175634)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece23_minus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((674913930295742753:ℝ)/100000000000) - ((1:ℝ)/8)*((21007787300673907:ℝ)/2000000000) - (((42280722753680473:ℝ)/20000000000) + ((3603643440639837:ℝ)/20000000000) + ((269315814664545349:ℝ)/10000000000000) + ((168738692681523943:ℝ)/10000000000000)))
      (((-439053637129836321:ℝ)/1000000000000) - ((1:ℝ)/8)*((42638329277237611:ℝ)/25000000000))
      (((429963797225000197:ℝ)/10000000000000) - ((1:ℝ)/8)*((42650034308382509:ℝ)/250000000000))
      (((10070885085285511:ℝ)/125000000000) - ((1:ℝ)/8)*((-659583856830948193:ℝ)/10000000000000))
      (((486543710518857781:ℝ)/100000000000) - ((1:ℝ)/8)*((58253754636779589:ℝ)/10000000000) - (((3603643440639837:ℝ)/20000000000) + ((143796435305291509:ℝ)/100000000000) + ((136392280253143861:ℝ)/1000000000000) + ((463467965146501679:ℝ)/5000000000000)))
      (((-115536401476607073:ℝ)/1000000000000) - ((1:ℝ)/8)*((102018025382534407:ℝ)/100000000000))
      (((-101513939131995057:ℝ)/500000000000) - ((1:ℝ)/8)*((924050204773504973:ℝ)/1000000000000))
      (((110715986345691769:ℝ)/20000000000) - ((1:ℝ)/8)*((13157371059420097:ℝ)/1250000000) - (((269315814664545349:ℝ)/10000000000000) + ((136392280253143861:ℝ)/1000000000000) + ((142223237700095477:ℝ)/100000000000) + ((176603433976257373:ℝ)/200000000000)))
      (((26891359308561771:ℝ)/50000000000) - ((1:ℝ)/8)*((106174832258629999:ℝ)/100000000000))
      (((269557773955570143:ℝ)/50000000000) - ((1:ℝ)/8)*((602327243301125547:ℝ)/1000000000000) - (((168738692681523943:ℝ)/10000000000000) + ((463467965146501679:ℝ)/5000000000000) + ((176603433976257373:ℝ)/200000000000) + ((74478884187809709:ℝ)/25000000000))) i j :=
  quadForm_nonneg_of_ldl ((30981288362146859133:ℝ)/10000000000000) ((666939266270806262537822996279527783631:ℝ)/309812883621468591330000000000000) ((46016528809850809399345508224809601476592846690550775632447:ℝ)/26677570650832250501512919851181111345240000000000000) ((57483051096610914413253889690568593176503265501045287370673190308982682545701:ℝ)/47120925501287228824929800422205031912031075011123994247625728000000000) ((-6522452835160243760:ℝ)/30981288362146859133) ((72237875227695884:ℝ)/10327096120715619711) ((7104950311413675233:ℝ)/247850306897174873064) ((-147778569167749558797817467561784079415:ℝ)/1333878532541612525075645992559055567262) ((-371573087306828714201612847294156890485:ℝ)/2667757065083225050151291985118111134524) ((19809105291724788316275018180742968831054248810744355433713:ℝ)/92033057619701618798691016449619202953185693381101551264894)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

/-- **Piece 23.** The piece matrix is positive semidefinite on `q ∈ [5, 21/4]`. -/
theorem piece_23 {q : ℝ} (h0 : (5:ℝ) ≤ q) (h1 : q ≤ ((21:ℝ)/4)) (y : Fin 4 → ℝ) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceW q pieceX_23 i j :=
  pieceForm_nonneg (pieceW_symm (sym4_symm _ _ _ _ _ _ _ _ _ _) q) (by norm_num : (0:ℝ) < ((1:ℝ)/8))
    (abs_le.mpr ⟨by linarith, by linarith⟩)
    (piece23_e00 h0 h1) (piece23_e01 h0 h1) (piece23_e02 h0 h1) (piece23_e03 h0 h1) (piece23_e11 h0 h1) (piece23_e12 h0 h1) (piece23_e13 h0 h1) (piece23_e22 h0 h1) (piece23_e23 h0 h1) (piece23_e33 h0 h1)
    piece23_plus piece23_minus y

/-! #### Piece 24 (bulk), `q ∈ [21/4, 11/2]` -/

/-- The compensation matrix of piece 24. -/
def pieceX_24 : Fin 4 → Fin 4 → ℝ :=
  sym4 ((-936217303929:ℝ)/1000000000000) ((452262246341:ℝ)/5000000000000) ((104622427621:ℝ)/50000000000000) ((3311168209:ℝ)/7812500000000) ((-319395341541:ℝ)/500000000000) ((11590978213:ℝ)/312500000000) ((187851920419:ℝ)/10000000000000) ((-591305273179:ℝ)/1000000000000) ((-459818084627:ℝ)/5000000000000) ((-291458477247:ℝ)/1000000000000)

theorem piece24_L3 : ((25173205951636628266068425251:ℝ)/2500000000000000000000) ≤ Real.exp ((3:ℝ)*((43:ℝ)/8)) := by
  have h := le_exp_nat_add 16 (f := ((1:ℝ)/8)) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((43:ℝ)/8) = ((16:ℕ):ℝ) + ((1:ℝ)/8) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece24_U3 : Real.exp ((3:ℝ)*((43:ℝ)/8)) ≤ ((12586602998062478850617801581:ℝ)/1250000000000000000000) := by
  have h := exp_nat_add_le 16 (f := ((1:ℝ)/8)) (by norm_num) (by norm_num)
  rw [show ((3:ℝ):ℝ)*((43:ℝ)/8) = ((16:ℕ):ℝ) + ((1:ℝ)/8) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem piece24_L8_at : ((17392749372464105735872954001:ℝ)/10000000000) ≤ Real.exp ((8:ℝ)*((21:ℝ)/4)) := by
  have h := le_exp_nat_add 42 (f := (0:ℝ)) (by norm_num)
  rw [show ((8:ℝ):ℝ)*((21:ℝ)/4) = ((42:ℕ):ℝ) + (0:ℝ) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece24_E8 {q : ℝ} (h0 : ((21:ℝ)/4) ≤ q) : Real.exp (-((8:ℝ))*q) ≤ 1/((17392749372464105735872954001:ℝ)/10000000000) := by
  have hm : Real.exp (-((8:ℝ))*q) ≤ Real.exp (-((8:ℝ)*((21:ℝ)/4))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece24_L8_at (le_refl _)).2

theorem piece24_L11_at : ((120366539043960987748087249207:ℝ)/10000) ≤ Real.exp ((11:ℝ)*((21:ℝ)/4)) := by
  have h := le_exp_nat_add 57 (f := ((3:ℝ)/4)) (by norm_num)
  rw [show ((11:ℝ):ℝ)*((21:ℝ)/4) = ((57:ℕ):ℝ) + ((3:ℝ)/4) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece24_E11 {q : ℝ} (h0 : ((21:ℝ)/4) ≤ q) : Real.exp (-((11:ℝ))*q) ≤ 1/((120366539043960987748087249207:ℝ)/10000) := by
  have hm : Real.exp (-((11:ℝ))*q) ≤ Real.exp (-((11:ℝ)*((21:ℝ)/4))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece24_L11_at (le_refl _)).2

theorem piece24_Lt_at : ((132704895456233735154909086813:ℝ)/100000) ≤ Real.exp (((529:ℝ)/50)*((21:ℝ)/4)) := by
  have h := le_exp_nat_add 55 (f := ((109:ℝ)/200)) (by norm_num)
  rw [show (((529:ℝ)/50):ℝ)*((21:ℝ)/4) = ((55:ℕ):ℝ) + ((109:ℝ)/200) by norm_num]
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith
theorem piece24_Et {q : ℝ} (h0 : ((21:ℝ)/4) ≤ q) : Real.exp (-(((529:ℝ)/50))*q) ≤ 1/((132704895456233735154909086813:ℝ)/100000) := by
  have hm : Real.exp (-(((529:ℝ)/50))*q) ≤ Real.exp (-(((529:ℝ)/50)*((21:ℝ)/4))) := Real.exp_le_exp.mpr (by nlinarith)
  exact hm.trans (exp_neg_bounds (by norm_num) piece24_Lt_at (le_refl _)).2

theorem piece24_e00 {q : ℝ} (h0 : ((21:ℝ)/4) ≤ q) (h1 : q ≤ ((11:ℝ)/2)) :
    |pieceW q pieceX_24 0 0 - (((25470002375676399:ℝ)/2500000000) + (q - ((43:ℝ)/8)) * ((479121735698959:ℝ)/31250000))| ≤ ((150243073075922833:ℝ)/50000000000) := by
  set t := q - ((43:ℝ)/8) with htd
  have hq : q = ((43:ℝ)/8) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/8) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece24_L3 piece24_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((43:ℝ)/8))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_00 q = ∑ e ∈ Finset.range 10, ([((287312271940099:ℝ)/4194304), ((63624519088185:ℝ)/524288), ((1569609145911:ℝ)/16384), ((90533269281:ℝ)/2048), ((6723668469:ℝ)/512), ((166615239:ℝ)/64), ((1377075:ℝ)/4), (29274:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_00; ring
  have h12 : centralNum12_00 q = ∑ e ∈ Finset.range 11, ([((-15218308580047609:ℝ)/2097152), ((-29666909031159831:ℝ)/2097152), ((-3253864149171537:ℝ)/262144), ((-52879029254727:ℝ)/8192), ((-2255918499345:ℝ)/1024), ((-131987420313:ℝ)/256), ((-2681130711:ℝ)/32), ((-18670731:ℝ)/2), (-682476:ℝ), (-29560:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_00; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((287312271940099:ℝ)/4194304), ((63624519088185:ℝ)/524288), ((1569609145911:ℝ)/16384), ((90533269281:ℝ)/2048), ((6723668469:ℝ)/512), ((166615239:ℝ)/64), ((1377075:ℝ)/4), (29274:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-15218308580047609:ℝ)/2097152), ((-29666909031159831:ℝ)/2097152), ((-3253864149171537:ℝ)/262144), ((-52879029254727:ℝ)/8192), ((-2255918499345:ℝ)/1024), ((-131987420313:ℝ)/256), ((-2681130711:ℝ)/32), ((-18670731:ℝ)/2), (-682476:ℝ), (-29560:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 9 ht
  have m12 := abs_poly_le (fun e => ([((-15218308580047609:ℝ)/2097152), ((-29666909031159831:ℝ)/2097152), ((-3253864149171537:ℝ)/262144), ((-52879029254727:ℝ)/8192), ((-2255918499345:ℝ)/1024), ((-131987420313:ℝ)/256), ((-2681130711:ℝ)/32), ((-18670731:ℝ)/2), (-682476:ℝ), (-29560:ℝ), (-576:ℝ)] : List ℝ).getD e 0) 11 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((287312271940099:ℝ)/4194304), ((63624519088185:ℝ)/524288), ((1569609145911:ℝ)/16384), ((90533269281:ℝ)/2048), ((6723668469:ℝ)/512), ((166615239:ℝ)/64), ((1377075:ℝ)/4), (29274:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - (((287312271940099:ℝ)/4194304) + ((63624519088185:ℝ)/524288)*t)| ≤ ((1663588948849:ℝ)/1048576) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 11, ([((-15218308580047609:ℝ)/2097152), ((-29666909031159831:ℝ)/2097152), ((-3253864149171537:ℝ)/262144), ((-52879029254727:ℝ)/8192), ((-2255918499345:ℝ)/1024), ((-131987420313:ℝ)/256), ((-2681130711:ℝ)/32), ((-18670731:ℝ)/2), (-682476:ℝ), (-29560:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e) - ((-15218308580047609:ℝ)/2097152) - ((-29666909031159831:ℝ)/2097152)*t| ≤ ((3474673352658977:ℝ)/16777216) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 11, ([((-15218308580047609:ℝ)/2097152), ((-29666909031159831:ℝ)/2097152), ((-3253864149171537:ℝ)/262144), ((-52879029254727:ℝ)/8192), ((-2255918499345:ℝ)/1024), ((-131987420313:ℝ)/256), ((-2681130711:ℝ)/32), ((-18670731:ℝ)/2), (-682476:ℝ), (-29560:ℝ), (-576:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((36928189045:ℝ)/4) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((261217685273827:ℝ)/4194304) - ((59376563119257:ℝ)/524288)*t| ≤ ((1586557175713:ℝ)/1048576) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((11:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (600:ℝ), (-7776:ℝ), (16800:ℝ), (-9216:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m13' : |centralNum13_00 q| ≤ ((2539275817155:ℝ)/8) := by
    rw [centralNum13_00_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((11:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (780:ℝ), (-6156:ℝ), (15288:ℝ), (-14400:ℝ)] : List ℝ).getD e 0) 11 hq1'
  have m23' : |centralNum23_00 q| ≤ ((14093609246475:ℝ)/32) := by
    rw [centralNum23_00_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((12586602998062478850617801581:ℝ)/1250000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece24_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece24_E11 h0) m23'
  have c5 := scaled_affine (X := ((-936217303929:ℝ)/1000000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0))| ≤ ((14832216749500480000000000:ℝ)/7836091371795145827162226667220837) := by
    rw [abs_neg, tailWeight_0, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((11:ℝ)/2)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((11:ℝ)/2)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece24_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((10465499600:ℝ)/59049)) ≤ ((11:ℝ)/2)^6*(8000*(2*((11:ℝ)/2)-3)^2*(1/((132704895456233735154909086813:ℝ)/100000))*((10465499600:ℝ)/59049)) := by
          gcongr
      _ ≤ ((14832216749500480000000000:ℝ)/7836091371795145827162226667220837) := by norm_num
  have c7 := affine_round (α := ((287312271940099:ℝ)/4194304) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((-15218308580047609:ℝ)/2097152) + ((261217685273827:ℝ)/4194304)*((-936217303929:ℝ)/1000000000000) - ((25470002375676399:ℝ)/2500000000)) (β := ((63624519088185:ℝ)/524288) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((-29666909031159831:ℝ)/2097152) - 3*((-15218308580047609:ℝ)/2097152)) + ((59376563119257:ℝ)/524288)*((-936217303929:ℝ)/1000000000000) - ((479121735698959:ℝ)/31250000)) ht
  have hW : pieceW q pieceX_24 0 0 = centralNum11_00 q + 8*(Real.exp (-(3*((43:ℝ)/8)))*Real.exp (-3*t))*centralNum12_00 q + 18*Real.exp (-8*q)*centralNum13_00 q + 72*Real.exp (-11*q)*centralNum23_00 q + 8*q^7*(2*q-3)^2*((-936217303929:ℝ)/1000000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 0)) := by
    rw [pieceW_00, pieceX_24, sym4_00, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((4596701683008937865427526596261314928205849500245832514857655183:ℝ)/132894487793563628759482616103599517816546311536324639438825062400000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((287312271940099:ℝ)/4194304) + ((63624519088185:ℝ)/524288)*t) + (8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((-15218308580047609:ℝ)/2097152) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((-29666909031159831:ℝ)/2097152) - 3*((-15218308580047609:ℝ)/2097152))*t) + (((261217685273827:ℝ)/4194304) + ((59376563119257:ℝ)/524288)*t)*((-936217303929:ℝ)/1000000000000) - (((25470002375676399:ℝ)/2500000000) + t * ((479121735698959:ℝ)/31250000)) = (((287312271940099:ℝ)/4194304) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((-15218308580047609:ℝ)/2097152) + ((261217685273827:ℝ)/4194304)*((-936217303929:ℝ)/1000000000000) - ((25470002375676399:ℝ)/2500000000)) + t*(((63624519088185:ℝ)/524288) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((-29666909031159831:ℝ)/2097152) - 3*((-15218308580047609:ℝ)/2097152)) + ((59376563119257:ℝ)/524288)*((-936217303929:ℝ)/1000000000000) - ((479121735698959:ℝ)/31250000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece24_e01 {q : ℝ} (h0 : ((21:ℝ)/4) ≤ q) (h1 : q ≤ ((11:ℝ)/2)) :
    |pieceW q pieceX_24 0 1 - (((-61713250851307927:ℝ)/100000000000) + (q - ((43:ℝ)/8)) * ((216352593068135189:ℝ)/100000000000))| ≤ ((55071921738866667:ℝ)/250000000000) := by
  set t := q - ((43:ℝ)/8) with htd
  have hq : q = ((43:ℝ)/8) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/8) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece24_L3 piece24_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((43:ℝ)/8))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_01 q = ∑ e ∈ Finset.range 8, ([((-815455833321:ℝ)/131072), ((-132748624029:ℝ)/16384), ((-9261531909:ℝ)/2048), ((-358974105:ℝ)/256), ((-8348235:ℝ)/32), ((-116487:ℝ)/4), (-1806:ℝ), (-48:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_01; ring
  have h12 : centralNum12_01 q = ∑ e ∈ Finset.range 12, ([((-1224768180665642703:ℝ)/33554432), ((-2747037311413316871:ℝ)/33554432), ((-174786039508020327:ℝ)/2097152), ((-26655333151594863:ℝ)/524288), ((-169165026409875:ℝ)/8192), ((-24019928905959:ℝ)/4096), ((-304172749797:ℝ)/256), ((-10993086219:ℝ)/64), (-17363016:ℝ), ((-2337675:ℝ)/2), (-47160:ℝ), (-864:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_01; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-815455833321:ℝ)/131072), ((-132748624029:ℝ)/16384), ((-9261531909:ℝ)/2048), ((-358974105:ℝ)/256), ((-8348235:ℝ)/32), ((-116487:ℝ)/4), (-1806:ℝ), (-48:ℝ)] : List ℝ).getD e 0) 6 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-1224768180665642703:ℝ)/33554432), ((-2747037311413316871:ℝ)/33554432), ((-174786039508020327:ℝ)/2097152), ((-26655333151594863:ℝ)/524288), ((-169165026409875:ℝ)/8192), ((-24019928905959:ℝ)/4096), ((-304172749797:ℝ)/256), ((-10993086219:ℝ)/64), (-17363016:ℝ), ((-2337675:ℝ)/2), (-47160:ℝ), (-864:ℝ)] : List ℝ).getD e 0) 10 ht
  have m12 := abs_poly_le (fun e => ([((-1224768180665642703:ℝ)/33554432), ((-2747037311413316871:ℝ)/33554432), ((-174786039508020327:ℝ)/2097152), ((-26655333151594863:ℝ)/524288), ((-169165026409875:ℝ)/8192), ((-24019928905959:ℝ)/4096), ((-304172749797:ℝ)/256), ((-10993086219:ℝ)/64), (-17363016:ℝ), ((-2337675:ℝ)/2), (-47160:ℝ), (-864:ℝ)] : List ℝ).getD e 0) 12 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 8, ([((-815455833321:ℝ)/131072), ((-132748624029:ℝ)/16384), ((-9261531909:ℝ)/2048), ((-358974105:ℝ)/256), ((-8348235:ℝ)/32), ((-116487:ℝ)/4), (-1806:ℝ), (-48:ℝ)] : List ℝ).getD e 0 * t^e) - (((-815455833321:ℝ)/131072) + ((-132748624029:ℝ)/16384)*t)| ≤ ((4814485821:ℝ)/65536) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 12, ([((-1224768180665642703:ℝ)/33554432), ((-2747037311413316871:ℝ)/33554432), ((-174786039508020327:ℝ)/2097152), ((-26655333151594863:ℝ)/524288), ((-169165026409875:ℝ)/8192), ((-24019928905959:ℝ)/4096), ((-304172749797:ℝ)/256), ((-10993086219:ℝ)/64), (-17363016:ℝ), ((-2337675:ℝ)/2), (-47160:ℝ), (-864:ℝ)] : List ℝ).getD e 0 * t^e) - ((-1224768180665642703:ℝ)/33554432) - ((-2747037311413316871:ℝ)/33554432)*t| ≤ ((377630011194055809:ℝ)/268435456) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 12, ([((-1224768180665642703:ℝ)/33554432), ((-2747037311413316871:ℝ)/33554432), ((-174786039508020327:ℝ)/2097152), ((-26655333151594863:ℝ)/524288), ((-169165026409875:ℝ)/8192), ((-24019928905959:ℝ)/4096), ((-304172749797:ℝ)/256), ((-10993086219:ℝ)/64), (-17363016:ℝ), ((-2337675:ℝ)/2), (-47160:ℝ), (-864:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((1540519329063:ℝ)/32) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((261217685273827:ℝ)/4194304) - ((59376563119257:ℝ)/524288)*t| ≤ ((1586557175713:ℝ)/1048576) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((11:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-6288:ℝ), (81024:ℝ), (-238720:ℝ), (246784:ℝ), (-98304:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m13' : |centralNum13_01 q| ≤ ((168912596177677:ℝ)/8) := by
    rw [centralNum13_01_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((11:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-7368:ℝ), (59208:ℝ), (-155734:ℝ), (205300:ℝ), (-60000:ℝ)] : List ℝ).getD e 0) 12 hq1'
  have m23' : |centralNum23_01 q| ≤ ((1833830541831013:ℝ)/128) := by
    rw [centralNum23_01_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((12586602998062478850617801581:ℝ)/1250000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece24_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece24_E11 h0) m23'
  have c5 := scaled_affine (X := ((452262246341:ℝ)/5000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-815455833321:ℝ)/131072) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((-1224768180665642703:ℝ)/33554432) + ((261217685273827:ℝ)/4194304)*((452262246341:ℝ)/5000000000000) - ((-61713250851307927:ℝ)/100000000000)) (β := ((-132748624029:ℝ)/16384) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((-2747037311413316871:ℝ)/33554432) - 3*((-1224768180665642703:ℝ)/33554432)) + ((59376563119257:ℝ)/524288)*((452262246341:ℝ)/5000000000000) - ((216352593068135189:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_24 0 1 = centralNum11_01 q + 8*(Real.exp (-(3*((43:ℝ)/8)))*Real.exp (-3*t))*centralNum12_01 q + 18*Real.exp (-8*q)*centralNum13_01 q + 72*Real.exp (-11*q)*centralNum23_01 q + 8*q^7*(2*q-3)^2*((452262246341:ℝ)/5000000000000) + (0:ℝ) := by
    rw [pieceW_01, pieceX_24, sym4_01, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((916562352421803406738313264832433958650843300712303484659771741:ℝ)/1661181097419545359493532701294993972706828894204057992985313280000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-815455833321:ℝ)/131072) + ((-132748624029:ℝ)/16384)*t) + (8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((-1224768180665642703:ℝ)/33554432) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((-2747037311413316871:ℝ)/33554432) - 3*((-1224768180665642703:ℝ)/33554432))*t) + (((261217685273827:ℝ)/4194304) + ((59376563119257:ℝ)/524288)*t)*((452262246341:ℝ)/5000000000000) - (((-61713250851307927:ℝ)/100000000000) + t * ((216352593068135189:ℝ)/100000000000)) = (((-815455833321:ℝ)/131072) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((-1224768180665642703:ℝ)/33554432) + ((261217685273827:ℝ)/4194304)*((452262246341:ℝ)/5000000000000) - ((-61713250851307927:ℝ)/100000000000)) + t*(((-132748624029:ℝ)/16384) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((-2747037311413316871:ℝ)/33554432) - 3*((-1224768180665642703:ℝ)/33554432)) + ((59376563119257:ℝ)/524288)*((452262246341:ℝ)/5000000000000) - ((216352593068135189:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece24_e02 {q : ℝ} (h0 : ((21:ℝ)/4) ≤ q) (h1 : q ≤ ((11:ℝ)/2)) :
    |pieceW q pieceX_24 0 2 - (((772598531961034943:ℝ)/10000000000000) + (q - ((43:ℝ)/8)) * ((240356171036166193:ℝ)/1000000000000))| ≤ ((259452083990824539:ℝ)/10000000000000) := by
  set t := q - ((43:ℝ)/8) with htd
  have hq : q = ((43:ℝ)/8) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/8) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece24_L3 piece24_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((43:ℝ)/8))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_02 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_02; ring
  have h12 : centralNum12_02 q = ∑ e ∈ Finset.range 13, ([((-143408012602728530511:ℝ)/2147483648), ((-421081051274268525477:ℝ)/2147483648), ((-68307873605468309097:ℝ)/268435456), ((-6548784284731840515:ℝ)/33554432), ((-416060213719480335:ℝ)/4194304), ((-9267502249178361:ℝ)/262144), ((-297732385913949:ℝ)/32768), ((-6964885315539:ℝ)/4096), ((-117927817515:ℝ)/512), ((-2822107545:ℝ)/128), ((-22671117:ℝ)/16), ((-109863:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_02; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-143408012602728530511:ℝ)/2147483648), ((-421081051274268525477:ℝ)/2147483648), ((-68307873605468309097:ℝ)/268435456), ((-6548784284731840515:ℝ)/33554432), ((-416060213719480335:ℝ)/4194304), ((-9267502249178361:ℝ)/262144), ((-297732385913949:ℝ)/32768), ((-6964885315539:ℝ)/4096), ((-117927817515:ℝ)/512), ((-2822107545:ℝ)/128), ((-22671117:ℝ)/16), ((-109863:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((-143408012602728530511:ℝ)/2147483648), ((-421081051274268525477:ℝ)/2147483648), ((-68307873605468309097:ℝ)/268435456), ((-6548784284731840515:ℝ)/33554432), ((-416060213719480335:ℝ)/4194304), ((-9267502249178361:ℝ)/262144), ((-297732385913949:ℝ)/32768), ((-6964885315539:ℝ)/4096), ((-117927817515:ℝ)/512), ((-2822107545:ℝ)/128), ((-22671117:ℝ)/16), ((-109863:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((-143408012602728530511:ℝ)/2147483648), ((-421081051274268525477:ℝ)/2147483648), ((-68307873605468309097:ℝ)/268435456), ((-6548784284731840515:ℝ)/33554432), ((-416060213719480335:ℝ)/4194304), ((-9267502249178361:ℝ)/262144), ((-297732385913949:ℝ)/32768), ((-6964885315539:ℝ)/4096), ((-117927817515:ℝ)/512), ((-2822107545:ℝ)/128), ((-22671117:ℝ)/16), ((-109863:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0 * t^e) - ((-143408012602728530511:ℝ)/2147483648) - ((-421081051274268525477:ℝ)/2147483648)*t| ≤ ((75291862741660969443:ℝ)/17179869184) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((-143408012602728530511:ℝ)/2147483648), ((-421081051274268525477:ℝ)/2147483648), ((-68307873605468309097:ℝ)/268435456), ((-6548784284731840515:ℝ)/33554432), ((-416060213719480335:ℝ)/4194304), ((-9267502249178361:ℝ)/262144), ((-297732385913949:ℝ)/32768), ((-6964885315539:ℝ)/4096), ((-117927817515:ℝ)/512), ((-2822107545:ℝ)/128), ((-22671117:ℝ)/16), ((-109863:ℝ)/2), (-972:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((191344532049:ℝ)/2) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((261217685273827:ℝ)/4194304) - ((59376563119257:ℝ)/524288)*t| ≤ ((1586557175713:ℝ)/1048576) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((11:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82080:ℝ), (-967680:ℝ), (3257600:ℝ), (-4474880:ℝ), (2908160:ℝ), (-786432:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_02 q| ≤ ((4547570324027973:ℝ)/4) := by
    rw [centralNum13_02_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((11:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (87660:ℝ), (-702180:ℝ), ((7421435:ℝ)/4), ((-10854125:ℝ)/4), ((2828125:ℝ)/2), (-187500:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_02 q| ≤ ((857171054540824485:ℝ)/2048) := by
    rw [centralNum23_02_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((12586602998062478850617801581:ℝ)/1250000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece24_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece24_E11 h0) m23'
  have c5 := scaled_affine (X := ((104622427621:ℝ)/50000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((-143408012602728530511:ℝ)/2147483648) + ((261217685273827:ℝ)/4194304)*((104622427621:ℝ)/50000000000000) - ((772598531961034943:ℝ)/10000000000000)) (β := (0:ℝ) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((-421081051274268525477:ℝ)/2147483648) - 3*((-143408012602728530511:ℝ)/2147483648)) + ((59376563119257:ℝ)/524288)*((104622427621:ℝ)/50000000000000) - ((240356171036166193:ℝ)/1000000000000)) ht
  have hW : pieceW q pieceX_24 0 2 = centralNum11_02 q + 8*(Real.exp (-(3*((43:ℝ)/8)))*Real.exp (-3*t))*centralNum12_02 q + 18*Real.exp (-8*q)*centralNum13_02 q + 72*Real.exp (-11*q)*centralNum23_02 q + 8*q^7*(2*q-3)^2*((104622427621:ℝ)/50000000000000) + (0:ℝ) := by
    rw [pieceW_02, pieceX_24, sym4_02, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((240921880147976341422040853511789095487417590054305231810059389:ℝ)/6644724389678181437974130805179975890827315576816231971941253120000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((-143408012602728530511:ℝ)/2147483648) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((-421081051274268525477:ℝ)/2147483648) - 3*((-143408012602728530511:ℝ)/2147483648))*t) + (((261217685273827:ℝ)/4194304) + ((59376563119257:ℝ)/524288)*t)*((104622427621:ℝ)/50000000000000) - (((772598531961034943:ℝ)/10000000000000) + t * ((240356171036166193:ℝ)/1000000000000)) = ((0:ℝ) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((-143408012602728530511:ℝ)/2147483648) + ((261217685273827:ℝ)/4194304)*((104622427621:ℝ)/50000000000000) - ((772598531961034943:ℝ)/10000000000000)) + t*((0:ℝ) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((-421081051274268525477:ℝ)/2147483648) - 3*((-143408012602728530511:ℝ)/2147483648)) + ((59376563119257:ℝ)/524288)*((104622427621:ℝ)/50000000000000) - ((240356171036166193:ℝ)/1000000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece24_e03 {q : ℝ} (h0 : ((21:ℝ)/4) ≤ q) (h1 : q ≤ ((11:ℝ)/2)) :
    |pieceW q pieceX_24 0 3 - (((345029123397448117:ℝ)/5000000000000) + (q - ((43:ℝ)/8)) * ((-9902571592584383:ℝ)/250000000000))| ≤ ((53742405191351449:ℝ)/5000000000000) := by
  set t := q - ((43:ℝ)/8) with htd
  have hq : q = ((43:ℝ)/8) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/8) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece24_L3 piece24_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((43:ℝ)/8))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_03 q = ∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_03; ring
  have h12 : centralNum12_03 q = ∑ e ∈ Finset.range 14, ([((12899378677775836296717:ℝ)/240518168576), ((12175978824747748262817:ℝ)/240518168576), ((-7133769252885451959:ℝ)/117440512), ((-271234104757765885089:ℝ)/1879048192), ((-33391886725849545:ℝ)/262144), ((-3972061846024204941:ℝ)/58720256), ((-5588265169778031:ℝ)/229376), ((-1431746881073379:ℝ)/229376), ((-16595777495439:ℝ)/14336), ((-2222411664105:ℝ)/14336), ((-820991943:ℝ)/56), ((-14896143:ℝ)/16), ((-249804:ℝ)/7), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_03; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0) 0 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((12899378677775836296717:ℝ)/240518168576), ((12175978824747748262817:ℝ)/240518168576), ((-7133769252885451959:ℝ)/117440512), ((-271234104757765885089:ℝ)/1879048192), ((-33391886725849545:ℝ)/262144), ((-3972061846024204941:ℝ)/58720256), ((-5588265169778031:ℝ)/229376), ((-1431746881073379:ℝ)/229376), ((-16595777495439:ℝ)/14336), ((-2222411664105:ℝ)/14336), ((-820991943:ℝ)/56), ((-14896143:ℝ)/16), ((-249804:ℝ)/7), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((12899378677775836296717:ℝ)/240518168576), ((12175978824747748262817:ℝ)/240518168576), ((-7133769252885451959:ℝ)/117440512), ((-271234104757765885089:ℝ)/1879048192), ((-33391886725849545:ℝ)/262144), ((-3972061846024204941:ℝ)/58720256), ((-5588265169778031:ℝ)/229376), ((-1431746881073379:ℝ)/229376), ((-16595777495439:ℝ)/14336), ((-2222411664105:ℝ)/14336), ((-820991943:ℝ)/56), ((-14896143:ℝ)/16), ((-249804:ℝ)/7), ((-4374:ℝ)/7)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 2, ([(0:ℝ), (0:ℝ)] : List ℝ).getD e 0 * t^e) - ((0:ℝ) + (0:ℝ)*t)| ≤ (0:ℝ) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((12899378677775836296717:ℝ)/240518168576), ((12175978824747748262817:ℝ)/240518168576), ((-7133769252885451959:ℝ)/117440512), ((-271234104757765885089:ℝ)/1879048192), ((-33391886725849545:ℝ)/262144), ((-3972061846024204941:ℝ)/58720256), ((-5588265169778031:ℝ)/229376), ((-1431746881073379:ℝ)/229376), ((-16595777495439:ℝ)/14336), ((-2222411664105:ℝ)/14336), ((-820991943:ℝ)/56), ((-14896143:ℝ)/16), ((-249804:ℝ)/7), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((12899378677775836296717:ℝ)/240518168576) - ((12175978824747748262817:ℝ)/240518168576)*t| ≤ ((2432708147601024168969:ℝ)/1924145348608) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((12899378677775836296717:ℝ)/240518168576), ((12175978824747748262817:ℝ)/240518168576), ((-7133769252885451959:ℝ)/117440512), ((-271234104757765885089:ℝ)/1879048192), ((-33391886725849545:ℝ)/262144), ((-3972061846024204941:ℝ)/58720256), ((-5588265169778031:ℝ)/229376), ((-1431746881073379:ℝ)/229376), ((-16595777495439:ℝ)/14336), ((-2222411664105:ℝ)/14336), ((-820991943:ℝ)/56), ((-14896143:ℝ)/16), ((-249804:ℝ)/7), ((-4374:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((58901858197277731402761:ℝ)/962072674304) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((261217685273827:ℝ)/4194304) - ((59376563119257:ℝ)/524288)*t| ≤ ((1586557175713:ℝ)/1048576) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((11:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-812160:ℝ), (8985600:ℝ), (-32225280:ℝ), (52019200:ℝ), ((-305233920:ℝ)/7), ((135528448:ℝ)/7), ((-25165824:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_03 q| ≤ ((262736687504541965:ℝ)/7) := by
    rw [centralNum13_03_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((11:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-833220:ℝ), (6469740:ℝ), ((-68603955:ℝ)/4), ((104396875:ℝ)/4), ((-1001334375:ℝ)/56), ((125828125:ℝ)/28), ((-2343750:ℝ)/7)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_03 q| ≤ ((463966417172240492785:ℝ)/57344) := by
    rw [centralNum23_03_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((12586602998062478850617801581:ℝ)/1250000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece24_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece24_E11 h0) m23'
  have c5 := scaled_affine (X := ((3311168209:ℝ)/7812500000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := (0:ℝ) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((12899378677775836296717:ℝ)/240518168576) + ((261217685273827:ℝ)/4194304)*((3311168209:ℝ)/7812500000000) - ((345029123397448117:ℝ)/5000000000000)) (β := (0:ℝ) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((12175978824747748262817:ℝ)/240518168576) - 3*((12899378677775836296717:ℝ)/240518168576)) + ((59376563119257:ℝ)/524288)*((3311168209:ℝ)/7812500000000) - ((-9902571592584383:ℝ)/250000000000)) ht
  have hW : pieceW q pieceX_24 0 3 = centralNum11_03 q + 8*(Real.exp (-(3*((43:ℝ)/8)))*Real.exp (-3*t))*centralNum12_03 q + 18*Real.exp (-8*q)*centralNum13_03 q + 72*Real.exp (-11*q)*centralNum23_03 q + 8*q^7*(2*q-3)^2*((3311168209:ℝ)/7812500000000) + (0:ℝ) := by
    rw [pieceW_03, pieceX_24, sym4_03, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((21485405941696515889886664965020899813336567827394298703187209:ℝ)/2595595464718039624208644845773428082354420147193840614039552000000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : ((0:ℝ) + (0:ℝ)*t) + (8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((12899378677775836296717:ℝ)/240518168576) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((12175978824747748262817:ℝ)/240518168576) - 3*((12899378677775836296717:ℝ)/240518168576))*t) + (((261217685273827:ℝ)/4194304) + ((59376563119257:ℝ)/524288)*t)*((3311168209:ℝ)/7812500000000) - (((345029123397448117:ℝ)/5000000000000) + t * ((-9902571592584383:ℝ)/250000000000)) = ((0:ℝ) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((12899378677775836296717:ℝ)/240518168576) + ((261217685273827:ℝ)/4194304)*((3311168209:ℝ)/7812500000000) - ((345029123397448117:ℝ)/5000000000000)) + t*((0:ℝ) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((12175978824747748262817:ℝ)/240518168576) - 3*((12899378677775836296717:ℝ)/240518168576)) + ((59376563119257:ℝ)/524288)*((3311168209:ℝ)/7812500000000) - ((-9902571592584383:ℝ)/250000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece24_e11 {q : ℝ} (h0 : ((21:ℝ)/4) ≤ q) (h1 : q ≤ ((11:ℝ)/2)) :
    |pieceW q pieceX_24 1 1 - (((718999580228358967:ℝ)/100000000000) + (q - ((43:ℝ)/8)) * ((429677594645886993:ℝ)/50000000000))| ≤ ((202078044238842161:ℝ)/100000000000) := by
  set t := q - ((43:ℝ)/8) with htd
  have hq : q = ((43:ℝ)/8) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/8) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece24_L3 piece24_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((43:ℝ)/8))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_11 q = ∑ e ∈ Finset.range 10, ([((295770255699661:ℝ)/6291456), ((21222285839923:ℝ)/262144), ((512529551915:ℝ)/8192), ((29144801483:ℝ)/1024), ((2148421513:ℝ)/256), ((53173757:ℝ)/32), ((441399:ℝ)/2), (18940:ℝ), (952:ℝ), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_11; ring
  have h12 : centralNum12_11 q = ∑ e ∈ Finset.range 13, ([((-77196131096597753423:ℝ)/1610612736), ((-89930446106619065143:ℝ)/536870912), ((-16237550601890633315:ℝ)/67108864), ((-1676400154134404033:ℝ)/8388608), ((-112550175827984645:ℝ)/1048576), ((-2617989188418515:ℝ)/65536), ((-87129893400543:ℝ)/8192), ((-2099507729969:ℝ)/1024), ((-36462708793:ℝ)/128), ((-2676401305:ℝ)/96), ((-7308783:ℝ)/4), (-72090:ℝ), (-1296:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_11; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((295770255699661:ℝ)/6291456), ((21222285839923:ℝ)/262144), ((512529551915:ℝ)/8192), ((29144801483:ℝ)/1024), ((2148421513:ℝ)/256), ((53173757:ℝ)/32), ((441399:ℝ)/2), (18940:ℝ), (952:ℝ), ((64:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-77196131096597753423:ℝ)/1610612736), ((-89930446106619065143:ℝ)/536870912), ((-16237550601890633315:ℝ)/67108864), ((-1676400154134404033:ℝ)/8388608), ((-112550175827984645:ℝ)/1048576), ((-2617989188418515:ℝ)/65536), ((-87129893400543:ℝ)/8192), ((-2099507729969:ℝ)/1024), ((-36462708793:ℝ)/128), ((-2676401305:ℝ)/96), ((-7308783:ℝ)/4), (-72090:ℝ), (-1296:ℝ)] : List ℝ).getD e 0) 11 ht
  have m12 := abs_poly_le (fun e => ([((-77196131096597753423:ℝ)/1610612736), ((-89930446106619065143:ℝ)/536870912), ((-16237550601890633315:ℝ)/67108864), ((-1676400154134404033:ℝ)/8388608), ((-112550175827984645:ℝ)/1048576), ((-2617989188418515:ℝ)/65536), ((-87129893400543:ℝ)/8192), ((-2099507729969:ℝ)/1024), ((-36462708793:ℝ)/128), ((-2676401305:ℝ)/96), ((-7308783:ℝ)/4), (-72090:ℝ), (-1296:ℝ)] : List ℝ).getD e 0) 13 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((295770255699661:ℝ)/6291456), ((21222285839923:ℝ)/262144), ((512529551915:ℝ)/8192), ((29144801483:ℝ)/1024), ((2148421513:ℝ)/256), ((53173757:ℝ)/32), ((441399:ℝ)/2), (18940:ℝ), (952:ℝ), ((64:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((295770255699661:ℝ)/6291456) + ((21222285839923:ℝ)/262144)*t)| ≤ ((3256653583181:ℝ)/3145728) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 13, ([((-77196131096597753423:ℝ)/1610612736), ((-89930446106619065143:ℝ)/536870912), ((-16237550601890633315:ℝ)/67108864), ((-1676400154134404033:ℝ)/8388608), ((-112550175827984645:ℝ)/1048576), ((-2617989188418515:ℝ)/65536), ((-87129893400543:ℝ)/8192), ((-2099507729969:ℝ)/1024), ((-36462708793:ℝ)/128), ((-2676401305:ℝ)/96), ((-7308783:ℝ)/4), (-72090:ℝ), (-1296:ℝ)] : List ℝ).getD e 0 * t^e) - ((-77196131096597753423:ℝ)/1610612736) - ((-89930446106619065143:ℝ)/536870912)*t| ≤ ((54095746328571048931:ℝ)/12884901888) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 13, ([((-77196131096597753423:ℝ)/1610612736), ((-89930446106619065143:ℝ)/536870912), ((-16237550601890633315:ℝ)/67108864), ((-1676400154134404033:ℝ)/8388608), ((-112550175827984645:ℝ)/1048576), ((-2617989188418515:ℝ)/65536), ((-87129893400543:ℝ)/8192), ((-2099507729969:ℝ)/1024), ((-36462708793:ℝ)/128), ((-2676401305:ℝ)/96), ((-7308783:ℝ)/4), (-72090:ℝ), (-1296:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((7014394800523:ℝ)/96) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((261217685273827:ℝ)/4194304) - ((59376563119257:ℝ)/524288)*t| ≤ ((1586557175713:ℝ)/1048576) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((11:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-3444:ℝ), (162624:ℝ), (-1531216:ℝ), (4800960:ℝ), (-6350848:ℝ), ((12025856:ℝ)/3), (-1048576:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m13' : |centralNum13_11 q| ≤ ((18554025565010969:ℝ)/12) := by
    rw [centralNum13_11_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((11:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-4074:ℝ), (159906:ℝ), (-1104799:ℝ), (2801499:ℝ), (-3931375:ℝ), ((5896250:ℝ)/3), (-250000:ℝ)] : List ℝ).getD e 0) 13 hq1'
  have m23' : |centralNum23_11 q| ≤ ((889025380501080889:ℝ)/1536) := by
    rw [centralNum23_11_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((12586602998062478850617801581:ℝ)/1250000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece24_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece24_E11 h0) m23'
  have c5 := scaled_affine (X := ((-319395341541:ℝ)/500000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1))| ≤ ((6823690349619936320000000000:ℝ)/70524822346156312444460040004987533) := by
    rw [abs_neg, tailWeight_1, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((11:ℝ)/2)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((11:ℝ)/2)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece24_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((4814744136400:ℝ)/531441)) ≤ ((11:ℝ)/2)^6*(8000*(2*((11:ℝ)/2)-3)^2*(1/((132704895456233735154909086813:ℝ)/100000))*((4814744136400:ℝ)/531441)) := by
          gcongr
      _ ≤ ((6823690349619936320000000000:ℝ)/70524822346156312444460040004987533) := by norm_num
  have c7 := affine_round (α := ((295770255699661:ℝ)/6291456) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((-77196131096597753423:ℝ)/1610612736) + ((261217685273827:ℝ)/4194304)*((-319395341541:ℝ)/500000000000) - ((718999580228358967:ℝ)/100000000000)) (β := ((21222285839923:ℝ)/262144) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((-89930446106619065143:ℝ)/536870912) - 3*((-77196131096597753423:ℝ)/1610612736)) + ((59376563119257:ℝ)/524288)*((-319395341541:ℝ)/500000000000) - ((429677594645886993:ℝ)/50000000000)) ht
  have hW : pieceW q pieceX_24 1 1 = centralNum11_11 q + 8*(Real.exp (-(3*((43:ℝ)/8)))*Real.exp (-3*t))*centralNum12_11 q + 18*Real.exp (-8*q)*centralNum13_11 q + 72*Real.exp (-11*q)*centralNum23_11 q + 8*q^7*(2*q-3)^2*((-319395341541:ℝ)/500000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 1)) := by
    rw [pieceW_11, pieceX_24, sym4_11, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((2097663183696160276435448964122925571971055911144416052478961783:ℝ)/498354329225863607848059810388498191812048668261217397895593984000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((295770255699661:ℝ)/6291456) + ((21222285839923:ℝ)/262144)*t) + (8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((-77196131096597753423:ℝ)/1610612736) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((-89930446106619065143:ℝ)/536870912) - 3*((-77196131096597753423:ℝ)/1610612736))*t) + (((261217685273827:ℝ)/4194304) + ((59376563119257:ℝ)/524288)*t)*((-319395341541:ℝ)/500000000000) - (((718999580228358967:ℝ)/100000000000) + t * ((429677594645886993:ℝ)/50000000000)) = (((295770255699661:ℝ)/6291456) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((-77196131096597753423:ℝ)/1610612736) + ((261217685273827:ℝ)/4194304)*((-319395341541:ℝ)/500000000000) - ((718999580228358967:ℝ)/100000000000)) + t*(((21222285839923:ℝ)/262144) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((-89930446106619065143:ℝ)/536870912) - 3*((-77196131096597753423:ℝ)/1610612736)) + ((59376563119257:ℝ)/524288)*((-319395341541:ℝ)/500000000000) - ((429677594645886993:ℝ)/50000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece24_e12 {q : ℝ} (h0 : ((21:ℝ)/4) ≤ q) (h1 : q ≤ ((11:ℝ)/2)) :
    |pieceW q pieceX_24 1 2 - (((-147316257674378249:ℝ)/1000000000000) + (q - ((43:ℝ)/8)) * ((40607773974804413:ℝ)/25000000000))| ≤ ((122260785221662961:ℝ)/1000000000000) := by
  set t := q - ((43:ℝ)/8) with htd
  have hq : q = ((43:ℝ)/8) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/8) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece24_L3 piece24_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((43:ℝ)/8))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_12 q = ∑ e ∈ Finset.range 9, ([((-16656791634115:ℝ)/6291456), ((-3675211075:ℝ)/1536), ((-10444437055:ℝ)/24576), ((238123465:ℝ)/768), ((147319075:ℝ)/768), ((287885:ℝ)/6), ((38525:ℝ)/6), ((1360:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_12; ring
  have h12 : centralNum12_12 q = ∑ e ∈ Finset.range 14, ([((24677578664515344039821:ℝ)/103079215104), ((50210729005685014823969:ℝ)/103079215104), ((37185020871678265379:ℝ)/100663296), ((60403830545720436511:ℝ)/805306368), ((-124948191533849935:ℝ)/1572864), ((-1952329431606476173:ℝ)/25165824), ((-3500406473407687:ℝ)/98304), ((-1030648335496483:ℝ)/98304), ((-13117904571439:ℝ)/6144), ((-627342325795:ℝ)/2048), ((-244580433:ℝ)/8), ((-32457699:ℝ)/16), (-80676:ℝ), (-1458:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_12; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-16656791634115:ℝ)/6291456), ((-3675211075:ℝ)/1536), ((-10444437055:ℝ)/24576), ((238123465:ℝ)/768), ((147319075:ℝ)/768), ((287885:ℝ)/6), ((38525:ℝ)/6), ((1360:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((24677578664515344039821:ℝ)/103079215104), ((50210729005685014823969:ℝ)/103079215104), ((37185020871678265379:ℝ)/100663296), ((60403830545720436511:ℝ)/805306368), ((-124948191533849935:ℝ)/1572864), ((-1952329431606476173:ℝ)/25165824), ((-3500406473407687:ℝ)/98304), ((-1030648335496483:ℝ)/98304), ((-13117904571439:ℝ)/6144), ((-627342325795:ℝ)/2048), ((-244580433:ℝ)/8), ((-32457699:ℝ)/16), (-80676:ℝ), (-1458:ℝ)] : List ℝ).getD e 0) 12 ht
  have m12 := abs_poly_le (fun e => ([((24677578664515344039821:ℝ)/103079215104), ((50210729005685014823969:ℝ)/103079215104), ((37185020871678265379:ℝ)/100663296), ((60403830545720436511:ℝ)/805306368), ((-124948191533849935:ℝ)/1572864), ((-1952329431606476173:ℝ)/25165824), ((-3500406473407687:ℝ)/98304), ((-1030648335496483:ℝ)/98304), ((-13117904571439:ℝ)/6144), ((-627342325795:ℝ)/2048), ((-244580433:ℝ)/8), ((-32457699:ℝ)/16), (-80676:ℝ), (-1458:ℝ)] : List ℝ).getD e 0) 14 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((-16656791634115:ℝ)/6291456), ((-3675211075:ℝ)/1536), ((-10444437055:ℝ)/24576), ((238123465:ℝ)/768), ((147319075:ℝ)/768), ((287885:ℝ)/6), ((38525:ℝ)/6), ((1360:ℝ)/3), ((40:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((-16656791634115:ℝ)/6291456) + ((-3675211075:ℝ)/1536)*t)| ≤ ((45891729595:ℝ)/6291456) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 14, ([((24677578664515344039821:ℝ)/103079215104), ((50210729005685014823969:ℝ)/103079215104), ((37185020871678265379:ℝ)/100663296), ((60403830545720436511:ℝ)/805306368), ((-124948191533849935:ℝ)/1572864), ((-1952329431606476173:ℝ)/25165824), ((-3500406473407687:ℝ)/98304), ((-1030648335496483:ℝ)/98304), ((-13117904571439:ℝ)/6144), ((-627342325795:ℝ)/2048), ((-244580433:ℝ)/8), ((-32457699:ℝ)/16), (-80676:ℝ), (-1458:ℝ)] : List ℝ).getD e 0 * t^e) - ((24677578664515344039821:ℝ)/103079215104) - ((50210729005685014823969:ℝ)/103079215104)*t| ≤ ((4898552273063628128261:ℝ)/824633720832) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 14, ([((24677578664515344039821:ℝ)/103079215104), ((50210729005685014823969:ℝ)/103079215104), ((37185020871678265379:ℝ)/100663296), ((60403830545720436511:ℝ)/805306368), ((-124948191533849935:ℝ)/1572864), ((-1952329431606476173:ℝ)/25165824), ((-3500406473407687:ℝ)/98304), ((-1030648335496483:ℝ)/98304), ((-13117904571439:ℝ)/6144), ((-627342325795:ℝ)/2048), ((-244580433:ℝ)/8), ((-32457699:ℝ)/16), (-80676:ℝ), (-1458:ℝ)] : List ℝ).getD e 0 * t^e)| ≤ ((126264955297435697635399:ℝ)/412316860416) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((261217685273827:ℝ)/4194304) - ((59376563119257:ℝ)/524288)*t| ≤ ((1586557175713:ℝ)/1048576) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((11:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (122790:ℝ), (-3586680:ℝ), (28529720:ℝ), (-90761600:ℝ), (137804800:ℝ), ((-332136448:ℝ)/3), ((141819904:ℝ)/3), (-8388608:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m13' : |centralNum13_12 q| ≤ ((2182306359185872711:ℝ)/24) := by
    rw [centralNum13_12_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((11:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (132555:ℝ), (-3252375:ℝ), ((39743695:ℝ)/2), ((-197111615:ℝ)/4), ((281947375:ℝ)/4), ((-1100234375:ℝ)/24), ((131828125:ℝ)/12), (-781250:ℝ)] : List ℝ).getD e 0) 14 hq1'
  have m23' : |centralNum23_12 q| ≤ ((494610494698995431185:ℝ)/24576) := by
    rw [centralNum23_12_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((12586602998062478850617801581:ℝ)/1250000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece24_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece24_E11 h0) m23'
  have c5 := scaled_affine (X := ((11590978213:ℝ)/312500000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-16656791634115:ℝ)/6291456) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((24677578664515344039821:ℝ)/103079215104) + ((261217685273827:ℝ)/4194304)*((11590978213:ℝ)/312500000000) - ((-147316257674378249:ℝ)/1000000000000)) (β := ((-3675211075:ℝ)/1536) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((50210729005685014823969:ℝ)/103079215104) - 3*((24677578664515344039821:ℝ)/103079215104)) + ((59376563119257:ℝ)/524288)*((11590978213:ℝ)/312500000000) - ((40607773974804413:ℝ)/25000000000)) ht
  have hW : pieceW q pieceX_24 1 2 = centralNum11_12 q + 8*(Real.exp (-(3*((43:ℝ)/8)))*Real.exp (-3*t))*centralNum12_12 q + 18*Real.exp (-8*q)*centralNum13_12 q + 72*Real.exp (-11*q)*centralNum23_12 q + 8*q^7*(2*q-3)^2*((11590978213:ℝ)/312500000000) + (0:ℝ) := by
    rw [pieceW_12, pieceX_24, sym4_12, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((130526868379374739074168300933911452989969542859313387113705143:ℝ)/124588582306465901962014952597124547953012167065304349473898496000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-16656791634115:ℝ)/6291456) + ((-3675211075:ℝ)/1536)*t) + (8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((24677578664515344039821:ℝ)/103079215104) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((50210729005685014823969:ℝ)/103079215104) - 3*((24677578664515344039821:ℝ)/103079215104))*t) + (((261217685273827:ℝ)/4194304) + ((59376563119257:ℝ)/524288)*t)*((11590978213:ℝ)/312500000000) - (((-147316257674378249:ℝ)/1000000000000) + t * ((40607773974804413:ℝ)/25000000000)) = (((-16656791634115:ℝ)/6291456) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((24677578664515344039821:ℝ)/103079215104) + ((261217685273827:ℝ)/4194304)*((11590978213:ℝ)/312500000000) - ((-147316257674378249:ℝ)/1000000000000)) + t*(((-3675211075:ℝ)/1536) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((50210729005685014823969:ℝ)/103079215104) - 3*((24677578664515344039821:ℝ)/103079215104)) + ((59376563119257:ℝ)/524288)*((11590978213:ℝ)/312500000000) - ((40607773974804413:ℝ)/25000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece24_e13 {q : ℝ} (h0 : ((21:ℝ)/4) ≤ q) (h1 : q ≤ ((11:ℝ)/2)) :
    |pieceW q pieceX_24 1 3 - (((-97777440834820871:ℝ)/500000000000) + (q - ((43:ℝ)/8)) * ((1646590377955971:ℝ)/1953125000))| ≤ ((29427537800508373:ℝ)/250000000000) := by
  set t := q - ((43:ℝ)/8) with htd
  have hq : q = ((43:ℝ)/8) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/8) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece24_L3 piece24_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((43:ℝ)/8))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_13 q = ∑ e ∈ Finset.range 7, ([((-94820445735:ℝ)/65536), ((-6615379935:ℝ)/4096), ((-769230225:ℝ)/1024), ((-5963025:ℝ)/32), ((-416025:ℝ)/16), (-1935:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_13; ring
  have h12 : centralNum12_13 q = ∑ e ∈ Finset.range 15, ([((394104559165460605976295:ℝ)/3848290697216), ((397718132858925727000263:ℝ)/549755813888), ((651439175552385101685507:ℝ)/481036337152), ((37914842082740745014439:ℝ)/30064771072), ((2594905654645979265813:ℝ)/3758096384), ((214034095237370038395:ℝ)/939524096), ((4410949320433212729:ℝ)/117440512), ((-9859056726371763:ℝ)/3670016), ((-214966841405901:ℝ)/65536), ((-215027903833641:ℝ)/229376), ((-4523450794875:ℝ)/28672), ((-30934114353:ℝ)/1792), ((-272193291:ℝ)/224), ((-2819043:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_13; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((-94820445735:ℝ)/65536), ((-6615379935:ℝ)/4096), ((-769230225:ℝ)/1024), ((-5963025:ℝ)/32), ((-416025:ℝ)/16), (-1935:ℝ), (-60:ℝ)] : List ℝ).getD e 0) 5 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((394104559165460605976295:ℝ)/3848290697216), ((397718132858925727000263:ℝ)/549755813888), ((651439175552385101685507:ℝ)/481036337152), ((37914842082740745014439:ℝ)/30064771072), ((2594905654645979265813:ℝ)/3758096384), ((214034095237370038395:ℝ)/939524096), ((4410949320433212729:ℝ)/117440512), ((-9859056726371763:ℝ)/3670016), ((-214966841405901:ℝ)/65536), ((-215027903833641:ℝ)/229376), ((-4523450794875:ℝ)/28672), ((-30934114353:ℝ)/1792), ((-272193291:ℝ)/224), ((-2819043:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((394104559165460605976295:ℝ)/3848290697216), ((397718132858925727000263:ℝ)/549755813888), ((651439175552385101685507:ℝ)/481036337152), ((37914842082740745014439:ℝ)/30064771072), ((2594905654645979265813:ℝ)/3758096384), ((214034095237370038395:ℝ)/939524096), ((4410949320433212729:ℝ)/117440512), ((-9859056726371763:ℝ)/3670016), ((-214966841405901:ℝ)/65536), ((-215027903833641:ℝ)/229376), ((-4523450794875:ℝ)/28672), ((-30934114353:ℝ)/1792), ((-272193291:ℝ)/224), ((-2819043:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 7, ([((-94820445735:ℝ)/65536), ((-6615379935:ℝ)/4096), ((-769230225:ℝ)/1024), ((-5963025:ℝ)/32), ((-416025:ℝ)/16), (-1935:ℝ), (-60:ℝ)] : List ℝ).getD e 0 * t^e) - (((-94820445735:ℝ)/65536) + ((-6615379935:ℝ)/4096)*t)| ≤ ((793502235:ℝ)/65536) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((394104559165460605976295:ℝ)/3848290697216), ((397718132858925727000263:ℝ)/549755813888), ((651439175552385101685507:ℝ)/481036337152), ((37914842082740745014439:ℝ)/30064771072), ((2594905654645979265813:ℝ)/3758096384), ((214034095237370038395:ℝ)/939524096), ((4410949320433212729:ℝ)/117440512), ((-9859056726371763:ℝ)/3670016), ((-214966841405901:ℝ)/65536), ((-215027903833641:ℝ)/229376), ((-4523450794875:ℝ)/28672), ((-30934114353:ℝ)/1792), ((-272193291:ℝ)/224), ((-2819043:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e) - ((394104559165460605976295:ℝ)/3848290697216) - ((397718132858925727000263:ℝ)/549755813888)*t| ≤ ((732677161746628588418823:ℝ)/30786325577728) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((394104559165460605976295:ℝ)/3848290697216), ((397718132858925727000263:ℝ)/549755813888), ((651439175552385101685507:ℝ)/481036337152), ((37914842082740745014439:ℝ)/30064771072), ((2594905654645979265813:ℝ)/3758096384), ((214034095237370038395:ℝ)/939524096), ((4410949320433212729:ℝ)/117440512), ((-9859056726371763:ℝ)/3670016), ((-214966841405901:ℝ)/65536), ((-215027903833641:ℝ)/229376), ((-4523450794875:ℝ)/28672), ((-30934114353:ℝ)/1792), ((-272193291:ℝ)/224), ((-2819043:ℝ)/56), ((-6561:ℝ)/7)] : List ℝ).getD e 0 * t^e)| ≤ ((416846285317674595326939:ℝ)/1924145348608) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((261217685273827:ℝ)/4194304) - ((59376563119257:ℝ)/524288)*t| ≤ ((1586557175713:ℝ)/1048576) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((11:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2325540:ℝ), (52589280:ℝ), (-375655200:ℝ), (1192958720:ℝ), (-1965096960:ℝ), ((12857851904:ℝ)/7), ((-21171273728:ℝ)/21), ((914358272:ℝ)/3), ((-268435456:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_13 q| ≤ ((1094423630457186407851:ℝ)/336) := by
    rw [centralNum13_13_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((11:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2399070:ℝ), (45666930:ℝ), (-251781675:ℝ), ((2452738385:ℝ)/4), ((-14104310625:ℝ)/16), ((74345740625:ℝ)/112), ((-74899765625:ℝ)/336), ((5161328125:ℝ)/168), ((-9765625:ℝ)/7)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_13 q| ≤ ((309969363155776651833605:ℝ)/688128) := by
    rw [centralNum23_13_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((12586602998062478850617801581:ℝ)/1250000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece24_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece24_E11 h0) m23'
  have c5 := scaled_affine (X := ((187851920419:ℝ)/10000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((-94820445735:ℝ)/65536) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((394104559165460605976295:ℝ)/3848290697216) + ((261217685273827:ℝ)/4194304)*((187851920419:ℝ)/10000000000000) - ((-97777440834820871:ℝ)/500000000000)) (β := ((-6615379935:ℝ)/4096) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((397718132858925727000263:ℝ)/549755813888) - 3*((394104559165460605976295:ℝ)/3848290697216)) + ((59376563119257:ℝ)/524288)*((187851920419:ℝ)/10000000000000) - ((1646590377955971:ℝ)/1953125000)) ht
  have hW : pieceW q pieceX_24 1 3 = centralNum11_13 q + 8*(Real.exp (-(3*((43:ℝ)/8)))*Real.exp (-3*t))*centralNum12_13 q + 18*Real.exp (-8*q)*centralNum13_13 q + 72*Real.exp (-11*q)*centralNum23_13 q + 8*q^7*(2*q-3)^2*((187851920419:ℝ)/10000000000000) + (0:ℝ) := by
    rw [pieceW_13, pieceX_24, sym4_13, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((1592396235835603192727495368009884105030169055451235687569953099:ℝ)/3322362194839090718987065402589987945413657788408115985970626560000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((-94820445735:ℝ)/65536) + ((-6615379935:ℝ)/4096)*t) + (8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((394104559165460605976295:ℝ)/3848290697216) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((397718132858925727000263:ℝ)/549755813888) - 3*((394104559165460605976295:ℝ)/3848290697216))*t) + (((261217685273827:ℝ)/4194304) + ((59376563119257:ℝ)/524288)*t)*((187851920419:ℝ)/10000000000000) - (((-97777440834820871:ℝ)/500000000000) + t * ((1646590377955971:ℝ)/1953125000)) = (((-94820445735:ℝ)/65536) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((394104559165460605976295:ℝ)/3848290697216) + ((261217685273827:ℝ)/4194304)*((187851920419:ℝ)/10000000000000) - ((-97777440834820871:ℝ)/500000000000)) + t*(((-6615379935:ℝ)/4096) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((397718132858925727000263:ℝ)/549755813888) - 3*((394104559165460605976295:ℝ)/3848290697216)) + ((59376563119257:ℝ)/524288)*((187851920419:ℝ)/10000000000000) - ((1646590377955971:ℝ)/1953125000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece24_e22 {q : ℝ} (h0 : ((21:ℝ)/4) ≤ q) (h1 : q ≤ ((11:ℝ)/2)) :
    |pieceW q pieceX_24 2 2 - (((767706453251836157:ℝ)/100000000000) + (q - ((43:ℝ)/8)) * ((25794232829947229:ℝ)/2000000000))| ≤ ((101051249118148067:ℝ)/50000000000) := by
  set t := q - ((43:ℝ)/8) with htd
  have hq : q = ((43:ℝ)/8) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/8) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece24_L3 piece24_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((43:ℝ)/8))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_22 q = ∑ e ∈ Finset.range 10, ([((1120990095787835:ℝ)/25165824), ((248971738382285:ℝ)/3145728), ((6177231566795:ℝ)/98304), ((120075751835:ℝ)/4096), ((27239933045:ℝ)/3072), ((692891435:ℝ)/384), ((1976085:ℝ)/8), ((65765:ℝ)/3), ((3430:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_22; ring
  have h12 : centralNum12_22 q = ∑ e ∈ Finset.range 15, ([((-341192450552571251340235:ℝ)/6597069766656), ((4934350323518132828595667:ℝ)/6597069766656), ((1567664181327546077857225:ℝ)/824633720832), ((34632232424519648913351:ℝ)/17179869184), ((7797509791347335083999:ℝ)/6442450944), ((712616448515283913265:ℝ)/1610612736), ((6114905277535905721:ℝ)/67108864), ((22594738442390215:ℝ)/6291456), ((-3098125155351089:ℝ)/786432), ((-538620577276283:ℝ)/393216), ((-4063769929275:ℝ)/16384), ((-28965888657:ℝ)/1024), ((-262128555:ℝ)/128), ((-2772387:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_22; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((1120990095787835:ℝ)/25165824), ((248971738382285:ℝ)/3145728), ((6177231566795:ℝ)/98304), ((120075751835:ℝ)/4096), ((27239933045:ℝ)/3072), ((692891435:ℝ)/384), ((1976085:ℝ)/8), ((65765:ℝ)/3), ((3430:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-341192450552571251340235:ℝ)/6597069766656), ((4934350323518132828595667:ℝ)/6597069766656), ((1567664181327546077857225:ℝ)/824633720832), ((34632232424519648913351:ℝ)/17179869184), ((7797509791347335083999:ℝ)/6442450944), ((712616448515283913265:ℝ)/1610612736), ((6114905277535905721:ℝ)/67108864), ((22594738442390215:ℝ)/6291456), ((-3098125155351089:ℝ)/786432), ((-538620577276283:ℝ)/393216), ((-4063769929275:ℝ)/16384), ((-28965888657:ℝ)/1024), ((-262128555:ℝ)/128), ((-2772387:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 13 ht
  have m12 := abs_poly_le (fun e => ([((-341192450552571251340235:ℝ)/6597069766656), ((4934350323518132828595667:ℝ)/6597069766656), ((1567664181327546077857225:ℝ)/824633720832), ((34632232424519648913351:ℝ)/17179869184), ((7797509791347335083999:ℝ)/6442450944), ((712616448515283913265:ℝ)/1610612736), ((6114905277535905721:ℝ)/67108864), ((22594738442390215:ℝ)/6291456), ((-3098125155351089:ℝ)/786432), ((-538620577276283:ℝ)/393216), ((-4063769929275:ℝ)/16384), ((-28965888657:ℝ)/1024), ((-262128555:ℝ)/128), ((-2772387:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0) 15 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((1120990095787835:ℝ)/25165824), ((248971738382285:ℝ)/3145728), ((6177231566795:ℝ)/98304), ((120075751835:ℝ)/4096), ((27239933045:ℝ)/3072), ((692891435:ℝ)/384), ((1976085:ℝ)/8), ((65765:ℝ)/3), ((3430:ℝ)/3), ((80:ℝ)/3)] : List ℝ).getD e 0 * t^e) - (((1120990095787835:ℝ)/25165824) + ((248971738382285:ℝ)/3145728)*t)| ≤ ((3275715614495:ℝ)/3145728) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 15, ([((-341192450552571251340235:ℝ)/6597069766656), ((4934350323518132828595667:ℝ)/6597069766656), ((1567664181327546077857225:ℝ)/824633720832), ((34632232424519648913351:ℝ)/17179869184), ((7797509791347335083999:ℝ)/6442450944), ((712616448515283913265:ℝ)/1610612736), ((6114905277535905721:ℝ)/67108864), ((22594738442390215:ℝ)/6291456), ((-3098125155351089:ℝ)/786432), ((-538620577276283:ℝ)/393216), ((-4063769929275:ℝ)/16384), ((-28965888657:ℝ)/1024), ((-262128555:ℝ)/128), ((-2772387:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e) - ((-341192450552571251340235:ℝ)/6597069766656) - ((4934350323518132828595667:ℝ)/6597069766656)*t| ≤ ((1791783659944148187605197:ℝ)/52776558133248) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 15, ([((-341192450552571251340235:ℝ)/6597069766656), ((4934350323518132828595667:ℝ)/6597069766656), ((1567664181327546077857225:ℝ)/824633720832), ((34632232424519648913351:ℝ)/17179869184), ((7797509791347335083999:ℝ)/6442450944), ((712616448515283913265:ℝ)/1610612736), ((6114905277535905721:ℝ)/67108864), ((22594738442390215:ℝ)/6291456), ((-3098125155351089:ℝ)/786432), ((-538620577276283:ℝ)/393216), ((-4063769929275:ℝ)/16384), ((-28965888657:ℝ)/1024), ((-262128555:ℝ)/128), ((-2772387:ℝ)/32), ((-6561:ℝ)/4)] : List ℝ).getD e 0 * t^e)| ≤ ((1181959198485356378365343:ℝ)/6597069766656) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((261217685273827:ℝ)/4194304) - ((59376563119257:ℝ)/524288)*t| ≤ ((1586557175713:ℝ)/1048576) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((11:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82125:ℝ), (-6663750:ℝ), (115666200:ℝ), (-750437000:ℝ), (2277262000:ℝ), (-3656824320:ℝ), (3359621120:ℝ), (-1817706496:ℝ), ((1625292800:ℝ)/3), (-67108864:ℝ)] : List ℝ).getD e 0) 15 hq1'
  have m13' : |centralNum13_22 q| ≤ ((278549404720989846521:ℝ)/48) := by
    rw [centralNum13_22_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((11:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((178425:ℝ)/2), ((-13176075:ℝ)/2), ((777815145:ℝ)/8), ((-3968389015:ℝ)/8), ((9393350195:ℝ)/8), ((-26366634375:ℝ)/16), ((77851609375:ℝ)/64), ((-25714921875:ℝ)/64), ((5236328125:ℝ)/96), ((-9765625:ℝ)/4)] : List ℝ).getD e 0) 15 hq1'
  have m23' : |centralNum23_22 q| ≤ ((319038377909772933662305:ℝ)/393216) := by
    rw [centralNum23_22_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((12586602998062478850617801581:ℝ)/1250000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece24_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece24_E11 h0) m23'
  have c5 := scaled_affine (X := ((-591305273179:ℝ)/1000000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2))| ≤ ((3642940166947465643600000000000:ℝ)/634723401115406812000140360044887797) := by
    rw [abs_neg, tailWeight_2, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((11:ℝ)/2)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((11:ℝ)/2)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece24_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((2570430941234500:ℝ)/4782969)) ≤ ((11:ℝ)/2)^6*(8000*(2*((11:ℝ)/2)-3)^2*(1/((132704895456233735154909086813:ℝ)/100000))*((2570430941234500:ℝ)/4782969)) := by
          gcongr
      _ ≤ ((3642940166947465643600000000000:ℝ)/634723401115406812000140360044887797) := by norm_num
  have c7 := affine_round (α := ((1120990095787835:ℝ)/25165824) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((-341192450552571251340235:ℝ)/6597069766656) + ((261217685273827:ℝ)/4194304)*((-591305273179:ℝ)/1000000000000) - ((767706453251836157:ℝ)/100000000000)) (β := ((248971738382285:ℝ)/3145728) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((4934350323518132828595667:ℝ)/6597069766656) - 3*((-341192450552571251340235:ℝ)/6597069766656)) + ((59376563119257:ℝ)/524288)*((-591305273179:ℝ)/1000000000000) - ((25794232829947229:ℝ)/2000000000)) ht
  have hW : pieceW q pieceX_24 2 2 = centralNum11_22 q + 8*(Real.exp (-(3*((43:ℝ)/8)))*Real.exp (-3*t))*centralNum12_22 q + 18*Real.exp (-8*q)*centralNum13_22 q + 72*Real.exp (-11*q)*centralNum23_22 q + 8*q^7*(2*q-3)^2*((-591305273179:ℝ)/1000000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 2)) := by
    rw [pieceW_22, pieceX_24, sym4_22, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((68183069151380511793310436534066341316800474815911141532672511:ℝ)/13653543266462016653371501654479402515398593650992257476591616000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((1120990095787835:ℝ)/25165824) + ((248971738382285:ℝ)/3145728)*t) + (8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((-341192450552571251340235:ℝ)/6597069766656) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((4934350323518132828595667:ℝ)/6597069766656) - 3*((-341192450552571251340235:ℝ)/6597069766656))*t) + (((261217685273827:ℝ)/4194304) + ((59376563119257:ℝ)/524288)*t)*((-591305273179:ℝ)/1000000000000) - (((767706453251836157:ℝ)/100000000000) + t * ((25794232829947229:ℝ)/2000000000)) = (((1120990095787835:ℝ)/25165824) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((-341192450552571251340235:ℝ)/6597069766656) + ((261217685273827:ℝ)/4194304)*((-591305273179:ℝ)/1000000000000) - ((767706453251836157:ℝ)/100000000000)) + t*(((248971738382285:ℝ)/3145728) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((4934350323518132828595667:ℝ)/6597069766656) - 3*((-341192450552571251340235:ℝ)/6597069766656)) + ((59376563119257:ℝ)/524288)*((-591305273179:ℝ)/1000000000000) - ((25794232829947229:ℝ)/2000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece24_e23 {q : ℝ} (h0 : ((21:ℝ)/4) ≤ q) (h1 : q ≤ ((11:ℝ)/2)) :
    |pieceW q pieceX_24 2 3 - (((34802495815237129:ℝ)/40000000000) + (q - ((43:ℝ)/8)) * ((223736070728410907:ℝ)/100000000000))| ≤ ((56886004868947983:ℝ)/62500000000) := by
  set t := q - ((43:ℝ)/8) with htd
  have hq : q = ((43:ℝ)/8) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/8) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece24_L3 piece24_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((43:ℝ)/8))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_23 q = ∑ e ∈ Finset.range 9, ([((16800859908255:ℝ)/2097152), ((1676186848285:ℝ)/131072), ((152851014895:ℝ)/16384), ((8240817345:ℝ)/2048), ((142055875:ℝ)/128), ((6349655:ℝ)/32), ((89145:ℝ)/4), (1430:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_23; ring
  have h12 : centralNum12_23 q = ∑ e ∈ Finset.range 16, ([((-438271416032842429409714397:ℝ)/246290604621824), ((-1356937871294722160983147517:ℝ)/246290604621824), ((-101885166611082452916143155:ℝ)/15393162788864), ((-14841508586953208221985643:ℝ)/3848290697216), ((-97137651507962336685481:ℝ)/120259084288), ((22488010049429579104595:ℝ)/60129542144), ((1312768291408732364691:ℝ)/3758096384), ((122370907019850896125:ℝ)/939524096), ((25380524777094671:ℝ)/917504), ((43954823880463809:ℝ)/14680064), ((-57848104019709:ℝ)/917504), ((-17558117637993:ℝ)/229376), ((-90519311565:ℝ)/7168), ((-3920024727:ℝ)/3584), ((-11567043:ℝ)/224), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_23; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((16800859908255:ℝ)/2097152), ((1676186848285:ℝ)/131072), ((152851014895:ℝ)/16384), ((8240817345:ℝ)/2048), ((142055875:ℝ)/128), ((6349655:ℝ)/32), ((89145:ℝ)/4), (1430:ℝ), (40:ℝ)] : List ℝ).getD e 0) 7 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((-438271416032842429409714397:ℝ)/246290604621824), ((-1356937871294722160983147517:ℝ)/246290604621824), ((-101885166611082452916143155:ℝ)/15393162788864), ((-14841508586953208221985643:ℝ)/3848290697216), ((-97137651507962336685481:ℝ)/120259084288), ((22488010049429579104595:ℝ)/60129542144), ((1312768291408732364691:ℝ)/3758096384), ((122370907019850896125:ℝ)/939524096), ((25380524777094671:ℝ)/917504), ((43954823880463809:ℝ)/14680064), ((-57848104019709:ℝ)/917504), ((-17558117637993:ℝ)/229376), ((-90519311565:ℝ)/7168), ((-3920024727:ℝ)/3584), ((-11567043:ℝ)/224), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 14 ht
  have m12 := abs_poly_le (fun e => ([((-438271416032842429409714397:ℝ)/246290604621824), ((-1356937871294722160983147517:ℝ)/246290604621824), ((-101885166611082452916143155:ℝ)/15393162788864), ((-14841508586953208221985643:ℝ)/3848290697216), ((-97137651507962336685481:ℝ)/120259084288), ((22488010049429579104595:ℝ)/60129542144), ((1312768291408732364691:ℝ)/3758096384), ((122370907019850896125:ℝ)/939524096), ((25380524777094671:ℝ)/917504), ((43954823880463809:ℝ)/14680064), ((-57848104019709:ℝ)/917504), ((-17558117637993:ℝ)/229376), ((-90519311565:ℝ)/7168), ((-3920024727:ℝ)/3584), ((-11567043:ℝ)/224), ((-59049:ℝ)/56)] : List ℝ).getD e 0) 16 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 9, ([((16800859908255:ℝ)/2097152), ((1676186848285:ℝ)/131072), ((152851014895:ℝ)/16384), ((8240817345:ℝ)/2048), ((142055875:ℝ)/128), ((6349655:ℝ)/32), ((89145:ℝ)/4), (1430:ℝ), (40:ℝ)] : List ℝ).getD e 0 * t^e) - (((16800859908255:ℝ)/2097152) + ((1676186848285:ℝ)/131072)*t)| ≤ ((322764767015:ℝ)/2097152) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 16, ([((-438271416032842429409714397:ℝ)/246290604621824), ((-1356937871294722160983147517:ℝ)/246290604621824), ((-101885166611082452916143155:ℝ)/15393162788864), ((-14841508586953208221985643:ℝ)/3848290697216), ((-97137651507962336685481:ℝ)/120259084288), ((22488010049429579104595:ℝ)/60129542144), ((1312768291408732364691:ℝ)/3758096384), ((122370907019850896125:ℝ)/939524096), ((25380524777094671:ℝ)/917504), ((43954823880463809:ℝ)/14680064), ((-57848104019709:ℝ)/917504), ((-17558117637993:ℝ)/229376), ((-90519311565:ℝ)/7168), ((-3920024727:ℝ)/3584), ((-11567043:ℝ)/224), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e) - ((-438271416032842429409714397:ℝ)/246290604621824) - ((-1356937871294722160983147517:ℝ)/246290604621824)*t| ≤ ((219025631625484845990467209:ℝ)/1970324836974592) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 16, ([((-438271416032842429409714397:ℝ)/246290604621824), ((-1356937871294722160983147517:ℝ)/246290604621824), ((-101885166611082452916143155:ℝ)/15393162788864), ((-14841508586953208221985643:ℝ)/3848290697216), ((-97137651507962336685481:ℝ)/120259084288), ((22488010049429579104595:ℝ)/60129542144), ((1312768291408732364691:ℝ)/3758096384), ((122370907019850896125:ℝ)/939524096), ((25380524777094671:ℝ)/917504), ((43954823880463809:ℝ)/14680064), ((-57848104019709:ℝ)/917504), ((-17558117637993:ℝ)/229376), ((-90519311565:ℝ)/7168), ((-3920024727:ℝ)/3584), ((-11567043:ℝ)/224), ((-59049:ℝ)/56)] : List ℝ).getD e 0 * t^e)| ≤ ((2541067415591473221125664951:ℝ)/985162418487296) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((261217685273827:ℝ)/4194304) - ((59376563119257:ℝ)/524288)*t| ≤ ((1586557175713:ℝ)/1048576) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((11:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-7627725:ℝ)/2), (173988600:ℝ), (-2299614450:ℝ), (13088188200:ℝ), (-38221499200:ℝ), (63366115840:ℝ), ((-445610508288:ℝ)/7), ((841540698112:ℝ)/21), ((-326820167680:ℝ)/21), ((10133438464:ℝ)/3), ((-2147483648:ℝ)/7)] : List ℝ).getD e 0) 16 hq1'
  have m13' : |centralNum13_23 q| ≤ ((25127264545224755926815:ℝ)/112) := by
    rw [centralNum13_23_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((11:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-15801525:ℝ)/4), ((655493865:ℝ)/4), ((-7334421225:ℝ)/4), ((16442962485:ℝ)/2), ((-598626108395:ℝ)/32), ((414013307125:ℝ)/16), ((-4611984703125:ℝ)/224), ((399923828125:ℝ)/48), ((-4353201171875:ℝ)/2688), ((189736328125:ℝ)/1344), ((-244140625:ℝ)/56)] : List ℝ).getD e 0) 16 hq1'
  have m23' : |centralNum23_23 q| ≤ ((75799639932239403878910575:ℝ)/3670016) := by
    rw [centralNum23_23_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((12586602998062478850617801581:ℝ)/1250000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece24_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece24_E11 h0) m23'
  have c5 := scaled_affine (X := ((-459818084627:ℝ)/5000000000000)) bD'
  have c6 : |(0:ℝ)| ≤ 0 := by simp
  have c7 := affine_round (α := ((16800859908255:ℝ)/2097152) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((-438271416032842429409714397:ℝ)/246290604621824) + ((261217685273827:ℝ)/4194304)*((-459818084627:ℝ)/5000000000000) - ((34802495815237129:ℝ)/40000000000)) (β := ((1676186848285:ℝ)/131072) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((-1356937871294722160983147517:ℝ)/246290604621824) - 3*((-438271416032842429409714397:ℝ)/246290604621824)) + ((59376563119257:ℝ)/524288)*((-459818084627:ℝ)/5000000000000) - ((223736070728410907:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_24 2 3 = centralNum11_23 q + 8*(Real.exp (-(3*((43:ℝ)/8)))*Real.exp (-3*t))*centralNum12_23 q + 18*Real.exp (-8*q)*centralNum13_23 q + 72*Real.exp (-11*q)*centralNum23_23 q + 8*q^7*(2*q-3)^2*((-459818084627:ℝ)/5000000000000) + (0:ℝ) := by
    rw [pieceW_23, pieceX_24, sym4_23, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((453316572568863959321373232269120827689121882787311250908927227:ℝ)/1661181097419545359493532701294993972706828894204057992985313280000000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((16800859908255:ℝ)/2097152) + ((1676186848285:ℝ)/131072)*t) + (8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((-438271416032842429409714397:ℝ)/246290604621824) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((-1356937871294722160983147517:ℝ)/246290604621824) - 3*((-438271416032842429409714397:ℝ)/246290604621824))*t) + (((261217685273827:ℝ)/4194304) + ((59376563119257:ℝ)/524288)*t)*((-459818084627:ℝ)/5000000000000) - (((34802495815237129:ℝ)/40000000000) + t * ((223736070728410907:ℝ)/100000000000)) = (((16800859908255:ℝ)/2097152) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((-438271416032842429409714397:ℝ)/246290604621824) + ((261217685273827:ℝ)/4194304)*((-459818084627:ℝ)/5000000000000) - ((34802495815237129:ℝ)/40000000000)) + t*(((1676186848285:ℝ)/131072) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((-1356937871294722160983147517:ℝ)/246290604621824) - 3*((-438271416032842429409714397:ℝ)/246290604621824)) + ((59376563119257:ℝ)/524288)*((-459818084627:ℝ)/5000000000000) - ((223736070728410907:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece24_e33 {q : ℝ} (h0 : ((21:ℝ)/4) ≤ q) (h1 : q ≤ ((11:ℝ)/2)) :
    |pieceW q pieceX_24 3 3 - (((565409150078080577:ℝ)/100000000000) + (q - ((43:ℝ)/8)) * ((189278883917404879:ℝ)/100000000000))| ≤ ((245777954776708999:ℝ)/100000000000) := by
  set t := q - ((43:ℝ)/8) with htd
  have hq : q = ((43:ℝ)/8) + t := by rw [htd]; ring
  have ht : |t| ≤ ((1:ℝ)/8) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE3 := exp_neg_bounds (by norm_num) piece24_L3 piece24_U3
  have hexp3 : Real.exp (-3*q) = Real.exp (-(3*((43:ℝ)/8))) * Real.exp (-3*t) := by
    rw [← Real.exp_add, hq]; ring_nf
  have h11 : centralNum11_33 q = ∑ e ∈ Finset.range 10, ([((567630589854065:ℝ)/29360128), ((143728200041505:ℝ)/3670016), ((1971101516235:ℝ)/57344), ((17778075015:ℝ)/1024), ((2872798935:ℝ)/512), ((77534895:ℝ)/64), (175605:ℝ), ((115680:ℝ)/7), ((6420:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum11_33; ring
  have h12 : centralNum12_33 q = ∑ e ∈ Finset.range 17, ([((155283121303892901331812949267:ℝ)/27584547717644288), ((317880137101712595998346338649:ℝ)/27584547717644288), ((21652646793883675961231248617:ℝ)/3448068464705536), ((-223678574968318432001090841:ℝ)/61572651155456), ((-53371179711031609761224073:ℝ)/7696581394432), ((-4197639560276508666701205:ℝ)/962072674304), ((-177177010304242611561189:ℝ)/120259084288), ((-25343105204624777560587:ℝ)/105226698752), ((155916864613075752597:ℝ)/13153337344), ((25733811217477215851:ℝ)/1644167168), ((108365549213385549:ℝ)/29360128), ((1526576411899125:ℝ)/3670016), ((4860745860069:ℝ)/458752), ((-197152882119:ℝ)/57344), ((-24807724929:ℝ)/50176), ((-182402361:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    unfold centralNum12_33; ring
  have hD : 8*q^7*(2*q-3)^2 = ∑ e ∈ Finset.range 10, ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e := by
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    ring
  have b11 := abs_poly_sub_affine_le (fun e => ([((567630589854065:ℝ)/29360128), ((143728200041505:ℝ)/3670016), ((1971101516235:ℝ)/57344), ((17778075015:ℝ)/1024), ((2872798935:ℝ)/512), ((77534895:ℝ)/64), (175605:ℝ), ((115680:ℝ)/7), ((6420:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0) 8 ht
  have b12 := abs_poly_sub_affine_le (fun e => ([((155283121303892901331812949267:ℝ)/27584547717644288), ((317880137101712595998346338649:ℝ)/27584547717644288), ((21652646793883675961231248617:ℝ)/3448068464705536), ((-223678574968318432001090841:ℝ)/61572651155456), ((-53371179711031609761224073:ℝ)/7696581394432), ((-4197639560276508666701205:ℝ)/962072674304), ((-177177010304242611561189:ℝ)/120259084288), ((-25343105204624777560587:ℝ)/105226698752), ((155916864613075752597:ℝ)/13153337344), ((25733811217477215851:ℝ)/1644167168), ((108365549213385549:ℝ)/29360128), ((1526576411899125:ℝ)/3670016), ((4860745860069:ℝ)/458752), ((-197152882119:ℝ)/57344), ((-24807724929:ℝ)/50176), ((-182402361:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 15 ht
  have m12 := abs_poly_le (fun e => ([((155283121303892901331812949267:ℝ)/27584547717644288), ((317880137101712595998346338649:ℝ)/27584547717644288), ((21652646793883675961231248617:ℝ)/3448068464705536), ((-223678574968318432001090841:ℝ)/61572651155456), ((-53371179711031609761224073:ℝ)/7696581394432), ((-4197639560276508666701205:ℝ)/962072674304), ((-177177010304242611561189:ℝ)/120259084288), ((-25343105204624777560587:ℝ)/105226698752), ((155916864613075752597:ℝ)/13153337344), ((25733811217477215851:ℝ)/1644167168), ((108365549213385549:ℝ)/29360128), ((1526576411899125:ℝ)/3670016), ((4860745860069:ℝ)/458752), ((-197152882119:ℝ)/57344), ((-24807724929:ℝ)/50176), ((-182402361:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0) 17 ht
  have bD := abs_poly_sub_affine_le (fun e => ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0) 8 ht
  have b11' : |(∑ e ∈ Finset.range 10, ([((567630589854065:ℝ)/29360128), ((143728200041505:ℝ)/3670016), ((1971101516235:ℝ)/57344), ((17778075015:ℝ)/1024), ((2872798935:ℝ)/512), ((77534895:ℝ)/64), (175605:ℝ), ((115680:ℝ)/7), ((6420:ℝ)/7), ((160:ℝ)/7)] : List ℝ).getD e 0 * t^e) - (((567630589854065:ℝ)/29360128) + ((143728200041505:ℝ)/3670016)*t)| ≤ ((8402854452535:ℝ)/14680064) := by
    refine (le_of_eq_of_le ?_ b11).trans (le_of_eq ?_)
    · rw [sub_add_eq_sub_sub]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have b12' : |(∑ e ∈ Finset.range 17, ([((155283121303892901331812949267:ℝ)/27584547717644288), ((317880137101712595998346338649:ℝ)/27584547717644288), ((21652646793883675961231248617:ℝ)/3448068464705536), ((-223678574968318432001090841:ℝ)/61572651155456), ((-53371179711031609761224073:ℝ)/7696581394432), ((-4197639560276508666701205:ℝ)/962072674304), ((-177177010304242611561189:ℝ)/120259084288), ((-25343105204624777560587:ℝ)/105226698752), ((155916864613075752597:ℝ)/13153337344), ((25733811217477215851:ℝ)/1644167168), ((108365549213385549:ℝ)/29360128), ((1526576411899125:ℝ)/3670016), ((4860745860069:ℝ)/458752), ((-197152882119:ℝ)/57344), ((-24807724929:ℝ)/50176), ((-182402361:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e) - ((155283121303892901331812949267:ℝ)/27584547717644288) - ((317880137101712595998346338649:ℝ)/27584547717644288)*t| ≤ ((482094782003231679132748277:ℝ)/4503599627370496) := by
    refine (le_of_eq_of_le ?_ b12).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have m12' : |(∑ e ∈ Finset.range 17, ([((155283121303892901331812949267:ℝ)/27584547717644288), ((317880137101712595998346338649:ℝ)/27584547717644288), ((21652646793883675961231248617:ℝ)/3448068464705536), ((-223678574968318432001090841:ℝ)/61572651155456), ((-53371179711031609761224073:ℝ)/7696581394432), ((-4197639560276508666701205:ℝ)/962072674304), ((-177177010304242611561189:ℝ)/120259084288), ((-25343105204624777560587:ℝ)/105226698752), ((155916864613075752597:ℝ)/13153337344), ((25733811217477215851:ℝ)/1644167168), ((108365549213385549:ℝ)/29360128), ((1526576411899125:ℝ)/3670016), ((4860745860069:ℝ)/458752), ((-197152882119:ℝ)/57344), ((-24807724929:ℝ)/50176), ((-182402361:ℝ)/6272), ((-531441:ℝ)/784)] : List ℝ).getD e 0 * t^e)| ≤ ((791883875925507079465177299179:ℝ)/110338190870577152) := by
    refine m12.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have bD' : |(∑ e ∈ Finset.range 10, ([((261217685273827:ℝ)/4194304), ((59376563119257:ℝ)/524288), ((1495516890639:ℝ)/16384), ((87661476441:ℝ)/2048), ((6590096709:ℝ)/512), ((164751447:ℝ)/64), ((1369851:ℝ)/4), (29226:ℝ), (1452:ℝ), (32:ℝ)] : List ℝ).getD e 0 * t^e) - ((261217685273827:ℝ)/4194304) - ((59376563119257:ℝ)/524288)*t| ≤ ((1586557175713:ℝ)/1048576) := by
    refine (le_of_eq_of_le ?_ bD).trans (le_of_eq ?_)
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((11:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m13 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-8120475:ℝ)/4), ((464861025:ℝ)/2), (-5906535975:ℝ), ((411904731750:ℝ)/7), ((-2024051769000:ℝ)/7), ((5554394637600:ℝ)/7), (-1314913862656:ℝ), ((9709155336192:ℝ)/7), ((-6724555112448:ℝ)/7), ((1313173667840:ℝ)/3), ((-6168244125696:ℝ)/49), ((3004329623552:ℝ)/147), ((-68719476736:ℝ)/49)] : List ℝ).getD e 0) 17 hq1'
  have m13' : |centralNum13_33 q| ≤ ((6261401871234643666632539:ℝ)/672) := by
    rw [centralNum13_33_list]; refine m13.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have hq1' : |q| ≤ ((11:ℝ)/2) := abs_le.mpr ⟨by linarith, h1⟩
  have m23 := abs_poly_le (fun e => ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-16872075:ℝ)/8), ((1833754545:ℝ)/8), ((-83998007145:ℝ)/16), ((4929124002765:ℝ)/112), ((-76723155584685:ℝ)/448), ((164888745653055:ℝ)/448), ((-63358359907625:ℝ)/128), ((364713160040625:ℝ)/896), ((-334937462578125:ℝ)/1792), ((245466998046875:ℝ)/5376), ((-72144521484375:ℝ)/12544), ((6518798828125:ℝ)/18816), ((-6103515625:ℝ)/784)] : List ℝ).getD e 0) 17 hq1'
  have m23' : |centralNum23_33 q| ≤ ((181777696680538765928543646785:ℝ)/308281344) := by
    rw [centralNum23_33_list]; refine m23.trans (le_of_eq ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero] <;> norm_num
  have c2 := comp_exp_bound (c := 8) (by norm_num) (by norm_num : (0:ℝ) ≤ (1/((12586602998062478850617801581:ℝ)/1250000000000000000000))) hE3 ht (by norm_num) b12' m12'
  have c3 := comp_crude_bound (c := 18) (by norm_num) (Real.exp_pos (-8*q)).le (piece24_E8 h0) m13'
  have c4 := comp_crude_bound (c := 72) (by norm_num) (Real.exp_pos (-11*q)).le (piece24_E11 h0) m23'
  have c5 := scaled_affine (X := ((-291458477247:ℝ)/1000000000000)) bD'
  have c6 : |-(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3))| ≤ ((4689069431270314097097200000000000:ℝ)/17137531830115983924003789721211970519) := by
    rw [abs_neg, tailWeight_3, abs_of_nonneg (by have := Real.exp_pos (-(529/50)*q); positivity)]
    have hq6 : q^6 ≤ ((11:ℝ)/2)^6 := pow_le_pow_left₀ (by linarith) h1 6
    have hB : (2*q-3)^2 ≤ (2*((11:ℝ)/2)-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hx := piece24_Et h0
    have hx0 : 0 ≤ Real.exp (-(529/50)*q) := (Real.exp_pos _).le
    calc q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*((3308571812705231500:ℝ)/129140163)) ≤ ((11:ℝ)/2)^6*(8000*(2*((11:ℝ)/2)-3)^2*(1/((132704895456233735154909086813:ℝ)/100000))*((3308571812705231500:ℝ)/129140163)) := by
          gcongr
      _ ≤ ((4689069431270314097097200000000000:ℝ)/17137531830115983924003789721211970519) := by norm_num
  have c7 := affine_round (α := ((567630589854065:ℝ)/29360128) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((155283121303892901331812949267:ℝ)/27584547717644288) + ((261217685273827:ℝ)/4194304)*((-291458477247:ℝ)/1000000000000) - ((565409150078080577:ℝ)/100000000000)) (β := ((143728200041505:ℝ)/3670016) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((317880137101712595998346338649:ℝ)/27584547717644288) - 3*((155283121303892901331812949267:ℝ)/27584547717644288)) + ((59376563119257:ℝ)/524288)*((-291458477247:ℝ)/1000000000000) - ((189278883917404879:ℝ)/100000000000)) ht
  have hW : pieceW q pieceX_24 3 3 = centralNum11_33 q + 8*(Real.exp (-(3*((43:ℝ)/8)))*Real.exp (-3*t))*centralNum12_33 q + 18*Real.exp (-8*q)*centralNum13_33 q + 72*Real.exp (-11*q)*centralNum23_33 q + 8*q^7*(2*q-3)^2*((-291458477247:ℝ)/1000000000000) + -(q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight 3)) := by
    rw [pieceW_33, pieceX_24, sym4_33, hexp3]; ring
  rw [h11, h12, hD] at hW
  refine entry_assemble (r7 := ((311687101832463499565392832587772652559202187146099840859941341:ℝ)/186052282910989080263275662545039324943164836150854495214355087360000000000)) hW b11' c2 (by simpa using c3) (by simpa using c4) c5 c6 ?_ ?_
  · have hab : (((567630589854065:ℝ)/29360128) + ((143728200041505:ℝ)/3670016)*t) + (8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((155283121303892901331812949267:ℝ)/27584547717644288) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((317880137101712595998346338649:ℝ)/27584547717644288) - 3*((155283121303892901331812949267:ℝ)/27584547717644288))*t) + (((261217685273827:ℝ)/4194304) + ((59376563119257:ℝ)/524288)*t)*((-291458477247:ℝ)/1000000000000) - (((565409150078080577:ℝ)/100000000000) + t * ((189278883917404879:ℝ)/100000000000)) = (((567630589854065:ℝ)/29360128) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*((155283121303892901331812949267:ℝ)/27584547717644288) + ((261217685273827:ℝ)/4194304)*((-291458477247:ℝ)/1000000000000) - ((565409150078080577:ℝ)/100000000000)) + t*(((143728200041505:ℝ)/3670016) + 8*(((1/((12586602998062478850617801581:ℝ)/1250000000000000000000))+(1/((25173205951636628266068425251:ℝ)/2500000000000000000000)))/2)*(((317880137101712595998346338649:ℝ)/27584547717644288) - 3*((155283121303892901331812949267:ℝ)/27584547717644288)) + ((59376563119257:ℝ)/524288)*((-291458477247:ℝ)/1000000000000) - ((189278883917404879:ℝ)/100000000000)) := by ring
    rw [hab]; exact c7.trans (by norm_num)
  · norm_num

theorem piece24_plus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((25470002375676399:ℝ)/2500000000) + ((1:ℝ)/8)*((479121735698959:ℝ)/31250000) - (((150243073075922833:ℝ)/50000000000) + ((55071921738866667:ℝ)/250000000000) + ((259452083990824539:ℝ)/10000000000000) + ((53742405191351449:ℝ)/5000000000000)))
      (((-61713250851307927:ℝ)/100000000000) + ((1:ℝ)/8)*((216352593068135189:ℝ)/100000000000))
      (((772598531961034943:ℝ)/10000000000000) + ((1:ℝ)/8)*((240356171036166193:ℝ)/1000000000000))
      (((345029123397448117:ℝ)/5000000000000) + ((1:ℝ)/8)*((-9902571592584383:ℝ)/250000000000))
      (((718999580228358967:ℝ)/100000000000) + ((1:ℝ)/8)*((429677594645886993:ℝ)/50000000000) - (((55071921738866667:ℝ)/250000000000) + ((202078044238842161:ℝ)/100000000000) + ((122260785221662961:ℝ)/1000000000000) + ((29427537800508373:ℝ)/250000000000)))
      (((-147316257674378249:ℝ)/1000000000000) + ((1:ℝ)/8)*((40607773974804413:ℝ)/25000000000))
      (((-97777440834820871:ℝ)/500000000000) + ((1:ℝ)/8)*((1646590377955971:ℝ)/1953125000))
      (((767706453251836157:ℝ)/100000000000) + ((1:ℝ)/8)*((25794232829947229:ℝ)/2000000000) - (((259452083990824539:ℝ)/10000000000000) + ((122260785221662961:ℝ)/1000000000000) + ((101051249118148067:ℝ)/50000000000) + ((56886004868947983:ℝ)/62500000000)))
      (((34802495815237129:ℝ)/40000000000) + ((1:ℝ)/8)*((223736070728410907:ℝ)/100000000000))
      (((565409150078080577:ℝ)/100000000000) + ((1:ℝ)/8)*((189278883917404879:ℝ)/100000000000) - (((53742405191351449:ℝ)/5000000000000) + ((29427537800508373:ℝ)/250000000000) + ((56886004868947983:ℝ)/62500000000) + ((245777954776708999:ℝ)/100000000000))) i j :=
  quadForm_nonneg_of_ldl ((88426450551551195283:ℝ)/10000000000000) ((1360484105698125173360033930725261553717:ℝ)/235803868137469854088000000000000) ((1013485408107058471366493157343612090910522987421728673233957:ℝ)/163258092683775020803204071687031386446040000000000000) ((6311100220800783039927911613564771877252958800836518406345531474464837040016911:ℝ)/2895672594591595632475694735267463116887208535490653352097020000000000000) ((-2311278447852735225:ℝ)/58950967034367463522) ((4292174983024970737:ℝ)/353705802206204781132) ((640545388831974319:ℝ)/88426450551551195283) ((28263297305336017712559659230389861781:ℝ)/2720968211396250346720067861450523107434) ((-20670973686997993233734625887796461914:ℝ)/1360484105698125173360033930725261553717) ((26817841353883397491277696194438943532652102501710364717802:ℝ)/144783629729579781623784736763373155844360426774532667604851)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece24_minus (y : Fin 4 → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * sym4 (((25470002375676399:ℝ)/2500000000) - ((1:ℝ)/8)*((479121735698959:ℝ)/31250000) - (((150243073075922833:ℝ)/50000000000) + ((55071921738866667:ℝ)/250000000000) + ((259452083990824539:ℝ)/10000000000000) + ((53742405191351449:ℝ)/5000000000000)))
      (((-61713250851307927:ℝ)/100000000000) - ((1:ℝ)/8)*((216352593068135189:ℝ)/100000000000))
      (((772598531961034943:ℝ)/10000000000000) - ((1:ℝ)/8)*((240356171036166193:ℝ)/1000000000000))
      (((345029123397448117:ℝ)/5000000000000) - ((1:ℝ)/8)*((-9902571592584383:ℝ)/250000000000))
      (((718999580228358967:ℝ)/100000000000) - ((1:ℝ)/8)*((429677594645886993:ℝ)/50000000000) - (((55071921738866667:ℝ)/250000000000) + ((202078044238842161:ℝ)/100000000000) + ((122260785221662961:ℝ)/1000000000000) + ((29427537800508373:ℝ)/250000000000)))
      (((-147316257674378249:ℝ)/1000000000000) - ((1:ℝ)/8)*((40607773974804413:ℝ)/25000000000))
      (((-97777440834820871:ℝ)/500000000000) - ((1:ℝ)/8)*((1646590377955971:ℝ)/1953125000))
      (((767706453251836157:ℝ)/100000000000) - ((1:ℝ)/8)*((25794232829947229:ℝ)/2000000000) - (((259452083990824539:ℝ)/10000000000000) + ((122260785221662961:ℝ)/1000000000000) + ((101051249118148067:ℝ)/50000000000) + ((56886004868947983:ℝ)/62500000000)))
      (((34802495815237129:ℝ)/40000000000) - ((1:ℝ)/8)*((223736070728410907:ℝ)/100000000000))
      (((565409150078080577:ℝ)/100000000000) - ((1:ℝ)/8)*((189278883917404879:ℝ)/100000000000) - (((53742405191351449:ℝ)/5000000000000) + ((29427537800508373:ℝ)/250000000000) + ((56886004868947983:ℝ)/62500000000) + ((245777954776708999:ℝ)/100000000000))) i j :=
  quadForm_nonneg_of_ldl ((50096711695634475283:ℝ)/10000000000000) ((1393694390602996362476949113449724248391:ℝ)/400773693565075802264000000000000) ((164536242954135369707937260273375858775909053110265124058647:ℝ)/55747775624119854499077964537988969935640000000000000) ((1962787916309370619426986013420311912203969995238902420828842650362351559133839:ℝ)/1096908286360902464719581735155839058506060354068434160390980000000000000) ((-17751464996964965125:ℝ)/100193423391268950566) ((1888613272663308807:ℝ)/200386846782537901132) ((739571104757818149:ℝ)/50096711695634475283) ((-274121106573574034536969668119186950617:ℝ)/2787388781205992724953898226899448496782) ((-115356110873849846018516792549385256454:ℝ)/1393694390602996362476949113449724248391) ((10432058271162531976673083472345479346359131756990659758158:ℝ)/54845414318045123235979086757791952925303017703421708019549)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

/-- **Piece 24.** The piece matrix is positive semidefinite on `q ∈ [21/4, 11/2]`. -/
theorem piece_24 {q : ℝ} (h0 : ((21:ℝ)/4) ≤ q) (h1 : q ≤ ((11:ℝ)/2)) (y : Fin 4 → ℝ) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceW q pieceX_24 i j :=
  pieceForm_nonneg (pieceW_symm (sym4_symm _ _ _ _ _ _ _ _ _ _) q) (by norm_num : (0:ℝ) < ((1:ℝ)/8))
    (abs_le.mpr ⟨by linarith, by linarith⟩)
    (piece24_e00 h0 h1) (piece24_e01 h0 h1) (piece24_e02 h0 h1) (piece24_e03 h0 h1) (piece24_e11 h0 h1) (piece24_e12 h0 h1) (piece24_e13 h0 h1) (piece24_e22 h0 h1) (piece24_e23 h0 h1) (piece24_e33 h0 h1)
    piece24_plus piece24_minus y

end
end RHTower.ThetaCuspOddFourPieces
