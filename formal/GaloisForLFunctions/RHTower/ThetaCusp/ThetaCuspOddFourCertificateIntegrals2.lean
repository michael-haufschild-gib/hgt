import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourPieceIntegral
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourCertificatePieces2
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourCertificatePieces3

/-!
# Piece integrals 6–11

For each piece: the compensation matrix is positive semidefinite by an exact `LDLᵀ` factorization, the weight
`r²κ(r)` is bounded above by a rational constant on the piece, and the moving-frame form integrates
exactly against `π e^r dr = dq`. Together with the piece certificate this bounds the seam-split
integral over the piece by an explicit quadratic form in `v`.
-/

namespace RHTower.ThetaCuspOddFourPieces
noncomputable section
open ThetaCuspOddCentral ThetaCuspOddFourCertificateTools

theorem piece6_X_psd (y : Fin 4 → ℝ) : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceX_6 i j := by
  unfold pieceX_6
  exact quadForm_nonneg_of_ldl ((63579018453:ℝ)/20000000000000) ((2584613852662777058577:ℝ)/105965030755000000000000) ((291428842338071038407875827044809:ℝ)/12923069263313885292885000000000000) ((245577809748657903586315417209821987085271:ℝ)/17485730540284262304472549622688540000000000) ((-72540330250:ℝ)/21193006151) ((765421222376:ℝ)/63579018453) ((-475742215700:ℝ)/21193006151) ((-10122574152655416387185:ℝ)/2584613852662777058577) ((19088018184902092149470:ℝ)/2584613852662777058577) ((-661596441885974292911430893208550:ℝ)/291428842338071038407875827044809)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece6_frame (v : Fin 4 → ℝ) (q : ℝ) :
    frameForm pieceX_6 q v = ∑ e ∈ Finset.range 7, ([(((63579018453:ℝ)/20000000000000)*(v 0*v 0) + ((-63579018453:ℝ)/2500000000000)*(v 0*v 1) + ((63579018453:ℝ)/625000000000)*(v 0*v 2) + ((-63579018453:ℝ)/156250000000)*(v 0*v 3) + ((63579018453:ℝ)/1250000000000)*(v 1*v 1) + ((-63579018453:ℝ)/156250000000)*(v 1*v 2) + ((63579018453:ℝ)/39062500000)*(v 1*v 3) + ((63579018453:ℝ)/78125000000)*(v 2*v 2) + ((-63579018453:ℝ)/9765625000)*(v 2*v 3) + ((63579018453:ℝ)/4882812500)*(v 3*v 3)), (((843600027609:ℝ)/1250000000000)*(v 0*v 1) + ((-843600027609:ℝ)/62500000000)*(v 0*v 2) + ((17715600579789:ℝ)/78125000000)*(v 0*v 3) + ((-843600027609:ℝ)/312500000000)*(v 1*v 1) + ((2530800082827:ℝ)/39062500000)*(v 1*v 2) + ((-9279600303699:ℝ)/9765625000)*(v 1*v 3) + ((-843600027609:ℝ)/3906250000)*(v 2*v 2) + ((10966800358917:ℝ)/2441406250)*(v 2*v 3) + ((-17715600579789:ℝ)/1220703125)*(v 3*v 3)), (((16667369667807:ℝ)/156250000000)*(v 0*v 2) + ((-116671587674649:ℝ)/19531250000)*(v 0*v 3) + ((15583746443049:ℝ)/312500000000)*(v 1*v 1) + ((-23646525470763:ℝ)/9765625000)*(v 1*v 2) + ((560601850653327:ℝ)/9765625000)*(v 1*v 3) + ((422928400411839:ℝ)/19531250000)*(v 2*v 2) + ((-7545215686149:ℝ)/9765625)*(v 2*v 3) + ((1467823706416641:ℝ)/244140625)*(v 3*v 3)), (((387999595418967:ℝ)/19531250000)*(v 0*v 3) + ((333835422804531:ℝ)/19531250000)*(v 1*v 2) + ((-5061695514682401:ℝ)/4882812500)*(v 1*v 3) + ((-333835422804531:ℝ)/976562500)*(v 2*v 2) + ((30767023070631288:ℝ)/1220703125)*(v 2*v 3) + ((-394142455599804324:ℝ)/1220703125)*(v 3*v 3)), (((7961433858484911:ℝ)/2441406250)*(v 1*v 3) + ((293058673794549:ℝ)/195312500)*(v 2*v 2) + ((-56951082048206682:ℝ)/244140625)*(v 2*v 3) + ((7081470894598625448:ℝ)/1220703125)*(v 3*v 3)), (((141052364826127524:ℝ)/244140625)*(v 2*v 3) + ((-7898932430263141344:ℝ)/244140625)*(v 3*v 3)), (((13634692908323214672:ℝ)/244140625)*(v 3*v 3))] : List ℝ).getD e 0 * q^e := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3, pieceX_6, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem piece6_frameIntegral (v : Fin 4 → ℝ) :
    ∫ r in Real.log (((37:ℝ)/10)/Real.pi)..Real.log (((19:ℝ)/5)/Real.pi),
      Real.pi*Real.exp r * frameForm pieceX_6 (Real.pi*Real.exp r) v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((63579018453:ℝ)/200000000000000) ((12526842377229:ℝ)/100000000000000) ((45301183984807597:ℝ)/625000000000000) ((15072290128838057999:ℝ)/312500000000000) ((21601181546182527:ℝ)/312500000000000) ((13557897155666785561:ℝ)/312500000000000) ((288688065751352442830009:ℝ)/9765625000000000) ((5451187695598542086023:ℝ)/195312500000000) ((4685940064285234681261923:ℝ)/244140625000000) ((4045690140002836027507847897:ℝ)/305175781250000) i j := by
  simp_rw [piece6_frame v]
  rw [integral_exp_poly, pi_mul_exp_log_div (by norm_num), pi_mul_exp_log_div (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero, Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  push_cast
  ring

theorem piece6_weight {r : ℝ} (hr : r ∈ Set.Ioo (Real.log (((37:ℝ)/10)/Real.pi)) (Real.log (((19:ℝ)/5)/Real.pi))) :
    r^2 * pieceKernel r ≤ ((2379675030774235331:ℝ)/10000000000000000000) := by
  obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
  have hr0 : 0 ≤ r := le_trans (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) hr.1.le
  have hrL : r ≤ ((95135704477:ℝ)/500000000000) := by
    refine hr.2.le.trans ((Real.log_le_iff_le_exp (by positivity)).mpr ?_)
    have h := le_exp_nat_add 0 (f := ((95135704477:ℝ)/500000000000)) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul h Real.pi_gt_d6.le (by norm_num) (Real.exp_pos _).le]
  have hU : Real.exp (((95135704477:ℝ)/500000000000)/2) ≤ ((109980809388188989756948528871:ℝ)/100000000000000000000000000000) := by
    have h := exp_nat_add_le 0 (f := ((95135704477:ℝ)/500000000000)/2) (by norm_num) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hE : ((81799220533807774091433623939:ℝ)/50000000000000000000000000) ≤ Real.exp (2*((37:ℝ)/10)) := by
    have h := le_exp_nat_add 7 (f := ((2:ℝ)/5)) (by norm_num)
    rw [show (2:ℝ)*((37:ℝ)/10) = ((7:ℕ):ℝ) + ((2:ℝ)/5) by norm_num]
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  exact (seam_weight_le hr0 (by linarith [Real.pi_gt_d2]) hqb (by norm_num) hrL hU (by norm_num) hE).trans
    (by norm_num)

/-- **Seam piece 6** on `q ∈ [37/10, 19/5]`. -/
theorem piece6_integral (v : Fin 4 → ℝ) :
    -(((2379675030774235331:ℝ)/10000000000000000000) * ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((63579018453:ℝ)/200000000000000) ((12526842377229:ℝ)/100000000000000) ((45301183984807597:ℝ)/625000000000000) ((15072290128838057999:ℝ)/312500000000000) ((21601181546182527:ℝ)/312500000000000) ((13557897155666785561:ℝ)/312500000000000) ((288688065751352442830009:ℝ)/9765625000000000) ((5451187695598542086023:ℝ)/195312500000000) ((4685940064285234681261923:ℝ)/244140625000000) ((4045690140002836027507847897:ℝ)/305175781250000) i j) ≤
      ∫ r in Real.log (((37:ℝ)/10)/Real.pi)..Real.log (((19:ℝ)/5)/Real.pi),
        thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have h := seam_piece_integral (ra' := Real.log (((37:ℝ)/10)/Real.pi)) (rc := Real.log (5/Real.pi)) (Ω := ((2379675030774235331:ℝ)/10000000000000000000))
    le_rfl (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith [Real.pi_lt_d2]) Real.pi_pos.le))
    (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2]))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le)) piece6_X_psd
    (fun r hr y => by
      obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
      exact piece_6 (by linarith [Real.pi_gt_d2]) hqb y)
    (by norm_num) (fun r hr => piece6_weight hr) v
  rwa [piece6_frameIntegral] at h

theorem piece7_X_psd (y : Fin 4 → ℝ) : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceX_7 i j := by
  unfold pieceX_7
  exact quadForm_nonneg_of_ldl ((254416990149:ℝ)/100000000000000) ((374109564851259982639:ℝ)/20191824615000000000000) ((42759810181559256323108647108429:ℝ)/2618766953958819878473000000000000) ((931736117799933054754386008749442275524131:ℝ)/96209572908508326726994455993965250000000000) ((-39534296170:ℝ)/12115094769) ((2792726254300:ℝ)/254416990149) ((-4916914478680:ℝ)/254416990149) ((-4184661152591453417365:ℝ)/1122328694553779947917) ((7441551569505428197120:ℝ)/1122328694553779947917) ((-272103944724836374575342563237590:ℝ)/128279430544677768969325941325287)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece7_frame (v : Fin 4 → ℝ) (q : ℝ) :
    frameForm pieceX_7 q v = ∑ e ∈ Finset.range 7, ([(((254416990149:ℝ)/100000000000000)*(v 0*v 0) + ((-254416990149:ℝ)/12500000000000)*(v 0*v 1) + ((254416990149:ℝ)/3125000000000)*(v 0*v 2) + ((-254416990149:ℝ)/781250000000)*(v 0*v 3) + ((254416990149:ℝ)/6250000000000)*(v 1*v 1) + ((-254416990149:ℝ)/781250000000)*(v 1*v 2) + ((254416990149:ℝ)/195312500000)*(v 1*v 3) + ((254416990149:ℝ)/390625000000)*(v 2*v 2) + ((-254416990149:ℝ)/48828125000)*(v 2*v 3) + ((254416990149:ℝ)/24414062500)*(v 3*v 3)), (((3253911629157:ℝ)/6250000000000)*(v 0*v 1) + ((-3253911629157:ℝ)/312500000000)*(v 0*v 2) + ((68332144212297:ℝ)/390625000000)*(v 0*v 3) + ((-3253911629157:ℝ)/1562500000000)*(v 1*v 1) + ((9761734887471:ℝ)/195312500000)*(v 1*v 2) + ((-35793027920727:ℝ)/48828125000)*(v 1*v 3) + ((-3253911629157:ℝ)/19531250000)*(v 2*v 2) + ((42300851179041:ℝ)/12207031250)*(v 2*v 3) + ((-68332144212297:ℝ)/6103515625)*(v 3*v 3)), (((12447115298187:ℝ)/156250000000)*(v 0*v 2) + ((-87129807087309:ℝ)/19531250000)*(v 0*v 3) + ((58291481819241:ℝ)/1562500000000)*(v 1*v 1) + ((-17684649279357:ℝ)/9765625000)*(v 1*v 2) + ((2095419189077151:ℝ)/48828125000)*(v 1*v 3) + ((316351639692579:ℝ)/19531250000)*(v 2*v 2) + ((-705413923838433:ℝ)/1220703125)*(v 2*v 3) + ((27449139624031461:ℝ)/6103515625)*(v 3*v 3)), (((281004197084583:ℝ)/19531250000)*(v 0*v 3) + ((242283478939011:ℝ)/19531250000)*(v 1*v 2) + ((-3672972902230737:ℝ)/4882812500)*(v 1*v 3) + ((-242283478939011:ℝ)/976562500)*(v 2*v 2) + ((22328800780534584:ℝ)/1220703125)*(v 2*v 3) + ((-286049388020615268:ℝ)/1220703125)*(v 3*v 3)), (((5607796716449739:ℝ)/2441406250)*(v 1*v 3) + ((1032387322563189:ℝ)/976562500)*(v 2*v 2) + ((-8024487692933754:ℝ)/48828125)*(v 2*v 3) + ((4989068152811257032:ℝ)/1220703125)*(v 3*v 3)), (((96478748014561668:ℝ)/244140625)*(v 2*v 3) + ((-5402809888815453408:ℝ)/244140625)*(v 3*v 3)), (((1811014110915370704:ℝ)/48828125)*(v 3*v 3))] : List ℝ).getD e 0 * q^e := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3, pieceX_7, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem piece7_frameIntegral (v : Fin 4 → ℝ) :
    ∫ r in Real.log (((19:ℝ)/5)/Real.pi)..Real.log (((39:ℝ)/10)/Real.pi),
      Real.pi*Real.exp r * frameForm pieceX_7 (Real.pi*Real.exp r) v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((254416990149:ℝ)/1000000000000000) ((248007025543599:ℝ)/2500000000000000) ((35651336013367771:ℝ)/625000000000000) ((11808207365968666793:ℝ)/312500000000000) ((85161010997583189:ℝ)/1562500000000000) ((10646474735998116271:ℝ)/312500000000000) ((225842289449557920714911:ℝ)/9765625000000000) ((21330393696662428679393:ℝ)/976562500000000) ((3654451649468901362942733:ℝ)/244140625000000) ((3144627149931182858613970691:ℝ)/305175781250000) i j := by
  simp_rw [piece7_frame v]
  rw [integral_exp_poly, pi_mul_exp_log_div (by norm_num), pi_mul_exp_log_div (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero, Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  push_cast
  ring

theorem piece7_weight {r : ℝ} (hr : r ∈ Set.Ioo (Real.log (((19:ℝ)/5)/Real.pi)) (Real.log (((39:ℝ)/10)/Real.pi))) :
    r^2 * pieceKernel r ≤ ((365502973076878367:ℝ)/1250000000000000000) := by
  obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
  have hr0 : 0 ≤ r := le_trans (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) hr.1.le
  have hrL : r ≤ ((43249379591:ℝ)/200000000000) := by
    refine hr.2.le.trans ((Real.log_le_iff_le_exp (by positivity)).mpr ?_)
    have h := le_exp_nat_add 0 (f := ((43249379591:ℝ)/200000000000)) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul h Real.pi_gt_d6.le (by norm_num) (Real.exp_pos _).le]
  have hU : Real.exp (((43249379591:ℝ)/200000000000)/2) ≤ ((111418528193077222755263662989:ℝ)/100000000000000000000000000000) := by
    have h := exp_nat_add_le 0 (f := ((43249379591:ℝ)/200000000000)/2) (by norm_num) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hE : ((199819540507241445801105084189:ℝ)/100000000000000000000000000) ≤ Real.exp (2*((19:ℝ)/5)) := by
    have h := le_exp_nat_add 7 (f := ((3:ℝ)/5)) (by norm_num)
    rw [show (2:ℝ)*((19:ℝ)/5) = ((7:ℕ):ℝ) + ((3:ℝ)/5) by norm_num]
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  exact (seam_weight_le hr0 (by linarith [Real.pi_gt_d2]) hqb (by norm_num) hrL hU (by norm_num) hE).trans
    (by norm_num)

/-- **Seam piece 7** on `q ∈ [19/5, 39/10]`. -/
theorem piece7_integral (v : Fin 4 → ℝ) :
    -(((365502973076878367:ℝ)/1250000000000000000) * ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((254416990149:ℝ)/1000000000000000) ((248007025543599:ℝ)/2500000000000000) ((35651336013367771:ℝ)/625000000000000) ((11808207365968666793:ℝ)/312500000000000) ((85161010997583189:ℝ)/1562500000000000) ((10646474735998116271:ℝ)/312500000000000) ((225842289449557920714911:ℝ)/9765625000000000) ((21330393696662428679393:ℝ)/976562500000000) ((3654451649468901362942733:ℝ)/244140625000000) ((3144627149931182858613970691:ℝ)/305175781250000) i j) ≤
      ∫ r in Real.log (((19:ℝ)/5)/Real.pi)..Real.log (((39:ℝ)/10)/Real.pi),
        thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have h := seam_piece_integral (ra' := Real.log (((19:ℝ)/5)/Real.pi)) (rc := Real.log (5/Real.pi)) (Ω := ((365502973076878367:ℝ)/1250000000000000000))
    le_rfl (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith [Real.pi_lt_d2]) Real.pi_pos.le))
    (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2]))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le)) piece7_X_psd
    (fun r hr y => by
      obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
      exact piece_7 (by linarith [Real.pi_gt_d2]) hqb y)
    (by norm_num) (fun r hr => piece7_weight hr) v
  rwa [piece7_frameIntegral] at h

theorem piece8_X_psd (y : Fin 4 → ℝ) : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceX_8 i j := by
  unfold pieceX_8
  exact quadForm_nonneg_of_ldl ((99012783759:ℝ)/50000000000000) ((68454721670294835742349:ℝ)/4950639187950000000000000) ((423351614549896059527629145429689:ℝ)/34227360835147417871174500000000000) ((2964030004218587829490777590319670452335633:ℝ)/423351614549896059527629145429689000000000000) ((-291667288841:ℝ)/99012783759) ((310722675010:ℝ)/33004261253) ((-1551067579355:ℝ)/99012783759) ((-242789202768592487961570:ℝ)/68454721670294835742349) ((407781892848358130986445:ℝ)/68454721670294835742349) ((-840301518214596810379625008147693:ℝ)/423351614549896059527629145429689)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece8_frame (v : Fin 4 → ℝ) (q : ℝ) :
    frameForm pieceX_8 q v = ∑ e ∈ Finset.range 7, ([(((99012783759:ℝ)/50000000000000)*(v 0*v 0) + ((-99012783759:ℝ)/6250000000000)*(v 0*v 1) + ((99012783759:ℝ)/1562500000000)*(v 0*v 2) + ((-99012783759:ℝ)/390625000000)*(v 0*v 3) + ((99012783759:ℝ)/3125000000000)*(v 1*v 1) + ((-99012783759:ℝ)/390625000000)*(v 1*v 2) + ((99012783759:ℝ)/97656250000)*(v 1*v 3) + ((99012783759:ℝ)/195312500000)*(v 2*v 2) + ((-99012783759:ℝ)/24414062500)*(v 2*v 3) + ((99012783759:ℝ)/12207031250)*(v 3*v 3)), (((5860201089:ℝ)/15625000000)*(v 0*v 1) + ((-5860201089:ℝ)/781250000)*(v 0*v 2) + ((123064222869:ℝ)/976562500)*(v 0*v 3) + ((-5860201089:ℝ)/3906250000)*(v 1*v 1) + ((17580603267:ℝ)/488281250)*(v 1*v 2) + ((-128924423958:ℝ)/244140625)*(v 1*v 3) + ((-5860201089:ℝ)/48828125)*(v 2*v 2) + ((609460913256:ℝ)/244140625)*(v 2*v 3) + ((-1969027565904:ℝ)/244140625)*(v 3*v 3)), (((856849068879:ℝ)/15625000000)*(v 0*v 2) + ((-5997943482153:ℝ)/1953125000)*(v 0*v 3) + ((20096099631099:ℝ)/781250000000)*(v 1*v 1) + ((-12190172487747:ℝ)/9765625000)*(v 1*v 2) + ((721915266360729:ℝ)/24414062500)*(v 1*v 3) + ((21809797768857:ℝ)/1953125000)*(v 2*v 2) + ((-486281772419004:ℝ)/1220703125)*(v 2*v 3) + ((18924348571059918:ℝ)/6103515625)*(v 3*v 3)), (((46746755725299:ℝ)/4882812500)*(v 0*v 3) + ((40406777755227:ℝ)/4882812500)*(v 1*v 2) + ((-612441644298477:ℝ)/1220703125)*(v 1*v 3) + ((-40406777755227:ℝ)/244140625)*(v 2*v 2) + ((14895054125803824:ℝ)/1220703125)*(v 2*v 3) + ((-190821430652192592:ℝ)/1220703125)*(v 3*v 3)), (((1815705265038147:ℝ)/1220703125)*(v 1*v 3) + ((66908770287399:ℝ)/97656250)*(v 2*v 2) + ((-25997276740624308:ℝ)/244140625)*(v 2*v 3) + ((3232900764318858192:ℝ)/1220703125)*(v 3*v 3)), (((60795321225893856:ℝ)/244140625)*(v 2*v 3) + ((-3404537988650055936:ℝ)/244140625)*(v 3*v 3)), (((5552126530126640352:ℝ)/244140625)*(v 3*v 3))] : List ℝ).getD e 0 * q^e := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3, pieceX_8, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem piece8_frameIntegral (v : Fin 4 → ℝ) :
    ∫ r in Real.log (((39:ℝ)/10)/Real.pi)..Real.log ((4:ℝ)/Real.pi),
      Real.pi*Real.exp r * frameForm pieceX_8 (Real.pi*Real.exp r) v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((99012783759:ℝ)/500000000000000) ((9160104936861:ℝ)/125000000000000) ((40336674624631:ℝ)/976562500000) ((10599671353176186091:ℝ)/390625000000000) ((1931008347372153:ℝ)/48828125000000) ((9585012851793720563:ℝ)/390625000000000) ((40496323899824671318319:ℝ)/2441406250000000) ((95712881268564695573:ℝ)/6103515625000) ((163569232715473160262729:ℝ)/15258789062500) ((140506572649808004480215603:ℝ)/19073486328125) i j := by
  simp_rw [piece8_frame v]
  rw [integral_exp_poly, pi_mul_exp_log_div (by norm_num), pi_mul_exp_log_div (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero, Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  push_cast
  ring

theorem piece8_weight {r : ℝ} (hr : r ∈ Set.Ioo (Real.log (((39:ℝ)/10)/Real.pi)) (Real.log ((4:ℝ)/Real.pi))) :
    r^2 * pieceKernel r ≤ ((3453313317776780999:ℝ)/10000000000000000000) := by
  obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
  have hr0 : 0 ≤ r := le_trans (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) hr.1.le
  have hrL : r ≤ ((241564708471:ℝ)/1000000000000) := by
    refine hr.2.le.trans ((Real.log_le_iff_le_exp (by positivity)).mpr ?_)
    have h := le_exp_nat_add 0 (f := ((241564708471:ℝ)/1000000000000)) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul h Real.pi_gt_d6.le (by norm_num) (Real.exp_pos _).le]
  have hU : Real.exp (((241564708471:ℝ)/1000000000000)/2) ≤ ((28209482466623594257845085809:ℝ)/25000000000000000000000000000) := by
    have h := exp_nat_add_le 0 (f := ((241564708471:ℝ)/1000000000000)/2) (by norm_num) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hE : ((244059697293106397522874308643:ℝ)/100000000000000000000000000) ≤ Real.exp (2*((39:ℝ)/10)) := by
    have h := le_exp_nat_add 7 (f := ((4:ℝ)/5)) (by norm_num)
    rw [show (2:ℝ)*((39:ℝ)/10) = ((7:ℕ):ℝ) + ((4:ℝ)/5) by norm_num]
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  exact (seam_weight_le hr0 (by linarith [Real.pi_gt_d2]) hqb (by norm_num) hrL hU (by norm_num) hE).trans
    (by norm_num)

/-- **Seam piece 8** on `q ∈ [39/10, 4]`. -/
theorem piece8_integral (v : Fin 4 → ℝ) :
    -(((3453313317776780999:ℝ)/10000000000000000000) * ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((99012783759:ℝ)/500000000000000) ((9160104936861:ℝ)/125000000000000) ((40336674624631:ℝ)/976562500000) ((10599671353176186091:ℝ)/390625000000000) ((1931008347372153:ℝ)/48828125000000) ((9585012851793720563:ℝ)/390625000000000) ((40496323899824671318319:ℝ)/2441406250000000) ((95712881268564695573:ℝ)/6103515625000) ((163569232715473160262729:ℝ)/15258789062500) ((140506572649808004480215603:ℝ)/19073486328125) i j) ≤
      ∫ r in Real.log (((39:ℝ)/10)/Real.pi)..Real.log ((4:ℝ)/Real.pi),
        thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have h := seam_piece_integral (ra' := Real.log (((39:ℝ)/10)/Real.pi)) (rc := Real.log (5/Real.pi)) (Ω := ((3453313317776780999:ℝ)/10000000000000000000))
    le_rfl (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith [Real.pi_lt_d2]) Real.pi_pos.le))
    (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2]))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le)) piece8_X_psd
    (fun r hr y => by
      obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
      exact piece_8 (by linarith [Real.pi_gt_d2]) hqb y)
    (by norm_num) (fun r hr => piece8_weight hr) v
  rwa [piece8_frameIntegral] at h

theorem piece9_X_psd (y : Fin 4 → ℝ) : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceX_9 i j := by
  unfold pieceX_9
  exact quadForm_nonneg_of_ldl ((147214026323:ℝ)/100000000000000) ((140555643621618397351969:ℝ)/14721402632300000000000000) ((271593027280769513084990637750653:ℝ)/28111128724323679470393800000000000) ((17867685604319018503867042374562834841683:ℝ)/3394912841009618913562382971883162500000000) ((-353895088751:ℝ)/147214026323) ((1055017971850:ℝ)/147214026323) ((-127543625660:ℝ)/11324155871) ((-470942833244451973939370:ℝ)/140555643621618397351969) ((747386094305546512411010:ℝ)/140555643621618397351969) ((-505113325769428214899700855843074:ℝ)/271593027280769513084990637750653)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece9_frame (v : Fin 4 → ℝ) (q : ℝ) :
    frameForm pieceX_9 q v = ∑ e ∈ Finset.range 7, ([(((147214026323:ℝ)/100000000000000)*(v 0*v 0) + ((-147214026323:ℝ)/12500000000000)*(v 0*v 1) + ((147214026323:ℝ)/3125000000000)*(v 0*v 2) + ((-147214026323:ℝ)/781250000000)*(v 0*v 3) + ((147214026323:ℝ)/6250000000000)*(v 1*v 1) + ((-147214026323:ℝ)/781250000000)*(v 1*v 2) + ((147214026323:ℝ)/195312500000)*(v 1*v 3) + ((147214026323:ℝ)/390625000000)*(v 2*v 2) + ((-147214026323:ℝ)/48828125000)*(v 2*v 3) + ((147214026323:ℝ)/24414062500)*(v 3*v 3)), (((751663672611:ℝ)/3125000000000)*(v 0*v 1) + ((-751663672611:ℝ)/156250000000)*(v 0*v 2) + ((15784937124831:ℝ)/195312500000)*(v 0*v 3) + ((-751663672611:ℝ)/781250000000)*(v 1*v 1) + ((2254991017833:ℝ)/97656250000)*(v 1*v 2) + ((-8268300398721:ℝ)/24414062500)*(v 1*v 3) + ((-751663672611:ℝ)/9765625000)*(v 2*v 2) + ((9771627743943:ℝ)/6103515625)*(v 2*v 3) + ((-31569874249662:ℝ)/6103515625)*(v 3*v 3)), (((1019411148783:ℝ)/31250000000)*(v 0*v 2) + ((-7135878041481:ℝ)/3906250000)*(v 0*v 3) + ((4788937559187:ℝ)/312500000000)*(v 1*v 1) + ((-580834870797:ℝ)/781250000)*(v 1*v 2) + ((171926469157737:ℝ)/9765625000)*(v 1*v 3) + ((25983510093501:ℝ)/3906250000)*(v 2*v 2) + ((-57929427987336:ℝ)/244140625)*(v 2*v 3) + ((2254639024431087:ℝ)/1220703125)*(v 3*v 3)), (((2660382969237:ℝ)/488281250)*(v 0*v 3) + ((23067321782733:ℝ)/4882812500)*(v 1*v 2) + ((-349546334650632:ℝ)/1220703125)*(v 1*v 3) + ((-23067321782733:ℝ)/244140625)*(v 2*v 2) + ((8502920447684292:ℝ)/1220703125)*(v 2*v 3) + ((-108934342941053952:ℝ)/1220703125)*(v 3*v 3)), (((2006717010732063:ℝ)/2441406250)*(v 1*v 3) + ((370285776450927:ℝ)/976562500)*(v 2*v 2) + ((-14381435762090082:ℝ)/244140625)*(v 2*v 3) + ((1788648701490620424:ℝ)/1220703125)*(v 3*v 3)), (((32719587324778872:ℝ)/244140625)*(v 2*v 3) + ((-1832296890187616832:ℝ)/244140625)*(v 3*v 3)), (((2912256202126994352:ℝ)/244140625)*(v 3*v 3))] : List ℝ).getD e 0 * q^e := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3, pieceX_9, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem piece9_frameIntegral (v : Fin 4 → ℝ) :
    ∫ r in Real.log ((4:ℝ)/Real.pi)..Real.log (((41:ℝ)/10)/Real.pi),
      Real.pi*Real.exp r * frameForm pieceX_9 (Real.pi*Real.exp r) v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((147214026323:ℝ)/1000000000000000) ((15037171837469:ℝ)/312500000000000) ((1611436544265213:ℝ)/62500000000000) ((64913886713567087:ℝ)/3906250000000) ((3867210232377521:ℝ)/156250000000000) ((2947013333371010859:ℝ)/195312500000000) ((24715477609158541607863:ℝ)/2441406250000000) ((4681432609577499626177:ℝ)/488281250000000) ((99724010920164951591559:ℝ)/15258789062500) ((684923812143871131751348737:ℝ)/152587890625000) i j := by
  simp_rw [piece9_frame v]
  rw [integral_exp_poly, pi_mul_exp_log_div (by norm_num), pi_mul_exp_log_div (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero, Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  push_cast
  ring

theorem piece9_weight {r : ℝ} (hr : r ∈ Set.Ioo (Real.log ((4:ℝ)/Real.pi)) (Real.log (((41:ℝ)/10)/Real.pi))) :
    r^2 * pieceKernel r ≤ ((790348597614761241:ℝ)/2000000000000000000) := by
  obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
  have hr0 : 0 ≤ r := le_trans (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) hr.1.le
  have hrL : r ≤ ((266257323531:ℝ)/1000000000000) := by
    refine hr.2.le.trans ((Real.log_le_iff_le_exp (by positivity)).mpr ?_)
    have h := le_exp_nat_add 0 (f := ((266257323531:ℝ)/1000000000000)) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul h Real.pi_gt_d6.le (by norm_num) (Real.exp_pos _).le]
  have hU : Real.exp (((266257323531:ℝ)/1000000000000)/2) ≤ ((57119848584365702802229496707:ℝ)/50000000000000000000000000000) := by
    have h := exp_nat_add_le 0 (f := ((266257323531:ℝ)/1000000000000)/2) (by norm_num) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hE : ((149047899282320702237006600847:ℝ)/50000000000000000000000000) ≤ Real.exp (2*(4:ℝ)) := by
    have h := le_exp_nat_add 8 (f := (0:ℝ)) (by norm_num)
    rw [show (2:ℝ)*(4:ℝ) = ((8:ℕ):ℝ) + (0:ℝ) by norm_num]
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  exact (seam_weight_le hr0 (by linarith [Real.pi_gt_d2]) hqb (by norm_num) hrL hU (by norm_num) hE).trans
    (by norm_num)

/-- **Seam piece 9** on `q ∈ [4, 41/10]`. -/
theorem piece9_integral (v : Fin 4 → ℝ) :
    -(((790348597614761241:ℝ)/2000000000000000000) * ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((147214026323:ℝ)/1000000000000000) ((15037171837469:ℝ)/312500000000000) ((1611436544265213:ℝ)/62500000000000) ((64913886713567087:ℝ)/3906250000000) ((3867210232377521:ℝ)/156250000000000) ((2947013333371010859:ℝ)/195312500000000) ((24715477609158541607863:ℝ)/2441406250000000) ((4681432609577499626177:ℝ)/488281250000000) ((99724010920164951591559:ℝ)/15258789062500) ((684923812143871131751348737:ℝ)/152587890625000) i j) ≤
      ∫ r in Real.log ((4:ℝ)/Real.pi)..Real.log (((41:ℝ)/10)/Real.pi),
        thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have h := seam_piece_integral (ra' := Real.log ((4:ℝ)/Real.pi)) (rc := Real.log (5/Real.pi)) (Ω := ((790348597614761241:ℝ)/2000000000000000000))
    le_rfl (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith [Real.pi_lt_d2]) Real.pi_pos.le))
    (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2]))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le)) piece9_X_psd
    (fun r hr y => by
      obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
      exact piece_9 (by linarith [Real.pi_gt_d2]) hqb y)
    (by norm_num) (fun r hr => piece9_weight hr) v
  rwa [piece9_frameIntegral] at h

theorem piece10_X_psd (y : Fin 4 → ℝ) : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceX_10 i j := by
  unfold pieceX_10
  exact quadForm_nonneg_of_ldl ((6424991643:ℝ)/6250000000000) ((50352783121013930727551:ℝ)/10279986628800000000000000) ((1863297843443681712970970673672957:ℝ)/251763915605069653637755000000000000) ((8445549554587532525709581811022546678540397:ℝ)/2070330937159646347745522970747730000000000000) ((-152627338127:ℝ)/102799866288) ((48216431323:ℝ)/12849983286) ((-563676216197:ℝ)/102799866288) ((-151823364264068187616472:ℝ)/50352783121013930727551) ((225151104199392487050101:ℝ)/50352783121013930727551) ((-1079019844631672148617384833795706:ℝ)/621099281147893904323656891224319)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece10_frame (v : Fin 4 → ℝ) (q : ℝ) :
    frameForm pieceX_10 q v = ∑ e ∈ Finset.range 7, ([(((6424991643:ℝ)/6250000000000)*(v 0*v 0) + ((-6424991643:ℝ)/781250000000)*(v 0*v 1) + ((6424991643:ℝ)/195312500000)*(v 0*v 2) + ((-6424991643:ℝ)/48828125000)*(v 0*v 3) + ((6424991643:ℝ)/390625000000)*(v 1*v 1) + ((-6424991643:ℝ)/48828125000)*(v 1*v 2) + ((6424991643:ℝ)/12207031250)*(v 1*v 3) + ((6424991643:ℝ)/24414062500)*(v 2*v 2) + ((-12849983286:ℝ)/6103515625)*(v 2*v 3) + ((25699966572:ℝ)/6103515625)*(v 3*v 3)), (((153256322649:ℝ)/1250000000000)*(v 0*v 1) + ((-153256322649:ℝ)/62500000000)*(v 0*v 2) + ((3218382775629:ℝ)/78125000000)*(v 0*v 3) + ((-153256322649:ℝ)/312500000000)*(v 1*v 1) + ((459768967947:ℝ)/39062500000)*(v 1*v 2) + ((-1685819549139:ℝ)/9765625000)*(v 1*v 3) + ((-153256322649:ℝ)/3906250000)*(v 2*v 2) + ((1992332194437:ℝ)/2441406250)*(v 2*v 3) + ((-3218382775629:ℝ)/1220703125)*(v 3*v 3)), (((5374797772569:ℝ)/390625000000)*(v 0*v 2) + ((-37623584407983:ℝ)/48828125000)*(v 0*v 3) + ((316258484949:ℝ)/48828125000)*(v 1*v 1) + ((-30675476568489:ℝ)/97656250000)*(v 1*v 2) + ((18151001975883:ℝ)/2441406250)*(v 1*v 3) + ((68626494762369:ℝ)/24414062500)*(v 2*v 2) + ((-122387244260571:ℝ)/1220703125)*(v 2*v 3) + ((4764028414864152:ℝ)/6103515625)*(v 3*v 3)), (((203424725177961:ℝ)/97656250000)*(v 0*v 3) + ((177379695800109:ℝ)/97656250000)*(v 1*v 2) + ((-2686740466379487:ℝ)/24414062500)*(v 1*v 3) + ((-177379695800109:ℝ)/4882812500)*(v 2*v 2) + ((3268995408597576:ℝ)/1220703125)*(v 2*v 3) + ((-209412221161640028:ℝ)/6103515625)*(v 3*v 3)), (((1823837723796249:ℝ)/6103515625)*(v 1*v 3) + ((168803613770121:ℝ)/1220703125)*(v 2*v 2) + ((-26201355637438548:ℝ)/1220703125)*(v 2*v 3) + ((3259650139111036944:ℝ)/6103515625)*(v 3*v 3)), (((57459617323062948:ℝ)/1220703125)*(v 2*v 3) + ((-3217738570091525088:ℝ)/1220703125)*(v 3*v 3)), (((4969808498414265408:ℝ)/1220703125)*(v 3*v 3))] : List ℝ).getD e 0 * q^e := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3, pieceX_10, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem piece10_frameIntegral (v : Fin 4 → ℝ) :
    ∫ r in Real.log (((41:ℝ)/10)/Real.pi)..Real.log (((21:ℝ)/5)/Real.pi),
      Real.pi*Real.exp r * frameForm pieceX_10 (Real.pi*Real.exp r) v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((6424991643:ℝ)/62500000000000) ((12514675047291:ℝ)/500000000000000) ((35443879100316389:ℝ)/3125000000000000) ((2121958022111739413:ℝ)/312500000000000) ((17115044105629677:ℝ)/1562500000000000) ((1944990259937962183:ℝ)/312500000000000) ((197558557995119589163627:ℝ)/48828125000000000) ((18789238329247340496583:ℝ)/4882812500000000) ((3161088519486528213201999:ℝ)/1220703125000000) ((2704258893382333327081704733:ℝ)/1525878906250000) i j := by
  simp_rw [piece10_frame v]
  rw [integral_exp_poly, pi_mul_exp_log_div (by norm_num), pi_mul_exp_log_div (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero, Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  push_cast
  ring

theorem piece10_weight {r : ℝ} (hr : r ∈ Set.Ioo (Real.log (((41:ℝ)/10)/Real.pi)) (Real.log (((21:ℝ)/5)/Real.pi))) :
    r^2 * pieceKernel r ≤ ((176274434900852919:ℝ)/400000000000000000) := by
  obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
  have hr0 : 0 ≤ r := le_trans (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) hr.1.le
  have hrL : r ≤ ((3629435969:ℝ)/12500000000) := by
    refine hr.2.le.trans ((Real.log_le_iff_le_exp (by positivity)).mpr ?_)
    have h := le_exp_nat_add 0 (f := ((3629435969:ℝ)/12500000000)) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul h Real.pi_gt_d6.le (by norm_num) (Real.exp_pos _).le]
  have hU : Real.exp (((3629435969:ℝ)/12500000000)/2) ≤ ((14453058933702009458889755301:ℝ)/12500000000000000000000000000) := by
    have h := exp_nat_add_le 0 (f := ((3629435969:ℝ)/12500000000)/2) (by norm_num) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hE : ((91023757635863882189832158933:ℝ)/25000000000000000000000000) ≤ Real.exp (2*((41:ℝ)/10)) := by
    have h := le_exp_nat_add 8 (f := ((1:ℝ)/5)) (by norm_num)
    rw [show (2:ℝ)*((41:ℝ)/10) = ((8:ℕ):ℝ) + ((1:ℝ)/5) by norm_num]
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  exact (seam_weight_le hr0 (by linarith [Real.pi_gt_d2]) hqb (by norm_num) hrL hU (by norm_num) hE).trans
    (by norm_num)

/-- **Seam piece 10** on `q ∈ [41/10, 21/5]`. -/
theorem piece10_integral (v : Fin 4 → ℝ) :
    -(((176274434900852919:ℝ)/400000000000000000) * ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((6424991643:ℝ)/62500000000000) ((12514675047291:ℝ)/500000000000000) ((35443879100316389:ℝ)/3125000000000000) ((2121958022111739413:ℝ)/312500000000000) ((17115044105629677:ℝ)/1562500000000000) ((1944990259937962183:ℝ)/312500000000000) ((197558557995119589163627:ℝ)/48828125000000000) ((18789238329247340496583:ℝ)/4882812500000000) ((3161088519486528213201999:ℝ)/1220703125000000) ((2704258893382333327081704733:ℝ)/1525878906250000) i j) ≤
      ∫ r in Real.log (((41:ℝ)/10)/Real.pi)..Real.log (((21:ℝ)/5)/Real.pi),
        thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have h := seam_piece_integral (ra' := Real.log (((41:ℝ)/10)/Real.pi)) (rc := Real.log (5/Real.pi)) (Ω := ((176274434900852919:ℝ)/400000000000000000))
    le_rfl (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith [Real.pi_lt_d2]) Real.pi_pos.le))
    (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2]))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le)) piece10_X_psd
    (fun r hr y => by
      obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
      exact piece_10 (by linarith [Real.pi_gt_d2]) hqb y)
    (by norm_num) (fun r hr => piece10_weight hr) v
  rwa [piece10_frameIntegral] at h

theorem piece11_X_psd (y : Fin 4 → ℝ) : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceX_11 i j := by
  unfold pieceX_11
  exact quadForm_nonneg_of_ldl ((211294010849:ℝ)/500000000000000) ((1065431671983206013459651:ℝ)/422588021698000000000000000) ((27953306896664740951524836774522603:ℝ)/10654316719832060134596510000000000000) ((67601247748913880496504849475713658435525401:ℝ)/55906613793329481903049673549045206000000000000) ((-852605032457:ℝ)/422588021698) ((1197543757785:ℝ)/211294010849) ((-1724366353875:ℝ)/211294010849) ((-3343831494465245768583710:ℝ)/1065431671983206013459651) ((1616036455330648874354350:ℝ)/355143890661068671153217) ((-45954185527558443528186374704178460:ℝ)/27953306896664740951524836774522603)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece11_frame (v : Fin 4 → ℝ) (q : ℝ) :
    frameForm pieceX_11 q v = ∑ e ∈ Finset.range 7, ([(((211294010849:ℝ)/500000000000000)*(v 0*v 0) + ((-211294010849:ℝ)/62500000000000)*(v 0*v 1) + ((211294010849:ℝ)/15625000000000)*(v 0*v 2) + ((-211294010849:ℝ)/3906250000000)*(v 0*v 3) + ((211294010849:ℝ)/31250000000000)*(v 1*v 1) + ((-211294010849:ℝ)/3906250000000)*(v 1*v 2) + ((211294010849:ℝ)/976562500000)*(v 1*v 3) + ((211294010849:ℝ)/1953125000000)*(v 2*v 2) + ((-211294010849:ℝ)/244140625000)*(v 2*v 3) + ((211294010849:ℝ)/122070312500)*(v 3*v 3)), (((765115832493:ℝ)/12500000000000)*(v 0*v 1) + ((-765115832493:ℝ)/625000000000)*(v 0*v 2) + ((16067432482353:ℝ)/781250000000)*(v 0*v 3) + ((-765115832493:ℝ)/3125000000000)*(v 1*v 1) + ((2295347497479:ℝ)/390625000000)*(v 1*v 2) + ((-8416274157423:ℝ)/97656250000)*(v 1*v 3) + ((-765115832493:ℝ)/39062500000)*(v 2*v 2) + ((9946505822409:ℝ)/24414062500)*(v 2*v 3) + ((-16067432482353:ℝ)/12207031250)*(v 3*v 3)), (((3032901074301:ℝ)/390625000000)*(v 0*v 2) + ((-21230307520107:ℝ)/48828125000)*(v 0*v 3) + ((28661414583879:ℝ)/7812500000000)*(v 1*v 1) + ((-34727216732481:ℝ)/195312500000)*(v 1*v 2) + ((1026495856663599:ℝ)/244140625000)*(v 1*v 3) + ((155438677216599:ℝ)/97656250000)*(v 2*v 2) + ((-692876738490489:ℝ)/12207031250)*(v 2*v 3) + ((13488896132294919:ℝ)/30517578125)*(v 3*v 3)), (((241239585775377:ℝ)/195312500000)*(v 0*v 3) + ((42435547085421:ℝ)/39062500000)*(v 1*v 2) + ((-3211727881754847:ℝ)/48828125000)*(v 1*v 3) + ((-42435547085421:ℝ)/1953125000)*(v 2*v 2) + ((9774706754820966:ℝ)/6103515625)*(v 2*v 3) + ((-125242987602688494:ℝ)/6103515625)*(v 3*v 3)), (((1108751109997923:ℝ)/6103515625)*(v 1*v 3) + ((82507898603547:ℝ)/976562500)*(v 2*v 2) + ((-15986110244488272:ℝ)/1220703125)*(v 2*v 3) + ((1989695185588823328:ℝ)/6103515625)*(v 3*v 3)), (((35142149656374138:ℝ)/1220703125)*(v 2*v 3) + ((-1967960380756951728:ℝ)/1220703125)*(v 3*v 3)), (((3018852227860841232:ℝ)/1220703125)*(v 3*v 3))] : List ℝ).getD e 0 * q^e := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3, pieceX_11, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem piece11_frameIntegral (v : Fin 4 → ℝ) :
    ∫ r in Real.log (((21:ℝ)/5)/Real.pi)..Real.log (((22:ℝ)/5)/Real.pi),
      Real.pi*Real.exp r * frameForm pieceX_11 (Real.pi*Real.exp r) v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((211294010849:ℝ)/2500000000000000) ((32477392775501:ℝ)/1250000000000000) ((21614993633807779:ℝ)/1562500000000000) ((3527478871739035779:ℝ)/390625000000000) ((26093646100397407:ℝ)/1953125000000000) ((1624144129087255819:ℝ)/195312500000000) ((34800568227047248470591:ℝ)/6103515625000000) ((332238893243888179083:ℝ)/61035156250000) ((580475855796124301389633:ℝ)/152587890625000) ((51158779964397608106432224:ℝ)/19073486328125) i j := by
  simp_rw [piece11_frame v]
  rw [integral_exp_poly, pi_mul_exp_log_div (by norm_num), pi_mul_exp_log_div (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero, Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  push_cast
  ring

theorem piece11_weight {r : ℝ} (hr : r ∈ Set.Ioo (Real.log (((21:ℝ)/5)/Real.pi)) (Real.log (((22:ℝ)/5)/Real.pi))) :
    r^2 * pieceKernel r ≤ ((1573498888356439799:ℝ)/2500000000000000000) := by
  obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
  have hr0 : 0 ≤ r := le_trans (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) hr.1.le
  have hrL : r ≤ ((168437448903:ℝ)/500000000000) := by
    refine hr.2.le.trans ((Real.log_le_iff_le_exp (by positivity)).mpr ?_)
    have h := le_exp_nat_add 0 (f := ((168437448903:ℝ)/500000000000)) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul h Real.pi_gt_d6.le (by norm_num) (Real.exp_pos _).le]
  have hU : Real.exp (((168437448903:ℝ)/500000000000)/2) ≤ ((118345419817295331549680637801:ℝ)/100000000000000000000000000000) := by
    have h := exp_nat_add_le 0 (f := ((168437448903:ℝ)/500000000000)/2) (by norm_num) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hE : ((222353334746153898118015562649:ℝ)/50000000000000000000000000) ≤ Real.exp (2*((21:ℝ)/5)) := by
    have h := le_exp_nat_add 8 (f := ((2:ℝ)/5)) (by norm_num)
    rw [show (2:ℝ)*((21:ℝ)/5) = ((8:ℕ):ℝ) + ((2:ℝ)/5) by norm_num]
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  exact (seam_weight_le hr0 (by linarith [Real.pi_gt_d2]) hqb (by norm_num) hrL hU (by norm_num) hE).trans
    (by norm_num)

/-- **Seam piece 11** on `q ∈ [21/5, 22/5]`. -/
theorem piece11_integral (v : Fin 4 → ℝ) :
    -(((1573498888356439799:ℝ)/2500000000000000000) * ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((211294010849:ℝ)/2500000000000000) ((32477392775501:ℝ)/1250000000000000) ((21614993633807779:ℝ)/1562500000000000) ((3527478871739035779:ℝ)/390625000000000) ((26093646100397407:ℝ)/1953125000000000) ((1624144129087255819:ℝ)/195312500000000) ((34800568227047248470591:ℝ)/6103515625000000) ((332238893243888179083:ℝ)/61035156250000) ((580475855796124301389633:ℝ)/152587890625000) ((51158779964397608106432224:ℝ)/19073486328125) i j) ≤
      ∫ r in Real.log (((21:ℝ)/5)/Real.pi)..Real.log (((22:ℝ)/5)/Real.pi),
        thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have h := seam_piece_integral (ra' := Real.log (((21:ℝ)/5)/Real.pi)) (rc := Real.log (5/Real.pi)) (Ω := ((1573498888356439799:ℝ)/2500000000000000000))
    le_rfl (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith [Real.pi_lt_d2]) Real.pi_pos.le))
    (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2]))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le)) piece11_X_psd
    (fun r hr y => by
      obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
      exact piece_11 (by linarith [Real.pi_gt_d2]) hqb y)
    (by norm_num) (fun r hr => piece11_weight hr) v
  rwa [piece11_frameIntegral] at h

end
end RHTower.ThetaCuspOddFourPieces
