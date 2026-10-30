import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourPieceIntegral
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourCertificatePieces1
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourCertificatePieces2

/-!
# Piece integrals 0–5

For each piece: the compensation matrix is positive semidefinite by an exact `LDLᵀ` factorization, the weight
`r²κ(r)` is bounded above by a rational constant on the piece, and the moving-frame form integrates
exactly against `π e^r dr = dq`. Together with the piece certificate this bounds the seam-split
integral over the piece by an explicit quadratic form in `v`.
-/

namespace RHTower.ThetaCuspOddFourPieces
noncomputable section
open ThetaCuspOddCentral ThetaCuspOddFourCertificateTools

theorem piece0_X_psd (y : Fin 4 → ℝ) : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceX_0 i j := by
  unfold pieceX_0
  exact quadForm_nonneg_of_ldl ((69161827163:ℝ)/50000000000) ((47466643498379505257417:ℝ)/13832365432600000000000) ((68969492511001079454600535606229769:ℝ)/4746664349837950525741700000000000) ((981866337432964797285418443954827057248842299:ℝ)/28737288546250449772750223169262403750000000) ((-143254744953:ℝ)/138323654326) ((193902528901:ℝ)/138323654326) ((-113602719426:ℝ)/69161827163) ((-119324594898484682648047:ℝ)/47466643498379505257417) ((192491517937168369052104:ℝ)/47466643498379505257417) ((-66182144487813591809396099998110426:ℝ)/22989830837000359818200178535409923)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece0_frame (v : Fin 4 → ℝ) (q : ℝ) :
    frameForm pieceX_0 q v = ∑ e ∈ Finset.range 7, ([(((69161827163:ℝ)/50000000000)*(v 0*v 0) + ((-69161827163:ℝ)/6250000000)*(v 0*v 1) + ((69161827163:ℝ)/1562500000)*(v 0*v 2) + ((-69161827163:ℝ)/390625000)*(v 0*v 3) + ((69161827163:ℝ)/3125000000)*(v 1*v 1) + ((-69161827163:ℝ)/390625000)*(v 1*v 2) + ((69161827163:ℝ)/97656250)*(v 1*v 3) + ((69161827163:ℝ)/195312500)*(v 2*v 2) + ((-138323654326:ℝ)/48828125)*(v 2*v 3) + ((276647308652:ℝ)/48828125)*(v 3*v 3)), (((844735197837:ℝ)/6250000000)*(v 0*v 1) + ((-844735197837:ℝ)/312500000)*(v 0*v 2) + ((17739439154577:ℝ)/390625000)*(v 0*v 3) + ((-844735197837:ℝ)/1562500000)*(v 1*v 1) + ((2534205593511:ℝ)/195312500)*(v 1*v 2) + ((-9292087176207:ℝ)/48828125)*(v 1*v 3) + ((-844735197837:ℝ)/19531250)*(v 2*v 2) + ((43926230287524:ℝ)/48828125)*(v 2*v 3) + ((-141915513236616:ℝ)/48828125)*(v 3*v 3)), (((2174831877573:ℝ)/195312500)*(v 0*v 2) + ((-30447646286022:ℝ)/48828125)*(v 0*v 3) + ((8247160267047:ℝ)/1562500000)*(v 1*v 1) + ((-49935128845527:ℝ)/195312500)*(v 1*v 2) + ((11799238030083:ℝ)/1953125)*(v 1*v 3) + ((223577661696759:ℝ)/97656250)*(v 2*v 2) + ((-797153392555452:ℝ)/9765625)*(v 2*v 3) + ((31044630784447224:ℝ)/48828125)*(v 3*v 3)), (((25519584502209:ℝ)/19531250)*(v 0*v 3) + ((115065724327551:ℝ)/97656250)*(v 1*v 2) + ((-3477036126193518:ℝ)/48828125)*(v 1*v 3) + ((-230131448655102:ℝ)/9765625)*(v 2*v 2) + ((84788630690545488:ℝ)/48828125)*(v 2*v 3) + ((-1086621467993953248:ℝ)/48828125)*(v 3*v 3)), (((1685089608744276:ℝ)/9765625)*(v 1*v 3) + ((31977056503404:ℝ)/390625)*(v 2*v 2) + ((-24647510076883344:ℝ)/1953125)*(v 2*v 3) + ((3073191338404950336:ℝ)/9765625)*(v 3*v 3)), (((11072295318875616:ℝ)/390625)*(v 2*v 3) + ((-620048537857034496:ℝ)/390625)*(v 3*v 3)), (((27300305395005197184:ℝ)/9765625)*(v 3*v 3))] : List ℝ).getD e 0 * q^e := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3, pieceX_0, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem piece0_frameIntegral (v : Fin 4 → ℝ) :
    ∫ r in Real.log (((31:ℝ)/10)/Real.pi)..Real.log (((16:ℝ)/5)/Real.pi),
      Real.pi*Real.exp r * frameForm pieceX_0 (Real.pi*Real.exp r) v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((69161827163:ℝ)/500000000000) ((51835080920471:ℝ)/2500000000000) ((15941723578215881:ℝ)/3125000000000) ((2719086224927097437:ℝ)/1562500000000) ((1980324635593117:ℝ)/390625000000) ((2682878926407924149:ℝ)/1562500000000) ((7241467539418839994831:ℝ)/9765625000000) ((143547517809250630331:ℝ)/195312500000) ((11609819216453876269309:ℝ)/30517578125) ((346696069059776557957317961:ℝ)/1525878906250) i j := by
  simp_rw [piece0_frame v]
  rw [integral_exp_poly, pi_mul_exp_log_div (by norm_num), pi_mul_exp_log_div (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero, Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  push_cast
  ring

theorem piece0_weight {r : ℝ} (hr : r ∈ Set.Ioo (Real.log (Real.pi/Real.pi)) (Real.log (((16:ℝ)/5)/Real.pi))) :
    r^2 * pieceKernel r ≤ ((3290977069125523:ℝ)/1250000000000000000) := by
  obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
  have hr0 : 0 ≤ r := le_trans (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) hr.1.le
  have hrL : r ≤ ((7368453937:ℝ)/400000000000) := by
    refine hr.2.le.trans ((Real.log_le_iff_le_exp (by positivity)).mpr ?_)
    have h := le_exp_nat_add 0 (f := ((7368453937:ℝ)/400000000000)) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul h Real.pi_gt_d6.le (by norm_num) (Real.exp_pos _).le]
  have hU : Real.exp (((7368453937:ℝ)/400000000000)/2) ≤ ((20185062304536906155850237937:ℝ)/20000000000000000000000000000) := by
    have h := exp_nat_add_le 0 (f := ((7368453937:ℝ)/400000000000)/2) (by norm_num) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hE : ((246374520447039001684189926657:ℝ)/500000000000000000000000000) ≤ Real.exp (2*((31:ℝ)/10)) := by
    have h := le_exp_nat_add 6 (f := ((1:ℝ)/5)) (by norm_num)
    rw [show (2:ℝ)*((31:ℝ)/10) = ((6:ℕ):ℝ) + ((1:ℝ)/5) by norm_num]
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  exact (seam_weight_le hr0 (by linarith [Real.pi_gt_d2]) hqb (by norm_num) hrL hU (by norm_num) hE).trans
    (by norm_num)

/-- **Seam piece 0** on `q ∈ [π, 16/5]`. -/
theorem piece0_integral (v : Fin 4 → ℝ) :
    -(((3290977069125523:ℝ)/1250000000000000000) * ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((69161827163:ℝ)/500000000000) ((51835080920471:ℝ)/2500000000000) ((15941723578215881:ℝ)/3125000000000) ((2719086224927097437:ℝ)/1562500000000) ((1980324635593117:ℝ)/390625000000) ((2682878926407924149:ℝ)/1562500000000) ((7241467539418839994831:ℝ)/9765625000000) ((143547517809250630331:ℝ)/195312500000) ((11609819216453876269309:ℝ)/30517578125) ((346696069059776557957317961:ℝ)/1525878906250) i j) ≤
      ∫ r in Real.log (Real.pi/Real.pi)..Real.log (((16:ℝ)/5)/Real.pi),
        thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have h := seam_piece_integral (ra' := Real.log (((31:ℝ)/10)/Real.pi)) (rc := Real.log (5/Real.pi)) (Ω := ((3290977069125523:ℝ)/1250000000000000000))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith [Real.pi_gt_d2]) Real.pi_pos.le)) (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith [Real.pi_lt_d2]) Real.pi_pos.le))
    (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2]))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le)) piece0_X_psd
    (fun r hr y => by
      obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
      exact piece_0 (by linarith [Real.pi_gt_d2]) hqb y)
    (by norm_num) (fun r hr => piece0_weight hr) v
  rwa [piece0_frameIntegral] at h

theorem piece1_X_psd (y : Fin 4 → ℝ) : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceX_1 i j := by
  unfold pieceX_1
  exact quadForm_nonneg_of_ldl ((108333464993:ℝ)/5000000000000) ((882446839939011466351:ℝ)/6770841562062500000000) ((115304400467814926061392597053457:ℝ)/220611709984752866587750000000000) ((191493007969541499193433000114339263081796861:ℝ)/368974081497007763396456310571062400000000000) ((-175634819505:ℝ)/108333464993) ((41482566150:ℝ)/8333343461) ((-1298247347455:ℝ)/108333464993) ((-4032970386123053696906:ℝ)/882446839939011466351) ((167626013531308384188625:ℝ)/14119149439024183461616) ((-389278589228303147535681822916150:ℝ)/115304400467814926061392597053457)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece1_frame (v : Fin 4 → ℝ) (q : ℝ) :
    frameForm pieceX_1 q v = ∑ e ∈ Finset.range 7, ([(((108333464993:ℝ)/5000000000000)*(v 0*v 0) + ((-108333464993:ℝ)/625000000000)*(v 0*v 1) + ((108333464993:ℝ)/156250000000)*(v 0*v 2) + ((-108333464993:ℝ)/39062500000)*(v 0*v 3) + ((108333464993:ℝ)/312500000000)*(v 1*v 1) + ((-108333464993:ℝ)/39062500000)*(v 1*v 2) + ((108333464993:ℝ)/9765625000)*(v 1*v 3) + ((108333464993:ℝ)/19531250000)*(v 2*v 2) + ((-108333464993:ℝ)/2441406250)*(v 2*v 3) + ((108333464993:ℝ)/1220703125)*(v 3*v 3)), (((425952426747:ℝ)/156250000000)*(v 0*v 1) + ((-425952426747:ℝ)/7812500000)*(v 0*v 2) + ((8945000961687:ℝ)/9765625000)*(v 0*v 3) + ((-425952426747:ℝ)/39062500000)*(v 1*v 1) + ((1277857280241:ℝ)/4882812500)*(v 1*v 2) + ((-4685476694217:ℝ)/1220703125)*(v 1*v 3) + ((-425952426747:ℝ)/488281250)*(v 2*v 2) + ((22149526190844:ℝ)/1220703125)*(v 2*v 3) + ((-71560007693496:ℝ)/1220703125)*(v 3*v 3)), (((2673065375889:ℝ)/7812500000)*(v 0*v 2) + ((-18711457631223:ℝ)/976562500)*(v 0*v 3) + ((3141004499973:ℝ)/19531250000)*(v 1*v 1) + ((-15237083375781:ℝ)/1953125000)*(v 1*v 2) + ((225479477154981:ℝ)/1220703125)*(v 1*v 3) + ((34083110375619:ℝ)/488281250)*(v 2*v 2) + ((-607880717272134:ℝ)/244140625)*(v 2*v 3) + ((23659844362307328:ℝ)/1220703125)*(v 3*v 3)), (((15582482293098:ℝ)/244140625)*(v 0*v 3) + ((27096482881467:ℝ)/488281250)*(v 1*v 2) + ((-821031449853468:ℝ)/244140625)*(v 1*v 3) + ((-54192965762934:ℝ)/48828125)*(v 2*v 2) + ((19975559254397544:ℝ)/244140625)*(v 2*v 3) + ((-255920989815599808:ℝ)/244140625)*(v 3*v 3)), (((2907067185756216:ℝ)/244140625)*(v 1*v 3) + ((268639377085953:ℝ)/48828125)*(v 2*v 2) + ((-1668635159066064:ℝ)/1953125)*(v 2*v 3) + ((5189040007121831616:ℝ)/244140625)*(v 3*v 3)), (((24508406042684928:ℝ)/9765625)*(v 2*v 3) + ((-1372470738390355968:ℝ)/9765625)*(v 3*v 3)), (((14389119051671895552:ℝ)/48828125)*(v 3*v 3))] : List ℝ).getD e 0 * q^e := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3, pieceX_1, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem piece1_frameIntegral (v : Fin 4 → ℝ) :
    ∫ r in Real.log (((16:ℝ)/5)/Real.pi)..Real.log (((33:ℝ)/10)/Real.pi),
      Real.pi*Real.exp r * frameForm pieceX_1 (Real.pi*Real.exp r) v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((108333464993:ℝ)/50000000000000) ((2714524041359:ℝ)/6250000000000) ((2685755187362937:ℝ)/15625000000000) ((194542508341031597:ℝ)/1953125000000) ((12997630273125191:ℝ)/78125000000000) ((712453569683996427:ℝ)/7812500000000) ((3709584384569511746969:ℝ)/61035156250000) ((1408019973641540975183:ℝ)/24414062500000) ((19973637489491006918533:ℝ)/488281250000) ((228131247383965215330727977:ℝ)/7629394531250) i j := by
  simp_rw [piece1_frame v]
  rw [integral_exp_poly, pi_mul_exp_log_div (by norm_num), pi_mul_exp_log_div (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero, Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  push_cast
  ring

theorem piece1_weight {r : ℝ} (hr : r ∈ Set.Ioo (Real.log (((16:ℝ)/5)/Real.pi)) (Real.log (((33:ℝ)/10)/Real.pi))) :
    r^2 * pieceKernel r ≤ ((37223163646246657:ℝ)/2000000000000000000) := by
  obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
  have hr0 : 0 ≤ r := le_trans (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) hr.1.le
  have hrL : r ≤ ((61490995733:ℝ)/1250000000000) := by
    refine hr.2.le.trans ((Real.log_le_iff_le_exp (by positivity)).mpr ?_)
    have h := le_exp_nat_add 0 (f := ((61490995733:ℝ)/1250000000000)) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul h Real.pi_gt_d6.le (by norm_num) (Real.exp_pos _).le]
  have hU : Real.exp (((61490995733:ℝ)/1250000000000)/2) ≤ ((102490138508955743605239822849:ℝ)/100000000000000000000000000000) := by
    have h := exp_nat_add_le 0 (f := ((61490995733:ℝ)/1250000000000)/2) (by norm_num) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hE : ((601845030799949111306308502971:ℝ)/1000000000000000000000000000) ≤ Real.exp (2*((16:ℝ)/5)) := by
    have h := le_exp_nat_add 6 (f := ((2:ℝ)/5)) (by norm_num)
    rw [show (2:ℝ)*((16:ℝ)/5) = ((6:ℕ):ℝ) + ((2:ℝ)/5) by norm_num]
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  exact (seam_weight_le hr0 (by linarith [Real.pi_gt_d2]) hqb (by norm_num) hrL hU (by norm_num) hE).trans
    (by norm_num)

/-- **Seam piece 1** on `q ∈ [16/5, 33/10]`. -/
theorem piece1_integral (v : Fin 4 → ℝ) :
    -(((37223163646246657:ℝ)/2000000000000000000) * ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((108333464993:ℝ)/50000000000000) ((2714524041359:ℝ)/6250000000000) ((2685755187362937:ℝ)/15625000000000) ((194542508341031597:ℝ)/1953125000000) ((12997630273125191:ℝ)/78125000000000) ((712453569683996427:ℝ)/7812500000000) ((3709584384569511746969:ℝ)/61035156250000) ((1408019973641540975183:ℝ)/24414062500000) ((19973637489491006918533:ℝ)/488281250000) ((228131247383965215330727977:ℝ)/7629394531250) i j) ≤
      ∫ r in Real.log (((16:ℝ)/5)/Real.pi)..Real.log (((33:ℝ)/10)/Real.pi),
        thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have h := seam_piece_integral (ra' := Real.log (((16:ℝ)/5)/Real.pi)) (rc := Real.log (5/Real.pi)) (Ω := ((37223163646246657:ℝ)/2000000000000000000))
    le_rfl (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith [Real.pi_lt_d2]) Real.pi_pos.le))
    (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2]))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le)) piece1_X_psd
    (fun r hr y => by
      obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
      exact piece_1 (by linarith [Real.pi_gt_d2]) hqb y)
    (by norm_num) (fun r hr => piece1_weight hr) v
  rwa [piece1_frameIntegral] at h

theorem piece2_X_psd (y : Fin 4 → ℝ) : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceX_2 i j := by
  unfold pieceX_2
  exact quadForm_nonneg_of_ldl ((39518198237:ℝ)/4000000000000) ((80965686111385566697099:ℝ)/987954955925000000000000) ((1943010725471511106385739756386523:ℝ)/10120710763923195837137375000000000) ((6096426725881378364792838783537523815504059:ℝ)/38860214509430222127714795127730460000000000) ((-449637991398:ℝ)/197590991185) ((235441050648:ℝ)/28227284455) ((-779718910436:ℝ)/39518198237) ((-378671944286692354807418:ℝ)/80965686111385566697099) ((928832154182814038733340:ℝ)/80965686111385566697099) ((-11985667504785584605563169857343805:ℝ)/3886021450943022212771479512773046)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece2_frame (v : Fin 4 → ℝ) (q : ℝ) :
    frameForm pieceX_2 q v = ∑ e ∈ Finset.range 7, ([(((39518198237:ℝ)/4000000000000)*(v 0*v 0) + ((-39518198237:ℝ)/500000000000)*(v 0*v 1) + ((39518198237:ℝ)/125000000000)*(v 0*v 2) + ((-39518198237:ℝ)/31250000000)*(v 0*v 3) + ((39518198237:ℝ)/250000000000)*(v 1*v 1) + ((-39518198237:ℝ)/31250000000)*(v 1*v 2) + ((39518198237:ℝ)/7812500000)*(v 1*v 3) + ((39518198237:ℝ)/15625000000)*(v 2*v 2) + ((-39518198237:ℝ)/1953125000)*(v 2*v 3) + ((39518198237:ℝ)/976562500)*(v 3*v 3)), (((1941686947749:ℝ)/1250000000000)*(v 0*v 1) + ((-1941686947749:ℝ)/62500000000)*(v 0*v 2) + ((40775425902729:ℝ)/78125000000)*(v 0*v 3) + ((-1941686947749:ℝ)/312500000000)*(v 1*v 1) + ((5825060843247:ℝ)/39062500000)*(v 1*v 2) + ((-21358556425239:ℝ)/9765625000)*(v 1*v 3) + ((-1941686947749:ℝ)/3906250000)*(v 2*v 2) + ((25241930320737:ℝ)/2441406250)*(v 2*v 3) + ((-40775425902729:ℝ)/1220703125)*(v 3*v 3)), (((36230052864147:ℝ)/156250000000)*(v 0*v 2) + ((-253610370049029:ℝ)/19531250000)*(v 0*v 3) + ((33832073329749:ℝ)/312500000000)*(v 1*v 1) + ((-51347604878223:ℝ)/9765625000)*(v 1*v 2) + ((1217694280022787:ℝ)/9765625000)*(v 1*v 3) + ((918261938972019:ℝ)/19531250000)*(v 2*v 2) + ((-81916369851717:ℝ)/48828125)*(v 2*v 3) + ((637375432744617:ℝ)/48828125)*(v 3*v 3)), (((905182977090987:ℝ)/19531250000)*(v 0*v 3) + ((779508351146151:ℝ)/19531250000)*(v 1*v 2) + ((-11818299893137101:ℝ)/4882812500)*(v 1*v 3) + ((-779508351146151:ℝ)/976562500)*(v 2*v 2) + ((71840442931390728:ℝ)/1220703125)*(v 2*v 3) + ((-920322552856237524:ℝ)/1220703125)*(v 3*v 3)), (((20977672167763731:ℝ)/2441406250)*(v 1*v 3) + ((3870652911650037:ℝ)/976562500)*(v 2*v 2) + ((-150333625861728498:ℝ)/244140625)*(v 2*v 3) + ((18697208337852451848:ℝ)/1220703125)*(v 3*v 3)), (((429109657819660692:ℝ)/244140625)*(v 2*v 3) + ((-24030140837900998752:ℝ)/244140625)*(v 3*v 3)), (((48218895426159181584:ℝ)/244140625)*(v 3*v 3))] : List ℝ).getD e 0 * q^e := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3, pieceX_2, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem piece2_frameIntegral (v : Fin 4 → ℝ) :
    ∫ r in Real.log (((33:ℝ)/10)/Real.pi)..Real.log (((17:ℝ)/5)/Real.pi),
      Real.pi*Real.exp r * frameForm pieceX_2 (Real.pi*Real.exp r) v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((39518198237:ℝ)/40000000000000) ((128117115587333:ℝ)/500000000000000) ((78081945907801641:ℝ)/625000000000000) ((24980836300203656803:ℝ)/312500000000000) ((37325338281038671:ℝ)/312500000000000) ((22535669493293949861:ℝ)/312500000000000) ((484878454750165013981269:ℝ)/9765625000000000) ((45890590381178625737719:ℝ)/976562500000000) ((8138771783280007318714639:ℝ)/244140625000000) ((7318399947592934720004196677:ℝ)/305175781250000) i j := by
  simp_rw [piece2_frame v]
  rw [integral_exp_poly, pi_mul_exp_log_div (by norm_num), pi_mul_exp_log_div (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero, Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  push_cast
  ring

theorem piece2_weight {r : ℝ} (hr : r ∈ Set.Ioo (Real.log (((33:ℝ)/10)/Real.pi)) (Real.log (((17:ℝ)/5)/Real.pi))) :
    r^2 * pieceKernel r ≤ ((118084609638061753:ℝ)/2500000000000000000) := by
  obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
  have hr0 : 0 ≤ r := le_trans (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) hr.1.le
  have hrL : r ≤ ((395228813607:ℝ)/5000000000000) := by
    refine hr.2.le.trans ((Real.log_le_iff_le_exp (by positivity)).mpr ?_)
    have h := le_exp_nat_add 0 (f := ((395228813607:ℝ)/5000000000000)) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul h Real.pi_gt_d6.le (by norm_num) (Real.exp_pos _).le]
  have hU : Real.exp (((395228813607:ℝ)/5000000000000)/2) ≤ ((104031430241942333702459427217:ℝ)/100000000000000000000000000000) := by
    have h := exp_nat_add_le 0 (f := ((395228813607:ℝ)/5000000000000)/2) (by norm_num) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hE : ((18377375225309841891303449673:ℝ)/25000000000000000000000000) ≤ Real.exp (2*((33:ℝ)/10)) := by
    have h := le_exp_nat_add 6 (f := ((3:ℝ)/5)) (by norm_num)
    rw [show (2:ℝ)*((33:ℝ)/10) = ((6:ℕ):ℝ) + ((3:ℝ)/5) by norm_num]
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  exact (seam_weight_le hr0 (by linarith [Real.pi_gt_d2]) hqb (by norm_num) hrL hU (by norm_num) hE).trans
    (by norm_num)

/-- **Seam piece 2** on `q ∈ [33/10, 17/5]`. -/
theorem piece2_integral (v : Fin 4 → ℝ) :
    -(((118084609638061753:ℝ)/2500000000000000000) * ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((39518198237:ℝ)/40000000000000) ((128117115587333:ℝ)/500000000000000) ((78081945907801641:ℝ)/625000000000000) ((24980836300203656803:ℝ)/312500000000000) ((37325338281038671:ℝ)/312500000000000) ((22535669493293949861:ℝ)/312500000000000) ((484878454750165013981269:ℝ)/9765625000000000) ((45890590381178625737719:ℝ)/976562500000000) ((8138771783280007318714639:ℝ)/244140625000000) ((7318399947592934720004196677:ℝ)/305175781250000) i j) ≤
      ∫ r in Real.log (((33:ℝ)/10)/Real.pi)..Real.log (((17:ℝ)/5)/Real.pi),
        thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have h := seam_piece_integral (ra' := Real.log (((33:ℝ)/10)/Real.pi)) (rc := Real.log (5/Real.pi)) (Ω := ((118084609638061753:ℝ)/2500000000000000000))
    le_rfl (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith [Real.pi_lt_d2]) Real.pi_pos.le))
    (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2]))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le)) piece2_X_psd
    (fun r hr y => by
      obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
      exact piece_2 (by linarith [Real.pi_gt_d2]) hqb y)
    (by norm_num) (fun r hr => piece2_weight hr) v
  rwa [piece2_frameIntegral] at h

theorem piece3_X_psd (y : Fin 4 → ℝ) : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceX_3 i j := by
  unfold pieceX_3
  exact quadForm_nonneg_of_ldl ((323892437917:ℝ)/50000000000000) ((19176166210089057329073:ℝ)/323892437917000000000000) ((1781114136597143382108147182024897:ℝ)/19176166210089057329073000000000000) ((2445597409725804947844269339555613041215211:ℝ)/35622282731942867642162943640497940000000000) ((-936756546350:ℝ)/323892437917) ((3587607628910:ℝ)/323892437917) ((-8042719282650:ℝ)/323892437917) ((-87061268058810169785055:ℝ)/19176166210089057329073) ((66521351595393591896340:ℝ)/6392055403363019109691) ((-5055555943766631230410014902051370:ℝ)/1781114136597143382108147182024897)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece3_frame (v : Fin 4 → ℝ) (q : ℝ) :
    frameForm pieceX_3 q v = ∑ e ∈ Finset.range 7, ([(((323892437917:ℝ)/50000000000000)*(v 0*v 0) + ((-323892437917:ℝ)/6250000000000)*(v 0*v 1) + ((323892437917:ℝ)/1562500000000)*(v 0*v 2) + ((-323892437917:ℝ)/390625000000)*(v 0*v 3) + ((323892437917:ℝ)/3125000000000)*(v 1*v 1) + ((-323892437917:ℝ)/390625000000)*(v 1*v 2) + ((323892437917:ℝ)/97656250000)*(v 1*v 3) + ((323892437917:ℝ)/195312500000)*(v 2*v 2) + ((-323892437917:ℝ)/24414062500)*(v 2*v 3) + ((323892437917:ℝ)/12207031250)*(v 3*v 3)), (((3781946952801:ℝ)/3125000000000)*(v 0*v 1) + ((-3781946952801:ℝ)/156250000000)*(v 0*v 2) + ((79420886008821:ℝ)/195312500000)*(v 0*v 3) + ((-3781946952801:ℝ)/781250000000)*(v 1*v 1) + ((11345840858403:ℝ)/97656250000)*(v 1*v 2) + ((-41601416480811:ℝ)/24414062500)*(v 1*v 3) + ((-3781946952801:ℝ)/9765625000)*(v 2*v 2) + ((49165310386413:ℝ)/6103515625)*(v 2*v 3) + ((-158841772017642:ℝ)/6103515625)*(v 3*v 3)), (((3040494980247:ℝ)/15625000000)*(v 0*v 2) + ((-21283464861729:ℝ)/1953125000)*(v 0*v 3) + ((70802509919103:ℝ)/781250000000)*(v 1*v 1) + ((-43002492410169:ℝ)/9765625000)*(v 1*v 2) + ((2551025951387613:ℝ)/24414062500)*(v 1*v 3) + ((76883499879597:ℝ)/1953125000)*(v 2*v 2) + ((-1714889831819688:ℝ)/1220703125)*(v 2*v 3) + ((66704506720994646:ℝ)/6103515625)*(v 3*v 3)), (((381750512061891:ℝ)/9765625000)*(v 0*v 3) + ((65512835310591:ℝ)/1953125000)*(v 1*v 2) + ((-4967648983803261:ℝ)/2441406250)*(v 1*v 3) + ((-65512835310591:ℝ)/97656250)*(v 2*v 2) + ((60380181156761592:ℝ)/1220703125)*(v 2*v 3) + ((-773484947349045288:ℝ)/1220703125)*(v 3*v 3)), (((8601804904774473:ℝ)/1220703125)*(v 1*v 3) + ((1585405770981957:ℝ)/488281250)*(v 2*v 2) + ((-123189942794087484:ℝ)/244140625)*(v 2*v 3) + ((15319787692502765808:ℝ)/1220703125)*(v 3*v 3)), (((338817612095604936:ℝ)/244140625)*(v 2*v 3) + ((-18973786277353876416:ℝ)/244140625)*(v 3*v 3)), (((7297548753866251104:ℝ)/48828125)*(v 3*v 3))] : List ℝ).getD e 0 * q^e := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3, pieceX_3, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem piece3_frameIntegral (v : Fin 4 → ℝ) :
    ∫ r in Real.log (((17:ℝ)/5)/Real.pi)..Real.log (((7:ℝ)/2)/Real.pi),
      Real.pi*Real.exp r * frameForm pieceX_3 (Real.pi*Real.exp r) v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((323892437917:ℝ)/500000000000000) ((257715415364099:ℝ)/1250000000000000) ((6978098494773923:ℝ)/62500000000000) ((57705294363489354689:ℝ)/781250000000000) ((82981913252603851:ℝ)/781250000000000) ((10356664773511943023:ℝ)/156250000000000) ((223724046462750539547667:ℝ)/4882812500000000) ((21147234937879686798589:ℝ)/488281250000000) ((3718717527675102910198919:ℝ)/122070312500000) ((3296177899989591921574734047:ℝ)/152587890625000) i j := by
  simp_rw [piece3_frame v]
  rw [integral_exp_poly, pi_mul_exp_log_div (by norm_num), pi_mul_exp_log_div (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero, Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  push_cast
  ring

theorem piece3_weight {r : ℝ} (hr : r ∈ Set.Ioo (Real.log (((17:ℝ)/5)/Real.pi)) (Real.log (((7:ℝ)/2)/Real.pi))) :
    r^2 * pieceKernel r ≤ ((430277766733877081:ℝ)/5000000000000000000) := by
  obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
  have hr0 : 0 ≤ r := le_trans (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) hr.1.le
  have hrL : r ≤ ((108033302493:ℝ)/1000000000000) := by
    refine hr.2.le.trans ((Real.log_le_iff_le_exp (by positivity)).mpr ?_)
    have h := le_exp_nat_add 0 (f := ((108033302493:ℝ)/1000000000000)) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul h Real.pi_gt_d6.le (by norm_num) (Real.exp_pos _).le]
  have hU : Real.exp (((108033302493:ℝ)/1000000000000)/2) ≤ ((105550217743569245191762125847:ℝ)/100000000000000000000000000000) := by
    have h := exp_nat_add_le 0 (f := ((108033302493:ℝ)/1000000000000)/2) (by norm_num) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hE : ((179569090115825204277163367037:ℝ)/200000000000000000000000000) ≤ Real.exp (2*((17:ℝ)/5)) := by
    have h := le_exp_nat_add 6 (f := ((4:ℝ)/5)) (by norm_num)
    rw [show (2:ℝ)*((17:ℝ)/5) = ((6:ℕ):ℝ) + ((4:ℝ)/5) by norm_num]
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  exact (seam_weight_le hr0 (by linarith [Real.pi_gt_d2]) hqb (by norm_num) hrL hU (by norm_num) hE).trans
    (by norm_num)

/-- **Seam piece 3** on `q ∈ [17/5, 7/2]`. -/
theorem piece3_integral (v : Fin 4 → ℝ) :
    -(((430277766733877081:ℝ)/5000000000000000000) * ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((323892437917:ℝ)/500000000000000) ((257715415364099:ℝ)/1250000000000000) ((6978098494773923:ℝ)/62500000000000) ((57705294363489354689:ℝ)/781250000000000) ((82981913252603851:ℝ)/781250000000000) ((10356664773511943023:ℝ)/156250000000000) ((223724046462750539547667:ℝ)/4882812500000000) ((21147234937879686798589:ℝ)/488281250000000) ((3718717527675102910198919:ℝ)/122070312500000) ((3296177899989591921574734047:ℝ)/152587890625000) i j) ≤
      ∫ r in Real.log (((17:ℝ)/5)/Real.pi)..Real.log (((7:ℝ)/2)/Real.pi),
        thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have h := seam_piece_integral (ra' := Real.log (((17:ℝ)/5)/Real.pi)) (rc := Real.log (5/Real.pi)) (Ω := ((430277766733877081:ℝ)/5000000000000000000))
    le_rfl (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith [Real.pi_lt_d2]) Real.pi_pos.le))
    (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2]))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le)) piece3_X_psd
    (fun r hr y => by
      obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
      exact piece_3 (by linarith [Real.pi_gt_d2]) hqb y)
    (by norm_num) (fun r hr => piece3_weight hr) v
  rwa [piece3_frameIntegral] at h

theorem piece4_X_psd (y : Fin 4 → ℝ) : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceX_4 i j := by
  unfold pieceX_4
  exact quadForm_nonneg_of_ldl ((244876469633:ℝ)/50000000000000) ((13283691369027961603403:ℝ)/306095587041250000000000) ((2798536991650510329592011510515173:ℝ)/53134765476111846413612000000000000) ((10190318031262132566859352933631284820272857:ℝ)/279853699165051032959201151051517300000000000) ((-800802254750:ℝ)/244876469633) ((3031524777305:ℝ)/244876469633) ((-6394831139000:ℝ)/244876469633) ((-230430358106930242511725:ℝ)/53134765476111846413612) ((123522414302244045832540:ℝ)/13283691369027961603403) ((-7354033080175686963155795137989360:ℝ)/2798536991650510329592011510515173)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece4_frame (v : Fin 4 → ℝ) (q : ℝ) :
    frameForm pieceX_4 q v = ∑ e ∈ Finset.range 7, ([(((244876469633:ℝ)/50000000000000)*(v 0*v 0) + ((-244876469633:ℝ)/6250000000000)*(v 0*v 1) + ((244876469633:ℝ)/1562500000000)*(v 0*v 2) + ((-244876469633:ℝ)/390625000000)*(v 0*v 3) + ((244876469633:ℝ)/3125000000000)*(v 1*v 1) + ((-244876469633:ℝ)/390625000000)*(v 1*v 2) + ((244876469633:ℝ)/97656250000)*(v 1*v 3) + ((244876469633:ℝ)/195312500000)*(v 2*v 2) + ((-244876469633:ℝ)/24414062500)*(v 2*v 3) + ((244876469633:ℝ)/12207031250)*(v 3*v 3)), (((3137036173149:ℝ)/3125000000000)*(v 0*v 1) + ((-3137036173149:ℝ)/156250000000)*(v 0*v 2) + ((65877759636129:ℝ)/195312500000)*(v 0*v 3) + ((-3137036173149:ℝ)/781250000000)*(v 1*v 1) + ((9411108519447:ℝ)/97656250000)*(v 1*v 2) + ((-34507397904639:ℝ)/24414062500)*(v 1*v 3) + ((-3137036173149:ℝ)/9765625000)*(v 2*v 2) + ((40781470250937:ℝ)/6103515625)*(v 2*v 3) + ((-131755519272258:ℝ)/6103515625)*(v 3*v 3)), (((12815102402931:ℝ)/78125000000)*(v 0*v 2) + ((-89705716820517:ℝ)/9765625000)*(v 0*v 3) + ((59716333163457:ℝ)/781250000000)*(v 1*v 1) + ((-18132858891597:ℝ)/4882812500)*(v 1*v 2) + ((2151100164637767:ℝ)/24414062500)*(v 1*v 3) + ((324211870623147:ℝ)/9765625000)*(v 2*v 2) + ((-1446269532476562:ℝ)/1220703125)*(v 2*v 3) + ((56258034522989754:ℝ)/6103515625)*(v 3*v 3)), (((63162991964583:ℝ)/1953125000)*(v 0*v 3) + ((270980235338463:ℝ)/9765625000)*(v 1*v 2) + ((-4109538254561397:ℝ)/2441406250)*(v 1*v 3) + ((-270980235338463:ℝ)/488281250)*(v 2*v 2) + ((49950032751246096:ℝ)/1220703125)*(v 2*v 3) + ((-639872033194648296:ℝ)/1220703125)*(v 3*v 3)), (((1379127648285387:ℝ)/244140625)*(v 1*v 3) + ((1270003782733209:ℝ)/488281250)*(v 2*v 2) + ((-98702764798767444:ℝ)/244140625)*(v 2*v 3) + ((2454752821149561744:ℝ)/244140625)*(v 3*v 3)), (((261694963142443656:ℝ)/244140625)*(v 2*v 3) + ((-14654917935976844736:ℝ)/244140625)*(v 3*v 3)), (((27111503029835425824:ℝ)/244140625)*(v 3*v 3))] : List ℝ).getD e 0 * q^e := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3, pieceX_4, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem piece4_frameIntegral (v : Fin 4 → ℝ) :
    ∫ r in Real.log (((7:ℝ)/2)/Real.pi)..Real.log (((18:ℝ)/5)/Real.pi),
      Real.pi*Real.exp r * frameForm pieceX_4 (Real.pi*Real.exp r) v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((244876469633:ℝ)/500000000000000) ((220280803597249:ℝ)/1250000000000000) ((31191402380216509:ℝ)/312500000000000) ((10410483998275947339:ℝ)/156250000000000) ((74154959300616569:ℝ)/781250000000000) ((46688086870740728753:ℝ)/781250000000000) ((40200945997723745725593:ℝ)/976562500000000) ((18986384189963238539943:ℝ)/488281250000000) ((3310194118981638857959807:ℝ)/122070312500000) ((2902213869338871401300298437:ℝ)/152587890625000) i j := by
  simp_rw [piece4_frame v]
  rw [integral_exp_poly, pi_mul_exp_log_div (by norm_num), pi_mul_exp_log_div (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero, Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  push_cast
  ring

theorem piece4_weight {r : ℝ} (hr : r ∈ Set.Ioo (Real.log (((7:ℝ)/2)/Real.pi)) (Real.log (((18:ℝ)/5)/Real.pi))) :
    r^2 * pieceKernel r ≤ ((264959461198715009:ℝ)/2000000000000000000) := by
  obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
  have hr0 : 0 ≤ r := le_trans (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) hr.1.le
  have hrL : r ≤ ((136204182277:ℝ)/1000000000000) := by
    refine hr.2.le.trans ((Real.log_le_iff_le_exp (by positivity)).mpr ?_)
    have h := le_exp_nat_add 0 (f := ((136204182277:ℝ)/1000000000000)) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul h Real.pi_gt_d6.le (by norm_num) (Real.exp_pos _).le]
  have hU : Real.exp (((136204182277:ℝ)/1000000000000)/2) ≤ ((107047458886991407252776136637:ℝ)/100000000000000000000000000000) := by
    have h := exp_nat_add_le 0 (f := ((136204182277:ℝ)/1000000000000)/2) (by norm_num) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hE : ((109663315797931460745737569441:ℝ)/100000000000000000000000000) ≤ Real.exp (2*((7:ℝ)/2)) := by
    have h := le_exp_nat_add 7 (f := (0:ℝ)) (by norm_num)
    rw [show (2:ℝ)*((7:ℝ)/2) = ((7:ℕ):ℝ) + (0:ℝ) by norm_num]
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  exact (seam_weight_le hr0 (by linarith [Real.pi_gt_d2]) hqb (by norm_num) hrL hU (by norm_num) hE).trans
    (by norm_num)

/-- **Seam piece 4** on `q ∈ [7/2, 18/5]`. -/
theorem piece4_integral (v : Fin 4 → ℝ) :
    -(((264959461198715009:ℝ)/2000000000000000000) * ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((244876469633:ℝ)/500000000000000) ((220280803597249:ℝ)/1250000000000000) ((31191402380216509:ℝ)/312500000000000) ((10410483998275947339:ℝ)/156250000000000) ((74154959300616569:ℝ)/781250000000000) ((46688086870740728753:ℝ)/781250000000000) ((40200945997723745725593:ℝ)/976562500000000) ((18986384189963238539943:ℝ)/488281250000000) ((3310194118981638857959807:ℝ)/122070312500000) ((2902213869338871401300298437:ℝ)/152587890625000) i j) ≤
      ∫ r in Real.log (((7:ℝ)/2)/Real.pi)..Real.log (((18:ℝ)/5)/Real.pi),
        thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have h := seam_piece_integral (ra' := Real.log (((7:ℝ)/2)/Real.pi)) (rc := Real.log (5/Real.pi)) (Ω := ((264959461198715009:ℝ)/2000000000000000000))
    le_rfl (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith [Real.pi_lt_d2]) Real.pi_pos.le))
    (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2]))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le)) piece4_X_psd
    (fun r hr y => by
      obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
      exact piece_4 (by linarith [Real.pi_gt_d2]) hqb y)
    (by norm_num) (fun r hr => piece4_weight hr) v
  rwa [piece4_frameIntegral] at h

theorem piece5_X_psd (y : Fin 4 → ℝ) : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceX_5 i j := by
  unfold pieceX_5
  exact quadForm_nonneg_of_ldl ((196070506143:ℝ)/50000000000000) ((31675438687990501613429:ℝ)/980352530715000000000000) ((190934559209078189030898854571893:ℝ)/5759170670543727566078000000000000) ((1139589493020849439137811232241265181306991:ℝ)/52507003782496501983497185007270575000000000) ((-673264258790:ℝ)/196070506143) ((822411767345:ℝ)/65356835381) ((-4889830829020:ℝ)/196070506143) ((-11869744571316213293625:ℝ)/2879585335271863783039) ((262203977271369563584120:ℝ)/31675438687990501613429) ((-465714242749268632692139725353996:ℝ)/190934559209078189030898854571893)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece5_frame (v : Fin 4 → ℝ) (q : ℝ) :
    frameForm pieceX_5 q v = ∑ e ∈ Finset.range 7, ([(((196070506143:ℝ)/50000000000000)*(v 0*v 0) + ((-196070506143:ℝ)/6250000000000)*(v 0*v 1) + ((196070506143:ℝ)/1562500000000)*(v 0*v 2) + ((-196070506143:ℝ)/390625000000)*(v 0*v 3) + ((196070506143:ℝ)/3125000000000)*(v 1*v 1) + ((-196070506143:ℝ)/390625000000)*(v 1*v 2) + ((196070506143:ℝ)/97656250000)*(v 1*v 3) + ((196070506143:ℝ)/195312500000)*(v 2*v 2) + ((-196070506143:ℝ)/24414062500)*(v 2*v 3) + ((196070506143:ℝ)/12207031250)*(v 3*v 3)), (((2608004294799:ℝ)/3125000000000)*(v 0*v 1) + ((-2608004294799:ℝ)/156250000000)*(v 0*v 2) + ((54768090190779:ℝ)/195312500000)*(v 0*v 3) + ((-2608004294799:ℝ)/781250000000)*(v 1*v 1) + ((7824012884397:ℝ)/97656250000)*(v 1*v 2) + ((-28688047242789:ℝ)/24414062500)*(v 1*v 3) + ((-2608004294799:ℝ)/9765625000)*(v 2*v 2) + ((33904055832387:ℝ)/6103515625)*(v 2*v 3) + ((-109536180381558:ℝ)/6103515625)*(v 3*v 3)), (((10549161796053:ℝ)/78125000000)*(v 0*v 2) + ((-73844132572371:ℝ)/9765625000)*(v 0*v 3) + ((49229616802077:ℝ)/781250000000)*(v 1*v 1) + ((-5977877859813:ℝ)/1953125000)*(v 1*v 2) + ((1772263278567327:ℝ)/24414062500)*(v 1*v 3) + ((267246407602491:ℝ)/9765625000)*(v 2*v 2) + ((-1192059379784412:ℝ)/1220703125)*(v 2*v 3) + ((46374287322326754:ℝ)/6103515625)*(v 3*v 3)), (((253030946082873:ℝ)/9765625000)*(v 0*v 3) + ((217343632008969:ℝ)/9765625000)*(v 1*v 2) + ((-3295841794208439:ℝ)/2441406250)*(v 1*v 3) + ((-217343632008969:ℝ)/488281250)*(v 2*v 2) + ((40062602917798104:ℝ)/1220703125)*(v 2*v 3) + ((-513216470053758072:ℝ)/1220703125)*(v 3*v 3)), (((5351854239163719:ℝ)/1220703125)*(v 1*v 3) + ((985175567144271:ℝ)/488281250)*(v 2*v 2) + ((-76577248716734052:ℝ)/244140625)*(v 2*v 3) + ((9521999470770094224:ℝ)/1220703125)*(v 3*v 3)), (((195995760091468344:ℝ)/244140625)*(v 2*v 3) + ((-10975762565122227264:ℝ)/244140625)*(v 3*v 3)), (((19584417995043735456:ℝ)/244140625)*(v 3*v 3))] : List ℝ).getD e 0 * q^e := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3, pieceX_5, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem piece5_frameIntegral (v : Fin 4 → ℝ) :
    ∫ r in Real.log (((18:ℝ)/5)/Real.pi)..Real.log (((37:ℝ)/10)/Real.pi),
      Real.pi*Real.exp r * frameForm pieceX_5 (Real.pi*Real.exp r) v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((196070506143:ℝ)/500000000000000) ((188423608458897:ℝ)/1250000000000000) ((27160038936675689:ℝ)/312500000000000) ((9066093306518191399:ℝ)/156250000000000) ((64643239647685863:ℝ)/781250000000000) ((1628064606156025681:ℝ)/31250000000000) ((174255698891111153005081:ℝ)/4882812500000000) ((16453023458878010562127:ℝ)/488281250000000) ((2846053048885498266906657:ℝ)/122070312500000) ((2473184782468192281937562797:ℝ)/152587890625000) i j := by
  simp_rw [piece5_frame v]
  rw [integral_exp_poly, pi_mul_exp_log_div (by norm_num), pi_mul_exp_log_div (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero, Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  push_cast
  ring

theorem piece5_weight {r : ℝ} (hr : r ∈ Set.Ioo (Real.log (((18:ℝ)/5)/Real.pi)) (Real.log (((37:ℝ)/10)/Real.pi))) :
    r^2 * pieceKernel r ≤ ((1839280032007880133:ℝ)/10000000000000000000) := by
  obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
  have hr0 : 0 ≤ r := le_trans (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) hr.1.le
  have hrL : r ≤ ((32720631841:ℝ)/200000000000) := by
    refine hr.2.le.trans ((Real.log_le_iff_le_exp (by positivity)).mpr ?_)
    have h := le_exp_nat_add 0 (f := ((32720631841:ℝ)/200000000000)) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul h Real.pi_gt_d6.le (by norm_num) (Real.exp_pos _).le]
  have hU : Real.exp (((32720631841:ℝ)/200000000000)/2) ≤ ((108524045462243921117231568249:ℝ)/100000000000000000000000000000) := by
    have h := exp_nat_add_le 0 (f := ((32720631841:ℝ)/200000000000)/2) (by norm_num) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hE : ((133943076377462582163901314607:ℝ)/100000000000000000000000000) ≤ Real.exp (2*((18:ℝ)/5)) := by
    have h := le_exp_nat_add 7 (f := ((1:ℝ)/5)) (by norm_num)
    rw [show (2:ℝ)*((18:ℝ)/5) = ((7:ℕ):ℝ) + ((1:ℝ)/5) by norm_num]
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  exact (seam_weight_le hr0 (by linarith [Real.pi_gt_d2]) hqb (by norm_num) hrL hU (by norm_num) hE).trans
    (by norm_num)

/-- **Seam piece 5** on `q ∈ [18/5, 37/10]`. -/
theorem piece5_integral (v : Fin 4 → ℝ) :
    -(((1839280032007880133:ℝ)/10000000000000000000) * ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((196070506143:ℝ)/500000000000000) ((188423608458897:ℝ)/1250000000000000) ((27160038936675689:ℝ)/312500000000000) ((9066093306518191399:ℝ)/156250000000000) ((64643239647685863:ℝ)/781250000000000) ((1628064606156025681:ℝ)/31250000000000) ((174255698891111153005081:ℝ)/4882812500000000) ((16453023458878010562127:ℝ)/488281250000000) ((2846053048885498266906657:ℝ)/122070312500000) ((2473184782468192281937562797:ℝ)/152587890625000) i j) ≤
      ∫ r in Real.log (((18:ℝ)/5)/Real.pi)..Real.log (((37:ℝ)/10)/Real.pi),
        thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have h := seam_piece_integral (ra' := Real.log (((18:ℝ)/5)/Real.pi)) (rc := Real.log (5/Real.pi)) (Ω := ((1839280032007880133:ℝ)/10000000000000000000))
    le_rfl (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith [Real.pi_lt_d2]) Real.pi_pos.le))
    (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2]))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le)) piece5_X_psd
    (fun r hr y => by
      obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
      exact piece_5 (by linarith [Real.pi_gt_d2]) hqb y)
    (by norm_num) (fun r hr => piece5_weight hr) v
  rwa [piece5_frameIntegral] at h

end
end RHTower.ThetaCuspOddFourPieces
