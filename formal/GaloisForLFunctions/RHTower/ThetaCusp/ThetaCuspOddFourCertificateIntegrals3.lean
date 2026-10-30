import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourPieceIntegral
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourCertificatePieces4
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourCertificatePieces5

/-!
# Piece integrals 12–17

For each piece: the compensation matrix is positive semidefinite (seam) or negative semidefinite (bulk) by an exact `LDLᵀ` factorization, the weight
`r²κ(r)` is bounded above (seam) or below (bulk) by a rational constant on the piece, and the moving-frame form integrates
exactly against `π e^r dr = dq`. Together with the piece certificate this bounds the seam-split
integral over the piece by an explicit quadratic form in `v`.
-/

namespace RHTower.ThetaCuspOddFourPieces
noncomputable section
open ThetaCuspOddCentral ThetaCuspOddFourCertificateTools

theorem piece12_X_psd (y : Fin 4 → ℝ) : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceX_12 i j := by
  unfold pieceX_12
  exact quadForm_nonneg_of_ldl ((131617542713:ℝ)/500000000000000) ((16302893954924601422453:ℝ)/52647017085200000000000000) ((4841815845721892181417780075526593899:ℝ)/8151446977462300711226500000000000000000) ((1636360445710603450909975394590341340067470241623:ℝ)/2420907922860946090708890037763296949500000000000000) ((-109527364439:ℝ)/263235085426) ((597725921551:ℝ)/2632350854260) ((-300046773823:ℝ)/2632350854260) ((-753566846433307290013931:ℝ)/815144697746230071122650) ((467844025097390082042423:ℝ)/815144697746230071122650) ((-4832882069848797322939325648006966617:ℝ)/4841815845721892181417780075526593899)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece12_frame (v : Fin 4 → ℝ) (q : ℝ) :
    frameForm pieceX_12 q v = ∑ e ∈ Finset.range 7, ([(((131617542713:ℝ)/500000000000000)*(v 0*v 0) + ((-131617542713:ℝ)/62500000000000)*(v 0*v 1) + ((131617542713:ℝ)/15625000000000)*(v 0*v 2) + ((-131617542713:ℝ)/3906250000000)*(v 0*v 3) + ((131617542713:ℝ)/31250000000000)*(v 1*v 1) + ((-131617542713:ℝ)/3906250000000)*(v 1*v 2) + ((131617542713:ℝ)/976562500000)*(v 1*v 3) + ((131617542713:ℝ)/1953125000000)*(v 2*v 2) + ((-131617542713:ℝ)/244140625000)*(v 2*v 3) + ((131617542713:ℝ)/122070312500)*(v 3*v 3)), (((223657469919:ℝ)/12500000000000)*(v 0*v 1) + ((-223657469919:ℝ)/625000000000)*(v 0*v 2) + ((4696806868299:ℝ)/781250000000)*(v 0*v 3) + ((-223657469919:ℝ)/3125000000000)*(v 1*v 1) + ((670972409757:ℝ)/390625000000)*(v 1*v 2) + ((-2460232169109:ℝ)/97656250000)*(v 1*v 3) + ((-223657469919:ℝ)/39062500000)*(v 2*v 2) + ((2907547108947:ℝ)/24414062500)*(v 2*v 3) + ((-4696806868299:ℝ)/12207031250)*(v 3*v 3)), (((19879045801053:ℝ)/19531250000000)*(v 0*v 2) + ((-139153320607371:ℝ)/2441406250000)*(v 0*v 3) + ((1507547385657:ℝ)/3125000000000)*(v 1*v 1) + ((-228201514809231:ℝ)/9765625000000)*(v 1*v 2) + ((1348075659899409:ℝ)/2441406250000)*(v 1*v 3) + ((1021733299239837:ℝ)/4882812500000)*(v 2*v 2) + ((-910736652276243:ℝ)/122070312500)*(v 2*v 3) + ((17733936491727393:ℝ)/305175781250)*(v 3*v 3)), (((398619449456067:ℝ)/4882812500000)*(v 0*v 3) + ((359779872670803:ℝ)/4882812500000)*(v 1*v 2) + ((-5435537666847309:ℝ)/1220703125000)*(v 1*v 3) + ((-359779872670803:ℝ)/244140625000)*(v 2*v 2) + ((3313858786249914:ℝ)/30517578125)*(v 2*v 3) + ((-212347804029344298:ℝ)/152587890625)*(v 3*v 3)), (((4462640572883031:ℝ)/610351562500)*(v 1*v 3) + ((424326232835343:ℝ)/122070312500)*(v 2*v 2) + ((-3268755018454527:ℝ)/6103515625)*(v 2*v 3) + ((2038220640836719164:ℝ)/152587890625)*(v 3*v 3)), (((24777002349881334:ℝ)/30517578125)*(v 2*v 3) + ((-1387512131593354704:ℝ)/30517578125)*(v 3*v 3)), (((1647784613247647112:ℝ)/30517578125)*(v 3*v 3))] : List ℝ).getD e 0 * q^e := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3, pieceX_12, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem piece12_frameIntegral (v : Fin 4 → ℝ) :
    ∫ r in Real.log (((22:ℝ)/5)/Real.pi)..Real.log (((23:ℝ)/5)/Real.pi),
      Real.pi*Real.exp r * frameForm pieceX_12 (Real.pi*Real.exp r) v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((131617542713:ℝ)/2500000000000000) ((9801351060929:ℝ)/1250000000000000) ((74265926235671727:ℝ)/39062500000000000) ((9867977985519863:ℝ)/15625000000000) ((184622267857139:ℝ)/97656250000000) ((122111151976864281:ℝ)/195312500000000) ((39768666717881860411453:ℝ)/152587890625000000) ((3957144290931867730759:ℝ)/15258789062500000) ((49230937266201510797797:ℝ)/381469726562500) ((353610476533046868383937321:ℝ)/4768371582031250) i j := by
  simp_rw [piece12_frame v]
  rw [integral_exp_poly, pi_mul_exp_log_div (by norm_num), pi_mul_exp_log_div (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero, Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  push_cast
  ring

theorem piece12_weight {r : ℝ} (hr : r ∈ Set.Ioo (Real.log (((22:ℝ)/5)/Real.pi)) (Real.log (((23:ℝ)/5)/Real.pi))) :
    r^2 * pieceKernel r ≤ ((215728177935400971:ℝ)/312500000000000000) := by
  obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
  have hr0 : 0 ≤ r := le_trans (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) hr.1.le
  have hrL : r ≤ ((190663332411:ℝ)/500000000000) := by
    refine hr.2.le.trans ((Real.log_le_iff_le_exp (by positivity)).mpr ?_)
    have h := le_exp_nat_add 0 (f := ((190663332411:ℝ)/500000000000)) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul h Real.pi_gt_d6.le (by norm_num) (Real.exp_pos _).le]
  have hU : Real.exp (((190663332411:ℝ)/500000000000)/2) ≤ ((30251299955314223159120450731:ℝ)/25000000000000000000000000000) := by
    have h := exp_nat_add_le 0 (f := ((190663332411:ℝ)/500000000000)/2) (by norm_num) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hE : ((663423040172249819244905366771:ℝ)/100000000000000000000000000) ≤ Real.exp (2*((22:ℝ)/5)) := by
    have h := le_exp_nat_add 8 (f := ((4:ℝ)/5)) (by norm_num)
    rw [show (2:ℝ)*((22:ℝ)/5) = ((8:ℕ):ℝ) + ((4:ℝ)/5) by norm_num]
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  exact (seam_weight_le hr0 (by linarith [Real.pi_gt_d2]) hqb (by norm_num) hrL hU (by norm_num) hE).trans
    (by norm_num)

/-- **Seam piece 12** on `q ∈ [22/5, 23/5]`. -/
theorem piece12_integral (v : Fin 4 → ℝ) :
    -(((215728177935400971:ℝ)/312500000000000000) * ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((131617542713:ℝ)/2500000000000000) ((9801351060929:ℝ)/1250000000000000) ((74265926235671727:ℝ)/39062500000000000) ((9867977985519863:ℝ)/15625000000000) ((184622267857139:ℝ)/97656250000000) ((122111151976864281:ℝ)/195312500000000) ((39768666717881860411453:ℝ)/152587890625000000) ((3957144290931867730759:ℝ)/15258789062500000) ((49230937266201510797797:ℝ)/381469726562500) ((353610476533046868383937321:ℝ)/4768371582031250) i j) ≤
      ∫ r in Real.log (((22:ℝ)/5)/Real.pi)..Real.log (((23:ℝ)/5)/Real.pi),
        thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have h := seam_piece_integral (ra' := Real.log (((22:ℝ)/5)/Real.pi)) (rc := Real.log (5/Real.pi)) (Ω := ((215728177935400971:ℝ)/312500000000000000))
    le_rfl (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith [Real.pi_lt_d2]) Real.pi_pos.le))
    (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2]))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le)) piece12_X_psd
    (fun r hr y => by
      obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
      exact piece_12 (by linarith [Real.pi_gt_d2]) hqb y)
    (by norm_num) (fun r hr => piece12_weight hr) v
  rwa [piece12_frameIntegral] at h

theorem piece13_X_psd (y : Fin 4 → ℝ) : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceX_13 i j := by
  unfold pieceX_13
  exact quadForm_nonneg_of_ldl ((126070965019:ℝ)/500000000000000) ((1713983457671478633758039:ℝ)/6303548250950000000000000000) ((819483300215579320209297363201400443:ℝ)/1713983457671478633758039000000000000000) ((544965211780009230739846074859869513950971675011:ℝ)/1092644400287439093612396484268533924000000000000000) ((-448589656181:ℝ)/1260709650190) ((21184760960:ℝ)/126070965019) ((-191827955379:ℝ)/2521419300380) ((-1334740894684632939758650:ℝ)/1713983457671478633758039) ((1439504949133984925473801:ℝ)/3427966915342957267516078) ((-452366047408697700029431324454100737:ℝ)/546322200143719546806198242134266962)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece13_frame (v : Fin 4 → ℝ) (q : ℝ) :
    frameForm pieceX_13 q v = ∑ e ∈ Finset.range 7, ([(((126070965019:ℝ)/500000000000000)*(v 0*v 0) + ((-126070965019:ℝ)/62500000000000)*(v 0*v 1) + ((126070965019:ℝ)/15625000000000)*(v 0*v 2) + ((-126070965019:ℝ)/3906250000000)*(v 0*v 3) + ((126070965019:ℝ)/31250000000000)*(v 1*v 1) + ((-126070965019:ℝ)/3906250000000)*(v 1*v 2) + ((126070965019:ℝ)/976562500000)*(v 1*v 3) + ((126070965019:ℝ)/1953125000000)*(v 2*v 2) + ((-126070965019:ℝ)/244140625000)*(v 2*v 3) + ((126070965019:ℝ)/122070312500)*(v 3*v 3)), (((5127897919113:ℝ)/312500000000000)*(v 0*v 1) + ((-5127897919113:ℝ)/15625000000000)*(v 0*v 2) + ((107685856301373:ℝ)/19531250000000)*(v 0*v 3) + ((-5127897919113:ℝ)/78125000000000)*(v 1*v 1) + ((15383693757339:ℝ)/9765625000000)*(v 1*v 2) + ((-56406877110243:ℝ)/2441406250000)*(v 1*v 3) + ((-5127897919113:ℝ)/976562500000)*(v 2*v 2) + ((66662672948469:ℝ)/610351562500)*(v 2*v 3) + ((-107685856301373:ℝ)/305175781250)*(v 3*v 3)), (((872762643837:ℝ)/976562500000)*(v 0*v 2) + ((-6109338506859:ℝ)/122070312500)*(v 0*v 3) + ((2068338464253:ℝ)/4882812500000)*(v 1*v 1) + ((-5009439572343:ℝ)/244140625000)*(v 1*v 2) + ((73981800283608:ℝ)/152587890625)*(v 1*v 3) + ((5607227482551:ℝ)/30517578125)*(v 2*v 2) + ((-199923310312362:ℝ)/30517578125)*(v 2*v 3) + ((7785845182433304:ℝ)/152587890625)*(v 3*v 3)), (((335122626712083:ℝ)/4882812500000)*(v 0*v 3) + ((60493975460577:ℝ)/976562500000)*(v 1*v 2) + ((-4569700908952473:ℝ)/1220703125000)*(v 1*v 3) + ((-60493975460577:ℝ)/48828125000)*(v 2*v 2) + ((13929940730637309:ℝ)/152587890625)*(v 2*v 3) + ((-178522533107520546:ℝ)/152587890625)*(v 3*v 3)), (((898032058165431:ℝ)/152587890625)*(v 1*v 3) + ((341554336705629:ℝ)/122070312500)*(v 2*v 2) + ((-13155649660419336:ℝ)/30517578125)*(v 2*v 3) + ((1640631771429650496:ℝ)/152587890625)*(v 3*v 3)), (((19095161687675766:ℝ)/30517578125)*(v 2*v 3) + ((-1069329054509842896:ℝ)/30517578125)*(v 3*v 3)), (((48635083788355008:ℝ)/1220703125)*(v 3*v 3))] : List ℝ).getD e 0 * q^e := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3, pieceX_13, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem piece13_frameIntegral (v : Fin 4 → ℝ) :
    ∫ r in Real.log (((23:ℝ)/5)/Real.pi)..Real.log (((24:ℝ)/5)/Real.pi),
      Real.pi*Real.exp r * frameForm pieceX_13 (Real.pi*Real.exp r) v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((126070965019:ℝ)/2500000000000000) ((234707653947361:ℝ)/31250000000000000) ((14227036346197091:ℝ)/7812500000000000) ((5907306889180741427:ℝ)/9765625000000000) ((8841973942288211:ℝ)/4882812500000000) ((116960143525499377:ℝ)/195312500000000) ((38089386626210482657927:ℝ)/152587890625000000) ((3790056945278078320117:ℝ)/15258789062500000) ((471494028140360972325839:ℝ)/3814697265625000) ((338634576031588862607897857:ℝ)/4768371582031250) i j := by
  simp_rw [piece13_frame v]
  rw [integral_exp_poly, pi_mul_exp_log_div (by norm_num), pi_mul_exp_log_div (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero, Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  push_cast
  ring

theorem piece13_weight {r : ℝ} (hr : r ∈ Set.Ioo (Real.log (((23:ℝ)/5)/Real.pi)) (Real.log (((24:ℝ)/5)/Real.pi))) :
    r^2 * pieceKernel r ≤ ((7207017138534971311:ℝ)/10000000000000000000) := by
  obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
  have hr0 : 0 ≤ r := le_trans (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) hr.1.le
  have hrL : r ≤ ((423886283497:ℝ)/1000000000000) := by
    refine hr.2.le.trans ((Real.log_le_iff_le_exp (by positivity)).mpr ?_)
    have h := le_exp_nat_add 0 (f := ((423886283497:ℝ)/1000000000000)) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul h Real.pi_gt_d6.le (by norm_num) (Real.exp_pos _).le]
  have hU : Real.exp (((423886283497:ℝ)/1000000000000)/2) ≤ ((61803880093973237031793934049:ℝ)/50000000000000000000000000000) := by
    have h := exp_nat_add_le 0 (f := ((423886283497:ℝ)/1000000000000)/2) (by norm_num) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hE : ((49485645265030431865782553731:ℝ)/5000000000000000000000000) ≤ Real.exp (2*((23:ℝ)/5)) := by
    have h := le_exp_nat_add 9 (f := ((1:ℝ)/5)) (by norm_num)
    rw [show (2:ℝ)*((23:ℝ)/5) = ((9:ℕ):ℝ) + ((1:ℝ)/5) by norm_num]
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  exact (seam_weight_le hr0 (by linarith [Real.pi_gt_d2]) hqb (by norm_num) hrL hU (by norm_num) hE).trans
    (by norm_num)

/-- **Seam piece 13** on `q ∈ [23/5, 24/5]`. -/
theorem piece13_integral (v : Fin 4 → ℝ) :
    -(((7207017138534971311:ℝ)/10000000000000000000) * ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((126070965019:ℝ)/2500000000000000) ((234707653947361:ℝ)/31250000000000000) ((14227036346197091:ℝ)/7812500000000000) ((5907306889180741427:ℝ)/9765625000000000) ((8841973942288211:ℝ)/4882812500000000) ((116960143525499377:ℝ)/195312500000000) ((38089386626210482657927:ℝ)/152587890625000000) ((3790056945278078320117:ℝ)/15258789062500000) ((471494028140360972325839:ℝ)/3814697265625000) ((338634576031588862607897857:ℝ)/4768371582031250) i j) ≤
      ∫ r in Real.log (((23:ℝ)/5)/Real.pi)..Real.log (((24:ℝ)/5)/Real.pi),
        thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have h := seam_piece_integral (ra' := Real.log (((23:ℝ)/5)/Real.pi)) (rc := Real.log (5/Real.pi)) (Ω := ((7207017138534971311:ℝ)/10000000000000000000))
    le_rfl (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith [Real.pi_lt_d2]) Real.pi_pos.le))
    (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2]))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le)) piece13_X_psd
    (fun r hr y => by
      obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
      exact piece_13 (by linarith [Real.pi_gt_d2]) hqb y)
    (by norm_num) (fun r hr => piece13_weight hr) v
  rwa [piece13_frameIntegral] at h

theorem piece14_X_psd (y : Fin 4 → ℝ) : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceX_14 i j := by
  unfold pieceX_14
  exact quadForm_nonneg_of_ldl ((125614721027:ℝ)/500000000000000) ((1565528952860747481730629:ℝ)/6280736051350000000000000000) ((841716604928800447388937416750830721:ℝ)/2087371937147663308974172000000000000000) ((763489807431422424975511485802908122435289047:ℝ)/1972773292801876048567822070509759502343750000000) ((-377451400039:ℝ)/1256147210270) ((306140339453:ℝ)/2512294420540) ((-12625559161:ℝ)/251229442054) ((-673083719921655488249211:ℝ)/1043685968573831654487086) ((471432865952391880156405:ℝ)/1565528952860747481730629) ((-565444072391489007122941123430293634:ℝ)/841716604928800447388937416750830721)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece14_frame (v : Fin 4 → ℝ) (q : ℝ) :
    frameForm pieceX_14 q v = ∑ e ∈ Finset.range 7, ([(((125614721027:ℝ)/500000000000000)*(v 0*v 0) + ((-125614721027:ℝ)/62500000000000)*(v 0*v 1) + ((125614721027:ℝ)/15625000000000)*(v 0*v 2) + ((-125614721027:ℝ)/3906250000000)*(v 0*v 3) + ((125614721027:ℝ)/31250000000000)*(v 1*v 1) + ((-125614721027:ℝ)/3906250000000)*(v 1*v 2) + ((125614721027:ℝ)/976562500000)*(v 1*v 3) + ((125614721027:ℝ)/1953125000000)*(v 2*v 2) + ((-125614721027:ℝ)/244140625000)*(v 2*v 3) + ((125614721027:ℝ)/122070312500)*(v 3*v 3)), (((4900795830927:ℝ)/312500000000000)*(v 0*v 1) + ((-4900795830927:ℝ)/15625000000000)*(v 0*v 2) + ((102916712449467:ℝ)/19531250000000)*(v 0*v 3) + ((-4900795830927:ℝ)/78125000000000)*(v 1*v 1) + ((14702387492781:ℝ)/9765625000000)*(v 1*v 2) + ((-53908754140197:ℝ)/2441406250000)*(v 1*v 3) + ((-4900795830927:ℝ)/976562500000)*(v 2*v 2) + ((63710345802051:ℝ)/610351562500)*(v 2*v 3) + ((-102916712449467:ℝ)/305175781250)*(v 3*v 3)), (((16001296095969:ℝ)/19531250000000)*(v 0*v 2) + ((-112009072671783:ℝ)/2441406250000)*(v 0*v 3) + ((30336858642537:ℝ)/78125000000000)*(v 1*v 1) + ((-183686885404623:ℝ)/9765625000000)*(v 1*v 2) + ((1085110322180409:ℝ)/2441406250000)*(v 1*v 3) + ((822426650447301:ℝ)/4882812500000)*(v 2*v 2) + ((-733081808069091:ℝ)/122070312500)*(v 2*v 3) + ((14274627242733081:ℝ)/305175781250)*(v 3*v 3)), (((294669065709333:ℝ)/4882812500000)*(v 0*v 3) + ((265957918224039:ℝ)/4882812500000)*(v 1*v 2) + ((-4018079920845879:ℝ)/1220703125000)*(v 1*v 3) + ((-265957918224039:ℝ)/244140625000)*(v 2*v 2) + ((12248419812048441:ℝ)/152587890625)*(v 2*v 3) + ((-156972594047153598:ℝ)/152587890625)*(v 3*v 3)), (((3029593807701909:ℝ)/610351562500)*(v 1*v 3) + ((288066248322813:ℝ)/122070312500)*(v 2*v 2) + ((-11095448760740673:ℝ)/30517578125)*(v 2*v 3) + ((1383705573272387316:ℝ)/152587890625)*(v 3*v 3)), (((3089496348769698:ℝ)/6103515625)*(v 2*v 3) + ((-173011795531103088:ℝ)/6103515625)*(v 3*v 3)), (((943465025791944936:ℝ)/30517578125)*(v 3*v 3))] : List ℝ).getD e 0 * q^e := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3, pieceX_14, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem piece14_frameIntegral (v : Fin 4 → ℝ) :
    ∫ r in Real.log (((24:ℝ)/5)/Real.pi)..Real.log ((5:ℝ)/Real.pi),
      Real.pi*Real.exp r * frameForm pieceX_14 (Real.pi*Real.exp r) v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((125614721027:ℝ)/2500000000000000) ((233858259664073:ℝ)/31250000000000000) ((70876820170944959:ℝ)/39062500000000000) ((29428453253356223879:ℝ)/48828125000000000) ((17619730902512009:ℝ)/9765625000000000) ((14566555842998732551:ℝ)/24414062500000000) ((37948593668818034263997:ℝ)/152587890625000000) ((472006792281006245113:ℝ)/1907348632812500) ((117431885447187332639017:ℝ)/953674316406250) ((168672016425357145225163264:ℝ)/2384185791015625) i j := by
  simp_rw [piece14_frame v]
  rw [integral_exp_poly, pi_mul_exp_log_div (by norm_num), pi_mul_exp_log_div (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero, Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  push_cast
  ring

theorem piece14_weight {r : ℝ} (hr : r ∈ Set.Ioo (Real.log (((24:ℝ)/5)/Real.pi)) (Real.log ((5:ℝ)/Real.pi))) :
    r^2 * pieceKernel r ≤ ((3616596837272610123:ℝ)/5000000000000000000) := by
  obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
  have hr0 : 0 ≤ r := le_trans (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) hr.1.le
  have hrL : r ≤ ((4647082821:ℝ)/10000000000) := by
    refine hr.2.le.trans ((Real.log_le_iff_le_exp (by positivity)).mpr ?_)
    have h := le_exp_nat_add 0 (f := ((4647082821:ℝ)/10000000000)) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul h Real.pi_gt_d6.le (by norm_num) (Real.exp_pos _).le]
  have hU : Real.exp (((4647082821:ℝ)/10000000000)/2) ≤ ((15769580277570007616088446729:ℝ)/12500000000000000000000000000) := by
    have h := exp_nat_add_le 0 (f := ((4647082821:ℝ)/10000000000)/2) (by norm_num) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hE : ((36911944857444416144704795411:ℝ)/2500000000000000000000000) ≤ Real.exp (2*((24:ℝ)/5)) := by
    have h := le_exp_nat_add 9 (f := ((3:ℝ)/5)) (by norm_num)
    rw [show (2:ℝ)*((24:ℝ)/5) = ((9:ℕ):ℝ) + ((3:ℝ)/5) by norm_num]
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  exact (seam_weight_le hr0 (by linarith [Real.pi_gt_d2]) hqb (by norm_num) hrL hU (by norm_num) hE).trans
    (by norm_num)

/-- **Seam piece 14** on `q ∈ [24/5, 5]`. -/
theorem piece14_integral (v : Fin 4 → ℝ) :
    -(((3616596837272610123:ℝ)/5000000000000000000) * ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((125614721027:ℝ)/2500000000000000) ((233858259664073:ℝ)/31250000000000000) ((70876820170944959:ℝ)/39062500000000000) ((29428453253356223879:ℝ)/48828125000000000) ((17619730902512009:ℝ)/9765625000000000) ((14566555842998732551:ℝ)/24414062500000000) ((37948593668818034263997:ℝ)/152587890625000000) ((472006792281006245113:ℝ)/1907348632812500) ((117431885447187332639017:ℝ)/953674316406250) ((168672016425357145225163264:ℝ)/2384185791015625) i j) ≤
      ∫ r in Real.log (((24:ℝ)/5)/Real.pi)..Real.log ((5:ℝ)/Real.pi),
        thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have h := seam_piece_integral (ra' := Real.log (((24:ℝ)/5)/Real.pi)) (rc := Real.log (5/Real.pi)) (Ω := ((3616596837272610123:ℝ)/5000000000000000000))
    le_rfl (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by linarith [Real.pi_lt_d2]) Real.pi_pos.le))
    (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2]))
    le_rfl piece14_X_psd
    (fun r hr y => by
      obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
      exact piece_14 (by linarith [Real.pi_gt_d2]) hqb y)
    (by norm_num) (fun r hr => piece14_weight hr) v
  rwa [piece14_frameIntegral] at h

theorem piece15_X_nsd (y : Fin 4 → ℝ) : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * (-pieceX_15 i j) := by
  unfold pieceX_15
  simp only [neg_sym4]
  exact quadForm_nonneg_of_ldl ((117636511139:ℝ)/125000000000) ((600735769665478574735751:ℝ)/941092089112000000000000) ((137624439676613003339157716290577056277:ℝ)/240294307866191429894300400000000000000) ((1221442235515331519146476412239823604039277596189735727:ℝ)/4300763739894156354348678634080533008656250000000000000) ((-103778688225:ℝ)/941092089112) ((-9816748973:ℝ)/3764368356448) ((-233203170329:ℝ)/941092089112000) ((-838818409054993490858849:ℝ)/12014715393309571494715020) ((-866474739710845462485601:ℝ)/24029430786619142989430040) ((213282564274140994466040772590835201349:ℝ)/1376244396766130033391577162905770562770)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece15_frame (v : Fin 4 → ℝ) (q : ℝ) :
    -frameForm pieceX_15 q v = ∑ e ∈ Finset.range 7, ([(((117636511139:ℝ)/125000000000)*(v 0*v 0) + ((-117636511139:ℝ)/15625000000)*(v 0*v 1) + ((117636511139:ℝ)/3906250000)*(v 0*v 2) + ((-117636511139:ℝ)/976562500)*(v 0*v 3) + ((117636511139:ℝ)/7812500000)*(v 1*v 1) + ((-117636511139:ℝ)/976562500)*(v 1*v 2) + ((117636511139:ℝ)/244140625)*(v 1*v 3) + ((117636511139:ℝ)/488281250)*(v 2*v 2) + ((-470546044556:ℝ)/244140625)*(v 2*v 3) + ((941092089112:ℝ)/244140625)*(v 3*v 3)), (((3134612332011:ℝ)/62500000000)*(v 0*v 1) + ((-3134612332011:ℝ)/3125000000)*(v 0*v 2) + ((65826858972231:ℝ)/3906250000)*(v 0*v 3) + ((-3134612332011:ℝ)/15625000000)*(v 1*v 1) + ((9403836996033:ℝ)/1953125000)*(v 1*v 2) + ((-34480735652121:ℝ)/488281250)*(v 1*v 3) + ((-3134612332011:ℝ)/195312500)*(v 2*v 2) + ((81499920632286:ℝ)/244140625)*(v 2*v 3) + ((-263307435888924:ℝ)/244140625)*(v 3*v 3)), (((17200291736511:ℝ)/7812500000)*(v 0*v 2) + ((-120402042155577:ℝ)/976562500)*(v 0*v 3) + ((3237178715073:ℝ)/3125000000)*(v 1*v 1) + ((-12266219951667:ℝ)/244140625)*(v 1*v 2) + ((580707849393819:ℝ)/488281250)*(v 1*v 3) + ((439047922857147:ℝ)/976562500)*(v 2*v 2) + ((-783009280584396:ℝ)/48828125)*(v 2*v 3) + ((30478348941433092:ℝ)/244140625)*(v 3*v 3)), (((32726522507160909:ℝ)/244140625000)*(v 0*v 3) + ((145432551532977:ℝ)/1220703125)*(v 1*v 2) + ((-439937666799496509:ℝ)/61035156250)*(v 1*v 3) + ((-581730206131908:ℝ)/244140625)*(v 2*v 2) + ((5359197920814684618:ℝ)/30517578125)*(v 2*v 3) + ((-68673284421169668072:ℝ)/30517578125)*(v 3*v 3)), (((266786774401305627:ℝ)/30517578125)*(v 1*v 3) + ((1003883190188886:ℝ)/244140625)*(v 2*v 2) + ((-3878020030134103308:ℝ)/6103515625)*(v 2*v 3) + ((483162566752882002672:ℝ)/30517578125)*(v 3*v 3)), (((4209003057970952136:ℝ)/6103515625)*(v 2*v 3) + ((-235704171246373319616:ℝ)/6103515625)*(v 3*v 3)), (((195608036833840947456:ℝ)/6103515625)*(v 3*v 3))] : List ℝ).getD e 0 * q^e := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3, pieceX_15, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem piece15_frameIntegral (v : Fin 4 → ℝ) :
    ∫ r in Real.log ((5:ℝ)/Real.pi)..Real.log (((21:ℝ)/4)/Real.pi),
      Real.pi*Real.exp r * -frameForm pieceX_15 (Real.pi*Real.exp r) v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((117636511139:ℝ)/500000000000) ((124754737256003:ℝ)/4000000000000) ((131820496004153:ℝ)/20000000000) ((931397529390848553229:ℝ)/500000000000000) ((6550196756643301:ℝ)/1000000000000) ((4609861222487040197:ℝ)/2500000000000) ((398298126726104394428509:ℝ)/625000000000000) ((395453118572704878643:ℝ)/625000000000) ((3167826487468468104130849:ℝ)/12500000000000) ((1113959671890262361241550207:ℝ)/9765625000000) i j := by
  simp_rw [piece15_frame v]
  rw [integral_exp_poly, pi_mul_exp_log_div (by norm_num), pi_mul_exp_log_div (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero, Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  push_cast
  ring

theorem piece15_weight {r : ℝ} (hr : r ∈ Set.Ioo (Real.log ((5:ℝ)/Real.pi)) (Real.log (((21:ℝ)/4)/Real.pi))) :
    ((2940790518009592861:ℝ)/10000000000000000000) ≤ r^2 * pieceKernel r := by
  obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
  have hLr : ((29044241803:ℝ)/62500000000) ≤ r := by
    refine le_trans ((Real.le_log_iff_exp_le (by positivity)).mpr ?_) hr.1.le
    have h := exp_nat_add_le 0 (f := ((29044241803:ℝ)/62500000000)) (by norm_num) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul_of_nonneg_left Real.pi_lt_d6.le (Real.exp_pos ((29044241803:ℝ)/62500000000)).le]
  have hU : ((25231323225923161159285356243:ℝ)/20000000000000000000000000000) ≤ Real.exp (((29044241803:ℝ)/62500000000)/2) := by
    have h := le_exp_nat_add 0 (f := ((29044241803:ℝ)/62500000000)/2) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hE : Real.exp (2*((21:ℝ)/4)) ≤ ((181577514175300299584940963669:ℝ)/5000000000000000000000000) := by
    have h := exp_nat_add_le 10 (f := ((1:ℝ)/2)) (by norm_num) (by norm_num)
    rw [show (2:ℝ)*((21:ℝ)/4) = ((10:ℕ):ℝ) + ((1:ℝ)/2) by norm_num]
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  exact le_trans (by norm_num) (bulk_weight_ge hqa hqb (by norm_num) (by norm_num) hLr (by norm_num) hU hE)

/-- **Bulk piece 15** on `q ∈ [5, 21/4]`. -/
theorem piece15_integral (v : Fin 4 → ℝ) :
    ((2940790518009592861:ℝ)/10000000000000000000) * ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((117636511139:ℝ)/500000000000) ((124754737256003:ℝ)/4000000000000) ((131820496004153:ℝ)/20000000000) ((931397529390848553229:ℝ)/500000000000000) ((6550196756643301:ℝ)/1000000000000) ((4609861222487040197:ℝ)/2500000000000) ((398298126726104394428509:ℝ)/625000000000000) ((395453118572704878643:ℝ)/625000000000) ((3167826487468468104130849:ℝ)/12500000000000) ((1113959671890262361241550207:ℝ)/9765625000000) i j ≤
      ∫ r in Real.log ((5:ℝ)/Real.pi)..Real.log (((21:ℝ)/4)/Real.pi),
        thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have h := bulk_piece_integral (rc := Real.log (5/Real.pi)) (Ω := ((2940790518009592861:ℝ)/10000000000000000000))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le))
    le_rfl
    (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) piece15_X_nsd
    (fun r hr y => by
      obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
      exact piece_15 hqa hqb y)
    (fun r hr => piece15_weight hr) v
  rwa [piece15_frameIntegral] at h

theorem piece16_X_nsd (y : Fin 4 → ℝ) : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * (-pieceX_16 i j) := by
  unfold pieceX_16
  simp only [neg_sym4]
  exact quadForm_nonneg_of_ldl ((468108221013:ℝ)/500000000000) ((14746685350637777381206739:ℝ)/23405411050650000000000000) ((1737540879834785734252342210335413943881:ℝ)/2949337070127555476241347800000000000000) ((301926341031923976357124349252065303040751991747544723:ℝ)/1085963049896741083907713881459633714925625000000000000) ((-452266898219:ℝ)/4681082210130) ((-23307136517:ℝ)/10402404911400) ((-17152507027:ℝ)/39009018417750) ((-17455477575558791951276607:ℝ)/294933707012755547624134780) ((-11000959534004768817377739:ℝ)/368667133765944434530168475) ((268117611785624426999194497681132064976:ℝ)/1737540879834785734252342210335413943881)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece16_frame (v : Fin 4 → ℝ) (q : ℝ) :
    -frameForm pieceX_16 q v = ∑ e ∈ Finset.range 7, ([(((468108221013:ℝ)/500000000000)*(v 0*v 0) + ((-468108221013:ℝ)/62500000000)*(v 0*v 1) + ((468108221013:ℝ)/15625000000)*(v 0*v 2) + ((-468108221013:ℝ)/3906250000)*(v 0*v 3) + ((468108221013:ℝ)/31250000000)*(v 1*v 1) + ((-468108221013:ℝ)/3906250000)*(v 1*v 2) + ((468108221013:ℝ)/976562500)*(v 1*v 3) + ((468108221013:ℝ)/1953125000)*(v 2*v 2) + ((-468108221013:ℝ)/244140625)*(v 2*v 3) + ((936216442026:ℝ)/244140625)*(v 3*v 3)), (((15400047325047:ℝ)/312500000000)*(v 0*v 1) + ((-15400047325047:ℝ)/15625000000)*(v 0*v 2) + ((323400993825987:ℝ)/19531250000)*(v 0*v 3) + ((-15400047325047:ℝ)/78125000000)*(v 1*v 1) + ((46200141975141:ℝ)/9765625000)*(v 1*v 2) + ((-169400520575517:ℝ)/2441406250)*(v 1*v 3) + ((-15400047325047:ℝ)/976562500)*(v 2*v 2) + ((400401230451222:ℝ)/1220703125)*(v 2*v 3) + ((-1293603975303948:ℝ)/1220703125)*(v 3*v 3)), (((418291907806641:ℝ)/195312500000)*(v 0*v 2) + ((-2928043354646487:ℝ)/24414062500)*(v 0*v 3) + ((39508131791511:ℝ)/39062500000)*(v 1*v 1) + ((-2393698497382191:ℝ)/48828125000)*(v 1*v 2) + ((7076397192755142:ℝ)/6103515625)*(v 1*v 3) + ((2678404190872758:ℝ)/6103515625)*(v 2*v 2) + ((-19103166799274466:ℝ)/1220703125)*(v 2*v 3) + ((743772138476597832:ℝ)/6103515625)*(v 3*v 3)), (((3946922331202746:ℝ)/30517578125)*(v 0*v 3) + ((1413649909120689:ℝ)/12207031250)*(v 1*v 2) + ((-213698676601707444:ℝ)/30517578125)*(v 1*v 3) + ((-2827299818241378:ℝ)/1220703125)*(v 2*v 2) + ((5208836426498551896:ℝ)/30517578125)*(v 2*v 3) + ((-66750694754234186304:ℝ)/30517578125)*(v 3*v 3)), (((258591821934087054:ℝ)/30517578125)*(v 1*v 3) + ((4890357652148316:ℝ)/1220703125)*(v 2*v 2) + ((-3772967572939405176:ℝ)/6103515625)*(v 2*v 3) + ((470290892098281224544:ℝ)/30517578125)*(v 3*v 3)), (((4112860993691636592:ℝ)/6103515625)*(v 2*v 3) + ((-230320215646731649152:ℝ)/6103515625)*(v 3*v 3)), (((192323676646131916032:ℝ)/6103515625)*(v 3*v 3))] : List ℝ).getD e 0 * q^e := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3, pieceX_16, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem piece16_frameIntegral (v : Fin 4 → ℝ) :
    ∫ r in Real.log (((21:ℝ)/4)/Real.pi)..Real.log (((11:ℝ)/2)/Real.pi),
      Real.pi*Real.exp r * -frameForm pieceX_16 (Real.pi*Real.exp r) v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((468108221013:ℝ)/2000000000000) ((643477706136501:ℝ)/20000000000000) ((44232215703095191:ℝ)/6250000000000) ((6530428537895427587:ℝ)/3125000000000) ((8806543197192579:ℝ)/1250000000000) ((51880268471737038539:ℝ)/25000000000000) ((117683378798113845005687:ℝ)/156250000000000) ((2343895420693975332379:ℝ)/3125000000000) ((9914558628410532385367607:ℝ)/31250000000000) ((738327238419584866837538477:ℝ)/4882812500000) i j := by
  simp_rw [piece16_frame v]
  rw [integral_exp_poly, pi_mul_exp_log_div (by norm_num), pi_mul_exp_log_div (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero, Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  push_cast
  ring

theorem piece16_weight {r : ℝ} (hr : r ∈ Set.Ioo (Real.log (((21:ℝ)/4)/Real.pi)) (Real.log (((11:ℝ)/2)/Real.pi))) :
    ((2824451040837379559:ℝ)/10000000000000000000) ≤ r^2 * pieceKernel r := by
  obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
  have hLr : ((513498028139:ℝ)/1000000000000) ≤ r := by
    refine le_trans ((Real.le_log_iff_exp_le (by positivity)).mpr ?_) hr.1.le
    have h := exp_nat_add_le 0 (f := ((513498028139:ℝ)/1000000000000)) (by norm_num) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul_of_nonneg_left Real.pi_lt_d6.le (Real.exp_pos ((513498028139:ℝ)/1000000000000)).le]
  have hU : ((64636031543329552723340646983:ℝ)/50000000000000000000000000000) ≤ Real.exp (((513498028139:ℝ)/1000000000000)/2) := by
    have h := le_exp_nat_add 0 (f := ((513498028139:ℝ)/1000000000000)/2) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hE : Real.exp (2*((11:ℝ)/2)) ≤ ((598741417493499067856494113277:ℝ)/10000000000000000000000000) := by
    have h := exp_nat_add_le 11 (f := (0:ℝ)) (by norm_num) (by norm_num)
    rw [show (2:ℝ)*((11:ℝ)/2) = ((11:ℕ):ℝ) + (0:ℝ) by norm_num]
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  exact le_trans (by norm_num) (bulk_weight_ge hqa hqb (by norm_num) (by norm_num) hLr (by norm_num) hU hE)

/-- **Bulk piece 16** on `q ∈ [21/4, 11/2]`. -/
theorem piece16_integral (v : Fin 4 → ℝ) :
    ((2824451040837379559:ℝ)/10000000000000000000) * ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((468108221013:ℝ)/2000000000000) ((643477706136501:ℝ)/20000000000000) ((44232215703095191:ℝ)/6250000000000) ((6530428537895427587:ℝ)/3125000000000) ((8806543197192579:ℝ)/1250000000000) ((51880268471737038539:ℝ)/25000000000000) ((117683378798113845005687:ℝ)/156250000000000) ((2343895420693975332379:ℝ)/3125000000000) ((9914558628410532385367607:ℝ)/31250000000000) ((738327238419584866837538477:ℝ)/4882812500000) i j ≤
      ∫ r in Real.log (((21:ℝ)/4)/Real.pi)..Real.log (((11:ℝ)/2)/Real.pi),
        thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have h := bulk_piece_integral (rc := Real.log (5/Real.pi)) (Ω := ((2824451040837379559:ℝ)/10000000000000000000))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le))
    (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) piece16_X_nsd
    (fun r hr y => by
      obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
      exact piece_16 hqa hqb y)
    (fun r hr => piece16_weight hr) v
  rwa [piece16_frameIntegral] at h

theorem piece17_X_nsd (y : Fin 4 → ℝ) : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * (-pieceX_17 i j) := by
  unfold pieceX_17
  simp only [neg_sym4]
  exact quadForm_nonneg_of_ldl ((931978198249:ℝ)/1000000000000) ((58047903099841667424820491:ℝ)/93197819824900000000000000) ((865956757235991107166603398054388442511:ℝ)/1451197577496041685620512275000000000000) ((6037909728126295490947273998999538485710062293176071:ℝ)/21648918930899777679165084951359711062775000000000000) ((-797084213003:ℝ)/9319781982490) ((-44143222369:ℝ)/23299454956225) ((-5109405423:ℝ)/9319781982490) ((-14116695141562832546111414:ℝ)/290239515499208337124102455) ((-1501735335287527362504779:ℝ)/58047903099841667424820491) ((134923483859065983893193459136050610897:ℝ)/865956757235991107166603398054388442511)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece17_frame (v : Fin 4 → ℝ) (q : ℝ) :
    -frameForm pieceX_17 q v = ∑ e ∈ Finset.range 7, ([(((931978198249:ℝ)/1000000000000)*(v 0*v 0) + ((-931978198249:ℝ)/125000000000)*(v 0*v 1) + ((931978198249:ℝ)/31250000000)*(v 0*v 2) + ((-931978198249:ℝ)/7812500000)*(v 0*v 3) + ((931978198249:ℝ)/62500000000)*(v 1*v 1) + ((-931978198249:ℝ)/7812500000)*(v 1*v 2) + ((931978198249:ℝ)/1953125000)*(v 1*v 3) + ((931978198249:ℝ)/3906250000)*(v 2*v 2) + ((-931978198249:ℝ)/488281250)*(v 2*v 3) + ((931978198249:ℝ)/244140625)*(v 3*v 3)), (((30350598586479:ℝ)/625000000000)*(v 0*v 1) + ((-30350598586479:ℝ)/31250000000)*(v 0*v 2) + ((637362570316059:ℝ)/39062500000)*(v 0*v 3) + ((-30350598586479:ℝ)/156250000000)*(v 1*v 1) + ((91051795759437:ℝ)/19531250000)*(v 1*v 2) + ((-333856584451269:ℝ)/4882812500)*(v 1*v 3) + ((-30350598586479:ℝ)/1953125000)*(v 2*v 2) + ((394557781624227:ℝ)/1220703125)*(v 2*v 3) + ((-1274725140632118:ℝ)/1220703125)*(v 3*v 3)), (((102185855412543:ℝ)/48828125000)*(v 0*v 2) + ((-715300987887801:ℝ)/6103515625)*(v 0*v 3) + ((77447625125157:ℝ)/78125000000)*(v 1*v 1) + ((-2344934049779097:ℝ)/48828125000)*(v 1*v 2) + ((13854408541243893:ℝ)/12207031250)*(v 1*v 3) + ((10498439983944969:ℝ)/24414062500)*(v 2*v 2) + ((-18716461806184002:ℝ)/1220703125)*(v 2*v 3) + ((728867316828704004:ℝ)/6103515625)*(v 3*v 3)), (((6128190942490659:ℝ)/48828125000)*(v 0*v 3) + ((5519546760579687:ℝ)/48828125000)*(v 1*v 2) + ((-83401845590606277:ℝ)/12207031250)*(v 1*v 3) + ((-5519546760579687:ℝ)/2441406250)*(v 2*v 2) + ((1016813892310484352:ℝ)/6103515625)*(v 2*v 3) + ((-13030999508423349096:ℝ)/6103515625)*(v 3*v 3)), (((50328499249166292:ℝ)/6103515625)*(v 1*v 3) + ((4776685558938207:ℝ)/1220703125)*(v 2*v 2) + ((-736302779597744352:ℝ)/1220703125)*(v 2*v 3) + ((91808805311870959872:ℝ)/6103515625)*(v 3*v 3)), (((804271437106369848:ℝ)/1220703125)*(v 2*v 3) + ((-45039200477956711488:ℝ)/1220703125)*(v 3*v 3)), (((37749858973268412096:ℝ)/1220703125)*(v 3*v 3))] : List ℝ).getD e 0 * q^e := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3, pieceX_17, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem piece17_frameIntegral (v : Fin 4 → ℝ) :
    ∫ r in Real.log (((11:ℝ)/2)/Real.pi)..Real.log (((23:ℝ)/4)/Real.pi),
      Real.pi*Real.exp r * -frameForm pieceX_17 (Real.pi*Real.exp r) v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((931978198249:ℝ)/4000000000000) ((265699561692319:ℝ)/8000000000000) ((379962810554268437:ℝ)/50000000000000) ((234140211682554756971:ℝ)/100000000000000) ((18933588407972293:ℝ)/2500000000000) ((232937741998698082199:ℝ)/100000000000000) ((110659667490505200579119:ℝ)/125000000000000) ((441536991826699777127:ℝ)/500000000000) ((4907969745474255485571793:ℝ)/12500000000000) ((1540197254628183594900335963:ℝ)/7812500000000) i j := by
  simp_rw [piece17_frame v]
  rw [integral_exp_poly, pi_mul_exp_log_div (by norm_num), pi_mul_exp_log_div (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero, Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  push_cast
  ring

theorem piece17_weight {r : ℝ} (hr : r ∈ Set.Ioo (Real.log (((11:ℝ)/2)/Real.pi)) (Real.log (((23:ℝ)/4)/Real.pi))) :
    ((130211456479368643:ℝ)/500000000000000000) ≤ r^2 * pieceKernel r := by
  obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
  have hLr : ((560018039121:ℝ)/1000000000000) ≤ r := by
    refine le_trans ((Real.le_log_iff_exp_le (by positivity)).mpr ?_) hr.1.le
    have h := exp_nat_add_le 0 (f := ((560018039121:ℝ)/1000000000000)) (by norm_num) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul_of_nonneg_left Real.pi_lt_d6.le (Real.exp_pos ((560018039121:ℝ)/1000000000000)).le]
  have hU : ((66157087273670036263054810707:ℝ)/50000000000000000000000000000) ≤ Real.exp (((560018039121:ℝ)/1000000000000)/2) := by
    have h := le_exp_nat_add 0 (f := ((560018039121:ℝ)/1000000000000)/2) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hE : Real.exp (2*((23:ℝ)/4)) ≤ ((98715771453015543861976228749:ℝ)/1000000000000000000000000) := by
    have h := exp_nat_add_le 11 (f := ((1:ℝ)/2)) (by norm_num) (by norm_num)
    rw [show (2:ℝ)*((23:ℝ)/4) = ((11:ℕ):ℝ) + ((1:ℝ)/2) by norm_num]
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  exact le_trans (by norm_num) (bulk_weight_ge hqa hqb (by norm_num) (by norm_num) hLr (by norm_num) hU hE)

/-- **Bulk piece 17** on `q ∈ [11/2, 23/4]`. -/
theorem piece17_integral (v : Fin 4 → ℝ) :
    ((130211456479368643:ℝ)/500000000000000000) * ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((931978198249:ℝ)/4000000000000) ((265699561692319:ℝ)/8000000000000) ((379962810554268437:ℝ)/50000000000000) ((234140211682554756971:ℝ)/100000000000000) ((18933588407972293:ℝ)/2500000000000) ((232937741998698082199:ℝ)/100000000000000) ((110659667490505200579119:ℝ)/125000000000000) ((441536991826699777127:ℝ)/500000000000) ((4907969745474255485571793:ℝ)/12500000000000) ((1540197254628183594900335963:ℝ)/7812500000000) i j ≤
      ∫ r in Real.log (((11:ℝ)/2)/Real.pi)..Real.log (((23:ℝ)/4)/Real.pi),
        thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have h := bulk_piece_integral (rc := Real.log (5/Real.pi)) (Ω := ((130211456479368643:ℝ)/500000000000000000))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le))
    (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) piece17_X_nsd
    (fun r hr y => by
      obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
      exact piece_17 hqa hqb y)
    (fun r hr => piece17_weight hr) v
  rwa [piece17_frameIntegral] at h

end
end RHTower.ThetaCuspOddFourPieces
