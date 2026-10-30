import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourPieceIntegral
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourCertificatePieces5
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourCertificatePieces6

/-!
# Piece integrals 18–22

For each piece: the compensation matrix is negative semidefinite by an exact `LDLᵀ` factorization, the weight
`r²κ(r)` is bounded below by a rational constant on the piece, and the moving-frame form integrates
exactly against `π e^r dr = dq`. Together with the piece certificate this bounds the seam-split
integral over the piece by an explicit quadratic form in `v`.
-/

namespace RHTower.ThetaCuspOddFourPieces
noncomputable section
open ThetaCuspOddCentral ThetaCuspOddFourCertificateTools

theorem piece18_X_nsd (y : Fin 4 → ℝ) : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * (-pieceX_18 i j) := by
  unfold pieceX_18
  simp only [neg_sym4]
  exact quadForm_nonneg_of_ldl ((464145091017:ℝ)/500000000000) ((57236921523247920263573639:ℝ)/92829018203400000000000000) ((686650166881569151544672622640851242167:ℝ)/1144738430464958405271472780000000000000) ((95201554257251151276825920612378982459558462273128059:ℝ)/343325083440784575772336311320425621083500000000000000) ((-708551738831:ℝ)/9282901820340) ((-30303447313:ℝ)/18565803640680) ((-58442958227:ℝ)/185658036406800) ((-4469327396817468819310943:ℝ)/114473843046495840527147278) ((-26339110385956808522975437:ℝ)/1144738430464958405271472780) ((1088797608051468790539235418436895044739:ℝ)/6866501668815691515446726226408512421670)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece18_frame (v : Fin 4 → ℝ) (q : ℝ) :
    -frameForm pieceX_18 q v = ∑ e ∈ Finset.range 7, ([(((464145091017:ℝ)/500000000000)*(v 0*v 0) + ((-464145091017:ℝ)/62500000000)*(v 0*v 1) + ((464145091017:ℝ)/15625000000)*(v 0*v 2) + ((-464145091017:ℝ)/3906250000)*(v 0*v 3) + ((464145091017:ℝ)/31250000000)*(v 1*v 1) + ((-464145091017:ℝ)/3906250000)*(v 1*v 2) + ((464145091017:ℝ)/976562500)*(v 1*v 3) + ((464145091017:ℝ)/1953125000)*(v 2*v 2) + ((-464145091017:ℝ)/244140625)*(v 2*v 3) + ((928290182034:ℝ)/244140625)*(v 3*v 3)), (((29974360677513:ℝ)/625000000000)*(v 0*v 1) + ((-29974360677513:ℝ)/31250000000)*(v 0*v 2) + ((629461574227773:ℝ)/39062500000)*(v 0*v 3) + ((-29974360677513:ℝ)/156250000000)*(v 1*v 1) + ((89923082032539:ℝ)/19531250000)*(v 1*v 2) + ((-329717967452643:ℝ)/4882812500)*(v 1*v 3) + ((-29974360677513:ℝ)/1953125000)*(v 2*v 2) + ((389666688807669:ℝ)/1220703125)*(v 2*v 3) + ((-1258923148455546:ℝ)/1220703125)*(v 3*v 3)), (((20039782348269:ℝ)/9765625000)*(v 0*v 2) + ((-140278476437883:ℝ)/1220703125)*(v 0*v 3) + ((38069846560197:ℝ)/39062500000)*(v 1*v 1) + ((-230428797497523:ℝ)/4882812500)*(v 1*v 2) + ((1360580683515669:ℝ)/1220703125)*(v 1*v 3) + ((1031905293398001:ℝ)/2441406250)*(v 2*v 2) + ((-3678821887415004:ℝ)/244140625)*(v 2*v 3) + ((143288241156399528:ℝ)/1220703125)*(v 3*v 3)), (((2985814287326451:ℝ)/24414062500)*(v 0*v 3) + ((1081257599890719:ℝ)/9765625000)*(v 1*v 2) + ((-40829830283501616:ℝ)/6103515625)*(v 1*v 3) + ((-1081257599890719:ℝ)/488281250)*(v 2*v 2) + ((995887673049860094:ℝ)/6103515625)*(v 2*v 3) + ((-12763362403312078656:ℝ)/6103515625)*(v 3*v 3)), (((49147117634288961:ℝ)/6103515625)*(v 1*v 3) + ((935643522334842:ℝ)/244140625)*(v 2*v 2) + ((-720548843044667364:ℝ)/1220703125)*(v 2*v 3) + ((89867883676172703696:ℝ)/6103515625)*(v 3*v 3)), (((787751310437750736:ℝ)/1220703125)*(v 2*v 3) + ((-44114073384514041216:ℝ)/1220703125)*(v 3*v 3)), (((37050937993119984192:ℝ)/1220703125)*(v 3*v 3))] : List ℝ).getD e 0 * q^e := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3, pieceX_18, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem piece18_frameIntegral (v : Fin 4 → ℝ) :
    ∫ r in Real.log (((23:ℝ)/4)/Real.pi)..Real.log ((6:ℝ)/Real.pi),
      Real.pi*Real.exp r * -frameForm pieceX_18 (Real.pi*Real.exp r) v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((464145091017:ℝ)/2000000000000) ((1371663344561751:ℝ)/40000000000000) ((81542275117617093:ℝ)/10000000000000) ((26173092628890670293:ℝ)/10000000000000) ((8132852270392371:ℝ)/1000000000000) ((52149686368985156529:ℝ)/20000000000000) ((64707327661056642645441:ℝ)/62500000000000) ((2584397382348412177383:ℝ)/2500000000000) ((752387545821038816190297:ℝ)/1562500000000) ((1981855100847994079397150519:ℝ)/7812500000000) i j := by
  simp_rw [piece18_frame v]
  rw [integral_exp_poly, pi_mul_exp_log_div (by norm_num), pi_mul_exp_log_div (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero, Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  push_cast
  ring

theorem piece18_weight {r : ℝ} (hr : r ∈ Set.Ioo (Real.log (((23:ℝ)/4)/Real.pi)) (Real.log ((6:ℝ)/Real.pi))) :
    ((232165613508934269:ℝ)/1000000000000000000) ≤ r^2 * pieceKernel r := by
  obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
  have hLr : ((604469797247:ℝ)/1000000000000) ≤ r := by
    refine le_trans ((Real.le_log_iff_exp_le (by positivity)).mpr ?_) hr.1.le
    have h := exp_nat_add_le 0 (f := ((604469797247:ℝ)/1000000000000)) (by norm_num) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul_of_nonneg_left Real.pi_lt_d6.le (Real.exp_pos ((604469797247:ℝ)/1000000000000)).le]
  have hU : ((33821974425289285222293306931:ℝ)/25000000000000000000000000000) ≤ Real.exp (((604469797247:ℝ)/1000000000000)/2) := by
    have h := le_exp_nat_add 0 (f := ((604469797247:ℝ)/1000000000000)/2) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hE : Real.exp (2*(6:ℝ)) ≤ ((162754791520278467478534630063:ℝ)/1000000000000000000000000) := by
    have h := exp_nat_add_le 12 (f := (0:ℝ)) (by norm_num) (by norm_num)
    rw [show (2:ℝ)*(6:ℝ) = ((12:ℕ):ℝ) + (0:ℝ) by norm_num]
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  exact le_trans (by norm_num) (bulk_weight_ge hqa hqb (by norm_num) (by norm_num) hLr (by norm_num) hU hE)

/-- **Bulk piece 18** on `q ∈ [23/4, 6]`. -/
theorem piece18_integral (v : Fin 4 → ℝ) :
    ((232165613508934269:ℝ)/1000000000000000000) * ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((464145091017:ℝ)/2000000000000) ((1371663344561751:ℝ)/40000000000000) ((81542275117617093:ℝ)/10000000000000) ((26173092628890670293:ℝ)/10000000000000) ((8132852270392371:ℝ)/1000000000000) ((52149686368985156529:ℝ)/20000000000000) ((64707327661056642645441:ℝ)/62500000000000) ((2584397382348412177383:ℝ)/2500000000000) ((752387545821038816190297:ℝ)/1562500000000) ((1981855100847994079397150519:ℝ)/7812500000000) i j ≤
      ∫ r in Real.log (((23:ℝ)/4)/Real.pi)..Real.log ((6:ℝ)/Real.pi),
        thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have h := bulk_piece_integral (rc := Real.log (5/Real.pi)) (Ω := ((232165613508934269:ℝ)/1000000000000000000))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le))
    (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) piece18_X_nsd
    (fun r hr y => by
      obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
      exact piece_18 hqa hqb y)
    (fun r hr => piece18_weight hr) v
  rwa [piece18_frameIntegral] at h

theorem piece19_X_nsd (y : Fin 4 → ℝ) : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * (-pieceX_19 i j) := by
  unfold pieceX_19
  simp only [neg_sym4]
  exact quadForm_nonneg_of_ldl ((86666388153:ℝ)/125000000000) ((63731698405956251813659:ℝ)/138666221044800000000000) ((34818494554377981363480509965067940043909:ℝ)/79664623007445314767073750000000000000000) ((25147481329144448212219680618271075554489931503390008094921:ℝ)/139273978217511925453922039860271760175636000000000000000000) ((-56851061383:ℝ)/693331105224) ((-31960580183:ℝ)/115555184204000) ((-975739683511:ℝ)/69333110522400000) ((-6429880096350153408880467:ℝ)/159329246014890629534147500) ((-771872075862388944000515713:ℝ)/31865849202978125906829500000) ((1273824430563801254684941356467222513616701:ℝ)/6963698910875596272696101993013588008781800)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece19_frame (v : Fin 4 → ℝ) (q : ℝ) :
    -frameForm pieceX_19 q v = ∑ e ∈ Finset.range 7, ([(((86666388153:ℝ)/125000000000)*(v 0*v 0) + ((-86666388153:ℝ)/15625000000)*(v 0*v 1) + ((86666388153:ℝ)/3906250000)*(v 0*v 2) + ((-86666388153:ℝ)/976562500)*(v 0*v 3) + ((86666388153:ℝ)/7812500000)*(v 1*v 1) + ((-86666388153:ℝ)/976562500)*(v 1*v 2) + ((86666388153:ℝ)/244140625)*(v 1*v 3) + ((86666388153:ℝ)/488281250)*(v 2*v 2) + ((-346665552612:ℝ)/244140625)*(v 2*v 3) + ((693331105224:ℝ)/244140625)*(v 3*v 3)), (((2250546499821:ℝ)/62500000000)*(v 0*v 1) + ((-2250546499821:ℝ)/3125000000)*(v 0*v 2) + ((47261476496241:ℝ)/3906250000)*(v 0*v 3) + ((-2250546499821:ℝ)/15625000000)*(v 1*v 1) + ((6751639499463:ℝ)/1953125000)*(v 1*v 2) + ((-24756011498031:ℝ)/488281250)*(v 1*v 3) + ((-2250546499821:ℝ)/195312500)*(v 2*v 2) + ((58514208995346:ℝ)/244140625)*(v 2*v 3) + ((-189045905984964:ℝ)/244140625)*(v 3*v 3)), (((1512899657259603:ℝ)/976562500000)*(v 0*v 2) + ((-10590297600817221:ℝ)/122070312500)*(v 0*v 3) + ((11441699234829:ℝ)/15625000000)*(v 1*v 1) + ((-1082995209878466:ℝ)/30517578125)*(v 1*v 2) + ((51215055693060567:ℝ)/61035156250)*(v 1*v 3) + ((38781109423359831:ℝ)/122070312500)*(v 2*v 2) + ((-69146318926409868:ℝ)/6103515625)*(v 2*v 3) + ((2692339442892870036:ℝ)/30517578125)*(v 3*v 3)), (((2266508640206561331:ℝ)/24414062500000)*(v 0*v 3) + ((2541220180129971:ℝ)/30517578125)*(v 1*v 2) + ((-30728174657662236531:ℝ)/6103515625000)*(v 1*v 3) + ((-10164880720519884:ℝ)/6103515625)*(v 2*v 2) + ((187267337753668450131:ℝ)/1525878906250)*(v 2*v 3) + ((-1199922990013551481062:ℝ)/762939453125)*(v 3*v 3)), (((18495652930433853993:ℝ)/3051757812500)*(v 1*v 3) + ((17533111373282718:ℝ)/6103515625)*(v 2*v 2) + ((-67588364775625464393:ℝ)/152587890625)*(v 2*v 3) + ((8426614504483269191412:ℝ)/762939453125)*(v 3*v 3)), (((73510674434540193186:ℝ)/152587890625)*(v 2*v 3) + ((-4116597768334250818416:ℝ)/152587890625)*(v 3*v 3)), (((3423712104640624887216:ℝ)/152587890625)*(v 3*v 3))] : List ℝ).getD e 0 * q^e := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3, pieceX_19, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem piece19_frameIntegral (v : Fin 4 → ℝ) :
    ∫ r in Real.log ((6:ℝ)/Real.pi)..Real.log (((13:ℝ)/2)/Real.pi),
      Real.pi*Real.exp r * -frameForm pieceX_19 (Real.pi*Real.exp r) v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((86666388153:ℝ)/250000000000) ((54877000285077:ℝ)/1000000000000) ((438041836553105413:ℝ)/31250000000000) ((605818047289668282091:ℝ)/125000000000000) ((866574324493983:ℝ)/62500000000) ((9275797053705011903:ℝ)/1953125000000) ((7889462158589626870135717:ℝ)/3906250000000000) ((488574893693062933759:ℝ)/244140625000) ((193869877397085537019553133:ℝ)/195312500000000) ((67502607186125058519592794757:ℝ)/122070312500000) i j := by
  simp_rw [piece19_frame v]
  rw [integral_exp_poly, pi_mul_exp_log_div (by norm_num), pi_mul_exp_log_div (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero, Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  push_cast
  ring

theorem piece19_weight {r : ℝ} (hr : r ∈ Set.Ioo (Real.log ((6:ℝ)/Real.pi)) (Real.log (((13:ℝ)/2)/Real.pi))) :
    ((610137792503742789:ℝ)/5000000000000000000) ≤ r^2 * pieceKernel r := by
  obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
  have hLr : ((64702940741:ℝ)/100000000000) ≤ r := by
    refine le_trans ((Real.le_log_iff_exp_le (by positivity)).mpr ?_) hr.1.le
    have h := exp_nat_add_le 0 (f := ((64702940741:ℝ)/100000000000)) (by norm_num) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul_of_nonneg_left Real.pi_lt_d6.le (Real.exp_pos ((64702940741:ℝ)/100000000000)).le]
  have hU : ((138197647320653379583676344329:ℝ)/100000000000000000000000000000) ≤ Real.exp (((64702940741:ℝ)/100000000000)/2) := by
    have h := le_exp_nat_add 0 (f := ((64702940741:ℝ)/100000000000)/2) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hE : Real.exp (2*((13:ℝ)/2)) ≤ ((221206696153577163279378372727:ℝ)/500000000000000000000000) := by
    have h := exp_nat_add_le 13 (f := (0:ℝ)) (by norm_num) (by norm_num)
    rw [show (2:ℝ)*((13:ℝ)/2) = ((13:ℕ):ℝ) + (0:ℝ) by norm_num]
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  exact le_trans (by norm_num) (bulk_weight_ge hqa hqb (by norm_num) (by norm_num) hLr (by norm_num) hU hE)

/-- **Bulk piece 19** on `q ∈ [6, 13/2]`. -/
theorem piece19_integral (v : Fin 4 → ℝ) :
    ((610137792503742789:ℝ)/5000000000000000000) * ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((86666388153:ℝ)/250000000000) ((54877000285077:ℝ)/1000000000000) ((438041836553105413:ℝ)/31250000000000) ((605818047289668282091:ℝ)/125000000000000) ((866574324493983:ℝ)/62500000000) ((9275797053705011903:ℝ)/1953125000000) ((7889462158589626870135717:ℝ)/3906250000000000) ((488574893693062933759:ℝ)/244140625000) ((193869877397085537019553133:ℝ)/195312500000000) ((67502607186125058519592794757:ℝ)/122070312500000) i j ≤
      ∫ r in Real.log ((6:ℝ)/Real.pi)..Real.log (((13:ℝ)/2)/Real.pi),
        thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have h := bulk_piece_integral (rc := Real.log (5/Real.pi)) (Ω := ((610137792503742789:ℝ)/5000000000000000000))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le))
    (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) piece19_X_nsd
    (fun r hr y => by
      obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
      exact piece_19 hqa hqb y)
    (fun r hr => piece19_weight hr) v
  rwa [piece19_frameIntegral] at h

theorem piece20_X_nsd (y : Fin 4 → ℝ) : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * (-pieceX_20 i j) := by
  unfold pieceX_20
  simp only [neg_sym4]
  exact quadForm_nonneg_of_ldl ((802660166369:ℝ)/1000000000000) ((42322446208140764900222959:ℝ)/80266016636900000000000000) ((5466955531978423265290612829285393487547587:ℝ)/10580611552035191225055739750000000000000000) ((34788358421842490719249173448362564579657167950537534119:ℝ)/145785480852757953741083008780943826334602320000000000000) ((-521159574721:ℝ)/8026601663690) ((-700055305019:ℝ)/8026601663690000) ((-23839296859:ℝ)/501662603980625) ((-968757027509403400738514699:ℝ)/42322446208140764900222959000) ((-97858721195343656982501428:ℝ)/5290305776017595612527869875) ((314628997135479187108452112776927842112129:ℝ)/1822318510659474421763537609761797829182529)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece20_frame (v : Fin 4 → ℝ) (q : ℝ) :
    -frameForm pieceX_20 q v = ∑ e ∈ Finset.range 7, ([(((802660166369:ℝ)/1000000000000)*(v 0*v 0) + ((-802660166369:ℝ)/125000000000)*(v 0*v 1) + ((802660166369:ℝ)/31250000000)*(v 0*v 2) + ((-802660166369:ℝ)/7812500000)*(v 0*v 3) + ((802660166369:ℝ)/62500000000)*(v 1*v 1) + ((-802660166369:ℝ)/7812500000)*(v 1*v 2) + ((802660166369:ℝ)/1953125000)*(v 1*v 3) + ((802660166369:ℝ)/3906250000)*(v 2*v 2) + ((-802660166369:ℝ)/488281250)*(v 2*v 3) + ((802660166369:ℝ)/244140625)*(v 3*v 3)), (((25643283715233:ℝ)/625000000000)*(v 0*v 1) + ((-25643283715233:ℝ)/31250000000)*(v 0*v 2) + ((538508958019893:ℝ)/39062500000)*(v 0*v 3) + ((-25643283715233:ℝ)/156250000000)*(v 1*v 1) + ((76929851145699:ℝ)/19531250000)*(v 1*v 2) + ((-282076120867563:ℝ)/4882812500)*(v 1*v 3) + ((-25643283715233:ℝ)/1953125000)*(v 2*v 2) + ((333362688298029:ℝ)/1220703125)*(v 2*v 3) + ((-1077017916039786:ℝ)/1220703125)*(v 3*v 3)), (((34006352883329943:ℝ)/19531250000000)*(v 0*v 2) + ((-238044470183309601:ℝ)/2441406250000)*(v 0*v 3) + ((32344946812017:ℝ)/39062500000)*(v 1*v 1) + ((-195731086943414943:ℝ)/4882812500000)*(v 1*v 2) + ((577666411709488101:ℝ)/610351562500)*(v 1*v 3) + ((438318188033542443:ℝ)/1220703125000)*(v 2*v 2) + ((-781262941702346829:ℝ)/61035156250)*(v 2*v 3) + ((15216299424832735404:ℝ)/152587890625)*(v 3*v 3)), (((251703516700669677:ℝ)/2441406250000)*(v 0*v 3) + ((228366684288110079:ℝ)/2441406250000)*(v 1*v 2) + ((-3448837096734210783:ℝ)/610351562500)*(v 1*v 3) + ((-228366684288110079:ℝ)/122070312500)*(v 2*v 2) + ((21033071786918686866:ℝ)/152587890625)*(v 2*v 3) + ((-269566034789620131612:ℝ)/152587890625)*(v 3*v 3)), (((2066498075431073781:ℝ)/305175781250)*(v 1*v 3) + ((197050823036259579:ℝ)/61035156250)*(v 2*v 2) + ((-15167842240892683986:ℝ)/30517578125)*(v 2*v 3) + ((1892050129276695494568:ℝ)/152587890625)*(v 3*v 3)), (((16548926031860598936:ℝ)/30517578125)*(v 2*v 3) + ((-926739857784193540416:ℝ)/30517578125)*(v 3*v 3)), (((777482215433567499744:ℝ)/30517578125)*(v 3*v 3))] : List ℝ).getD e 0 * q^e := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3, pieceX_20, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem piece20_frameIntegral (v : Fin 4 → ℝ) :
    ∫ r in Real.log (((13:ℝ)/2)/Real.pi)..Real.log ((7:ℝ)/Real.pi),
      Real.pi*Real.exp r * -frameForm pieceX_20 (Real.pi*Real.exp r) v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((802660166369:ℝ)/2000000000000) ((676315456983911:ℝ)/10000000000000) ((360610494590532827:ℝ)/19531250000000) ((2140572467575983594343:ℝ)/312500000000000) ((22905905816250131:ℝ)/1250000000000) ((2109869546961197713117:ℝ)/312500000000000) ((1210777589609629418957479:ℝ)/390625000000000) ((120325467232697935564999:ℝ)/39062500000000) ((16212650021678104927028969:ℝ)/9765625000000) ((12353763180990983873699554439:ℝ)/12207031250000) i j := by
  simp_rw [piece20_frame v]
  rw [integral_exp_poly, pi_mul_exp_log_div (by norm_num), pi_mul_exp_log_div (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero, Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  push_cast
  ring

theorem piece20_weight {r : ℝ} (hr : r ∈ Set.Ioo (Real.log (((13:ℝ)/2)/Real.pi)) (Real.log ((7:ℝ)/Real.pi))) :
    ((2137128425969463:ℝ)/25000000000000000) ≤ r^2 * pieceKernel r := by
  obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
  have hLr : ((727072107079:ℝ)/1000000000000) ≤ r := by
    refine le_trans ((Real.le_log_iff_exp_le (by positivity)).mpr ?_) hr.1.le
    have h := exp_nat_add_le 0 (f := ((727072107079:ℝ)/1000000000000)) (by norm_num) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul_of_nonneg_left Real.pi_lt_d6.le (Real.exp_pos ((727072107079:ℝ)/1000000000000)).le]
  have hU : ((35960167693519497750244564009:ℝ)/25000000000000000000000000000) ≤ Real.exp (((727072107079:ℝ)/1000000000000)/2) := by
    have h := le_exp_nat_add 0 (f := ((727072107079:ℝ)/1000000000000)/2) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hE : Real.exp (2*(7:ℝ)) ≤ ((60130214251891031783026941569:ℝ)/50000000000000000000000) := by
    have h := exp_nat_add_le 14 (f := (0:ℝ)) (by norm_num) (by norm_num)
    rw [show (2:ℝ)*(7:ℝ) = ((14:ℕ):ℝ) + (0:ℝ) by norm_num]
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  exact le_trans (by norm_num) (bulk_weight_ge hqa hqb (by norm_num) (by norm_num) hLr (by norm_num) hU hE)

/-- **Bulk piece 20** on `q ∈ [13/2, 7]`. -/
theorem piece20_integral (v : Fin 4 → ℝ) :
    ((2137128425969463:ℝ)/25000000000000000) * ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((802660166369:ℝ)/2000000000000) ((676315456983911:ℝ)/10000000000000) ((360610494590532827:ℝ)/19531250000000) ((2140572467575983594343:ℝ)/312500000000000) ((22905905816250131:ℝ)/1250000000000) ((2109869546961197713117:ℝ)/312500000000000) ((1210777589609629418957479:ℝ)/390625000000000) ((120325467232697935564999:ℝ)/39062500000000) ((16212650021678104927028969:ℝ)/9765625000000) ((12353763180990983873699554439:ℝ)/12207031250000) i j ≤
      ∫ r in Real.log (((13:ℝ)/2)/Real.pi)..Real.log ((7:ℝ)/Real.pi),
        thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have h := bulk_piece_integral (rc := Real.log (5/Real.pi)) (Ω := ((2137128425969463:ℝ)/25000000000000000))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le))
    (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) piece20_X_nsd
    (fun r hr y => by
      obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
      exact piece_20 hqa hqb y)
    (fun r hr => piece20_weight hr) v
  rwa [piece20_frameIntegral] at h

theorem piece21_X_nsd (y : Fin 4 → ℝ) : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * (-pieceX_21 i j) := by
  unfold pieceX_21
  simp only [neg_sym4]
  exact quadForm_nonneg_of_ldl ((81928772437:ℝ)/100000000000) ((341890481818957011615457:ℝ)/640068534664062500000000) ((11663715773939137553679862351360576318464191:ℝ)/21880990836413248743389248000000000000000000) ((2507973040418089390093949755404698850611922208024901843361:ℝ)/9330972619151310042943889881088461054771352800000000000000) ((-108220279563:ℝ)/2048219310925) ((-215780281383:ℝ)/8192877243700000) ((-211484429777:ℝ)/8192877243700000) ((-112706168706407000094140629:ℝ)/10940495418206624371694624000) ((-157327745099732194764444951:ℝ)/10940495418206624371694624000) ((1893170085889209071230108465372965619243429:ℝ)/11663715773939137553679862351360576318464191)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece21_frame (v : Fin 4 → ℝ) (q : ℝ) :
    -frameForm pieceX_21 q v = ∑ e ∈ Finset.range 7, ([(((81928772437:ℝ)/100000000000)*(v 0*v 0) + ((-81928772437:ℝ)/12500000000)*(v 0*v 1) + ((81928772437:ℝ)/3125000000)*(v 0*v 2) + ((-81928772437:ℝ)/781250000)*(v 0*v 3) + ((81928772437:ℝ)/6250000000)*(v 1*v 1) + ((-81928772437:ℝ)/781250000)*(v 1*v 2) + ((81928772437:ℝ)/195312500)*(v 1*v 3) + ((81928772437:ℝ)/390625000)*(v 2*v 2) + ((-81928772437:ℝ)/48828125)*(v 2*v 3) + ((163857544874:ℝ)/48828125)*(v 3*v 3)), (((808664846433:ℝ)/19531250000)*(v 0*v 1) + ((-808664846433:ℝ)/976562500)*(v 0*v 2) + ((16981961775093:ℝ)/1220703125)*(v 0*v 3) + ((-808664846433:ℝ)/4882812500)*(v 1*v 1) + ((4851989078598:ℝ)/1220703125)*(v 1*v 2) + ((-71162506486104:ℝ)/1220703125)*(v 1*v 3) + ((-3234659385732:ℝ)/244140625)*(v 2*v 2) + ((336404576116128:ℝ)/1220703125)*(v 2*v 3) + ((-1086845553605952:ℝ)/1220703125)*(v 3*v 3)), (((33969250709920851:ℝ)/19531250000000)*(v 0*v 2) + ((-237784754969445957:ℝ)/2441406250000)*(v 0*v 3) + ((4056462588213:ℝ)/4882812500)*(v 1*v 1) + ((-196227754238440851:ℝ)/4882812500000)*(v 1*v 2) + ((578527612379337957:ℝ)/610351562500)*(v 1*v 3) + ((439615509531220851:ℝ)/1220703125000)*(v 2*v 2) + ((-783393466949546553:ℝ)/61035156250)*(v 2*v 3) + ((15262339031093247828:ℝ)/152587890625)*(v 3*v 3)), (((62285815681192047:ℝ)/610351562500)*(v 0*v 3) + ((227970418601019753:ℝ)/2441406250000)*(v 1*v 2) + ((-344072912313904473:ℝ)/61035156250)*(v 1*v 3) + ((-227970418601019753:ℝ)/122070312500)*(v 2*v 2) + ((20994451355417565711:ℝ)/152587890625)*(v 2*v 3) + ((-53817957065139660456:ℝ)/30517578125)*(v 3*v 3)), (((1027201780683424332:ℝ)/152587890625)*(v 1*v 3) + ((196702635608808453:ℝ)/61035156250)*(v 2*v 2) + ((-15124154716826970696:ℝ)/30517578125)*(v 2*v 3) + ((1887288461482688847072:ℝ)/152587890625)*(v 3*v 3)), (((3307340812810902588:ℝ)/6103515625)*(v 2*v 3) + ((-185211085517410544928:ℝ)/6103515625)*(v 3*v 3)), (((782197225087200846336:ℝ)/30517578125)*(v 3*v 3))] : List ℝ).getD e 0 * q^e := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3, pieceX_21, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem piece21_frameIntegral (v : Fin 4 → ℝ) :
    ∫ r in Real.log ((7:ℝ)/Real.pi)..Real.log (((15:ℝ)/2)/Real.pi),
      Real.pi*Real.exp r * -frameForm pieceX_21 (Real.pi*Real.exp r) v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((81928772437:ℝ)/200000000000) ((91756902875303:ℝ)/1250000000000) ((6677888341033137327:ℝ)/312500000000000) ((132477452548225326449:ℝ)/15625000000000) ((6640112356704877:ℝ)/312500000000) ((2620441020189134367069:ℝ)/312500000000000) ((807703728365816438040083:ℝ)/195312500000000) ((32154039891916613311967:ℝ)/7812500000000) ((46759564123931837149432037:ℝ)/19531250000000) ((9666904528291787403160718073:ℝ)/6103515625000) i j := by
  simp_rw [piece21_frame v]
  rw [integral_exp_poly, pi_mul_exp_log_div (by norm_num), pi_mul_exp_log_div (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero, Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  push_cast
  ring

theorem piece21_weight {r : ℝ} (hr : r ∈ Set.Ioo (Real.log ((7:ℝ)/Real.pi)) (Real.log (((15:ℝ)/2)/Real.pi))) :
    ((556094389573308239:ℝ)/10000000000000000000) ≤ r^2 * pieceKernel r := by
  obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
  have hLr : ((400590035911:ℝ)/500000000000) ≤ r := by
    refine le_trans ((Real.le_log_iff_exp_le (by positivity)).mpr ?_) hr.1.le
    have h := exp_nat_add_le 0 (f := ((400590035911:ℝ)/500000000000)) (by norm_num) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul_of_nonneg_left Real.pi_lt_d6.le (Real.exp_pos ((400590035911:ℝ)/500000000000)).le]
  have hU : ((149270517031132927007630466567:ℝ)/100000000000000000000000000000) ≤ Real.exp (((400590035911:ℝ)/500000000000)/2) := by
    have h := le_exp_nat_add 0 (f := ((400590035911:ℝ)/500000000000)/2) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hE : Real.exp (2*((15:ℝ)/2)) ≤ ((163450868750740134883107193171:ℝ)/50000000000000000000000) := by
    have h := exp_nat_add_le 15 (f := (0:ℝ)) (by norm_num) (by norm_num)
    rw [show (2:ℝ)*((15:ℝ)/2) = ((15:ℕ):ℝ) + (0:ℝ) by norm_num]
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  exact le_trans (by norm_num) (bulk_weight_ge hqa hqb (by norm_num) (by norm_num) hLr (by norm_num) hU hE)

/-- **Bulk piece 21** on `q ∈ [7, 15/2]`. -/
theorem piece21_integral (v : Fin 4 → ℝ) :
    ((556094389573308239:ℝ)/10000000000000000000) * ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((81928772437:ℝ)/200000000000) ((91756902875303:ℝ)/1250000000000) ((6677888341033137327:ℝ)/312500000000000) ((132477452548225326449:ℝ)/15625000000000) ((6640112356704877:ℝ)/312500000000) ((2620441020189134367069:ℝ)/312500000000000) ((807703728365816438040083:ℝ)/195312500000000) ((32154039891916613311967:ℝ)/7812500000000) ((46759564123931837149432037:ℝ)/19531250000000) ((9666904528291787403160718073:ℝ)/6103515625000) i j ≤
      ∫ r in Real.log ((7:ℝ)/Real.pi)..Real.log (((15:ℝ)/2)/Real.pi),
        thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have h := bulk_piece_integral (rc := Real.log (5/Real.pi)) (Ω := ((556094389573308239:ℝ)/10000000000000000000))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le))
    (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) piece21_X_nsd
    (fun r hr y => by
      obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
      exact piece_21 hqa hqb y)
    (fun r hr => piece21_weight hr) v
  rwa [piece21_frameIntegral] at h

theorem piece22_X_nsd (y : Fin 4 → ℝ) : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * (-pieceX_22 i j) := by
  unfold pieceX_22
  simp only [neg_sym4]
  exact quadForm_nonneg_of_ldl ((166381367997:ℝ)/200000000000) ((14956515073416977769375213:ℝ)/27730227999500000000000000) ((17016073163968553832625546754825998016344623:ℝ)/31159406402952037019531693750000000000000000) ((7184573411558596472955440256937381117683085325866934393181409:ℝ)/24503145356114717518980787326949437143536257120000000000000000) ((-121747395577:ℝ)/2773022799950) ((-640780238357:ℝ)/83190683998500000) ((-35422045597:ℝ)/3327627359940000) ((-173042593665065883733926989:ℝ)/149565150734169777693752130000) ((-67694175285834579578962469:ℝ)/5982606029366791107750085200) ((31247962257893764292954817711711593239651925:ℝ)/204192877967622645991506561057911976196135476)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y

theorem piece22_frame (v : Fin 4 → ℝ) (q : ℝ) :
    -frameForm pieceX_22 q v = ∑ e ∈ Finset.range 7, ([(((166381367997:ℝ)/200000000000)*(v 0*v 0) + ((-166381367997:ℝ)/25000000000)*(v 0*v 1) + ((166381367997:ℝ)/6250000000)*(v 0*v 2) + ((-166381367997:ℝ)/1562500000)*(v 0*v 3) + ((166381367997:ℝ)/12500000000)*(v 1*v 1) + ((-166381367997:ℝ)/1562500000)*(v 1*v 2) + ((166381367997:ℝ)/390625000)*(v 1*v 3) + ((166381367997:ℝ)/781250000)*(v 2*v 2) + ((-166381367997:ℝ)/97656250)*(v 2*v 3) + ((166381367997:ℝ)/48828125)*(v 3*v 3)), (((26052931759743:ℝ)/625000000000)*(v 0*v 1) + ((-26052931759743:ℝ)/31250000000)*(v 0*v 2) + ((547111566954603:ℝ)/39062500000)*(v 0*v 3) + ((-26052931759743:ℝ)/156250000000)*(v 1*v 1) + ((78158795279229:ℝ)/19531250000)*(v 1*v 2) + ((-286582249357173:ℝ)/4882812500)*(v 1*v 3) + ((-26052931759743:ℝ)/1953125000)*(v 2*v 2) + ((338688112876659:ℝ)/1220703125)*(v 2*v 3) + ((-1094223133909206:ℝ)/1220703125)*(v 3*v 3)), (((339356306658484929:ℝ)/195312500000000)*(v 0*v 2) + ((-2375494146609394503:ℝ)/24414062500000)*(v 0*v 3) + ((1016660148471:ℝ)/1220703125)*(v 1*v 1) + ((-1966012544212084929:ℝ)/48828125000000)*(v 1*v 2) + ((5791472245471954503:ℝ)/6103515625000)*(v 1*v 3) + ((4405996900542484929:ℝ)/12207031250000)*(v 2*v 2) + ((-7850025117700574787:ℝ)/610351562500)*(v 2*v 3) + ((76486528369332549006:ℝ)/762939453125)*(v 3*v 3)), (((1235680952215104717:ℝ)/12207031250000)*(v 0*v 3) + ((2276883133277143887:ℝ)/24414062500000)*(v 1*v 2) + ((-8586931442577555963:ℝ)/1525878906250)*(v 1*v 3) + ((-2276883133277143887:ℝ)/1220703125000)*(v 2*v 2) + ((209667727032650303151:ℝ)/1525878906250)*(v 2*v 3) + ((-1343750006175821024424:ℝ)/762939453125)*(v 3*v 3)), (((10227634611589585701:ℝ)/1525878906250)*(v 1*v 3) + ((1965002506945235487:ℝ)/610351562500)*(v 2*v 2) + ((-75475339417645765038:ℝ)/152587890625)*(v 2*v 3) + ((9421052441972373506808:ℝ)/762939453125)*(v 3*v 3)), (((82687953113396139222:ℝ)/152587890625)*(v 2*v 3) + ((-4630525374350183796432:ℝ)/152587890625)*(v 3*v 3)), (((3933654006381397379424:ℝ)/152587890625)*(v 3*v 3))] : List ℝ).getD e 0 * q^e := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3, pieceX_22, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  ring

theorem piece22_frameIntegral (v : Fin 4 → ℝ) :
    ∫ r in Real.log (((15:ℝ)/2)/Real.pi)..Real.log ((8:ℝ)/Real.pi),
      Real.pi*Real.exp r * -frameForm pieceX_22 (Real.pi*Real.exp r) v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((166381367997:ℝ)/400000000000) ((791002747752333:ℝ)/10000000000000) ((76531674509471963353:ℝ)/3125000000000000) ((16183956523302577668803:ℝ)/1562500000000000) ((30475855444545033:ℝ)/1250000000000) ((6416951408729100802129:ℝ)/625000000000000) ((5289293532574616554718047:ℝ)/976562500000000) ((84303408812123270816467:ℝ)/15625000000000) ((658122193475888155707533499:ℝ)/195312500000000) ((18338539974455310856608821743:ℝ)/7629394531250) i j := by
  simp_rw [piece22_frame v]
  rw [integral_exp_poly, pi_mul_exp_log_div (by norm_num), pi_mul_exp_log_div (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero, Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33]
  push_cast
  ring

theorem piece22_weight {r : ℝ} (hr : r ∈ Set.Ioo (Real.log (((15:ℝ)/2)/Real.pi)) (Real.log ((8:ℝ)/Real.pi))) :
    ((341263682846572121:ℝ)/10000000000000000000) ≤ r^2 * pieceKernel r := by
  obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
  have hLr : ((87017293641:ℝ)/100000000000) ≤ r := by
    refine le_trans ((Real.le_log_iff_exp_le (by positivity)).mpr ?_) hr.1.le
    have h := exp_nat_add_le 0 (f := ((87017293641:ℝ)/100000000000)) (by norm_num) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith [mul_le_mul_of_nonneg_left Real.pi_lt_d6.le (Real.exp_pos ((87017293641:ℝ)/100000000000)).le]
  have hU : ((38627415536303631023205051693:ℝ)/25000000000000000000000000000) ≤ Real.exp (((87017293641:ℝ)/100000000000)/2) := by
    have h := le_exp_nat_add 0 (f := ((87017293641:ℝ)/100000000000)/2) (by norm_num)
    rw [Nat.cast_zero, zero_add] at h
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  have hE : Real.exp (2*(8:ℝ)) ≤ ((888611052788040982906926536603:ℝ)/100000000000000000000000) := by
    have h := exp_nat_add_le 16 (f := (0:ℝ)) (by norm_num) (by norm_num)
    rw [show (2:ℝ)*(8:ℝ) = ((16:ℕ):ℝ) + (0:ℝ) by norm_num]
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    linarith
  exact le_trans (by norm_num) (bulk_weight_ge hqa hqb (by norm_num) (by norm_num) hLr (by norm_num) hU hE)

/-- **Bulk piece 22** on `q ∈ [15/2, 8]`. -/
theorem piece22_integral (v : Fin 4 → ℝ) :
    ((341263682846572121:ℝ)/10000000000000000000) * ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((166381367997:ℝ)/400000000000) ((791002747752333:ℝ)/10000000000000) ((76531674509471963353:ℝ)/3125000000000000) ((16183956523302577668803:ℝ)/1562500000000000) ((30475855444545033:ℝ)/1250000000000) ((6416951408729100802129:ℝ)/625000000000000) ((5289293532574616554718047:ℝ)/976562500000000) ((84303408812123270816467:ℝ)/15625000000000) ((658122193475888155707533499:ℝ)/195312500000000) ((18338539974455310856608821743:ℝ)/7629394531250) i j ≤
      ∫ r in Real.log (((15:ℝ)/2)/Real.pi)..Real.log ((8:ℝ)/Real.pi),
        thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have h := bulk_piece_integral (rc := Real.log (5/Real.pi)) (Ω := ((341263682846572121:ℝ)/10000000000000000000))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le))
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le))
    (Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) piece22_X_nsd
    (fun r hr y => by
      obtain ⟨hqa, hqb⟩ := scale_mem_of_mem (by positivity) (by norm_num) hr
      exact piece_22 hqa hqb y)
    (fun r hr => piece22_weight hr) v
  rwa [piece22_frameIntegral] at h

end
end RHTower.ThetaCuspOddFourPieces
