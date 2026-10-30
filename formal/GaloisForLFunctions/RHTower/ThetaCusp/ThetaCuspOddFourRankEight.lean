import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourCertificateIntegrals1
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourCertificateIntegrals2
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourCertificateIntegrals3
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourCertificateIntegrals4

/-!
# The eighth signed section: `I_7(a) ≥ 0` at every critical aperture

Split the ray at `r_c = log(5/π)` (scale `q = π e^r = 5`). Beyond `r_c` the odd native fibre form
is nonnegative: on `q ∈ (5, 6]` by the bulk piece certificates, beyond `6` by the first-atom
coercivity. Below `r_c` its negative part, weighted by `r²`, is paid by the `r²`-weighted bulk on
`q ∈ [5, 8]`: the fifteen seam pieces on `q ∈ [π, 5]` and the eight bulk pieces on `q ∈ [5, 8]`
bound the seam-split integral over `(0, log(8/π)]` below by an explicit quadratic form in `v`,
which is positive semidefinite by an exact `LDLᵀ` factorization; the tail beyond `log(8/π)` is
nonnegative. The aperture-free seam split then gives the size-eight signed Hankel section and
`I_7(a) ≥ 0` for every `0 < a < 1/2`.
-/

open MeasureTheory Set
namespace RHTower.ThetaCuspOddFourPieces
noncomputable section
open ThetaCuspOddCentral ThetaCuspOddFourNativeBulk ThetaCuspOddFourCertificateTools

/-- The piece edges in the scale `q`. -/
def pieceEdges : List ℝ := [Real.pi, ((16:ℝ)/5), ((33:ℝ)/10), ((17:ℝ)/5), ((7:ℝ)/2), ((18:ℝ)/5), ((37:ℝ)/10), ((19:ℝ)/5), ((39:ℝ)/10), (4:ℝ), ((41:ℝ)/10), ((21:ℝ)/5), ((22:ℝ)/5), ((23:ℝ)/5), ((24:ℝ)/5), (5:ℝ), ((21:ℝ)/4), ((11:ℝ)/2), ((23:ℝ)/4), (6:ℝ), ((13:ℝ)/2), (7:ℝ), ((15:ℝ)/2), (8:ℝ)]

theorem pieceEdges_ge {k : ℕ} (hk : k < 24) : Real.pi ≤ pieceEdges.getD k Real.pi := by
  interval_cases k <;> simp only [pieceEdges, List.getD_cons_succ, List.getD_cons_zero] <;>
    linarith [Real.pi_lt_d2]

theorem pieceEdge_log_nonneg {k : ℕ} (hk : k < 24) :
    0 ≤ Real.log (pieceEdges.getD k Real.pi / Real.pi) :=
  Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [pieceEdges_ge hk])

/-- The final comparison: the bulk reserve dominates the seam cost. -/
theorem finalForm_nonneg (v : Fin 4 → ℝ) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * sym4 ((9057754822559147539403092084654229:ℝ)/25000000000000000000000000000000000) ((33649373865335126021655561732748377667:ℝ)/625000000000000000000000000000000000) ((5072225811117657754016786429892642140737:ℝ)/390625000000000000000000000000000000) ((66763518699872545430465034125757998759160117:ℝ)/15625000000000000000000000000000000000) ((10091170902286028037912954499429101853447:ℝ)/781250000000000000000000000000000000) ((33101176804632977978604836907032326368369403:ℝ)/7812500000000000000000000000000000000) ((6822108927818430964602543653196455801197151853:ℝ)/3906250000000000000000000000000000000) ((8497177468438514464621436296269378118787779467:ℝ)/4882812500000000000000000000000000000) ((8364105502904568051132379192812100375278128178943:ℝ)/9765625000000000000000000000000000000) ((1488740380006922622650686218817579185094091268666647:ℝ)/3051757812500000000000000000000000000) i j :=
  quadForm_nonneg_of_ldl ((9057754822559147539403092084654229:ℝ)/25000000000000000000000000000000000) ((695786676579897693452583036557117424167937843596202728692186966180071184371:ℝ)/141527419102486680303173313822722328125000000000000000000000000000000000) ((289751421942729519945547766632901784759097168031477517257793890494946211391766581268430544791527238444323091217419718963:ℝ)/1509953725216791869471751381417355521197781778637592727196586298133835035527343750000000000000000000000000000000) ((1601439395124934238904902922093281424346459939896615838317784069458717609799168735510059712523869702331630131068554647676748805072488301095067896411389055423878989539034173:ℝ)/113184149196378718728729596340977259671522331262295905178825738474588363824908820807980681559190327517313707506804577719921875000000000000000000000000000000000) ((33649373865335126021655561732748377667:ℝ)/226443870563978688485077302116355725) ((40577806488941262032134291439141137125896:ℝ)/1132219352819893442425386510581778625) ((66763518699872545430465034125757998759160117:ℝ)/5661096764099467212126932552908893125) ((544268552387955768291828520648506338232803573919588419206500677116566949262746:ℝ)/1159644460966496155754305060928529040279896405993671214486978276966785307285) ((1310916134266605547203568023189193679791809506562669059762117292860450841307908887:ℝ)/5798222304832480778771525304642645201399482029968356072434891384833926536425) ((2743113710708309297230731602924651546367739355519161619886895857582865000562200046542570719201843346556849526104811762796981:ℝ)/2897514219427295199455477666329017847590971680314775172577938904949462113917665812684305447915272384443230912174197189630)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) v

/-- **The seam-split inequality at `r_c = log(5/π)`.** -/
theorem oddFour_seamSplit_logFive (v : Fin 4 → ℝ) :
    0 ≤ ∫ r in Ioi 0, thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
  have hr8 : 0 ≤ Real.log (8/Real.pi) :=
    Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])
  rw [seamSplit_integral_split hr8 v]
  have htail : 0 ≤ ∫ r in Ioi (Real.log (8/Real.pi)),
      thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v := by
    refine setIntegral_nonneg measurableSet_Ioi fun r hr => ?_
    have h6 : Real.log (6/Real.pi) < r := lt_of_le_of_lt (Real.log_le_log (by positivity)
      (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le)) hr
    have h5 : ¬ r ≤ Real.log (5/Real.pi) := not_le.mpr (lt_of_le_of_lt (Real.log_le_log
      (by positivity) (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le)) h6)
    unfold thetaCuspOddFourSeamSplitIntegrand
    rw [if_neg h5]
    exact mul_nonneg (sq_nonneg r) (thetaCuspOddFourFibreForm_nonneg_of_log_six h6 v)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun r => thetaCuspOddFourSeamSplitIntegrand (Real.log (5/Real.pi)) r v) (μ := volume)
    (a := fun k => Real.log (pieceEdges.getD k Real.pi / Real.pi)) (n := 23)
    (fun k hk => intervalIntegrable_seamSplit (pieceEdge_log_nonneg (by omega))
      (pieceEdge_log_nonneg (by omega)) v)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pieceEdges,
    List.getD_cons_succ, List.getD_cons_zero] at hsum
  have h0 : Real.log (Real.pi/Real.pi) = 0 := by rw [div_self Real.pi_pos.ne', Real.log_one]
  have i0 := piece0_integral v
  have i1 := piece1_integral v
  have i2 := piece2_integral v
  have i3 := piece3_integral v
  have i4 := piece4_integral v
  have i5 := piece5_integral v
  have i6 := piece6_integral v
  have i7 := piece7_integral v
  have i8 := piece8_integral v
  have i9 := piece9_integral v
  have i10 := piece10_integral v
  have i11 := piece11_integral v
  have i12 := piece12_integral v
  have i13 := piece13_integral v
  have i14 := piece14_integral v
  have i15 := piece15_integral v
  have i16 := piece16_integral v
  have i17 := piece17_integral v
  have i18 := piece18_integral v
  have i19 := piece19_integral v
  have i20 := piece20_integral v
  have i21 := piece21_integral v
  have i22 := piece22_integral v
  have hF := finalForm_nonneg v
  rw [h0] at hsum i0
  simp only [Fin.sum_univ_four, sym4_00, sym4_01, sym4_02, sym4_03, sym4_10, sym4_11, sym4_12, sym4_13, sym4_20, sym4_21, sym4_22, sym4_23, sym4_30, sym4_31, sym4_32, sym4_33] at i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 hF
  linarith

/-- **The bulk hypothesis at `r_c = log(5/π)`.** Beyond `log(5/π)` the odd native fibre form is
nonnegative. -/
theorem oddFour_fibre_nonneg_beyond_logFive {r : ℝ} (hr : Real.log (5/Real.pi) < r)
    (v : Fin 4 → ℝ) : 0 ≤ thetaCuspOddFourFibreForm r v := by
  by_cases h6 : Real.log (6/Real.pi) < r
  · exact thetaCuspOddFourFibreForm_nonneg_of_log_six h6 v
  replace h6 := not_lt.mp h6
  have hr0 : 0 ≤ r := le_trans (Real.log_nonneg (by
    rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])) hr.le
  have hq5 : 5 < Real.pi * Real.exp r := by
    have h := Real.exp_lt_exp.mpr hr
    rw [Real.exp_log (by positivity), div_lt_iff₀ Real.pi_pos] at h
    linarith
  have hq6 : Real.pi * Real.exp r ≤ 6 := by
    have h := Real.exp_le_exp.mpr h6
    rw [Real.exp_log (by positivity), le_div_iff₀ Real.pi_pos] at h
    linarith
  rcases le_or_gt (Real.pi * Real.exp r) ((21:ℝ)/4) with h1 | h1
  · exact fibreForm_nonneg_of_bulk hr0 piece15_X_nsd (fun y => piece_15 hq5.le h1 y) v
  rcases le_or_gt (Real.pi * Real.exp r) ((11:ℝ)/2) with h2 | h2
  · exact fibreForm_nonneg_of_bulk hr0 piece16_X_nsd (fun y => piece_16 h1.le h2 y) v
  rcases le_or_gt (Real.pi * Real.exp r) ((23:ℝ)/4) with h3 | h3
  · exact fibreForm_nonneg_of_bulk hr0 piece17_X_nsd (fun y => piece_17 h2.le h3 y) v
  · exact fibreForm_nonneg_of_bulk hr0 piece18_X_nsd (fun y => piece_18 h3.le hq6 y) v

theorem log_five_div_pi_pos : 0 < Real.log (5/Real.pi) :=
  Real.log_pos (by rw [lt_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])

end
end RHTower.ThetaCuspOddFourPieces

namespace RHTower
open MeasureTheory Set ThetaCuspOddFourPieces

/-- **The odd block of the eighth section** is positive semidefinite at every critical aperture. -/
theorem thetaCuspCenterMixedOddFour_posSemidef {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    (thetaCuspCenterMixedOddFour a).PosSemidef :=
  thetaCuspCenterMixedOddFour_posSemidef_of_seamSplit log_five_div_pi_pos
    (fun _ hr v => oddFour_fibre_nonneg_beyond_logFive hr v) oddFour_seamSplit_logFive ha0 ha

/-- **The size-eight signed center-mixed Hankel section** is positive semidefinite at every
critical aperture `0 < a < 1/2`. -/
theorem thetaCuspCenterMixedSignedHankel_eight_posSemidef {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    (thetaCuspCenterMixedSignedHankel a 8).PosSemidef :=
  thetaCuspCenterMixedSignedHankel_eight_posSemidef_of_oddFour ha0 ha
    (thetaCuspCenterMixedOddFour_posSemidef ha0 ha)

/-- **The first successor test: `I_7(a) ≥ 0`** for every critical aperture `0 < a < 1/2`. -/
theorem thetaCuspNativeSuccessorIntegral_seven_nonneg {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    0 ≤ ∫ r : ℝ in Ioi 0, r*Real.sinh (a*r)*thetaCuspNativeSuccessorSource a 7 (r/2) :=
  thetaCuspNativeSuccessorIntegral_seven_nonneg_of_seamSplit log_five_div_pi_pos
    (fun _ hr v => oddFour_fibre_nonneg_beyond_logFive hr v) oddFour_seamSplit_logFive ha0 ha

end RHTower
