import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourCentralBound
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourCertificateTools

/-!
# Piecewise certificates: the common piece matrix

For a constant matrix `X` the piece matrix is
`W(q) = E(q) − q⁶·8000(2q−3)²e^{-529q/50}·diag(ρ̃) + 8q⁷(2q−3)²·X`. If `W(q)` is positive
semidefinite then the native odd form at `c = B(1/q)y` is at least `−K(q)·8q(2q−3)²·yᵀXy`.
-/

open Polynomial
namespace RHTower.ThetaCuspOddFourPieces
noncomputable section
open ThetaCuspOddCentralTail ThetaCuspOddFourCentralEntries ThetaCuspOddFourCentralBound

/-- The piece matrix with compensation `X`. -/
def pieceW (q : ℝ) (X : Fin 4 → Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  centralEntryMat q i j -
    (if i = j then q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*tailWeight i) else 0) +
    8*q^7*(2*q-3)^2*X i j

theorem bm_00 : basisMajorant 0 0 = 1 := rfl
theorem bm_01 : basisMajorant 0 1 = 1 := rfl
theorem bm_02 : basisMajorant 0 2 = 5/4 := rfl
theorem bm_03 : basisMajorant 0 3 = 5/4 := rfl
theorem bm_10 : basisMajorant 1 0 = 0 := rfl
theorem bm_11 : basisMajorant 1 1 = 1/72 := rfl
theorem bm_12 : basisMajorant 1 2 = 5/144 := rfl
theorem bm_13 : basisMajorant 1 3 = 5/96 := rfl
theorem bm_20 : basisMajorant 2 0 = 0 := rfl
theorem bm_21 : basisMajorant 2 1 = 0 := rfl
theorem bm_22 : basisMajorant 2 2 = 1/6912 := rfl
theorem bm_23 : basisMajorant 2 3 = 1/2304 := rfl
theorem bm_30 : basisMajorant 3 0 = 0 := rfl
theorem bm_31 : basisMajorant 3 1 = 0 := rfl
theorem bm_32 : basisMajorant 3 2 = 0 := rfl
theorem bm_33 : basisMajorant 3 3 = 1/1161216 := rfl

theorem tailWeight_0 : tailWeight 0 = ((10465499600:ℝ)/59049) := by
  simp only [tailWeight, tailFactor, Fin.sum_univ_four, bm_00, bm_01, bm_02, bm_03, bm_10, bm_11, bm_12, bm_13, bm_20, bm_21, bm_22, bm_23, bm_30, bm_31, bm_32, bm_33, fin4_v0, fin4_v1, fin4_v2, fin4_v3]
  norm_num [Nat.factorial]

theorem tailWeight_1 : tailWeight 1 = ((4814744136400:ℝ)/531441) := by
  simp only [tailWeight, tailFactor, Fin.sum_univ_four, bm_00, bm_01, bm_02, bm_03, bm_10, bm_11, bm_12, bm_13, bm_20, bm_21, bm_22, bm_23, bm_30, bm_31, bm_32, bm_33, fin4_v0, fin4_v1, fin4_v2, fin4_v3]
  norm_num [Nat.factorial]

theorem tailWeight_2 : tailWeight 2 = ((2570430941234500:ℝ)/4782969) := by
  simp only [tailWeight, tailFactor, Fin.sum_univ_four, bm_00, bm_01, bm_02, bm_03, bm_10, bm_11, bm_12, bm_13, bm_20, bm_21, bm_22, bm_23, bm_30, bm_31, bm_32, bm_33, fin4_v0, fin4_v1, fin4_v2, fin4_v3]
  norm_num [Nat.factorial]

theorem tailWeight_3 : tailWeight 3 = ((3308571812705231500:ℝ)/129140163) := by
  simp only [tailWeight, tailFactor, Fin.sum_univ_four, bm_00, bm_01, bm_02, bm_03, bm_10, bm_11, bm_12, bm_13, bm_20, bm_21, bm_22, bm_23, bm_30, bm_31, bm_32, bm_33, fin4_v0, fin4_v1, fin4_v2, fin4_v3]
  norm_num [Nat.factorial]

theorem centralNum13_00_list (q : ℝ) :
    centralNum13_00 q = ∑ e ∈ Finset.range 11, ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (600:ℝ), (-7776:ℝ), (16800:ℝ), (-9216:ℝ)] : List ℝ).getD e 0 * q^e := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  unfold centralNum13_00
  ring

theorem centralNum13_01_list (q : ℝ) :
    centralNum13_01 q = ∑ e ∈ Finset.range 12, ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-6288:ℝ), (81024:ℝ), (-238720:ℝ), (246784:ℝ), (-98304:ℝ)] : List ℝ).getD e 0 * q^e := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  unfold centralNum13_01
  ring

theorem centralNum13_02_list (q : ℝ) :
    centralNum13_02 q = ∑ e ∈ Finset.range 13, ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82080:ℝ), (-967680:ℝ), (3257600:ℝ), (-4474880:ℝ), (2908160:ℝ), (-786432:ℝ)] : List ℝ).getD e 0 * q^e := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  unfold centralNum13_02
  ring

theorem centralNum13_03_list (q : ℝ) :
    centralNum13_03 q = ∑ e ∈ Finset.range 14, ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-812160:ℝ), (8985600:ℝ), (-32225280:ℝ), (52019200:ℝ), ((-305233920:ℝ)/7), ((135528448:ℝ)/7), ((-25165824:ℝ)/7)] : List ℝ).getD e 0 * q^e := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  unfold centralNum13_03
  ring

theorem centralNum13_11_list (q : ℝ) :
    centralNum13_11 q = ∑ e ∈ Finset.range 13, ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-3444:ℝ), (162624:ℝ), (-1531216:ℝ), (4800960:ℝ), (-6350848:ℝ), ((12025856:ℝ)/3), (-1048576:ℝ)] : List ℝ).getD e 0 * q^e := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  unfold centralNum13_11
  ring

theorem centralNum13_12_list (q : ℝ) :
    centralNum13_12 q = ∑ e ∈ Finset.range 14, ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (122790:ℝ), (-3586680:ℝ), (28529720:ℝ), (-90761600:ℝ), (137804800:ℝ), ((-332136448:ℝ)/3), ((141819904:ℝ)/3), (-8388608:ℝ)] : List ℝ).getD e 0 * q^e := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  unfold centralNum13_12
  ring

theorem centralNum13_13_list (q : ℝ) :
    centralNum13_13 q = ∑ e ∈ Finset.range 15, ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2325540:ℝ), (52589280:ℝ), (-375655200:ℝ), (1192958720:ℝ), (-1965096960:ℝ), ((12857851904:ℝ)/7), ((-21171273728:ℝ)/21), ((914358272:ℝ)/3), ((-268435456:ℝ)/7)] : List ℝ).getD e 0 * q^e := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  unfold centralNum13_13
  ring

theorem centralNum13_22_list (q : ℝ) :
    centralNum13_22 q = ∑ e ∈ Finset.range 15, ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (82125:ℝ), (-6663750:ℝ), (115666200:ℝ), (-750437000:ℝ), (2277262000:ℝ), (-3656824320:ℝ), (3359621120:ℝ), (-1817706496:ℝ), ((1625292800:ℝ)/3), (-67108864:ℝ)] : List ℝ).getD e 0 * q^e := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  unfold centralNum13_22
  ring

theorem centralNum13_23_list (q : ℝ) :
    centralNum13_23 q = ∑ e ∈ Finset.range 16, ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-7627725:ℝ)/2), (173988600:ℝ), (-2299614450:ℝ), (13088188200:ℝ), (-38221499200:ℝ), (63366115840:ℝ), ((-445610508288:ℝ)/7), ((841540698112:ℝ)/21), ((-326820167680:ℝ)/21), ((10133438464:ℝ)/3), ((-2147483648:ℝ)/7)] : List ℝ).getD e 0 * q^e := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  unfold centralNum13_23
  ring

theorem centralNum13_33_list (q : ℝ) :
    centralNum13_33 q = ∑ e ∈ Finset.range 17, ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-8120475:ℝ)/4), ((464861025:ℝ)/2), (-5906535975:ℝ), ((411904731750:ℝ)/7), ((-2024051769000:ℝ)/7), ((5554394637600:ℝ)/7), (-1314913862656:ℝ), ((9709155336192:ℝ)/7), ((-6724555112448:ℝ)/7), ((1313173667840:ℝ)/3), ((-6168244125696:ℝ)/49), ((3004329623552:ℝ)/147), ((-68719476736:ℝ)/49)] : List ℝ).getD e 0 * q^e := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  unfold centralNum13_33
  ring

theorem centralNum23_00_list (q : ℝ) :
    centralNum23_00 q = ∑ e ∈ Finset.range 11, ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (780:ℝ), (-6156:ℝ), (15288:ℝ), (-14400:ℝ)] : List ℝ).getD e 0 * q^e := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  unfold centralNum23_00
  ring

theorem centralNum23_01_list (q : ℝ) :
    centralNum23_01 q = ∑ e ∈ Finset.range 12, ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-7368:ℝ), (59208:ℝ), (-155734:ℝ), (205300:ℝ), (-60000:ℝ)] : List ℝ).getD e 0 * q^e := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  unfold centralNum23_01
  ring

theorem centralNum23_02_list (q : ℝ) :
    centralNum23_02 q = ∑ e ∈ Finset.range 13, ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (87660:ℝ), (-702180:ℝ), ((7421435:ℝ)/4), ((-10854125:ℝ)/4), ((2828125:ℝ)/2), (-187500:ℝ)] : List ℝ).getD e 0 * q^e := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  unfold centralNum23_02
  ring

theorem centralNum23_03_list (q : ℝ) :
    centralNum23_03 q = ∑ e ∈ Finset.range 14, ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-833220:ℝ), (6469740:ℝ), ((-68603955:ℝ)/4), ((104396875:ℝ)/4), ((-1001334375:ℝ)/56), ((125828125:ℝ)/28), ((-2343750:ℝ)/7)] : List ℝ).getD e 0 * q^e := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  unfold centralNum23_03
  ring

theorem centralNum23_11_list (q : ℝ) :
    centralNum23_11 q = ∑ e ∈ Finset.range 13, ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-4074:ℝ), (159906:ℝ), (-1104799:ℝ), (2801499:ℝ), (-3931375:ℝ), ((5896250:ℝ)/3), (-250000:ℝ)] : List ℝ).getD e 0 * q^e := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  unfold centralNum23_11
  ring

theorem centralNum23_12_list (q : ℝ) :
    centralNum23_12 q = ∑ e ∈ Finset.range 14, ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (132555:ℝ), (-3252375:ℝ), ((39743695:ℝ)/2), ((-197111615:ℝ)/4), ((281947375:ℝ)/4), ((-1100234375:ℝ)/24), ((131828125:ℝ)/12), (-781250:ℝ)] : List ℝ).getD e 0 * q^e := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  unfold centralNum23_12
  ring

theorem centralNum23_13_list (q : ℝ) :
    centralNum23_13 q = ∑ e ∈ Finset.range 15, ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2399070:ℝ), (45666930:ℝ), (-251781675:ℝ), ((2452738385:ℝ)/4), ((-14104310625:ℝ)/16), ((74345740625:ℝ)/112), ((-74899765625:ℝ)/336), ((5161328125:ℝ)/168), ((-9765625:ℝ)/7)] : List ℝ).getD e 0 * q^e := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  unfold centralNum23_13
  ring

theorem centralNum23_22_list (q : ℝ) :
    centralNum23_22 q = ∑ e ∈ Finset.range 15, ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((178425:ℝ)/2), ((-13176075:ℝ)/2), ((777815145:ℝ)/8), ((-3968389015:ℝ)/8), ((9393350195:ℝ)/8), ((-26366634375:ℝ)/16), ((77851609375:ℝ)/64), ((-25714921875:ℝ)/64), ((5236328125:ℝ)/96), ((-9765625:ℝ)/4)] : List ℝ).getD e 0 * q^e := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  unfold centralNum23_22
  ring

theorem centralNum23_23_list (q : ℝ) :
    centralNum23_23 q = ∑ e ∈ Finset.range 16, ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-15801525:ℝ)/4), ((655493865:ℝ)/4), ((-7334421225:ℝ)/4), ((16442962485:ℝ)/2), ((-598626108395:ℝ)/32), ((414013307125:ℝ)/16), ((-4611984703125:ℝ)/224), ((399923828125:ℝ)/48), ((-4353201171875:ℝ)/2688), ((189736328125:ℝ)/1344), ((-244140625:ℝ)/56)] : List ℝ).getD e 0 * q^e := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  unfold centralNum23_23
  ring

theorem centralNum23_33_list (q : ℝ) :
    centralNum23_33 q = ∑ e ∈ Finset.range 17, ([(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), ((-16872075:ℝ)/8), ((1833754545:ℝ)/8), ((-83998007145:ℝ)/16), ((4929124002765:ℝ)/112), ((-76723155584685:ℝ)/448), ((164888745653055:ℝ)/448), ((-63358359907625:ℝ)/128), ((364713160040625:ℝ)/896), ((-334937462578125:ℝ)/1792), ((245466998046875:ℝ)/5376), ((-72144521484375:ℝ)/12544), ((6518798828125:ℝ)/18816), ((-6103515625:ℝ)/784)] : List ℝ).getD e 0 * q^e := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]
  unfold centralNum23_33
  ring

/-- A positive semidefinite piece matrix bounds the native odd form below. -/
theorem nativeOddForm_ge_of_piece {x : ℝ} (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (X : Fin 4 → Fin 4 → ℝ) (y : Fin 4 → ℝ)
    (hW : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j *
      pieceW (thetaCuspSingleAtomReflectionScale 1 x) X i j) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let c := (centralBasis (1/q)).mulVec y
    ∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
        thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x ≥
      -(4*q^2*Real.exp (x-2*q)*(8*q*(2*q-3)^2)*∑ i : Fin 4, ∑ j : Fin 4, y i * y j * X i j) := by
  intro q c
  have h := nativeOddForm_ge_central hq y
  have hq0 : 0 < q := by linarith
  have hsplit : (∑ i : Fin 4, ∑ j : Fin 4, y i * y j * pieceW q X i j) =
      (∑ i : Fin 4, ∑ j : Fin 4, y i * y j * centralEntryMat q i j) -
        q^6*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*∑ k : Fin 4, tailWeight k * y k^2) +
        8*q^7*(2*q-3)^2*∑ i : Fin 4, ∑ j : Fin 4, y i * y j * X i j := by
    simp only [pieceW, Fin.sum_univ_four, Fin.isValue, if_true, if_false]
    simp
    ring
  rw [hsplit] at hW
  have hK : 0 ≤ 4*q^2*Real.exp (x-2*q) := by positivity
  have hq6 : 0 < q^6 := by positivity
  have key : -(8*q*(2*q-3)^2*∑ i : Fin 4, ∑ j : Fin 4, y i * y j * X i j) ≤
      (∑ i : Fin 4, ∑ j : Fin 4, y i * y j * centralEntryMat q i j)/q^6 -
        8000*(2*q-3)^2*Real.exp (-(529/50)*q)*∑ k : Fin 4, tailWeight k * y k^2 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hq6]
    nlinarith [hW]
  calc -(4*q^2*Real.exp (x-2*q)*(8*q*(2*q-3)^2)*∑ i : Fin 4, ∑ j : Fin 4, y i * y j * X i j)
      = 4*q^2*Real.exp (x-2*q)*(-(8*q*(2*q-3)^2*∑ i : Fin 4, ∑ j : Fin 4, y i * y j * X i j)) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left key hK).trans h


/-- Assembly of one entry from its component bounds. -/
theorem entry_assemble {W a1 a2 a3 a4 a5 a6 m1 m2 m5 A B t r1 r2 r3 r4 r5 r6 r7 R : ℝ}
    (hW : W = a1 + a2 + a3 + a4 + a5 + a6) (h1 : |a1 - m1| ≤ r1) (h2 : |a2 - m2| ≤ r2)
    (h3 : |a3| ≤ r3) (h4 : |a4| ≤ r4) (h5 : |a5 - m5| ≤ r5) (h6 : |a6| ≤ r6)
    (h7 : |m1 + m2 + m5 - (A + t*B)| ≤ r7) (hR : r1 + r2 + r3 + r4 + r5 + r6 + r7 ≤ R) :
    |W - (A + t*B)| ≤ R := by
  rw [hW]
  have e : a1 + a2 + a3 + a4 + a5 + a6 - (A + t*B) =
      (a1 - m1) + (a2 - m2) + a3 + a4 + (a5 - m5) + a6 + (m1 + m2 + m5 - (A + t*B)) := by ring
  rw [e]
  calc _ ≤ |a1 - m1| + |a2 - m2| + |a3| + |a4| + |a5 - m5| + |a6| + |m1 + m2 + m5 - (A + t*B)| := by
        refine (abs_add_le _ _).trans ?_
        refine add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add le_rfl le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl
    _ ≤ _ := by linarith

/-- The affine rounding step: `|α + tβ| ≤ |α| + ρ|β|` on `|t| ≤ ρ`. -/
theorem affine_round {α β t ρ : ℝ} (ht : |t| ≤ ρ) : |α + t*β| ≤ |α| + ρ*|β| := by
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)

/-- A scaled affine model of a polynomial factor. -/
theorem scaled_affine {D d0 d1 rD X t : ℝ} (h : |D - d0 - d1*t| ≤ rD) :
    |D*X - (d0 + d1*t)*X| ≤ |X| * rD := by
  rw [show D*X - (d0 + d1*t)*X = (D - d0 - d1*t)*X by ring, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

end
end RHTower.ThetaCuspOddFourPieces
