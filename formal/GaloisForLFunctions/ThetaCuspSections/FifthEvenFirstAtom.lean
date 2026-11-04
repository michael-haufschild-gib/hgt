import Mathlib.LinearAlgebra.Matrix.PosDef
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRadialCoefficients
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFirstAtomReflectionJets

/-!
# Positive fifth even sections of theta atoms

Every individual theta atom has a positive definite fifth even reflected-moment
matrix once its reflection scale reaches five. The radial recurrence gives its
nine moments exactly. Eliminating the leading two coordinates leaves a
three-by-three Schur matrix whose leading minors have positive coefficients
in `q - 5`. Two square completions transfer these signs to the full matrix.
-/

noncomputable section
open Matrix _root_.RHTower Polynomial
namespace GaloisForLFunctions.ThetaCuspSections.FifthFirstAtom
-- Exact signed radial moments through reflection order sixteen.
private def r0 (q : ℝ) : ℝ := 9 - q * 12 + q ^ 2 * 4
private def r1 (q : ℝ) : ℝ := q * 120 - q ^ 2 * 96 + q ^ 3 * 32
private def r2 (q : ℝ) : ℝ := -(q * 480) + q ^ 2 * 4416 - q ^ 3 * 2432 + q ^ 4 * 768
private def r3 (q : ℝ) : ℝ := q * 1920 - q ^ 2 * 82176 + q ^ 3 * 253952 - q ^ 4 * 107520 + q ^ 5 * 30720
private def r4 (q : ℝ) : ℝ := -(q * 7680) + q ^ 2 * 1360896 - q ^ 3 * 12388352 + q ^ 4 * 19611648 - q ^ 5 * 6881280 + q ^ 6 * 1720320
private def r5 (q : ℝ) : ℝ := q * 30720 - q ^ 2 * 21958656 + q ^ 3 * 500252672 - q ^ 4 * 1924055040 + q ^ 5 * 1899233280 - q ^ 6 * 578027520 +
      q ^ 7 * 123863040
private def r6 (q : ℝ) : ℝ := -(q * 122880) + q ^ 2 * 352075776 - q ^ 3 * 18886787072 + q ^ 4 * 150752329728 - q ^ 5 * 320229212160 +
          q ^ 6 * 221632266240 -
        q ^ 7 * 59949711360 +
      q ^ 8 * 10899947520
private def r7 (q : ℝ) : ℝ := q * 491520 - q ^ 2 * 5636161536 + q ^ 3 * 694004744192 - q ^ 4 * 10699371970560 + q ^ 5 * 42564900618240 -
            q ^ 6 * 57797577277440 +
          q ^ 7 * 30323654000640 -
        q ^ 8 * 7368364523520 +
      q ^ 9 * 1133594542080
private def r8 (q : ℝ) : ℝ := -(q * 1966080) + q ^ 2 * 90190381056 - q ^ 3 * 25209606766592 + q ^ 4 * 723521013547008 - q ^ 5 * 5015348591984640 +
              q ^ 6 * 11904065218805760 -
            q ^ 7 * 11342746988052480 +
          q ^ 8 * 4763364265820160 -
        q ^ 9 * 1042906978713600 +
      q ^ 10 * 136031345049600
-- Eliminate the leading two coordinates and remove the positive factor q³.
private def headDelta (q : ℝ) : ℝ := r0 q*r2 q-(r1 q)^2
private def s00 (q : ℝ) : ℝ := -(q ^ (3-3) * 3344302080) + q ^ (4-3) * 31531991040 - q ^ (5-3) * 167108935680 + q ^ (6-3) * 388066443264 - q ^ (7-3) * 472519802880 +
              q ^ (8-3) * 344381718528 -
            q ^ (9-3) * 160130138112 +
          q ^ (10-3) * 47563407360 -
        q ^ (11-3) * 8657043456 +
      q ^ (12-3) * 805306368
private def s01 (q : ℝ) : ℝ := q ^ (3-3) * 66886041600 - q ^ (4-3) * 1662595891200 + q ^ (5-3) * 12782665728000 - q ^ (6-3) * 46257112350720 +
                  q ^ (7-3) * 84502055485440 -
                q ^ (8-3) * 87473635983360 +
              q ^ (9-3) * 56469089157120 -
            q ^ (10-3) * 23799823073280 +
          q ^ (11-3) * 6508888719360 -
        q ^ (12-3) * 1103269724160 +
      q ^ (13-3) * 96636764160
private def s02 (q : ℝ) : ℝ := -(q ^ (3-3) * 1123685498880) + q ^ (4-3) * 68384288931840 - q ^ (5-3) * 820254741626880 + q ^ (6-3) * 4374282910040064 -
                    q ^ (7-3) * 11662452357857280 +
                  q ^ (8-3) * 17197824630325248 -
                q ^ (9-3) * 15283987270336512 +
              q ^ (10-3) * 8773229032243200 -
            q ^ (11-3) * 3352387330768896 +
          q ^ (12-3) * 842459982594048 -
        q ^ (13-3) * 132585640427520 +
      q ^ (14-3) * 10823317585920
private def s11 (q : ℝ) : ℝ := -(q ^ (3-3) * 1337720832000) + q ^ (4-3) * 74530160640000 - q ^ (5-3) * 955395971481600 + q ^ (6-3) * 5129713483776000 -
                    q ^ (7-3) * 13775019599462400 +
                  q ^ (8-3) * 20440940544000000 -
                q ^ (9-3) * 18236680112701440 +
              q ^ (10-3) * 10496129661665280 -
            q ^ (11-3) * 4022972385853440 +
          q ^ (12-3) * 1014573280788480 -
        q ^ (13-3) * 160223754977280 +
      q ^ (14-3) * 13142599925760
private def s12 (q : ℝ) : ℝ := q ^ (3-3) * 22473709977600 - q ^ (4-3) * 2870213817139200 + q ^ (5-3) * 59490407389593600 - q ^ (6-3) * 468389786151813120 +
                      q ^ (7-3) * 1791130618130595840 -
                    q ^ (8-3) * 3723439322494402560 +
                  q ^ (9-3) * 4573054955484610560 -
                q ^ (10-3) * 3543838627945512960 +
              q ^ (11-3) * 1823783806272798720 -
            q ^ (12-3) * 635539796986429440 +
          q ^ (13-3) * 147473113766952960 -
        q ^ (14-3) * 21624988536668160 +
      q ^ (15-3) * 1645144273059840
private def s22 (q : ℝ) : ℝ := -(q ^ (3-3) * 377558327623680) + q ^ (4-3) * 107118691237232640 - q ^ (5-3) * 3716780064956743680 + q ^ (6-3) * 42461901944745099264 -
                        q ^ (7-3) * 227223119599427911680 +
                      q ^ (8-3) * 649127801778673287168 -
                    q ^ (9-3) * 1081228297417525297152 +
                  q ^ (10-3) * 1121130609779429867520 -
                q ^ (11-3) * 762099666828159614976 +
              q ^ (12-3) * 352315897773092241408 -
            q ^ (13-3) * 111874096601833144320 +
          q ^ (14-3) * 23910440278111027200 -
        q ^ (15-3) * 3253922199030988800 +
      q ^ (16-3) * 228588467414630400
private def minor (q : ℝ) : ℝ := s00 q*s11 q-(s01 q)^2
private def determinant (q : ℝ) : ℝ := minor q*s22 q-(s11 q*(s02 q)^2-2*s01 q*s02 q*s12 q+s00 q*(s12 q)^2)
private def minorPolynomial (q : ℝ) : ℝ := -(q * 69023456654146928640000) + q ^ 2 * 1294573275913333506048000 - q ^ 3 * 11561903754086279282688000 +
                                      q ^ 4 * 68513535216346416021504000 -
                                    q ^ 5 * 291104734706306914870886400 +
                                  q ^ 6 * 876991499040024100129996800 -
                                q ^ 7 * 1891649055202896700558540800 +
                              q ^ 8 * 2999652806973620445039820800 -
                            q ^ 9 * 3593570695878730286534492160 +
                          q ^ 10 * 3325738993357106343491665920 -
                        q ^ 11 * 2417331745582601292616826880 +
                      q ^ 12 * 1395345393134443500184535040 -
                    q ^ 13 * 643395996823406523501772800 +
                  q ^ 14 * 237097703489688050230886400 -
                q ^ 15 * 69421459058662722188083200 +
              q ^ 16 * 15924071297268433048043520 -
            q ^ 17 * 2786248826936738363473920 +
          q ^ 18 * 354013194900816915333120 -
        q ^ 19 * 29572436593165624934400 +
      q ^ 20 * 1245155224975394734080
private def borderPolynomial (q : ℝ) : ℝ := q * 26060380861145281435565141734195200000 - q ^ 2 * 7882479262502222617834208171906826240000 +
                                                                  q ^ 3 * 377742214675936976275525748907583733760000 -
                                                                q ^ 4 * 8394530754994731375006069905458609520640000 +
                                                              q ^ 5 * 112970885907737262395304899539794263015424000 -
                                                            q ^ 6 * 1047321968358332643430321700822738987384832000 +
                                                          q ^ 7 * 7200591323173307761411796505892369610047488000 -
                                                        q ^ 8 * 38285349986800870355651634755795639514798489600 +
                                                      q ^ 9 * 160952004254195809002482544729446525184245760000 -
                                                    q ^ 10 * 541537388911290120304525170798657626553345638400 +
                                                  q ^ 11 * 1471287146708634528702070768497519858400257638400 -
                                                q ^ 12 * 3256369924172943088941057096208927609508321034240 +
                                              q ^ 13 * 5926405969946058182515288436074452410316179374080 -
                                            q ^ 14 * 8952976314054875153893166629633425534644492697600 +
                                          q ^ 15 * 11328204185803337513697414658832224695266354135040 -
                                        q ^ 16 * 12103244987478897192047694509376886207726831534080 +
                                      q ^ 17 * 10996513414621658010349521476148519873191702691840 -
                                    q ^ 18 * 8546314023518519743718339719687379990810072186880 +
                                  q ^ 19 * 5708306667575358017962418694217294354048792657920 -
                                q ^ 20 * 3288062672474552293818376062098929662786545909760 +
                              q ^ 21 * 1636921129527098150703644501333847953825448591360 -
                            q ^ 22 * 704924402684835276501728428097284938706767052800 +
                          q ^ 23 * 262437570891344143624318241537166247541310750720 -
                        q ^ 24 * 84275484101358050382016917705187951277097615360 +
                      q ^ 25 * 23245095321645485002284044666787071064664965120 -
                    q ^ 26 * 5470065447854021246594280380688874813721149440 +
                  q ^ 27 * 1087191863007506410972122307948293314586869760 -
                q ^ 28 * 179812515778755340273976883733620792471060480 +
              q ^ 29 * 24205089773383134519806917796596328473559040 -
            q ^ 30 * 2562322940596474838426533219058830226227200 +
          q ^ 31 * 201407928189173565606822626730428910796800 -
        q ^ 32 * 10535553156448434183567629056355598336000 +
      q ^ 33 * 277728048823282505698630909221981388800
private theorem minor_eq (q : ℝ) : minor q = minorPolynomial q := by
  simp only [minor, s00, s01, s11, minorPolynomial]
  norm_num only [Nat.reduceSub]
  ring
private theorem border_eq (q : ℝ) :
    s11 q*(s02 q)^2-2*s01 q*s02 q*s12 q+s00 q*(s12 q)^2 = borderPolynomial q := by
  simp only [s00, s01, s02, s11, s12, borderPolynomial]
  norm_num only [Nat.reduceSub]
  ring
-- Translation by five exposes positive coefficients in every required minor.
private theorem headDelta_shift (y : ℝ) : headDelta (5+y) =
    9076000 + y * 13106720 + y ^ 2 * 7954304 + y ^ 3 * 2603520 + y ^ 4 * 484864 + y ^ 5 * 48640 + y ^ 6 * 2048 := by
  simp only [headDelta, r0, r1, r2]
  ring
private theorem headDelta_pos {q : ℝ} (hq : 5 ≤ q) : 0 < headDelta q := by
  rw [show q = 5+(q-5) by ring, headDelta_shift]
  have hy : 0 ≤ q-5 := sub_nonneg.mpr hq
  positivity
private theorem s00_shift (y : ℝ) : s00 (5+y) =
    230417083269120 + y * 487709025239040 + y ^ 2 * 462849276641280 + y ^ 3 * 259139293937664 + y ^ 4 * 94521859768320 +
              y ^ 5 * 23329838727168 +
            y ^ 6 * 3900375564288 +
          y ^ 7 * 426057400320 +
        y ^ 8 * 27581743104 +
      y ^ 9 * 805306368 := by
  simp only [s00]
  norm_num only [Nat.reduceSub]
  ring
private theorem s00_pos {q : ℝ} (hq : 5 ≤ q) : 0 < s00 q := by
  rw [show q = 5+(q-5) by ring, s00_shift]
  have hy : 0 ≤ q-5 := sub_nonneg.mpr hq
  positivity
private theorem minor_shift (y : ℝ) : minor (5+y) =
    1514219860379890261312929792000000 + y * 7271283802457092109887592202240000 +
                                          y ^ 2 * 16593530311898991635229025763328000 +
                                        y ^ 3 * 23946232875397199474355226017792000 +
                                      y ^ 4 * 24525729189399663168632226054144000 +
                                    y ^ 5 * 18962626993693896342034896755097600 +
                                  y ^ 6 * 11490957476306361695538762271948800 +
                                y ^ 7 * 5591579482410592396292031460147200 +
                              y ^ 8 * 2220168023964289853473227905433600 +
                            y ^ 9 * 726726399274097400818974945443840 +
                          y ^ 10 * 197258685217402962682544935403520 +
                        y ^ 11 * 44493650064347927385401217515520 +
                      y ^ 12 * 8327770292930555756722299863040 +
                    y ^ 13 * 1286671760470312254633620275200 +
                  y ^ 14 * 162530505545652412483004006400 +
                y ^ 15 * 16529147116135375312414310400 +
              y ^ 16 * 1321717674784701232258744320 +
            y ^ 17 * 80087391837347487028346880 +
          y ^ 18 * 3459119037183207533445120 +
        y ^ 19 * 94943085904373848473600 +
      y ^ 20 * 1245155224975394734080 := by
  simp only [minor_eq, minorPolynomial]
  ring
private theorem minor_pos {q : ℝ} (hq : 5 ≤ q) : 0 < minor q := by
  rw [show q = 5+(q-5) by ring, minor_shift]
  have hy : 0 ≤ q-5 := sub_nonneg.mpr hq
  positivity
private theorem determinant_shift (y : ℝ) : determinant (5+y) =
    129823383134251507159847425628427538655084544000000000000 +
                                                                      y *
                                                                        1344007877077558065174954682796564604420001628160000000000 +
                                                                    y ^ 2 *
                                                                      6271076370233166896881651330307787697036704979353600000000 +
                                                                  y ^ 3 *
                                                                    18085212047731066284160544978646234471763172665589760000000 +
                                                                y ^ 4 *
                                                                  36774731278232207463816507653686151544202561000046592000000 +
                                                              y ^ 5 *
                                                                56672438033923644284731496352590531566776966374542540800000 +
                                                            y ^ 6 *
                                                              69252465348992059007906512500256687255666244267802624000000 +
                                                          y ^ 7 *
                                                            69195506849836232444763497685959950896531195451303526400000 +
                                                        y ^ 8 *
                                                          57789227431233813875756965232097422409404998326681600000000 +
                                                      y ^ 9 *
                                                        41003895953421823526488865591570755234052142771732480000000 +
                                                    y ^ 10 *
                                                      25026235129668891371558255266909137538371991921817026560000 +
                                                  y ^ 11 * 13265074900780410455664259189655255868346541251850403840000 +
                                                y ^ 12 * 6151615308983428272199932201395770250832739691397120000000 +
                                              y ^ 13 * 2510298000848973231951817136377439446027236792845991936000 +
                                            y ^ 14 * 905346518841654424845229361456564135285536697515769856000 +
                                          y ^ 15 * 289502507918801245675457100750812500202211374039826432000 +
                                        y ^ 16 * 82260551136623910976494115296632039883267918652243968000 +
                                      y ^ 17 * 20796226763470087866004083077496395968400232042568089600 +
                                    y ^ 18 * 4679516673435870788377698241578949941131011857108172800 +
                                  y ^ 19 * 936768841561155335031802063220953683513646068321484800 +
                                y ^ 20 * 166601657005404316609421488384889910829082275636838400 +
                              y ^ 21 * 26261587583326390540170783124068823859169894963609600 +
                            y ^ 22 * 3656490879365734497392092309885823460186519502848000 +
                          y ^ 23 * 447575365657837906705367217425871999081370563379200 +
                        y ^ 24 * 47864651136353366662742051489620591265621999616000 +
                      y ^ 25 * 4435668238535315817251598334768034844346259865600 +
                    y ^ 26 * 352407673127186429860409582490012496802768486400 +
                  y ^ 27 * 23665283673082971442641373225321362368338329600 +
                y ^ 28 * 1317717393903365194338004835954162460839116800 +
              y ^ 29 * 59225462019280792870290602955532844767641600 +
            y ^ 30 * 2065184261658359020622271078850146965913600 +
          y ^ 31 * 52434538112154699903530648646993523507200 +
        y ^ 32 * 862509468395287284778356860937830400000 +
      y ^ 33 * 6900075747162298278226854887502643200 := by
  simp only [determinant, minor_eq, border_eq, minorPolynomial, borderPolynomial, s22]
  norm_num only [Nat.reduceSub]
  ring
private theorem determinant_pos {q : ℝ} (hq : 5 ≤ q) : 0 < determinant q := by
  rw [show q = 5+(q-5) by ring, determinant_shift]
  have hy : 0 ≤ q-5 := sub_nonneg.mpr hq
  positivity
-- These identities retain the exact denominator-cleared Schur entries.
private theorem schur_00 (q : ℝ) :
    headDelta q*r4 q-(r2 q*r2 q*r2 q-r1 q*(r2 q*r3 q+r3 q*r2 q)+r0 q*r3 q*r3 q) = q^3*s00 q := by
  simp only [headDelta, s00, r0, r1, r2, r3, r4]
  norm_num only [Nat.reduceSub]
  ring
private theorem schur_01 (q : ℝ) :
    headDelta q*r5 q-(r2 q*r2 q*r3 q-r1 q*(r2 q*r4 q+r3 q*r3 q)+r0 q*r3 q*r4 q) = q^3*s01 q := by
  simp only [headDelta, s01, r0, r1, r2, r3, r4, r5]
  norm_num only [Nat.reduceSub]
  ring
private theorem schur_02 (q : ℝ) :
    headDelta q*r6 q-(r2 q*r2 q*r4 q-r1 q*(r2 q*r5 q+r3 q*r4 q)+r0 q*r3 q*r5 q) = q^3*s02 q := by
  simp only [headDelta, s02, r0, r1, r2, r3, r4, r5, r6]
  norm_num only [Nat.reduceSub]
  ring
private theorem schur_11 (q : ℝ) :
    headDelta q*r6 q-(r2 q*r3 q*r3 q-r1 q*(r3 q*r4 q+r4 q*r3 q)+r0 q*r4 q*r4 q) = q^3*s11 q := by
  simp only [headDelta, s11, r0, r1, r2, r3, r4, r6]
  norm_num only [Nat.reduceSub]
  ring
private theorem schur_12 (q : ℝ) :
    headDelta q*r7 q-(r2 q*r3 q*r4 q-r1 q*(r3 q*r5 q+r4 q*r4 q)+r0 q*r4 q*r5 q) = q^3*s12 q := by
  simp only [headDelta, s12, r0, r1, r2, r3, r4, r5, r7]
  norm_num only [Nat.reduceSub]
  ring
private theorem schur_22 (q : ℝ) :
    headDelta q*r8 q-(r2 q*r4 q*r4 q-r1 q*(r4 q*r5 q+r5 q*r4 q)+r0 q*r5 q*r5 q) = q^3*s22 q := by
  simp only [headDelta, s22, r0, r1, r2, r4, r5, r8]
  norm_num only [Nat.reduceSub]
  ring
private theorem r0_pos {q : ℝ} (hq : 5 ≤ q) : 0 < r0 q := by
  have he : r0 q = (2*q-3)^2 := by unfold r0; ring
  rw [he]
  exact sq_pos_of_pos (by linarith only [hq])
-- The first square completion signs the remaining three-coordinate form.
private def schurQuadratic (q u v w : ℝ) : ℝ :=
  s00 q*u^2+2*s01 q*u*v+2*s02 q*u*w+s11 q*v^2+2*s12 q*v*w+s22 q*w^2
private theorem schur_square_completion (q u v w : ℝ) :
    (s00 q*minor q)*schurQuadratic q u v w =
      minor q*(s00 q*u+s01 q*v+s02 q*w)^2+
      (minor q*v+(s00 q*s12 q-s01 q*s02 q)*w)^2+
      s00 q*determinant q*w^2 := by
  unfold schurQuadratic determinant minor
  ring
private theorem schurQuadratic_pos {q : ℝ} (hq : 5 ≤ q) (u v w : ℝ)
    (h : u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) : 0 < schurQuadratic q u v w := by
  have hs := s00_pos hq
  have hm := minor_pos hq
  have hd := determinant_pos hq
  have hc := mul_pos hs hm
  apply pos_of_mul_pos_right ?_ hc.le
  rw [schur_square_completion]
  by_cases hw : w = 0
  · subst w
    simp only [mul_zero, add_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    by_cases hv : v = 0
    · subst v
      simp only [mul_zero, add_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      have hu : u ≠ 0 := h.resolve_right (by simp)
      exact mul_pos hm (sq_pos_of_ne_zero (mul_ne_zero hs.ne' hu))
    · have hp : 0 < (minor q*v)^2 := sq_pos_of_ne_zero (mul_ne_zero hm.ne' hv)
      exact add_pos_of_nonneg_of_pos (mul_nonneg hm.le (sq_nonneg _)) hp
  · have hp : 0 < s00 q*determinant q*w^2 := mul_pos (mul_pos hs hd) (sq_pos_of_ne_zero hw)
    exact add_pos_of_nonneg_of_pos
      (add_nonneg (mul_nonneg hm.le (sq_nonneg _)) (sq_nonneg _)) hp
-- Restoring the eliminated coordinates gives the complete fifth radial form.
private def quadratic (q x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  r0 q*x0^2+2*r1 q*x0*x1+2*r2 q*x0*x2+2*r3 q*x0*x3+2*r4 q*x0*x4+
  r2 q*x1^2+2*r3 q*x1*x2+2*r4 q*x1*x3+2*r5 q*x1*x4+
  r4 q*x2^2+2*r5 q*x2*x3+2*r6 q*x2*x4+r6 q*x3^2+2*r7 q*x3*x4+r8 q*x4^2
private def firstCoordinate (q x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  r0 q*x0+r1 q*x1+r2 q*x2+r3 q*x3+r4 q*x4
private def secondCoordinate (q x1 x2 x3 x4 : ℝ) : ℝ :=
  headDelta q*x1+r0 q*(r3 q*x2+r4 q*x3+r5 q*x4)-r1 q*(r2 q*x2+r3 q*x3+r4 q*x4)
private theorem quadratic_square_completion (q x0 x1 x2 x3 x4 : ℝ) :
    (r0 q*headDelta q)*quadratic q x0 x1 x2 x3 x4 =
      headDelta q*(firstCoordinate q x0 x1 x2 x3 x4)^2+
      (secondCoordinate q x1 x2 x3 x4)^2+
      r0 q*q^3*schurQuadratic q x2 x3 x4 := by
  have h00 := schur_00 q
  have h01 := schur_01 q
  have h02 := schur_02 q
  have h11 := schur_11 q
  have h12 := schur_12 q
  have h22 := schur_22 q
  unfold quadratic firstCoordinate secondCoordinate schurQuadratic
  unfold headDelta at h00 h01 h02 h11 h12 h22 ⊢
  linear_combination r0 q*x2^2*h00+2*r0 q*x2*x3*h01+2*r0 q*x2*x4*h02+
    r0 q*x3^2*h11+2*r0 q*x3*x4*h12+r0 q*x4^2*h22
private theorem quadratic_pos {q : ℝ} (hq : 5 ≤ q) (x0 x1 x2 x3 x4 : ℝ)
    (h : x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0 ∨ x3 ≠ 0 ∨ x4 ≠ 0) :
    0 < quadratic q x0 x1 x2 x3 x4 := by
  have hr := r0_pos hq
  have hd := headDelta_pos hq
  have hq0 : 0 < q := by linarith only [hq]
  have hc := mul_pos hr hd
  apply pos_of_mul_pos_right ?_ hc.le
  rw [quadratic_square_completion]
  by_cases ht : x2 ≠ 0 ∨ x3 ≠ 0 ∨ x4 ≠ 0
  · have hs := schurQuadratic_pos hq x2 x3 x4 ht
    exact add_pos_of_nonneg_of_pos
      (add_nonneg (mul_nonneg hd.le (sq_nonneg _)) (sq_nonneg _))
      (mul_pos (mul_pos hr (pow_pos hq0 3)) hs)
  · push Not at ht
    rcases ht with ⟨h2,h3,h4⟩
    subst x2; subst x3; subst x4
    simp only [firstCoordinate, secondCoordinate, schurQuadratic, mul_zero,
      add_zero, sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    by_cases h1 : x1 = 0
    · subst x1
      simp only [mul_zero, add_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      have h0 : x0 ≠ 0 := h.resolve_right (by simp)
      exact mul_pos hd (sq_pos_of_ne_zero (mul_ne_zero hr.ne' h0))
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hd.le (sq_nonneg _))
        (sq_pos_of_ne_zero (mul_ne_zero hd.ne' h1))
private def moment (q : ℝ) : ℕ → ℝ
  | 0 => r0 q | 1 => r1 q | 2 => r2 q | 3 => r3 q | 4 => r4 q
  | 5 => r5 q | 6 => r6 q | 7 => r7 q | _ => r8 q
private def model (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => moment q (i.val+j.val)
private theorem model_energy (q : ℝ) (v : Fin 5 → ℝ) :
    v ⬝ᵥ (model q *ᵥ v) = quadratic q (v 0) (v 1) (v 2) (v 3) (v 4) := by
  norm_num [dotProduct, Matrix.mulVec, model, moment, Fin.sum_univ_succ, quadratic]
  simp only [show (Fin.succ (2 : Fin 4) : Fin 5) = 3 by rfl,
    show (Fin.succ (Fin.succ (2 : Fin 3)) : Fin 5) = 4 by rfl]
  ring
private theorem model_posDef {q : ℝ} (hq : 5 ≤ q) : (model q).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, model, add_comm]
  · intro v hv
    simp only [star_trivial]
    rw [model_energy]
    apply quadratic_pos hq
    by_contra h
    push Not at h
    rcases h with ⟨h0,h1,h2,h3,h4⟩
    apply hv
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4

-- Coefficient recurrence identifies the polynomial moments with literal radial jets.
private theorem radial_eight_coeff (a : ℝ) (k : ℕ) :
 radialCoeffs a 8 k = radialStepCoeff a (radialCoeffs a 7) k := rfl
private theorem radial_seven_zero_16 (a : ℝ) : radialCoeffs a 7 16=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_17 (a : ℝ) : radialCoeffs a 7 17=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_18 (a : ℝ) : radialCoeffs a 7 18=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_19 (a : ℝ) : radialCoeffs a 7 19=0 :=
 radialCoeffs_eq_zero a (by norm_num)



local macro "reduce_radial" : tactic =>
  `(tactic| norm_num only [eval_thetaPairRadialEvenPolynomial, Finset.sum_range_succ, radialCoeffs_0_0,
    radialCoeffs_0_1, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3,
    radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4,
    radialCoeffs_2_5, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3,
    radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7, radialCoeffs_4_0,
    radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5,
    radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9, radialCoeffs_5_0,
    radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5,
    radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10,
    radialCoeffs_5_11, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3,
    radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8,
    radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12,
    radialCoeffs_6_13, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3,
    radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8,
    radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12,
    radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15, radial_eight_coeff,
    radial_seven_zero_16, radial_seven_zero_17, radial_seven_zero_18, radial_seven_zero_19,
    radialStepCoeff, radialInnerCoeff, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow])
private theorem radialMoment_0 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (q^2) 0).eval (2*q) = r0 q := by
  unfold r0
  reduce_radial
  ring
private theorem radialMoment_1 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (q^2) 1).eval (2*q) = r1 q := by
  unfold r1
  reduce_radial
  ring
private theorem radialMoment_2 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (q^2) 2).eval (2*q) = r2 q := by
  unfold r2
  reduce_radial
  ring
private theorem radialMoment_3 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (q^2) 3).eval (2*q) = r3 q := by
  unfold r3
  reduce_radial
  ring
private theorem radialMoment_4 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (q^2) 4).eval (2*q) = r4 q := by
  unfold r4
  reduce_radial
  ring
private theorem radialMoment_5 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (q^2) 5).eval (2*q) = r5 q := by
  unfold r5
  reduce_radial
  ring
private theorem radialMoment_6 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (q^2) 6).eval (2*q) = r6 q := by
  unfold r6
  reduce_radial
  ring
private theorem radialMoment_7 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (q^2) 7).eval (2*q) = r7 q := by
  unfold r7
  reduce_radial
  ring
private theorem radialMoment_8 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (q^2) 8).eval (2*q) = r8 q := by
  unfold r8
  reduce_radial
  ring

private theorem radialMatrix_eq_model (q : ℝ) :
    (fun i j : Fin 5 => (thetaPairRadialEvenPolynomial (q^2) (i.val+j.val)).eval (2*q)) =
      model q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [model, moment, radialMoment_0, radialMoment_1, radialMoment_2,
      radialMoment_3, radialMoment_4, radialMoment_5, radialMoment_6,
      radialMoment_7, radialMoment_8]
/-- The fifth even first-atom radial matrix is strictly positive from scale five onward. -/
theorem radial_even_five_posDef {q : ℝ} (hq : 5 ≤ q) :
    Matrix.PosDef (fun i j : Fin 5 => (thetaPairRadialEvenPolynomial (q^2) (i.val+j.val)).eval (2*q)) := by
  rw [radialMatrix_eq_model]
  exact model_posDef hq
private theorem atom_signed_radial (n k : ℕ) (x : ℝ) :
    (-1 : ℝ)^k*iteratedDeriv (2*k)
      (fun t => thetaCuspSourceTerm (x+t) n*thetaCuspSourceTerm (x-t) n) 0 =
      4*(thetaCuspSingleAtomReflectionScale n x)^2*
        Real.exp (x-2*thetaCuspSingleAtomReflectionScale n x)*
        (thetaPairRadialEvenPolynomial ((thetaCuspSingleAtomReflectionScale n x)^2) k).eval
          (2*thetaCuspSingleAtomReflectionScale n x) := by
  rw [thetaCuspAtomPairEvenJet_eq_radial]
  let q := thetaCuspSingleAtomReflectionScale n x
  change (-1 : ℝ)^k*((-1 : ℝ)^k*4*(q*q)*Real.exp (x-q-q)*
    (thetaPairRadialEvenPolynomial (q*q) k).eval (q+q)) = _
  rw [show q*q=q^2 by ring, show q+q=2*q by ring,
    show x-q-q=x-2*q by ring]
  have hp : (-1 : ℝ)^k*(-1 : ℝ)^k = 1 := by rw [← mul_pow]; norm_num
  calc
    _ = ((-1 : ℝ)^k*(-1 : ℝ)^k)*
        (4*q^2*Real.exp (x-2*q)*(thetaPairRadialEvenPolynomial (q^2) k).eval (2*q)) := by ring
    _ = _ := by rw [hp, one_mul]
/-- Every individual theta atom has a positive definite fifth even section
whenever its reflection scale is at least five. -/
theorem atom_even_five_posDef {n : ℕ} {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale n x) :
    Matrix.PosDef (fun i j : Fin 5 => (-1 : ℝ)^(i.val+j.val)*
      iteratedDeriv (2*(i.val+j.val))
        (fun t => thetaCuspSourceTerm (x+t) n*thetaCuspSourceTerm (x-t) n) 0) := by
  have hp : 0 < thetaCuspSingleAtomReflectionScale n x := by linarith only [hq]
  have hc : 0 < 4*(thetaCuspSingleAtomReflectionScale n x)^2*
      Real.exp (x-2*thetaCuspSingleAtomReflectionScale n x) := by positivity
  have he : (fun i j : Fin 5 => (-1 : ℝ)^(i.val+j.val)*
      iteratedDeriv (2*(i.val+j.val))
        (fun t => thetaCuspSourceTerm (x+t) n*thetaCuspSourceTerm (x-t) n) 0) =
      (4*(thetaCuspSingleAtomReflectionScale n x)^2*
        Real.exp (x-2*thetaCuspSingleAtomReflectionScale n x)) •
      (fun i j : Fin 5 =>
        (thetaPairRadialEvenPolynomial ((thetaCuspSingleAtomReflectionScale n x)^2)
          (i.val+j.val)).eval (2*thetaCuspSingleAtomReflectionScale n x)) := by
    ext i j
    exact atom_signed_radial n (i.val+j.val) x
  rw [he]
  exact (radial_even_five_posDef hq).smul hc

/-- The fifth even section of the first theta atom is strict on the scale-five ray. -/
theorem firstAtom_even_five_posDef {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    Matrix.PosDef (fun i j : Fin 5 => (-1 : ℝ)^(i.val+j.val)*
      thetaCuspFirstAtomReflectionJet (2*(i.val+j.val)) x) := by
  exact atom_even_five_posDef hq

end GaloisForLFunctions.ThetaCuspSections.FifthFirstAtom
