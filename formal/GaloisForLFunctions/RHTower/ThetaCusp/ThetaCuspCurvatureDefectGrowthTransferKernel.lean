import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectBinaryGrowthKernel
/-!
# Stable spectral kernel for curvature-defect growth comparison

The exact dominant-component anchor gives a positive transfer polynomial
for q >= 3/2 and spectral parameter t >= 8. The corresponding t >= 6
claim fails at q = 3/2, t = 6; the dominant self-pair has a separate
coupled moment proof. The stable-domain certificate is split into short
positive blocks and uses the default Lean resource limits.

Complete-source cumulant growth still requires the signed sector comparison.
-/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
noncomputable section

private def transferAnchor (q : ℝ) : ℝ :=
  q ^ 2 * 98415 +
      (q ^ 3 * 393660 +
        (q ^ 4 * (1541835/2) +
          (q ^ 5 * 987795 +
            (q ^ 6 * (7468605/8) +
              (q ^ 7 * 695466 +
                (q ^ 8 * (14811093/32) +
                  (q ^ 9 * (3340035/16) +
                    (q ^ 10 * (-2113371/32) +
                      (q ^ 11 * (-897885/8) +
                        (q ^ 12 * (-130977/2) +
                          (q ^ 13 * (-19683/2) +
                            (q ^ 14 * (54675/2) +
                              (q ^ 15 * 8748 + 0)))))))))))))

private def transferAnchorSlope (q : ℝ) : ℝ :=
  q ^ 2 * (-590490) +
      (q ^ 3 * (-2263545) +
        (q ^ 4 * (-4264650) +
          (q ^ 5 * (-10552275/2) +
            (q ^ 6 * (-19322145/4) +
              (q ^ 7 * (-27969543/8) +
                (q ^ 8 * (-2086398) +
                  (q ^ 9 * (-37753209/32) +
                    (q ^ 10 * (-3033369/4) +
                      (q ^ 11 * (-4434507/32) +
                        (q ^ 12 * (598023/8) +
                          (q ^ 13 * 147258 +
                            (q ^ 14 * (387099/2) +
                              (q ^ 15 * (-41553/2) +
                                (q ^ 16 * (-26244) + 0))))))))))))))

private theorem growthNumerator_three_eq (q : ℝ) : growthNumerator q 3=transferAnchor q := by
  unfold growthNumerator transferAnchor
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [growthCoefficient,growthCoefficientJet,coolingCoefficient,coolingCoefficientJet,
    coolingCoefficientJetTwo]
  unfold polynomialMoment
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

private theorem slopeNumerator_three_eq (q : ℝ) : slopeNumerator q 3=transferAnchorSlope q := by
  unfold slopeNumerator transferAnchorSlope
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [growthCoefficient,growthCoefficientJet,coolingCoefficient,coolingCoefficientJet,
    coolingCoefficientJetTwo]
  unfold polynomialMoment
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

def growthScore (q t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 6, growthCoefficient q (j+2)*t^(j+2)
def growthScoreJet (q t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 6, growthCoefficientJet q (j+2)*t^(j+2)
def growthTransferKernel (q t : ℝ) : ℝ :=
  growthScore q t*slopeNumerator q 3+
    q*t*growthScore q t*growthNumerator q 3-
    q*growthScoreJet q t*growthNumerator q 3
theorem growthTransferKernel_threeHalves_six_neg :
    growthTransferKernel (3/2) 6 < 0 := by
  unfold growthTransferKernel
  rw [growthNumerator_three_eq,slopeNumerator_three_eq]
  norm_num [growthScore,growthScoreJet,growthCoefficient,growthCoefficientJet,
    coolingCoefficient,coolingCoefficientJet,coolingCoefficientJetTwo,
    transferAnchor,transferAnchorSlope,Finset.sum_range_succ]

private def growthTransferBlock00 (y v tail : ℝ) : ℝ :=
  NNRat.rawCast 188427766132485 16 + (
    y ^ Nat.rawCast 1 * NNRat.rawCast 6771279857442792201 32 + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 1 * NNRat.rawCast 35689412777501337651 64) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 2 * NNRat.rawCast 910979890991023697613 2048) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 3 * NNRat.rawCast 1435561397477309260125 8192) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 4 * NNRat.rawCast 325820918259783763425 8192) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 5 * NNRat.rawCast 179479148314290187563 32768) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 6 * NNRat.rawCast 14867299062505327329 32768) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 7 * NNRat.rawCast 683461768906047321 32768) + (
    y ^ Nat.rawCast 1 * (v ^ Nat.rawCast 8 * NNRat.rawCast 13429472157905535 32768) + (
    y ^ Nat.rawCast 2 * NNRat.rawCast 61141119936477201441 32 + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 1 * NNRat.rawCast 213952602414326734053 64) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 2 * NNRat.rawCast 4606819200218811402693 2048) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 3 * NNRat.rawCast 6580542485907576406521 8192) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 4 * NNRat.rawCast 349637802883891636905 2048) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 5 * NNRat.rawCast 734465869490915727093 32768) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 6 * NNRat.rawCast 29328958217801945691 16384) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 7 * NNRat.rawCast 2619801619289704611 32768) + (
    y ^ Nat.rawCast 2 * (v ^ Nat.rawCast 8 * NNRat.rawCast 25144977088871109 16384) + (
    y ^ Nat.rawCast 3 * NNRat.rawCast 279405152765012736081 32 + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 1 * NNRat.rawCast 811775310724640493783 64) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 2 * NNRat.rawCast 15588884783607554297349 2048) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 3 * NNRat.rawCast 20553381517914927014589 8192) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 4 * NNRat.rawCast 1028006257093312944735 2048) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 5 * NNRat.rawCast 1029336007100635364769 16384) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 6 * NNRat.rawCast 158118152280158927907 32768) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 7 * NNRat.rawCast 3417629019612724269 16384) + (
    y ^ Nat.rawCast 3 * (v ^ Nat.rawCast 8 * NNRat.rawCast 127626942348481257 32768) + (
    y ^ Nat.rawCast 4 * NNRat.rawCast 868092896237693376051 32 + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 1 * NNRat.rawCast 2284450984223292437001 64) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 2 * NNRat.rawCast 40760348529631563554895 2048) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 3 * NNRat.rawCast 50708786352483810050271 8192) + (
    tail))))))))))))))))))))))))))))))))
private theorem growthTransferBlock00_pos (y v tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (ht : 0 ≤ tail) :
    0 < growthTransferBlock00 y v tail := by
  unfold growthTransferBlock00
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,Mathlib.Tactic.RingNF.nat_rawCast_1,
    Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity

private def growthTransferBlock01 (y v tail : ℝ) : ℝ :=
  y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 4 * NNRat.rawCast 4835675638309624407585 4096) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 5 * NNRat.rawCast 2324811454354327226499 16384) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 6 * NNRat.rawCast 21550748670083187279 2048) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 7 * NNRat.rawCast 903343470383398635 2048) + (
    y ^ Nat.rawCast 4 * (v ^ Nat.rawCast 8 * NNRat.rawCast 131290898242888359 16384) + (
    y ^ Nat.rawCast 5 * NNRat.rawCast 128094394016382633243 2 + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 1 * NNRat.rawCast 1279680954065872257159 16) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 2 * NNRat.rawCast 1368527420103269761413 32) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 3 * NNRat.rawCast 13153806148567323744621 1024) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 4 * NNRat.rawCast 19479649976453573548515 8192) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 5 * NNRat.rawCast 9123604289515758577959 32768) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 6 * NNRat.rawCast 661050012331585896219 32768) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 7 * NNRat.rawCast 27134299817517986109 32768) + (
    y ^ Nat.rawCast 5 * (v ^ Nat.rawCast 8 * NNRat.rawCast 483624814568950989 32768) + (
    y ^ Nat.rawCast 6 * Nat.rawCast 120430560595379287734 + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 1 * NNRat.rawCast 4685675230194991059213 32) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 2 * NNRat.rawCast 9810485101595371247649 128) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 3 * NNRat.rawCast 46329519835434073958721 2048) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 4 * NNRat.rawCast 8451367865425522080495 2048) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 5 * NNRat.rawCast 15636447778442581389249 32768) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 6 * NNRat.rawCast 560364362308170068247 16384) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 7 * NNRat.rawCast 45567617568018685983 32768) + (
    y ^ Nat.rawCast 6 * (v ^ Nat.rawCast 8 * NNRat.rawCast 402671318386927131 16384) + (
    y ^ Nat.rawCast 7 * NNRat.rawCast 367894655461548197091 2 + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 1 * Nat.rawCast 220527346581872927010) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 2 * NNRat.rawCast 14617469168190168280227 128) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 3 * NNRat.rawCast 17115901447861788930909 512) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 4 * NNRat.rawCast 12409917523361437717755 2048) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 5 * NNRat.rawCast 5712097284434538046557 8192) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 6 * NNRat.rawCast 1631527702635365060805 32768) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 7 * NNRat.rawCast 16537357399866231321 8192) + (
    y ^ Nat.rawCast 7 * (v ^ Nat.rawCast 8 * NNRat.rawCast 1166668501931690607 32768) + (
    tail))))))))))))))))))))))))))))))))
private theorem growthTransferBlock01_nonneg (y v tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (ht : 0 ≤ tail) :
    0 ≤ growthTransferBlock01 y v tail := by
  unfold growthTransferBlock01
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,Mathlib.Tactic.RingNF.nat_rawCast_1,
    Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity

private def growthTransferBlock02 (y v tail : ℝ) : ℝ :=
  y ^ Nat.rawCast 8 * NNRat.rawCast 460748075352045352641 2 + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 1 * NNRat.rawCast 547603862719010650767 2) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 2 * NNRat.rawCast 18033191024278652968293 128) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 3 * NNRat.rawCast 21017368053245204850159 512) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 4 * NNRat.rawCast 7594108759224837175725 1024) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 5 * NNRat.rawCast 6975085107968477280207 8192) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 6 * NNRat.rawCast 497356553112641828739 8192) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 7 * NNRat.rawCast 80599300047977536431 32768) + (
    y ^ Nat.rawCast 8 * (v ^ Nat.rawCast 8 * NNRat.rawCast 1421220415520473677 32768) + (
    y ^ Nat.rawCast 9 * Nat.rawCast 237989094878203819668 + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 1 * Nat.rawCast 280958361746965771023) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 2 * NNRat.rawCast 2301300779273124620139 16) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 3 * NNRat.rawCast 1335913676633229526305 32) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 4 * NNRat.rawCast 3850559954678013857055 512) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 5 * NNRat.rawCast 1764675556414690588713 2048) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 6 * NNRat.rawCast 502593746004215005527 8192) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 7 * NNRat.rawCast 20343205699817311251 8192) + (
    y ^ Nat.rawCast 9 * (v ^ Nat.rawCast 8 * NNRat.rawCast 358536894709954275 8192) + (
    y ^ Nat.rawCast 10 * Nat.rawCast 203755208278918211748 + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 1 * NNRat.rawCast 478107057237504176871 2) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 2 * NNRat.rawCast 1948241715777517908699 16) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 3 * NNRat.rawCast 4505386661079771116745 128) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 4 * NNRat.rawCast 404464321292960016405 64) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 5 * NNRat.rawCast 1478876308937837715033 2048) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 6 * NNRat.rawCast 820835785723611141 16) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 7 * NNRat.rawCast 16980712770387031101 8192) + (
    y ^ Nat.rawCast 10 * (v ^ Nat.rawCast 8 * NNRat.rawCast 298850653349369505 8192) + (
    y ^ Nat.rawCast 11 * Nat.rawCast 145099014635000641464 + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 1 * Nat.rawCast 169179404034594166776) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 2 * NNRat.rawCast 685722399936608766663 8) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 3 * NNRat.rawCast 789235161513639921765 32) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 4 * NNRat.rawCast 564553354751604044775 128) + (
    tail))))))))))))))))))))))))))))))))
private theorem growthTransferBlock02_nonneg (y v tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (ht : 0 ≤ tail) :
    0 ≤ growthTransferBlock02 y v tail := by
  unfold growthTransferBlock02
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,Mathlib.Tactic.RingNF.nat_rawCast_1,
    Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity

private def growthTransferBlock03 (y v tail : ℝ) : ℝ :=
  y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 5 * NNRat.rawCast 257126413479276483261 512) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 6 * NNRat.rawCast 72846346885338528981 2048) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 7 * NNRat.rawCast 366922679423786037 256) + (
    y ^ Nat.rawCast 11 * (v ^ Nat.rawCast 8 * NNRat.rawCast 51538195984595985 2048) + (
    y ^ Nat.rawCast 12 * Nat.rawCast 86138979037529273064 + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 1 * Nat.rawCast 99796409753021892972) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 2 * NNRat.rawCast 402200879558326329033 8) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 3 * NNRat.rawCast 460550746348728820317 32) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 4 * NNRat.rawCast 163959090811050932775 64) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 5 * NNRat.rawCast 148723967333424572991 512) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 6 * NNRat.rawCast 10493418134510589573 512) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 7 * NNRat.rawCast 1685430748420635591 2048) + (
    y ^ Nat.rawCast 12 * (v ^ Nat.rawCast 8 * NNRat.rawCast 29497107305287881 2048) + (
    y ^ Nat.rawCast 13 * Nat.rawCast 42651307733232363264 + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 1 * Nat.rawCast 49092432192266594832) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 2 * Nat.rawCast 24583621062486889170) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 3 * NNRat.rawCast 27994412675712617181 4) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 4 * NNRat.rawCast 39660223457989280025 32) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 5 * NNRat.rawCast 17901612547763802759 128) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 6 * NNRat.rawCast 5029786720793564343 512) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 7 * NNRat.rawCast 201127492807212105 512) + (
    y ^ Nat.rawCast 13 * (v ^ Nat.rawCast 8 * NNRat.rawCast 3506251324276611 512) + (
    y ^ Nat.rawCast 14 * Nat.rawCast 17586023005540554624 + (
    y ^ Nat.rawCast 14 * (v ^ Nat.rawCast 1 * Nat.rawCast 20107895929984120536) + (
    y ^ Nat.rawCast 14 * (v ^ Nat.rawCast 2 * Nat.rawCast 10006600297733016444) + (
    y ^ Nat.rawCast 14 * (v ^ Nat.rawCast 3 * NNRat.rawCast 22656182869105571403 8) + (
    y ^ Nat.rawCast 14 * (v ^ Nat.rawCast 4 * NNRat.rawCast 3989952658574451855 8) + (
    y ^ Nat.rawCast 14 * (v ^ Nat.rawCast 5 * NNRat.rawCast 7166096773676565579 128) + (
    y ^ Nat.rawCast 14 * (v ^ Nat.rawCast 6 * NNRat.rawCast 250431243785038413 64) + (
    y ^ Nat.rawCast 14 * (v ^ Nat.rawCast 7 * NNRat.rawCast 79735224571488981 512) + (
    y ^ Nat.rawCast 14 * (v ^ Nat.rawCast 8 * NNRat.rawCast 1383805760942349 512) + (
    y ^ Nat.rawCast 15 * Nat.rawCast 6013386462767078016 + (
    tail))))))))))))))))))))))))))))))))
private theorem growthTransferBlock03_nonneg (y v tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (ht : 0 ≤ tail) :
    0 ≤ growthTransferBlock03 y v tail := by
  unfold growthTransferBlock03
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,Mathlib.Tactic.RingNF.nat_rawCast_1,
    Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity

private def growthTransferBlock04 (y v tail : ℝ) : ℝ :=
  y ^ Nat.rawCast 15 * (v ^ Nat.rawCast 1 * Nat.rawCast 6829672378821198336) + (
    y ^ Nat.rawCast 15 * (v ^ Nat.rawCast 2 * Nat.rawCast 3376982977485633162) + (
    y ^ Nat.rawCast 15 * (v ^ Nat.rawCast 3 * NNRat.rawCast 1899760378071117771 2) + (
    y ^ Nat.rawCast 15 * (v ^ Nat.rawCast 4 * NNRat.rawCast 1330404689770984305 8) + (
    y ^ Nat.rawCast 15 * (v ^ Nat.rawCast 5 * NNRat.rawCast 594005698740065679 32) + (
    y ^ Nat.rawCast 15 * (v ^ Nat.rawCast 6 * NNRat.rawCast 165173509448053191 128) + (
    y ^ Nat.rawCast 15 * (v ^ Nat.rawCast 7 * NNRat.rawCast 3269885581430721 64) + (
    y ^ Nat.rawCast 15 * (v ^ Nat.rawCast 8 * NNRat.rawCast 112935154149783 128) + (
    y ^ Nat.rawCast 16 * Nat.rawCast 1693009960544138112 + (
    y ^ Nat.rawCast 16 * (v ^ Nat.rawCast 1 * Nat.rawCast 1909844459391446784) + (
    y ^ Nat.rawCast 16 * (v ^ Nat.rawCast 2 * Nat.rawCast 938155018943449062) + (
    y ^ Nat.rawCast 16 * (v ^ Nat.rawCast 3 * NNRat.rawCast 524423451358484973 2) + (
    y ^ Nat.rawCast 16 * (v ^ Nat.rawCast 4 * NNRat.rawCast 182500206233687595 4) + (
    y ^ Nat.rawCast 16 * (v ^ Nat.rawCast 5 * NNRat.rawCast 161999362635369093 32) + (
    y ^ Nat.rawCast 16 * (v ^ Nat.rawCast 6 * NNRat.rawCast 11196970515593901 32) + (
    y ^ Nat.rawCast 16 * (v ^ Nat.rawCast 7 * NNRat.rawCast 1763444039225877 128) + (
    y ^ Nat.rawCast 16 * (v ^ Nat.rawCast 8 * NNRat.rawCast 30289069215639 128) + (
    y ^ Nat.rawCast 17 * Nat.rawCast 388091059368975360 + (
    y ^ Nat.rawCast 17 * (v ^ Nat.rawCast 1 * Nat.rawCast 434822930731544832) + (
    y ^ Nat.rawCast 17 * (v ^ Nat.rawCast 2 * Nat.rawCast 212171546529815184) + (
    y ^ Nat.rawCast 17 * (v ^ Nat.rawCast 3 * Nat.rawCast 58914954817060680) + (
    y ^ Nat.rawCast 17 * (v ^ Nat.rawCast 4 * NNRat.rawCast 20371986710124165 2) + (
    y ^ Nat.rawCast 17 * (v ^ Nat.rawCast 5 * NNRat.rawCast 8985597048951435 8) + (
    y ^ Nat.rawCast 17 * (v ^ Nat.rawCast 6 * NNRat.rawCast 2469193180895853 32) + (
    y ^ Nat.rawCast 17 * (v ^ Nat.rawCast 7 * NNRat.rawCast 96646019857461 32) + (
    y ^ Nat.rawCast 17 * (v ^ Nat.rawCast 8 * NNRat.rawCast 1650447892305 32) + (
    y ^ Nat.rawCast 18 * Nat.rawCast 71238579632225280 + (
    y ^ Nat.rawCast 18 * (v ^ Nat.rawCast 1 * Nat.rawCast 79272102886429824) + (
    y ^ Nat.rawCast 18 * (v ^ Nat.rawCast 2 * Nat.rawCast 38419463543404752) + (
    y ^ Nat.rawCast 18 * (v ^ Nat.rawCast 3 * Nat.rawCast 10597039735477518) + (
    y ^ Nat.rawCast 18 * (v ^ Nat.rawCast 4 * Nat.rawCast 1820127741951600) + (
    y ^ Nat.rawCast 18 * (v ^ Nat.rawCast 5 * NNRat.rawCast 1595267219546235 8) + (
    tail))))))))))))))))))))))))))))))))
private theorem growthTransferBlock04_nonneg (y v tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (ht : 0 ≤ tail) :
    0 ≤ growthTransferBlock04 y v tail := by
  unfold growthTransferBlock04
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,Mathlib.Tactic.RingNF.nat_rawCast_1,
    Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity

private def growthTransferBlock05 (y v tail : ℝ) : ℝ :=
  y ^ Nat.rawCast 18 * (v ^ Nat.rawCast 6 * NNRat.rawCast 27224546102721 2) + (
    y ^ Nat.rawCast 18 * (v ^ Nat.rawCast 7 * NNRat.rawCast 16943418841023 32) + (
    y ^ Nat.rawCast 18 * (v ^ Nat.rawCast 8 * NNRat.rawCast 287583183027 32) + (
    y ^ Nat.rawCast 19 * Nat.rawCast 10215717098618880 + (
    y ^ Nat.rawCast 19 * (v ^ Nat.rawCast 1 * Nat.rawCast 11289847675087872) + (
    y ^ Nat.rawCast 19 * (v ^ Nat.rawCast 2 * Nat.rawCast 5434236170370432) + (
    y ^ Nat.rawCast 19 * (v ^ Nat.rawCast 3 * Nat.rawCast 1488703763591856) + (
    y ^ Nat.rawCast 19 * (v ^ Nat.rawCast 4 * Nat.rawCast 253972946887290) + (
    y ^ Nat.rawCast 19 * (v ^ Nat.rawCast 5 * NNRat.rawCast 55277990796015 2) + (
    y ^ Nat.rawCast 19 * (v ^ Nat.rawCast 6 * NNRat.rawCast 14994370654047 8) + (
    y ^ Nat.rawCast 19 * (v ^ Nat.rawCast 7 * NNRat.rawCast 144862513533 2) + (
    y ^ Nat.rawCast 19 * (v ^ Nat.rawCast 8 * NNRat.rawCast 9772064451 8) + (
    y ^ Nat.rawCast 20 * Nat.rawCast 1101940412792832 + (
    y ^ Nat.rawCast 20 * (v ^ Nat.rawCast 1 * Nat.rawCast 1209430141028352) + (
    y ^ Nat.rawCast 20 * (v ^ Nat.rawCast 2 * Nat.rawCast 578120601715200) + (
    y ^ Nat.rawCast 20 * (v ^ Nat.rawCast 3 * Nat.rawCast 157279819825728) + (
    y ^ Nat.rawCast 20 * (v ^ Nat.rawCast 4 * Nat.rawCast 26646778307700) + (
    y ^ Nat.rawCast 20 * (v ^ Nat.rawCast 5 * NNRat.rawCast 5759932379733 2) + (
    y ^ Nat.rawCast 20 * (v ^ Nat.rawCast 6 * NNRat.rawCast 387937962603 2) + (
    y ^ Nat.rawCast 20 * (v ^ Nat.rawCast 7 * NNRat.rawCast 59561296245 8) + (
    y ^ Nat.rawCast 20 * (v ^ Nat.rawCast 8 * NNRat.rawCast 997738803 8) + (
    y ^ Nat.rawCast 21 * Nat.rawCast 84035049357312 + (
    y ^ Nat.rawCast 21 * (v ^ Nat.rawCast 1 * Nat.rawCast 91596456640512) + (
    y ^ Nat.rawCast 21 * (v ^ Nat.rawCast 2 * Nat.rawCast 43478687582208) + (
    y ^ Nat.rawCast 21 * (v ^ Nat.rawCast 3 * Nat.rawCast 11745488623104) + (
    y ^ Nat.rawCast 21 * (v ^ Nat.rawCast 4 * Nat.rawCast 1975943652480) + (
    y ^ Nat.rawCast 21 * (v ^ Nat.rawCast 5 * Nat.rawCast 212055482844) + (
    y ^ Nat.rawCast 21 * (v ^ Nat.rawCast 6 * NNRat.rawCast 28363769433 2) + (
    y ^ Nat.rawCast 21 * (v ^ Nat.rawCast 7 * NNRat.rawCast 1081080027 2) + (
    y ^ Nat.rawCast 21 * (v ^ Nat.rawCast 8 * NNRat.rawCast 17983701 2) + (
    y ^ Nat.rawCast 22 * Nat.rawCast 4036094853120 + (
    y ^ Nat.rawCast 22 * (v ^ Nat.rawCast 1 * Nat.rawCast 4368900685824) + (
    tail))))))))))))))))))))))))))))))))
private theorem growthTransferBlock05_nonneg (y v tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (ht : 0 ≤ tail) :
    0 ≤ growthTransferBlock05 y v tail := by
  unfold growthTransferBlock05
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,Mathlib.Tactic.RingNF.nat_rawCast_1,
    Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity

private def growthTransferBlock06 (y v tail : ℝ) : ℝ :=
  y ^ Nat.rawCast 22 * (v ^ Nat.rawCast 2 * Nat.rawCast 2059254005760) + (
    y ^ Nat.rawCast 22 * (v ^ Nat.rawCast 3 * Nat.rawCast 552342841344) + (
    y ^ Nat.rawCast 22 * (v ^ Nat.rawCast 4 * Nat.rawCast 92255708160) + (
    y ^ Nat.rawCast 22 * (v ^ Nat.rawCast 5 * Nat.rawCast 9829602720) + (
    y ^ Nat.rawCast 22 * (v ^ Nat.rawCast 6 * Nat.rawCast 652653288) + (
    y ^ Nat.rawCast 22 * (v ^ Nat.rawCast 7 * NNRat.rawCast 49393395 2) + (
    y ^ Nat.rawCast 22 * (v ^ Nat.rawCast 8 * NNRat.rawCast 815751 2) + (
    y ^ Nat.rawCast 23 * Nat.rawCast 91729428480 + (
    y ^ Nat.rawCast 23 * (v ^ Nat.rawCast 1 * Nat.rawCast 98609135616) + (
    y ^ Nat.rawCast 23 * (v ^ Nat.rawCast 2 * Nat.rawCast 46151368704) + (
    y ^ Nat.rawCast 23 * (v ^ Nat.rawCast 3 * Nat.rawCast 12290310144) + (
    y ^ Nat.rawCast 23 * (v ^ Nat.rawCast 4 * Nat.rawCast 2037934080) + (
    y ^ Nat.rawCast 23 * (v ^ Nat.rawCast 5 * Nat.rawCast 215550720) + (
    y ^ Nat.rawCast 23 * (v ^ Nat.rawCast 6 * Nat.rawCast 14206752) + (
    y ^ Nat.rawCast 23 * (v ^ Nat.rawCast 7 * Nat.rawCast 533628) + (
    y ^ Nat.rawCast 23 * (v ^ Nat.rawCast 8 * Nat.rawCast 8748) + (
    v ^ Nat.rawCast 1 * NNRat.rawCast 1283668031950995285 32 + (
    v ^ Nat.rawCast 2 * NNRat.rawCast 43269831994163497065 1024 + (
    v ^ Nat.rawCast 3 * NNRat.rawCast 76852067160216319605 4096 + (
    v ^ Nat.rawCast 4 * NNRat.rawCast 18694569805934186925 4096 + (
    v ^ Nat.rawCast 5 * NNRat.rawCast 336988873358193465 512 + (
    v ^ Nat.rawCast 6 * NNRat.rawCast 115413627142342305 2048 + (
    v ^ Nat.rawCast 7 * NNRat.rawCast 87025379188252635 32768 + (
    v ^ Nat.rawCast 8 * NNRat.rawCast 1743060955981905 32768 + (
    tail))))))))))))))))))))))))
private theorem growthTransferBlock06_nonneg (y v tail : ℝ)
    (_hy : 0 ≤ y) (_hv : 0 ≤ v) (ht : 0 ≤ tail) :
    0 ≤ growthTransferBlock06 y v tail := by
  unfold growthTransferBlock06
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,Mathlib.Tactic.RingNF.nat_rawCast_1,
    Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity

private theorem growthTransferKernel_shift_pos (y v : ℝ) (hy : 0 ≤ y) (hv : 0 ≤ v) :
    0 < growthTransferKernel (3/2+y) (8+v) := by
  unfold growthTransferKernel
  rw [growthNumerator_three_eq,slopeNumerator_three_eq]
  unfold growthScore growthScoreJet
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [growthCoefficient,growthCoefficientJet,coolingCoefficient,coolingCoefficientJet,
    coolingCoefficientJetTwo]
  unfold transferAnchor transferAnchorSlope
  apply sub_pos.mp
  ring_nf (config := {mode := .raw})
  apply growthTransferBlock00_pos y v _ hy hv
  apply growthTransferBlock01_nonneg y v _ hy hv
  apply growthTransferBlock02_nonneg y v _ hy hv
  apply growthTransferBlock03_nonneg y v _ hy hv
  apply growthTransferBlock04_nonneg y v _ hy hv
  apply growthTransferBlock05_nonneg y v _ hy hv
  apply growthTransferBlock06_nonneg y v _ hy hv
  exact le_rfl

theorem growthTransferKernel_pos {q t : ℝ} (hq : 3/2 ≤ q) (ht : 8 ≤ t) :
    0 < growthTransferKernel q t := by
  have h := growthTransferKernel_shift_pos (q-3/2) (t-8) (by linarith) (by linarith)
  simpa only [show (3/2:ℝ)+(q-3/2)=q by ring,show (8:ℝ)+(t-8)=t by ring] using h

end
end RHTower.ThetaCuspDefect
