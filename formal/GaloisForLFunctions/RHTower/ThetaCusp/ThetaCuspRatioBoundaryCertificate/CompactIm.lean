import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.SlopeCoefficients
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
def boundaryCompactImVC75_0 (h : ℂ) : ℂ :=
  (((((h ^ (21-0:ℕ) * (NNRat.rawCast 27429101485 5159780352)) + (h ^ (21-1:ℕ) * (1 * NNRat.rawCast 1697645176421 11609505792))) + ((h ^ (21-2:ℕ) * (1 * NNRat.rawCast 196225277815531 123834728448)) + (h ^ (21-3:ℕ) * (1 * NNRat.rawCast 353780154807803 41278242816)))) + (((h ^ (21-4:ℕ) * (1 * NNRat.rawCast 108052329608933 4586471424)) + (h ^ (21-5:ℕ) * (1 * NNRat.rawCast 235771451135333 9172942848))) + ((h ^ (21-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 403807254809563) 24461180928)) + ((h ^ (21-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 553194879498421) 8153726976)) + (h ^ (21-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 78086561417617) 905969664)))))) + ((((h ^ (21-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 47653438766765) 301989888)) + (h ^ (21-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 43314015356077) 150994944))) + ((h ^ (21-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 7215135204485) 25165824)) + (h ^ (21-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1480272887473) 8388608)))) + (((h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 385687074393) 8388608)) + (h ^ (21-14:ℕ) * (1 * NNRat.rawCast 4514555151 524288))) + ((h ^ (21-15:ℕ) * (1 * NNRat.rawCast 31307254623 4194304)) + ((h ^ (21-16:ℕ) * (1 * NNRat.rawCast 2143063575 2097152)) + (h ^ (21-0:ℕ) * (0)))))))

theorem boundaryCompactImVC75_0_eq {h : ℂ} (hh : h≠0) :
    h^21*boundarySlopeImVC75_0 h⁻¹=boundaryCompactImVC75_0 h := by
  rw [(boundarySlopeImVC75_0Norm h⁻¹).property]
  dsimp only [boundarySlopeImVC75_0Norm,boundaryCompactImVC75_0]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactImVC75_1 (h : ℂ) : ℂ :=
  (((((h ^ (21-0:ℕ) * (Rat.rawCast (Int.negOfNat 184857827557) 417942208512)) + (h ^ (21-1:ℕ) * (1 * Rat.rawCast (Int.negOfNat 77546215409849) 835884417024))) + ((h ^ (21-2:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1815291212169305) 1253826625536)) + (h ^ (21-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 145595861950152211) 17832200896512)))) + (((h ^ (21-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 259355272022446715) 17832200896512)) + (h ^ (21-5:ℕ) * (1 * NNRat.rawCast 102538004872463045 3962711310336))) + ((h ^ (21-6:ℕ) * (1 * NNRat.rawCast 74291364526466905 660451885056)) + ((h ^ (21-7:ℕ) * (1 * NNRat.rawCast 144758318102038195 2641807540224)) + (h ^ (21-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 57764338619576083) 440301256704)))))) + ((((h ^ (21-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 709180814539553) 10871635968)) + (h ^ (21-10:ℕ) * (1 * NNRat.rawCast 3853735675901 2038431744))) + ((h ^ (21-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 5322463246392437) 16307453952)) + ((h ^ (21-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 487403723358485) 1811939328)) + (h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 140435009266811) 905969664))))) + (((h ^ (21-14:ℕ) * (1 * NNRat.rawCast 12147692281 8388608)) + (h ^ (21-15:ℕ) * (1 * NNRat.rawCast 104806913525 4194304))) + ((h ^ (21-16:ℕ) * (1 * NNRat.rawCast 19409725565 4194304)) + ((h ^ (21-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3537700575) 2097152)) + (h ^ (21-0:ℕ) * (0)))))))

theorem boundaryCompactImVC75_1_eq {h : ℂ} (hh : h≠0) :
    h^21*boundarySlopeImVC75_1 h⁻¹=boundaryCompactImVC75_1 h := by
  rw [(boundarySlopeImVC75_1Norm h⁻¹).property]
  dsimp only [boundarySlopeImVC75_1Norm,boundaryCompactImVC75_1]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactImVC75_2 (h : ℂ) : ℂ :=
  (((((h ^ (21-0:ℕ) * (Rat.rawCast (Int.negOfNat 37242466582621) 15045919506432)) + (h ^ (21-1:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1254464250852989) 180551034077184))) + ((h ^ (21-2:ℕ) * (1 * NNRat.rawCast 996130696258992781 2888816545234944)) + ((h ^ (21-3:ℕ) * (1 * NNRat.rawCast 875971993557133867 320979616137216)) + (h ^ (21-4:ℕ) * (1 * NNRat.rawCast 41754076126747365605 11555266180939776))))) + (((h ^ (21-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 69542130774647286185) 3851755393646592)) + (h ^ (21-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 44837104917074734837) 1283918464548864))) + ((h ^ (21-7:ℕ) * (1 * NNRat.rawCast 24208145906366581123 427972821516288)) + ((h ^ (21-8:ℕ) * (1 * NNRat.rawCast 754723872866343775 7925422620672)) + (h ^ (21-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1452100659165115363) 11888133931008)))))) + ((((h ^ (21-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 159961707471277067) 1761205026816)) + (h ^ (21-11:ℕ) * (1 * NNRat.rawCast 359448526698477877 1761205026816))) + ((h ^ (21-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 42015173395724431) 293534171136)) + ((h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 8053311891194269) 146767085568)) + (h ^ (21-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1581418449566329) 24461180928))))) + (((h ^ (21-15:ℕ) * (1 * NNRat.rawCast 59150350688339 4076863488)) + (h ^ (21-16:ℕ) * (1 * NNRat.rawCast 13294660908083 679477248))) + ((h ^ (21-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3493834939) 37748736)) + ((h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 20767772435) 18874368)) + (h ^ (21-0:ℕ) * (0)))))))

theorem boundaryCompactImVC75_2_eq {h : ℂ} (hh : h≠0) :
    h^21*boundarySlopeImVC75_2 h⁻¹=boundaryCompactImVC75_2 h := by
  rw [(boundarySlopeImVC75_2Norm h⁻¹).property]
  dsimp only [boundarySlopeImVC75_2Norm,boundaryCompactImVC75_2]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactImVC75_3 (h : ℂ) : ℂ :=
  (((((h ^ (21-0:ℕ) * (NNRat.rawCast 25392432737659 33853318889472)) + (h ^ (21-1:ℕ) * (1 * NNRat.rawCast 35213777399831863 3249918613389312))) + ((h ^ (21-2:ℕ) * (1 * Rat.rawCast (Int.negOfNat 15747911874540521) 1083306204463104)) + ((h ^ (21-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 110290885026902232415) 207994791256915968)) + (h ^ (21-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 153634139936233586977) 207994791256915968))))) + (((h ^ (21-5:ℕ) * (1 * NNRat.rawCast 1282628309404222887073 277326388342554624)) + (h ^ (21-6:ℕ) * (1 * NNRat.rawCast 1548806645332958792549 415989582513831936))) + ((h ^ (21-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 174126955421105363063) 6847565144260608)) + ((h ^ (21-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 424643147979146083777) 184884258895036416)) + (h ^ (21-9:ℕ) * (1 * NNRat.rawCast 1197431664934064086981 15407021574586368)))))) + ((((h ^ (21-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 39840762943397988995) 1711891286065152)) + (h ^ (21-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 16889721904996319377) 142657607172096))) + ((h ^ (21-12:ℕ) * (1 * NNRat.rawCast 508970529139131805 3962711310336)) + ((h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 70663623927078715) 1320903770112)) + (h ^ (21-14:ℕ) * (1 * NNRat.rawCast 2244965563384789 165112971264))))) + (((h ^ (21-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 852519606732089) 41278242816)) + ((h ^ (21-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 19998355996631) 12230590464)) + (h ^ (21-17:ℕ) * (1 * NNRat.rawCast 5344082188891 1146617856)))) + ((h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2020697904707) 3057647616)) + ((h ^ (21-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 15170363) 5308416)) + (h ^ (21-0:ℕ) * (0)))))))

theorem boundaryCompactImVC75_3_eq {h : ℂ} (hh : h≠0) :
    h^21*boundarySlopeImVC75_3 h⁻¹=boundaryCompactImVC75_3 h := by
  rw [(boundarySlopeImVC75_3Norm h⁻¹).property]
  dsimp only [boundarySlopeImVC75_3Norm,boundaryCompactImVC75_3]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactImVC75_4 (h : ℂ) : ℂ :=
  (((((h ^ (21-0:ℕ) * (Rat.rawCast (Int.negOfNat 20284677665801) 1828079220031488)) + (h ^ (21-1:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2145131480309245) 914039610015744))) + ((h ^ (21-2:ℕ) * (1 * Rat.rawCast (Int.negOfNat 305667986187197137) 38999023360671744)) + ((h ^ (21-3:ℕ) * (1 * NNRat.rawCast 259917494939025929 3656158440062976)) + (h ^ (21-4:ℕ) * (1 * NNRat.rawCast 2332084216577419178165 14975624970497949696))))) + (((h ^ (21-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 11095787700535033481053) 14975624970497949696)) + ((h ^ (21-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 11044526420847116351173) 29951249940995899392)) + (h ^ (21-7:ℕ) * (1 * NNRat.rawCast 15361466634911803010177 3327916660110655488)))) + ((h ^ (21-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 20474442936624974109997) 7487812485248974848)) + ((h ^ (21-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 12180153571556963385197) 831979165027663872)) + (h ^ (21-10:ℕ) * (1 * NNRat.rawCast 2383920112706856025837 138663194171277312)))))) + ((((h ^ (21-11:ℕ) * (1 * NNRat.rawCast 246548045283582801661 11555266180939776)) + (h ^ (21-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 575934161908701477383) 11555266180939776))) + ((h ^ (21-13:ℕ) * (1 * NNRat.rawCast 34343830477044446173 962938848411648)) + ((h ^ (21-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 443197318256033323) 26748301344768)) + (h ^ (21-15:ℕ) * (1 * NNRat.rawCast 418625329293845641 53496602689536))))) + (((h ^ (21-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 12908401958343563) 4458050224128)) + ((h ^ (21-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1220935858955671) 1486016741376)) + (h ^ (21-18:ℕ) * (1 * NNRat.rawCast 137647615951147 247669456896)))) + ((h ^ (21-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2820755267987) 20639121408)) + ((h ^ (21-20:ℕ) * (1 * NNRat.rawCast 4830556825 254803968)) + (h ^ (21-0:ℕ) * (0)))))))

theorem boundaryCompactImVC75_4_eq {h : ℂ} (hh : h≠0) :
    h^21*boundarySlopeImVC75_4 h⁻¹=boundaryCompactImVC75_4 h := by
  rw [(boundarySlopeImVC75_4Norm h⁻¹).property]
  dsimp only [boundarySlopeImVC75_4Norm,boundaryCompactImVC75_4]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactImVC75_5 (h : ℂ) : ℂ :=
  (((((h ^ (21-0:ℕ) * (Rat.rawCast (Int.negOfNat 1479421697135717) 65810851921133568)) + (h ^ (21-1:ℕ) * (1 * NNRat.rawCast 14783918267123351 65810851921133568))) + ((h ^ (21-2:ℕ) * (1 * NNRat.rawCast 259977087727915727 131621703842267136)) + ((h ^ (21-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 104024458499492322599) 16847578091810193408)) + (h ^ (21-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 8012122957936442058515) 269561249468963094528))))) + (((h ^ (21-5:ℕ) * (1 * NNRat.rawCast 22315043395977035489309 269561249468963094528)) + ((h ^ (21-6:ℕ) * (1 * NNRat.rawCast 37548666297781708544957 269561249468963094528)) + (h ^ (21-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 158870754839314040804773) 269561249468963094528)))) + ((h ^ (21-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1332887890223042354405) 134780624734481547264)) + ((h ^ (21-9:ℕ) * (1 * NNRat.rawCast 822779298208131658295 415989582513831936)) + (h ^ (21-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1332203911636682979547) 623984373770747904)))))) + ((((h ^ (21-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 12827771875331338031779) 5615859363936731136)) + ((h ^ (21-12:ℕ) * (1 * NNRat.rawCast 3716147500141826913041 467988280328060928)) + (h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 219802882573527109825) 25999348907114496)))) + ((h ^ (21-14:ℕ) * (1 * NNRat.rawCast 66110645978421189829 12999674453557248)) + ((h ^ (21-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3846618513379848161) 1444408272617472)) + (h ^ (21-16:ℕ) * (1 * NNRat.rawCast 284744187583252627 240734712102912))))) + (((h ^ (21-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 17834903652550199) 60183678025728)) + ((h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 80424429991165) 3343537668096)) + (h ^ (21-19:ℕ) * (1 * NNRat.rawCast 28377898278787 1114512556032)))) + ((h ^ (21-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 48440424487) 10319560704)) + ((h ^ (21-21:ℕ) * (1 * NNRat.rawCast 1415963209 46438023168)) + (h ^ (21-0:ℕ) * (0)))))))

theorem boundaryCompactImVC75_5_eq {h : ℂ} (hh : h≠0) :
    h^21*boundarySlopeImVC75_5 h⁻¹=boundaryCompactImVC75_5 h := by
  rw [(boundarySlopeImVC75_5Norm h⁻¹).property]
  dsimp only [boundarySlopeImVC75_5Norm,boundaryCompactImVC75_5]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactImVC75_6 (h : ℂ) : ℂ :=
  (((((h ^ (21-0:ℕ) * (NNRat.rawCast 1119105389526979 296148833645101056)) + (h ^ (21-1:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2939577980692427) 789730223053602816))) + ((h ^ (21-2:ℕ) * (1 * Rat.rawCast (Int.negOfNat 150934558425116527) 592297667290202112)) + ((h ^ (21-3:ℕ) * (1 * NNRat.rawCast 23876849155910486101 151628202826291740672)) + (h ^ (21-4:ℕ) * (1 * NNRat.rawCast 174567286430279108027 37907050706572935168))))) + (((h ^ (21-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 7284592085209150152173) 1213025622610333925376)) + ((h ^ (21-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3662866265733844675643) 101085468550861160448)) + (h ^ (21-7:ℕ) * (1 * NNRat.rawCast 90036390415964904175955 1213025622610333925376)))) + ((h ^ (21-8:ℕ) * (1 * NNRat.rawCast 65594174281734999347747 606512811305166962688)) + ((h ^ (21-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 36095393956487947591759) 101085468550861160448)) + (h ^ (21-10:ℕ) * (1 * NNRat.rawCast 22767639542521803714427 303256405652583481344)))))) + ((((h ^ (21-11:ℕ) * (1 * NNRat.rawCast 8694167503360249384345 16847578091810193408)) + ((h ^ (21-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 6657888251587653932215) 9476762676643233792)) + (h ^ (21-13:ℕ) * (1 * NNRat.rawCast 152141996556233844401 263243407684534272)))) + ((h ^ (21-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 48826751755423573697) 131621703842267136)) + ((h ^ (21-15:ℕ) * (1 * NNRat.rawCast 33730229198817979157 175495605123022848)) + (h ^ (21-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 219997941271283275) 1828079220031488))))) + (((h ^ (21-17:ℕ) * (1 * NNRat.rawCast 157688744149548647 2437438960041984)) + ((h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 39646388344825051) 1624959306694656)) + (h ^ (21-19:ℕ) * (1 * NNRat.rawCast 1261522490832569 270826551115776)))) + ((h ^ (21-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3118383321145) 7522959753216)) + ((h ^ (21-21:ℕ) * (1 * NNRat.rawCast 28759598545 3761479876608)) + (h ^ (21-0:ℕ) * (0)))))))

theorem boundaryCompactImVC75_6_eq {h : ℂ} (hh : h≠0) :
    h^21*boundarySlopeImVC75_6 h⁻¹=boundaryCompactImVC75_6 h := by
  rw [(boundarySlopeImVC75_6Norm h⁻¹).property]
  dsimp only [boundarySlopeImVC75_6Norm,boundaryCompactImVC75_6]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactImVC75_7 (h : ℂ) : ℂ :=
  (((((h ^ (21-0:ℕ) * (Rat.rawCast (Int.negOfNat 742521673386751) 2665339502805909504)) + (h ^ (21-1:ℕ) * (1 * Rat.rawCast (Int.negOfNat 35338293534191977) 21322716022447276032))) + ((h ^ (21-2:ℕ) * (1 * NNRat.rawCast 102343859453501011 4738381338321616896)) + ((h ^ (21-3:ℕ) * (1 * NNRat.rawCast 49325366184687466103 1364653825436625666048)) + (h ^ (21-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2788856400941062613429) 5458615301746502664192))))) + (((h ^ (21-5:ℕ) * (1 * NNRat.rawCast 1171637831918493252461 5458615301746502664192)) + ((h ^ (21-6:ℕ) * (1 * NNRat.rawCast 8923524902276450482633 1819538433915500888064)) + (h ^ (21-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 43882471341432012974747) 5458615301746502664192)))) + ((h ^ (21-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 87546033245226997776389) 5458615301746502664192)) + ((h ^ (21-9:ℕ) * (1 * NNRat.rawCast 265230337975473560334823 5458615301746502664192)) + (h ^ (21-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 21394567256770296485579) 2729307650873251332096)))))) + ((((h ^ (21-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 106111160218854659779825) 1364653825436625666048)) + ((h ^ (21-12:ℕ) * (1 * NNRat.rawCast 842726915517664572821 14215144014964850688)) + (h ^ (21-13:ℕ) * (1 * NNRat.rawCast 3704515312396018479853 85290864089789104128)))) + ((h ^ (21-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1275647106807323008463) 14215144014964850688)) + ((h ^ (21-15:ℕ) * (1 * NNRat.rawCast 129757651923090564323 1776893001870606336)) + (h ^ (21-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2037969511651823051) 49358138940850176))))) + (((h ^ (21-17:ℕ) * (1 * NNRat.rawCast 3802187662892235037 263243407684534272)) + ((h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 326326367575866481) 131621703842267136)) + (h ^ (21-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 17600440647665) 270826551115776)))) + ((h ^ (21-20:ℕ) * (1 * NNRat.rawCast 27327568185443 609359740010496)) + ((h ^ (21-21:ℕ) * (1 * Rat.rawCast (Int.negOfNat 122089290161) 76169967501312)) + (h ^ (21-0:ℕ) * (0)))))))

theorem boundaryCompactImVC75_7_eq {h : ℂ} (hh : h≠0) :
    h^21*boundarySlopeImVC75_7 h⁻¹=boundaryCompactImVC75_7 h := by
  rw [(boundarySlopeImVC75_7Norm h⁻¹).property]
  dsimp only [boundarySlopeImVC75_7Norm,boundaryCompactImVC75_7]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactImVC75_8 (h : ℂ) : ℂ :=
  (((((h ^ (21-0:ℕ) * (NNRat.rawCast 13468290577691 1332669751402954752)) + (h ^ (21-1:ℕ) * (1 * NNRat.rawCast 18980919410755759 95952222101012742144))) + ((h ^ (21-2:ℕ) * (1 * Rat.rawCast (Int.negOfNat 885911481751024529) 767617776808101937152)) + ((h ^ (21-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 61447296244520948231) 12281884428929630994432)) + (h ^ (21-4:ℕ) * (1 * NNRat.rawCast 1662452534149833013517 49127537715718523977728))))) + (((h ^ (21-5:ℕ) * (1 * NNRat.rawCast 603891207997987813253 49127537715718523977728)) + ((h ^ (21-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 34444039147129021737943) 98255075431437047955456)) + (h ^ (21-7:ℕ) * (1 * NNRat.rawCast 43813546331831456080615 98255075431437047955456)))) + ((h ^ (21-8:ℕ) * (1 * NNRat.rawCast 27484358263067175510793 24563768857859261988864)) + ((h ^ (21-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 75744369757104597786673) 24563768857859261988864)) + (h ^ (21-10:ℕ) * (1 * NNRat.rawCast 2803365520936702504999 4093961476309876998144)))))) + ((((h ^ (21-11:ℕ) * (1 * NNRat.rawCast 59835780665371331143681 12281884428929630994432)) + ((h ^ (21-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 224033475842517801395) 75814101413145870336)) + (h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 4537868508482449510447) 511745184538734624768)))) + ((h ^ (21-14:ℕ) * (1 * NNRat.rawCast 6720583837678091972885 383808888404050968576)) + ((h ^ (21-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 767660047926502459415) 47976111050506371072)) + (h ^ (21-16:ℕ) * (1 * NNRat.rawCast 648917405575460129209 63968148067341828096))))) + (((h ^ (21-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 51329531888847422429) 10661358011223638016)) + ((h ^ (21-18:ℕ) * (1 * NNRat.rawCast 302336333003724493 197432555763400704)) + (h ^ (21-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 175095897514994519) 592297667290202112)))) + ((h ^ (21-20:ℕ) * (1 * NNRat.rawCast 2756658698183947 98716277881700352)) + ((h ^ (21-21:ℕ) * (1 * Rat.rawCast (Int.negOfNat 8201635047221) 8226356490141696)) + (h ^ (21-0:ℕ) * (0)))))))

theorem boundaryCompactImVC75_8_eq {h : ℂ} (hh : h≠0) :
    h^21*boundarySlopeImVC75_8 h⁻¹=boundaryCompactImVC75_8 h := by
  rw [(boundarySlopeImVC75_8Norm h⁻¹).property]
  dsimp only [boundarySlopeImVC75_8Norm,boundaryCompactImVC75_8]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactImVC75_9 (h : ℂ) : ℂ :=
  (((((h ^ (21-0:ℕ) * (Rat.rawCast (Int.negOfNat 63860187804325) 431784999454557339648)) + (h ^ (21-1:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2765220130844951) 287856666303038226432))) + ((h ^ (21-2:ℕ) * (1 * NNRat.rawCast 13412501716325153 575713332606076452864)) + ((h ^ (21-3:ℕ) * (1 * NNRat.rawCast 11462164070981874049 36845653286788892983296)) + (h ^ (21-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 831144632839076075257) 884295678882933431599104))))) + (((h ^ (21-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2650852379824084196465) 884295678882933431599104)) + ((h ^ (21-6:ℕ) * (1 * NNRat.rawCast 11124450723713509024759 884295678882933431599104)) + (h ^ (21-7:ℕ) * (1 * NNRat.rawCast 1452750819988746324919 294765226294311143866368)))) + ((h ^ (21-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 28621178566725299905333) 442147839441466715799552)) + ((h ^ (21-9:ℕ) * (1 * NNRat.rawCast 103686602394755897927 2046980738154938499072)) + (h ^ (21-10:ℕ) * (1 * NNRat.rawCast 2178165190301217171071 18422826643394446491648)))))) + ((((h ^ (21-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 12397113453579769175881) 55268479930183339474944)) + ((h ^ (21-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 50050519095905892985) 3454279995636458717184)) + (h ^ (21-13:ℕ) * (1 * NNRat.rawCast 7789231460582828545727 13817119982545834868736)))) + ((h ^ (21-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1181084971815308952085) 1151426665212152905728)) + ((h ^ (21-15:ℕ) * (1 * NNRat.rawCast 1178619399096245367895 1151426665212152905728)) + (h ^ (21-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1176811753864755329497) 1727139997818229358592))))) + (((h ^ (21-17:ℕ) * (1 * NNRat.rawCast 12193802341173352315 35982083287879778304)) + ((h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2943027671712739409) 23988055525253185536)) + (h ^ (21-19:ℕ) * (1 * NNRat.rawCast 211017156126564169 7996018508417728512)))) + ((h ^ (21-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1546504537702189) 666334875701477376)) + ((h ^ (21-21:ℕ) * (1 * Rat.rawCast (Int.negOfNat 11523388527833) 222111625233825792)) + (h ^ (21-0:ℕ) * (0)))))))

theorem boundaryCompactImVC75_9_eq {h : ℂ} (hh : h≠0) :
    h^21*boundarySlopeImVC75_9 h⁻¹=boundaryCompactImVC75_9 h := by
  rw [(boundarySlopeImVC75_9Norm h⁻¹).property]
  dsimp only [boundarySlopeImVC75_9Norm,boundaryCompactImVC75_9]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactImVC75_10 (h : ℂ) : ℂ :=
  (((((h ^ (21-1:ℕ) * (1 * NNRat.rawCast 2763132821290541 15544259980364064227328)) + (h ^ (21-2:ℕ) * (1 * NNRat.rawCast 115602713701059643 124354079842912513818624))) + ((h ^ (21-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 10668827186198714329) 994832638743300110548992)) + ((h ^ (21-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 11602777841668913155) 994832638743300110548992)) + (h ^ (21-5:ℕ) * (1 * NNRat.rawCast 278565705665590818863 1326443518324400147398656))))) + (((h ^ (21-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 730400333513838868537) 3979330554973200442195968)) + ((h ^ (21-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2967678770428371016883) 1989665277486600221097984)) + (h ^ (21-8:ℕ) * (1 * NNRat.rawCast 6732687577698146896513 1989665277486600221097984)))) + ((h ^ (21-9:ℕ) * (1 * NNRat.rawCast 236052740124371921015 165805439790550018424832)) + ((h ^ (21-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 12490145536615428779039) 994832638743300110548992)) + (h ^ (21-11:ℕ) * (1 * NNRat.rawCast 3756422781579954181171 248708159685825027637248)))))) + ((((h ^ (21-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 431107406961313709959) 82902719895275009212416)) + (h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 183488636763979444499) 124354079842912513818624))) + ((h ^ (21-14:ℕ) * (1 * NNRat.rawCast 42200567518653481859 62177039921456256909312)) + ((h ^ (21-15:ℕ) * (1 * NNRat.rawCast 2567486478940465339 10362839986909376151552)) + (h ^ (21-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 186993163112492717) 191904444202025484288))))) + (((h ^ (21-17:ℕ) * (1 * NNRat.rawCast 405894573348658397 287856666303038226432)) + ((h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 15397603669177765) 23988055525253185536)) + (h ^ (21-19:ℕ) * (1 * NNRat.rawCast 284337688244123 2665339502805909504)))) + ((h ^ (21-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 29923102734281) 666334875701477376)) + ((h ^ (21-21:ℕ) * (1 * NNRat.rawCast 2027567501417 111055812616912896)) + (h ^ (21-0:ℕ) * (0)))))))

theorem boundaryCompactImVC75_10_eq {h : ℂ} (hh : h≠0) :
    h^21*boundarySlopeImVC75_10 h⁻¹=boundaryCompactImVC75_10 h := by
  rw [(boundarySlopeImVC75_10Norm h⁻¹).property]
  dsimp only [boundarySlopeImVC75_10Norm,boundaryCompactImVC75_10]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactImVC75_11 (h : ℂ) : ℂ :=
  (((((h ^ (21-2:ℕ) * (1 * Rat.rawCast (Int.negOfNat 12177572871726983) 279796679646553156091904)) + (h ^ (21-3:ℕ) * (1 * NNRat.rawCast 276250494121672511 2238373437172425248735232))) + ((h ^ (21-4:ℕ) * (1 * NNRat.rawCast 36715794121288289951 35813974994758803979763712)) + ((h ^ (21-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2651240975580384035) 663221759162200073699328)) + (h ^ (21-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 51231536509561229437) 11937991664919601326587904))))) + (((h ^ (21-7:ℕ) * (1 * NNRat.rawCast 876512525061514920299 23875983329839202653175808)) + (h ^ (21-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 907436930742855671087) 23875983329839202653175808))) + ((h ^ (21-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 6190141896446080159) 93265559882184385363968)) + ((h ^ (21-10:ℕ) * (1 * NNRat.rawCast 356100210095292795113 1989665277486600221097984)) + (h ^ (21-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 354172127059892889013) 2238373437172425248735232)))))) + ((((h ^ (21-12:ℕ) * (1 * NNRat.rawCast 268304706585517554167 1119186718586212624367616)) + (h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 306893460640637783507) 373062239528737541455872))) + ((h ^ (21-14:ℕ) * (1 * NNRat.rawCast 226520684664239487989 139898339823276578045952)) + ((h ^ (21-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 85208931354555915247) 46632779941092192681984)) + (h ^ (21-16:ℕ) * (1 * NNRat.rawCast 13639926687849953299 10362839986909376151552))))) + (((h ^ (21-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1662912652745549323) 2590709996727344037888)) + ((h ^ (21-18:ℕ) * (1 * NNRat.rawCast 168867306342210395 863569998909114679296)) + (h ^ (21-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 425029829189723) 23988055525253185536)))) + ((h ^ (21-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 58328125867511) 5997013881313296384)) + ((h ^ (21-21:ℕ) * (1 * NNRat.rawCast 697175670491 249875578388054016)) + (h ^ (21-0:ℕ) * (0)))))))

theorem boundaryCompactImVC75_11_eq {h : ℂ} (hh : h≠0) :
    h^21*boundarySlopeImVC75_11 h⁻¹=boundaryCompactImVC75_11 h := by
  rw [(boundarySlopeImVC75_11Norm h⁻¹).property]
  dsimp only [boundarySlopeImVC75_11Norm,boundaryCompactImVC75_11]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactImVC75_12 (h : ℂ) : ℂ :=
  (((((h ^ (21-3:ℕ) * (1 * NNRat.rawCast 259263771223410611 80581443738207308954468352)) + (h ^ (21-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 6771534277469186855) 644651549905658471635746816))) + ((h ^ (21-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 41233895519141854669) 644651549905658471635746816)) + ((h ^ (21-6:ℕ) * (1 * NNRat.rawCast 129834755092999434521 429767699937105647757164544)) + (h ^ (21-7:ℕ) * (1 * NNRat.rawCast 40891582619342933323 429767699937105647757164544))))) + (((h ^ (21-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 780432523886176868077) 322325774952829235817873408)) + (h ^ (21-9:ℕ) * (1 * NNRat.rawCast 434824457127091522529 107441924984276411939291136))) + ((h ^ (21-10:ℕ) * (1 * NNRat.rawCast 84819599235729847945 53720962492138205969645568)) + ((h ^ (21-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 32236630840567180195) 2238373437172425248735232)) + (h ^ (21-12:ℕ) * (1 * NNRat.rawCast 357808292494234197353 13430240623034551492411392)))))) + ((((h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 345076523572688408639) 10072680467275913619308544)) + (h ^ (21-14:ℕ) * (1 * NNRat.rawCast 29744438864974513301 839390038939659468275712))) + ((h ^ (21-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 15460873766844241777) 559593359293106312183808)) + ((h ^ (21-16:ℕ) * (1 * NNRat.rawCast 693243905027729521 46632779941092192681984)) + (h ^ (21-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 69965147823604477) 15544259980364064227328))))) + (((h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1449196054625731) 2590709996727344037888)) + (h ^ (21-19:ℕ) * (1 * NNRat.rawCast 76578580512751 53973124931819667456))) + ((h ^ (21-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 47362056109777) 71964166575759556608)) + ((h ^ (21-21:ℕ) * (1 * NNRat.rawCast 339604856879 2998506940656648192)) + (h ^ (21-0:ℕ) * (0)))))))

theorem boundaryCompactImVC75_12_eq {h : ℂ} (hh : h≠0) :
    h^21*boundarySlopeImVC75_12 h⁻¹=boundaryCompactImVC75_12 h := by
  rw [(boundarySlopeImVC75_12Norm h⁻¹).property]
  dsimp only [boundarySlopeImVC75_12Norm,boundaryCompactImVC75_12]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactImVC75_13 (h : ℂ) : ℂ :=
  (((((h ^ (21-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 308296208412382897) 3867909299433950829814480896)) + (h ^ (21-5:ℕ) * (1 * NNRat.rawCast 1733146236921181453 11603727898301852489443442688))) + ((h ^ (21-6:ℕ) * (1 * NNRat.rawCast 6375695219256325151 3867909299433950829814480896)) + (h ^ (21-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 56090595233724044413) 11603727898301852489443442688)))) + (((h ^ (21-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 40581628574320095505) 5801863949150926244721721344)) + (h ^ (21-9:ℕ) * (1 * NNRat.rawCast 20910924802386688763 483488662429243853726810112))) + ((h ^ (21-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 11030220801096393163) 241744331214621926863405056)) + ((h ^ (21-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 15871506289105900207) 241744331214621926863405056)) + (h ^ (21-12:ℕ) * (1 * NNRat.rawCast 1700590599923844623 6715120311517275746205696)))))) + ((((h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 416739548982250871) 1119186718586212624367616)) + (h ^ (21-14:ℕ) * (1 * NNRat.rawCast 20655960538821725 62177039921456256909312))) + ((h ^ (21-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 11378897714332081) 62177039921456256909312)) + ((h ^ (21-16:ℕ) * (1 * NNRat.rawCast 413417462475143 10362839986909376151552)) + (h ^ (21-17:ℕ) * (1 * NNRat.rawCast 29660368261253 863569998909114679296))))) + (((h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 6814808029253) 143928333151519113216)) + (h ^ (21-19:ℕ) * (1 * NNRat.rawCast 1449123128095 47976111050506371072))) + ((h ^ (21-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 128086332385) 11994027762626592768)) + ((h ^ (21-21:ℕ) * (1 * NNRat.rawCast 1088169557 666334875701477376)) + (h ^ (21-0:ℕ) * (0)))))))

theorem boundaryCompactImVC75_13_eq {h : ℂ} (hh : h≠0) :
    h^21*boundarySlopeImVC75_13 h⁻¹=boundaryCompactImVC75_13 h := by
  rw [(boundarySlopeImVC75_13Norm h⁻¹).property]
  dsimp only [boundarySlopeImVC75_13Norm,boundaryCompactImVC75_13]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactImVC75_14 (h : ℂ) : ℂ :=
  (((((h ^ (21-5:ℕ) * (1 * NNRat.rawCast 33325770944820067 52216775542358336202495492096)) + (h ^ (21-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2150726749913651) 26108387771179168101247746048))) + ((h ^ (21-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 215813021449087265) 17405591847452778734165164032)) + (h ^ (21-8:ℕ) * (1 * NNRat.rawCast 438359376756264859 26108387771179168101247746048)))) + (((h ^ (21-9:ℕ) * (1 * NNRat.rawCast 309441909453956615 4351397961863194683541291008)) + (h ^ (21-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 300497245475259401) 1450465987287731561180430336))) + ((h ^ (21-11:ℕ) * (1 * NNRat.rawCast 136391578290798275 2175698980931597341770645504)) + ((h ^ (21-12:ℕ) * (1 * NNRat.rawCast 48146518272214579 90654124205483222573776896)) + (h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1883935891253153) 1678780077879318936551424)))))) + ((((h ^ (21-14:ℕ) * (1 * NNRat.rawCast 957224681919997 839390038939659468275712)) + (h ^ (21-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 179309194221989) 279796679646553156091904))) + ((h ^ (21-16:ℕ) * (1 * NNRat.rawCast 769261509433 7772129990182032113664)) + (h ^ (21-17:ℕ) * (1 * NNRat.rawCast 789598641251 3886064995091016056832)))) + (((h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 672978592433) 2590709996727344037888)) + (h ^ (21-19:ℕ) * (1 * NNRat.rawCast 8068557079 47976111050506371072))) + ((h ^ (21-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 6422749579) 107946249863639334912)) + ((h ^ (21-21:ℕ) * (1 * NNRat.rawCast 160573861 17991041643939889152)) + (h ^ (21-0:ℕ) * (0)))))))

theorem boundaryCompactImVC75_14_eq {h : ℂ} (hh : h≠0) :
    h^21*boundarySlopeImVC75_14 h⁻¹=boundaryCompactImVC75_14 h := by
  rw [(boundarySlopeImVC75_14Norm h⁻¹).property]
  dsimp only [boundarySlopeImVC75_14Norm,boundaryCompactImVC75_14]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactImVC75_15 (h : ℂ) : ℂ :=
  (((((h ^ (21-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 20228983537427) 14685968121288282056951857152)) + (h ^ (21-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 49776973961981) 26108387771179168101247746048))) + ((h ^ (21-8:ℕ) * (1 * NNRat.rawCast 9251706189649 407943558924674501581996032)) + (h ^ (21-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 246438973711903) 78325163313537504303743238144)))) + (((h ^ (21-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 5667455241208943) 39162581656768752151871619072)) + (h ^ (21-11:ℕ) * (1 * NNRat.rawCast 1440045205742479 6527096942794792025311936512))) + ((h ^ (21-12:ℕ) * (1 * NNRat.rawCast 10405510821289 67990593154112416930332672)) + (h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3057373250401) 3777255175228467607240704))))) + ((((h ^ (21-14:ℕ) * (1 * NNRat.rawCast 2820366673361 2518170116818978404827136)) + (h ^ (21-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 370489998715) 419695019469829734137856))) + ((h ^ (21-16:ℕ) * (1 * NNRat.rawCast 51504189035 139898339823276578045952)) + (h ^ (21-17:ℕ) * (1 * NNRat.rawCast 6688106383 46632779941092192681984)))) + (((h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3081004639) 7772129990182032113664)) + (h ^ (21-19:ℕ) * (1 * NNRat.rawCast 1208055905 3886064995091016056832))) + ((h ^ (21-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 37748009) 323838749590918004736)) + ((h ^ (21-21:ℕ) * (1 * NNRat.rawCast 236221 13493281232954916864)) + (h ^ (21-0:ℕ) * (0)))))))

theorem boundaryCompactImVC75_15_eq {h : ℂ} (hh : h≠0) :
    h^21*boundarySlopeImVC75_15 h⁻¹=boundaryCompactImVC75_15 h := by
  rw [(boundarySlopeImVC75_15Norm h⁻¹).property]
  dsimp only [boundarySlopeImVC75_15Norm,boundaryCompactImVC75_15]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactImVC75_16 (h : ℂ) : ℂ :=
  (((((h ^ (21-7:ℕ) * (1 * NNRat.rawCast 121763303179 264347426183189077025133428736)) + (h ^ (21-8:ℕ) * (1 * NNRat.rawCast 295754879875 264347426183189077025133428736))) + ((h ^ (21-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1016211943691) 176231617455459384683422285824)) + (h ^ (21-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 14309462993) 3263548471397396012655968256)))) + (((h ^ (21-11:ℕ) * (1 * NNRat.rawCast 637681789283 19581290828384376075935809536)) + (h ^ (21-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 119061920929) 3263548471397396012655968256))) + ((h ^ (21-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 518880257) 30218041401827740857925632)) + (h ^ (21-14:ℕ) * (1 * NNRat.rawCast 1155165971 7554510350456935214481408))))) + ((((h ^ (21-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 834148613) 2518170116818978404827136)) + (h ^ (21-16:ℕ) * (1 * NNRat.rawCast 142757915 419695019469829734137856))) + ((h ^ (21-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 9341461) 104923754867457433534464)) + (h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1315019) 8743646238954786127872)))) + (((h ^ (21-19:ℕ) * (1 * NNRat.rawCast 70265 431784999454557339648)) + (h ^ (21-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 126809) 1943032497545508028416))) + ((h ^ (21-21:ℕ) * (1 * NNRat.rawCast 1589 161919374795459002368)) + (h ^ (21-0:ℕ) * (0))))))

theorem boundaryCompactImVC75_16_eq {h : ℂ} (hh : h≠0) :
    h^21*boundarySlopeImVC75_16 h⁻¹=boundaryCompactImVC75_16 h := by
  rw [(boundarySlopeImVC75_16Norm h⁻¹).property]
  dsimp only [boundarySlopeImVC75_16Norm,boundaryCompactImVC75_16]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactImVC75_17 (h : ℂ) : ℂ :=
  ((((h ^ (21-8:ℕ) * (1 * NNRat.rawCast 5764801 148695427228043855826637553664)) + ((h ^ (21-9:ℕ) * (1 * NNRat.rawCast 45294865 198260569637391807768850071552)) + (h ^ (21-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 823543) 5507238045483105771356946432)))) + (((h ^ (21-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 24118045) 11014476090966211542713892864)) + (h ^ (21-12:ℕ) * (1 * NNRat.rawCast 991613 917873007580517628559491072))) + ((h ^ (21-13:ℕ) * (1 * NNRat.rawCast 2518649 271962372616449667721330688)) + (h ^ (21-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 171157) 16997648288528104232583168))))) + ((((h ^ (21-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 75943) 5665882762842701410861056)) + (h ^ (21-16:ℕ) * (1 * NNRat.rawCast 4859 157385632301186150301696))) + ((h ^ (21-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 15397) 944313793807116901810176)) + (h ^ (21-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 245) 39346408075296537575424)))) + (((h ^ (21-19:ℕ) * (1 * NNRat.rawCast 47 4371823119477393063936)) + (h ^ (21-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 5) 1092955779869348265984))) + ((h ^ (21-21:ℕ) * (1 * NNRat.rawCast 1 1457274373159131021312)) + (h ^ (21-0:ℕ) * (0))))))

theorem boundaryCompactImVC75_17_eq {h : ℂ} (hh : h≠0) :
    h^21*boundarySlopeImVC75_17 h⁻¹=boundaryCompactImVC75_17 h := by
  rw [(boundarySlopeImVC75_17Norm h⁻¹).property]
  dsimp only [boundarySlopeImVC75_17Norm,boundaryCompactImVC75_17]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactImVC75_18 (h : ℂ) : ℂ :=
  (h ^ (21-0:ℕ) * (0))

theorem boundaryCompactImVC75_18_eq {h : ℂ} (hh : h≠0) :
    h^21*boundarySlopeImVC75_18 h⁻¹=boundaryCompactImVC75_18 h := by
  rw [(boundarySlopeImVC75_18Norm h⁻¹).property]
  dsimp only [boundarySlopeImVC75_18Norm,boundaryCompactImVC75_18]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

end
end HTGeometry.ThetaRatioInfinity
