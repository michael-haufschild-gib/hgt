import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.SlopeCoefficients
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
def boundaryCompactReVC75_0 (h : ℂ) : ℂ :=
  (((((h ^ (22-0:ℕ) * (NNRat.rawCast 2573973995 2902376448)) + (h ^ (22-1:ℕ) * (1 * NNRat.rawCast 338900672335 17414258688))) + ((h ^ (22-2:ℕ) * (1 * NNRat.rawCast 55724743567 429981696)) + (h ^ (22-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 4706340498913) 61917364224)))) + (((h ^ (22-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 197405054102927) 41278242816)) + (h ^ (22-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 623312575473853) 27518828544))) + ((h ^ (22-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 367564930306885) 9172942848)) + ((h ^ (22-7:ℕ) * (1 * NNRat.rawCast 2408369381717 2038431744)) + (h ^ (22-8:ℕ) * (1 * NNRat.rawCast 840943075781335 8153726976)))))) + ((((h ^ (22-9:ℕ) * (1 * NNRat.rawCast 67201316424679 452984832)) + (h ^ (22-10:ℕ) * (1 * NNRat.rawCast 128399801008549 905969664))) + ((h ^ (22-11:ℕ) * (1 * NNRat.rawCast 10267109560423 50331648)) + ((h ^ (22-12:ℕ) * (1 * NNRat.rawCast 4688785053799 25165824)) + (h ^ (22-13:ℕ) * (1 * NNRat.rawCast 1065954322969 8388608))))) + (((h ^ (22-14:ℕ) * (1 * NNRat.rawCast 330759446817 8388608)) + (h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 14668844751) 4194304))) + ((h ^ (22-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 25694689023) 4194304)) + ((h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2143063575) 2097152)) + (h ^ (22-0:ℕ) * (0)))))))

theorem boundaryCompactReVC75_0_eq {h : ℂ} (hh : h≠0) :
    h^22*boundarySlopeReVC75_0 h⁻¹=boundaryCompactReVC75_0 h := by
  rw [(boundarySlopeReVC75_0Norm h⁻¹).property]
  dsimp only [boundarySlopeReVC75_0Norm,boundaryCompactReVC75_0]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactReVC75_1 (h : ℂ) : ℂ :=
  (((((h ^ (22-0:ℕ) * (Rat.rawCast (Int.negOfNat 17292029129) 52242776064)) + (h ^ (22-1:ℕ) * (1 * NNRat.rawCast 24955595685487 3761479876608))) + ((h ^ (22-2:ℕ) * (1 * NNRat.rawCast 839106961710943 5015306502144)) + ((h ^ (22-3:ℕ) * (1 * NNRat.rawCast 45036002279140661 40122452017152)) + (h ^ (22-4:ℕ) * (1 * NNRat.rawCast 5151597573795289 1981355655168))))) + (((h ^ (22-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 30067988072344235) 17832200896512)) + (h ^ (22-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 67265735545439009) 3962711310336))) + ((h ^ (22-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3780203172032099) 146767085568)) + ((h ^ (22-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2739206985380101) 330225942528)) + (h ^ (22-9:ℕ) * (1 * NNRat.rawCast 14148525842108561 440301256704)))))) + ((((h ^ (22-10:ℕ) * (1 * NNRat.rawCast 3591841198761031 48922361856)) + (h ^ (22-11:ℕ) * (1 * NNRat.rawCast 751753536487855 8153726976))) + ((h ^ (22-12:ℕ) * (1 * NNRat.rawCast 1786487770662925 16307453952)) + ((h ^ (22-13:ℕ) * (1 * NNRat.rawCast 22204205508317 603979776)) + (h ^ (22-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 204813782125) 452984832))))) + (((h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 250681695941) 25165824)) + (h ^ (22-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 8454111609) 4194304))) + ((h ^ (22-17:ℕ) * (1 * NNRat.rawCast 2340170249 4194304)) + ((h ^ (22-18:ℕ) * (1 * NNRat.rawCast 317173155 1048576)) + (h ^ (22-0:ℕ) * (0)))))))

theorem boundaryCompactReVC75_1_eq {h : ℂ} (hh : h≠0) :
    h^22*boundarySlopeReVC75_1 h⁻¹=boundaryCompactReVC75_1 h := by
  rw [(boundarySlopeReVC75_1Norm h⁻¹).property]
  dsimp only [boundarySlopeReVC75_1Norm,boundaryCompactReVC75_1]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactReVC75_2 (h : ℂ) : ℂ :=
  (((((h ^ (22-0:ℕ) * (NNRat.rawCast 20219441971579 33853318889472)) + (h ^ (22-1:ℕ) * (1 * NNRat.rawCast 46128252912581 22568879259648))) + ((h ^ (22-2:ℕ) * (1 * Rat.rawCast (Int.negOfNat 49683018421054853) 722204136308736)) + ((h ^ (22-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 8293584138003209) 16926659444736)) + (h ^ (22-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 222036889921946309) 1925877696823296))))) + (((h ^ (22-5:ℕ) * (1 * NNRat.rawCast 29074569920658936547 5777633090469888)) + (h ^ (22-6:ℕ) * (1 * NNRat.rawCast 38936215187601031349 7703510787293184))) + ((h ^ (22-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 23134312829944287313) 1283918464548864)) + ((h ^ (22-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3283120390260343081) 213986410758144)) + (h ^ (22-9:ℕ) * (1 * NNRat.rawCast 2577054043646679577 95105071448064)))))) + ((((h ^ (22-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 43031725233047023) 47552535724032)) + (h ^ (22-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 517796061788995) 16307453952))) + ((h ^ (22-12:ℕ) * (1 * NNRat.rawCast 29569024117770637 587068342272)) + ((h ^ (22-13:ℕ) * (1 * NNRat.rawCast 7015422420796223 293534171136)) + (h ^ (22-14:ℕ) * (1 * NNRat.rawCast 2191897219508795 146767085568))))) + (((h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 195638259582067) 24461180928)) + ((h ^ (22-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 28226486170435) 4076863488)) + (h ^ (22-17:ℕ) * (1 * NNRat.rawCast 330508399625 679477248)))) + ((h ^ (22-18:ℕ) * (1 * NNRat.rawCast 14721710857 37748736)) + ((h ^ (22-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 295633355) 18874368)) + (h ^ (22-0:ℕ) * (0)))))))

theorem boundaryCompactReVC75_2_eq {h : ℂ} (hh : h≠0) :
    h^22*boundarySlopeReVC75_2 h⁻¹=boundaryCompactReVC75_2 h := by
  rw [(boundarySlopeReVC75_2Norm h⁻¹).property]
  dsimp only [boundarySlopeReVC75_2Norm,boundaryCompactReVC75_2]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactReVC75_3 (h : ℂ) : ℂ :=
  (((((h ^ (22-0:ℕ) * (Rat.rawCast (Int.negOfNat 18738851201825) 101559956668416)) + (h ^ (22-1:ℕ) * (1 * Rat.rawCast (Int.negOfNat 90256708004023) 38084983750656))) + ((h ^ (22-2:ℕ) * (1 * NNRat.rawCast 17324976025536443 2166612408926208)) + ((h ^ (22-3:ℕ) * (1 * NNRat.rawCast 2314620102503007505 19499511680335872)) + (h ^ (22-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 54745614365774773109) 623984373770747904))))) + (((h ^ (22-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3882748207687346909285) 2495937495082991616)) + ((h ^ (22-6:ℕ) * (1 * NNRat.rawCast 229055935164392221813 207994791256915968)) + (h ^ (22-7:ℕ) * (1 * NNRat.rawCast 14510317869674037298997 1663958330055327744)))) + ((h ^ (22-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 121585713866489571841) 15407021574586368)) + ((h ^ (22-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3896779907004063833143) 184884258895036416)) + (h ^ (22-10:ℕ) * (1 * NNRat.rawCast 195124945227342650339 7703510787293184)))))) + ((((h ^ (22-11:ℕ) * (1 * NNRat.rawCast 33783576514210273303 1711891286065152)) + (h ^ (22-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 7361057213124629149) 142657607172096))) + ((h ^ (22-13:ℕ) * (1 * NNRat.rawCast 283551782499224893 7925422620672)) + ((h ^ (22-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 37311574969886143) 3962711310336)) + (h ^ (22-15:ℕ) * (1 * NNRat.rawCast 5908005846099869 660451885056))))) + (((h ^ (22-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 496866136571689) 330225942528)) + ((h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 25252133621603) 12230590464)) + (h ^ (22-18:ℕ) * (1 * NNRat.rawCast 7601836559675 9172942848)))) + ((h ^ (22-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 261107069759) 3057647616)) + ((h ^ (22-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 118427) 331776)) + (h ^ (22-0:ℕ) * (0)))))))

theorem boundaryCompactReVC75_3_eq {h : ℂ} (hh : h≠0) :
    h^22*boundarySlopeReVC75_3 h⁻¹=boundaryCompactReVC75_3 h := by
  rw [(boundarySlopeReVC75_3Norm h⁻¹).property]
  dsimp only [boundarySlopeReVC75_3Norm,boundaryCompactReVC75_3]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactReVC75_4 (h : ℂ) : ℂ :=
  (((((h ^ (22-0:ℕ) * (NNRat.rawCast 2130476228443 1218719480020992)) + (h ^ (22-1:ℕ) * (1 * NNRat.rawCast 2165935878964505 3656158440062976))) + ((h ^ (22-2:ℕ) * (1 * NNRat.rawCast 137173779309851905 350991210246045696)) + ((h ^ (22-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 845862351893666249) 38999023360671744)) + (h ^ (22-4:ℕ) * (1 * NNRat.rawCast 846538065240488697023 44926874911493849088))))) + (((h ^ (22-5:ℕ) * (1 * NNRat.rawCast 6216584612660265947341 22463437455746924544)) + ((h ^ (22-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1980495601564716868033) 3743906242624487424)) + (h ^ (22-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 15618423417637542795461) 11231718727873462272)))) + ((h ^ (22-8:ℕ) * (1 * NNRat.rawCast 120991256636412595293395 29951249940995899392)) + ((h ^ (22-9:ℕ) * (1 * NNRat.rawCast 62358839466823347069269 29951249940995899392)) + (h ^ (22-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 20611009260936251150755) 1663958330055327744)))))) + ((((h ^ (22-11:ℕ) * (1 * NNRat.rawCast 710644361937096360637 277326388342554624)) + ((h ^ (22-12:ℕ) * (1 * NNRat.rawCast 315172826303921751737 15407021574586368)) + (h ^ (22-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 150637807624708758265) 5777633090469888)))) + ((h ^ (22-14:ℕ) * (1 * NNRat.rawCast 30631781454315436439 1925877696823296)) + ((h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 253988364770939839) 35664401793024)) + (h ^ (22-16:ℕ) * (1 * NNRat.rawCast 39631726330443853 13374150672384))))) + (((h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 395143561787987) 17832200896512)) + ((h ^ (22-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1574506515896309) 2972033482752)) + (h ^ (22-19:ℕ) * (1 * NNRat.rawCast 99116094182567 495338913792)))) + ((h ^ (22-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3499390120043) 82556485632)) + ((h ^ (22-21:ℕ) * (1 * NNRat.rawCast 1063682155 254803968)) + (h ^ (22-0:ℕ) * (0)))))))

theorem boundaryCompactReVC75_4_eq {h : ℂ} (hh : h≠0) :
    h^22*boundarySlopeReVC75_4 h⁻¹=boundaryCompactReVC75_4 h := by
  rw [(boundarySlopeReVC75_4Norm h⁻¹).property]
  dsimp only [boundarySlopeReVC75_4Norm,boundaryCompactReVC75_4]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactReVC75_5 (h : ℂ) : ℂ :=
  (((((h ^ (22-0:ℕ) * (NNRat.rawCast 156940142708137 24679069470425088)) + ((h ^ (22-1:ℕ) * (1 * Rat.rawCast (Int.negOfNat 5150579091074147) 65810851921133568)) + (h ^ (22-2:ℕ) * (1 * Rat.rawCast (Int.negOfNat 808397167512059009) 3158920892214411264)))) + ((h ^ (22-3:ℕ) * (1 * NNRat.rawCast 73965071280821056117 25271367137715290112)) + ((h ^ (22-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 85126829364201859813) 67390312367240773632)) + (h ^ (22-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 57376351664537434940435) 1617367496813778567168))))) + (((h ^ (22-6:ℕ) * (1 * NNRat.rawCast 125224662746615173518425 1617367496813778567168)) + ((h ^ (22-7:ℕ) * (1 * NNRat.rawCast 206472121072036806729509 1617367496813778567168)) + (h ^ (22-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1016063989492284869895919) 1617367496813778567168)))) + ((h ^ (22-9:ℕ) * (1 * NNRat.rawCast 26788283590402750610645 134780624734481547264)) + ((h ^ (22-10:ℕ) * (1 * NNRat.rawCast 32479145122147016955665 16847578091810193408)) + (h ^ (22-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 44884578798858997377449) 22463437455746924544)))))) + ((((h ^ (22-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 33163026330405157318661) 11231718727873462272)) + ((h ^ (22-13:ℕ) * (1 * NNRat.rawCast 13698989235951035150963 1871953121312243712)) + (h ^ (22-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 171062954862404659955) 25999348907114496)))) + ((h ^ (22-15:ℕ) * (1 * NNRat.rawCast 49885731574910801809 12999674453557248)) + ((h ^ (22-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 190590726744196973) 106993205379072)) + (h ^ (22-17:ℕ) * (1 * NNRat.rawCast 33494889062154179 60183678025728))))) + (((h ^ (22-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 382742526859747) 30091839012864)) + ((h ^ (22-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 723720349910629) 13374150672384)) + (h ^ (22-20:ℕ) * (1 * NNRat.rawCast 13444892471737 743008370688)))) + ((h ^ (22-21:ℕ) * (1 * Rat.rawCast (Int.negOfNat 830159266759) 371504185344)) + ((h ^ (22-22:ℕ) * (1 * NNRat.rawCast 237639341 23219011584)) + (h ^ (22-0:ℕ) * (0)))))))

theorem boundaryCompactReVC75_5_eq {h : ℂ} (hh : h≠0) :
    h^22*boundarySlopeReVC75_5 h⁻¹=boundaryCompactReVC75_5 h := by
  rw [(boundarySlopeReVC75_5Norm h⁻¹).property]
  dsimp only [boundarySlopeReVC75_5Norm,boundaryCompactReVC75_5]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactReVC75_6 (h : ℂ) : ℂ :=
  (((((h ^ (22-0:ℕ) * (Rat.rawCast (Int.negOfNat 481627174061185) 444223250467651584)) + ((h ^ (22-1:ℕ) * (1 * NNRat.rawCast 557906639413369 98716277881700352)) + (h ^ (22-2:ℕ) * (1 * NNRat.rawCast 1219387355802268729 28430288029929701376)))) + ((h ^ (22-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 58122293236334202227) 227442304239437611008)) + ((h ^ (22-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 231315239670513525181) 909769216957750444032)) + (h ^ (22-5:ℕ) * (1 * NNRat.rawCast 51430836067057328897645 14556307471324007104512))))) + (((h ^ (22-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 281761075635426891451) 75814101413145870336)) + ((h ^ (22-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 233698320193774483288829) 14556307471324007104512)) + (h ^ (22-8:ℕ) * (1 * NNRat.rawCast 107343733308333326334655 2426051245220667850752)))) + ((h ^ (22-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 10544893741401536648471) 2426051245220667850752)) + ((h ^ (22-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 145741444199649128321281) 909769216957750444032)) + (h ^ (22-11:ℕ) * (1 * NNRat.rawCast 217283734849662393760351 909769216957750444032)))))) + ((((h ^ (22-12:ℕ) * (1 * NNRat.rawCast 57682450310238252761467 303256405652583481344)) + ((h ^ (22-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 35273132611297615146547) 37907050706572935168)) + (h ^ (22-14:ℕ) * (1 * NNRat.rawCast 4980749091225040376033 4211894522952548352)))) + ((h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 917648299010004047923) 1052973630738137088)) + ((h ^ (22-16:ℕ) * (1 * NNRat.rawCast 171166027756488223399 350991210246045696)) + (h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 25098369019341149041) 116997070082015232))))) + (((h ^ (22-18:ℕ) * (1 * NNRat.rawCast 607067186808576749 9749755840167936)) + ((h ^ (22-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1615212828003749) 203119913336832)) + (h ^ (22-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 231393718616249) 541653102231552)))) + ((h ^ (22-21:ℕ) * (1 * NNRat.rawCast 1470174938317 7522959753216)) + ((h ^ (22-22:ℕ) * (1 * Rat.rawCast (Int.negOfNat 6390601583) 3761479876608)) + (h ^ (22-0:ℕ) * (0)))))))

theorem boundaryCompactReVC75_6_eq {h : ℂ} (hh : h≠0) :
    h^22*boundarySlopeReVC75_6 h⁻¹=boundaryCompactReVC75_6 h := by
  rw [(boundarySlopeReVC75_6Norm h⁻¹).property]
  dsimp only [boundarySlopeReVC75_6Norm,boundaryCompactReVC75_6]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactReVC75_7 (h : ℂ) : ℂ :=
  (((((h ^ (22-0:ℕ) * (NNRat.rawCast 81230749376785 999502313552216064)) + ((h ^ (22-1:ℕ) * (1 * Rat.rawCast (Int.negOfNat 496737052078147) 7996018508417728512)) + (h ^ (22-2:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1195112806016720977) 255872592269367312384)))) + ((h ^ (22-3:ℕ) * (1 * NNRat.rawCast 24762701480477393177 2046980738154938499072)) + ((h ^ (22-4:ℕ) * (1 * NNRat.rawCast 313842574109956854443 4093961476309876998144)) + (h ^ (22-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1129103945050697019451) 3639076867831001776128))))) + (((h ^ (22-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 13807642091898483940871) 43668922413972021313536)) + ((h ^ (22-7:ℕ) * (1 * NNRat.rawCast 185742948129001140193165 65503383620958031970304)) + (h ^ (22-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 287923889288486821105085) 131006767241916063940608)))) + ((h ^ (22-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 93342218685735778372457) 10917230603493005328384)) + ((h ^ (22-10:ℕ) * (1 * NNRat.rawCast 304167568125043871031755 16375845905239507992576)) + (h ^ (22-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 158415410897264082940625) 16375845905239507992576)))))) + ((((h ^ (22-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 148836131214605550856559) 8187922952619753996288)) + ((h ^ (22-13:ℕ) * (1 * NNRat.rawCast 39768630018302239350229 682326912718312833024)) + (h ^ (22-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 4981256759504263998289) 56860576059859402752)))) + ((h ^ (22-15:ℕ) * (1 * NNRat.rawCast 4515688081356966679595 56860576059859402752)) + ((h ^ (22-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2906552668529720416055) 56860576059859402752)) + (h ^ (22-17:ℕ) * (1 * NNRat.rawCast 43089469661531776945 1579460446107205632))))) + (((h ^ (22-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2986895310826234465) 263243407684534272)) + ((h ^ (22-19:ℕ) * (1 * NNRat.rawCast 850454224292735941 263243407684534272)) + (h ^ (22-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 7967989674815663) 14624633760251904)))) + ((h ^ (22-21:ℕ) * (1 * NNRat.rawCast 51748298396375 1218719480020992)) + ((h ^ (22-22:ℕ) * (1 * Rat.rawCast (Int.negOfNat 146122178851) 152339935002624)) + (h ^ (22-0:ℕ) * (0)))))))

theorem boundaryCompactReVC75_7_eq {h : ℂ} (hh : h≠0) :
    h^22*boundarySlopeReVC75_7 h⁻¹=boundaryCompactReVC75_7 h := by
  rw [(boundarySlopeReVC75_7Norm h⁻¹).property]
  dsimp only [boundarySlopeReVC75_7Norm,boundaryCompactReVC75_7]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactReVC75_8 (h : ℂ) : ℂ :=
  (((((h ^ (22-0:ℕ) * (Rat.rawCast (Int.negOfNat 215184678307973) 71964166575759556608)) + ((h ^ (22-1:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1724993331041965) 71964166575759556608)) + (h ^ (22-2:ℕ) * (1 * NNRat.rawCast 269967154765347329 767617776808101937152)))) + ((h ^ (22-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1162115703515777765) 6140942214464815497216)) + ((h ^ (22-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1217569843162022658095) 147382613147155571933184)) + (h ^ (22-5:ℕ) * (1 * NNRat.rawCast 2287292812882742527355 98255075431437047955456))))) + (((h ^ (22-6:ℕ) * (1 * NNRat.rawCast 441846406193946970051 9211413321697223245824)) + ((h ^ (22-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 87804898030082716376593) 294765226294311143866368)) + (h ^ (22-8:ℕ) * (1 * NNRat.rawCast 22179299769693391051463 98255075431437047955456)))) + ((h ^ (22-9:ℕ) * (1 * NNRat.rawCast 301421433559311819865325 294765226294311143866368)) + ((h ^ (22-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 331499366305689418554149) 147382613147155571933184)) + (h ^ (22-11:ℕ) * (1 * NNRat.rawCast 113344674946822636143241 147382613147155571933184)))))) + ((((h ^ (22-12:ℕ) * (1 * NNRat.rawCast 34705095933069585653809 18422826643394446491648)) + ((h ^ (22-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 16606306217037983949313) 9211413321697223245824)) + (h ^ (22-14:ℕ) * (1 * NNRat.rawCast 1545855966180359988673 9211413321697223245824)))) + ((h ^ (22-15:ℕ) * (1 * NNRat.rawCast 180593255494178709653 383808888404050968576)) + ((h ^ (22-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 360790148552129508947) 767617776808101937152)) + (h ^ (22-17:ℕ) * (1 * NNRat.rawCast 222675550817164993 999502313552216064))))) + (((h ^ (22-18:ℕ) * (1 * NNRat.rawCast 578136324146852569 10661358011223638016)) + ((h ^ (22-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 217078033682838691) 2369190669160808448)) + (h ^ (22-20:ℕ) * (1 * NNRat.rawCast 20096918107407283 592297667290202112)))) + ((h ^ (22-21:ℕ) * (1 * Rat.rawCast (Int.negOfNat 369218454545003) 98716277881700352)) + ((h ^ (22-22:ℕ) * (1 * Rat.rawCast (Int.negOfNat 462236958017) 8226356490141696)) + (h ^ (22-0:ℕ) * (0)))))))

theorem boundaryCompactReVC75_8_eq {h : ℂ} (hh : h≠0) :
    h^22*boundarySlopeReVC75_8 h⁻¹=boundaryCompactReVC75_8 h := by
  rw [(boundarySlopeReVC75_8Norm h⁻¹).property]
  dsimp only [boundarySlopeReVC75_8Norm,boundaryCompactReVC75_8]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactReVC75_9 (h : ℂ) : ℂ :=
  (((((h ^ (22-0:ℕ) * (NNRat.rawCast 3583883340325 80959687397729501184)) + ((h ^ (22-1:ℕ) * (1 * NNRat.rawCast 2230642890041647 1295354998363672018944)) + (h ^ (22-2:ℕ) * (1 * Rat.rawCast (Int.negOfNat 310204600881843443) 20725679973818752303104)))) + ((h ^ (22-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 549139232604042251) 55268479930183339474944)) + ((h ^ (22-4:ℕ) * (1 * NNRat.rawCast 89306678582029681073 221073919720733357899776)) + (h ^ (22-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 5160698425928265416837) 5305774073297600589594624))))) + (((h ^ (22-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 12371300642096435429515) 5305774073297600589594624)) + ((h ^ (22-7:ℕ) * (1 * NNRat.rawCast 73277382533984112347327 5305774073297600589594624)) + (h ^ (22-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 71932924127465264777429) 5305774073297600589594624)))) + ((h ^ (22-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3412479099071539444645) 82902719895275009212416)) + ((h ^ (22-10:ℕ) * (1 * NNRat.rawCast 101473495072202368216489 884295678882933431599104)) + (h ^ (22-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 21420596387907027650563) 331610879581100036849664)))))) + ((((h ^ (22-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 23017327816305596756789) 331610879581100036849664)) + ((h ^ (22-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 8469310340657753919685) 331610879581100036849664)) + (h ^ (22-14:ℕ) * (1 * NNRat.rawCast 30434543818219388941837 82902719895275009212416)))) + ((h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 5871337127094591358921) 10362839986909376151552)) + ((h ^ (22-16:ℕ) * (1 * NNRat.rawCast 3353900685787599339853 6908559991272917434368)) + (h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1027008814990190065373) 3454279995636458717184))))) + (((h ^ (22-18:ℕ) * (1 * NNRat.rawCast 152159557915890669563 1151426665212152905728)) + ((h ^ (22-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 225651476856301229) 5997013881313296384)) + (h ^ (22-20:ℕ) * (1 * NNRat.rawCast 96039540769832831 15992037016835457024)))) + ((h ^ (22-21:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2540983306797479) 5330679005611819008)) + ((h ^ (22-22:ℕ) * (1 * NNRat.rawCast 3484089980375 111055812616912896)) + (h ^ (22-0:ℕ) * (0)))))))

theorem boundaryCompactReVC75_9_eq {h : ℂ} (hh : h≠0) :
    h^22*boundarySlopeReVC75_9 h⁻¹=boundaryCompactReVC75_9 h := by
  rw [(boundarySlopeReVC75_9Norm h⁻¹).property]
  dsimp only [boundarySlopeReVC75_9Norm,boundaryCompactReVC75_9]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactReVC75_10 (h : ℂ) : ℂ :=
  (((((h ^ (22-1:ℕ) * (1 * Rat.rawCast (Int.negOfNat 219554668799417) 5829097492636524085248)) + (h ^ (22-2:ℕ) * (1 * NNRat.rawCast 12130058470804363 62177039921456256909312))) + ((h ^ (22-3:ℕ) * (1 * NNRat.rawCast 1568068473089652007 1492248958114950165823488)) + ((h ^ (22-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 47621265901752686737) 5968995832459800663293952)) + (h ^ (22-5:ℕ) * (1 * NNRat.rawCast 30307738044516609971 47751966659678405306351616))))) + (((h ^ (22-6:ℕ) * (1 * NNRat.rawCast 137718802375168940327 1492248958114950165823488)) + ((h ^ (22-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 8226262614482804328827) 47751966659678405306351616)) + (h ^ (22-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2194088939615026270777) 7958661109946400884391936)))) + ((h ^ (22-9:ℕ) * (1 * NNRat.rawCast 28720732444219307679151 23875983329839202653175808)) + ((h ^ (22-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 173821314463967610587) 221073919720733357899776)) + (h ^ (22-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 7364025302116830422221) 2984497916229900331646976)))))) + ((((h ^ (22-12:ℕ) * (1 * NNRat.rawCast 15913194802104545222659 2984497916229900331646976)) + ((h ^ (22-13:ℕ) * (1 * NNRat.rawCast 388050210858173238445 746124479057475082911744)) + (h ^ (22-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1625256668537592527107) 93265559882184385363968)))) + ((h ^ (22-15:ℕ) * (1 * NNRat.rawCast 5922961490081569048043 186531119764368770727936)) + ((h ^ (22-16:ℕ) * (1 * Rat.rawCast (Int.negOfNat 721749056167545670429) 23316389970546096340992)) + (h ^ (22-17:ℕ) * (1 * NNRat.rawCast 209943755440339635623 10362839986909376151552))))) + (((h ^ (22-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 8412143827697953753) 863569998909114679296)) + ((h ^ (22-19:ℕ) * (1 * NNRat.rawCast 1391085708731893169 431784999454557339648)) + (h ^ (22-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 27862005220957595) 47976111050506371072)))) + ((h ^ (22-21:ℕ) * (1 * NNRat.rawCast 51618736230307 1999004627104432128)) + ((h ^ (22-22:ℕ) * (1 * NNRat.rawCast 4346286687145 999502313552216064)) + (h ^ (22-0:ℕ) * (0)))))))

theorem boundaryCompactReVC75_10_eq {h : ℂ} (hh : h≠0) :
    h^22*boundarySlopeReVC75_10 h⁻¹=boundaryCompactReVC75_10 h := by
  rw [(boundarySlopeReVC75_10Norm h⁻¹).property]
  dsimp only [boundarySlopeReVC75_10Norm,boundaryCompactReVC75_10]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactReVC75_11 (h : ℂ) : ℂ :=
  (((((h ^ (22-2:ℕ) * (1 * NNRat.rawCast 2092690629306389 559593359293106312183808)) + (h ^ (22-3:ℕ) * (1 * Rat.rawCast (Int.negOfNat 195696744640400479) 4476746874344850497470464))) + ((h ^ (22-4:ℕ) * (1 * NNRat.rawCast 463758260460286567 6715120311517275746205696)) + ((h ^ (22-5:ℕ) * (1 * NNRat.rawCast 197027590222479495187 214883849968552823878582272)) + (h ^ (22-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1686110171985694647533) 429767699937105647757164544))))) + (((h ^ (22-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 274850889402850673191) 214883849968552823878582272)) + ((h ^ (22-8:ℕ) * (1 * NNRat.rawCast 15663352326677126150243 429767699937105647757164544)) + (h ^ (22-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 530562256287476278741) 7958661109946400884391936)))) + ((h ^ (22-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 284809855741897658651) 8953493748689700994940928)) + ((h ^ (22-11:ℕ) * (1 * NNRat.rawCast 2431146124146807267779 8953493748689700994940928)) + (h ^ (22-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 12096348797041315544957) 26860481246069102984822784)))))) + ((((h ^ (22-13:ℕ) * (1 * NNRat.rawCast 31145032053012378161 69949169911638289022976)) + (h ^ (22-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 991483469309568904681) 3357560155758637873102848))) + ((h ^ (22-15:ℕ) * (1 * NNRat.rawCast 44743664677374445597 839390038939659468275712)) + ((h ^ (22-16:ℕ) * (1 * NNRat.rawCast 75898718405562616109 559593359293106312183808)) + (h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 5090260560777314953) 31088519960728128454656))))) + (((h ^ (22-18:ℕ) * (1 * NNRat.rawCast 840239744932859063 7772129990182032113664)) + ((h ^ (22-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 67366298761168637) 1295354998363672018944)) + (h ^ (22-20:ℕ) * (1 * NNRat.rawCast 750761698285889 47976111050506371072)))) + ((h ^ (22-21:ℕ) * (1 * Rat.rawCast (Int.negOfNat 62061492234979) 35982083287879778304)) + ((h ^ (22-22:ℕ) * (1 * Rat.rawCast (Int.negOfNat 278045141603) 1499253470328324096)) + (h ^ (22-0:ℕ) * (0)))))))

theorem boundaryCompactReVC75_11_eq {h : ℂ} (hh : h≠0) :
    h^22*boundarySlopeReVC75_11 h⁻¹=boundaryCompactReVC75_11 h := by
  rw [(boundarySlopeReVC75_11Norm h⁻¹).property]
  dsimp only [boundarySlopeReVC75_11Norm,boundaryCompactReVC75_11]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactReVC75_12 (h : ℂ) : ℂ :=
  (((((h ^ (22-3:ℕ) * (1 * NNRat.rawCast 13750076961227201 40290721869103654477234176)) + (h ^ (22-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2272675605429860617) 1933954649716975414907240448))) + ((h ^ (22-5:ℕ) * (1 * Rat.rawCast (Int.negOfNat 5039774240878068055) 644651549905658471635746816)) + ((h ^ (22-6:ℕ) * (1 * NNRat.rawCast 18566124275462682571 483488662429243853726810112)) + (h ^ (22-7:ℕ) * (1 * NNRat.rawCast 26776111773646803391 1933954649716975414907240448))))) + (((h ^ (22-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1304097701503479099571) 3867909299433950829814480896)) + (h ^ (22-9:ℕ) * (1 * NNRat.rawCast 2120623462217466563867 3867909299433950829814480896))) + ((h ^ (22-10:ℕ) * (1 * NNRat.rawCast 78606866482981670647 214883849968552823878582272)) + ((h ^ (22-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 618220385259497250371) 322325774952829235817873408)) + (h ^ (22-12:ℕ) * (1 * NNRat.rawCast 1046849667960175476809 483488662429243853726810112)))))) + ((((h ^ (22-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 71698112184124150135) 20145360934551827238617088)) + (h ^ (22-14:ℕ) * (1 * NNRat.rawCast 228960159330259212487 20145360934551827238617088))) + ((h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 71472793920992688065) 3357560155758637873102848)) + ((h ^ (22-16:ℕ) * (1 * NNRat.rawCast 6468702351852070967 279796679646553156091904)) + (h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3038075452299828817) 186531119764368770727936))))) + (((h ^ (22-18:ℕ) * (1 * NNRat.rawCast 241831928414606501 31088519960728128454656)) + ((h ^ (22-19:ℕ) * (1 * Rat.rawCast (Int.negOfNat 11415856074045205) 5181419993454688075776)) + (h ^ (22-20:ℕ) * (1 * NNRat.rawCast 72967459076987 863569998909114679296)))) + ((h ^ (22-21:ℕ) * (1 * NNRat.rawCast 11559301569253 71964166575759556608)) + ((h ^ (22-22:ℕ) * (1 * Rat.rawCast (Int.negOfNat 116284680869) 2998506940656648192)) + (h ^ (22-0:ℕ) * (0)))))))

theorem boundaryCompactReVC75_12_eq {h : ℂ} (hh : h≠0) :
    h^22*boundarySlopeReVC75_12 h⁻¹=boundaryCompactReVC75_12 h := by
  rw [(boundarySlopeReVC75_12Norm h⁻¹).property]
  dsimp only [boundarySlopeReVC75_12Norm,boundaryCompactReVC75_12]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactReVC75_13 (h : ℂ) : ℂ :=
  (((((h ^ (22-4:ℕ) * (1 * Rat.rawCast (Int.negOfNat 293575300609695167) 8702795923726389367082582016)) + (h ^ (22-5:ℕ) * (1 * NNRat.rawCast 8348206677096029765 69622367389811114936660656128))) + ((h ^ (22-6:ℕ) * (1 * NNRat.rawCast 44936924283632287949 69622367389811114936660656128)) + ((h ^ (22-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 231947510939720780939) 69622367389811114936660656128)) + (h ^ (22-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 24492496571545759715) 69622367389811114936660656128))))) + (((h ^ (22-9:ℕ) * (1 * NNRat.rawCast 445549157507532871811 17405591847452778734165164032)) + (h ^ (22-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 137281532535594258137) 2900931974575463122360860672))) + ((h ^ (22-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 23136298541254051547) 2900931974575463122360860672)) + ((h ^ (22-12:ℕ) * (1 * NNRat.rawCast 228223513353820054213 1450465987287731561180430336)) + (h ^ (22-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 694079110520357887337) 2175698980931597341770645504)))))) + ((((h ^ (22-14:ℕ) * (1 * NNRat.rawCast 6074204053222347575 15109020700913870428962816)) + (h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1835568962721740285) 5036340233637956809654272))) + ((h ^ (22-16:ℕ) * (1 * NNRat.rawCast 29034035389673845 124354079842912513818624)) + ((h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 12953531278545725) 139898339823276578045952)) + (h ^ (22-18:ℕ) * (1 * NNRat.rawCast 210883010884061 46632779941092192681984))))) + (((h ^ (22-19:ℕ) * (1 * NNRat.rawCast 390881856585281 15544259980364064227328)) + (h ^ (22-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 52274983049483) 2590709996727344037888))) + ((h ^ (22-21:ℕ) * (1 * NNRat.rawCast 3259747474309 431784999454557339648)) + ((h ^ (22-22:ℕ) * (1 * Rat.rawCast (Int.negOfNat 31501017683) 26986562465909833728)) + (h ^ (22-0:ℕ) * (0)))))))

theorem boundaryCompactReVC75_13_eq {h : ℂ} (hh : h≠0) :
    h^22*boundarySlopeReVC75_13 h⁻¹=boundaryCompactReVC75_13 h := by
  rw [(boundarySlopeReVC75_13Norm h⁻¹).property]
  dsimp only [boundarySlopeReVC75_13Norm,boundaryCompactReVC75_13]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactReVC75_14 (h : ℂ) : ℂ :=
  (((((h ^ (22-5:ℕ) * (1 * NNRat.rawCast 405506432602597781 626601306508300034429945905152)) + (h ^ (22-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 21101830690497529) 19581290828384376075935809536))) + ((h ^ (22-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 8209422637318359989) 626601306508300034429945905152)) + (h ^ (22-8:ℕ) * (1 * NNRat.rawCast 11310413425473433145 313300653254150017214972952576)))) + (((h ^ (22-9:ℕ) * (1 * NNRat.rawCast 17353859589311349559 313300653254150017214972952576)) + (h ^ (22-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 14810488993092655) 45327062102741611286888448))) + ((h ^ (22-11:ℕ) * (1 * NNRat.rawCast 4516372364942935217 13054193885589584050623873024)) + ((h ^ (22-12:ℕ) * (1 * NNRat.rawCast 6578963650269116407 13054193885589584050623873024)) + (h ^ (22-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1061782103192386915) 543924745232899335442661376)))))) + ((((h ^ (22-14:ℕ) * (1 * NNRat.rawCast 56585322924564629 20145360934551827238617088)) + (h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 11858614216838335) 5036340233637956809654272))) + ((h ^ (22-16:ℕ) * (1 * NNRat.rawCast 1882041096446303 1678780077879318936551424)) + ((h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 4049378169677) 62177039921456256909312)) + (h ^ (22-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 19107514648465) 46632779941092192681984))))) + (((h ^ (22-19:ℕ) * (1 * NNRat.rawCast 831670544725 1943032497545508028416)) + (h ^ (22-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 639614828653) 2590709996727344037888))) + ((h ^ (22-21:ℕ) * (1 * NNRat.rawCast 26178089645 323838749590918004736)) + ((h ^ (22-22:ℕ) * (1 * Rat.rawCast (Int.negOfNat 620897345) 53973124931819667456)) + (h ^ (22-0:ℕ) * (0)))))))

theorem boundaryCompactReVC75_14_eq {h : ℂ} (hh : h≠0) :
    h^22*boundarySlopeReVC75_14 h⁻¹=boundaryCompactReVC75_14 h := by
  rw [(boundarySlopeReVC75_14Norm h⁻¹).property]
  dsimp only [boundarySlopeReVC75_14Norm,boundaryCompactReVC75_14]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactReVC75_15 (h : ℂ) : ℂ :=
  (((((h ^ (22-6:ℕ) * (1 * Rat.rawCast (Int.negOfNat 18285856292474113) 5639411758574700309869513146368)) + (h ^ (22-7:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1511966328663049) 2819705879287350154934756573184))) + ((h ^ (22-8:ℕ) * (1 * NNRat.rawCast 339871085508091991 5639411758574700309869513146368)) + (h ^ (22-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 33453624729784819) 469950979881225025822459428864)))) + (((h ^ (22-10:ℕ) * (1 * Rat.rawCast (Int.negOfNat 81733900791335149) 234975489940612512911229714432)) + (h ^ (22-11:ℕ) * (1 * NNRat.rawCast 74320809587825143 78325163313537504303743238144))) + ((h ^ (22-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2806193702380529) 13054193885589584050623873024)) + ((h ^ (22-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 912627572016575) 362616496821932890295107584)) + (h ^ (22-14:ℕ) * (1 * NNRat.rawCast 153363552041435 30218041401827740857925632)))))) + ((((h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 50511907346555) 10072680467275913619308544)) + (h ^ (22-16:ℕ) * (1 * NNRat.rawCast 9321260092597 3357560155758637873102848))) + ((h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 98888408879) 279796679646553156091904)) + (h ^ (22-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 17206671299) 15544259980364064227328)))) + (((h ^ (22-19:ℕ) * (1 * NNRat.rawCast 64740079991 46632779941092192681984)) + (h ^ (22-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 6749363443) 7772129990182032113664))) + ((h ^ (22-21:ℕ) * (1 * NNRat.rawCast 187667839 647677499181836009472)) + ((h ^ (22-22:ℕ) * (1 * Rat.rawCast (Int.negOfNat 121577) 2998506940656648192)) + (h ^ (22-0:ℕ) * (0)))))))

theorem boundaryCompactReVC75_15_eq {h : ℂ} (hh : h≠0) :
    h^22*boundarySlopeReVC75_15 h⁻¹=boundaryCompactReVC75_15 h := by
  rw [(boundarySlopeReVC75_15Norm h⁻¹).property]
  dsimp only [boundarySlopeReVC75_15Norm,boundaryCompactReVC75_15]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactReVC75_16 (h : ℂ) : ℂ :=
  (((((h ^ (22-7:ℕ) * (1 * NNRat.rawCast 168937493305 49565142409347951942212517888)) + (h ^ (22-8:ℕ) * (1 * NNRat.rawCast 8265944738779 1586084557099134462150800572416))) + ((h ^ (22-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 342464455864405) 6344338228396537848603202289664)) + (h ^ (22-10:ℕ) * (1 * NNRat.rawCast 855060108259 1057389704732756308100533714944)))) + (((h ^ (22-11:ℕ) * (1 * NNRat.rawCast 78978986476313 234975489940612512911229714432)) + (h ^ (22-12:ℕ) * (1 * Rat.rawCast (Int.negOfNat 28241139865477) 58743872485153128227807428608))) + ((h ^ (22-13:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1566533457391) 4895322707096094018983952384)) + (h ^ (22-14:ℕ) * (1 * NNRat.rawCast 103476255715 60436082803655481715851264))))) + ((((h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 119579308637) 45327062102741611286888448)) + (h ^ (22-16:ℕ) * (1 * NNRat.rawCast 38588663779 15109020700913870428962816))) + ((h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 3402513433) 2518170116818978404827136)) + (h ^ (22-18:ℕ) * (1 * Rat.rawCast (Int.negOfNat 454484377) 1259085058409489202413568)))) + (((h ^ (22-19:ℕ) * (1 * NNRat.rawCast 527387345 419695019469829734137856)) + (h ^ (22-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 1383029) 1457274373159131021312))) + ((h ^ (22-21:ℕ) * (1 * NNRat.rawCast 1935091 5829097492636524085248)) + ((h ^ (22-22:ℕ) * (1 * Rat.rawCast (Int.negOfNat 22445) 485758124386377007104)) + (h ^ (22-0:ℕ) * (0)))))))

theorem boundaryCompactReVC75_16_eq {h : ℂ} (hh : h≠0) :
    h^22*boundarySlopeReVC75_16 h⁻¹=boundaryCompactReVC75_16 h := by
  rw [(boundarySlopeReVC75_16Norm h⁻¹).property]
  dsimp only [boundarySlopeReVC75_16Norm,boundaryCompactReVC75_16]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactReVC75_17 (h : ℂ) : ℂ :=
  (((((h ^ (22-8:ℕ) * (1 * Rat.rawCast (Int.negOfNat 14325530485) 114198088111137681274857641213952)) + (h ^ (22-9:ℕ) * (1 * Rat.rawCast (Int.negOfNat 2426981221) 57099044055568840637428820606976))) + ((h ^ (22-10:ℕ) * (1 * NNRat.rawCast 26945503417 38066029370379227091619213737984)) + (h ^ (22-11:ℕ) * (1 * Rat.rawCast (Int.negOfNat 7534594907) 1057389704732756308100533714944)))) + (((h ^ (22-12:ℕ) * (1 * NNRat.rawCast 758012507 132173713091594538512566714368)) + (h ^ (22-13:ℕ) * (1 * NNRat.rawCast 11700680453 176231617455459384683422285824))) + ((h ^ (22-14:ℕ) * (1 * Rat.rawCast (Int.negOfNat 72277303) 543924745232899335442661376)) + (h ^ (22-15:ℕ) * (1 * Rat.rawCast (Int.negOfNat 18989215) 203971779462337250790998016))))) + ((((h ^ (22-16:ℕ) * (1 * NNRat.rawCast 4489513 8498824144264052116291584)) + (h ^ (22-17:ℕ) * (1 * Rat.rawCast (Int.negOfNat 13254793) 22663531051370805643444224))) + ((h ^ (22-18:ℕ) * (1 * NNRat.rawCast 3202801 22663531051370805643444224)) + (h ^ (22-19:ℕ) * (1 * NNRat.rawCast 434041 1888627587614233803620352)))) + (((h ^ (22-20:ℕ) * (1 * Rat.rawCast (Int.negOfNat 11819) 52461877433728716767232)) + (h ^ (22-21:ℕ) * (1 * NNRat.rawCast 8669 104923754867457433534464))) + ((h ^ (22-22:ℕ) * (1 * Rat.rawCast (Int.negOfNat 25) 2185911559738696531968)) + (h ^ (22-0:ℕ) * (0))))))

theorem boundaryCompactReVC75_17_eq {h : ℂ} (hh : h≠0) :
    h^22*boundarySlopeReVC75_17 h⁻¹=boundaryCompactReVC75_17 h := by
  rw [(boundarySlopeReVC75_17Norm h⁻¹).property]
  dsimp only [boundarySlopeReVC75_17Norm,boundaryCompactReVC75_17]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

def boundaryCompactReVC75_18 (h : ℂ) : ℂ :=
  (h ^ (22-0:ℕ) * (0))

theorem boundaryCompactReVC75_18_eq {h : ℂ} (hh : h≠0) :
    h^22*boundarySlopeReVC75_18 h⁻¹=boundaryCompactReVC75_18 h := by
  rw [(boundarySlopeReVC75_18Norm h⁻¹).property]
  dsimp only [boundarySlopeReVC75_18Norm,boundaryCompactReVC75_18]
  all_goals norm_num
  all_goals field_simp [hh]
  all_goals ring

end
end HTGeometry.ThetaRatioInfinity
