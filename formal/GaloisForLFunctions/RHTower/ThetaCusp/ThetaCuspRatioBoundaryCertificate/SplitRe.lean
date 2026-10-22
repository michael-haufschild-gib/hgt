import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.ClockRe

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

def boundaryReLowColumn76_0 (h r : ℂ) : ℂ :=
  0

def boundaryReHighColumn76_0 (h r : ℂ) : ℂ :=
  ((((h^((22-0)+2*0-6:ℕ)*r^0*(Rat.rawCast (Int.negOfNat 230981303) 816293376)) + (h^((22-0)+2*1-6:ℕ)*r^1*(Rat.rawCast (Int.negOfNat 14198581679) 58773123072))) + ((h^((22-0)+2*2-6:ℕ)*r^2*(NNRat.rawCast 1259320357 44079842304)) + ((h^((22-0)+2*3-6:ℕ)*r^3*(NNRat.rawCast 343884160085 12694994583552)) + (h^((22-0)+2*4-6:ℕ)*r^4*(NNRat.rawCast 3398669372467 10968475320188928))))) + (((h^((22-0)+2*5-6:ℕ)*r^5*(Rat.rawCast (Int.negOfNat 2383866633305) 4113178245070848)) + (h^((22-0)+2*6-6:ℕ)*r^6*(Rat.rawCast (Int.negOfNat 15566885473627) 444223250467651584))) + ((h^((22-0)+2*7-6:ℕ)*r^7*(NNRat.rawCast 77095760617 15617223649253376)) + ((h^((22-0)+2*8-6:ℕ)*r^8*(NNRat.rawCast 42854922195427 71964166575759556608)) + (h^((22-0)+2*9-6:ℕ)*r^9*(Rat.rawCast (Int.negOfNat 3583883340325) 80959687397729501184))))))

theorem boundaryReClock76_0_split (h r : ℂ) :

    h^(22-0:ℕ)*boundaryReClock76_0 (r*h^2)=boundaryReLowColumn76_0 h r+h^6*boundaryReHighColumn76_0 h r := by

  rw [(boundaryReClock76_0Norm (r*h^2)).property]

  change h^(22-0:ℕ)*(Rat.rawCast (Int.negOfNat 230981303) 816293376 +
      ((r*h^2) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 14198581679) 58773123072 +
        ((r*h^2) ^ Nat.rawCast 2 * NNRat.rawCast 1259320357 44079842304 +
          ((r*h^2) ^ Nat.rawCast 3 * NNRat.rawCast 343884160085 12694994583552 +
            ((r*h^2) ^ Nat.rawCast 4 * NNRat.rawCast 3398669372467 10968475320188928 +
              ((r*h^2) ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 2383866633305) 4113178245070848 +
                ((r*h^2) ^ Nat.rawCast 6 * Rat.rawCast (Int.negOfNat 15566885473627) 444223250467651584 +
                  ((r*h^2) ^ Nat.rawCast 7 * NNRat.rawCast 77095760617 15617223649253376 +
                    ((r*h^2) ^ Nat.rawCast 8 * NNRat.rawCast 42854922195427 71964166575759556608 +
                      ((r*h^2) ^ Nat.rawCast 9 * Rat.rawCast (Int.negOfNat 3583883340325) 80959687397729501184 + 0))))))))))=_

  dsimp only [boundaryReLowColumn76_0,boundaryReHighColumn76_0]

  norm_num

  ring <;> simp


def boundaryReLowColumn76_1 (h r : ℂ) : ℂ :=
  0

def boundaryReHighColumn76_1 (h r : ℂ) : ℂ :=
  ((((h^((22-1)+2*0-6:ℕ)*r^0*(Rat.rawCast (Int.negOfNat 324249763) 45349632)) + (h^((22-1)+2*1-6:ℕ)*r^1*(Rat.rawCast (Int.negOfNat 167201743973) 58773123072))) + ((h^((22-1)+2*2-6:ℕ)*r^2*(NNRat.rawCast 6187558971961 4231664861184)) + ((h^((22-1)+2*3-6:ℕ)*r^3*(NNRat.rawCast 7863700323469 25389989167104)) + (h^((22-1)+2*4-6:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 116766132507617) 2437438960041984))))) + (((h^((22-1)+2*5-6:ℕ)*r^5*(Rat.rawCast (Int.negOfNat 1145421589780511) 197432555763400704)) + ((h^((22-1)+2*6-6:ℕ)*r^6*(NNRat.rawCast 206177013717469 222111625233825792)) + (h^((22-1)+2*7-6:ℕ)*r^7*(NNRat.rawCast 54630215066029 888446500935303168)))) + ((h^((22-1)+2*8-6:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 3134120843656637) 143928333151519113216)) + ((h^((22-1)+2*9-6:ℕ)*r^9*(NNRat.rawCast 240050053994077 143928333151519113216)) + (h^((22-1)+2*10-6:ℕ)*r^10*(Rat.rawCast (Int.negOfNat 219554668799417) 5829097492636524085248))))))

theorem boundaryReClock76_1_split (h r : ℂ) :

    h^(22-1:ℕ)*boundaryReClock76_1 (r*h^2)=boundaryReLowColumn76_1 h r+h^6*boundaryReHighColumn76_1 h r := by

  rw [(boundaryReClock76_1Norm (r*h^2)).property]

  change h^(22-1:ℕ)*(Rat.rawCast (Int.negOfNat 324249763) 45349632 +
      ((r*h^2) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 167201743973) 58773123072 +
        ((r*h^2) ^ Nat.rawCast 2 * NNRat.rawCast 6187558971961 4231664861184 +
          ((r*h^2) ^ Nat.rawCast 3 * NNRat.rawCast 7863700323469 25389989167104 +
            ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 116766132507617) 2437438960041984 +
              ((r*h^2) ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 1145421589780511) 197432555763400704 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 206177013717469 222111625233825792 +
                  ((r*h^2) ^ Nat.rawCast 7 * NNRat.rawCast 54630215066029 888446500935303168 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 3134120843656637) 143928333151519113216 +
                      ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 240050053994077 143928333151519113216 +
                        ((r*h^2) ^ Nat.rawCast 10 * Rat.rawCast (Int.negOfNat 219554668799417) 5829097492636524085248 +
                          0)))))))))))=_

  dsimp only [boundaryReLowColumn76_1,boundaryReHighColumn76_1]

  norm_num

  ring <;> simp


def boundaryReLowColumn76_2 (h r : ℂ) : ℂ :=
  0

def boundaryReHighColumn76_2 (h r : ℂ) : ℂ :=
  ((((h^((22-2)+2*0-6:ℕ)*r^0*(Rat.rawCast (Int.negOfNat 17013304387) 272097792)) + ((h^((22-2)+2*1-6:ℕ)*r^1*(NNRat.rawCast 38431147015 7346640384)) + (h^((22-2)+2*2-6:ℕ)*r^2*(NNRat.rawCast 61220920127935 4231664861184)))) + ((h^((22-2)+2*3-6:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 276330887018353) 304679870005248)) + ((h^((22-2)+2*4-6:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 1905102852670427) 5484237660094464)) + (h^((22-2)+2*5-6:ℕ)*r^5*(NNRat.rawCast 62486563359189029 789730223053602816))))) + (((h^((22-2)+2*6-6:ℕ)*r^6*(NNRat.rawCast 892127151386231 1579460446107205632)) + ((h^((22-2)+2*7-6:ℕ)*r^7*(Rat.rawCast (Int.negOfNat 555318049108146761) 255872592269367312384)) + (h^((22-2)+2*8-6:ℕ)*r^8*(NNRat.rawCast 7203123035673985 23988055525253185536)))) + ((h^((22-2)+2*9-6:ℕ)*r^9*(Rat.rawCast (Int.negOfNat 12468472096182551) 647677499181836009472)) + ((h^((22-2)+2*10-6:ℕ)*r^10*(NNRat.rawCast 17574827696587321 31088519960728128454656)) + (h^((22-2)+2*11-6:ℕ)*r^11*(Rat.rawCast (Int.negOfNat 2092690629306389) 559593359293106312183808))))))

theorem boundaryReClock76_2_split (h r : ℂ) :

    h^(22-2:ℕ)*boundaryReClock76_2 (r*h^2)=boundaryReLowColumn76_2 h r+h^6*boundaryReHighColumn76_2 h r := by

  rw [(boundaryReClock76_2Norm (r*h^2)).property]

  change h^(22-2:ℕ)*(Rat.rawCast (Int.negOfNat 17013304387) 272097792 +
      ((r*h^2) ^ Nat.rawCast 1 * NNRat.rawCast 38431147015 7346640384 +
        ((r*h^2) ^ Nat.rawCast 2 * NNRat.rawCast 61220920127935 4231664861184 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 276330887018353) 304679870005248 +
            ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 1905102852670427) 5484237660094464 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 62486563359189029 789730223053602816 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 892127151386231 1579460446107205632 +
                  ((r*h^2) ^ Nat.rawCast 7 * Rat.rawCast (Int.negOfNat 555318049108146761) 255872592269367312384 +
                    ((r*h^2) ^ Nat.rawCast 8 * NNRat.rawCast 7203123035673985 23988055525253185536 +
                      ((r*h^2) ^ Nat.rawCast 9 * Rat.rawCast (Int.negOfNat 12468472096182551) 647677499181836009472 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 17574827696587321 31088519960728128454656 +
                          ((r*h^2) ^ Nat.rawCast 11 * Rat.rawCast (Int.negOfNat 2092690629306389) 559593359293106312183808 +
                            0))))))))))))=_

  dsimp only [boundaryReLowColumn76_2,boundaryReHighColumn76_2]

  norm_num

  ring <;> simp


def boundaryReLowColumn76_3 (h r : ℂ) : ℂ :=
  0

def boundaryReHighColumn76_3 (h r : ℂ) : ℂ :=
  ((((h^((22-3)+2*0-6:ℕ)*r^0*(Rat.rawCast (Int.negOfNat 255401548) 1594323)) + ((h^((22-3)+2*1-6:ℕ)*r^1*(NNRat.rawCast 459665122079 2448880128)) + (h^((22-3)+2*2-6:ℕ)*r^2*(NNRat.rawCast 24735163810307 1410554953728)))) + ((h^((22-3)+2*3-6:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 3984197611531409) 304679870005248)) + ((h^((22-3)+2*4-6:ℕ)*r^4*(NNRat.rawCast 21192601872574421 7312316880125952)) + (h^((22-3)+2*5-6:ℕ)*r^5*(NNRat.rawCast 30446098602014515 789730223053602816))))) + (((h^((22-3)+2*6-6:ℕ)*r^6*(Rat.rawCast (Int.negOfNat 128178562347826931) 1184595334580404224)) + ((h^((22-3)+2*7-6:ℕ)*r^7*(NNRat.rawCast 35336490088500240085 2046980738154938499072)) + (h^((22-3)+2*8-6:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 8067016470465992459) 6140942214464815497216)))) + (((h^((22-3)+2*9-6:ℕ)*r^9*(NNRat.rawCast 4590822519085866529 82902719895275009212416)) + (h^((22-3)+2*10-6:ℕ)*r^10*(Rat.rawCast (Int.negOfNat 1083704430860289001) 746124479057475082911744))) + ((h^((22-3)+2*11-6:ℕ)*r^11*(NNRat.rawCast 30695821105674067 4476746874344850497470464)) + (h^((22-3)+2*12-6:ℕ)*r^12*(NNRat.rawCast 13750076961227201 40290721869103654477234176))))))

theorem boundaryReClock76_3_split (h r : ℂ) :

    h^(22-3:ℕ)*boundaryReClock76_3 (r*h^2)=boundaryReLowColumn76_3 h r+h^6*boundaryReHighColumn76_3 h r := by

  rw [(boundaryReClock76_3Norm (r*h^2)).property]

  change h^(22-3:ℕ)*(Rat.rawCast (Int.negOfNat 255401548) 1594323 +
      ((r*h^2) ^ Nat.rawCast 1 * NNRat.rawCast 459665122079 2448880128 +
        ((r*h^2) ^ Nat.rawCast 2 * NNRat.rawCast 24735163810307 1410554953728 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 3984197611531409) 304679870005248 +
            ((r*h^2) ^ Nat.rawCast 4 * NNRat.rawCast 21192601872574421 7312316880125952 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 30446098602014515 789730223053602816 +
                ((r*h^2) ^ Nat.rawCast 6 * Rat.rawCast (Int.negOfNat 128178562347826931) 1184595334580404224 +
                  ((r*h^2) ^ Nat.rawCast 7 * NNRat.rawCast 35336490088500240085 2046980738154938499072 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 8067016470465992459) 6140942214464815497216 +
                      ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 4590822519085866529 82902719895275009212416 +
                        ((r*h^2) ^ Nat.rawCast 10 * Rat.rawCast (Int.negOfNat 1083704430860289001) 746124479057475082911744 +
                          ((r*h^2) ^ Nat.rawCast 11 * NNRat.rawCast 30695821105674067 4476746874344850497470464 +
                            ((r*h^2) ^ Nat.rawCast 12 * NNRat.rawCast 13750076961227201 40290721869103654477234176 +
                              0)))))))))))))=_

  dsimp only [boundaryReLowColumn76_3,boundaryReHighColumn76_3]

  norm_num

  ring <;> simp


def boundaryReLowColumn76_4 (h r : ℂ) : ℂ :=
  0

def boundaryReHighColumn76_4 (h r : ℂ) : ℂ :=
  ((((h^((22-4)+2*0-6:ℕ)*r^0*(NNRat.rawCast 580451074939 816293376)) + ((h^((22-4)+2*1-6:ℕ)*r^1*(NNRat.rawCast 3027591827663 4897760256)) + (h^((22-4)+2*2-6:ℕ)*r^2*(Rat.rawCast (Int.negOfNat 872943112477597) 4231664861184)))) + (((h^((22-4)+2*3-6:ℕ)*r^3*(NNRat.rawCast 1082809371360415 25389989167104)) + (h^((22-4)+2*4-6:ℕ)*r^4*(NNRat.rawCast 103660301096665273 21936950640377856))) + ((h^((22-4)+2*5-6:ℕ)*r^5*(Rat.rawCast (Int.negOfNat 6349396462835622133) 1579460446107205632)) + (h^((22-4)+2*6-6:ℕ)*r^6*(NNRat.rawCast 17452969212118235473 28430288029929701376))))) + (((h^((22-4)+2*7-6:ℕ)*r^7*(Rat.rawCast (Int.negOfNat 105209792018815952689) 4093961476309876998144)) + ((h^((22-4)+2*8-6:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 793839895007146664479) 294765226294311143866368)) + (h^((22-4)+2*9-6:ℕ)*r^9*(NNRat.rawCast 468378633871040181617 1326443518324400147398656)))) + (((h^((22-4)+2*10-6:ℕ)*r^10*(Rat.rawCast (Int.negOfNat 172581908916053155805) 11937991664919601326587904)) + (h^((22-4)+2*11-6:ℕ)*r^11*(NNRat.rawCast 3639349364096350207 13430240623034551492411392))) + ((h^((22-4)+2*12-6:ℕ)*r^12*(Rat.rawCast (Int.negOfNat 9905633421281934959) 1933954649716975414907240448)) + (h^((22-4)+2*13-6:ℕ)*r^13*(NNRat.rawCast 293575300609695167 8702795923726389367082582016))))))

theorem boundaryReClock76_4_split (h r : ℂ) :

    h^(22-4:ℕ)*boundaryReClock76_4 (r*h^2)=boundaryReLowColumn76_4 h r+h^6*boundaryReHighColumn76_4 h r := by

  rw [(boundaryReClock76_4Norm (r*h^2)).property]

  change h^(22-4:ℕ)*(NNRat.rawCast 580451074939 816293376 +
      ((r*h^2) ^ Nat.rawCast 1 * NNRat.rawCast 3027591827663 4897760256 +
        ((r*h^2) ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 872943112477597) 4231664861184 +
          ((r*h^2) ^ Nat.rawCast 3 * NNRat.rawCast 1082809371360415 25389989167104 +
            ((r*h^2) ^ Nat.rawCast 4 * NNRat.rawCast 103660301096665273 21936950640377856 +
              ((r*h^2) ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 6349396462835622133) 1579460446107205632 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 17452969212118235473 28430288029929701376 +
                  ((r*h^2) ^ Nat.rawCast 7 * Rat.rawCast (Int.negOfNat 105209792018815952689) 4093961476309876998144 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 793839895007146664479) 294765226294311143866368 +
                      ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 468378633871040181617 1326443518324400147398656 +
                        ((r*h^2) ^ Nat.rawCast 10 *
                            Rat.rawCast (Int.negOfNat 172581908916053155805) 11937991664919601326587904 +
                          ((r*h^2) ^ Nat.rawCast 11 * NNRat.rawCast 3639349364096350207 13430240623034551492411392 +
                            ((r*h^2) ^ Nat.rawCast 12 *
                                Rat.rawCast (Int.negOfNat 9905633421281934959) 1933954649716975414907240448 +
                              ((r*h^2) ^ Nat.rawCast 13 * NNRat.rawCast 293575300609695167 8702795923726389367082582016 +
                                0))))))))))))))=_

  dsimp only [boundaryReLowColumn76_4,boundaryReHighColumn76_4]

  norm_num

  ring <;> simp


def boundaryReLowColumn76_5 (h r : ℂ) : ℂ :=
  0

def boundaryReHighColumn76_5 (h r : ℂ) : ℂ :=
  ((((h^((22-5)+2*0-6:ℕ)*r^0*(NNRat.rawCast 641382265649 136048896)) + ((h^((22-5)+2*1-6:ℕ)*r^1*(Rat.rawCast (Int.negOfNat 42631093586323) 58773123072)) + (h^((22-5)+2*2-6:ℕ)*r^2*(NNRat.rawCast 24033298136159 264479053824)))) + (((h^((22-5)+2*3-6:ℕ)*r^3*(NNRat.rawCast 25507776569387275 152339935002624)) + (h^((22-5)+2*4-6:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 557960873325484405) 5484237660094464))) + ((h^((22-5)+2*5-6:ℕ)*r^5*(NNRat.rawCast 7418330926261069049 526486815369068544)) + (h^((22-5)+2*6-6:ℕ)*r^6*(NNRat.rawCast 38501327257187750557 113721152119718805504))))) + ((((h^((22-5)+2*7-6:ℕ)*r^7*(Rat.rawCast (Int.negOfNat 443037124184622331457) 1364653825436625666048)) + (h^((22-5)+2*8-6:ℕ)*r^8*(NNRat.rawCast 8224411146406593623867 196510150862874095910912))) + ((h^((22-5)+2*9-6:ℕ)*r^9*(Rat.rawCast (Int.negOfNat 27106615414255252681223) 10611548146595201179189248)) + (h^((22-5)+2*10-6:ℕ)*r^10*(NNRat.rawCast 2510609098595788666727 31834644439785603537567744)))) + (((h^((22-5)+2*11-6:ℕ)*r^11*(Rat.rawCast (Int.negOfNat 143524555414052015797) 143255899979035215919054848)) + (h^((22-5)+2*12-6:ℕ)*r^12*(NNRat.rawCast 21237620319636992089 1933954649716975414907240448))) + ((h^((22-5)+2*13-6:ℕ)*r^13*(Rat.rawCast (Int.negOfNat 4675098911177466233) 23207455796603704978886885376)) + (h^((22-5)+2*14-6:ℕ)*r^14*(NNRat.rawCast 405506432602597781 626601306508300034429945905152))))))

theorem boundaryReClock76_5_split (h r : ℂ) :

    h^(22-5:ℕ)*boundaryReClock76_5 (r*h^2)=boundaryReLowColumn76_5 h r+h^6*boundaryReHighColumn76_5 h r := by

  rw [(boundaryReClock76_5Norm (r*h^2)).property]

  change h^(22-5:ℕ)*(NNRat.rawCast 641382265649 136048896 +
      ((r*h^2) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 42631093586323) 58773123072 +
        ((r*h^2) ^ Nat.rawCast 2 * NNRat.rawCast 24033298136159 264479053824 +
          ((r*h^2) ^ Nat.rawCast 3 * NNRat.rawCast 25507776569387275 152339935002624 +
            ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 557960873325484405) 5484237660094464 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 7418330926261069049 526486815369068544 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 38501327257187750557 113721152119718805504 +
                  ((r*h^2) ^ Nat.rawCast 7 * Rat.rawCast (Int.negOfNat 443037124184622331457) 1364653825436625666048 +
                    ((r*h^2) ^ Nat.rawCast 8 * NNRat.rawCast 8224411146406593623867 196510150862874095910912 +
                      ((r*h^2) ^ Nat.rawCast 9 *
                          Rat.rawCast (Int.negOfNat 27106615414255252681223) 10611548146595201179189248 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 2510609098595788666727 31834644439785603537567744 +
                          ((r*h^2) ^ Nat.rawCast 11 *
                              Rat.rawCast (Int.negOfNat 143524555414052015797) 143255899979035215919054848 +
                            ((r*h^2) ^ Nat.rawCast 12 * NNRat.rawCast 21237620319636992089 1933954649716975414907240448 +
                              ((r*h^2) ^ Nat.rawCast 13 *
                                  Rat.rawCast (Int.negOfNat 4675098911177466233) 23207455796603704978886885376 +
                                ((r*h^2) ^ Nat.rawCast 14 * NNRat.rawCast 405506432602597781 626601306508300034429945905152 +
                                  0)))))))))))))))=_

  dsimp only [boundaryReLowColumn76_5,boundaryReHighColumn76_5]

  norm_num

  ring <;> simp


def boundaryReLowColumn76_6 (h r : ℂ) : ℂ :=
  0

def boundaryReHighColumn76_6 (h r : ℂ) : ℂ :=
  (((((h^((22-6)+2*0-6:ℕ)*r^0*(NNRat.rawCast 521984467501 90699264)) + (h^((22-6)+2*1-6:ℕ)*r^1*(Rat.rawCast (Int.negOfNat 38296672442261) 19591041024))) + ((h^((22-6)+2*2-6:ℕ)*r^2*(NNRat.rawCast 9044128743375011 4231664861184)) + (h^((22-6)+2*3-6:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 460923347021608217) 304679870005248)))) + (((h^((22-6)+2*4-6:ℕ)*r^4*(NNRat.rawCast 3386468087123864579 21936950640377856)) + (h^((22-6)+2*5-6:ℕ)*r^5*(NNRat.rawCast 31639773598267866541 789730223053602816))) + ((h^((22-6)+2*6-6:ℕ)*r^6*(Rat.rawCast (Int.negOfNat 1534458378055478218519) 113721152119718805504)) + (h^((22-6)+2*7-6:ℕ)*r^7*(NNRat.rawCast 14056976992682328934859 8187922952619753996288))))) + ((((h^((22-6)+2*8-6:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 3849413208508757250629) 36845653286788892983296)) + (h^((22-6)+2*9-6:ℕ)*r^9*(NNRat.rawCast 13017708381092649189173 5305774073297600589594624))) + ((h^((22-6)+2*10-6:ℕ)*r^10*(NNRat.rawCast 3446520881208640473325 95503933319356810612703232)) + (h^((22-6)+2*11-6:ℕ)*r^11*(Rat.rawCast (Int.negOfNat 1142267097772873945517) 286511799958070431838109696)))) + (((h^((22-6)+2*12-6:ℕ)*r^12*(NNRat.rawCast 405734704255409069305 3867909299433950829814480896)) + (h^((22-6)+2*13-6:ℕ)*r^13*(Rat.rawCast (Int.negOfNat 8390822305894903273) 17405591847452778734165164032))) + ((h^((22-6)+2*14-6:ℕ)*r^14*(Rat.rawCast (Int.negOfNat 949546426483032623) 626601306508300034429945905152)) + (h^((22-6)+2*15-6:ℕ)*r^15*(NNRat.rawCast 18285856292474113 5639411758574700309869513146368))))))

theorem boundaryReClock76_6_split (h r : ℂ) :

    h^(22-6:ℕ)*boundaryReClock76_6 (r*h^2)=boundaryReLowColumn76_6 h r+h^6*boundaryReHighColumn76_6 h r := by

  rw [(boundaryReClock76_6Norm (r*h^2)).property]

  change h^(22-6:ℕ)*(NNRat.rawCast 521984467501 90699264 +
      ((r*h^2) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 38296672442261) 19591041024 +
        ((r*h^2) ^ Nat.rawCast 2 * NNRat.rawCast 9044128743375011 4231664861184 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 460923347021608217) 304679870005248 +
            ((r*h^2) ^ Nat.rawCast 4 * NNRat.rawCast 3386468087123864579 21936950640377856 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 31639773598267866541 789730223053602816 +
                ((r*h^2) ^ Nat.rawCast 6 * Rat.rawCast (Int.negOfNat 1534458378055478218519) 113721152119718805504 +
                  ((r*h^2) ^ Nat.rawCast 7 * NNRat.rawCast 14056976992682328934859 8187922952619753996288 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 3849413208508757250629) 36845653286788892983296 +
                      ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 13017708381092649189173 5305774073297600589594624 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 3446520881208640473325 95503933319356810612703232 +
                          ((r*h^2) ^ Nat.rawCast 11 *
                              Rat.rawCast (Int.negOfNat 1142267097772873945517) 286511799958070431838109696 +
                            ((r*h^2) ^ Nat.rawCast 12 * NNRat.rawCast 405734704255409069305 3867909299433950829814480896 +
                              ((r*h^2) ^ Nat.rawCast 13 *
                                  Rat.rawCast (Int.negOfNat 8390822305894903273) 17405591847452778734165164032 +
                                ((r*h^2) ^ Nat.rawCast 14 *
                                    Rat.rawCast (Int.negOfNat 949546426483032623) 626601306508300034429945905152 +
                                  ((r*h^2) ^ Nat.rawCast 15 *
                                      NNRat.rawCast 18285856292474113 5639411758574700309869513146368 +
                                    0))))))))))))))))=_

  dsimp only [boundaryReLowColumn76_6,boundaryReHighColumn76_6]

  norm_num

  ring <;> simp


def boundaryReLowColumn76_7 (h r : ℂ) : ℂ :=
  0

def boundaryReHighColumn76_7 (h r : ℂ) : ℂ :=
  (((((h^((22-7)+2*0-6:ℕ)*r^0*(Rat.rawCast (Int.negOfNat 47837539691) 8503056)) + (h^((22-7)+2*1-6:ℕ)*r^1*(NNRat.rawCast 86019589412363 9795520512))) + ((h^((22-7)+2*2-6:ℕ)*r^2*(Rat.rawCast (Int.negOfNat 13018275535923361) 1057916215296)) + (h^((22-7)+2*3-6:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 124219748680329659) 304679870005248)))) + (((h^((22-7)+2*4-6:ℕ)*r^4*(NNRat.rawCast 13467142392276357361 10968475320188928)) + (h^((22-7)+2*5-6:ℕ)*r^5*(Rat.rawCast (Int.negOfNat 253415598630830755853) 789730223053602816))) + ((h^((22-7)+2*6-6:ℕ)*r^6*(NNRat.rawCast 2173733722472516133643 56860576059859402752)) + (h^((22-7)+2*7-6:ℕ)*r^7*(Rat.rawCast (Int.negOfNat 9950442194462674810099) 8187922952619753996288))))) + ((((h^((22-7)+2*8-6:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 112080901432557906299243) 589530452588622287732736)) + (h^((22-7)+2*9-6:ℕ)*r^9*(NNRat.rawCast 237165594725865884168879 10611548146595201179189248))) + ((h^((22-7)+2*10-6:ℕ)*r^10*(Rat.rawCast (Int.negOfNat 96039386593052954438111) 95503933319356810612703232)) + (h^((22-7)+2*11-6:ℕ)*r^11*(NNRat.rawCast 1741471493734137984437 71627949989517607959527424)))) + (((h^((22-7)+2*12-6:ℕ)*r^12*(Rat.rawCast (Int.negOfNat 457041462381164301229) 966977324858487707453620224)) + (h^((22-7)+2*13-6:ℕ)*r^13*(NNRat.rawCast 347100065275036241875 69622367389811114936660656128))) + ((h^((22-7)+2*14-6:ℕ)*r^14*(Rat.rawCast (Int.negOfNat 8234022588000933059) 626601306508300034429945905152)) + ((h^((22-7)+2*15-6:ℕ)*r^15*(NNRat.rawCast 128030383508489 2819705879287350154934756573184)) + (h^((22-7)+2*16-6:ℕ)*r^16*(NNRat.rawCast 168937493305 49565142409347951942212517888)))))))

theorem boundaryReClock76_7_split (h r : ℂ) :

    h^(22-7:ℕ)*boundaryReClock76_7 (r*h^2)=boundaryReLowColumn76_7 h r+h^6*boundaryReHighColumn76_7 h r := by

  rw [(boundaryReClock76_7Norm (r*h^2)).property]

  change h^(22-7:ℕ)*(Rat.rawCast (Int.negOfNat 47837539691) 8503056 +
      ((r*h^2) ^ Nat.rawCast 1 * NNRat.rawCast 86019589412363 9795520512 +
        ((r*h^2) ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 13018275535923361) 1057916215296 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 124219748680329659) 304679870005248 +
            ((r*h^2) ^ Nat.rawCast 4 * NNRat.rawCast 13467142392276357361 10968475320188928 +
              ((r*h^2) ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 253415598630830755853) 789730223053602816 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 2173733722472516133643 56860576059859402752 +
                  ((r*h^2) ^ Nat.rawCast 7 * Rat.rawCast (Int.negOfNat 9950442194462674810099) 8187922952619753996288 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 112080901432557906299243) 589530452588622287732736 +
                      ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 237165594725865884168879 10611548146595201179189248 +
                        ((r*h^2) ^ Nat.rawCast 10 *
                            Rat.rawCast (Int.negOfNat 96039386593052954438111) 95503933319356810612703232 +
                          ((r*h^2) ^ Nat.rawCast 11 * NNRat.rawCast 1741471493734137984437 71627949989517607959527424 +
                            ((r*h^2) ^ Nat.rawCast 12 *
                                Rat.rawCast (Int.negOfNat 457041462381164301229) 966977324858487707453620224 +
                              ((r*h^2) ^ Nat.rawCast 13 * NNRat.rawCast 347100065275036241875 69622367389811114936660656128 +
                                ((r*h^2) ^ Nat.rawCast 14 *
                                    Rat.rawCast (Int.negOfNat 8234022588000933059) 626601306508300034429945905152 +
                                  ((r*h^2) ^ Nat.rawCast 15 * NNRat.rawCast 128030383508489 2819705879287350154934756573184 +
                                    ((r*h^2) ^ Nat.rawCast 16 * NNRat.rawCast 168937493305 49565142409347951942212517888 +
                                      0)))))))))))))))))=_

  dsimp only [boundaryReLowColumn76_7,boundaryReHighColumn76_7]

  norm_num

  ring <;> simp


def boundaryReLowColumn76_8 (h r : ℂ) : ℂ :=
  0

def boundaryReHighColumn76_8 (h r : ℂ) : ℂ :=
  (((((h^((22-8)+2*0-6:ℕ)*r^0*(Rat.rawCast (Int.negOfNat 43039903891) 8503056)) + (h^((22-8)+2*1-6:ℕ)*r^1*(Rat.rawCast (Int.negOfNat 51993159655921) 918330048))) + ((h^((22-8)+2*2-6:ℕ)*r^2*(Rat.rawCast (Int.negOfNat 36816383964341737) 1410554953728)) + (h^((22-8)+2*3-6:ℕ)*r^3*(NNRat.rawCast 2698941304137620131 152339935002624)))) + (((h^((22-8)+2*4-6:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 10091284279338785291) 2437438960041984)) + (h^((22-8)+2*5-6:ℕ)*r^5*(NNRat.rawCast 618740256739823012981 1579460446107205632))) + ((h^((22-8)+2*6-6:ℕ)*r^6*(NNRat.rawCast 4356046131743194851953 113721152119718805504)) + ((h^((22-8)+2*7-6:ℕ)*r^7*(Rat.rawCast (Int.negOfNat 28321057871217096711049) 2046980738154938499072)) + (h^((22-8)+2*8-6:ℕ)*r^8*(NNRat.rawCast 3326170804881961551697 2302853330424305811456)))))) + ((((h^((22-8)+2*9-6:ℕ)*r^9*(Rat.rawCast (Int.negOfNat 128581347659693864508937) 1768591357765866863198208)) + (h^((22-8)+2*10-6:ℕ)*r^10*(NNRat.rawCast 162785130924697058101727 95503933319356810612703232))) + ((h^((22-8)+2*11-6:ℕ)*r^11*(Rat.rawCast (Int.negOfNat 6817004761674135994351) 859535399874211295514329088)) + (h^((22-8)+2*12-6:ℕ)*r^12*(Rat.rawCast (Int.negOfNat 118830036176441743817) 1289303099811316943271493632)))) + (((h^((22-8)+2*13-6:ℕ)*r^13*(Rat.rawCast (Int.negOfNat 13668063861280363745) 2900931974575463122360860672)) + (h^((22-8)+2*14-6:ℕ)*r^14*(NNRat.rawCast 27750595395922238315 626601306508300034429945905152))) + ((h^((22-8)+2*15-6:ℕ)*r^15*(Rat.rawCast (Int.negOfNat 12744276152806037) 208867102169433344809981968384)) + ((h^((22-8)+2*16-6:ℕ)*r^16*(NNRat.rawCast 21961341297329 4229558818931025232402134859776)) + (h^((22-8)+2*17-6:ℕ)*r^17*(NNRat.rawCast 14325530485 114198088111137681274857641213952)))))))

theorem boundaryReClock76_8_split (h r : ℂ) :

    h^(22-8:ℕ)*boundaryReClock76_8 (r*h^2)=boundaryReLowColumn76_8 h r+h^6*boundaryReHighColumn76_8 h r := by

  rw [(boundaryReClock76_8Norm (r*h^2)).property]

  change h^(22-8:ℕ)*(Rat.rawCast (Int.negOfNat 43039903891) 8503056 +
      ((r*h^2) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 51993159655921) 918330048 +
        ((r*h^2) ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 36816383964341737) 1410554953728 +
          ((r*h^2) ^ Nat.rawCast 3 * NNRat.rawCast 2698941304137620131 152339935002624 +
            ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 10091284279338785291) 2437438960041984 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 618740256739823012981 1579460446107205632 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 4356046131743194851953 113721152119718805504 +
                  ((r*h^2) ^ Nat.rawCast 7 * Rat.rawCast (Int.negOfNat 28321057871217096711049) 2046980738154938499072 +
                    ((r*h^2) ^ Nat.rawCast 8 * NNRat.rawCast 3326170804881961551697 2302853330424305811456 +
                      ((r*h^2) ^ Nat.rawCast 9 *
                          Rat.rawCast (Int.negOfNat 128581347659693864508937) 1768591357765866863198208 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 162785130924697058101727 95503933319356810612703232 +
                          ((r*h^2) ^ Nat.rawCast 11 *
                              Rat.rawCast (Int.negOfNat 6817004761674135994351) 859535399874211295514329088 +
                            ((r*h^2) ^ Nat.rawCast 12 *
                                Rat.rawCast (Int.negOfNat 118830036176441743817) 1289303099811316943271493632 +
                              ((r*h^2) ^ Nat.rawCast 13 *
                                  Rat.rawCast (Int.negOfNat 13668063861280363745) 2900931974575463122360860672 +
                                ((r*h^2) ^ Nat.rawCast 14 *
                                    NNRat.rawCast 27750595395922238315 626601306508300034429945905152 +
                                  ((r*h^2) ^ Nat.rawCast 15 *
                                      Rat.rawCast (Int.negOfNat 12744276152806037) 208867102169433344809981968384 +
                                    ((r*h^2) ^ Nat.rawCast 16 * NNRat.rawCast 21961341297329 4229558818931025232402134859776 +
                                      ((r*h^2) ^ Nat.rawCast 17 *
                                          NNRat.rawCast 14325530485 114198088111137681274857641213952 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryReLowColumn76_8,boundaryReHighColumn76_8]

  norm_num

  ring <;> simp


def boundaryReLowColumn76_9 (h r : ℂ) : ℂ :=
  0

def boundaryReHighColumn76_9 (h r : ℂ) : ℂ :=
  (((((h^((22-9)+2*0-6:ℕ)*r^0*(Rat.rawCast (Int.negOfNat 231964931983) 1594323)) + (h^((22-9)+2*1-6:ℕ)*r^1*(Rat.rawCast (Int.negOfNat 210557044735907) 918330048))) + ((h^((22-9)+2*2-6:ℕ)*r^2*(NNRat.rawCast 248462674122865985 2115832430592)) + (h^((22-9)+2*3-6:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 3320502011641449089) 152339935002624)))) + (((h^((22-9)+2*4-6:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 11336060693792637367) 10968475320188928)) + (h^((22-9)+2*5-6:ℕ)*r^5*(NNRat.rawCast 2831905986445154163811 1579460446107205632))) + ((h^((22-9)+2*6-6:ℕ)*r^6*(Rat.rawCast (Int.negOfNat 47687123763919179400543) 113721152119718805504)) + ((h^((22-9)+2*7-6:ℕ)*r^7*(NNRat.rawCast 45224940920577500951155 1023490369077469249536)) + (h^((22-9)+2*8-6:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 6551210243106906428767) 3070471107232407748608)))))) + ((((h^((22-9)+2*9-6:ℕ)*r^9*(NNRat.rawCast 6863276214059699449571 442147839441466715799552)) + (h^((22-9)+2*10-6:ℕ)*r^10*(NNRat.rawCast 153860227282608727952087 47751966659678405306351616))) + ((h^((22-9)+2*11-6:ℕ)*r^11*(Rat.rawCast (Int.negOfNat 6028302026926271670019) 35813974994758803979763712)) + (h^((22-9)+2*12-6:ℕ)*r^12*(NNRat.rawCast 632928382634042059765 161162887476414617908936704)))) + (((h^((22-9)+2*13-6:ℕ)*r^13*(Rat.rawCast (Int.negOfNat 20596470781475235377) 644651549905658471635746816)) + (h^((22-9)+2*14-6:ℕ)*r^14*(NNRat.rawCast 14178643823426880329 313300653254150017214972952576))) + ((h^((22-9)+2*15-6:ℕ)*r^15*(NNRat.rawCast 111320396915907529 1409852939643675077467378286592)) + ((h^((22-9)+2*16-6:ℕ)*r^16*(Rat.rawCast (Int.negOfNat 6342698417503) 117487744970306256455614857216)) + (h^((22-9)+2*17-6:ℕ)*r^17*(NNRat.rawCast 2426981221 57099044055568840637428820606976)))))))

theorem boundaryReClock76_9_split (h r : ℂ) :

    h^(22-9:ℕ)*boundaryReClock76_9 (r*h^2)=boundaryReLowColumn76_9 h r+h^6*boundaryReHighColumn76_9 h r := by

  rw [(boundaryReClock76_9Norm (r*h^2)).property]

  change h^(22-9:ℕ)*(Rat.rawCast (Int.negOfNat 231964931983) 1594323 +
      ((r*h^2) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 210557044735907) 918330048 +
        ((r*h^2) ^ Nat.rawCast 2 * NNRat.rawCast 248462674122865985 2115832430592 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 3320502011641449089) 152339935002624 +
            ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 11336060693792637367) 10968475320188928 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 2831905986445154163811 1579460446107205632 +
                ((r*h^2) ^ Nat.rawCast 6 * Rat.rawCast (Int.negOfNat 47687123763919179400543) 113721152119718805504 +
                  ((r*h^2) ^ Nat.rawCast 7 * NNRat.rawCast 45224940920577500951155 1023490369077469249536 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 6551210243106906428767) 3070471107232407748608 +
                      ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 6863276214059699449571 442147839441466715799552 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 153860227282608727952087 47751966659678405306351616 +
                          ((r*h^2) ^ Nat.rawCast 11 *
                              Rat.rawCast (Int.negOfNat 6028302026926271670019) 35813974994758803979763712 +
                            ((r*h^2) ^ Nat.rawCast 12 * NNRat.rawCast 632928382634042059765 161162887476414617908936704 +
                              ((r*h^2) ^ Nat.rawCast 13 *
                                  Rat.rawCast (Int.negOfNat 20596470781475235377) 644651549905658471635746816 +
                                ((r*h^2) ^ Nat.rawCast 14 *
                                    NNRat.rawCast 14178643823426880329 313300653254150017214972952576 +
                                  ((r*h^2) ^ Nat.rawCast 15 *
                                      NNRat.rawCast 111320396915907529 1409852939643675077467378286592 +
                                    ((r*h^2) ^ Nat.rawCast 16 *
                                        Rat.rawCast (Int.negOfNat 6342698417503) 117487744970306256455614857216 +
                                      ((r*h^2) ^ Nat.rawCast 17 * NNRat.rawCast 2426981221 57099044055568840637428820606976 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryReLowColumn76_9,boundaryReHighColumn76_9]

  norm_num

  ring <;> simp


def boundaryReLowColumn76_10 (h r : ℂ) : ℂ :=
  0

def boundaryReHighColumn76_10 (h r : ℂ) : ℂ :=
  (((((h^((22-10)+2*0-6:ℕ)*r^0*(Rat.rawCast (Int.negOfNat 2118054708323) 3188646)) + (h^((22-10)+2*1-6:ℕ)*r^1*(NNRat.rawCast 56480011677895 229582512))) + ((h^((22-10)+2*2-6:ℕ)*r^2*(NNRat.rawCast 134058055137985705 4231664861184)) + (h^((22-10)+2*3-6:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 17815765018373067625) 304679870005248)))) + (((h^((22-10)+2*4-6:ℕ)*r^4*(NNRat.rawCast 657569270106038332769 21936950640377856)) + (h^((22-10)+2*5-6:ℕ)*r^5*(Rat.rawCast (Int.negOfNat 2727909046342592746033) 394865111526801408))) + ((h^((22-10)+2*6-6:ℕ)*r^6*(NNRat.rawCast 41665285645354960385633 56860576059859402752)) + ((h^((22-10)+2*7-6:ℕ)*r^7*(Rat.rawCast (Int.negOfNat 45193801069645288518005) 2046980738154938499072)) + (h^((22-10)+2*8-6:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 190647925918021881910891) 73691306573577785966592)))))) + ((((h^((22-10)+2*9-6:ℕ)*r^9*(NNRat.rawCast 265826180879443913349661 884295678882933431599104)) + (h^((22-10)+2*10-6:ℕ)*r^10*(Rat.rawCast (Int.negOfNat 9320943547576114567169) 663221759162200073699328))) + ((h^((22-10)+2*11-6:ℕ)*r^11*(NNRat.rawCast 4549686955444780899643 11937991664919601326587904)) + (h^((22-10)+2*12-6:ℕ)*r^12*(Rat.rawCast (Int.negOfNat 4960483886744146624255) 644651549905658471635746816)))) + (((h^((22-10)+2*13-6:ℕ)*r^13*(NNRat.rawCast 33161798203314162799 362616496821932890295107584)) + (h^((22-10)+2*14-6:ℕ)*r^14*(Rat.rawCast (Int.negOfNat 9756635795994252575) 26108387771179168101247746048))) + ((h^((22-10)+2*15-6:ℕ)*r^15*(NNRat.rawCast 27234902191212835 78325163313537504303743238144)) + ((h^((22-10)+2*16-6:ℕ)*r^16*(NNRat.rawCast 1292771330375 1409852939643675077467378286592)) + (h^((22-10)+2*17-6:ℕ)*r^17*(Rat.rawCast (Int.negOfNat 26945503417) 38066029370379227091619213737984)))))))

theorem boundaryReClock76_10_split (h r : ℂ) :

    h^(22-10:ℕ)*boundaryReClock76_10 (r*h^2)=boundaryReLowColumn76_10 h r+h^6*boundaryReHighColumn76_10 h r := by

  rw [(boundaryReClock76_10Norm (r*h^2)).property]

  change h^(22-10:ℕ)*(Rat.rawCast (Int.negOfNat 2118054708323) 3188646 +
      ((r*h^2) ^ Nat.rawCast 1 * NNRat.rawCast 56480011677895 229582512 +
        ((r*h^2) ^ Nat.rawCast 2 * NNRat.rawCast 134058055137985705 4231664861184 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 17815765018373067625) 304679870005248 +
            ((r*h^2) ^ Nat.rawCast 4 * NNRat.rawCast 657569270106038332769 21936950640377856 +
              ((r*h^2) ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 2727909046342592746033) 394865111526801408 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 41665285645354960385633 56860576059859402752 +
                  ((r*h^2) ^ Nat.rawCast 7 * Rat.rawCast (Int.negOfNat 45193801069645288518005) 2046980738154938499072 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 190647925918021881910891) 73691306573577785966592 +
                      ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 265826180879443913349661 884295678882933431599104 +
                        ((r*h^2) ^ Nat.rawCast 10 *
                            Rat.rawCast (Int.negOfNat 9320943547576114567169) 663221759162200073699328 +
                          ((r*h^2) ^ Nat.rawCast 11 * NNRat.rawCast 4549686955444780899643 11937991664919601326587904 +
                            ((r*h^2) ^ Nat.rawCast 12 *
                                Rat.rawCast (Int.negOfNat 4960483886744146624255) 644651549905658471635746816 +
                              ((r*h^2) ^ Nat.rawCast 13 * NNRat.rawCast 33161798203314162799 362616496821932890295107584 +
                                ((r*h^2) ^ Nat.rawCast 14 *
                                    Rat.rawCast (Int.negOfNat 9756635795994252575) 26108387771179168101247746048 +
                                  ((r*h^2) ^ Nat.rawCast 15 * NNRat.rawCast 27234902191212835 78325163313537504303743238144 +
                                    ((r*h^2) ^ Nat.rawCast 16 * NNRat.rawCast 1292771330375 1409852939643675077467378286592 +
                                      ((r*h^2) ^ Nat.rawCast 17 *
                                          Rat.rawCast (Int.negOfNat 26945503417) 38066029370379227091619213737984 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryReLowColumn76_10,boundaryReHighColumn76_10]

  norm_num

  ring <;> simp


def boundaryReLowColumn76_11 (h r : ℂ) : ℂ :=
  0

def boundaryReHighColumn76_11 (h r : ℂ) : ℂ :=
  (((((h^((22-11)+2*0-6:ℕ)*r^0*(Rat.rawCast (Int.negOfNat 360033540581) 1594323)) + (h^((22-11)+2*1-6:ℕ)*r^1*(NNRat.rawCast 17568454872499 28697814))) + ((h^((22-11)+2*2-6:ℕ)*r^2*(Rat.rawCast (Int.negOfNat 920524941361915531) 2115832430592)) + (h^((22-11)+2*3-6:ℕ)*r^3*(NNRat.rawCast 73496748484323052529 304679870005248)))) + (((h^((22-11)+2*4-6:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 27429392756818027649) 457019805007872)) + (h^((22-11)+2*5-6:ℕ)*r^5*(NNRat.rawCast 3978806380121646237391 789730223053602816))) + ((h^((22-11)+2*6-6:ℕ)*r^6*(NNRat.rawCast 13225175638740216702139 28430288029929701376)) + ((h^((22-11)+2*7-6:ℕ)*r^7*(Rat.rawCast (Int.negOfNat 4046844871148757577) 29249267520503808)) + (h^((22-11)+2*8-6:ℕ)*r^8*(NNRat.rawCast 477167294277387620196913 36845653286788892983296)))))) + ((((h^((22-11)+2*9-6:ℕ)*r^9*(Rat.rawCast (Int.negOfNat 206070765128072537541793) 331610879581100036849664)) + (h^((22-11)+2*10-6:ℕ)*r^10*(NNRat.rawCast 178347676301480892829787 11937991664919601326587904))) + ((h^((22-11)+2*11-6:ℕ)*r^11*(Rat.rawCast (Int.negOfNat 1365558175881921806213) 11937991664919601326587904)) + (h^((22-11)+2*12-6:ℕ)*r^12*(NNRat.rawCast 636471752928721651 35813974994758803979763712)))) + (((h^((22-11)+2*13-6:ℕ)*r^13*(Rat.rawCast (Int.negOfNat 21188485667851309369) 483488662429243853726810112)) + (h^((22-11)+2*14-6:ℕ)*r^14*(NNRat.rawCast 12462386243290758229 26108387771179168101247746048))) + ((h^((22-11)+2*15-6:ℕ)*r^15*(Rat.rawCast (Int.negOfNat 78105652709244055) 78325163313537504303743238144)) + ((h^((22-11)+2*16-6:ℕ)*r^16*(NNRat.rawCast 26240936749825 78325163313537504303743238144)) + (h^((22-11)+2*17-6:ℕ)*r^17*(NNRat.rawCast 7534594907 1057389704732756308100533714944)))))))

theorem boundaryReClock76_11_split (h r : ℂ) :

    h^(22-11:ℕ)*boundaryReClock76_11 (r*h^2)=boundaryReLowColumn76_11 h r+h^6*boundaryReHighColumn76_11 h r := by

  rw [(boundaryReClock76_11Norm (r*h^2)).property]

  change h^(22-11:ℕ)*(Rat.rawCast (Int.negOfNat 360033540581) 1594323 +
      ((r*h^2) ^ Nat.rawCast 1 * NNRat.rawCast 17568454872499 28697814 +
        ((r*h^2) ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 920524941361915531) 2115832430592 +
          ((r*h^2) ^ Nat.rawCast 3 * NNRat.rawCast 73496748484323052529 304679870005248 +
            ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 27429392756818027649) 457019805007872 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 3978806380121646237391 789730223053602816 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 13225175638740216702139 28430288029929701376 +
                  ((r*h^2) ^ Nat.rawCast 7 * Rat.rawCast (Int.negOfNat 4046844871148757577) 29249267520503808 +
                    ((r*h^2) ^ Nat.rawCast 8 * NNRat.rawCast 477167294277387620196913 36845653286788892983296 +
                      ((r*h^2) ^ Nat.rawCast 9 *
                          Rat.rawCast (Int.negOfNat 206070765128072537541793) 331610879581100036849664 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 178347676301480892829787 11937991664919601326587904 +
                          ((r*h^2) ^ Nat.rawCast 11 *
                              Rat.rawCast (Int.negOfNat 1365558175881921806213) 11937991664919601326587904 +
                            ((r*h^2) ^ Nat.rawCast 12 * NNRat.rawCast 636471752928721651 35813974994758803979763712 +
                              ((r*h^2) ^ Nat.rawCast 13 *
                                  Rat.rawCast (Int.negOfNat 21188485667851309369) 483488662429243853726810112 +
                                ((r*h^2) ^ Nat.rawCast 14 * NNRat.rawCast 12462386243290758229 26108387771179168101247746048 +
                                  ((r*h^2) ^ Nat.rawCast 15 *
                                      Rat.rawCast (Int.negOfNat 78105652709244055) 78325163313537504303743238144 +
                                    ((r*h^2) ^ Nat.rawCast 16 * NNRat.rawCast 26240936749825 78325163313537504303743238144 +
                                      ((r*h^2) ^ Nat.rawCast 17 * NNRat.rawCast 7534594907 1057389704732756308100533714944 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryReLowColumn76_11,boundaryReHighColumn76_11]

  norm_num

  ring <;> simp


def boundaryReLowColumn76_12 (h r : ℂ) : ℂ :=
  0

def boundaryReHighColumn76_12 (h r : ℂ) : ℂ :=
  (((((h^((22-12)+2*0-6:ℕ)*r^0*(NNRat.rawCast 2115896746330 1594323)) + (h^((22-12)+2*1-6:ℕ)*r^1*(Rat.rawCast (Int.negOfNat 4887845985995) 4782969))) + ((h^((22-12)+2*2-6:ℕ)*r^2*(NNRat.rawCast 452481369635861897 470184984576)) + (h^((22-12)+2*3-6:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 735812267157759707) 3173748645888)))) + (((h^((22-12)+2*4-6:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 75435289208493100207) 3656158440062976)) + (h^((22-12)+2*5-6:ℕ)*r^5*(NNRat.rawCast 888373109037337581125 49358138940850176))) + ((h^((22-12)+2*6-6:ℕ)*r^6*(Rat.rawCast (Int.negOfNat 191721690042457850287) 55527906308456448)) + ((h^((22-12)+2*7-6:ℕ)*r^7*(NNRat.rawCast 1613838269297808138013 4738381338321616896)) + (h^((22-12)+2*8-6:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 172121852342837169901975) 9211413321697223245824)))))) + ((((h^((22-12)+2*9-6:ℕ)*r^9*(NNRat.rawCast 37425770717325900097697 82902719895275009212416)) + (h^((22-12)+2*10-6:ℕ)*r^10*(NNRat.rawCast 38681680767025580551 4605706660848611622912))) + ((h^((22-12)+2*11-6:ℕ)*r^11*(Rat.rawCast (Int.negOfNat 48847947315614820159353) 53720962492138205969645568)) + (h^((22-12)+2*12-6:ℕ)*r^12*(NNRat.rawCast 5853187574794241724079 241744331214621926863405056)))) + (((h^((22-12)+2*13-6:ℕ)*r^13*(Rat.rawCast (Int.negOfNat 52898768435336212561) 241744331214621926863405056)) + (h^((22-12)+2*14-6:ℕ)*r^14*(NNRat.rawCast 383697734414416087 815887117849349003163992064))) + ((h^((22-12)+2*15-6:ℕ)*r^15*(NNRat.rawCast 1236361820156059 4351397961863194683541291008)) + ((h^((22-12)+2*16-6:ℕ)*r^16*(Rat.rawCast (Int.negOfNat 3132177223889) 6527096942794792025311936512)) + (h^((22-12)+2*17-6:ℕ)*r^17*(Rat.rawCast (Int.negOfNat 758012507) 132173713091594538512566714368)))))))

theorem boundaryReClock76_12_split (h r : ℂ) :

    h^(22-12:ℕ)*boundaryReClock76_12 (r*h^2)=boundaryReLowColumn76_12 h r+h^6*boundaryReHighColumn76_12 h r := by

  rw [(boundaryReClock76_12Norm (r*h^2)).property]

  change h^(22-12:ℕ)*(NNRat.rawCast 2115896746330 1594323 +
      ((r*h^2) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 4887845985995) 4782969 +
        ((r*h^2) ^ Nat.rawCast 2 * NNRat.rawCast 452481369635861897 470184984576 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 735812267157759707) 3173748645888 +
            ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 75435289208493100207) 3656158440062976 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 888373109037337581125 49358138940850176 +
                ((r*h^2) ^ Nat.rawCast 6 * Rat.rawCast (Int.negOfNat 191721690042457850287) 55527906308456448 +
                  ((r*h^2) ^ Nat.rawCast 7 * NNRat.rawCast 1613838269297808138013 4738381338321616896 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 172121852342837169901975) 9211413321697223245824 +
                      ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 37425770717325900097697 82902719895275009212416 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 38681680767025580551 4605706660848611622912 +
                          ((r*h^2) ^ Nat.rawCast 11 *
                              Rat.rawCast (Int.negOfNat 48847947315614820159353) 53720962492138205969645568 +
                            ((r*h^2) ^ Nat.rawCast 12 * NNRat.rawCast 5853187574794241724079 241744331214621926863405056 +
                              ((r*h^2) ^ Nat.rawCast 13 *
                                  Rat.rawCast (Int.negOfNat 52898768435336212561) 241744331214621926863405056 +
                                ((r*h^2) ^ Nat.rawCast 14 * NNRat.rawCast 383697734414416087 815887117849349003163992064 +
                                  ((r*h^2) ^ Nat.rawCast 15 * NNRat.rawCast 1236361820156059 4351397961863194683541291008 +
                                    ((r*h^2) ^ Nat.rawCast 16 *
                                        Rat.rawCast (Int.negOfNat 3132177223889) 6527096942794792025311936512 +
                                      ((r*h^2) ^ Nat.rawCast 17 *
                                          Rat.rawCast (Int.negOfNat 758012507) 132173713091594538512566714368 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryReLowColumn76_12,boundaryReHighColumn76_12]

  norm_num

  ring <;> simp


def boundaryReLowColumn76_13 (h r : ℂ) : ℂ :=
  0

def boundaryReHighColumn76_13 (h r : ℂ) : ℂ :=
  (((((h^((22-13)+2*0-6:ℕ)*r^0*(NNRat.rawCast 114719017340 531441)) + (h^((22-13)+2*1-6:ℕ)*r^1*(NNRat.rawCast 3221264502340 1594323))) + ((h^((22-13)+2*2-6:ℕ)*r^2*(Rat.rawCast (Int.negOfNat 33439209471454373) 2115832430592)) + (h^((22-13)+2*3-6:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 21222272779248714413) 38084983750656)))) + (((h^((22-13)+2*4-6:ℕ)*r^4*(NNRat.rawCast 105788716395505184105 457019805007872)) + (h^((22-13)+2*5-6:ℕ)*r^5*(Rat.rawCast (Int.negOfNat 4527507267961596325865) 98716277881700352))) + ((h^((22-13)+2*6-6:ℕ)*r^6*(NNRat.rawCast 37874640804033095876825 7107572007482425344)) + ((h^((22-13)+2*7-6:ℕ)*r^7*(Rat.rawCast (Int.negOfNat 1492942879875765628315) 3998009254208864256)) + (h^((22-13)+2*8-6:ℕ)*r^8*(NNRat.rawCast 115933709965584087279551 9211413321697223245824)))))) + ((((h^((22-13)+2*9-6:ℕ)*r^9*(NNRat.rawCast 24866062742864992766795 82902719895275009212416)) + (h^((22-13)+2*10-6:ℕ)*r^10*(Rat.rawCast (Int.negOfNat 40445270447041873837189) 746124479057475082911744))) + ((h^((22-13)+2*11-6:ℕ)*r^11*(NNRat.rawCast 930892117094983328173 373062239528737541455872)) + (h^((22-13)+2*12-6:ℕ)*r^12*(Rat.rawCast (Int.negOfNat 13564531176772919328887) 241744331214621926863405056)))) + (((h^((22-13)+2*13-6:ℕ)*r^13*(NNRat.rawCast 1276070651702658008447 2175698980931597341770645504)) + (h^((22-13)+2*14-6:ℕ)*r^14*(Rat.rawCast (Int.negOfNat 2496526281237265085) 1087849490465798670885322752))) + ((h^((22-13)+2*15-6:ℕ)*r^15*(NNRat.rawCast 2787216140415433 1087849490465798670885322752)) + ((h^((22-13)+2*16-6:ℕ)*r^16*(Rat.rawCast (Int.negOfNat 2022407420621) 6527096942794792025311936512)) + (h^((22-13)+2*17-6:ℕ)*r^17*(Rat.rawCast (Int.negOfNat 11700680453) 176231617455459384683422285824)))))))

theorem boundaryReClock76_13_split (h r : ℂ) :

    h^(22-13:ℕ)*boundaryReClock76_13 (r*h^2)=boundaryReLowColumn76_13 h r+h^6*boundaryReHighColumn76_13 h r := by

  rw [(boundaryReClock76_13Norm (r*h^2)).property]

  change h^(22-13:ℕ)*(NNRat.rawCast 114719017340 531441 +
      ((r*h^2) ^ Nat.rawCast 1 * NNRat.rawCast 3221264502340 1594323 +
        ((r*h^2) ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 33439209471454373) 2115832430592 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 21222272779248714413) 38084983750656 +
            ((r*h^2) ^ Nat.rawCast 4 * NNRat.rawCast 105788716395505184105 457019805007872 +
              ((r*h^2) ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 4527507267961596325865) 98716277881700352 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 37874640804033095876825 7107572007482425344 +
                  ((r*h^2) ^ Nat.rawCast 7 * Rat.rawCast (Int.negOfNat 1492942879875765628315) 3998009254208864256 +
                    ((r*h^2) ^ Nat.rawCast 8 * NNRat.rawCast 115933709965584087279551 9211413321697223245824 +
                      ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 24866062742864992766795 82902719895275009212416 +
                        ((r*h^2) ^ Nat.rawCast 10 *
                            Rat.rawCast (Int.negOfNat 40445270447041873837189) 746124479057475082911744 +
                          ((r*h^2) ^ Nat.rawCast 11 * NNRat.rawCast 930892117094983328173 373062239528737541455872 +
                            ((r*h^2) ^ Nat.rawCast 12 *
                                Rat.rawCast (Int.negOfNat 13564531176772919328887) 241744331214621926863405056 +
                              ((r*h^2) ^ Nat.rawCast 13 * NNRat.rawCast 1276070651702658008447 2175698980931597341770645504 +
                                ((r*h^2) ^ Nat.rawCast 14 *
                                    Rat.rawCast (Int.negOfNat 2496526281237265085) 1087849490465798670885322752 +
                                  ((r*h^2) ^ Nat.rawCast 15 * NNRat.rawCast 2787216140415433 1087849490465798670885322752 +
                                    ((r*h^2) ^ Nat.rawCast 16 *
                                        Rat.rawCast (Int.negOfNat 2022407420621) 6527096942794792025311936512 +
                                      ((r*h^2) ^ Nat.rawCast 17 *
                                          Rat.rawCast (Int.negOfNat 11700680453) 176231617455459384683422285824 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryReLowColumn76_13,boundaryReHighColumn76_13]

  norm_num

  ring <;> simp


def boundaryReLowColumn76_14 (h r : ℂ) : ℂ :=
  0

def boundaryReHighColumn76_14 (h r : ℂ) : ℂ :=
  (((((h^((22-14)+2*0-6:ℕ)*r^0*(NNRat.rawCast 5394966086360 1594323)) + (h^((22-14)+2*1-6:ℕ)*r^1*(NNRat.rawCast 39350588681348 14348907))) + ((h^((22-14)+2*2-6:ℕ)*r^2*(Rat.rawCast (Int.negOfNat 3589142796807723451) 1057916215296)) + (h^((22-14)+2*3-6:ℕ)*r^3*(NNRat.rawCast 3321917108806349755 2380311484416)))) + (((h^((22-14)+2*4-6:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 217657400230905663265) 685529707511808)) + (h^((22-14)+2*5-6:ℕ)*r^5*(NNRat.rawCast 1100265958586151215 24100653779712))) + ((h^((22-14)+2*6-6:ℕ)*r^6*(Rat.rawCast (Int.negOfNat 15237509241550300368319) 3553786003741212672)) + ((h^((22-14)+2*7-6:ℕ)*r^7*(NNRat.rawCast 14274429312099492278899 63968148067341828096)) + (h^((22-14)+2*8-6:ℕ)*r^8*(NNRat.rawCast 13675116414641514484481 4605706660848611622912)))))) + ((((h^((22-14)+2*9-6:ℕ)*r^9*(Rat.rawCast (Int.negOfNat 42489802366065464004667) 27634239965091669737472)) + (h^((22-14)+2*10-6:ℕ)*r^10*(NNRat.rawCast 29166773656570587434287 248708159685825027637248))) + ((h^((22-14)+2*11-6:ℕ)*r^11*(Rat.rawCast (Int.negOfNat 7157306975615495392435) 1678780077879318936551424)) + (h^((22-14)+2*12-6:ℕ)*r^12*(NNRat.rawCast 50873455678515303779 629542529204744601206784)))) + (((h^((22-14)+2*13-6:ℕ)*r^13*(Rat.rawCast (Int.negOfNat 755264063166663593) 944313793807116901810176)) + (h^((22-14)+2*14-6:ℕ)*r^14*(NNRat.rawCast 70721978665527299 20145360934551827238617088))) + ((h^((22-14)+2*15-6:ℕ)*r^15*(Rat.rawCast (Int.negOfNat 160769608743479) 30218041401827740857925632)) + ((h^((22-14)+2*16-6:ℕ)*r^16*(NNRat.rawCast 25561885391 15109020700913870428962816)) + (h^((22-14)+2*17-6:ℕ)*r^17*(NNRat.rawCast 72277303 543924745232899335442661376)))))))

theorem boundaryReClock76_14_split (h r : ℂ) :

    h^(22-14:ℕ)*boundaryReClock76_14 (r*h^2)=boundaryReLowColumn76_14 h r+h^6*boundaryReHighColumn76_14 h r := by

  rw [(boundaryReClock76_14Norm (r*h^2)).property]

  change h^(22-14:ℕ)*(NNRat.rawCast 5394966086360 1594323 +
      ((r*h^2) ^ Nat.rawCast 1 * NNRat.rawCast 39350588681348 14348907 +
        ((r*h^2) ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 3589142796807723451) 1057916215296 +
          ((r*h^2) ^ Nat.rawCast 3 * NNRat.rawCast 3321917108806349755 2380311484416 +
            ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 217657400230905663265) 685529707511808 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 1100265958586151215 24100653779712 +
                ((r*h^2) ^ Nat.rawCast 6 * Rat.rawCast (Int.negOfNat 15237509241550300368319) 3553786003741212672 +
                  ((r*h^2) ^ Nat.rawCast 7 * NNRat.rawCast 14274429312099492278899 63968148067341828096 +
                    ((r*h^2) ^ Nat.rawCast 8 * NNRat.rawCast 13675116414641514484481 4605706660848611622912 +
                      ((r*h^2) ^ Nat.rawCast 9 * Rat.rawCast (Int.negOfNat 42489802366065464004667) 27634239965091669737472 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 29166773656570587434287 248708159685825027637248 +
                          ((r*h^2) ^ Nat.rawCast 11 *
                              Rat.rawCast (Int.negOfNat 7157306975615495392435) 1678780077879318936551424 +
                            ((r*h^2) ^ Nat.rawCast 12 * NNRat.rawCast 50873455678515303779 629542529204744601206784 +
                              ((r*h^2) ^ Nat.rawCast 13 *
                                  Rat.rawCast (Int.negOfNat 755264063166663593) 944313793807116901810176 +
                                ((r*h^2) ^ Nat.rawCast 14 * NNRat.rawCast 70721978665527299 20145360934551827238617088 +
                                  ((r*h^2) ^ Nat.rawCast 15 *
                                      Rat.rawCast (Int.negOfNat 160769608743479) 30218041401827740857925632 +
                                    ((r*h^2) ^ Nat.rawCast 16 * NNRat.rawCast 25561885391 15109020700913870428962816 +
                                      ((r*h^2) ^ Nat.rawCast 17 * NNRat.rawCast 72277303 543924745232899335442661376 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryReLowColumn76_14,boundaryReHighColumn76_14]

  norm_num

  ring <;> simp


def boundaryReLowColumn76_15 (h r : ℂ) : ℂ :=
  0

def boundaryReHighColumn76_15 (h r : ℂ) : ℂ :=
  (((((h^((22-15)+2*0-6:ℕ)*r^0*(NNRat.rawCast 13563919004608 1594323)) + (h^((22-15)+2*1-6:ℕ)*r^1*(Rat.rawCast (Int.negOfNat 37984810940960) 4782969))) + ((h^((22-15)+2*2-6:ℕ)*r^2*(NNRat.rawCast 1955412045322578445 528958107648)) + (h^((22-15)+2*3-6:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 835620800934279901) 793437161472)))) + (((h^((22-15)+2*4-6:ℕ)*r^4*(NNRat.rawCast 22691434948548053101 114254951251968)) + (h^((22-15)+2*5-6:ℕ)*r^5*(Rat.rawCast (Int.negOfNat 52590016560273871169) 2056589122535424))) + ((h^((22-15)+2*6-6:ℕ)*r^6*(NNRat.rawCast 128301344524369850393 65810851921133568)) + ((h^((22-15)+2*7-6:ℕ)*r^7*(NNRat.rawCast 145160439264704640047 10661358011223638016)) + (h^((22-15)+2*8-6:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 3072446940346684817225) 127936296134683656192)))))) + ((((h^((22-15)+2*9-6:ℕ)*r^9*(NNRat.rawCast 119666949353033694298499 41451359947637504606208)) + (h^((22-15)+2*10-6:ℕ)*r^10*(Rat.rawCast (Int.negOfNat 21031234662045789362075) 124354079842912513818624))) + ((h^((22-15)+2*11-6:ℕ)*r^11*(NNRat.rawCast 17522417463260795714321 3357560155758637873102848)) + (h^((22-15)+2*12-6:ℕ)*r^12*(Rat.rawCast (Int.negOfNat 69652784203948633385) 839390038939659468275712)))) + (((h^((22-15)+2*13-6:ℕ)*r^13*(NNRat.rawCast 7099975357912210705 10072680467275913619308544)) + (h^((22-15)+2*14-6:ℕ)*r^14*(Rat.rawCast (Int.negOfNat 30795092088100715) 10072680467275913619308544))) + ((h^((22-15)+2*15-6:ℕ)*r^15*(NNRat.rawCast 54348775355899 10072680467275913619308544)) + ((h^((22-15)+2*16-6:ℕ)*r^16*(Rat.rawCast (Int.negOfNat 13358326883) 5036340233637956809654272)) + (h^((22-15)+2*17-6:ℕ)*r^17*(NNRat.rawCast 18989215 203971779462337250790998016)))))))

theorem boundaryReClock76_15_split (h r : ℂ) :

    h^(22-15:ℕ)*boundaryReClock76_15 (r*h^2)=boundaryReLowColumn76_15 h r+h^6*boundaryReHighColumn76_15 h r := by

  rw [(boundaryReClock76_15Norm (r*h^2)).property]

  change h^(22-15:ℕ)*(NNRat.rawCast 13563919004608 1594323 +
      ((r*h^2) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 37984810940960) 4782969 +
        ((r*h^2) ^ Nat.rawCast 2 * NNRat.rawCast 1955412045322578445 528958107648 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 835620800934279901) 793437161472 +
            ((r*h^2) ^ Nat.rawCast 4 * NNRat.rawCast 22691434948548053101 114254951251968 +
              ((r*h^2) ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 52590016560273871169) 2056589122535424 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 128301344524369850393 65810851921133568 +
                  ((r*h^2) ^ Nat.rawCast 7 * NNRat.rawCast 145160439264704640047 10661358011223638016 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 3072446940346684817225) 127936296134683656192 +
                      ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 119666949353033694298499 41451359947637504606208 +
                        ((r*h^2) ^ Nat.rawCast 10 *
                            Rat.rawCast (Int.negOfNat 21031234662045789362075) 124354079842912513818624 +
                          ((r*h^2) ^ Nat.rawCast 11 * NNRat.rawCast 17522417463260795714321 3357560155758637873102848 +
                            ((r*h^2) ^ Nat.rawCast 12 *
                                Rat.rawCast (Int.negOfNat 69652784203948633385) 839390038939659468275712 +
                              ((r*h^2) ^ Nat.rawCast 13 * NNRat.rawCast 7099975357912210705 10072680467275913619308544 +
                                ((r*h^2) ^ Nat.rawCast 14 *
                                    Rat.rawCast (Int.negOfNat 30795092088100715) 10072680467275913619308544 +
                                  ((r*h^2) ^ Nat.rawCast 15 * NNRat.rawCast 54348775355899 10072680467275913619308544 +
                                    ((r*h^2) ^ Nat.rawCast 16 *
                                        Rat.rawCast (Int.negOfNat 13358326883) 5036340233637956809654272 +
                                      ((r*h^2) ^ Nat.rawCast 17 * NNRat.rawCast 18989215 203971779462337250790998016 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryReLowColumn76_15,boundaryReHighColumn76_15]

  norm_num

  ring <;> simp


def boundaryReLowColumn76_16 (h r : ℂ) : ℂ :=
  0

def boundaryReHighColumn76_16 (h r : ℂ) : ℂ :=
  (((((h^((22-16)+2*0-6:ℕ)*r^0*(Rat.rawCast (Int.negOfNat 2280513882496) 1594323)) + (h^((22-16)+2*1-6:ℕ)*r^1*(NNRat.rawCast 38642214431872 14348907))) + ((h^((22-16)+2*2-6:ℕ)*r^2*(Rat.rawCast (Int.negOfNat 5027075167090235) 3265173504)) + (h^((22-16)+2*3-6:ℕ)*r^3*(NNRat.rawCast 115014345418774361 264479053824)))) + (((h^((22-16)+2*4-6:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 8228038022974059391) 114254951251968)) + (h^((22-16)+2*5-6:ℕ)*r^5*(NNRat.rawCast 3164816948286127745 514147280633856))) + ((h^((22-16)+2*6-6:ℕ)*r^6*(NNRat.rawCast 118335823536562382989 296148833645101056)) + ((h^((22-16)+2*7-6:ℕ)*r^7*(Rat.rawCast (Int.negOfNat 204118511716521456295) 888446500935303168)) + (h^((22-16)+2*8-6:ℕ)*r^8*(NNRat.rawCast 14217058126033528159781 383808888404050968576)))))) + ((((h^((22-16)+2*9-6:ℕ)*r^9*(Rat.rawCast (Int.negOfNat 67296295829398153290253) 20725679973818752303104)) + (h^((22-16)+2*10-6:ℕ)*r^10*(NNRat.rawCast 60664994436785965393673 373062239528737541455872))) + ((h^((22-16)+2*11-6:ℕ)*r^11*(Rat.rawCast (Int.negOfNat 4958718258837756564619) 1119186718586212624367616)) + (h^((22-16)+2*12-6:ℕ)*r^12*(NNRat.rawCast 16690238053394868131 279796679646553156091904)))) + (((h^((22-16)+2*13-6:ℕ)*r^13*(Rat.rawCast (Int.negOfNat 18624987334963153) 46632779941092192681984)) + (h^((22-16)+2*14-6:ℕ)*r^14*(NNRat.rawCast 5106683045381761 3357560155758637873102848))) + ((h^((22-16)+2*15-6:ℕ)*r^15*(Rat.rawCast (Int.negOfNat 10575635694101) 3357560155758637873102848)) + ((h^((22-16)+2*16-6:ℕ)*r^16*(NNRat.rawCast 13269937105 5036340233637956809654272)) + (h^((22-16)+2*17-6:ℕ)*r^17*(Rat.rawCast (Int.negOfNat 4489513) 8498824144264052116291584)))))))

theorem boundaryReClock76_16_split (h r : ℂ) :

    h^(22-16:ℕ)*boundaryReClock76_16 (r*h^2)=boundaryReLowColumn76_16 h r+h^6*boundaryReHighColumn76_16 h r := by

  rw [(boundaryReClock76_16Norm (r*h^2)).property]

  change h^(22-16:ℕ)*(Rat.rawCast (Int.negOfNat 2280513882496) 1594323 +
      ((r*h^2) ^ Nat.rawCast 1 * NNRat.rawCast 38642214431872 14348907 +
        ((r*h^2) ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 5027075167090235) 3265173504 +
          ((r*h^2) ^ Nat.rawCast 3 * NNRat.rawCast 115014345418774361 264479053824 +
            ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 8228038022974059391) 114254951251968 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 3164816948286127745 514147280633856 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 118335823536562382989 296148833645101056 +
                  ((r*h^2) ^ Nat.rawCast 7 * Rat.rawCast (Int.negOfNat 204118511716521456295) 888446500935303168 +
                    ((r*h^2) ^ Nat.rawCast 8 * NNRat.rawCast 14217058126033528159781 383808888404050968576 +
                      ((r*h^2) ^ Nat.rawCast 9 * Rat.rawCast (Int.negOfNat 67296295829398153290253) 20725679973818752303104 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 60664994436785965393673 373062239528737541455872 +
                          ((r*h^2) ^ Nat.rawCast 11 *
                              Rat.rawCast (Int.negOfNat 4958718258837756564619) 1119186718586212624367616 +
                            ((r*h^2) ^ Nat.rawCast 12 * NNRat.rawCast 16690238053394868131 279796679646553156091904 +
                              ((r*h^2) ^ Nat.rawCast 13 *
                                  Rat.rawCast (Int.negOfNat 18624987334963153) 46632779941092192681984 +
                                ((r*h^2) ^ Nat.rawCast 14 * NNRat.rawCast 5106683045381761 3357560155758637873102848 +
                                  ((r*h^2) ^ Nat.rawCast 15 *
                                      Rat.rawCast (Int.negOfNat 10575635694101) 3357560155758637873102848 +
                                    ((r*h^2) ^ Nat.rawCast 16 * NNRat.rawCast 13269937105 5036340233637956809654272 +
                                      ((r*h^2) ^ Nat.rawCast 17 *
                                          Rat.rawCast (Int.negOfNat 4489513) 8498824144264052116291584 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryReLowColumn76_16,boundaryReHighColumn76_16]

  norm_num

  ring <;> simp


def boundaryReLowColumn76_17 (h r : ℂ) : ℂ :=
  (h^(22-17:ℕ)*(r*h^2)^0*(NNRat.rawCast 1490519130112 531441))

def boundaryReHighColumn76_17 (h r : ℂ) : ℂ :=
  (((((h^((22-17)+2*1-6:ℕ)*r^1*(Rat.rawCast (Int.negOfNat 1199292895232) 531441)) + (h^((22-17)+2*2-6:ℕ)*r^2*(NNRat.rawCast 8944684236155561 14693280768))) + ((h^((22-17)+2*3-6:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 8683150037025379) 264479053824)) + (h^((22-17)+2*4-6:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 187436597613540635) 9521245937664)))) + (((h^((22-17)+2*5-6:ℕ)*r^5*(NNRat.rawCast 2375754080265139879 342764853755904)) + (h^((22-17)+2*6-6:ℕ)*r^6*(Rat.rawCast (Int.negOfNat 12481067345496906211) 8226356490141696))) + ((h^((22-17)+2*7-6:ℕ)*r^7*(NNRat.rawCast 112471540232634081337 444223250467651584)) + (h^((22-17)+2*8-6:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 1903538488994906298383) 63968148067341828096))))) + ((((h^((22-17)+2*9-6:ℕ)*r^9*(NNRat.rawCast 975245758317349834675 431784999454557339648)) + (h^((22-17)+2*10-6:ℕ)*r^10*(Rat.rawCast (Int.negOfNat 2131079243627675191859) 20725679973818752303104))) + ((h^((22-17)+2*11-6:ℕ)*r^11*(NNRat.rawCast 2456531140649170829 971516248772754014208)) + (h^((22-17)+2*12-6:ℕ)*r^12*(Rat.rawCast (Int.negOfNat 323330429893532167) 11658194985273048170496)))) + (((h^((22-17)+2*13-6:ℕ)*r^13*(NNRat.rawCast 3650124895641203 34974584955819144511488)) + (h^((22-17)+2*14-6:ℕ)*r^14*(Rat.rawCast (Int.negOfNat 872295575383) 6908559991272917434368))) + ((h^((22-17)+2*15-6:ℕ)*r^15*(NNRat.rawCast 155131275655 279796679646553156091904)) + ((h^((22-17)+2*16-6:ℕ)*r^16*(Rat.rawCast (Int.negOfNat 604640819) 419695019469829734137856)) + (h^((22-17)+2*17-6:ℕ)*r^17*(NNRat.rawCast 13254793 22663531051370805643444224)))))))

theorem boundaryReClock76_17_split (h r : ℂ) :

    h^(22-17:ℕ)*boundaryReClock76_17 (r*h^2)=boundaryReLowColumn76_17 h r+h^6*boundaryReHighColumn76_17 h r := by

  rw [(boundaryReClock76_17Norm (r*h^2)).property]

  change h^(22-17:ℕ)*(NNRat.rawCast 1490519130112 531441 +
      ((r*h^2) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 1199292895232) 531441 +
        ((r*h^2) ^ Nat.rawCast 2 * NNRat.rawCast 8944684236155561 14693280768 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 8683150037025379) 264479053824 +
            ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 187436597613540635) 9521245937664 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 2375754080265139879 342764853755904 +
                ((r*h^2) ^ Nat.rawCast 6 * Rat.rawCast (Int.negOfNat 12481067345496906211) 8226356490141696 +
                  ((r*h^2) ^ Nat.rawCast 7 * NNRat.rawCast 112471540232634081337 444223250467651584 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 1903538488994906298383) 63968148067341828096 +
                      ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 975245758317349834675 431784999454557339648 +
                        ((r*h^2) ^ Nat.rawCast 10 *
                            Rat.rawCast (Int.negOfNat 2131079243627675191859) 20725679973818752303104 +
                          ((r*h^2) ^ Nat.rawCast 11 * NNRat.rawCast 2456531140649170829 971516248772754014208 +
                            ((r*h^2) ^ Nat.rawCast 12 *
                                Rat.rawCast (Int.negOfNat 323330429893532167) 11658194985273048170496 +
                              ((r*h^2) ^ Nat.rawCast 13 * NNRat.rawCast 3650124895641203 34974584955819144511488 +
                                ((r*h^2) ^ Nat.rawCast 14 * Rat.rawCast (Int.negOfNat 872295575383) 6908559991272917434368 +
                                  ((r*h^2) ^ Nat.rawCast 15 * NNRat.rawCast 155131275655 279796679646553156091904 +
                                    ((r*h^2) ^ Nat.rawCast 16 *
                                        Rat.rawCast (Int.negOfNat 604640819) 419695019469829734137856 +
                                      ((r*h^2) ^ Nat.rawCast 17 * NNRat.rawCast 13254793 22663531051370805643444224 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryReLowColumn76_17,boundaryReHighColumn76_17]

  norm_num

  ring <;> simp


def boundaryReLowColumn76_18 (h r : ℂ) : ℂ :=
  (h^(22-18:ℕ)*(r*h^2)^0*(NNRat.rawCast 68961173504 177147))

def boundaryReHighColumn76_18 (h r : ℂ) : ℂ :=
  (((((h^((22-18)+2*1-6:ℕ)*r^1*(Rat.rawCast (Int.negOfNat 375750311936) 531441)) + (h^((22-18)+2*2-6:ℕ)*r^2*(NNRat.rawCast 421183371165691 816293376))) + ((h^((22-18)+2*3-6:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 8457817153131913) 44079842304)) + (h^((22-18)+2*4-6:ℕ)*r^4*(NNRat.rawCast 133891807211385611 3173748645888)))) + (((h^((22-18)+2*5-6:ℕ)*r^5*(Rat.rawCast (Int.negOfNat 370690693657613579) 57127475625984)) + (h^((22-18)+2*6-6:ℕ)*r^6*(NNRat.rawCast 407819072049208669 457019805007872))) + ((h^((22-18)+2*7-6:ℕ)*r^7*(Rat.rawCast (Int.negOfNat 35745420741850372343) 296148833645101056)) + (h^((22-18)+2*8-6:ℕ)*r^8*(NNRat.rawCast 70229091406890953501 5330679005611819008))))) + ((((h^((22-18)+2*9-6:ℕ)*r^9*(Rat.rawCast (Int.negOfNat 1098982786589008091093) 1151426665212152905728)) + (h^((22-18)+2*10-6:ℕ)*r^10*(NNRat.rawCast 23374696935716413813 575713332606076452864))) + ((h^((22-18)+2*11-6:ℕ)*r^11*(Rat.rawCast (Int.negOfNat 13337893701029924839) 15544259980364064227328)) + (h^((22-18)+2*12-6:ℕ)*r^12*(NNRat.rawCast 152839347767787587 31088519960728128454656)))) + (((h^((22-18)+2*13-6:ℕ)*r^13*(NNRat.rawCast 165153809425039 2914548746318262042624)) + (h^((22-18)+2*14-6:ℕ)*r^14*(Rat.rawCast (Int.negOfNat 6559141010815) 11658194985273048170496))) + ((h^((22-18)+2*15-6:ℕ)*r^15*(NNRat.rawCast 161914001255 139898339823276578045952)) + ((h^((22-18)+2*16-6:ℕ)*r^16*(Rat.rawCast (Int.negOfNat 31648931) 93265559882184385363968)) + (h^((22-18)+2*17-6:ℕ)*r^17*(Rat.rawCast (Int.negOfNat 3202801) 22663531051370805643444224)))))))

theorem boundaryReClock76_18_split (h r : ℂ) :

    h^(22-18:ℕ)*boundaryReClock76_18 (r*h^2)=boundaryReLowColumn76_18 h r+h^6*boundaryReHighColumn76_18 h r := by

  rw [(boundaryReClock76_18Norm (r*h^2)).property]

  change h^(22-18:ℕ)*(NNRat.rawCast 68961173504 177147 +
      ((r*h^2) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 375750311936) 531441 +
        ((r*h^2) ^ Nat.rawCast 2 * NNRat.rawCast 421183371165691 816293376 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 8457817153131913) 44079842304 +
            ((r*h^2) ^ Nat.rawCast 4 * NNRat.rawCast 133891807211385611 3173748645888 +
              ((r*h^2) ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 370690693657613579) 57127475625984 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 407819072049208669 457019805007872 +
                  ((r*h^2) ^ Nat.rawCast 7 * Rat.rawCast (Int.negOfNat 35745420741850372343) 296148833645101056 +
                    ((r*h^2) ^ Nat.rawCast 8 * NNRat.rawCast 70229091406890953501 5330679005611819008 +
                      ((r*h^2) ^ Nat.rawCast 9 * Rat.rawCast (Int.negOfNat 1098982786589008091093) 1151426665212152905728 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 23374696935716413813 575713332606076452864 +
                          ((r*h^2) ^ Nat.rawCast 11 *
                              Rat.rawCast (Int.negOfNat 13337893701029924839) 15544259980364064227328 +
                            ((r*h^2) ^ Nat.rawCast 12 * NNRat.rawCast 152839347767787587 31088519960728128454656 +
                              ((r*h^2) ^ Nat.rawCast 13 * NNRat.rawCast 165153809425039 2914548746318262042624 +
                                ((r*h^2) ^ Nat.rawCast 14 * Rat.rawCast (Int.negOfNat 6559141010815) 11658194985273048170496 +
                                  ((r*h^2) ^ Nat.rawCast 15 * NNRat.rawCast 161914001255 139898339823276578045952 +
                                    ((r*h^2) ^ Nat.rawCast 16 * Rat.rawCast (Int.negOfNat 31648931) 93265559882184385363968 +
                                      ((r*h^2) ^ Nat.rawCast 17 *
                                          Rat.rawCast (Int.negOfNat 3202801) 22663531051370805643444224 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryReLowColumn76_18,boundaryReHighColumn76_18]

  norm_num

  ring <;> simp


def boundaryReLowColumn76_19 (h r : ℂ) : ℂ :=
  ((h^(22-19:ℕ)*(r*h^2)^0*(Rat.rawCast (Int.negOfNat 11127488512) 59049)) + (h^(22-19:ℕ)*(r*h^2)^1*(NNRat.rawCast 175354806272 531441)))

def boundaryReHighColumn76_19 (h r : ℂ) : ℂ :=
  (((((h^((22-19)+2*2-6:ℕ)*r^2*(Rat.rawCast (Int.negOfNat 89727402628717) 408146688)) + (h^((22-19)+2*3-6:ℕ)*r^3*(NNRat.rawCast 1048897307666959 14693280768))) + ((h^((22-19)+2*4-6:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 3295831149082177) 264479053824)) + (h^((22-19)+2*5-6:ℕ)*r^5*(NNRat.rawCast 16116813321962179 12694994583552)))) + (((h^((22-19)+2*6-6:ℕ)*r^6*(Rat.rawCast (Int.negOfNat 77928912523889347) 685529707511808)) + (h^((22-19)+2*7-6:ℕ)*r^7*(NNRat.rawCast 204117221675779999 12339534735212544))) + ((h^((22-19)+2*8-6:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 52291721529779) 24100653779712)) + (h^((22-19)+2*9-6:ℕ)*r^9*(NNRat.rawCast 3847406362216530181 23988055525253185536))))) + ((((h^((22-19)+2*10-6:ℕ)*r^10*(Rat.rawCast (Int.negOfNat 9326284373807451169) 1727139997818229358592)) + (h^((22-19)+2*11-6:ℕ)*r^11*(NNRat.rawCast 24568017717062699 5181419993454688075776))) + ((h^((22-19)+2*12-6:ℕ)*r^12*(NNRat.rawCast 22640030757368255 5181419993454688075776)) + (h^((22-19)+2*13-6:ℕ)*r^13*(Rat.rawCast (Int.negOfNat 710386886024143) 7772129990182032113664)))) + (((h^((22-19)+2*14-6:ℕ)*r^14*(NNRat.rawCast 9758298288875 15544259980364064227328)) + (h^((22-19)+2*15-6:ℕ)*r^15*(Rat.rawCast (Int.negOfNat 8144037407) 5181419993454688075776))) + ((h^((22-19)+2*16-6:ℕ)*r^16*(NNRat.rawCast 180714913 139898339823276578045952)) + (h^((22-19)+2*17-6:ℕ)*r^17*(Rat.rawCast (Int.negOfNat 434041) 1888627587614233803620352))))))

theorem boundaryReClock76_19_split (h r : ℂ) :

    h^(22-19:ℕ)*boundaryReClock76_19 (r*h^2)=boundaryReLowColumn76_19 h r+h^6*boundaryReHighColumn76_19 h r := by

  rw [(boundaryReClock76_19Norm (r*h^2)).property]

  change h^(22-19:ℕ)*(Rat.rawCast (Int.negOfNat 11127488512) 59049 +
      ((r*h^2) ^ Nat.rawCast 1 * NNRat.rawCast 175354806272 531441 +
        ((r*h^2) ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 89727402628717) 408146688 +
          ((r*h^2) ^ Nat.rawCast 3 * NNRat.rawCast 1048897307666959 14693280768 +
            ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 3295831149082177) 264479053824 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 16116813321962179 12694994583552 +
                ((r*h^2) ^ Nat.rawCast 6 * Rat.rawCast (Int.negOfNat 77928912523889347) 685529707511808 +
                  ((r*h^2) ^ Nat.rawCast 7 * NNRat.rawCast 204117221675779999 12339534735212544 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 52291721529779) 24100653779712 +
                      ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 3847406362216530181 23988055525253185536 +
                        ((r*h^2) ^ Nat.rawCast 10 * Rat.rawCast (Int.negOfNat 9326284373807451169) 1727139997818229358592 +
                          ((r*h^2) ^ Nat.rawCast 11 * NNRat.rawCast 24568017717062699 5181419993454688075776 +
                            ((r*h^2) ^ Nat.rawCast 12 * NNRat.rawCast 22640030757368255 5181419993454688075776 +
                              ((r*h^2) ^ Nat.rawCast 13 * Rat.rawCast (Int.negOfNat 710386886024143) 7772129990182032113664 +
                                ((r*h^2) ^ Nat.rawCast 14 * NNRat.rawCast 9758298288875 15544259980364064227328 +
                                  ((r*h^2) ^ Nat.rawCast 15 * Rat.rawCast (Int.negOfNat 8144037407) 5181419993454688075776 +
                                    ((r*h^2) ^ Nat.rawCast 16 * NNRat.rawCast 180714913 139898339823276578045952 +
                                      ((r*h^2) ^ Nat.rawCast 17 *
                                          Rat.rawCast (Int.negOfNat 434041) 1888627587614233803620352 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryReLowColumn76_19,boundaryReHighColumn76_19]

  norm_num

  ring <;> simp


def boundaryReLowColumn76_20 (h r : ℂ) : ℂ :=
  ((h^(22-20:ℕ)*(r*h^2)^0*(NNRat.rawCast 3489660928 19683)) + (h^(22-20:ℕ)*(r*h^2)^1*(Rat.rawCast (Int.negOfNat 1414529024) 6561)))

def boundaryReHighColumn76_20 (h r : ℂ) : ℂ :=
  (((((h^((22-20)+2*2-6:ℕ)*r^2*(NNRat.rawCast 3556367801657 34012224)) + (h^((22-20)+2*3-6:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 14723747455213) 612220032))) + ((h^((22-20)+2*4-6:ℕ)*r^4*(NNRat.rawCast 319944259319861 176319369216)) + (h^((22-20)+2*5-6:ℕ)*r^5*(NNRat.rawCast 603041593462733 1586874322944)))) + (((h^((22-20)+2*6-6:ℕ)*r^6*(Rat.rawCast (Int.negOfNat 1024458717848417) 8463329722368)) + (h^((22-20)+2*7-6:ℕ)*r^7*(NNRat.rawCast 33439102748176391 2056589122535424))) + ((h^((22-20)+2*8-6:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 412963346704651303) 296148833645101056)) + (h^((22-20)+2*9-6:ℕ)*r^9*(NNRat.rawCast 356624431433807509 3998009254208864256))))) + ((((h^((22-20)+2*10-6:ℕ)*r^10*(Rat.rawCast (Int.negOfNat 13692029644271483) 2998506940656648192)) + (h^((22-20)+2*11-6:ℕ)*r^11*(NNRat.rawCast 16911220892262683 95952222101012742144))) + ((h^((22-20)+2*12-6:ℕ)*r^12*(Rat.rawCast (Int.negOfNat 948973981549615) 215892499727278669824)) + (h^((22-20)+2*13-6:ℕ)*r^13*(NNRat.rawCast 76506878907493 1295354998363672018944)))) + (((h^((22-20)+2*14-6:ℕ)*r^14*(Rat.rawCast (Int.negOfNat 241881063457) 647677499181836009472)) + (h^((22-20)+2*15-6:ℕ)*r^15*(NNRat.rawCast 7830818323 7772129990182032113664))) + ((h^((22-20)+2*16-6:ℕ)*r^16*(Rat.rawCast (Int.negOfNat 1911013) 1943032497545508028416)) + (h^((22-20)+2*17-6:ℕ)*r^17*(NNRat.rawCast 11819 52461877433728716767232))))))

theorem boundaryReClock76_20_split (h r : ℂ) :

    h^(22-20:ℕ)*boundaryReClock76_20 (r*h^2)=boundaryReLowColumn76_20 h r+h^6*boundaryReHighColumn76_20 h r := by

  rw [(boundaryReClock76_20Norm (r*h^2)).property]

  change h^(22-20:ℕ)*(NNRat.rawCast 3489660928 19683 +
      ((r*h^2) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 1414529024) 6561 +
        ((r*h^2) ^ Nat.rawCast 2 * NNRat.rawCast 3556367801657 34012224 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 14723747455213) 612220032 +
            ((r*h^2) ^ Nat.rawCast 4 * NNRat.rawCast 319944259319861 176319369216 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 603041593462733 1586874322944 +
                ((r*h^2) ^ Nat.rawCast 6 * Rat.rawCast (Int.negOfNat 1024458717848417) 8463329722368 +
                  ((r*h^2) ^ Nat.rawCast 7 * NNRat.rawCast 33439102748176391 2056589122535424 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 412963346704651303) 296148833645101056 +
                      ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 356624431433807509 3998009254208864256 +
                        ((r*h^2) ^ Nat.rawCast 10 * Rat.rawCast (Int.negOfNat 13692029644271483) 2998506940656648192 +
                          ((r*h^2) ^ Nat.rawCast 11 * NNRat.rawCast 16911220892262683 95952222101012742144 +
                            ((r*h^2) ^ Nat.rawCast 12 * Rat.rawCast (Int.negOfNat 948973981549615) 215892499727278669824 +
                              ((r*h^2) ^ Nat.rawCast 13 * NNRat.rawCast 76506878907493 1295354998363672018944 +
                                ((r*h^2) ^ Nat.rawCast 14 * Rat.rawCast (Int.negOfNat 241881063457) 647677499181836009472 +
                                  ((r*h^2) ^ Nat.rawCast 15 * NNRat.rawCast 7830818323 7772129990182032113664 +
                                    ((r*h^2) ^ Nat.rawCast 16 * Rat.rawCast (Int.negOfNat 1911013) 1943032497545508028416 +
                                      ((r*h^2) ^ Nat.rawCast 17 * NNRat.rawCast 11819 52461877433728716767232 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryReLowColumn76_20,boundaryReHighColumn76_20]

  norm_num

  ring <;> simp


def boundaryReLowColumn76_21 (h r : ℂ) : ℂ :=
  ((h^(22-21:ℕ)*(r*h^2)^0*(Rat.rawCast (Int.negOfNat 268435456) 6561)) + ((h^(22-21:ℕ)*(r*h^2)^1*(NNRat.rawCast 721420288 19683)) + (h^(22-21:ℕ)*(r*h^2)^2*(Rat.rawCast (Int.negOfNat 1636827136) 177147))))

def boundaryReHighColumn76_21 (h r : ℂ) : ℂ :=
  ((((h^((22-21)+2*3-6:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 52125568405) 25509168)) + ((h^((22-21)+2*4-6:ℕ)*r^4*(NNRat.rawCast 3541517122583 1836660096)) + (h^((22-21)+2*5-6:ℕ)*r^5*(Rat.rawCast (Int.negOfNat 38816024418325) 66119763456)))) + (((h^((22-21)+2*6-6:ℕ)*r^6*(NNRat.rawCast 55848590646085 528958107648)) + (h^((22-21)+2*7-6:ℕ)*r^7*(Rat.rawCast (Int.negOfNat 544701864665579) 42845606719488))) + ((h^((22-21)+2*8-6:ℕ)*r^8*(NNRat.rawCast 1662459929233771 1542441841901568)) + (h^((22-21)+2*9-6:ℕ)*r^9*(Rat.rawCast (Int.negOfNat 10942077893885723) 166583718925369344))))) + ((((h^((22-21)+2*10-6:ℕ)*r^10*(NNRat.rawCast 956688408399985 333167437850738688)) + (h^((22-21)+2*11-6:ℕ)*r^11*(Rat.rawCast (Int.negOfNat 3146705839806479) 35982083287879778304))) + ((h^((22-21)+2*12-6:ℕ)*r^12*(NNRat.rawCast 250416060102239 143928333151519113216)) + (h^((22-21)+2*13-6:ℕ)*r^13*(Rat.rawCast (Int.negOfNat 8780817403579) 431784999454557339648)))) + (((h^((22-21)+2*14-6:ℕ)*r^14*(NNRat.rawCast 79807762975 647677499181836009472)) + (h^((22-21)+2*15-6:ℕ)*r^15*(Rat.rawCast (Int.negOfNat 24357643) 71964166575759556608))) + ((h^((22-21)+2*16-6:ℕ)*r^16*(NNRat.rawCast 446395 1295354998363672018944)) + (h^((22-21)+2*17-6:ℕ)*r^17*(Rat.rawCast (Int.negOfNat 8669) 104923754867457433534464))))))

theorem boundaryReClock76_21_split (h r : ℂ) :

    h^(22-21:ℕ)*boundaryReClock76_21 (r*h^2)=boundaryReLowColumn76_21 h r+h^6*boundaryReHighColumn76_21 h r := by

  rw [(boundaryReClock76_21Norm (r*h^2)).property]

  change h^(22-21:ℕ)*(Rat.rawCast (Int.negOfNat 268435456) 6561 +
      ((r*h^2) ^ Nat.rawCast 1 * NNRat.rawCast 721420288 19683 +
        ((r*h^2) ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 1636827136) 177147 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 52125568405) 25509168 +
            ((r*h^2) ^ Nat.rawCast 4 * NNRat.rawCast 3541517122583 1836660096 +
              ((r*h^2) ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 38816024418325) 66119763456 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 55848590646085 528958107648 +
                  ((r*h^2) ^ Nat.rawCast 7 * Rat.rawCast (Int.negOfNat 544701864665579) 42845606719488 +
                    ((r*h^2) ^ Nat.rawCast 8 * NNRat.rawCast 1662459929233771 1542441841901568 +
                      ((r*h^2) ^ Nat.rawCast 9 * Rat.rawCast (Int.negOfNat 10942077893885723) 166583718925369344 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 956688408399985 333167437850738688 +
                          ((r*h^2) ^ Nat.rawCast 11 * Rat.rawCast (Int.negOfNat 3146705839806479) 35982083287879778304 +
                            ((r*h^2) ^ Nat.rawCast 12 * NNRat.rawCast 250416060102239 143928333151519113216 +
                              ((r*h^2) ^ Nat.rawCast 13 * Rat.rawCast (Int.negOfNat 8780817403579) 431784999454557339648 +
                                ((r*h^2) ^ Nat.rawCast 14 * NNRat.rawCast 79807762975 647677499181836009472 +
                                  ((r*h^2) ^ Nat.rawCast 15 * Rat.rawCast (Int.negOfNat 24357643) 71964166575759556608 +
                                    ((r*h^2) ^ Nat.rawCast 16 * NNRat.rawCast 446395 1295354998363672018944 +
                                      ((r*h^2) ^ Nat.rawCast 17 * Rat.rawCast (Int.negOfNat 8669) 104923754867457433534464 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryReLowColumn76_21,boundaryReHighColumn76_21]

  norm_num

  ring <;> simp


def boundaryReLowColumn76_22 (h r : ℂ) : ℂ :=
  ((h^(22-22:ℕ)*(r*h^2)^1*(NNRat.rawCast 67108864 19683)) + (h^(22-22:ℕ)*(r*h^2)^2*(Rat.rawCast (Int.negOfNat 255852544) 59049)))

def boundaryReHighColumn76_22 (h r : ℂ) : ℂ :=
  ((((h^((22-22)+2*3-6:ℕ)*r^3*(NNRat.rawCast 1301807104 531441)) + ((h^((22-22)+2*4-6:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 1303347200) 1594323)) + (h^((22-22)+2*5-6:ℕ)*r^5*(NNRat.rawCast 7741010944 43046721)))) + (((h^((22-22)+2*6-6:ℕ)*r^6*(Rat.rawCast (Int.negOfNat 2730161975915) 99179645184)) + (h^((22-22)+2*7-6:ℕ)*r^7*(NNRat.rawCast 10758161428625 3570467226624))) + ((h^((22-22)+2*8-6:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 122502146602415) 514147280633856)) + (h^((22-22)+2*9-6:ℕ)*r^9*(NNRat.rawCast 31394877020285 2313662762852352))))) + ((((h^((22-22)+2*10-6:ℕ)*r^10*(Rat.rawCast (Int.negOfNat 1094746213523575) 1999004627104432128)) + (h^((22-22)+2*11-6:ℕ)*r^11*(NNRat.rawCast 45506594977039 2998506940656648192))) + ((h^((22-22)+2*12-6:ℕ)*r^12*(Rat.rawCast (Int.negOfNat 1644097616381) 5997013881313296384)) + (h^((22-22)+2*13-6:ℕ)*r^13*(NNRat.rawCast 80437533983 26986562465909833728)))) + (((h^((22-22)+2*14-6:ℕ)*r^14*(Rat.rawCast (Int.negOfNat 940876055) 53973124931819667456)) + (h^((22-22)+2*15-6:ℕ)*r^15*(NNRat.rawCast 1277153 26986562465909833728))) + ((h^((22-22)+2*16-6:ℕ)*r^16*(Rat.rawCast (Int.negOfNat 7765) 161919374795459002368)) + (h^((22-22)+2*17-6:ℕ)*r^17*(NNRat.rawCast 25 2185911559738696531968))))))

theorem boundaryReClock76_22_split (h r : ℂ) :

    h^(22-22:ℕ)*boundaryReClock76_22 (r*h^2)=boundaryReLowColumn76_22 h r+h^6*boundaryReHighColumn76_22 h r := by

  rw [(boundaryReClock76_22Norm (r*h^2)).property]

  change h^(22-22:ℕ)*((r*h^2) ^ Nat.rawCast 1 * NNRat.rawCast 67108864 19683 +
      ((r*h^2) ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 255852544) 59049 +
        ((r*h^2) ^ Nat.rawCast 3 * NNRat.rawCast 1301807104 531441 +
          ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 1303347200) 1594323 +
            ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 7741010944 43046721 +
              ((r*h^2) ^ Nat.rawCast 6 * Rat.rawCast (Int.negOfNat 2730161975915) 99179645184 +
                ((r*h^2) ^ Nat.rawCast 7 * NNRat.rawCast 10758161428625 3570467226624 +
                  ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 122502146602415) 514147280633856 +
                    ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 31394877020285 2313662762852352 +
                      ((r*h^2) ^ Nat.rawCast 10 * Rat.rawCast (Int.negOfNat 1094746213523575) 1999004627104432128 +
                        ((r*h^2) ^ Nat.rawCast 11 * NNRat.rawCast 45506594977039 2998506940656648192 +
                          ((r*h^2) ^ Nat.rawCast 12 * Rat.rawCast (Int.negOfNat 1644097616381) 5997013881313296384 +
                            ((r*h^2) ^ Nat.rawCast 13 * NNRat.rawCast 80437533983 26986562465909833728 +
                              ((r*h^2) ^ Nat.rawCast 14 * Rat.rawCast (Int.negOfNat 940876055) 53973124931819667456 +
                                ((r*h^2) ^ Nat.rawCast 15 * NNRat.rawCast 1277153 26986562465909833728 +
                                  ((r*h^2) ^ Nat.rawCast 16 * Rat.rawCast (Int.negOfNat 7765) 161919374795459002368 +
                                    ((r*h^2) ^ Nat.rawCast 17 * NNRat.rawCast 25 2185911559738696531968 + 0)))))))))))))))))=_

  dsimp only [boundaryReLowColumn76_22,boundaryReHighColumn76_22]

  norm_num

  ring <;> simp


def boundaryReLow76 (h r : ℂ) : ℂ :=
  (((((boundaryReLowColumn76_0 h r) + (boundaryReLowColumn76_1 h r)) + ((boundaryReLowColumn76_2 h r) + ((boundaryReLowColumn76_3 h r) + (boundaryReLowColumn76_4 h r)))) + (((boundaryReLowColumn76_5 h r) + ((boundaryReLowColumn76_6 h r) + (boundaryReLowColumn76_7 h r))) + ((boundaryReLowColumn76_8 h r) + ((boundaryReLowColumn76_9 h r) + (boundaryReLowColumn76_10 h r))))) + ((((boundaryReLowColumn76_11 h r) + ((boundaryReLowColumn76_12 h r) + (boundaryReLowColumn76_13 h r))) + ((boundaryReLowColumn76_14 h r) + ((boundaryReLowColumn76_15 h r) + (boundaryReLowColumn76_16 h r)))) + (((boundaryReLowColumn76_17 h r) + ((boundaryReLowColumn76_18 h r) + (boundaryReLowColumn76_19 h r))) + ((boundaryReLowColumn76_20 h r) + ((boundaryReLowColumn76_21 h r) + (boundaryReLowColumn76_22 h r))))))

def boundaryReHigh76 (h r : ℂ) : ℂ :=
  (((((boundaryReHighColumn76_0 h r) + (boundaryReHighColumn76_1 h r)) + ((boundaryReHighColumn76_2 h r) + ((boundaryReHighColumn76_3 h r) + (boundaryReHighColumn76_4 h r)))) + (((boundaryReHighColumn76_5 h r) + ((boundaryReHighColumn76_6 h r) + (boundaryReHighColumn76_7 h r))) + ((boundaryReHighColumn76_8 h r) + ((boundaryReHighColumn76_9 h r) + (boundaryReHighColumn76_10 h r))))) + ((((boundaryReHighColumn76_11 h r) + ((boundaryReHighColumn76_12 h r) + (boundaryReHighColumn76_13 h r))) + ((boundaryReHighColumn76_14 h r) + ((boundaryReHighColumn76_15 h r) + (boundaryReHighColumn76_16 h r)))) + (((boundaryReHighColumn76_17 h r) + ((boundaryReHighColumn76_18 h r) + (boundaryReHighColumn76_19 h r))) + ((boundaryReHighColumn76_20 h r) + ((boundaryReHighColumn76_21 h r) + (boundaryReHighColumn76_22 h r))))))

theorem boundaryReCompleteSplit76 (h r : ℂ) :

    boundaryCompactA75 h r=boundaryReLow76 h r+h^6*boundaryReHigh76 h r := by

  rw [boundaryReClockSum76_eq]

  dsimp only [boundaryReClockSum76,boundaryReClockBlock76_0,boundaryReClockBlock76_1,boundaryReClockBlock76_2]

  rw [boundaryReClock76_0_split,boundaryReClock76_1_split,boundaryReClock76_2_split,boundaryReClock76_3_split,boundaryReClock76_4_split,boundaryReClock76_5_split,boundaryReClock76_6_split,boundaryReClock76_7_split,boundaryReClock76_8_split,boundaryReClock76_9_split,boundaryReClock76_10_split,boundaryReClock76_11_split,boundaryReClock76_12_split,boundaryReClock76_13_split,boundaryReClock76_14_split,boundaryReClock76_15_split,boundaryReClock76_16_split,boundaryReClock76_17_split,boundaryReClock76_18_split,boundaryReClock76_19_split,boundaryReClock76_20_split,boundaryReClock76_21_split,boundaryReClock76_22_split]

  dsimp only [boundaryReLow76,boundaryReHigh76]

  ring


end

end HTGeometry.ThetaRatioInfinity
