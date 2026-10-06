import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.ClockIm

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

def boundaryImLowColumn76_0 (h r : ℂ) : ℂ :=
  0

def boundaryImHighColumn76_0 (h r : ℂ) : ℂ :=
  ((((h^((21-0)+2*0-5:ℕ)*r^0*(NNRat.rawCast 258052183 272097792)) + (h^((21-0)+2*1-5:ℕ)*r^1*(NNRat.rawCast 6510854519 9795520512))) + ((h^((21-0)+2*2-5:ℕ)*r^2*(Rat.rawCast (Int.negOfNat 186364574969) 1410554953728)) + ((h^((21-0)+2*3-5:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 1033797574409) 12694994583552)) + (h^((21-0)+2*4-5:ℕ)*r^4*(NNRat.rawCast 12105944831381 7312316880125952))))) + (((h^((21-0)+2*5-5:ℕ)*r^5*(NNRat.rawCast 130377163775405 65810851921133568)) + (h^((21-0)+2*6-5:ℕ)*r^6*(NNRat.rawCast 284835824941 3084883683803136))) + ((h^((21-0)+2*7-5:ℕ)*r^7*(Rat.rawCast (Int.negOfNat 47428789322903) 2665339502805909504)) + ((h^((21-0)+2*8-5:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 9987025493561) 5330679005611819008)) + (h^((21-0)+2*9-5:ℕ)*r^9*(NNRat.rawCast 63860187804325 431784999454557339648))))))

theorem boundaryImClock76_0_split (h r : ℂ) :

    h^(21-0:ℕ)*boundaryImClock76_0 (r*h^2)=boundaryImLowColumn76_0 h r+h^5*boundaryImHighColumn76_0 h r := by

  rw [(boundaryImClock76_0Norm (r*h^2)).property]

  change h^(21-0:ℕ)*(NNRat.rawCast 258052183 272097792 +
      ((r*h^2) ^ Nat.rawCast 1 * NNRat.rawCast 6510854519 9795520512 +
        ((r*h^2) ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 186364574969) 1410554953728 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 1033797574409) 12694994583552 +
            ((r*h^2) ^ Nat.rawCast 4 * NNRat.rawCast 12105944831381 7312316880125952 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 130377163775405 65810851921133568 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 284835824941 3084883683803136 +
                  ((r*h^2) ^ Nat.rawCast 7 * Rat.rawCast (Int.negOfNat 47428789322903) 2665339502805909504 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 9987025493561) 5330679005611819008 +
                      ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 63860187804325 431784999454557339648 + 0))))))))))=_

  dsimp only [boundaryImLowColumn76_0,boundaryImHighColumn76_0]

  norm_num

  ring <;> simp


def boundaryImLowColumn76_1 (h r : ℂ) : ℂ :=
  0

def boundaryImHighColumn76_1 (h r : ℂ) : ℂ :=
  ((((h^((21-1)+2*0-5:ℕ)*r^0*(NNRat.rawCast 347952563 15116544)) + (h^((21-1)+2*1-5:ℕ)*r^1*(NNRat.rawCast 133551734933 19591041024))) + ((h^((21-1)+2*2-5:ℕ)*r^2*(Rat.rawCast (Int.negOfNat 2312978499941) 470184984576)) + ((h^((21-1)+2*3-5:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 4421341459327) 5642219814912)) + (h^((21-1)+2*4-5:ℕ)*r^4*(NNRat.rawCast 1248266550682421 7312316880125952))))) + (((h^((21-1)+2*5-5:ℕ)*r^5*(NNRat.rawCast 1404956250307805 87747802561511424)) + ((h^((21-1)+2*6-5:ℕ)*r^6*(Rat.rawCast (Int.negOfNat 3334177576970155) 1184595334580404224)) + (h^((21-1)+2*7-5:ℕ)*r^7*(Rat.rawCast (Int.negOfNat 293867481139519) 2369190669160808448)))) + ((h^((21-1)+2*8-5:ℕ)*r^8*(NNRat.rawCast 12980928713958509 191904444202025484288)) + ((h^((21-1)+2*9-5:ℕ)*r^9*(Rat.rawCast (Int.negOfNat 1380000928479463) 215892499727278669824)) + (h^((21-1)+2*10-5:ℕ)*r^10*(NNRat.rawCast 2763132821290541 15544259980364064227328))))))

theorem boundaryImClock76_1_split (h r : ℂ) :

    h^(21-1:ℕ)*boundaryImClock76_1 (r*h^2)=boundaryImLowColumn76_1 h r+h^5*boundaryImHighColumn76_1 h r := by

  rw [(boundaryImClock76_1Norm (r*h^2)).property]

  change h^(21-1:ℕ)*(NNRat.rawCast 347952563 15116544 +
      ((r*h^2) ^ Nat.rawCast 1 * NNRat.rawCast 133551734933 19591041024 +
        ((r*h^2) ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 2312978499941) 470184984576 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 4421341459327) 5642219814912 +
            ((r*h^2) ^ Nat.rawCast 4 * NNRat.rawCast 1248266550682421 7312316880125952 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 1404956250307805 87747802561511424 +
                ((r*h^2) ^ Nat.rawCast 6 * Rat.rawCast (Int.negOfNat 3334177576970155) 1184595334580404224 +
                  ((r*h^2) ^ Nat.rawCast 7 * Rat.rawCast (Int.negOfNat 293867481139519) 2369190669160808448 +
                    ((r*h^2) ^ Nat.rawCast 8 * NNRat.rawCast 12980928713958509 191904444202025484288 +
                      ((r*h^2) ^ Nat.rawCast 9 * Rat.rawCast (Int.negOfNat 1380000928479463) 215892499727278669824 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 2763132821290541 15544259980364064227328 + 0)))))))))))=_

  dsimp only [boundaryImLowColumn76_1,boundaryImHighColumn76_1]

  norm_num

  ring <;> simp


def boundaryImLowColumn76_2 (h r : ℂ) : ℂ :=
  0

def boundaryImHighColumn76_2 (h r : ℂ) : ℂ :=
  ((((h^((21-2)+2*0-5:ℕ)*r^0*(NNRat.rawCast 17921951587 90699264)) + ((h^((21-2)+2*1-5:ℕ)*r^1*(Rat.rawCast (Int.negOfNat 596954040563) 19591041024)) + (h^((21-2)+2*2-5:ℕ)*r^2*(Rat.rawCast (Int.negOfNat 9899750372263) 235092492288)))) + ((h^((21-2)+2*3-5:ℕ)*r^3*(NNRat.rawCast 429128690993677 101559956668416)) + ((h^((21-2)+2*4-5:ℕ)*r^4*(NNRat.rawCast 264069531291865 304679870005248)) + (h^((21-2)+2*5-5:ℕ)*r^5*(Rat.rawCast (Int.negOfNat 7183393786654495) 29249267520503808))))) + (((h^((21-2)+2*6-5:ℕ)*r^6*(NNRat.rawCast 26953734167286863 3158920892214411264)) + ((h^((21-2)+2*7-5:ℕ)*r^7*(NNRat.rawCast 275968457834471069 42645432044894552064)) + (h^((21-2)+2*8-5:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 1709798571567940855) 1535235553616203874304)))) + ((h^((21-2)+2*9-5:ℕ)*r^9*(NNRat.rawCast 600569426788768079 6908559991272917434368)) + ((h^((21-2)+2*10-5:ℕ)*r^10*(Rat.rawCast (Int.negOfNat 46690054739436401) 13817119982545834868736)) + (h^((21-2)+2*11-5:ℕ)*r^11*(NNRat.rawCast 12177572871726983 279796679646553156091904))))))

theorem boundaryImClock76_2_split (h r : ℂ) :

    h^(21-2:ℕ)*boundaryImClock76_2 (r*h^2)=boundaryImLowColumn76_2 h r+h^5*boundaryImHighColumn76_2 h r := by

  rw [(boundaryImClock76_2Norm (r*h^2)).property]

  change h^(21-2:ℕ)*(NNRat.rawCast 17921951587 90699264 +
      ((r*h^2) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 596954040563) 19591041024 +
        ((r*h^2) ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 9899750372263) 235092492288 +
          ((r*h^2) ^ Nat.rawCast 3 * NNRat.rawCast 429128690993677 101559956668416 +
            ((r*h^2) ^ Nat.rawCast 4 * NNRat.rawCast 264069531291865 304679870005248 +
              ((r*h^2) ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 7183393786654495) 29249267520503808 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 26953734167286863 3158920892214411264 +
                  ((r*h^2) ^ Nat.rawCast 7 * NNRat.rawCast 275968457834471069 42645432044894552064 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 1709798571567940855) 1535235553616203874304 +
                      ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 600569426788768079 6908559991272917434368 +
                        ((r*h^2) ^ Nat.rawCast 10 * Rat.rawCast (Int.negOfNat 46690054739436401) 13817119982545834868736 +
                          ((r*h^2) ^ Nat.rawCast 11 * NNRat.rawCast 12177572871726983 279796679646553156091904 + 0))))))))))))=_

  dsimp only [boundaryImLowColumn76_2,boundaryImHighColumn76_2]

  norm_num

  ring <;> simp


def boundaryImLowColumn76_3 (h r : ℂ) : ℂ :=
  0

def boundaryImHighColumn76_3 (h r : ℂ) : ℂ :=
  ((((h^((21-3)+2*0-5:ℕ)*r^0*(NNRat.rawCast 4433739133 8503056)) + ((h^((21-3)+2*1-5:ℕ)*r^1*(Rat.rawCast (Int.negOfNat 5748284649001) 9795520512)) + (h^((21-3)+2*2-5:ℕ)*r^2*(Rat.rawCast (Int.negOfNat 25425160016345) 1410554953728)))) + ((h^((21-3)+2*3-5:ℕ)*r^3*(NNRat.rawCast 3798237873321137 101559956668416)) + ((h^((21-3)+2*4-5:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 36297245462526875) 3656158440062976)) + (h^((21-3)+2*5-5:ℕ)*r^5*(NNRat.rawCast 5189128058942131 14624633760251904))))) + (((h^((21-3)+2*6-5:ℕ)*r^6*(NNRat.rawCast 5839049016890081813 18953525353286467584)) + ((h^((21-3)+2*7-5:ℕ)*r^7*(Rat.rawCast (Int.negOfNat 85389012600265476499) 1364653825436625666048)) + (h^((21-3)+2*8-5:ℕ)*r^8*(NNRat.rawCast 9824350396117451999 1535235553616203874304)))) + (((h^((21-3)+2*9-5:ℕ)*r^9*(Rat.rawCast (Int.negOfNat 5056817636319640633) 12281884428929630994432)) + (h^((21-3)+2*10-5:ℕ)*r^10*(NNRat.rawCast 6199201151966658827 331610879581100036849664))) + ((h^((21-3)+2*11-5:ℕ)*r^11*(Rat.rawCast (Int.negOfNat 131755225973988043) 279796679646553156091904)) + (h^((21-3)+2*12-5:ℕ)*r^12*(NNRat.rawCast 259263771223410611 80581443738207308954468352))))))

theorem boundaryImClock76_3_split (h r : ℂ) :

    h^(21-3:ℕ)*boundaryImClock76_3 (r*h^2)=boundaryImLowColumn76_3 h r+h^5*boundaryImHighColumn76_3 h r := by

  rw [(boundaryImClock76_3Norm (r*h^2)).property]

  change h^(21-3:ℕ)*(NNRat.rawCast 4433739133 8503056 +
      ((r*h^2) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 5748284649001) 9795520512 +
        ((r*h^2) ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 25425160016345) 1410554953728 +
          ((r*h^2) ^ Nat.rawCast 3 * NNRat.rawCast 3798237873321137 101559956668416 +
            ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 36297245462526875) 3656158440062976 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 5189128058942131 14624633760251904 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 5839049016890081813 18953525353286467584 +
                  ((r*h^2) ^ Nat.rawCast 7 * Rat.rawCast (Int.negOfNat 85389012600265476499) 1364653825436625666048 +
                    ((r*h^2) ^ Nat.rawCast 8 * NNRat.rawCast 9824350396117451999 1535235553616203874304 +
                      ((r*h^2) ^ Nat.rawCast 9 * Rat.rawCast (Int.negOfNat 5056817636319640633) 12281884428929630994432 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 6199201151966658827 331610879581100036849664 +
                          ((r*h^2) ^ Nat.rawCast 11 * Rat.rawCast (Int.negOfNat 131755225973988043) 279796679646553156091904 +
                            ((r*h^2) ^ Nat.rawCast 12 * NNRat.rawCast 259263771223410611 80581443738207308954468352 +
                              0)))))))))))))=_

  dsimp only [boundaryImLowColumn76_3,boundaryImHighColumn76_3]

  norm_num

  ring <;> simp


def boundaryImLowColumn76_4 (h r : ℂ) : ℂ :=
  0

def boundaryImHighColumn76_4 (h r : ℂ) : ℂ :=
  ((((h^((21-4)+2*0-5:ℕ)*r^0*(Rat.rawCast (Int.negOfNat 526010560219) 272097792)) + ((h^((21-4)+2*1-5:ℕ)*r^1*(Rat.rawCast (Int.negOfNat 30790866766487) 19591041024)) + (h^((21-4)+2*2-5:ℕ)*r^2*(NNRat.rawCast 108460793539765 156728328192)))) + (((h^((21-4)+2*3-5:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 1052275049253833) 6347497291776)) + (h^((21-4)+2*4-5:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 24190683190474379) 7312316880125952))) + ((h^((21-4)+2*5-5:ℕ)*r^5*(NNRat.rawCast 768886023267285253 65810851921133568)) + (h^((21-4)+2*6-5:ℕ)*r^6*(Rat.rawCast (Int.negOfNat 87324025383315097261) 37907050706572935168))))) + (((h^((21-4)+2*7-5:ℕ)*r^7*(NNRat.rawCast 245316404231561318377 1364653825436625666048)) + ((h^((21-4)+2*8-5:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 326519775830088756265) 196510150862874095910912)) + (h^((21-4)+2*9-5:ℕ)*r^9*(Rat.rawCast (Int.negOfNat 917970537207242003641) 1768591357765866863198208)))) + (((h^((21-4)+2*10-5:ℕ)*r^10*(NNRat.rawCast 15082768023679164271 884295678882933431599104)) + (h^((21-4)+2*11-5:ℕ)*r^11*(NNRat.rawCast 43897479471302461307 71627949989517607959527424))) + ((h^((21-4)+2*12-5:ℕ)*r^12*(Rat.rawCast (Int.negOfNat 25566620683021306693) 1289303099811316943271493632)) + (h^((21-4)+2*13-5:ℕ)*r^13*(NNRat.rawCast 308296208412382897 3867909299433950829814480896))))))

theorem boundaryImClock76_4_split (h r : ℂ) :

    h^(21-4:ℕ)*boundaryImClock76_4 (r*h^2)=boundaryImLowColumn76_4 h r+h^5*boundaryImHighColumn76_4 h r := by

  rw [(boundaryImClock76_4Norm (r*h^2)).property]

  change h^(21-4:ℕ)*(Rat.rawCast (Int.negOfNat 526010560219) 272097792 +
      ((r*h^2) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 30790866766487) 19591041024 +
        ((r*h^2) ^ Nat.rawCast 2 * NNRat.rawCast 108460793539765 156728328192 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 1052275049253833) 6347497291776 +
            ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 24190683190474379) 7312316880125952 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 768886023267285253 65810851921133568 +
                ((r*h^2) ^ Nat.rawCast 6 * Rat.rawCast (Int.negOfNat 87324025383315097261) 37907050706572935168 +
                  ((r*h^2) ^ Nat.rawCast 7 * NNRat.rawCast 245316404231561318377 1364653825436625666048 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 326519775830088756265) 196510150862874095910912 +
                      ((r*h^2) ^ Nat.rawCast 9 * Rat.rawCast (Int.negOfNat 917970537207242003641) 1768591357765866863198208 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 15082768023679164271 884295678882933431599104 +
                          ((r*h^2) ^ Nat.rawCast 11 * NNRat.rawCast 43897479471302461307 71627949989517607959527424 +
                            ((r*h^2) ^ Nat.rawCast 12 *
                                Rat.rawCast (Int.negOfNat 25566620683021306693) 1289303099811316943271493632 +
                              ((r*h^2) ^ Nat.rawCast 13 * NNRat.rawCast 308296208412382897 3867909299433950829814480896 +
                                0))))))))))))))=_

  dsimp only [boundaryImLowColumn76_4,boundaryImHighColumn76_4]

  norm_num

  ring <;> simp


def boundaryImLowColumn76_5 (h r : ℂ) : ℂ :=
  0

def boundaryImHighColumn76_5 (h r : ℂ) : ℂ :=
  ((((h^((21-5)+2*0-5:ℕ)*r^0*(Rat.rawCast (Int.negOfNat 595134447329) 45349632)) + ((h^((21-5)+2*1-5:ℕ)*r^1*(NNRat.rawCast 68246754478747 19591041024)) + (h^((21-5)+2*2-5:ℕ)*r^2*(Rat.rawCast (Int.negOfNat 139280847775457) 235092492288)))) + (((h^((21-5)+2*3-5:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 653806045063829) 1586874322944)) + (h^((21-5)+2*4-5:ℕ)*r^4*(NNRat.rawCast 576135055035147667 1828079220031488))) + ((h^((21-5)+2*5-5:ℕ)*r^5*(Rat.rawCast (Int.negOfNat 30144349061698426627) 526486815369068544)) + (h^((21-5)+2*6-5:ℕ)*r^6*(NNRat.rawCast 8535111205340920181 4211894522952548352))))) + ((((h^((21-5)+2*7-5:ℕ)*r^7*(NNRat.rawCast 87540653190844684615 113721152119718805504)) + (h^((21-5)+2*8-5:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 27755368091845695374635) 196510150862874095910912))) + ((h^((21-5)+2*9-5:ℕ)*r^9*(NNRat.rawCast 6713613650610981410789 589530452588622287732736)) + (h^((21-5)+2*10-5:ℕ)*r^10*(Rat.rawCast (Int.negOfNat 1959259070331909946855) 3979330554973200442195968)))) + (((h^((21-5)+2*11-5:ℕ)*r^11*(NNRat.rawCast 701417487728543150753 71627949989517607959527424)) + (h^((21-5)+2*12-5:ℕ)*r^12*(Rat.rawCast (Int.negOfNat 53871599646351098255) 1289303099811316943271493632))) + ((h^((21-5)+2*13-5:ℕ)*r^13*(Rat.rawCast (Int.negOfNat 2666267823376143329) 11603727898301852489443442688)) + (h^((21-5)+2*14-5:ℕ)*r^14*(NNRat.rawCast 33325770944820067 52216775542358336202495492096))))))

theorem boundaryImClock76_5_split (h r : ℂ) :

    h^(21-5:ℕ)*boundaryImClock76_5 (r*h^2)=boundaryImLowColumn76_5 h r+h^5*boundaryImHighColumn76_5 h r := by

  rw [(boundaryImClock76_5Norm (r*h^2)).property]

  change h^(21-5:ℕ)*(Rat.rawCast (Int.negOfNat 595134447329) 45349632 +
      ((r*h^2) ^ Nat.rawCast 1 * NNRat.rawCast 68246754478747 19591041024 +
        ((r*h^2) ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 139280847775457) 235092492288 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 653806045063829) 1586874322944 +
            ((r*h^2) ^ Nat.rawCast 4 * NNRat.rawCast 576135055035147667 1828079220031488 +
              ((r*h^2) ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 30144349061698426627) 526486815369068544 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 8535111205340920181 4211894522952548352 +
                  ((r*h^2) ^ Nat.rawCast 7 * NNRat.rawCast 87540653190844684615 113721152119718805504 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 27755368091845695374635) 196510150862874095910912 +
                      ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 6713613650610981410789 589530452588622287732736 +
                        ((r*h^2) ^ Nat.rawCast 10 *
                            Rat.rawCast (Int.negOfNat 1959259070331909946855) 3979330554973200442195968 +
                          ((r*h^2) ^ Nat.rawCast 11 * NNRat.rawCast 701417487728543150753 71627949989517607959527424 +
                            ((r*h^2) ^ Nat.rawCast 12 *
                                Rat.rawCast (Int.negOfNat 53871599646351098255) 1289303099811316943271493632 +
                              ((r*h^2) ^ Nat.rawCast 13 *
                                  Rat.rawCast (Int.negOfNat 2666267823376143329) 11603727898301852489443442688 +
                                ((r*h^2) ^ Nat.rawCast 14 * NNRat.rawCast 33325770944820067 52216775542358336202495492096 +
                                  0)))))))))))))))=_

  dsimp only [boundaryImLowColumn76_5,boundaryImHighColumn76_5]

  norm_num

  ring <;> simp


def boundaryImLowColumn76_6 (h r : ℂ) : ℂ :=
  0

def boundaryImHighColumn76_6 (h r : ℂ) : ℂ :=
  (((((h^((21-6)+2*0-5:ℕ)*r^0*(Rat.rawCast (Int.negOfNat 435529901581) 30233088)) + (h^((21-6)+2*1-5:ℕ)*r^1*(NNRat.rawCast 21079894651837 3265173504))) + ((h^((21-6)+2*2-5:ℕ)*r^2*(Rat.rawCast (Int.negOfNat 9224477539639031) 1410554953728)) + (h^((21-6)+2*3-5:ℕ)*r^3*(NNRat.rawCast 124313652617230921 25389989167104)))) + (((h^((21-6)+2*4-5:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 927716298309686179) 1218719480020992)) + (h^((21-6)+2*5-5:ℕ)*r^5*(Rat.rawCast (Int.negOfNat 33720799191539834227) 526486815369068544))) + ((h^((21-6)+2*6-5:ℕ)*r^6*(NNRat.rawCast 1513072156662829446371 37907050706572935168)) + (h^((21-6)+2*7-5:ℕ)*r^7*(Rat.rawCast (Int.negOfNat 18092585090551991507689) 2729307650873251332096))))) + ((((h^((21-6)+2*8-5:ℕ)*r^8*(NNRat.rawCast 28957134332878925827015 49127537715718523977728)) + (h^((21-6)+2*9-5:ℕ)*r^9*(Rat.rawCast (Int.negOfNat 19521058616475826326175) 589530452588622287732736))) + ((h^((21-6)+2*10-5:ℕ)*r^10*(NNRat.rawCast 2685120561813462228287 1989665277486600221097984)) + (h^((21-6)+2*11-5:ℕ)*r^11*(Rat.rawCast (Int.negOfNat 2773143382194760538135) 71627949989517607959527424)))) + (((h^((21-6)+2*12-5:ℕ)*r^12*(NNRat.rawCast 3316585657773002819 6715120311517275746205696)) + (h^((21-6)+2*13-5:ℕ)*r^13*(Rat.rawCast (Int.negOfNat 18870706190402301557) 11603727898301852489443442688))) + ((h^((21-6)+2*14-5:ℕ)*r^14*(Rat.rawCast (Int.negOfNat 7005682798896131) 26108387771179168101247746048)) + (h^((21-6)+2*15-5:ℕ)*r^15*(NNRat.rawCast 20228983537427 14685968121288282056951857152))))))

theorem boundaryImClock76_6_split (h r : ℂ) :

    h^(21-6:ℕ)*boundaryImClock76_6 (r*h^2)=boundaryImLowColumn76_6 h r+h^5*boundaryImHighColumn76_6 h r := by

  rw [(boundaryImClock76_6Norm (r*h^2)).property]

  change h^(21-6:ℕ)*(Rat.rawCast (Int.negOfNat 435529901581) 30233088 +
      ((r*h^2) ^ Nat.rawCast 1 * NNRat.rawCast 21079894651837 3265173504 +
        ((r*h^2) ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 9224477539639031) 1410554953728 +
          ((r*h^2) ^ Nat.rawCast 3 * NNRat.rawCast 124313652617230921 25389989167104 +
            ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 927716298309686179) 1218719480020992 +
              ((r*h^2) ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 33720799191539834227) 526486815369068544 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 1513072156662829446371 37907050706572935168 +
                  ((r*h^2) ^ Nat.rawCast 7 * Rat.rawCast (Int.negOfNat 18092585090551991507689) 2729307650873251332096 +
                    ((r*h^2) ^ Nat.rawCast 8 * NNRat.rawCast 28957134332878925827015 49127537715718523977728 +
                      ((r*h^2) ^ Nat.rawCast 9 * Rat.rawCast (Int.negOfNat 19521058616475826326175) 589530452588622287732736 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 2685120561813462228287 1989665277486600221097984 +
                          ((r*h^2) ^ Nat.rawCast 11 *
                              Rat.rawCast (Int.negOfNat 2773143382194760538135) 71627949989517607959527424 +
                            ((r*h^2) ^ Nat.rawCast 12 * NNRat.rawCast 3316585657773002819 6715120311517275746205696 +
                              ((r*h^2) ^ Nat.rawCast 13 *
                                  Rat.rawCast (Int.negOfNat 18870706190402301557) 11603727898301852489443442688 +
                                ((r*h^2) ^ Nat.rawCast 14 *
                                    Rat.rawCast (Int.negOfNat 7005682798896131) 26108387771179168101247746048 +
                                  ((r*h^2) ^ Nat.rawCast 15 * NNRat.rawCast 20228983537427 14685968121288282056951857152 +
                                    0))))))))))))))))=_

  dsimp only [boundaryImLowColumn76_6,boundaryImHighColumn76_6]

  norm_num

  ring <;> simp


def boundaryImLowColumn76_7 (h r : ℂ) : ℂ :=
  0

def boundaryImHighColumn76_7 (h r : ℂ) : ℂ :=
  (((((h^((21-7)+2*0-5:ℕ)*r^0*(NNRat.rawCast 6485976127 354294)) + (h^((21-7)+2*1-5:ℕ)*r^1*(Rat.rawCast (Int.negOfNat 1512397466611) 51018336))) + ((h^((21-7)+2*2-5:ℕ)*r^2*(NNRat.rawCast 55906294622035723 1410554953728)) + (h^((21-7)+2*3-5:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 93733933937039437) 50779978334208)))) + (((h^((21-7)+2*4-5:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 11873006041514127179) 3656158440062976)) + (h^((21-7)+2*5-5:ℕ)*r^5*(NNRat.rawCast 188763308079355258709 175495605123022848))) + ((h^((21-7)+2*6-5:ℕ)*r^6*(Rat.rawCast (Int.negOfNat 1056501236337848358445) 6317841784428822528)) + (h^((21-7)+2*7-5:ℕ)*r^7*(NNRat.rawCast 34718044567770180348823 2729307650873251332096))))) + ((((h^((21-7)+2*8-5:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 389889974090594344295) 1535235553616203874304)) + (h^((21-7)+2*9-5:ℕ)*r^9*(Rat.rawCast (Int.negOfNat 14944578412970495446663) 589530452588622287732736))) + ((h^((21-7)+2*10-5:ℕ)*r^10*(NNRat.rawCast 1035895688294606674283 663221759162200073699328)) + (h^((21-7)+2*11-5:ℕ)*r^11*(Rat.rawCast (Int.negOfNat 52287251018809068667) 3979330554973200442195968)))) + (((h^((21-7)+2*12-5:ℕ)*r^12*(Rat.rawCast (Int.negOfNat 13428613985746398665) 23875983329839202653175808)) + (h^((21-7)+2*13-5:ℕ)*r^13*(NNRat.rawCast 24801621332876898391 3867909299433950829814480896))) + ((h^((21-7)+2*14-5:ℕ)*r^14*(Rat.rawCast (Int.negOfNat 220215020591630995) 17405591847452778734165164032)) + ((h^((21-7)+2*15-5:ℕ)*r^15*(NNRat.rawCast 432407062850917 234975489940612512911229714432)) + (h^((21-7)+2*16-5:ℕ)*r^16*(NNRat.rawCast 121763303179 264347426183189077025133428736)))))))

theorem boundaryImClock76_7_split (h r : ℂ) :

    h^(21-7:ℕ)*boundaryImClock76_7 (r*h^2)=boundaryImLowColumn76_7 h r+h^5*boundaryImHighColumn76_7 h r := by

  rw [(boundaryImClock76_7Norm (r*h^2)).property]

  change h^(21-7:ℕ)*(NNRat.rawCast 6485976127 354294 +
      ((r*h^2) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 1512397466611) 51018336 +
        ((r*h^2) ^ Nat.rawCast 2 * NNRat.rawCast 55906294622035723 1410554953728 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 93733933937039437) 50779978334208 +
            ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 11873006041514127179) 3656158440062976 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 188763308079355258709 175495605123022848 +
                ((r*h^2) ^ Nat.rawCast 6 * Rat.rawCast (Int.negOfNat 1056501236337848358445) 6317841784428822528 +
                  ((r*h^2) ^ Nat.rawCast 7 * NNRat.rawCast 34718044567770180348823 2729307650873251332096 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 389889974090594344295) 1535235553616203874304 +
                      ((r*h^2) ^ Nat.rawCast 9 * Rat.rawCast (Int.negOfNat 14944578412970495446663) 589530452588622287732736 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 1035895688294606674283 663221759162200073699328 +
                          ((r*h^2) ^ Nat.rawCast 11 *
                              Rat.rawCast (Int.negOfNat 52287251018809068667) 3979330554973200442195968 +
                            ((r*h^2) ^ Nat.rawCast 12 *
                                Rat.rawCast (Int.negOfNat 13428613985746398665) 23875983329839202653175808 +
                              ((r*h^2) ^ Nat.rawCast 13 * NNRat.rawCast 24801621332876898391 3867909299433950829814480896 +
                                ((r*h^2) ^ Nat.rawCast 14 *
                                    Rat.rawCast (Int.negOfNat 220215020591630995) 17405591847452778734165164032 +
                                  ((r*h^2) ^ Nat.rawCast 15 * NNRat.rawCast 432407062850917 234975489940612512911229714432 +
                                    ((r*h^2) ^ Nat.rawCast 16 * NNRat.rawCast 121763303179 264347426183189077025133428736 +
                                      0)))))))))))))))))=_

  dsimp only [boundaryImLowColumn76_7,boundaryImHighColumn76_7]

  norm_num

  ring <;> simp


def boundaryImLowColumn76_8 (h r : ℂ) : ℂ :=
  0

def boundaryImHighColumn76_8 (h r : ℂ) : ℂ :=
  (((((h^((21-8)+2*0-5:ℕ)*r^0*(NNRat.rawCast 12527514121 2834352)) + (h^((21-8)+2*1-5:ℕ)*r^1*(NNRat.rawCast 103937121884549 612220032))) + ((h^((21-8)+2*2-5:ℕ)*r^2*(NNRat.rawCast 22103980013276113 352638738432)) + (h^((21-8)+2*3-5:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 2764061372084054567) 50779978334208)))) + (((h^((21-8)+2*4-5:ℕ)*r^4*(NNRat.rawCast 112996085825195544631 7312316880125952)) + (h^((21-8)+2*5-5:ℕ)*r^5*(Rat.rawCast (Int.negOfNat 1152414434751891020869) 526486815369068544))) + ((h^((21-8)+2*6-5:ℕ)*r^6*(NNRat.rawCast 666591430340066365967 12635683568857645056)) + ((h^((21-8)+2*7-5:ℕ)*r^7*(NNRat.rawCast 40719454819020256086709 1364653825436625666048)) + (h^((21-8)+2*8-5:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 232348310570295420515159) 49127537715718523977728)))))) + ((((h^((21-8)+2*9-5:ℕ)*r^9*(NNRat.rawCast 25688294525482570044535 73691306573577785966592)) + (h^((21-8)+2*10-5:ℕ)*r^10*(Rat.rawCast (Int.negOfNat 116728468063016088656663) 7958661109946400884391936))) + ((h^((21-8)+2*11-5:ℕ)*r^11*(NNRat.rawCast 2698262661898301017619 7958661109946400884391936)) + (h^((21-8)+2*12-5:ℕ)*r^12*(Rat.rawCast (Int.negOfNat 667928938946074571671) 214883849968552823878582272)))) + (((h^((21-8)+2*13-5:ℕ)*r^13*(NNRat.rawCast 9061942056114367711 1933954649716975414907240448)) + (h^((21-8)+2*14-5:ℕ)*r^14*(NNRat.rawCast 518578544687791259 26108387771179168101247746048))) + ((h^((21-8)+2*15-5:ℕ)*r^15*(Rat.rawCast (Int.negOfNat 83858433492463) 3671492030322070514237964288)) + ((h^((21-8)+2*16-5:ℕ)*r^16*(NNRat.rawCast 99107635249 88115808727729692341711142912)) + (h^((21-8)+2*17-5:ℕ)*r^17*(Rat.rawCast (Int.negOfNat 5764801) 148695427228043855826637553664)))))))

theorem boundaryImClock76_8_split (h r : ℂ) :

    h^(21-8:ℕ)*boundaryImClock76_8 (r*h^2)=boundaryImLowColumn76_8 h r+h^5*boundaryImHighColumn76_8 h r := by

  rw [(boundaryImClock76_8Norm (r*h^2)).property]

  change h^(21-8:ℕ)*(NNRat.rawCast 12527514121 2834352 +
      ((r*h^2) ^ Nat.rawCast 1 * NNRat.rawCast 103937121884549 612220032 +
        ((r*h^2) ^ Nat.rawCast 2 * NNRat.rawCast 22103980013276113 352638738432 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 2764061372084054567) 50779978334208 +
            ((r*h^2) ^ Nat.rawCast 4 * NNRat.rawCast 112996085825195544631 7312316880125952 +
              ((r*h^2) ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 1152414434751891020869) 526486815369068544 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 666591430340066365967 12635683568857645056 +
                  ((r*h^2) ^ Nat.rawCast 7 * NNRat.rawCast 40719454819020256086709 1364653825436625666048 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 232348310570295420515159) 49127537715718523977728 +
                      ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 25688294525482570044535 73691306573577785966592 +
                        ((r*h^2) ^ Nat.rawCast 10 *
                            Rat.rawCast (Int.negOfNat 116728468063016088656663) 7958661109946400884391936 +
                          ((r*h^2) ^ Nat.rawCast 11 * NNRat.rawCast 2698262661898301017619 7958661109946400884391936 +
                            ((r*h^2) ^ Nat.rawCast 12 *
                                Rat.rawCast (Int.negOfNat 667928938946074571671) 214883849968552823878582272 +
                              ((r*h^2) ^ Nat.rawCast 13 * NNRat.rawCast 9061942056114367711 1933954649716975414907240448 +
                                ((r*h^2) ^ Nat.rawCast 14 * NNRat.rawCast 518578544687791259 26108387771179168101247746048 +
                                  ((r*h^2) ^ Nat.rawCast 15 *
                                      Rat.rawCast (Int.negOfNat 83858433492463) 3671492030322070514237964288 +
                                    ((r*h^2) ^ Nat.rawCast 16 * NNRat.rawCast 99107635249 88115808727729692341711142912 +
                                      ((r*h^2) ^ Nat.rawCast 17 *
                                          Rat.rawCast (Int.negOfNat 5764801) 148695427228043855826637553664 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryImLowColumn76_8,boundaryImHighColumn76_8]

  norm_num

  ring <;> simp


def boundaryImLowColumn76_9 (h r : ℂ) : ℂ :=
  0

def boundaryImHighColumn76_9 (h r : ℂ) : ℂ :=
  (((((h^((21-9)+2*0-5:ℕ)*r^0*(NNRat.rawCast 883107573397 2125764)) + (h^((21-9)+2*1-5:ℕ)*r^1*(NNRat.rawCast 33041956144873 51018336))) + ((h^((21-9)+2*2-5:ℕ)*r^2*(Rat.rawCast (Int.negOfNat 275023540930675933) 705277476864)) + (h^((21-9)+2*3-5:ℕ)*r^3*(NNRat.rawCast 4896217808561804567 50779978334208)))) + (((h^((21-9)+2*4-5:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 7877649846144796109) 1218719480020992)) + (h^((21-9)+2*5-5:ℕ)*r^5*(Rat.rawCast (Int.negOfNat 527453930303400479755) 131621703842267136))) + ((h^((21-9)+2*6-5:ℕ)*r^6*(NNRat.rawCast 12458970774516295731425 9476762676643233792)) + ((h^((21-9)+2*7-5:ℕ)*r^7*(Rat.rawCast (Int.negOfNat 24349283258521101697) 131621703842267136)) + (h^((21-9)+2*8-5:ℕ)*r^8*(NNRat.rawCast 90695834307067983738521 6140942214464815497216)))))) + ((((h^((21-9)+2*9-5:ℕ)*r^9*(Rat.rawCast (Int.negOfNat 109572784178532326192639) 147382613147155571933184)) + (h^((21-9)+2*10-5:ℕ)*r^10*(NNRat.rawCast 34450895411528530056647 1326443518324400147398656))) + ((h^((21-9)+2*11-5:ℕ)*r^11*(Rat.rawCast (Int.negOfNat 7912579175518822931677) 11937991664919601326587904)) + (h^((21-9)+2*12-5:ℕ)*r^12*(NNRat.rawCast 64669213170180283487 6715120311517275746205696)))) + (((h^((21-9)+2*13-5:ℕ)*r^13*(Rat.rawCast (Int.negOfNat 50458074112147463491) 966977324858487707453620224)) + (h^((21-9)+2*14-5:ℕ)*r^14*(NNRat.rawCast 614700438185525405 8702795923726389367082582016))) + ((h^((21-9)+2*15-5:ℕ)*r^15*(NNRat.rawCast 311279414855647 78325163313537504303743238144)) + ((h^((21-9)+2*16-5:ℕ)*r^16*(Rat.rawCast (Int.negOfNat 1010051842051) 176231617455459384683422285824)) + (h^((21-9)+2*17-5:ℕ)*r^17*(Rat.rawCast (Int.negOfNat 45294865) 198260569637391807768850071552)))))))

theorem boundaryImClock76_9_split (h r : ℂ) :

    h^(21-9:ℕ)*boundaryImClock76_9 (r*h^2)=boundaryImLowColumn76_9 h r+h^5*boundaryImHighColumn76_9 h r := by

  rw [(boundaryImClock76_9Norm (r*h^2)).property]

  change h^(21-9:ℕ)*(NNRat.rawCast 883107573397 2125764 +
      ((r*h^2) ^ Nat.rawCast 1 * NNRat.rawCast 33041956144873 51018336 +
        ((r*h^2) ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 275023540930675933) 705277476864 +
          ((r*h^2) ^ Nat.rawCast 3 * NNRat.rawCast 4896217808561804567 50779978334208 +
            ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 7877649846144796109) 1218719480020992 +
              ((r*h^2) ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 527453930303400479755) 131621703842267136 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 12458970774516295731425 9476762676643233792 +
                  ((r*h^2) ^ Nat.rawCast 7 * Rat.rawCast (Int.negOfNat 24349283258521101697) 131621703842267136 +
                    ((r*h^2) ^ Nat.rawCast 8 * NNRat.rawCast 90695834307067983738521 6140942214464815497216 +
                      ((r*h^2) ^ Nat.rawCast 9 *
                          Rat.rawCast (Int.negOfNat 109572784178532326192639) 147382613147155571933184 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 34450895411528530056647 1326443518324400147398656 +
                          ((r*h^2) ^ Nat.rawCast 11 *
                              Rat.rawCast (Int.negOfNat 7912579175518822931677) 11937991664919601326587904 +
                            ((r*h^2) ^ Nat.rawCast 12 * NNRat.rawCast 64669213170180283487 6715120311517275746205696 +
                              ((r*h^2) ^ Nat.rawCast 13 *
                                  Rat.rawCast (Int.negOfNat 50458074112147463491) 966977324858487707453620224 +
                                ((r*h^2) ^ Nat.rawCast 14 * NNRat.rawCast 614700438185525405 8702795923726389367082582016 +
                                  ((r*h^2) ^ Nat.rawCast 15 * NNRat.rawCast 311279414855647 78325163313537504303743238144 +
                                    ((r*h^2) ^ Nat.rawCast 16 *
                                        Rat.rawCast (Int.negOfNat 1010051842051) 176231617455459384683422285824 +
                                      ((r*h^2) ^ Nat.rawCast 17 *
                                          Rat.rawCast (Int.negOfNat 45294865) 198260569637391807768850071552 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryImLowColumn76_9,boundaryImHighColumn76_9]

  norm_num

  ring <;> simp


def boundaryImLowColumn76_10 (h r : ℂ) : ℂ :=
  0

def boundaryImHighColumn76_10 (h r : ℂ) : ℂ :=
  (((((h^((21-10)+2*0-5:ℕ)*r^0*(NNRat.rawCast 1056981749179 531441)) + (h^((21-10)+2*1-5:ℕ)*r^1*(Rat.rawCast (Int.negOfNat 11402695394645) 12754584))) + ((h^((21-10)+2*2-5:ℕ)*r^2*(NNRat.rawCast 12870230893791391 470184984576)) + (h^((21-10)+2*3-5:ℕ)*r^3*(NNRat.rawCast 7361937210697033783 50779978334208)))) + (((h^((21-10)+2*4-5:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 21005958712237110757) 228509902503936)) + (h^((21-10)+2*5-5:ℕ)*r^5*(NNRat.rawCast 277597856591286462035 10968475320188928))) + ((h^((21-10)+2*6-5:ℕ)*r^6*(Rat.rawCast (Int.negOfNat 8689755945636813856739) 2369190669160808448)) + ((h^((21-10)+2*7-5:ℕ)*r^7*(NNRat.rawCast 25228436644955969253769 85290864089789104128)) + (h^((21-10)+2*8-5:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 51781920294494115701321) 4093961476309876998144)))))) + ((((h^((21-10)+2*9-5:ℕ)*r^9*(NNRat.rawCast 22116772737772060641623 110536959860366678949888)) + (h^((21-10)+2*10-5:ℕ)*r^10*(NNRat.rawCast 5381776536547254490367 1989665277486600221097984))) + ((h^((21-10)+2*11-5:ℕ)*r^11*(Rat.rawCast (Int.negOfNat 2461295950530559967) 497416319371650055274496)) + (h^((21-10)+2*12-5:ℕ)*r^12*(Rat.rawCast (Int.negOfNat 286583397345662596295) 53720962492138205969645568)))) + (((h^((21-10)+2*13-5:ℕ)*r^13*(NNRat.rawCast 35277275277781064663 483488662429243853726810112)) + (h^((21-10)+2*14-5:ℕ)*r^14*(Rat.rawCast (Int.negOfNat 3045337463733407) 13430240623034551492411392))) + ((h^((21-10)+2*15-5:ℕ)*r^15*(NNRat.rawCast 5692246506325295 39162581656768752151871619072)) + ((h^((21-10)+2*16-5:ℕ)*r^16*(Rat.rawCast (Int.negOfNat 43152392675) 9790645414192188037967904768)) + (h^((21-10)+2*17-5:ℕ)*r^17*(NNRat.rawCast 823543 5507238045483105771356946432)))))))

theorem boundaryImClock76_10_split (h r : ℂ) :

    h^(21-10:ℕ)*boundaryImClock76_10 (r*h^2)=boundaryImLowColumn76_10 h r+h^5*boundaryImHighColumn76_10 h r := by

  rw [(boundaryImClock76_10Norm (r*h^2)).property]

  change h^(21-10:ℕ)*(NNRat.rawCast 1056981749179 531441 +
      ((r*h^2) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 11402695394645) 12754584 +
        ((r*h^2) ^ Nat.rawCast 2 * NNRat.rawCast 12870230893791391 470184984576 +
          ((r*h^2) ^ Nat.rawCast 3 * NNRat.rawCast 7361937210697033783 50779978334208 +
            ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 21005958712237110757) 228509902503936 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 277597856591286462035 10968475320188928 +
                ((r*h^2) ^ Nat.rawCast 6 * Rat.rawCast (Int.negOfNat 8689755945636813856739) 2369190669160808448 +
                  ((r*h^2) ^ Nat.rawCast 7 * NNRat.rawCast 25228436644955969253769 85290864089789104128 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 51781920294494115701321) 4093961476309876998144 +
                      ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 22116772737772060641623 110536959860366678949888 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 5381776536547254490367 1989665277486600221097984 +
                          ((r*h^2) ^ Nat.rawCast 11 *
                              Rat.rawCast (Int.negOfNat 2461295950530559967) 497416319371650055274496 +
                            ((r*h^2) ^ Nat.rawCast 12 *
                                Rat.rawCast (Int.negOfNat 286583397345662596295) 53720962492138205969645568 +
                              ((r*h^2) ^ Nat.rawCast 13 * NNRat.rawCast 35277275277781064663 483488662429243853726810112 +
                                ((r*h^2) ^ Nat.rawCast 14 *
                                    Rat.rawCast (Int.negOfNat 3045337463733407) 13430240623034551492411392 +
                                  ((r*h^2) ^ Nat.rawCast 15 * NNRat.rawCast 5692246506325295 39162581656768752151871619072 +
                                    ((r*h^2) ^ Nat.rawCast 16 *
                                        Rat.rawCast (Int.negOfNat 43152392675) 9790645414192188037967904768 +
                                      ((r*h^2) ^ Nat.rawCast 17 * NNRat.rawCast 823543 5507238045483105771356946432 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryImLowColumn76_10,boundaryImHighColumn76_10]

  norm_num

  ring <;> simp


def boundaryImLowColumn76_11 (h r : ℂ) : ℂ :=
  0

def boundaryImHighColumn76_11 (h r : ℂ) : ℂ :=
  (((((h^((21-11)+2*0-5:ℕ)*r^0*(NNRat.rawCast 387862448546 531441)) + (h^((21-11)+2*1-5:ℕ)*r^1*(Rat.rawCast (Int.negOfNat 1840027141589) 1062882))) + ((h^((21-11)+2*2-5:ℕ)*r^2*(NNRat.rawCast 647159530264634513 470184984576)) + (h^((21-11)+2*3-5:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 6917532202939476529) 8463329722368)))) + (((h^((21-11)+2*4-5:ℕ)*r^4*(NNRat.rawCast 882016326540022631215 3656158440062976)) + (h^((21-11)+2*5-5:ℕ)*r^5*(Rat.rawCast (Int.negOfNat 4545390810138934654915) 131621703842267136))) + ((h^((21-11)+2*6-5:ℕ)*r^6*(NNRat.rawCast 1439110332312322964399 789730223053602816)) + ((h^((21-11)+2*7-5:ℕ)*r^7*(NNRat.rawCast 11486925271511345542985 85290864089789104128)) + (h^((21-11)+2*8-5:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 177667019376837771900037) 6140942214464815497216)))))) + ((((h^((21-11)+2*9-5:ℕ)*r^9*(NNRat.rawCast 30116181184398691347919 13817119982545834868736)) + (h^((21-11)+2*10-5:ℕ)*r^10*(Rat.rawCast (Int.negOfNat 11290153506474494427131) 124354079842912513818624))) + ((h^((21-11)+2*11-5:ℕ)*r^11*(NNRat.rawCast 18890139867475262663467 8953493748689700994940928)) + (h^((21-11)+2*12-5:ℕ)*r^12*(Rat.rawCast (Int.negOfNat 578781432778087876871) 26860481246069102984822784)))) + (((h^((21-11)+2*13-5:ℕ)*r^13*(NNRat.rawCast 70339605743459581 1259085058409489202413568)) + (h^((21-11)+2*14-5:ℕ)*r^14*(NNRat.rawCast 100939973621334535 1087849490465798670885322752))) + ((h^((21-11)+2*15-5:ℕ)*r^15*(Rat.rawCast (Int.negOfNat 1470496489030303) 6527096942794792025311936512)) + ((h^((21-11)+2*16-5:ℕ)*r^16*(NNRat.rawCast 70124631227 2175698980931597341770645504)) + (h^((21-11)+2*17-5:ℕ)*r^17*(NNRat.rawCast 24118045 11014476090966211542713892864)))))))

theorem boundaryImClock76_11_split (h r : ℂ) :

    h^(21-11:ℕ)*boundaryImClock76_11 (r*h^2)=boundaryImLowColumn76_11 h r+h^5*boundaryImHighColumn76_11 h r := by

  rw [(boundaryImClock76_11Norm (r*h^2)).property]

  change h^(21-11:ℕ)*(NNRat.rawCast 387862448546 531441 +
      ((r*h^2) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 1840027141589) 1062882 +
        ((r*h^2) ^ Nat.rawCast 2 * NNRat.rawCast 647159530264634513 470184984576 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 6917532202939476529) 8463329722368 +
            ((r*h^2) ^ Nat.rawCast 4 * NNRat.rawCast 882016326540022631215 3656158440062976 +
              ((r*h^2) ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 4545390810138934654915) 131621703842267136 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 1439110332312322964399 789730223053602816 +
                  ((r*h^2) ^ Nat.rawCast 7 * NNRat.rawCast 11486925271511345542985 85290864089789104128 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 177667019376837771900037) 6140942214464815497216 +
                      ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 30116181184398691347919 13817119982545834868736 +
                        ((r*h^2) ^ Nat.rawCast 10 *
                            Rat.rawCast (Int.negOfNat 11290153506474494427131) 124354079842912513818624 +
                          ((r*h^2) ^ Nat.rawCast 11 * NNRat.rawCast 18890139867475262663467 8953493748689700994940928 +
                            ((r*h^2) ^ Nat.rawCast 12 *
                                Rat.rawCast (Int.negOfNat 578781432778087876871) 26860481246069102984822784 +
                              ((r*h^2) ^ Nat.rawCast 13 * NNRat.rawCast 70339605743459581 1259085058409489202413568 +
                                ((r*h^2) ^ Nat.rawCast 14 * NNRat.rawCast 100939973621334535 1087849490465798670885322752 +
                                  ((r*h^2) ^ Nat.rawCast 15 *
                                      Rat.rawCast (Int.negOfNat 1470496489030303) 6527096942794792025311936512 +
                                    ((r*h^2) ^ Nat.rawCast 16 * NNRat.rawCast 70124631227 2175698980931597341770645504 +
                                      ((r*h^2) ^ Nat.rawCast 17 * NNRat.rawCast 24118045 11014476090966211542713892864 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryImLowColumn76_11,boundaryImHighColumn76_11]

  norm_num

  ring <;> simp


def boundaryImLowColumn76_12 (h r : ℂ) : ℂ :=
  0

def boundaryImHighColumn76_12 (h r : ℂ) : ℂ :=
  (((((h^((21-12)+2*0-5:ℕ)*r^0*(Rat.rawCast (Int.negOfNat 1986570578980) 531441)) + (h^((21-12)+2*1-5:ℕ)*r^1*(NNRat.rawCast 16747353386672 4782969))) + ((h^((21-12)+2*2-5:ℕ)*r^2*(Rat.rawCast (Int.negOfNat 2331474115948712719) 705277476864)) + (h^((21-12)+2*3-5:ℕ)*r^3*(NNRat.rawCast 6565504311987924541 6347497291776)))) + (((h^((21-12)+2*4-5:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 289008052064981183) 4760622968832)) + (h^((21-12)+2*5-5:ℕ)*r^5*(Rat.rawCast (Int.negOfNat 384738771558344262133) 10968475320188928))) + ((h^((21-12)+2*6-5:ℕ)*r^6*(NNRat.rawCast 23806395026525945751893 2369190669160808448)) + ((h^((21-12)+2*7-5:ℕ)*r^7*(Rat.rawCast (Int.negOfNat 6416155732178433742061) 4738381338321616896)) + (h^((21-12)+2*8-5:ℕ)*r^8*(NNRat.rawCast 1797122151745559513509 15992037016835457024)))))) + ((((h^((21-12)+2*9-5:ℕ)*r^9*(Rat.rawCast (Int.negOfNat 168832731406995898136789) 27634239965091669737472)) + (h^((21-12)+2*10-5:ℕ)*r^10*(NNRat.rawCast 1688705555747040690811 7772129990182032113664))) + ((h^((21-12)+2*11-5:ℕ)*r^11*(Rat.rawCast (Int.negOfNat 5438552691705840303863) 1119186718586212624367616)) + (h^((21-12)+2*12-5:ℕ)*r^12*(NNRat.rawCast 808998414497480038439 13430240623034551492411392)))) + (((h^((21-12)+2*13-5:ℕ)*r^13*(Rat.rawCast (Int.negOfNat 6475796502468056641) 20145360934551827238617088)) + (h^((21-12)+2*14-5:ℕ)*r^14*(NNRat.rawCast 49987412050768249 90654124205483222573776896))) + ((h^((21-12)+2*15-5:ℕ)*r^15*(Rat.rawCast (Int.negOfNat 5024567107355) 33995296577056208465166336)) + ((h^((21-12)+2*16-5:ℕ)*r^16*(Rat.rawCast (Int.negOfNat 118522483457) 3263548471397396012655968256)) + (h^((21-12)+2*17-5:ℕ)*r^17*(Rat.rawCast (Int.negOfNat 991613) 917873007580517628559491072)))))))

theorem boundaryImClock76_12_split (h r : ℂ) :

    h^(21-12:ℕ)*boundaryImClock76_12 (r*h^2)=boundaryImLowColumn76_12 h r+h^5*boundaryImHighColumn76_12 h r := by

  rw [(boundaryImClock76_12Norm (r*h^2)).property]

  change h^(21-12:ℕ)*(Rat.rawCast (Int.negOfNat 1986570578980) 531441 +
      ((r*h^2) ^ Nat.rawCast 1 * NNRat.rawCast 16747353386672 4782969 +
        ((r*h^2) ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 2331474115948712719) 705277476864 +
          ((r*h^2) ^ Nat.rawCast 3 * NNRat.rawCast 6565504311987924541 6347497291776 +
            ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 289008052064981183) 4760622968832 +
              ((r*h^2) ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 384738771558344262133) 10968475320188928 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 23806395026525945751893 2369190669160808448 +
                  ((r*h^2) ^ Nat.rawCast 7 * Rat.rawCast (Int.negOfNat 6416155732178433742061) 4738381338321616896 +
                    ((r*h^2) ^ Nat.rawCast 8 * NNRat.rawCast 1797122151745559513509 15992037016835457024 +
                      ((r*h^2) ^ Nat.rawCast 9 * Rat.rawCast (Int.negOfNat 168832731406995898136789) 27634239965091669737472 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 1688705555747040690811 7772129990182032113664 +
                          ((r*h^2) ^ Nat.rawCast 11 *
                              Rat.rawCast (Int.negOfNat 5438552691705840303863) 1119186718586212624367616 +
                            ((r*h^2) ^ Nat.rawCast 12 * NNRat.rawCast 808998414497480038439 13430240623034551492411392 +
                              ((r*h^2) ^ Nat.rawCast 13 *
                                  Rat.rawCast (Int.negOfNat 6475796502468056641) 20145360934551827238617088 +
                                ((r*h^2) ^ Nat.rawCast 14 * NNRat.rawCast 49987412050768249 90654124205483222573776896 +
                                  ((r*h^2) ^ Nat.rawCast 15 *
                                      Rat.rawCast (Int.negOfNat 5024567107355) 33995296577056208465166336 +
                                    ((r*h^2) ^ Nat.rawCast 16 *
                                        Rat.rawCast (Int.negOfNat 118522483457) 3263548471397396012655968256 +
                                      ((r*h^2) ^ Nat.rawCast 17 *
                                          Rat.rawCast (Int.negOfNat 991613) 917873007580517628559491072 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryImLowColumn76_12,boundaryImHighColumn76_12]

  norm_num

  ring <;> simp


def boundaryImLowColumn76_13 (h r : ℂ) : ℂ :=
  0

def boundaryImHighColumn76_13 (h r : ℂ) : ℂ :=
  (((((h^((21-13)+2*0-5:ℕ)*r^0*(Rat.rawCast (Int.negOfNat 21387348920) 177147)) + (h^((21-13)+2*1-5:ℕ)*r^1*(Rat.rawCast (Int.negOfNat 3394832635850) 531441))) + ((h^((21-13)+2*2-5:ℕ)*r^2*(NNRat.rawCast 33228267578653235 39182082048)) + (h^((21-13)+2*3-5:ℕ)*r^3*(NNRat.rawCast 4339944743525504705 3173748645888)))) + (((h^((21-13)+2*4-5:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 162875512255664436413) 228509902503936)) + (h^((21-13)+2*5-5:ℕ)*r^5*(NNRat.rawCast 4431864761983718933 25389989167104))) + ((h^((21-13)+2*6-5:ℕ)*r^6*(Rat.rawCast (Int.negOfNat 31719383994419434377493) 1184595334580404224)) + ((h^((21-13)+2*7-5:ℕ)*r^7*(NNRat.rawCast 60167119326862619049737 21322716022447276032)) + (h^((21-13)+2*8-5:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 53454047900078358757529) 255872592269367312384)))))) + ((((h^((21-13)+2*9-5:ℕ)*r^9*(NNRat.rawCast 146598159183810982851329 13817119982545834868736)) + (h^((21-13)+2*10-5:ℕ)*r^10*(Rat.rawCast (Int.negOfNat 10918644408274193254457) 31088519960728128454656))) + ((h^((21-13)+2*11-5:ℕ)*r^11*(NNRat.rawCast 2678650914043232871421 373062239528737541455872)) + (h^((21-13)+2*12-5:ℕ)*r^12*(Rat.rawCast (Int.negOfNat 217482139099894383509) 2518170116818978404827136)))) + (((h^((21-13)+2*13-5:ℕ)*r^13*(NNRat.rawCast 582702428059627343 1119186718586212624367616)) + (h^((21-13)+2*14-5:ℕ)*r^14*(Rat.rawCast (Int.negOfNat 2067650774550053) 1678780077879318936551424))) + ((h^((21-13)+2*15-5:ℕ)*r^15*(NNRat.rawCast 1533163870865 1888627587614233803620352)) + ((h^((21-13)+2*16-5:ℕ)*r^16*(Rat.rawCast (Int.negOfNat 59507903) 3777255175228467607240704)) + (h^((21-13)+2*17-5:ℕ)*r^17*(Rat.rawCast (Int.negOfNat 2518649) 271962372616449667721330688)))))))

theorem boundaryImClock76_13_split (h r : ℂ) :

    h^(21-13:ℕ)*boundaryImClock76_13 (r*h^2)=boundaryImLowColumn76_13 h r+h^5*boundaryImHighColumn76_13 h r := by

  rw [(boundaryImClock76_13Norm (r*h^2)).property]

  change h^(21-13:ℕ)*(Rat.rawCast (Int.negOfNat 21387348920) 177147 +
      ((r*h^2) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 3394832635850) 531441 +
        ((r*h^2) ^ Nat.rawCast 2 * NNRat.rawCast 33228267578653235 39182082048 +
          ((r*h^2) ^ Nat.rawCast 3 * NNRat.rawCast 4339944743525504705 3173748645888 +
            ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 162875512255664436413) 228509902503936 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 4431864761983718933 25389989167104 +
                ((r*h^2) ^ Nat.rawCast 6 * Rat.rawCast (Int.negOfNat 31719383994419434377493) 1184595334580404224 +
                  ((r*h^2) ^ Nat.rawCast 7 * NNRat.rawCast 60167119326862619049737 21322716022447276032 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 53454047900078358757529) 255872592269367312384 +
                      ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 146598159183810982851329 13817119982545834868736 +
                        ((r*h^2) ^ Nat.rawCast 10 *
                            Rat.rawCast (Int.negOfNat 10918644408274193254457) 31088519960728128454656 +
                          ((r*h^2) ^ Nat.rawCast 11 * NNRat.rawCast 2678650914043232871421 373062239528737541455872 +
                            ((r*h^2) ^ Nat.rawCast 12 *
                                Rat.rawCast (Int.negOfNat 217482139099894383509) 2518170116818978404827136 +
                              ((r*h^2) ^ Nat.rawCast 13 * NNRat.rawCast 582702428059627343 1119186718586212624367616 +
                                ((r*h^2) ^ Nat.rawCast 14 *
                                    Rat.rawCast (Int.negOfNat 2067650774550053) 1678780077879318936551424 +
                                  ((r*h^2) ^ Nat.rawCast 15 * NNRat.rawCast 1533163870865 1888627587614233803620352 +
                                    ((r*h^2) ^ Nat.rawCast 16 *
                                        Rat.rawCast (Int.negOfNat 59507903) 3777255175228467607240704 +
                                      ((r*h^2) ^ Nat.rawCast 17 *
                                          Rat.rawCast (Int.negOfNat 2518649) 271962372616449667721330688 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryImLowColumn76_13,boundaryImHighColumn76_13]

  norm_num

  ring <;> simp


def boundaryImLowColumn76_14 (h r : ℂ) : ℂ :=
  0

def boundaryImHighColumn76_14 (h r : ℂ) : ℂ :=
  (((((h^((21-14)+2*0-5:ℕ)*r^0*(Rat.rawCast (Int.negOfNat 5134963891520) 531441)) + (h^((21-14)+2*1-5:ℕ)*r^1*(Rat.rawCast (Int.negOfNat 35095739829088) 4782969))) + ((h^((21-14)+2*2-5:ℕ)*r^2*(NNRat.rawCast 604606809589446209 58773123072)) + (h^((21-14)+2*3-5:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 7754220762129884119) 1586874322944)))) + (((h^((21-14)+2*4-5:ℕ)*r^4*(NNRat.rawCast 77952780941915794805 57127475625984)) + (h^((21-14)+2*5-5:ℕ)*r^5*(Rat.rawCast (Int.negOfNat 2142573310515031248481) 8226356490141696))) + ((h^((21-14)+2*6-5:ℕ)*r^6*(NNRat.rawCast 21476636981648276397217 592297667290202112)) + ((h^((21-14)+2*7-5:ℕ)*r^7*(Rat.rawCast (Int.negOfNat 39705129638856741393889) 10661358011223638016)) + (h^((21-14)+2*8-5:ℕ)*r^8*(NNRat.rawCast 26276211601461844624817 95952222101012742144)))))) + ((((h^((21-14)+2*9-5:ℕ)*r^9*(Rat.rawCast (Int.negOfNat 94151306940429308087569) 6908559991272917434368)) + (h^((21-14)+2*10-5:ℕ)*r^10*(NNRat.rawCast 8857539250109601020951 20725679973818752303104))) + ((h^((21-14)+2*11-5:ℕ)*r^11*(Rat.rawCast (Int.negOfNat 1099298370620383148009) 139898339823276578045952)) + (h^((21-14)+2*12-5:ℕ)*r^12*(NNRat.rawCast 139479190140860759029 1678780077879318936551424)))) + (((h^((21-14)+2*13-5:ℕ)*r^13*(Rat.rawCast (Int.negOfNat 90558618457966681) 186531119764368770727936)) + (h^((21-14)+2*14-5:ℕ)*r^14*(NNRat.rawCast 542692285773281 419695019469829734137856))) + ((h^((21-14)+2*15-5:ℕ)*r^15*(Rat.rawCast (Int.negOfNat 2875535311745) 2518170116818978404827136)) + ((h^((21-14)+2*16-5:ℕ)*r^16*(NNRat.rawCast 381175765 2518170116818978404827136)) + (h^((21-14)+2*17-5:ℕ)*r^17*(NNRat.rawCast 171157 16997648288528104232583168)))))))

theorem boundaryImClock76_14_split (h r : ℂ) :

    h^(21-14:ℕ)*boundaryImClock76_14 (r*h^2)=boundaryImLowColumn76_14 h r+h^5*boundaryImHighColumn76_14 h r := by

  rw [(boundaryImClock76_14Norm (r*h^2)).property]

  change h^(21-14:ℕ)*(Rat.rawCast (Int.negOfNat 5134963891520) 531441 +
      ((r*h^2) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 35095739829088) 4782969 +
        ((r*h^2) ^ Nat.rawCast 2 * NNRat.rawCast 604606809589446209 58773123072 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 7754220762129884119) 1586874322944 +
            ((r*h^2) ^ Nat.rawCast 4 * NNRat.rawCast 77952780941915794805 57127475625984 +
              ((r*h^2) ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 2142573310515031248481) 8226356490141696 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 21476636981648276397217 592297667290202112 +
                  ((r*h^2) ^ Nat.rawCast 7 * Rat.rawCast (Int.negOfNat 39705129638856741393889) 10661358011223638016 +
                    ((r*h^2) ^ Nat.rawCast 8 * NNRat.rawCast 26276211601461844624817 95952222101012742144 +
                      ((r*h^2) ^ Nat.rawCast 9 * Rat.rawCast (Int.negOfNat 94151306940429308087569) 6908559991272917434368 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 8857539250109601020951 20725679973818752303104 +
                          ((r*h^2) ^ Nat.rawCast 11 *
                              Rat.rawCast (Int.negOfNat 1099298370620383148009) 139898339823276578045952 +
                            ((r*h^2) ^ Nat.rawCast 12 * NNRat.rawCast 139479190140860759029 1678780077879318936551424 +
                              ((r*h^2) ^ Nat.rawCast 13 *
                                  Rat.rawCast (Int.negOfNat 90558618457966681) 186531119764368770727936 +
                                ((r*h^2) ^ Nat.rawCast 14 * NNRat.rawCast 542692285773281 419695019469829734137856 +
                                  ((r*h^2) ^ Nat.rawCast 15 *
                                      Rat.rawCast (Int.negOfNat 2875535311745) 2518170116818978404827136 +
                                    ((r*h^2) ^ Nat.rawCast 16 * NNRat.rawCast 381175765 2518170116818978404827136 +
                                      ((r*h^2) ^ Nat.rawCast 17 * NNRat.rawCast 171157 16997648288528104232583168 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryImLowColumn76_14,boundaryImHighColumn76_14]

  norm_num

  ring <;> simp


def boundaryImLowColumn76_15 (h r : ℂ) : ℂ :=
  0

def boundaryImHighColumn76_15 (h r : ℂ) : ℂ :=
  (((((h^((21-15)+2*0-5:ℕ)*r^0*(Rat.rawCast (Int.negOfNat 13348111443328) 531441)) + (h^((21-15)+2*1-5:ℕ)*r^1*(NNRat.rawCast 121624395483872 4782969))) + ((h^((21-15)+2*2-5:ℕ)*r^2*(Rat.rawCast (Int.negOfNat 1217373131793371045) 88159684608)) + (h^((21-15)+2*3-5:ℕ)*r^3*(NNRat.rawCast 1952289368708571257 396718580736)))) + (((h^((21-15)+2*4-5:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 142384554437803330775) 114254951251968)) + (h^((21-15)+2*5-5:ℕ)*r^5*(NNRat.rawCast 967959029416596061405 4113178245070848))) + ((h^((21-15)+2*6-5:ℕ)*r^6*(Rat.rawCast (Int.negOfNat 9913731652170419685223) 296148833645101056)) + ((h^((21-15)+2*7-5:ℕ)*r^7*(NNRat.rawCast 37298378120628914810429 10661358011223638016)) + (h^((21-15)+2*8-5:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 49254447986530343382971) 191904444202025484288)))))) + ((((h^((21-15)+2*9-5:ℕ)*r^9*(NNRat.rawCast 9566163794288972646301 767617776808101937152)) + (h^((21-15)+2*10-5:ℕ)*r^10*(Rat.rawCast (Int.negOfNat 40034513487506580839) 107946249863639334912))) + ((h^((21-15)+2*11-5:ℕ)*r^11*(NNRat.rawCast 573156975769303689767 93265559882184385363968)) + (h^((21-15)+2*12-5:ℕ)*r^12*(Rat.rawCast (Int.negOfNat 472692161127254209) 8743646238954786127872)))) + (((h^((21-15)+2*13-5:ℕ)*r^13*(NNRat.rawCast 5624931260846731 20725679973818752303104)) + (h^((21-15)+2*14-5:ℕ)*r^14*(Rat.rawCast (Int.negOfNat 213556033693019) 279796679646553156091904))) + ((h^((21-15)+2*15-5:ℕ)*r^15*(NNRat.rawCast 390571534915 419695019469829734137856)) + ((h^((21-15)+2*16-5:ℕ)*r^16*(Rat.rawCast (Int.negOfNat 839312737) 2518170116818978404827136)) + (h^((21-15)+2*17-5:ℕ)*r^17*(NNRat.rawCast 75943 5665882762842701410861056)))))))

theorem boundaryImClock76_15_split (h r : ℂ) :

    h^(21-15:ℕ)*boundaryImClock76_15 (r*h^2)=boundaryImLowColumn76_15 h r+h^5*boundaryImHighColumn76_15 h r := by

  rw [(boundaryImClock76_15Norm (r*h^2)).property]

  change h^(21-15:ℕ)*(Rat.rawCast (Int.negOfNat 13348111443328) 531441 +
      ((r*h^2) ^ Nat.rawCast 1 * NNRat.rawCast 121624395483872 4782969 +
        ((r*h^2) ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 1217373131793371045) 88159684608 +
          ((r*h^2) ^ Nat.rawCast 3 * NNRat.rawCast 1952289368708571257 396718580736 +
            ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 142384554437803330775) 114254951251968 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 967959029416596061405 4113178245070848 +
                ((r*h^2) ^ Nat.rawCast 6 * Rat.rawCast (Int.negOfNat 9913731652170419685223) 296148833645101056 +
                  ((r*h^2) ^ Nat.rawCast 7 * NNRat.rawCast 37298378120628914810429 10661358011223638016 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 49254447986530343382971) 191904444202025484288 +
                      ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 9566163794288972646301 767617776808101937152 +
                        ((r*h^2) ^ Nat.rawCast 10 * Rat.rawCast (Int.negOfNat 40034513487506580839) 107946249863639334912 +
                          ((r*h^2) ^ Nat.rawCast 11 * NNRat.rawCast 573156975769303689767 93265559882184385363968 +
                            ((r*h^2) ^ Nat.rawCast 12 * Rat.rawCast (Int.negOfNat 472692161127254209) 8743646238954786127872 +
                              ((r*h^2) ^ Nat.rawCast 13 * NNRat.rawCast 5624931260846731 20725679973818752303104 +
                                ((r*h^2) ^ Nat.rawCast 14 *
                                    Rat.rawCast (Int.negOfNat 213556033693019) 279796679646553156091904 +
                                  ((r*h^2) ^ Nat.rawCast 15 * NNRat.rawCast 390571534915 419695019469829734137856 +
                                    ((r*h^2) ^ Nat.rawCast 16 *
                                        Rat.rawCast (Int.negOfNat 839312737) 2518170116818978404827136 +
                                      ((r*h^2) ^ Nat.rawCast 17 * NNRat.rawCast 75943 5665882762842701410861056 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryImLowColumn76_15,boundaryImHighColumn76_15]

  norm_num

  ring <;> simp


def boundaryImLowColumn76_16 (h r : ℂ) : ℂ :=
  0

def boundaryImHighColumn76_16 (h r : ℂ) : ℂ :=
  (((((h^((21-16)+2*0-5:ℕ)*r^0*(NNRat.rawCast 2528462995456 531441)) + (h^((21-16)+2*1-5:ℕ)*r^1*(Rat.rawCast (Int.negOfNat 17099871361024) 1594323))) + ((h^((21-16)+2*2-5:ℕ)*r^2*(NNRat.rawCast 109574406966704513 14693280768)) + (h^((21-16)+2*3-5:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 375791054218986221) 132239526912)))) + (((h^((21-16)+2*4-5:ℕ)*r^4*(NNRat.rawCast 7018160380710446653 9521245937664)) + (h^((21-16)+2*5-5:ℕ)*r^5*(Rat.rawCast (Int.negOfNat 12218341762226909015) 85691213438976))) + ((h^((21-16)+2*6-5:ℕ)*r^6*(NNRat.rawCast 170844576349099210283 8226356490141696)) + ((h^((21-16)+2*7-5:ℕ)*r^7*(Rat.rawCast (Int.negOfNat 3909468748870903135145) 1776893001870606336)) + (h^((21-16)+2*8-5:ℕ)*r^8*(NNRat.rawCast 10312112752460434180081 63968148067341828096)))))) + ((((h^((21-16)+2*9-5:ℕ)*r^9*(Rat.rawCast (Int.negOfNat 13262401795358356899695) 1727139997818229358592)) + (h^((21-16)+2*10-5:ℕ)*r^10*(NNRat.rawCast 250827967197227695307 1151426665212152905728))) + ((h^((21-16)+2*11-5:ℕ)*r^11*(Rat.rawCast (Int.negOfNat 33197001440833200679) 10362839986909376151552)) + (h^((21-16)+2*12-5:ℕ)*r^12*(NNRat.rawCast 1901628107210069351 93265559882184385363968)))) + (((h^((21-16)+2*13-5:ℕ)*r^13*(Rat.rawCast (Int.negOfNat 576545030764577) 10362839986909376151552)) + (h^((21-16)+2*14-5:ℕ)*r^14*(NNRat.rawCast 2362716600431 15544259980364064227328))) + ((h^((21-16)+2*15-5:ℕ)*r^15*(Rat.rawCast (Int.negOfNat 58404148283) 139898339823276578045952)) + ((h^((21-16)+2*16-5:ℕ)*r^16*(NNRat.rawCast 144740387 419695019469829734137856)) + (h^((21-16)+2*17-5:ℕ)*r^17*(Rat.rawCast (Int.negOfNat 4859) 157385632301186150301696)))))))

theorem boundaryImClock76_16_split (h r : ℂ) :

    h^(21-16:ℕ)*boundaryImClock76_16 (r*h^2)=boundaryImLowColumn76_16 h r+h^5*boundaryImHighColumn76_16 h r := by

  rw [(boundaryImClock76_16Norm (r*h^2)).property]

  change h^(21-16:ℕ)*(NNRat.rawCast 2528462995456 531441 +
      ((r*h^2) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 17099871361024) 1594323 +
        ((r*h^2) ^ Nat.rawCast 2 * NNRat.rawCast 109574406966704513 14693280768 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 375791054218986221) 132239526912 +
            ((r*h^2) ^ Nat.rawCast 4 * NNRat.rawCast 7018160380710446653 9521245937664 +
              ((r*h^2) ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 12218341762226909015) 85691213438976 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 170844576349099210283 8226356490141696 +
                  ((r*h^2) ^ Nat.rawCast 7 * Rat.rawCast (Int.negOfNat 3909468748870903135145) 1776893001870606336 +
                    ((r*h^2) ^ Nat.rawCast 8 * NNRat.rawCast 10312112752460434180081 63968148067341828096 +
                      ((r*h^2) ^ Nat.rawCast 9 * Rat.rawCast (Int.negOfNat 13262401795358356899695) 1727139997818229358592 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 250827967197227695307 1151426665212152905728 +
                          ((r*h^2) ^ Nat.rawCast 11 *
                              Rat.rawCast (Int.negOfNat 33197001440833200679) 10362839986909376151552 +
                            ((r*h^2) ^ Nat.rawCast 12 * NNRat.rawCast 1901628107210069351 93265559882184385363968 +
                              ((r*h^2) ^ Nat.rawCast 13 * Rat.rawCast (Int.negOfNat 576545030764577) 10362839986909376151552 +
                                ((r*h^2) ^ Nat.rawCast 14 * NNRat.rawCast 2362716600431 15544259980364064227328 +
                                  ((r*h^2) ^ Nat.rawCast 15 *
                                      Rat.rawCast (Int.negOfNat 58404148283) 139898339823276578045952 +
                                    ((r*h^2) ^ Nat.rawCast 16 * NNRat.rawCast 144740387 419695019469829734137856 +
                                      ((r*h^2) ^ Nat.rawCast 17 * Rat.rawCast (Int.negOfNat 4859) 157385632301186150301696 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryImLowColumn76_16,boundaryImHighColumn76_16]

  norm_num

  ring <;> simp


def boundaryImLowColumn76_17 (h r : ℂ) : ℂ :=
  (h^(21-17:ℕ)*(r*h^2)^0*(Rat.rawCast (Int.negOfNat 1490519130112) 177147))

def boundaryImHighColumn76_17 (h r : ℂ) : ℂ :=
  (((((h^((21-17)+2*1-5:ℕ)*r^1*(NNRat.rawCast 4243318681600 531441)) + (h^((21-17)+2*2-5:ℕ)*r^2*(Rat.rawCast (Int.negOfNat 8177048138099647) 2448880128))) + ((h^((21-17)+2*3-5:ℕ)*r^3*(NNRat.rawCast 9851696752629245 11019960576)) + (h^((21-17)+2*4-5:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 39328210763218429) 198359290368)))) + (((h^((21-17)+2*5-5:ℕ)*r^5*(NNRat.rawCast 2298492282801997615 57127475625984)) + (h^((21-17)+2*6-5:ℕ)*r^6*(Rat.rawCast (Int.negOfNat 18269417046061876823) 2742118830047232))) + ((h^((21-17)+2*7-5:ℕ)*r^7*(NNRat.rawCast 116417121054948576299 148074416822550528)) + (h^((21-17)+2*8-5:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 81442488227202758647) 1332669751402954752))))) + ((((h^((21-17)+2*9-5:ℕ)*r^9*(NNRat.rawCast 1686909070369165695149 575713332606076452864)) + (h^((21-17)+2*10-5:ℕ)*r^10*(Rat.rawCast (Int.negOfNat 14906678686634376827) 191904444202025484288))) + ((h^((21-17)+2*11-5:ℕ)*r^11*(NNRat.rawCast 4434303375353566451 5181419993454688075776)) + (h^((21-17)+2*12-5:ℕ)*r^12*(NNRat.rawCast 4125741632104397 3886064995091016056832)))) + (((h^((21-17)+2*13-5:ℕ)*r^13*(Rat.rawCast (Int.negOfNat 105581799586967) 1727139997818229358592)) + (h^((21-17)+2*14-5:ℕ)*r^14*(NNRat.rawCast 3445782008879 15544259980364064227328))) + ((h^((21-17)+2*15-5:ℕ)*r^15*(Rat.rawCast (Int.negOfNat 6081876911) 46632779941092192681984)) + ((h^((21-17)+2*16-5:ℕ)*r^16*(Rat.rawCast (Int.negOfNat 1600535) 17487292477909572255744)) + (h^((21-17)+2*17-5:ℕ)*r^17*(NNRat.rawCast 15397 944313793807116901810176)))))))

theorem boundaryImClock76_17_split (h r : ℂ) :

    h^(21-17:ℕ)*boundaryImClock76_17 (r*h^2)=boundaryImLowColumn76_17 h r+h^5*boundaryImHighColumn76_17 h r := by

  rw [(boundaryImClock76_17Norm (r*h^2)).property]

  change h^(21-17:ℕ)*(Rat.rawCast (Int.negOfNat 1490519130112) 177147 +
      ((r*h^2) ^ Nat.rawCast 1 * NNRat.rawCast 4243318681600 531441 +
        ((r*h^2) ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 8177048138099647) 2448880128 +
          ((r*h^2) ^ Nat.rawCast 3 * NNRat.rawCast 9851696752629245 11019960576 +
            ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 39328210763218429) 198359290368 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 2298492282801997615 57127475625984 +
                ((r*h^2) ^ Nat.rawCast 6 * Rat.rawCast (Int.negOfNat 18269417046061876823) 2742118830047232 +
                  ((r*h^2) ^ Nat.rawCast 7 * NNRat.rawCast 116417121054948576299 148074416822550528 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 81442488227202758647) 1332669751402954752 +
                      ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 1686909070369165695149 575713332606076452864 +
                        ((r*h^2) ^ Nat.rawCast 10 * Rat.rawCast (Int.negOfNat 14906678686634376827) 191904444202025484288 +
                          ((r*h^2) ^ Nat.rawCast 11 * NNRat.rawCast 4434303375353566451 5181419993454688075776 +
                            ((r*h^2) ^ Nat.rawCast 12 * NNRat.rawCast 4125741632104397 3886064995091016056832 +
                              ((r*h^2) ^ Nat.rawCast 13 * Rat.rawCast (Int.negOfNat 105581799586967) 1727139997818229358592 +
                                ((r*h^2) ^ Nat.rawCast 14 * NNRat.rawCast 3445782008879 15544259980364064227328 +
                                  ((r*h^2) ^ Nat.rawCast 15 * Rat.rawCast (Int.negOfNat 6081876911) 46632779941092192681984 +
                                    ((r*h^2) ^ Nat.rawCast 16 * Rat.rawCast (Int.negOfNat 1600535) 17487292477909572255744 +
                                      ((r*h^2) ^ Nat.rawCast 17 * NNRat.rawCast 15397 944313793807116901810176 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryImLowColumn76_17,boundaryImHighColumn76_17]

  norm_num

  ring <;> simp


def boundaryImLowColumn76_18 (h r : ℂ) : ℂ :=
  (h^(21-18:ℕ)*(r*h^2)^0*(Rat.rawCast (Int.negOfNat 68961173504) 59049))

def boundaryImHighColumn76_18 (h r : ℂ) : ℂ :=
  (((((h^((21-18)+2*1-5:ℕ)*r^1*(NNRat.rawCast 30183784448 19683)) + (h^((21-18)+2*2-5:ℕ)*r^2*(Rat.rawCast (Int.negOfNat 16115551352825) 15116544))) + ((h^((21-18)+2*3-5:ℕ)*r^3*(NNRat.rawCast 3054395235517693 7346640384)) + (h^((21-18)+2*4-5:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 75013329306275) 816293376)))) + (((h^((21-18)+2*5-5:ℕ)*r^5*(NNRat.rawCast 69537024667402933 6347497291776)) + (h^((21-18)+2*6-5:ℕ)*r^6*(Rat.rawCast (Int.negOfNat 641425827648240931) 1371059415023616))) + ((h^((21-18)+2*7-5:ℕ)*r^7*(Rat.rawCast (Int.negOfNat 9948386981474227) 228509902503936)) + (h^((21-18)+2*8-5:ℕ)*r^8*(NNRat.rawCast 4106602093000574207 592297667290202112))))) + ((((h^((21-18)+2*9-5:ℕ)*r^9*(Rat.rawCast (Int.negOfNat 16652314821037002701) 47976111050506371072)) + (h^((21-18)+2*10-5:ℕ)*r^10*(NNRat.rawCast 130424793973229581 31984074033670914048))) + ((h^((21-18)+2*11-5:ℕ)*r^11*(NNRat.rawCast 51066298187104675 215892499727278669824)) + (h^((21-18)+2*12-5:ℕ)*r^12*(Rat.rawCast (Int.negOfNat 21107016783832027) 2590709996727344037888)))) + (((h^((21-18)+2*13-5:ℕ)*r^13*(NNRat.rawCast 24039534658013 287856666303038226432)) + (h^((21-18)+2*14-5:ℕ)*r^14*(Rat.rawCast (Int.negOfNat 203854763177) 647677499181836009472))) + ((h^((21-18)+2*15-5:ℕ)*r^15*(NNRat.rawCast 3249860191 7772129990182032113664)) + ((h^((21-18)+2*16-5:ℕ)*r^16*(Rat.rawCast (Int.negOfNat 1323349) 8743646238954786127872)) + (h^((21-18)+2*17-5:ℕ)*r^17*(NNRat.rawCast 245 39346408075296537575424)))))))

theorem boundaryImClock76_18_split (h r : ℂ) :

    h^(21-18:ℕ)*boundaryImClock76_18 (r*h^2)=boundaryImLowColumn76_18 h r+h^5*boundaryImHighColumn76_18 h r := by

  rw [(boundaryImClock76_18Norm (r*h^2)).property]

  change h^(21-18:ℕ)*(Rat.rawCast (Int.negOfNat 68961173504) 59049 +
      ((r*h^2) ^ Nat.rawCast 1 * NNRat.rawCast 30183784448 19683 +
        ((r*h^2) ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 16115551352825) 15116544 +
          ((r*h^2) ^ Nat.rawCast 3 * NNRat.rawCast 3054395235517693 7346640384 +
            ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 75013329306275) 816293376 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 69537024667402933 6347497291776 +
                ((r*h^2) ^ Nat.rawCast 6 * Rat.rawCast (Int.negOfNat 641425827648240931) 1371059415023616 +
                  ((r*h^2) ^ Nat.rawCast 7 * Rat.rawCast (Int.negOfNat 9948386981474227) 228509902503936 +
                    ((r*h^2) ^ Nat.rawCast 8 * NNRat.rawCast 4106602093000574207 592297667290202112 +
                      ((r*h^2) ^ Nat.rawCast 9 * Rat.rawCast (Int.negOfNat 16652314821037002701) 47976111050506371072 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 130424793973229581 31984074033670914048 +
                          ((r*h^2) ^ Nat.rawCast 11 * NNRat.rawCast 51066298187104675 215892499727278669824 +
                            ((r*h^2) ^ Nat.rawCast 12 * Rat.rawCast (Int.negOfNat 21107016783832027) 2590709996727344037888 +
                              ((r*h^2) ^ Nat.rawCast 13 * NNRat.rawCast 24039534658013 287856666303038226432 +
                                ((r*h^2) ^ Nat.rawCast 14 * Rat.rawCast (Int.negOfNat 203854763177) 647677499181836009472 +
                                  ((r*h^2) ^ Nat.rawCast 15 * NNRat.rawCast 3249860191 7772129990182032113664 +
                                    ((r*h^2) ^ Nat.rawCast 16 * Rat.rawCast (Int.negOfNat 1323349) 8743646238954786127872 +
                                      ((r*h^2) ^ Nat.rawCast 17 * NNRat.rawCast 245 39346408075296537575424 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryImLowColumn76_18,boundaryImHighColumn76_18]

  norm_num

  ring <;> simp


def boundaryImLowColumn76_19 (h r : ℂ) : ℂ :=
  ((h^(21-19:ℕ)*(r*h^2)^0*(NNRat.rawCast 11127488512 19683)) + (h^(21-19:ℕ)*(r*h^2)^1*(Rat.rawCast (Int.negOfNat 67443884032) 59049)))

def boundaryImHighColumn76_19 (h r : ℂ) : ℂ :=
  (((((h^((21-19)+2*2-5:ℕ)*r^2*(NNRat.rawCast 29795377108907 34012224)) + (h^((21-19)+2*3-5:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 437897528894045) 1224440064))) + ((h^((21-19)+2*4-5:ℕ)*r^4*(NNRat.rawCast 15644466017518031 176319369216)) + (h^((21-19)+2*5-5:ℕ)*r^5*(Rat.rawCast (Int.negOfNat 90981090116776051) 6347497291776)))) + (((h^((21-19)+2*6-5:ℕ)*r^6*(NNRat.rawCast 120098757160894523 76169967501312)) + (h^((21-19)+2*7-5:ℕ)*r^7*(Rat.rawCast (Int.negOfNat 507242181469983599) 4113178245070848))) + ((h^((21-19)+2*8-5:ℕ)*r^8*(NNRat.rawCast 2156268021145190891 296148833645101056)) + (h^((21-19)+2*9-5:ℕ)*r^9*(Rat.rawCast (Int.negOfNat 693695452583458339) 1999004627104432128))))) + ((((h^((21-19)+2*10-5:ℕ)*r^10*(NNRat.rawCast 1115739130466579 83291859462684672)) + (h^((21-19)+2*11-5:ℕ)*r^11*(Rat.rawCast (Int.negOfNat 17933669805700133) 47976111050506371072))) + ((h^((21-19)+2*12-5:ℕ)*r^12*(NNRat.rawCast 2719178938354451 431784999454557339648)) + (h^((21-19)+2*13-5:ℕ)*r^13*(Rat.rawCast (Int.negOfNat 1297901232197) 23988055525253185536)))) + (((h^((21-19)+2*14-5:ℕ)*r^14*(NNRat.rawCast 15237188201 71964166575759556608)) + (h^((21-19)+2*15-5:ℕ)*r^15*(Rat.rawCast (Int.negOfNat 1299579569) 3886064995091016056832))) + ((h^((21-19)+2*16-5:ℕ)*r^16*(NNRat.rawCast 638777 3886064995091016056832)) + (h^((21-19)+2*17-5:ℕ)*r^17*(Rat.rawCast (Int.negOfNat 47) 4371823119477393063936))))))

theorem boundaryImClock76_19_split (h r : ℂ) :

    h^(21-19:ℕ)*boundaryImClock76_19 (r*h^2)=boundaryImLowColumn76_19 h r+h^5*boundaryImHighColumn76_19 h r := by

  rw [(boundaryImClock76_19Norm (r*h^2)).property]

  change h^(21-19:ℕ)*(NNRat.rawCast 11127488512 19683 +
      ((r*h^2) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 67443884032) 59049 +
        ((r*h^2) ^ Nat.rawCast 2 * NNRat.rawCast 29795377108907 34012224 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 437897528894045) 1224440064 +
            ((r*h^2) ^ Nat.rawCast 4 * NNRat.rawCast 15644466017518031 176319369216 +
              ((r*h^2) ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 90981090116776051) 6347497291776 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 120098757160894523 76169967501312 +
                  ((r*h^2) ^ Nat.rawCast 7 * Rat.rawCast (Int.negOfNat 507242181469983599) 4113178245070848 +
                    ((r*h^2) ^ Nat.rawCast 8 * NNRat.rawCast 2156268021145190891 296148833645101056 +
                      ((r*h^2) ^ Nat.rawCast 9 * Rat.rawCast (Int.negOfNat 693695452583458339) 1999004627104432128 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 1115739130466579 83291859462684672 +
                          ((r*h^2) ^ Nat.rawCast 11 * Rat.rawCast (Int.negOfNat 17933669805700133) 47976111050506371072 +
                            ((r*h^2) ^ Nat.rawCast 12 * NNRat.rawCast 2719178938354451 431784999454557339648 +
                              ((r*h^2) ^ Nat.rawCast 13 * Rat.rawCast (Int.negOfNat 1297901232197) 23988055525253185536 +
                                ((r*h^2) ^ Nat.rawCast 14 * NNRat.rawCast 15237188201 71964166575759556608 +
                                  ((r*h^2) ^ Nat.rawCast 15 * Rat.rawCast (Int.negOfNat 1299579569) 3886064995091016056832 +
                                    ((r*h^2) ^ Nat.rawCast 16 * NNRat.rawCast 638777 3886064995091016056832 +
                                      ((r*h^2) ^ Nat.rawCast 17 * Rat.rawCast (Int.negOfNat 47) 4371823119477393063936 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryImLowColumn76_19,boundaryImHighColumn76_19]

  norm_num

  ring <;> simp


def boundaryImLowColumn76_20 (h r : ℂ) : ℂ :=
  ((h^(21-20:ℕ)*(r*h^2)^0*(Rat.rawCast (Int.negOfNat 3489660928) 6561)) + (h^(21-20:ℕ)*(r*h^2)^1*(NNRat.rawCast 14675869696 19683)))

def boundaryImHighColumn76_20 (h r : ℂ) : ℂ :=
  (((((h^((21-20)+2*2-5:ℕ)*r^2*(Rat.rawCast (Int.negOfNat 82847596544) 177147)) + (h^((21-20)+2*3-5:ℕ)*r^3*(NNRat.rawCast 4398482249537 25509168))) + ((h^((21-20)+2*4-5:ℕ)*r^4*(Rat.rawCast (Int.negOfNat 76317551083573) 1836660096)) + (h^((21-20)+2*5-5:ℕ)*r^5*(NNRat.rawCast 114351004022381 16529940864)))) + (((h^((21-20)+2*6-5:ℕ)*r^6*(Rat.rawCast (Int.negOfNat 1304943382921777) 1586874322944)) + (h^((21-20)+2*7-5:ℕ)*r^7*(NNRat.rawCast 12206930250593419 171382426877952))) + ((h^((21-20)+2*8-5:ℕ)*r^8*(Rat.rawCast (Int.negOfNat 7004604422418047) 1542441841901568)) + (h^((21-20)+2*9-5:ℕ)*r^9*(NNRat.rawCast 141722042087919145 666334875701477376))))) + ((((h^((21-20)+2*10-5:ℕ)*r^10*(Rat.rawCast (Int.negOfNat 3182611997616607) 444223250467651584)) + (h^((21-20)+2*11-5:ℕ)*r^11*(NNRat.rawCast 1980514142210113 11994027762626592768))) + ((h^((21-20)+2*12-5:ℕ)*r^12*(Rat.rawCast (Int.negOfNat 171678661461703) 71964166575759556608)) + (h^((21-20)+2*13-5:ℕ)*r^13*(NNRat.rawCast 12789770267 666334875701477376)))) + (((h^((21-20)+2*14-5:ℕ)*r^14*(Rat.rawCast (Int.negOfNat 2047532911) 26986562465909833728)) + (h^((21-20)+2*15-5:ℕ)*r^15*(NNRat.rawCast 40807745 323838749590918004736))) + ((h^((21-20)+2*16-5:ℕ)*r^16*(Rat.rawCast (Int.negOfNat 4747) 71964166575759556608)) + (h^((21-20)+2*17-5:ℕ)*r^17*(NNRat.rawCast 5 1092955779869348265984))))))

theorem boundaryImClock76_20_split (h r : ℂ) :

    h^(21-20:ℕ)*boundaryImClock76_20 (r*h^2)=boundaryImLowColumn76_20 h r+h^5*boundaryImHighColumn76_20 h r := by

  rw [(boundaryImClock76_20Norm (r*h^2)).property]

  change h^(21-20:ℕ)*(Rat.rawCast (Int.negOfNat 3489660928) 6561 +
      ((r*h^2) ^ Nat.rawCast 1 * NNRat.rawCast 14675869696 19683 +
        ((r*h^2) ^ Nat.rawCast 2 * Rat.rawCast (Int.negOfNat 82847596544) 177147 +
          ((r*h^2) ^ Nat.rawCast 3 * NNRat.rawCast 4398482249537 25509168 +
            ((r*h^2) ^ Nat.rawCast 4 * Rat.rawCast (Int.negOfNat 76317551083573) 1836660096 +
              ((r*h^2) ^ Nat.rawCast 5 * NNRat.rawCast 114351004022381 16529940864 +
                ((r*h^2) ^ Nat.rawCast 6 * Rat.rawCast (Int.negOfNat 1304943382921777) 1586874322944 +
                  ((r*h^2) ^ Nat.rawCast 7 * NNRat.rawCast 12206930250593419 171382426877952 +
                    ((r*h^2) ^ Nat.rawCast 8 * Rat.rawCast (Int.negOfNat 7004604422418047) 1542441841901568 +
                      ((r*h^2) ^ Nat.rawCast 9 * NNRat.rawCast 141722042087919145 666334875701477376 +
                        ((r*h^2) ^ Nat.rawCast 10 * Rat.rawCast (Int.negOfNat 3182611997616607) 444223250467651584 +
                          ((r*h^2) ^ Nat.rawCast 11 * NNRat.rawCast 1980514142210113 11994027762626592768 +
                            ((r*h^2) ^ Nat.rawCast 12 * Rat.rawCast (Int.negOfNat 171678661461703) 71964166575759556608 +
                              ((r*h^2) ^ Nat.rawCast 13 * NNRat.rawCast 12789770267 666334875701477376 +
                                ((r*h^2) ^ Nat.rawCast 14 * Rat.rawCast (Int.negOfNat 2047532911) 26986562465909833728 +
                                  ((r*h^2) ^ Nat.rawCast 15 * NNRat.rawCast 40807745 323838749590918004736 +
                                    ((r*h^2) ^ Nat.rawCast 16 * Rat.rawCast (Int.negOfNat 4747) 71964166575759556608 +
                                      ((r*h^2) ^ Nat.rawCast 17 * NNRat.rawCast 5 1092955779869348265984 + 0))))))))))))))))))=_

  dsimp only [boundaryImLowColumn76_20,boundaryImHighColumn76_20]

  norm_num

  ring <;> simp


def boundaryImLowColumn76_21 (h r : ℂ) : ℂ :=
  ((h^(21-21:ℕ)*(r*h^2)^0*(NNRat.rawCast 268435456 2187)) + ((h^(21-21:ℕ)*(r*h^2)^1*(Rat.rawCast (Int.negOfNat 1090519040) 6561)) + (h^(21-21:ℕ)*(r*h^2)^2*(NNRat.rawCast 5924454400 59049))))

def boundaryImHighColumn76_21 (h r : ℂ) : ℂ :=
  ((((h^((21-21)+2*3-5:ℕ)*r^3*(Rat.rawCast (Int.negOfNat 2116157440) 59049)) + ((h^((21-21)+2*4-5:ℕ)*r^4*(NNRat.rawCast 40487047168 4782969)) + (h^((21-21)+2*5-5:ℕ)*r^5*(Rat.rawCast (Int.negOfNat 60155799296) 43046721)))) + (((h^((21-21)+2*6-5:ℕ)*r^6*(NNRat.rawCast 16458456017087 99179645184)) + (h^((21-21)+2*7-5:ℕ)*r^7*(Rat.rawCast (Int.negOfNat 3202435542593) 223154201664))) + ((h^((21-21)+2*8-5:ℕ)*r^8*(NNRat.rawCast 464622800108815 514147280633856)) + (h^((21-21)+2*9-5:ℕ)*r^9*(Rat.rawCast (Int.negOfNat 2273787291250585) 55527906308456448))))) + ((((h^((21-21)+2*10-5:ℕ)*r^10*(NNRat.rawCast 96411338058443 74037208411275264)) + (h^((21-21)+2*11-5:ℕ)*r^11*(Rat.rawCast (Int.negOfNat 27853481344505) 999502313552216064))) + ((h^((21-21)+2*12-5:ℕ)*r^12*(NNRat.rawCast 140944386775 374813367582081024)) + (h^((21-21)+2*13-5:ℕ)*r^13*(Rat.rawCast (Int.negOfNat 5818211165) 1999004627104432128)))) + (((h^((21-21)+2*14-5:ℕ)*r^14*(NNRat.rawCast 204815881 17991041643939889152)) + (h^((21-21)+2*15-5:ℕ)*r^15*(Rat.rawCast (Int.negOfNat 255391) 13493281232954916864))) + ((h^((21-21)+2*16-5:ℕ)*r^16*(NNRat.rawCast 803 80959687397729501184)) + (h^((21-21)+2*17-5:ℕ)*r^17*(Rat.rawCast (Int.negOfNat 1) 1457274373159131021312))))))

theorem boundaryImClock76_21_split (h r : ℂ) :

    h^(21-21:ℕ)*boundaryImClock76_21 (r*h^2)=boundaryImLowColumn76_21 h r+h^5*boundaryImHighColumn76_21 h r := by

  rw [(boundaryImClock76_21Norm (r*h^2)).property]

  change h^(21-21:ℕ)*(NNRat.rawCast 268435456 2187 +
      ((r*h^2) ^ Nat.rawCast 1 * Rat.rawCast (Int.negOfNat 1090519040) 6561 +
        ((r*h^2) ^ Nat.rawCast 2 * NNRat.rawCast 5924454400 59049 +
          ((r*h^2) ^ Nat.rawCast 3 * Rat.rawCast (Int.negOfNat 2116157440) 59049 +
            ((r*h^2) ^ Nat.rawCast 4 * NNRat.rawCast 40487047168 4782969 +
              ((r*h^2) ^ Nat.rawCast 5 * Rat.rawCast (Int.negOfNat 60155799296) 43046721 +
                ((r*h^2) ^ Nat.rawCast 6 * NNRat.rawCast 16458456017087 99179645184 +
                  ((r*h^2) ^ Nat.rawCast 7 * Rat.rawCast (Int.negOfNat 3202435542593) 223154201664 +
                    ((r*h^2) ^ Nat.rawCast 8 * NNRat.rawCast 464622800108815 514147280633856 +
                      ((r*h^2) ^ Nat.rawCast 9 * Rat.rawCast (Int.negOfNat 2273787291250585) 55527906308456448 +
                        ((r*h^2) ^ Nat.rawCast 10 * NNRat.rawCast 96411338058443 74037208411275264 +
                          ((r*h^2) ^ Nat.rawCast 11 * Rat.rawCast (Int.negOfNat 27853481344505) 999502313552216064 +
                            ((r*h^2) ^ Nat.rawCast 12 * NNRat.rawCast 140944386775 374813367582081024 +
                              ((r*h^2) ^ Nat.rawCast 13 * Rat.rawCast (Int.negOfNat 5818211165) 1999004627104432128 +
                                ((r*h^2) ^ Nat.rawCast 14 * NNRat.rawCast 204815881 17991041643939889152 +
                                  ((r*h^2) ^ Nat.rawCast 15 * Rat.rawCast (Int.negOfNat 255391) 13493281232954916864 +
                                    ((r*h^2) ^ Nat.rawCast 16 * NNRat.rawCast 803 80959687397729501184 +
                                      ((r*h^2) ^ Nat.rawCast 17 * Rat.rawCast (Int.negOfNat 1) 1457274373159131021312 +
                                        0))))))))))))))))))=_

  dsimp only [boundaryImLowColumn76_21,boundaryImHighColumn76_21]

  norm_num

  ring <;> simp


def boundaryImLow76 (h r : ℂ) : ℂ :=
  (((((boundaryImLowColumn76_0 h r) + (boundaryImLowColumn76_1 h r)) + ((boundaryImLowColumn76_2 h r) + ((boundaryImLowColumn76_3 h r) + (boundaryImLowColumn76_4 h r)))) + (((boundaryImLowColumn76_5 h r) + ((boundaryImLowColumn76_6 h r) + (boundaryImLowColumn76_7 h r))) + ((boundaryImLowColumn76_8 h r) + ((boundaryImLowColumn76_9 h r) + (boundaryImLowColumn76_10 h r))))) + ((((boundaryImLowColumn76_11 h r) + (boundaryImLowColumn76_12 h r)) + ((boundaryImLowColumn76_13 h r) + ((boundaryImLowColumn76_14 h r) + (boundaryImLowColumn76_15 h r)))) + (((boundaryImLowColumn76_16 h r) + ((boundaryImLowColumn76_17 h r) + (boundaryImLowColumn76_18 h r))) + ((boundaryImLowColumn76_19 h r) + ((boundaryImLowColumn76_20 h r) + (boundaryImLowColumn76_21 h r))))))

def boundaryImHigh76 (h r : ℂ) : ℂ :=
  (((((boundaryImHighColumn76_0 h r) + (boundaryImHighColumn76_1 h r)) + ((boundaryImHighColumn76_2 h r) + ((boundaryImHighColumn76_3 h r) + (boundaryImHighColumn76_4 h r)))) + (((boundaryImHighColumn76_5 h r) + ((boundaryImHighColumn76_6 h r) + (boundaryImHighColumn76_7 h r))) + ((boundaryImHighColumn76_8 h r) + ((boundaryImHighColumn76_9 h r) + (boundaryImHighColumn76_10 h r))))) + ((((boundaryImHighColumn76_11 h r) + (boundaryImHighColumn76_12 h r)) + ((boundaryImHighColumn76_13 h r) + ((boundaryImHighColumn76_14 h r) + (boundaryImHighColumn76_15 h r)))) + (((boundaryImHighColumn76_16 h r) + ((boundaryImHighColumn76_17 h r) + (boundaryImHighColumn76_18 h r))) + ((boundaryImHighColumn76_19 h r) + ((boundaryImHighColumn76_20 h r) + (boundaryImHighColumn76_21 h r))))))

theorem boundaryImCompleteSplit76 (h r : ℂ) :

    boundaryCompactB75 h r=boundaryImLow76 h r+h^5*boundaryImHigh76 h r := by

  rw [boundaryImClockSum76_eq]

  dsimp only [boundaryImClockSum76,boundaryImClockBlock76_0,boundaryImClockBlock76_1,boundaryImClockBlock76_2]

  rw [boundaryImClock76_0_split,boundaryImClock76_1_split,boundaryImClock76_2_split,boundaryImClock76_3_split,boundaryImClock76_4_split,boundaryImClock76_5_split,boundaryImClock76_6_split,boundaryImClock76_7_split,boundaryImClock76_8_split,boundaryImClock76_9_split,boundaryImClock76_10_split,boundaryImClock76_11_split,boundaryImClock76_12_split,boundaryImClock76_13_split,boundaryImClock76_14_split,boundaryImClock76_15_split,boundaryImClock76_16_split,boundaryImClock76_17_split,boundaryImClock76_18_split,boundaryImClock76_19_split,boundaryImClock76_20_split,boundaryImClock76_21_split]

  dsimp only [boundaryImLow76,boundaryImHigh76]

  ring


end

end HTGeometry.ThetaRatioInfinity
