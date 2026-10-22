import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.Bernstein

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

def boundaryReCoefficient77_0 (A B : ℕ) : ℝ :=
  (((((boundaryTermCoefficient77 ((-230981303/816293376 : ℝ)) ((22-0)+2*0-6) 0 0 A B)) + ((boundaryTermCoefficient77 ((-14198581679/58773123072 : ℝ)) ((22-0)+2*1-6) 0 1 A B))) + (((boundaryTermCoefficient77 ((1259320357/44079842304 : ℝ)) ((22-0)+2*2-6) 0 2 A B)) + (((boundaryTermCoefficient77 ((343884160085/12694994583552 : ℝ)) ((22-0)+2*3-6) 0 3 A B)) + ((boundaryTermCoefficient77 ((3398669372467/10968475320188928 : ℝ)) ((22-0)+2*4-6) 0 4 A B))))) + ((((boundaryTermCoefficient77 ((-2383866633305/4113178245070848 : ℝ)) ((22-0)+2*5-6) 0 5 A B)) + ((boundaryTermCoefficient77 ((-15566885473627/444223250467651584 : ℝ)) ((22-0)+2*6-6) 0 6 A B))) + (((boundaryTermCoefficient77 ((77095760617/15617223649253376 : ℝ)) ((22-0)+2*7-6) 0 7 A B)) + (((boundaryTermCoefficient77 ((42854922195427/71964166575759556608 : ℝ)) ((22-0)+2*8-6) 0 8 A B)) + ((boundaryTermCoefficient77 ((-3583883340325/80959687397729501184 : ℝ)) ((22-0)+2*9-6) 0 9 A B))))))

theorem boundaryReCoefficient77_0_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryReCoefficient77_0 t v=boundaryReHighColumn77_0 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryReCoefficient77_0

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((-230981303/816293376 : ℝ)) ((22-0)+2*0-6) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-14198581679/58773123072 : ℝ)) ((22-0)+2*1-6) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((1259320357/44079842304 : ℝ)) ((22-0)+2*2-6) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((343884160085/12694994583552 : ℝ)) ((22-0)+2*3-6) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((3398669372467/10968475320188928 : ℝ)) ((22-0)+2*4-6) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-2383866633305/4113178245070848 : ℝ)) ((22-0)+2*5-6) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-15566885473627/444223250467651584 : ℝ)) ((22-0)+2*6-6) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((77095760617/15617223649253376 : ℝ)) ((22-0)+2*7-6) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((42854922195427/71964166575759556608 : ℝ)) ((22-0)+2*8-6) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-3583883340325/80959687397729501184 : ℝ)) ((22-0)+2*9-6) 0 9 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryReHighColumn77_0]

  ring


def boundaryReCoefficient77_1 (A B : ℕ) : ℝ :=
  (((((boundaryTermCoefficient77 ((-324249763/45349632 : ℝ)) ((22-1)+2*0-6) 0 0 A B)) + ((boundaryTermCoefficient77 ((-167201743973/58773123072 : ℝ)) ((22-1)+2*1-6) 0 1 A B))) + (((boundaryTermCoefficient77 ((6187558971961/4231664861184 : ℝ)) ((22-1)+2*2-6) 0 2 A B)) + (((boundaryTermCoefficient77 ((7863700323469/25389989167104 : ℝ)) ((22-1)+2*3-6) 0 3 A B)) + ((boundaryTermCoefficient77 ((-116766132507617/2437438960041984 : ℝ)) ((22-1)+2*4-6) 0 4 A B))))) + ((((boundaryTermCoefficient77 ((-1145421589780511/197432555763400704 : ℝ)) ((22-1)+2*5-6) 0 5 A B)) + (((boundaryTermCoefficient77 ((206177013717469/222111625233825792 : ℝ)) ((22-1)+2*6-6) 0 6 A B)) + ((boundaryTermCoefficient77 ((54630215066029/888446500935303168 : ℝ)) ((22-1)+2*7-6) 0 7 A B)))) + (((boundaryTermCoefficient77 ((-3134120843656637/143928333151519113216 : ℝ)) ((22-1)+2*8-6) 0 8 A B)) + (((boundaryTermCoefficient77 ((240050053994077/143928333151519113216 : ℝ)) ((22-1)+2*9-6) 0 9 A B)) + ((boundaryTermCoefficient77 ((-219554668799417/5829097492636524085248 : ℝ)) ((22-1)+2*10-6) 0 10 A B))))))

theorem boundaryReCoefficient77_1_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryReCoefficient77_1 t v=boundaryReHighColumn77_1 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryReCoefficient77_1

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((-324249763/45349632 : ℝ)) ((22-1)+2*0-6) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-167201743973/58773123072 : ℝ)) ((22-1)+2*1-6) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((6187558971961/4231664861184 : ℝ)) ((22-1)+2*2-6) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((7863700323469/25389989167104 : ℝ)) ((22-1)+2*3-6) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-116766132507617/2437438960041984 : ℝ)) ((22-1)+2*4-6) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-1145421589780511/197432555763400704 : ℝ)) ((22-1)+2*5-6) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((206177013717469/222111625233825792 : ℝ)) ((22-1)+2*6-6) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((54630215066029/888446500935303168 : ℝ)) ((22-1)+2*7-6) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-3134120843656637/143928333151519113216 : ℝ)) ((22-1)+2*8-6) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((240050053994077/143928333151519113216 : ℝ)) ((22-1)+2*9-6) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-219554668799417/5829097492636524085248 : ℝ)) ((22-1)+2*10-6) 0 10 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryReHighColumn77_1]

  ring


def boundaryReCoefficient77_2 (A B : ℕ) : ℝ :=
  (((((boundaryTermCoefficient77 ((-17013304387/272097792 : ℝ)) ((22-2)+2*0-6) 0 0 A B)) + (((boundaryTermCoefficient77 ((38431147015/7346640384 : ℝ)) ((22-2)+2*1-6) 0 1 A B)) + ((boundaryTermCoefficient77 ((61220920127935/4231664861184 : ℝ)) ((22-2)+2*2-6) 0 2 A B)))) + (((boundaryTermCoefficient77 ((-276330887018353/304679870005248 : ℝ)) ((22-2)+2*3-6) 0 3 A B)) + (((boundaryTermCoefficient77 ((-1905102852670427/5484237660094464 : ℝ)) ((22-2)+2*4-6) 0 4 A B)) + ((boundaryTermCoefficient77 ((62486563359189029/789730223053602816 : ℝ)) ((22-2)+2*5-6) 0 5 A B))))) + ((((boundaryTermCoefficient77 ((892127151386231/1579460446107205632 : ℝ)) ((22-2)+2*6-6) 0 6 A B)) + (((boundaryTermCoefficient77 ((-555318049108146761/255872592269367312384 : ℝ)) ((22-2)+2*7-6) 0 7 A B)) + ((boundaryTermCoefficient77 ((7203123035673985/23988055525253185536 : ℝ)) ((22-2)+2*8-6) 0 8 A B)))) + (((boundaryTermCoefficient77 ((-12468472096182551/647677499181836009472 : ℝ)) ((22-2)+2*9-6) 0 9 A B)) + (((boundaryTermCoefficient77 ((17574827696587321/31088519960728128454656 : ℝ)) ((22-2)+2*10-6) 0 10 A B)) + ((boundaryTermCoefficient77 ((-2092690629306389/559593359293106312183808 : ℝ)) ((22-2)+2*11-6) 0 11 A B))))))

theorem boundaryReCoefficient77_2_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryReCoefficient77_2 t v=boundaryReHighColumn77_2 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryReCoefficient77_2

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((-17013304387/272097792 : ℝ)) ((22-2)+2*0-6) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((38431147015/7346640384 : ℝ)) ((22-2)+2*1-6) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((61220920127935/4231664861184 : ℝ)) ((22-2)+2*2-6) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-276330887018353/304679870005248 : ℝ)) ((22-2)+2*3-6) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-1905102852670427/5484237660094464 : ℝ)) ((22-2)+2*4-6) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((62486563359189029/789730223053602816 : ℝ)) ((22-2)+2*5-6) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((892127151386231/1579460446107205632 : ℝ)) ((22-2)+2*6-6) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-555318049108146761/255872592269367312384 : ℝ)) ((22-2)+2*7-6) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((7203123035673985/23988055525253185536 : ℝ)) ((22-2)+2*8-6) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-12468472096182551/647677499181836009472 : ℝ)) ((22-2)+2*9-6) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((17574827696587321/31088519960728128454656 : ℝ)) ((22-2)+2*10-6) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-2092690629306389/559593359293106312183808 : ℝ)) ((22-2)+2*11-6) 0 11 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryReHighColumn77_2]

  ring


def boundaryReCoefficient77_3 (A B : ℕ) : ℝ :=
  (((((boundaryTermCoefficient77 ((-255401548/1594323 : ℝ)) ((22-3)+2*0-6) 0 0 A B)) + (((boundaryTermCoefficient77 ((459665122079/2448880128 : ℝ)) ((22-3)+2*1-6) 0 1 A B)) + ((boundaryTermCoefficient77 ((24735163810307/1410554953728 : ℝ)) ((22-3)+2*2-6) 0 2 A B)))) + (((boundaryTermCoefficient77 ((-3984197611531409/304679870005248 : ℝ)) ((22-3)+2*3-6) 0 3 A B)) + (((boundaryTermCoefficient77 ((21192601872574421/7312316880125952 : ℝ)) ((22-3)+2*4-6) 0 4 A B)) + ((boundaryTermCoefficient77 ((30446098602014515/789730223053602816 : ℝ)) ((22-3)+2*5-6) 0 5 A B))))) + ((((boundaryTermCoefficient77 ((-128178562347826931/1184595334580404224 : ℝ)) ((22-3)+2*6-6) 0 6 A B)) + (((boundaryTermCoefficient77 ((35336490088500240085/2046980738154938499072 : ℝ)) ((22-3)+2*7-6) 0 7 A B)) + ((boundaryTermCoefficient77 ((-8067016470465992459/6140942214464815497216 : ℝ)) ((22-3)+2*8-6) 0 8 A B)))) + ((((boundaryTermCoefficient77 ((4590822519085866529/82902719895275009212416 : ℝ)) ((22-3)+2*9-6) 0 9 A B)) + ((boundaryTermCoefficient77 ((-1083704430860289001/746124479057475082911744 : ℝ)) ((22-3)+2*10-6) 0 10 A B))) + (((boundaryTermCoefficient77 ((30695821105674067/4476746874344850497470464 : ℝ)) ((22-3)+2*11-6) 0 11 A B)) + ((boundaryTermCoefficient77 ((13750076961227201/40290721869103654477234176 : ℝ)) ((22-3)+2*12-6) 0 12 A B))))))

theorem boundaryReCoefficient77_3_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryReCoefficient77_3 t v=boundaryReHighColumn77_3 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryReCoefficient77_3

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((-255401548/1594323 : ℝ)) ((22-3)+2*0-6) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((459665122079/2448880128 : ℝ)) ((22-3)+2*1-6) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((24735163810307/1410554953728 : ℝ)) ((22-3)+2*2-6) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-3984197611531409/304679870005248 : ℝ)) ((22-3)+2*3-6) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((21192601872574421/7312316880125952 : ℝ)) ((22-3)+2*4-6) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((30446098602014515/789730223053602816 : ℝ)) ((22-3)+2*5-6) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-128178562347826931/1184595334580404224 : ℝ)) ((22-3)+2*6-6) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((35336490088500240085/2046980738154938499072 : ℝ)) ((22-3)+2*7-6) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-8067016470465992459/6140942214464815497216 : ℝ)) ((22-3)+2*8-6) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((4590822519085866529/82902719895275009212416 : ℝ)) ((22-3)+2*9-6) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-1083704430860289001/746124479057475082911744 : ℝ)) ((22-3)+2*10-6) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((30695821105674067/4476746874344850497470464 : ℝ)) ((22-3)+2*11-6) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((13750076961227201/40290721869103654477234176 : ℝ)) ((22-3)+2*12-6) 0 12 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryReHighColumn77_3]

  ring


def boundaryReCoefficient77_4 (A B : ℕ) : ℝ :=
  (((((boundaryTermCoefficient77 ((580451074939/816293376 : ℝ)) ((22-4)+2*0-6) 0 0 A B)) + (((boundaryTermCoefficient77 ((3027591827663/4897760256 : ℝ)) ((22-4)+2*1-6) 0 1 A B)) + ((boundaryTermCoefficient77 ((-872943112477597/4231664861184 : ℝ)) ((22-4)+2*2-6) 0 2 A B)))) + ((((boundaryTermCoefficient77 ((1082809371360415/25389989167104 : ℝ)) ((22-4)+2*3-6) 0 3 A B)) + ((boundaryTermCoefficient77 ((103660301096665273/21936950640377856 : ℝ)) ((22-4)+2*4-6) 0 4 A B))) + (((boundaryTermCoefficient77 ((-6349396462835622133/1579460446107205632 : ℝ)) ((22-4)+2*5-6) 0 5 A B)) + ((boundaryTermCoefficient77 ((17452969212118235473/28430288029929701376 : ℝ)) ((22-4)+2*6-6) 0 6 A B))))) + ((((boundaryTermCoefficient77 ((-105209792018815952689/4093961476309876998144 : ℝ)) ((22-4)+2*7-6) 0 7 A B)) + (((boundaryTermCoefficient77 ((-793839895007146664479/294765226294311143866368 : ℝ)) ((22-4)+2*8-6) 0 8 A B)) + ((boundaryTermCoefficient77 ((468378633871040181617/1326443518324400147398656 : ℝ)) ((22-4)+2*9-6) 0 9 A B)))) + ((((boundaryTermCoefficient77 ((-172581908916053155805/11937991664919601326587904 : ℝ)) ((22-4)+2*10-6) 0 10 A B)) + ((boundaryTermCoefficient77 ((3639349364096350207/13430240623034551492411392 : ℝ)) ((22-4)+2*11-6) 0 11 A B))) + (((boundaryTermCoefficient77 ((-9905633421281934959/1933954649716975414907240448 : ℝ)) ((22-4)+2*12-6) 0 12 A B)) + ((boundaryTermCoefficient77 ((293575300609695167/8702795923726389367082582016 : ℝ)) ((22-4)+2*13-6) 0 13 A B))))))

theorem boundaryReCoefficient77_4_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryReCoefficient77_4 t v=boundaryReHighColumn77_4 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryReCoefficient77_4

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((580451074939/816293376 : ℝ)) ((22-4)+2*0-6) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((3027591827663/4897760256 : ℝ)) ((22-4)+2*1-6) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-872943112477597/4231664861184 : ℝ)) ((22-4)+2*2-6) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((1082809371360415/25389989167104 : ℝ)) ((22-4)+2*3-6) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((103660301096665273/21936950640377856 : ℝ)) ((22-4)+2*4-6) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-6349396462835622133/1579460446107205632 : ℝ)) ((22-4)+2*5-6) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((17452969212118235473/28430288029929701376 : ℝ)) ((22-4)+2*6-6) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-105209792018815952689/4093961476309876998144 : ℝ)) ((22-4)+2*7-6) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-793839895007146664479/294765226294311143866368 : ℝ)) ((22-4)+2*8-6) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((468378633871040181617/1326443518324400147398656 : ℝ)) ((22-4)+2*9-6) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-172581908916053155805/11937991664919601326587904 : ℝ)) ((22-4)+2*10-6) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((3639349364096350207/13430240623034551492411392 : ℝ)) ((22-4)+2*11-6) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-9905633421281934959/1933954649716975414907240448 : ℝ)) ((22-4)+2*12-6) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((293575300609695167/8702795923726389367082582016 : ℝ)) ((22-4)+2*13-6) 0 13 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryReHighColumn77_4]

  ring


def boundaryReCoefficient77_5 (A B : ℕ) : ℝ :=
  (((((boundaryTermCoefficient77 ((641382265649/136048896 : ℝ)) ((22-5)+2*0-6) 0 0 A B)) + (((boundaryTermCoefficient77 ((-42631093586323/58773123072 : ℝ)) ((22-5)+2*1-6) 0 1 A B)) + ((boundaryTermCoefficient77 ((24033298136159/264479053824 : ℝ)) ((22-5)+2*2-6) 0 2 A B)))) + ((((boundaryTermCoefficient77 ((25507776569387275/152339935002624 : ℝ)) ((22-5)+2*3-6) 0 3 A B)) + ((boundaryTermCoefficient77 ((-557960873325484405/5484237660094464 : ℝ)) ((22-5)+2*4-6) 0 4 A B))) + (((boundaryTermCoefficient77 ((7418330926261069049/526486815369068544 : ℝ)) ((22-5)+2*5-6) 0 5 A B)) + ((boundaryTermCoefficient77 ((38501327257187750557/113721152119718805504 : ℝ)) ((22-5)+2*6-6) 0 6 A B))))) + (((((boundaryTermCoefficient77 ((-443037124184622331457/1364653825436625666048 : ℝ)) ((22-5)+2*7-6) 0 7 A B)) + ((boundaryTermCoefficient77 ((8224411146406593623867/196510150862874095910912 : ℝ)) ((22-5)+2*8-6) 0 8 A B))) + (((boundaryTermCoefficient77 ((-27106615414255252681223/10611548146595201179189248 : ℝ)) ((22-5)+2*9-6) 0 9 A B)) + ((boundaryTermCoefficient77 ((2510609098595788666727/31834644439785603537567744 : ℝ)) ((22-5)+2*10-6) 0 10 A B)))) + ((((boundaryTermCoefficient77 ((-143524555414052015797/143255899979035215919054848 : ℝ)) ((22-5)+2*11-6) 0 11 A B)) + ((boundaryTermCoefficient77 ((21237620319636992089/1933954649716975414907240448 : ℝ)) ((22-5)+2*12-6) 0 12 A B))) + (((boundaryTermCoefficient77 ((-4675098911177466233/23207455796603704978886885376 : ℝ)) ((22-5)+2*13-6) 0 13 A B)) + ((boundaryTermCoefficient77 ((405506432602597781/626601306508300034429945905152 : ℝ)) ((22-5)+2*14-6) 0 14 A B))))))

theorem boundaryReCoefficient77_5_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryReCoefficient77_5 t v=boundaryReHighColumn77_5 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryReCoefficient77_5

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((641382265649/136048896 : ℝ)) ((22-5)+2*0-6) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-42631093586323/58773123072 : ℝ)) ((22-5)+2*1-6) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((24033298136159/264479053824 : ℝ)) ((22-5)+2*2-6) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((25507776569387275/152339935002624 : ℝ)) ((22-5)+2*3-6) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-557960873325484405/5484237660094464 : ℝ)) ((22-5)+2*4-6) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((7418330926261069049/526486815369068544 : ℝ)) ((22-5)+2*5-6) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((38501327257187750557/113721152119718805504 : ℝ)) ((22-5)+2*6-6) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-443037124184622331457/1364653825436625666048 : ℝ)) ((22-5)+2*7-6) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((8224411146406593623867/196510150862874095910912 : ℝ)) ((22-5)+2*8-6) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-27106615414255252681223/10611548146595201179189248 : ℝ)) ((22-5)+2*9-6) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((2510609098595788666727/31834644439785603537567744 : ℝ)) ((22-5)+2*10-6) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-143524555414052015797/143255899979035215919054848 : ℝ)) ((22-5)+2*11-6) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((21237620319636992089/1933954649716975414907240448 : ℝ)) ((22-5)+2*12-6) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-4675098911177466233/23207455796603704978886885376 : ℝ)) ((22-5)+2*13-6) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((405506432602597781/626601306508300034429945905152 : ℝ)) ((22-5)+2*14-6) 0 14 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryReHighColumn77_5]

  ring


def boundaryReCoefficient77_6 (A B : ℕ) : ℝ :=
  ((((((boundaryTermCoefficient77 ((521984467501/90699264 : ℝ)) ((22-6)+2*0-6) 0 0 A B)) + ((boundaryTermCoefficient77 ((-38296672442261/19591041024 : ℝ)) ((22-6)+2*1-6) 0 1 A B))) + (((boundaryTermCoefficient77 ((9044128743375011/4231664861184 : ℝ)) ((22-6)+2*2-6) 0 2 A B)) + ((boundaryTermCoefficient77 ((-460923347021608217/304679870005248 : ℝ)) ((22-6)+2*3-6) 0 3 A B)))) + ((((boundaryTermCoefficient77 ((3386468087123864579/21936950640377856 : ℝ)) ((22-6)+2*4-6) 0 4 A B)) + ((boundaryTermCoefficient77 ((31639773598267866541/789730223053602816 : ℝ)) ((22-6)+2*5-6) 0 5 A B))) + (((boundaryTermCoefficient77 ((-1534458378055478218519/113721152119718805504 : ℝ)) ((22-6)+2*6-6) 0 6 A B)) + ((boundaryTermCoefficient77 ((14056976992682328934859/8187922952619753996288 : ℝ)) ((22-6)+2*7-6) 0 7 A B))))) + (((((boundaryTermCoefficient77 ((-3849413208508757250629/36845653286788892983296 : ℝ)) ((22-6)+2*8-6) 0 8 A B)) + ((boundaryTermCoefficient77 ((13017708381092649189173/5305774073297600589594624 : ℝ)) ((22-6)+2*9-6) 0 9 A B))) + (((boundaryTermCoefficient77 ((3446520881208640473325/95503933319356810612703232 : ℝ)) ((22-6)+2*10-6) 0 10 A B)) + ((boundaryTermCoefficient77 ((-1142267097772873945517/286511799958070431838109696 : ℝ)) ((22-6)+2*11-6) 0 11 A B)))) + ((((boundaryTermCoefficient77 ((405734704255409069305/3867909299433950829814480896 : ℝ)) ((22-6)+2*12-6) 0 12 A B)) + ((boundaryTermCoefficient77 ((-8390822305894903273/17405591847452778734165164032 : ℝ)) ((22-6)+2*13-6) 0 13 A B))) + (((boundaryTermCoefficient77 ((-949546426483032623/626601306508300034429945905152 : ℝ)) ((22-6)+2*14-6) 0 14 A B)) + ((boundaryTermCoefficient77 ((18285856292474113/5639411758574700309869513146368 : ℝ)) ((22-6)+2*15-6) 0 15 A B))))))

theorem boundaryReCoefficient77_6_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryReCoefficient77_6 t v=boundaryReHighColumn77_6 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryReCoefficient77_6

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((521984467501/90699264 : ℝ)) ((22-6)+2*0-6) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-38296672442261/19591041024 : ℝ)) ((22-6)+2*1-6) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((9044128743375011/4231664861184 : ℝ)) ((22-6)+2*2-6) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-460923347021608217/304679870005248 : ℝ)) ((22-6)+2*3-6) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((3386468087123864579/21936950640377856 : ℝ)) ((22-6)+2*4-6) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((31639773598267866541/789730223053602816 : ℝ)) ((22-6)+2*5-6) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-1534458378055478218519/113721152119718805504 : ℝ)) ((22-6)+2*6-6) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((14056976992682328934859/8187922952619753996288 : ℝ)) ((22-6)+2*7-6) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-3849413208508757250629/36845653286788892983296 : ℝ)) ((22-6)+2*8-6) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((13017708381092649189173/5305774073297600589594624 : ℝ)) ((22-6)+2*9-6) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((3446520881208640473325/95503933319356810612703232 : ℝ)) ((22-6)+2*10-6) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-1142267097772873945517/286511799958070431838109696 : ℝ)) ((22-6)+2*11-6) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((405734704255409069305/3867909299433950829814480896 : ℝ)) ((22-6)+2*12-6) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-8390822305894903273/17405591847452778734165164032 : ℝ)) ((22-6)+2*13-6) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-949546426483032623/626601306508300034429945905152 : ℝ)) ((22-6)+2*14-6) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((18285856292474113/5639411758574700309869513146368 : ℝ)) ((22-6)+2*15-6) 0 15 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryReHighColumn77_6]

  ring


def boundaryReCoefficient77_7 (A B : ℕ) : ℝ :=
  ((((((boundaryTermCoefficient77 ((-47837539691/8503056 : ℝ)) ((22-7)+2*0-6) 0 0 A B)) + ((boundaryTermCoefficient77 ((86019589412363/9795520512 : ℝ)) ((22-7)+2*1-6) 0 1 A B))) + (((boundaryTermCoefficient77 ((-13018275535923361/1057916215296 : ℝ)) ((22-7)+2*2-6) 0 2 A B)) + ((boundaryTermCoefficient77 ((-124219748680329659/304679870005248 : ℝ)) ((22-7)+2*3-6) 0 3 A B)))) + ((((boundaryTermCoefficient77 ((13467142392276357361/10968475320188928 : ℝ)) ((22-7)+2*4-6) 0 4 A B)) + ((boundaryTermCoefficient77 ((-253415598630830755853/789730223053602816 : ℝ)) ((22-7)+2*5-6) 0 5 A B))) + (((boundaryTermCoefficient77 ((2173733722472516133643/56860576059859402752 : ℝ)) ((22-7)+2*6-6) 0 6 A B)) + ((boundaryTermCoefficient77 ((-9950442194462674810099/8187922952619753996288 : ℝ)) ((22-7)+2*7-6) 0 7 A B))))) + (((((boundaryTermCoefficient77 ((-112080901432557906299243/589530452588622287732736 : ℝ)) ((22-7)+2*8-6) 0 8 A B)) + ((boundaryTermCoefficient77 ((237165594725865884168879/10611548146595201179189248 : ℝ)) ((22-7)+2*9-6) 0 9 A B))) + (((boundaryTermCoefficient77 ((-96039386593052954438111/95503933319356810612703232 : ℝ)) ((22-7)+2*10-6) 0 10 A B)) + ((boundaryTermCoefficient77 ((1741471493734137984437/71627949989517607959527424 : ℝ)) ((22-7)+2*11-6) 0 11 A B)))) + ((((boundaryTermCoefficient77 ((-457041462381164301229/966977324858487707453620224 : ℝ)) ((22-7)+2*12-6) 0 12 A B)) + ((boundaryTermCoefficient77 ((347100065275036241875/69622367389811114936660656128 : ℝ)) ((22-7)+2*13-6) 0 13 A B))) + (((boundaryTermCoefficient77 ((-8234022588000933059/626601306508300034429945905152 : ℝ)) ((22-7)+2*14-6) 0 14 A B)) + (((boundaryTermCoefficient77 ((128030383508489/2819705879287350154934756573184 : ℝ)) ((22-7)+2*15-6) 0 15 A B)) + ((boundaryTermCoefficient77 ((168937493305/49565142409347951942212517888 : ℝ)) ((22-7)+2*16-6) 0 16 A B)))))))

theorem boundaryReCoefficient77_7_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryReCoefficient77_7 t v=boundaryReHighColumn77_7 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryReCoefficient77_7

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((-47837539691/8503056 : ℝ)) ((22-7)+2*0-6) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((86019589412363/9795520512 : ℝ)) ((22-7)+2*1-6) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-13018275535923361/1057916215296 : ℝ)) ((22-7)+2*2-6) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-124219748680329659/304679870005248 : ℝ)) ((22-7)+2*3-6) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((13467142392276357361/10968475320188928 : ℝ)) ((22-7)+2*4-6) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-253415598630830755853/789730223053602816 : ℝ)) ((22-7)+2*5-6) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((2173733722472516133643/56860576059859402752 : ℝ)) ((22-7)+2*6-6) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-9950442194462674810099/8187922952619753996288 : ℝ)) ((22-7)+2*7-6) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-112080901432557906299243/589530452588622287732736 : ℝ)) ((22-7)+2*8-6) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((237165594725865884168879/10611548146595201179189248 : ℝ)) ((22-7)+2*9-6) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-96039386593052954438111/95503933319356810612703232 : ℝ)) ((22-7)+2*10-6) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((1741471493734137984437/71627949989517607959527424 : ℝ)) ((22-7)+2*11-6) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-457041462381164301229/966977324858487707453620224 : ℝ)) ((22-7)+2*12-6) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((347100065275036241875/69622367389811114936660656128 : ℝ)) ((22-7)+2*13-6) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-8234022588000933059/626601306508300034429945905152 : ℝ)) ((22-7)+2*14-6) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((128030383508489/2819705879287350154934756573184 : ℝ)) ((22-7)+2*15-6) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((168937493305/49565142409347951942212517888 : ℝ)) ((22-7)+2*16-6) 0 16 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryReHighColumn77_7]

  ring


def boundaryReCoefficient77_8 (A B : ℕ) : ℝ :=
  ((((((boundaryTermCoefficient77 ((-43039903891/8503056 : ℝ)) ((22-8)+2*0-6) 0 0 A B)) + ((boundaryTermCoefficient77 ((-51993159655921/918330048 : ℝ)) ((22-8)+2*1-6) 0 1 A B))) + (((boundaryTermCoefficient77 ((-36816383964341737/1410554953728 : ℝ)) ((22-8)+2*2-6) 0 2 A B)) + ((boundaryTermCoefficient77 ((2698941304137620131/152339935002624 : ℝ)) ((22-8)+2*3-6) 0 3 A B)))) + ((((boundaryTermCoefficient77 ((-10091284279338785291/2437438960041984 : ℝ)) ((22-8)+2*4-6) 0 4 A B)) + ((boundaryTermCoefficient77 ((618740256739823012981/1579460446107205632 : ℝ)) ((22-8)+2*5-6) 0 5 A B))) + (((boundaryTermCoefficient77 ((4356046131743194851953/113721152119718805504 : ℝ)) ((22-8)+2*6-6) 0 6 A B)) + (((boundaryTermCoefficient77 ((-28321057871217096711049/2046980738154938499072 : ℝ)) ((22-8)+2*7-6) 0 7 A B)) + ((boundaryTermCoefficient77 ((3326170804881961551697/2302853330424305811456 : ℝ)) ((22-8)+2*8-6) 0 8 A B)))))) + (((((boundaryTermCoefficient77 ((-128581347659693864508937/1768591357765866863198208 : ℝ)) ((22-8)+2*9-6) 0 9 A B)) + ((boundaryTermCoefficient77 ((162785130924697058101727/95503933319356810612703232 : ℝ)) ((22-8)+2*10-6) 0 10 A B))) + (((boundaryTermCoefficient77 ((-6817004761674135994351/859535399874211295514329088 : ℝ)) ((22-8)+2*11-6) 0 11 A B)) + ((boundaryTermCoefficient77 ((-118830036176441743817/1289303099811316943271493632 : ℝ)) ((22-8)+2*12-6) 0 12 A B)))) + ((((boundaryTermCoefficient77 ((-13668063861280363745/2900931974575463122360860672 : ℝ)) ((22-8)+2*13-6) 0 13 A B)) + ((boundaryTermCoefficient77 ((27750595395922238315/626601306508300034429945905152 : ℝ)) ((22-8)+2*14-6) 0 14 A B))) + (((boundaryTermCoefficient77 ((-12744276152806037/208867102169433344809981968384 : ℝ)) ((22-8)+2*15-6) 0 15 A B)) + (((boundaryTermCoefficient77 ((21961341297329/4229558818931025232402134859776 : ℝ)) ((22-8)+2*16-6) 0 16 A B)) + ((boundaryTermCoefficient77 ((14325530485/114198088111137681274857641213952 : ℝ)) ((22-8)+2*17-6) 0 17 A B)))))))

theorem boundaryReCoefficient77_8_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryReCoefficient77_8 t v=boundaryReHighColumn77_8 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryReCoefficient77_8

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((-43039903891/8503056 : ℝ)) ((22-8)+2*0-6) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-51993159655921/918330048 : ℝ)) ((22-8)+2*1-6) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-36816383964341737/1410554953728 : ℝ)) ((22-8)+2*2-6) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((2698941304137620131/152339935002624 : ℝ)) ((22-8)+2*3-6) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-10091284279338785291/2437438960041984 : ℝ)) ((22-8)+2*4-6) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((618740256739823012981/1579460446107205632 : ℝ)) ((22-8)+2*5-6) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((4356046131743194851953/113721152119718805504 : ℝ)) ((22-8)+2*6-6) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-28321057871217096711049/2046980738154938499072 : ℝ)) ((22-8)+2*7-6) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((3326170804881961551697/2302853330424305811456 : ℝ)) ((22-8)+2*8-6) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-128581347659693864508937/1768591357765866863198208 : ℝ)) ((22-8)+2*9-6) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((162785130924697058101727/95503933319356810612703232 : ℝ)) ((22-8)+2*10-6) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-6817004761674135994351/859535399874211295514329088 : ℝ)) ((22-8)+2*11-6) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-118830036176441743817/1289303099811316943271493632 : ℝ)) ((22-8)+2*12-6) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-13668063861280363745/2900931974575463122360860672 : ℝ)) ((22-8)+2*13-6) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((27750595395922238315/626601306508300034429945905152 : ℝ)) ((22-8)+2*14-6) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-12744276152806037/208867102169433344809981968384 : ℝ)) ((22-8)+2*15-6) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((21961341297329/4229558818931025232402134859776 : ℝ)) ((22-8)+2*16-6) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((14325530485/114198088111137681274857641213952 : ℝ)) ((22-8)+2*17-6) 0 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryReHighColumn77_8]

  ring


def boundaryReCoefficient77_9 (A B : ℕ) : ℝ :=
  ((((((boundaryTermCoefficient77 ((-231964931983/1594323 : ℝ)) ((22-9)+2*0-6) 0 0 A B)) + ((boundaryTermCoefficient77 ((-210557044735907/918330048 : ℝ)) ((22-9)+2*1-6) 0 1 A B))) + (((boundaryTermCoefficient77 ((248462674122865985/2115832430592 : ℝ)) ((22-9)+2*2-6) 0 2 A B)) + ((boundaryTermCoefficient77 ((-3320502011641449089/152339935002624 : ℝ)) ((22-9)+2*3-6) 0 3 A B)))) + ((((boundaryTermCoefficient77 ((-11336060693792637367/10968475320188928 : ℝ)) ((22-9)+2*4-6) 0 4 A B)) + ((boundaryTermCoefficient77 ((2831905986445154163811/1579460446107205632 : ℝ)) ((22-9)+2*5-6) 0 5 A B))) + (((boundaryTermCoefficient77 ((-47687123763919179400543/113721152119718805504 : ℝ)) ((22-9)+2*6-6) 0 6 A B)) + (((boundaryTermCoefficient77 ((45224940920577500951155/1023490369077469249536 : ℝ)) ((22-9)+2*7-6) 0 7 A B)) + ((boundaryTermCoefficient77 ((-6551210243106906428767/3070471107232407748608 : ℝ)) ((22-9)+2*8-6) 0 8 A B)))))) + (((((boundaryTermCoefficient77 ((6863276214059699449571/442147839441466715799552 : ℝ)) ((22-9)+2*9-6) 0 9 A B)) + ((boundaryTermCoefficient77 ((153860227282608727952087/47751966659678405306351616 : ℝ)) ((22-9)+2*10-6) 0 10 A B))) + (((boundaryTermCoefficient77 ((-6028302026926271670019/35813974994758803979763712 : ℝ)) ((22-9)+2*11-6) 0 11 A B)) + ((boundaryTermCoefficient77 ((632928382634042059765/161162887476414617908936704 : ℝ)) ((22-9)+2*12-6) 0 12 A B)))) + ((((boundaryTermCoefficient77 ((-20596470781475235377/644651549905658471635746816 : ℝ)) ((22-9)+2*13-6) 0 13 A B)) + ((boundaryTermCoefficient77 ((14178643823426880329/313300653254150017214972952576 : ℝ)) ((22-9)+2*14-6) 0 14 A B))) + (((boundaryTermCoefficient77 ((111320396915907529/1409852939643675077467378286592 : ℝ)) ((22-9)+2*15-6) 0 15 A B)) + (((boundaryTermCoefficient77 ((-6342698417503/117487744970306256455614857216 : ℝ)) ((22-9)+2*16-6) 0 16 A B)) + ((boundaryTermCoefficient77 ((2426981221/57099044055568840637428820606976 : ℝ)) ((22-9)+2*17-6) 0 17 A B)))))))

theorem boundaryReCoefficient77_9_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryReCoefficient77_9 t v=boundaryReHighColumn77_9 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryReCoefficient77_9

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((-231964931983/1594323 : ℝ)) ((22-9)+2*0-6) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-210557044735907/918330048 : ℝ)) ((22-9)+2*1-6) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((248462674122865985/2115832430592 : ℝ)) ((22-9)+2*2-6) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-3320502011641449089/152339935002624 : ℝ)) ((22-9)+2*3-6) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-11336060693792637367/10968475320188928 : ℝ)) ((22-9)+2*4-6) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((2831905986445154163811/1579460446107205632 : ℝ)) ((22-9)+2*5-6) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-47687123763919179400543/113721152119718805504 : ℝ)) ((22-9)+2*6-6) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((45224940920577500951155/1023490369077469249536 : ℝ)) ((22-9)+2*7-6) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-6551210243106906428767/3070471107232407748608 : ℝ)) ((22-9)+2*8-6) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((6863276214059699449571/442147839441466715799552 : ℝ)) ((22-9)+2*9-6) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((153860227282608727952087/47751966659678405306351616 : ℝ)) ((22-9)+2*10-6) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-6028302026926271670019/35813974994758803979763712 : ℝ)) ((22-9)+2*11-6) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((632928382634042059765/161162887476414617908936704 : ℝ)) ((22-9)+2*12-6) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-20596470781475235377/644651549905658471635746816 : ℝ)) ((22-9)+2*13-6) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((14178643823426880329/313300653254150017214972952576 : ℝ)) ((22-9)+2*14-6) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((111320396915907529/1409852939643675077467378286592 : ℝ)) ((22-9)+2*15-6) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-6342698417503/117487744970306256455614857216 : ℝ)) ((22-9)+2*16-6) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((2426981221/57099044055568840637428820606976 : ℝ)) ((22-9)+2*17-6) 0 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryReHighColumn77_9]

  ring


def boundaryReCoefficient77_10 (A B : ℕ) : ℝ :=
  ((((((boundaryTermCoefficient77 ((-2118054708323/3188646 : ℝ)) ((22-10)+2*0-6) 0 0 A B)) + ((boundaryTermCoefficient77 ((56480011677895/229582512 : ℝ)) ((22-10)+2*1-6) 0 1 A B))) + (((boundaryTermCoefficient77 ((134058055137985705/4231664861184 : ℝ)) ((22-10)+2*2-6) 0 2 A B)) + ((boundaryTermCoefficient77 ((-17815765018373067625/304679870005248 : ℝ)) ((22-10)+2*3-6) 0 3 A B)))) + ((((boundaryTermCoefficient77 ((657569270106038332769/21936950640377856 : ℝ)) ((22-10)+2*4-6) 0 4 A B)) + ((boundaryTermCoefficient77 ((-2727909046342592746033/394865111526801408 : ℝ)) ((22-10)+2*5-6) 0 5 A B))) + (((boundaryTermCoefficient77 ((41665285645354960385633/56860576059859402752 : ℝ)) ((22-10)+2*6-6) 0 6 A B)) + (((boundaryTermCoefficient77 ((-45193801069645288518005/2046980738154938499072 : ℝ)) ((22-10)+2*7-6) 0 7 A B)) + ((boundaryTermCoefficient77 ((-190647925918021881910891/73691306573577785966592 : ℝ)) ((22-10)+2*8-6) 0 8 A B)))))) + (((((boundaryTermCoefficient77 ((265826180879443913349661/884295678882933431599104 : ℝ)) ((22-10)+2*9-6) 0 9 A B)) + ((boundaryTermCoefficient77 ((-9320943547576114567169/663221759162200073699328 : ℝ)) ((22-10)+2*10-6) 0 10 A B))) + (((boundaryTermCoefficient77 ((4549686955444780899643/11937991664919601326587904 : ℝ)) ((22-10)+2*11-6) 0 11 A B)) + ((boundaryTermCoefficient77 ((-4960483886744146624255/644651549905658471635746816 : ℝ)) ((22-10)+2*12-6) 0 12 A B)))) + ((((boundaryTermCoefficient77 ((33161798203314162799/362616496821932890295107584 : ℝ)) ((22-10)+2*13-6) 0 13 A B)) + ((boundaryTermCoefficient77 ((-9756635795994252575/26108387771179168101247746048 : ℝ)) ((22-10)+2*14-6) 0 14 A B))) + (((boundaryTermCoefficient77 ((27234902191212835/78325163313537504303743238144 : ℝ)) ((22-10)+2*15-6) 0 15 A B)) + (((boundaryTermCoefficient77 ((1292771330375/1409852939643675077467378286592 : ℝ)) ((22-10)+2*16-6) 0 16 A B)) + ((boundaryTermCoefficient77 ((-26945503417/38066029370379227091619213737984 : ℝ)) ((22-10)+2*17-6) 0 17 A B)))))))

theorem boundaryReCoefficient77_10_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryReCoefficient77_10 t v=boundaryReHighColumn77_10 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryReCoefficient77_10

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((-2118054708323/3188646 : ℝ)) ((22-10)+2*0-6) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((56480011677895/229582512 : ℝ)) ((22-10)+2*1-6) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((134058055137985705/4231664861184 : ℝ)) ((22-10)+2*2-6) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-17815765018373067625/304679870005248 : ℝ)) ((22-10)+2*3-6) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((657569270106038332769/21936950640377856 : ℝ)) ((22-10)+2*4-6) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-2727909046342592746033/394865111526801408 : ℝ)) ((22-10)+2*5-6) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((41665285645354960385633/56860576059859402752 : ℝ)) ((22-10)+2*6-6) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-45193801069645288518005/2046980738154938499072 : ℝ)) ((22-10)+2*7-6) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-190647925918021881910891/73691306573577785966592 : ℝ)) ((22-10)+2*8-6) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((265826180879443913349661/884295678882933431599104 : ℝ)) ((22-10)+2*9-6) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-9320943547576114567169/663221759162200073699328 : ℝ)) ((22-10)+2*10-6) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((4549686955444780899643/11937991664919601326587904 : ℝ)) ((22-10)+2*11-6) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-4960483886744146624255/644651549905658471635746816 : ℝ)) ((22-10)+2*12-6) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((33161798203314162799/362616496821932890295107584 : ℝ)) ((22-10)+2*13-6) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-9756635795994252575/26108387771179168101247746048 : ℝ)) ((22-10)+2*14-6) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((27234902191212835/78325163313537504303743238144 : ℝ)) ((22-10)+2*15-6) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((1292771330375/1409852939643675077467378286592 : ℝ)) ((22-10)+2*16-6) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-26945503417/38066029370379227091619213737984 : ℝ)) ((22-10)+2*17-6) 0 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryReHighColumn77_10]

  ring


def boundaryReCoefficient77_11 (A B : ℕ) : ℝ :=
  ((((((boundaryTermCoefficient77 ((-360033540581/1594323 : ℝ)) ((22-11)+2*0-6) 0 0 A B)) + ((boundaryTermCoefficient77 ((17568454872499/28697814 : ℝ)) ((22-11)+2*1-6) 0 1 A B))) + (((boundaryTermCoefficient77 ((-920524941361915531/2115832430592 : ℝ)) ((22-11)+2*2-6) 0 2 A B)) + ((boundaryTermCoefficient77 ((73496748484323052529/304679870005248 : ℝ)) ((22-11)+2*3-6) 0 3 A B)))) + ((((boundaryTermCoefficient77 ((-27429392756818027649/457019805007872 : ℝ)) ((22-11)+2*4-6) 0 4 A B)) + ((boundaryTermCoefficient77 ((3978806380121646237391/789730223053602816 : ℝ)) ((22-11)+2*5-6) 0 5 A B))) + (((boundaryTermCoefficient77 ((13225175638740216702139/28430288029929701376 : ℝ)) ((22-11)+2*6-6) 0 6 A B)) + (((boundaryTermCoefficient77 ((-4046844871148757577/29249267520503808 : ℝ)) ((22-11)+2*7-6) 0 7 A B)) + ((boundaryTermCoefficient77 ((477167294277387620196913/36845653286788892983296 : ℝ)) ((22-11)+2*8-6) 0 8 A B)))))) + (((((boundaryTermCoefficient77 ((-206070765128072537541793/331610879581100036849664 : ℝ)) ((22-11)+2*9-6) 0 9 A B)) + ((boundaryTermCoefficient77 ((178347676301480892829787/11937991664919601326587904 : ℝ)) ((22-11)+2*10-6) 0 10 A B))) + (((boundaryTermCoefficient77 ((-1365558175881921806213/11937991664919601326587904 : ℝ)) ((22-11)+2*11-6) 0 11 A B)) + ((boundaryTermCoefficient77 ((636471752928721651/35813974994758803979763712 : ℝ)) ((22-11)+2*12-6) 0 12 A B)))) + ((((boundaryTermCoefficient77 ((-21188485667851309369/483488662429243853726810112 : ℝ)) ((22-11)+2*13-6) 0 13 A B)) + ((boundaryTermCoefficient77 ((12462386243290758229/26108387771179168101247746048 : ℝ)) ((22-11)+2*14-6) 0 14 A B))) + (((boundaryTermCoefficient77 ((-78105652709244055/78325163313537504303743238144 : ℝ)) ((22-11)+2*15-6) 0 15 A B)) + (((boundaryTermCoefficient77 ((26240936749825/78325163313537504303743238144 : ℝ)) ((22-11)+2*16-6) 0 16 A B)) + ((boundaryTermCoefficient77 ((7534594907/1057389704732756308100533714944 : ℝ)) ((22-11)+2*17-6) 0 17 A B)))))))

theorem boundaryReCoefficient77_11_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryReCoefficient77_11 t v=boundaryReHighColumn77_11 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryReCoefficient77_11

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((-360033540581/1594323 : ℝ)) ((22-11)+2*0-6) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((17568454872499/28697814 : ℝ)) ((22-11)+2*1-6) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-920524941361915531/2115832430592 : ℝ)) ((22-11)+2*2-6) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((73496748484323052529/304679870005248 : ℝ)) ((22-11)+2*3-6) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-27429392756818027649/457019805007872 : ℝ)) ((22-11)+2*4-6) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((3978806380121646237391/789730223053602816 : ℝ)) ((22-11)+2*5-6) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((13225175638740216702139/28430288029929701376 : ℝ)) ((22-11)+2*6-6) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-4046844871148757577/29249267520503808 : ℝ)) ((22-11)+2*7-6) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((477167294277387620196913/36845653286788892983296 : ℝ)) ((22-11)+2*8-6) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-206070765128072537541793/331610879581100036849664 : ℝ)) ((22-11)+2*9-6) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((178347676301480892829787/11937991664919601326587904 : ℝ)) ((22-11)+2*10-6) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-1365558175881921806213/11937991664919601326587904 : ℝ)) ((22-11)+2*11-6) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((636471752928721651/35813974994758803979763712 : ℝ)) ((22-11)+2*12-6) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-21188485667851309369/483488662429243853726810112 : ℝ)) ((22-11)+2*13-6) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((12462386243290758229/26108387771179168101247746048 : ℝ)) ((22-11)+2*14-6) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-78105652709244055/78325163313537504303743238144 : ℝ)) ((22-11)+2*15-6) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((26240936749825/78325163313537504303743238144 : ℝ)) ((22-11)+2*16-6) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((7534594907/1057389704732756308100533714944 : ℝ)) ((22-11)+2*17-6) 0 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryReHighColumn77_11]

  ring


def boundaryReCoefficient77_12 (A B : ℕ) : ℝ :=
  ((((((boundaryTermCoefficient77 ((2115896746330/1594323 : ℝ)) ((22-12)+2*0-6) 0 0 A B)) + ((boundaryTermCoefficient77 ((-4887845985995/4782969 : ℝ)) ((22-12)+2*1-6) 0 1 A B))) + (((boundaryTermCoefficient77 ((452481369635861897/470184984576 : ℝ)) ((22-12)+2*2-6) 0 2 A B)) + ((boundaryTermCoefficient77 ((-735812267157759707/3173748645888 : ℝ)) ((22-12)+2*3-6) 0 3 A B)))) + ((((boundaryTermCoefficient77 ((-75435289208493100207/3656158440062976 : ℝ)) ((22-12)+2*4-6) 0 4 A B)) + ((boundaryTermCoefficient77 ((888373109037337581125/49358138940850176 : ℝ)) ((22-12)+2*5-6) 0 5 A B))) + (((boundaryTermCoefficient77 ((-191721690042457850287/55527906308456448 : ℝ)) ((22-12)+2*6-6) 0 6 A B)) + (((boundaryTermCoefficient77 ((1613838269297808138013/4738381338321616896 : ℝ)) ((22-12)+2*7-6) 0 7 A B)) + ((boundaryTermCoefficient77 ((-172121852342837169901975/9211413321697223245824 : ℝ)) ((22-12)+2*8-6) 0 8 A B)))))) + (((((boundaryTermCoefficient77 ((37425770717325900097697/82902719895275009212416 : ℝ)) ((22-12)+2*9-6) 0 9 A B)) + ((boundaryTermCoefficient77 ((38681680767025580551/4605706660848611622912 : ℝ)) ((22-12)+2*10-6) 0 10 A B))) + (((boundaryTermCoefficient77 ((-48847947315614820159353/53720962492138205969645568 : ℝ)) ((22-12)+2*11-6) 0 11 A B)) + ((boundaryTermCoefficient77 ((5853187574794241724079/241744331214621926863405056 : ℝ)) ((22-12)+2*12-6) 0 12 A B)))) + ((((boundaryTermCoefficient77 ((-52898768435336212561/241744331214621926863405056 : ℝ)) ((22-12)+2*13-6) 0 13 A B)) + ((boundaryTermCoefficient77 ((383697734414416087/815887117849349003163992064 : ℝ)) ((22-12)+2*14-6) 0 14 A B))) + (((boundaryTermCoefficient77 ((1236361820156059/4351397961863194683541291008 : ℝ)) ((22-12)+2*15-6) 0 15 A B)) + (((boundaryTermCoefficient77 ((-3132177223889/6527096942794792025311936512 : ℝ)) ((22-12)+2*16-6) 0 16 A B)) + ((boundaryTermCoefficient77 ((-758012507/132173713091594538512566714368 : ℝ)) ((22-12)+2*17-6) 0 17 A B)))))))

theorem boundaryReCoefficient77_12_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryReCoefficient77_12 t v=boundaryReHighColumn77_12 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryReCoefficient77_12

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((2115896746330/1594323 : ℝ)) ((22-12)+2*0-6) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-4887845985995/4782969 : ℝ)) ((22-12)+2*1-6) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((452481369635861897/470184984576 : ℝ)) ((22-12)+2*2-6) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-735812267157759707/3173748645888 : ℝ)) ((22-12)+2*3-6) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-75435289208493100207/3656158440062976 : ℝ)) ((22-12)+2*4-6) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((888373109037337581125/49358138940850176 : ℝ)) ((22-12)+2*5-6) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-191721690042457850287/55527906308456448 : ℝ)) ((22-12)+2*6-6) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((1613838269297808138013/4738381338321616896 : ℝ)) ((22-12)+2*7-6) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-172121852342837169901975/9211413321697223245824 : ℝ)) ((22-12)+2*8-6) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((37425770717325900097697/82902719895275009212416 : ℝ)) ((22-12)+2*9-6) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((38681680767025580551/4605706660848611622912 : ℝ)) ((22-12)+2*10-6) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-48847947315614820159353/53720962492138205969645568 : ℝ)) ((22-12)+2*11-6) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((5853187574794241724079/241744331214621926863405056 : ℝ)) ((22-12)+2*12-6) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-52898768435336212561/241744331214621926863405056 : ℝ)) ((22-12)+2*13-6) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((383697734414416087/815887117849349003163992064 : ℝ)) ((22-12)+2*14-6) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((1236361820156059/4351397961863194683541291008 : ℝ)) ((22-12)+2*15-6) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-3132177223889/6527096942794792025311936512 : ℝ)) ((22-12)+2*16-6) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-758012507/132173713091594538512566714368 : ℝ)) ((22-12)+2*17-6) 0 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryReHighColumn77_12]

  ring


def boundaryReCoefficient77_13 (A B : ℕ) : ℝ :=
  ((((((boundaryTermCoefficient77 ((114719017340/531441 : ℝ)) ((22-13)+2*0-6) 0 0 A B)) + ((boundaryTermCoefficient77 ((3221264502340/1594323 : ℝ)) ((22-13)+2*1-6) 0 1 A B))) + (((boundaryTermCoefficient77 ((-33439209471454373/2115832430592 : ℝ)) ((22-13)+2*2-6) 0 2 A B)) + ((boundaryTermCoefficient77 ((-21222272779248714413/38084983750656 : ℝ)) ((22-13)+2*3-6) 0 3 A B)))) + ((((boundaryTermCoefficient77 ((105788716395505184105/457019805007872 : ℝ)) ((22-13)+2*4-6) 0 4 A B)) + ((boundaryTermCoefficient77 ((-4527507267961596325865/98716277881700352 : ℝ)) ((22-13)+2*5-6) 0 5 A B))) + (((boundaryTermCoefficient77 ((37874640804033095876825/7107572007482425344 : ℝ)) ((22-13)+2*6-6) 0 6 A B)) + (((boundaryTermCoefficient77 ((-1492942879875765628315/3998009254208864256 : ℝ)) ((22-13)+2*7-6) 0 7 A B)) + ((boundaryTermCoefficient77 ((115933709965584087279551/9211413321697223245824 : ℝ)) ((22-13)+2*8-6) 0 8 A B)))))) + (((((boundaryTermCoefficient77 ((24866062742864992766795/82902719895275009212416 : ℝ)) ((22-13)+2*9-6) 0 9 A B)) + ((boundaryTermCoefficient77 ((-40445270447041873837189/746124479057475082911744 : ℝ)) ((22-13)+2*10-6) 0 10 A B))) + (((boundaryTermCoefficient77 ((930892117094983328173/373062239528737541455872 : ℝ)) ((22-13)+2*11-6) 0 11 A B)) + ((boundaryTermCoefficient77 ((-13564531176772919328887/241744331214621926863405056 : ℝ)) ((22-13)+2*12-6) 0 12 A B)))) + ((((boundaryTermCoefficient77 ((1276070651702658008447/2175698980931597341770645504 : ℝ)) ((22-13)+2*13-6) 0 13 A B)) + ((boundaryTermCoefficient77 ((-2496526281237265085/1087849490465798670885322752 : ℝ)) ((22-13)+2*14-6) 0 14 A B))) + (((boundaryTermCoefficient77 ((2787216140415433/1087849490465798670885322752 : ℝ)) ((22-13)+2*15-6) 0 15 A B)) + (((boundaryTermCoefficient77 ((-2022407420621/6527096942794792025311936512 : ℝ)) ((22-13)+2*16-6) 0 16 A B)) + ((boundaryTermCoefficient77 ((-11700680453/176231617455459384683422285824 : ℝ)) ((22-13)+2*17-6) 0 17 A B)))))))

theorem boundaryReCoefficient77_13_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryReCoefficient77_13 t v=boundaryReHighColumn77_13 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryReCoefficient77_13

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((114719017340/531441 : ℝ)) ((22-13)+2*0-6) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((3221264502340/1594323 : ℝ)) ((22-13)+2*1-6) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-33439209471454373/2115832430592 : ℝ)) ((22-13)+2*2-6) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-21222272779248714413/38084983750656 : ℝ)) ((22-13)+2*3-6) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((105788716395505184105/457019805007872 : ℝ)) ((22-13)+2*4-6) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-4527507267961596325865/98716277881700352 : ℝ)) ((22-13)+2*5-6) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((37874640804033095876825/7107572007482425344 : ℝ)) ((22-13)+2*6-6) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-1492942879875765628315/3998009254208864256 : ℝ)) ((22-13)+2*7-6) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((115933709965584087279551/9211413321697223245824 : ℝ)) ((22-13)+2*8-6) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((24866062742864992766795/82902719895275009212416 : ℝ)) ((22-13)+2*9-6) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-40445270447041873837189/746124479057475082911744 : ℝ)) ((22-13)+2*10-6) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((930892117094983328173/373062239528737541455872 : ℝ)) ((22-13)+2*11-6) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-13564531176772919328887/241744331214621926863405056 : ℝ)) ((22-13)+2*12-6) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((1276070651702658008447/2175698980931597341770645504 : ℝ)) ((22-13)+2*13-6) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-2496526281237265085/1087849490465798670885322752 : ℝ)) ((22-13)+2*14-6) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((2787216140415433/1087849490465798670885322752 : ℝ)) ((22-13)+2*15-6) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-2022407420621/6527096942794792025311936512 : ℝ)) ((22-13)+2*16-6) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-11700680453/176231617455459384683422285824 : ℝ)) ((22-13)+2*17-6) 0 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryReHighColumn77_13]

  ring


def boundaryReCoefficient77_14 (A B : ℕ) : ℝ :=
  ((((((boundaryTermCoefficient77 ((5394966086360/1594323 : ℝ)) ((22-14)+2*0-6) 0 0 A B)) + ((boundaryTermCoefficient77 ((39350588681348/14348907 : ℝ)) ((22-14)+2*1-6) 0 1 A B))) + (((boundaryTermCoefficient77 ((-3589142796807723451/1057916215296 : ℝ)) ((22-14)+2*2-6) 0 2 A B)) + ((boundaryTermCoefficient77 ((3321917108806349755/2380311484416 : ℝ)) ((22-14)+2*3-6) 0 3 A B)))) + ((((boundaryTermCoefficient77 ((-217657400230905663265/685529707511808 : ℝ)) ((22-14)+2*4-6) 0 4 A B)) + ((boundaryTermCoefficient77 ((1100265958586151215/24100653779712 : ℝ)) ((22-14)+2*5-6) 0 5 A B))) + (((boundaryTermCoefficient77 ((-15237509241550300368319/3553786003741212672 : ℝ)) ((22-14)+2*6-6) 0 6 A B)) + (((boundaryTermCoefficient77 ((14274429312099492278899/63968148067341828096 : ℝ)) ((22-14)+2*7-6) 0 7 A B)) + ((boundaryTermCoefficient77 ((13675116414641514484481/4605706660848611622912 : ℝ)) ((22-14)+2*8-6) 0 8 A B)))))) + (((((boundaryTermCoefficient77 ((-42489802366065464004667/27634239965091669737472 : ℝ)) ((22-14)+2*9-6) 0 9 A B)) + ((boundaryTermCoefficient77 ((29166773656570587434287/248708159685825027637248 : ℝ)) ((22-14)+2*10-6) 0 10 A B))) + (((boundaryTermCoefficient77 ((-7157306975615495392435/1678780077879318936551424 : ℝ)) ((22-14)+2*11-6) 0 11 A B)) + ((boundaryTermCoefficient77 ((50873455678515303779/629542529204744601206784 : ℝ)) ((22-14)+2*12-6) 0 12 A B)))) + ((((boundaryTermCoefficient77 ((-755264063166663593/944313793807116901810176 : ℝ)) ((22-14)+2*13-6) 0 13 A B)) + ((boundaryTermCoefficient77 ((70721978665527299/20145360934551827238617088 : ℝ)) ((22-14)+2*14-6) 0 14 A B))) + (((boundaryTermCoefficient77 ((-160769608743479/30218041401827740857925632 : ℝ)) ((22-14)+2*15-6) 0 15 A B)) + (((boundaryTermCoefficient77 ((25561885391/15109020700913870428962816 : ℝ)) ((22-14)+2*16-6) 0 16 A B)) + ((boundaryTermCoefficient77 ((72277303/543924745232899335442661376 : ℝ)) ((22-14)+2*17-6) 0 17 A B)))))))

theorem boundaryReCoefficient77_14_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryReCoefficient77_14 t v=boundaryReHighColumn77_14 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryReCoefficient77_14

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((5394966086360/1594323 : ℝ)) ((22-14)+2*0-6) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((39350588681348/14348907 : ℝ)) ((22-14)+2*1-6) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-3589142796807723451/1057916215296 : ℝ)) ((22-14)+2*2-6) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((3321917108806349755/2380311484416 : ℝ)) ((22-14)+2*3-6) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-217657400230905663265/685529707511808 : ℝ)) ((22-14)+2*4-6) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((1100265958586151215/24100653779712 : ℝ)) ((22-14)+2*5-6) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-15237509241550300368319/3553786003741212672 : ℝ)) ((22-14)+2*6-6) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((14274429312099492278899/63968148067341828096 : ℝ)) ((22-14)+2*7-6) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((13675116414641514484481/4605706660848611622912 : ℝ)) ((22-14)+2*8-6) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-42489802366065464004667/27634239965091669737472 : ℝ)) ((22-14)+2*9-6) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((29166773656570587434287/248708159685825027637248 : ℝ)) ((22-14)+2*10-6) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-7157306975615495392435/1678780077879318936551424 : ℝ)) ((22-14)+2*11-6) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((50873455678515303779/629542529204744601206784 : ℝ)) ((22-14)+2*12-6) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-755264063166663593/944313793807116901810176 : ℝ)) ((22-14)+2*13-6) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((70721978665527299/20145360934551827238617088 : ℝ)) ((22-14)+2*14-6) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-160769608743479/30218041401827740857925632 : ℝ)) ((22-14)+2*15-6) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((25561885391/15109020700913870428962816 : ℝ)) ((22-14)+2*16-6) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((72277303/543924745232899335442661376 : ℝ)) ((22-14)+2*17-6) 0 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryReHighColumn77_14]

  ring


def boundaryReCoefficient77_15 (A B : ℕ) : ℝ :=
  ((((((boundaryTermCoefficient77 ((13563919004608/1594323 : ℝ)) ((22-15)+2*0-6) 0 0 A B)) + ((boundaryTermCoefficient77 ((-37984810940960/4782969 : ℝ)) ((22-15)+2*1-6) 0 1 A B))) + (((boundaryTermCoefficient77 ((1955412045322578445/528958107648 : ℝ)) ((22-15)+2*2-6) 0 2 A B)) + ((boundaryTermCoefficient77 ((-835620800934279901/793437161472 : ℝ)) ((22-15)+2*3-6) 0 3 A B)))) + ((((boundaryTermCoefficient77 ((22691434948548053101/114254951251968 : ℝ)) ((22-15)+2*4-6) 0 4 A B)) + ((boundaryTermCoefficient77 ((-52590016560273871169/2056589122535424 : ℝ)) ((22-15)+2*5-6) 0 5 A B))) + (((boundaryTermCoefficient77 ((128301344524369850393/65810851921133568 : ℝ)) ((22-15)+2*6-6) 0 6 A B)) + (((boundaryTermCoefficient77 ((145160439264704640047/10661358011223638016 : ℝ)) ((22-15)+2*7-6) 0 7 A B)) + ((boundaryTermCoefficient77 ((-3072446940346684817225/127936296134683656192 : ℝ)) ((22-15)+2*8-6) 0 8 A B)))))) + (((((boundaryTermCoefficient77 ((119666949353033694298499/41451359947637504606208 : ℝ)) ((22-15)+2*9-6) 0 9 A B)) + ((boundaryTermCoefficient77 ((-21031234662045789362075/124354079842912513818624 : ℝ)) ((22-15)+2*10-6) 0 10 A B))) + (((boundaryTermCoefficient77 ((17522417463260795714321/3357560155758637873102848 : ℝ)) ((22-15)+2*11-6) 0 11 A B)) + ((boundaryTermCoefficient77 ((-69652784203948633385/839390038939659468275712 : ℝ)) ((22-15)+2*12-6) 0 12 A B)))) + ((((boundaryTermCoefficient77 ((7099975357912210705/10072680467275913619308544 : ℝ)) ((22-15)+2*13-6) 0 13 A B)) + ((boundaryTermCoefficient77 ((-30795092088100715/10072680467275913619308544 : ℝ)) ((22-15)+2*14-6) 0 14 A B))) + (((boundaryTermCoefficient77 ((54348775355899/10072680467275913619308544 : ℝ)) ((22-15)+2*15-6) 0 15 A B)) + (((boundaryTermCoefficient77 ((-13358326883/5036340233637956809654272 : ℝ)) ((22-15)+2*16-6) 0 16 A B)) + ((boundaryTermCoefficient77 ((18989215/203971779462337250790998016 : ℝ)) ((22-15)+2*17-6) 0 17 A B)))))))

theorem boundaryReCoefficient77_15_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryReCoefficient77_15 t v=boundaryReHighColumn77_15 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryReCoefficient77_15

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((13563919004608/1594323 : ℝ)) ((22-15)+2*0-6) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-37984810940960/4782969 : ℝ)) ((22-15)+2*1-6) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((1955412045322578445/528958107648 : ℝ)) ((22-15)+2*2-6) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-835620800934279901/793437161472 : ℝ)) ((22-15)+2*3-6) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((22691434948548053101/114254951251968 : ℝ)) ((22-15)+2*4-6) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-52590016560273871169/2056589122535424 : ℝ)) ((22-15)+2*5-6) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((128301344524369850393/65810851921133568 : ℝ)) ((22-15)+2*6-6) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((145160439264704640047/10661358011223638016 : ℝ)) ((22-15)+2*7-6) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-3072446940346684817225/127936296134683656192 : ℝ)) ((22-15)+2*8-6) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((119666949353033694298499/41451359947637504606208 : ℝ)) ((22-15)+2*9-6) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-21031234662045789362075/124354079842912513818624 : ℝ)) ((22-15)+2*10-6) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((17522417463260795714321/3357560155758637873102848 : ℝ)) ((22-15)+2*11-6) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-69652784203948633385/839390038939659468275712 : ℝ)) ((22-15)+2*12-6) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((7099975357912210705/10072680467275913619308544 : ℝ)) ((22-15)+2*13-6) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-30795092088100715/10072680467275913619308544 : ℝ)) ((22-15)+2*14-6) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((54348775355899/10072680467275913619308544 : ℝ)) ((22-15)+2*15-6) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-13358326883/5036340233637956809654272 : ℝ)) ((22-15)+2*16-6) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((18989215/203971779462337250790998016 : ℝ)) ((22-15)+2*17-6) 0 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryReHighColumn77_15]

  ring


def boundaryReCoefficient77_16 (A B : ℕ) : ℝ :=
  ((((((boundaryTermCoefficient77 ((-2280513882496/1594323 : ℝ)) ((22-16)+2*0-6) 0 0 A B)) + ((boundaryTermCoefficient77 ((38642214431872/14348907 : ℝ)) ((22-16)+2*1-6) 0 1 A B))) + (((boundaryTermCoefficient77 ((-5027075167090235/3265173504 : ℝ)) ((22-16)+2*2-6) 0 2 A B)) + ((boundaryTermCoefficient77 ((115014345418774361/264479053824 : ℝ)) ((22-16)+2*3-6) 0 3 A B)))) + ((((boundaryTermCoefficient77 ((-8228038022974059391/114254951251968 : ℝ)) ((22-16)+2*4-6) 0 4 A B)) + ((boundaryTermCoefficient77 ((3164816948286127745/514147280633856 : ℝ)) ((22-16)+2*5-6) 0 5 A B))) + (((boundaryTermCoefficient77 ((118335823536562382989/296148833645101056 : ℝ)) ((22-16)+2*6-6) 0 6 A B)) + (((boundaryTermCoefficient77 ((-204118511716521456295/888446500935303168 : ℝ)) ((22-16)+2*7-6) 0 7 A B)) + ((boundaryTermCoefficient77 ((14217058126033528159781/383808888404050968576 : ℝ)) ((22-16)+2*8-6) 0 8 A B)))))) + (((((boundaryTermCoefficient77 ((-67296295829398153290253/20725679973818752303104 : ℝ)) ((22-16)+2*9-6) 0 9 A B)) + ((boundaryTermCoefficient77 ((60664994436785965393673/373062239528737541455872 : ℝ)) ((22-16)+2*10-6) 0 10 A B))) + (((boundaryTermCoefficient77 ((-4958718258837756564619/1119186718586212624367616 : ℝ)) ((22-16)+2*11-6) 0 11 A B)) + ((boundaryTermCoefficient77 ((16690238053394868131/279796679646553156091904 : ℝ)) ((22-16)+2*12-6) 0 12 A B)))) + ((((boundaryTermCoefficient77 ((-18624987334963153/46632779941092192681984 : ℝ)) ((22-16)+2*13-6) 0 13 A B)) + ((boundaryTermCoefficient77 ((5106683045381761/3357560155758637873102848 : ℝ)) ((22-16)+2*14-6) 0 14 A B))) + (((boundaryTermCoefficient77 ((-10575635694101/3357560155758637873102848 : ℝ)) ((22-16)+2*15-6) 0 15 A B)) + (((boundaryTermCoefficient77 ((13269937105/5036340233637956809654272 : ℝ)) ((22-16)+2*16-6) 0 16 A B)) + ((boundaryTermCoefficient77 ((-4489513/8498824144264052116291584 : ℝ)) ((22-16)+2*17-6) 0 17 A B)))))))

theorem boundaryReCoefficient77_16_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryReCoefficient77_16 t v=boundaryReHighColumn77_16 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryReCoefficient77_16

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((-2280513882496/1594323 : ℝ)) ((22-16)+2*0-6) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((38642214431872/14348907 : ℝ)) ((22-16)+2*1-6) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-5027075167090235/3265173504 : ℝ)) ((22-16)+2*2-6) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((115014345418774361/264479053824 : ℝ)) ((22-16)+2*3-6) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-8228038022974059391/114254951251968 : ℝ)) ((22-16)+2*4-6) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((3164816948286127745/514147280633856 : ℝ)) ((22-16)+2*5-6) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((118335823536562382989/296148833645101056 : ℝ)) ((22-16)+2*6-6) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-204118511716521456295/888446500935303168 : ℝ)) ((22-16)+2*7-6) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((14217058126033528159781/383808888404050968576 : ℝ)) ((22-16)+2*8-6) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-67296295829398153290253/20725679973818752303104 : ℝ)) ((22-16)+2*9-6) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((60664994436785965393673/373062239528737541455872 : ℝ)) ((22-16)+2*10-6) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-4958718258837756564619/1119186718586212624367616 : ℝ)) ((22-16)+2*11-6) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((16690238053394868131/279796679646553156091904 : ℝ)) ((22-16)+2*12-6) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-18624987334963153/46632779941092192681984 : ℝ)) ((22-16)+2*13-6) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((5106683045381761/3357560155758637873102848 : ℝ)) ((22-16)+2*14-6) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-10575635694101/3357560155758637873102848 : ℝ)) ((22-16)+2*15-6) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((13269937105/5036340233637956809654272 : ℝ)) ((22-16)+2*16-6) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-4489513/8498824144264052116291584 : ℝ)) ((22-16)+2*17-6) 0 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryReHighColumn77_16]

  ring


def boundaryReCoefficient77_17 (A B : ℕ) : ℝ :=
  ((((((boundaryTermCoefficient77 ((-1199292895232/531441 : ℝ)) ((22-17)+2*1-6) 0 1 A B)) + ((boundaryTermCoefficient77 ((8944684236155561/14693280768 : ℝ)) ((22-17)+2*2-6) 0 2 A B))) + (((boundaryTermCoefficient77 ((-8683150037025379/264479053824 : ℝ)) ((22-17)+2*3-6) 0 3 A B)) + ((boundaryTermCoefficient77 ((-187436597613540635/9521245937664 : ℝ)) ((22-17)+2*4-6) 0 4 A B)))) + ((((boundaryTermCoefficient77 ((2375754080265139879/342764853755904 : ℝ)) ((22-17)+2*5-6) 0 5 A B)) + ((boundaryTermCoefficient77 ((-12481067345496906211/8226356490141696 : ℝ)) ((22-17)+2*6-6) 0 6 A B))) + (((boundaryTermCoefficient77 ((112471540232634081337/444223250467651584 : ℝ)) ((22-17)+2*7-6) 0 7 A B)) + ((boundaryTermCoefficient77 ((-1903538488994906298383/63968148067341828096 : ℝ)) ((22-17)+2*8-6) 0 8 A B))))) + (((((boundaryTermCoefficient77 ((975245758317349834675/431784999454557339648 : ℝ)) ((22-17)+2*9-6) 0 9 A B)) + ((boundaryTermCoefficient77 ((-2131079243627675191859/20725679973818752303104 : ℝ)) ((22-17)+2*10-6) 0 10 A B))) + (((boundaryTermCoefficient77 ((2456531140649170829/971516248772754014208 : ℝ)) ((22-17)+2*11-6) 0 11 A B)) + ((boundaryTermCoefficient77 ((-323330429893532167/11658194985273048170496 : ℝ)) ((22-17)+2*12-6) 0 12 A B)))) + ((((boundaryTermCoefficient77 ((3650124895641203/34974584955819144511488 : ℝ)) ((22-17)+2*13-6) 0 13 A B)) + ((boundaryTermCoefficient77 ((-872295575383/6908559991272917434368 : ℝ)) ((22-17)+2*14-6) 0 14 A B))) + (((boundaryTermCoefficient77 ((155131275655/279796679646553156091904 : ℝ)) ((22-17)+2*15-6) 0 15 A B)) + (((boundaryTermCoefficient77 ((-604640819/419695019469829734137856 : ℝ)) ((22-17)+2*16-6) 0 16 A B)) + ((boundaryTermCoefficient77 ((13254793/22663531051370805643444224 : ℝ)) ((22-17)+2*17-6) 0 17 A B)))))))

theorem boundaryReCoefficient77_17_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryReCoefficient77_17 t v=boundaryReHighColumn77_17 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryReCoefficient77_17

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((-1199292895232/531441 : ℝ)) ((22-17)+2*1-6) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((8944684236155561/14693280768 : ℝ)) ((22-17)+2*2-6) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-8683150037025379/264479053824 : ℝ)) ((22-17)+2*3-6) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-187436597613540635/9521245937664 : ℝ)) ((22-17)+2*4-6) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((2375754080265139879/342764853755904 : ℝ)) ((22-17)+2*5-6) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-12481067345496906211/8226356490141696 : ℝ)) ((22-17)+2*6-6) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((112471540232634081337/444223250467651584 : ℝ)) ((22-17)+2*7-6) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-1903538488994906298383/63968148067341828096 : ℝ)) ((22-17)+2*8-6) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((975245758317349834675/431784999454557339648 : ℝ)) ((22-17)+2*9-6) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-2131079243627675191859/20725679973818752303104 : ℝ)) ((22-17)+2*10-6) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((2456531140649170829/971516248772754014208 : ℝ)) ((22-17)+2*11-6) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-323330429893532167/11658194985273048170496 : ℝ)) ((22-17)+2*12-6) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((3650124895641203/34974584955819144511488 : ℝ)) ((22-17)+2*13-6) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-872295575383/6908559991272917434368 : ℝ)) ((22-17)+2*14-6) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((155131275655/279796679646553156091904 : ℝ)) ((22-17)+2*15-6) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-604640819/419695019469829734137856 : ℝ)) ((22-17)+2*16-6) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((13254793/22663531051370805643444224 : ℝ)) ((22-17)+2*17-6) 0 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryReHighColumn77_17]

  ring


def boundaryReCoefficient77_18 (A B : ℕ) : ℝ :=
  ((((((boundaryTermCoefficient77 ((-375750311936/531441 : ℝ)) ((22-18)+2*1-6) 0 1 A B)) + ((boundaryTermCoefficient77 ((421183371165691/816293376 : ℝ)) ((22-18)+2*2-6) 0 2 A B))) + (((boundaryTermCoefficient77 ((-8457817153131913/44079842304 : ℝ)) ((22-18)+2*3-6) 0 3 A B)) + ((boundaryTermCoefficient77 ((133891807211385611/3173748645888 : ℝ)) ((22-18)+2*4-6) 0 4 A B)))) + ((((boundaryTermCoefficient77 ((-370690693657613579/57127475625984 : ℝ)) ((22-18)+2*5-6) 0 5 A B)) + ((boundaryTermCoefficient77 ((407819072049208669/457019805007872 : ℝ)) ((22-18)+2*6-6) 0 6 A B))) + (((boundaryTermCoefficient77 ((-35745420741850372343/296148833645101056 : ℝ)) ((22-18)+2*7-6) 0 7 A B)) + ((boundaryTermCoefficient77 ((70229091406890953501/5330679005611819008 : ℝ)) ((22-18)+2*8-6) 0 8 A B))))) + (((((boundaryTermCoefficient77 ((-1098982786589008091093/1151426665212152905728 : ℝ)) ((22-18)+2*9-6) 0 9 A B)) + ((boundaryTermCoefficient77 ((23374696935716413813/575713332606076452864 : ℝ)) ((22-18)+2*10-6) 0 10 A B))) + (((boundaryTermCoefficient77 ((-13337893701029924839/15544259980364064227328 : ℝ)) ((22-18)+2*11-6) 0 11 A B)) + ((boundaryTermCoefficient77 ((152839347767787587/31088519960728128454656 : ℝ)) ((22-18)+2*12-6) 0 12 A B)))) + ((((boundaryTermCoefficient77 ((165153809425039/2914548746318262042624 : ℝ)) ((22-18)+2*13-6) 0 13 A B)) + ((boundaryTermCoefficient77 ((-6559141010815/11658194985273048170496 : ℝ)) ((22-18)+2*14-6) 0 14 A B))) + (((boundaryTermCoefficient77 ((161914001255/139898339823276578045952 : ℝ)) ((22-18)+2*15-6) 0 15 A B)) + (((boundaryTermCoefficient77 ((-31648931/93265559882184385363968 : ℝ)) ((22-18)+2*16-6) 0 16 A B)) + ((boundaryTermCoefficient77 ((-3202801/22663531051370805643444224 : ℝ)) ((22-18)+2*17-6) 0 17 A B)))))))

theorem boundaryReCoefficient77_18_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryReCoefficient77_18 t v=boundaryReHighColumn77_18 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryReCoefficient77_18

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((-375750311936/531441 : ℝ)) ((22-18)+2*1-6) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((421183371165691/816293376 : ℝ)) ((22-18)+2*2-6) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-8457817153131913/44079842304 : ℝ)) ((22-18)+2*3-6) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((133891807211385611/3173748645888 : ℝ)) ((22-18)+2*4-6) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-370690693657613579/57127475625984 : ℝ)) ((22-18)+2*5-6) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((407819072049208669/457019805007872 : ℝ)) ((22-18)+2*6-6) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-35745420741850372343/296148833645101056 : ℝ)) ((22-18)+2*7-6) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((70229091406890953501/5330679005611819008 : ℝ)) ((22-18)+2*8-6) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-1098982786589008091093/1151426665212152905728 : ℝ)) ((22-18)+2*9-6) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((23374696935716413813/575713332606076452864 : ℝ)) ((22-18)+2*10-6) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-13337893701029924839/15544259980364064227328 : ℝ)) ((22-18)+2*11-6) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((152839347767787587/31088519960728128454656 : ℝ)) ((22-18)+2*12-6) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((165153809425039/2914548746318262042624 : ℝ)) ((22-18)+2*13-6) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-6559141010815/11658194985273048170496 : ℝ)) ((22-18)+2*14-6) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((161914001255/139898339823276578045952 : ℝ)) ((22-18)+2*15-6) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-31648931/93265559882184385363968 : ℝ)) ((22-18)+2*16-6) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-3202801/22663531051370805643444224 : ℝ)) ((22-18)+2*17-6) 0 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryReHighColumn77_18]

  ring


def boundaryReCoefficient77_19 (A B : ℕ) : ℝ :=
  ((((((boundaryTermCoefficient77 ((-89727402628717/408146688 : ℝ)) ((22-19)+2*2-6) 0 2 A B)) + ((boundaryTermCoefficient77 ((1048897307666959/14693280768 : ℝ)) ((22-19)+2*3-6) 0 3 A B))) + (((boundaryTermCoefficient77 ((-3295831149082177/264479053824 : ℝ)) ((22-19)+2*4-6) 0 4 A B)) + ((boundaryTermCoefficient77 ((16116813321962179/12694994583552 : ℝ)) ((22-19)+2*5-6) 0 5 A B)))) + ((((boundaryTermCoefficient77 ((-77928912523889347/685529707511808 : ℝ)) ((22-19)+2*6-6) 0 6 A B)) + ((boundaryTermCoefficient77 ((204117221675779999/12339534735212544 : ℝ)) ((22-19)+2*7-6) 0 7 A B))) + (((boundaryTermCoefficient77 ((-52291721529779/24100653779712 : ℝ)) ((22-19)+2*8-6) 0 8 A B)) + ((boundaryTermCoefficient77 ((3847406362216530181/23988055525253185536 : ℝ)) ((22-19)+2*9-6) 0 9 A B))))) + (((((boundaryTermCoefficient77 ((-9326284373807451169/1727139997818229358592 : ℝ)) ((22-19)+2*10-6) 0 10 A B)) + ((boundaryTermCoefficient77 ((24568017717062699/5181419993454688075776 : ℝ)) ((22-19)+2*11-6) 0 11 A B))) + (((boundaryTermCoefficient77 ((22640030757368255/5181419993454688075776 : ℝ)) ((22-19)+2*12-6) 0 12 A B)) + ((boundaryTermCoefficient77 ((-710386886024143/7772129990182032113664 : ℝ)) ((22-19)+2*13-6) 0 13 A B)))) + ((((boundaryTermCoefficient77 ((9758298288875/15544259980364064227328 : ℝ)) ((22-19)+2*14-6) 0 14 A B)) + ((boundaryTermCoefficient77 ((-8144037407/5181419993454688075776 : ℝ)) ((22-19)+2*15-6) 0 15 A B))) + (((boundaryTermCoefficient77 ((180714913/139898339823276578045952 : ℝ)) ((22-19)+2*16-6) 0 16 A B)) + ((boundaryTermCoefficient77 ((-434041/1888627587614233803620352 : ℝ)) ((22-19)+2*17-6) 0 17 A B))))))

theorem boundaryReCoefficient77_19_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryReCoefficient77_19 t v=boundaryReHighColumn77_19 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryReCoefficient77_19

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((-89727402628717/408146688 : ℝ)) ((22-19)+2*2-6) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((1048897307666959/14693280768 : ℝ)) ((22-19)+2*3-6) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-3295831149082177/264479053824 : ℝ)) ((22-19)+2*4-6) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((16116813321962179/12694994583552 : ℝ)) ((22-19)+2*5-6) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-77928912523889347/685529707511808 : ℝ)) ((22-19)+2*6-6) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((204117221675779999/12339534735212544 : ℝ)) ((22-19)+2*7-6) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-52291721529779/24100653779712 : ℝ)) ((22-19)+2*8-6) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((3847406362216530181/23988055525253185536 : ℝ)) ((22-19)+2*9-6) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-9326284373807451169/1727139997818229358592 : ℝ)) ((22-19)+2*10-6) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((24568017717062699/5181419993454688075776 : ℝ)) ((22-19)+2*11-6) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((22640030757368255/5181419993454688075776 : ℝ)) ((22-19)+2*12-6) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-710386886024143/7772129990182032113664 : ℝ)) ((22-19)+2*13-6) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((9758298288875/15544259980364064227328 : ℝ)) ((22-19)+2*14-6) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-8144037407/5181419993454688075776 : ℝ)) ((22-19)+2*15-6) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((180714913/139898339823276578045952 : ℝ)) ((22-19)+2*16-6) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-434041/1888627587614233803620352 : ℝ)) ((22-19)+2*17-6) 0 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryReHighColumn77_19]

  ring


def boundaryReCoefficient77_20 (A B : ℕ) : ℝ :=
  ((((((boundaryTermCoefficient77 ((3556367801657/34012224 : ℝ)) ((22-20)+2*2-6) 0 2 A B)) + ((boundaryTermCoefficient77 ((-14723747455213/612220032 : ℝ)) ((22-20)+2*3-6) 0 3 A B))) + (((boundaryTermCoefficient77 ((319944259319861/176319369216 : ℝ)) ((22-20)+2*4-6) 0 4 A B)) + ((boundaryTermCoefficient77 ((603041593462733/1586874322944 : ℝ)) ((22-20)+2*5-6) 0 5 A B)))) + ((((boundaryTermCoefficient77 ((-1024458717848417/8463329722368 : ℝ)) ((22-20)+2*6-6) 0 6 A B)) + ((boundaryTermCoefficient77 ((33439102748176391/2056589122535424 : ℝ)) ((22-20)+2*7-6) 0 7 A B))) + (((boundaryTermCoefficient77 ((-412963346704651303/296148833645101056 : ℝ)) ((22-20)+2*8-6) 0 8 A B)) + ((boundaryTermCoefficient77 ((356624431433807509/3998009254208864256 : ℝ)) ((22-20)+2*9-6) 0 9 A B))))) + (((((boundaryTermCoefficient77 ((-13692029644271483/2998506940656648192 : ℝ)) ((22-20)+2*10-6) 0 10 A B)) + ((boundaryTermCoefficient77 ((16911220892262683/95952222101012742144 : ℝ)) ((22-20)+2*11-6) 0 11 A B))) + (((boundaryTermCoefficient77 ((-948973981549615/215892499727278669824 : ℝ)) ((22-20)+2*12-6) 0 12 A B)) + ((boundaryTermCoefficient77 ((76506878907493/1295354998363672018944 : ℝ)) ((22-20)+2*13-6) 0 13 A B)))) + ((((boundaryTermCoefficient77 ((-241881063457/647677499181836009472 : ℝ)) ((22-20)+2*14-6) 0 14 A B)) + ((boundaryTermCoefficient77 ((7830818323/7772129990182032113664 : ℝ)) ((22-20)+2*15-6) 0 15 A B))) + (((boundaryTermCoefficient77 ((-1911013/1943032497545508028416 : ℝ)) ((22-20)+2*16-6) 0 16 A B)) + ((boundaryTermCoefficient77 ((11819/52461877433728716767232 : ℝ)) ((22-20)+2*17-6) 0 17 A B))))))

theorem boundaryReCoefficient77_20_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryReCoefficient77_20 t v=boundaryReHighColumn77_20 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryReCoefficient77_20

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((3556367801657/34012224 : ℝ)) ((22-20)+2*2-6) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-14723747455213/612220032 : ℝ)) ((22-20)+2*3-6) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((319944259319861/176319369216 : ℝ)) ((22-20)+2*4-6) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((603041593462733/1586874322944 : ℝ)) ((22-20)+2*5-6) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-1024458717848417/8463329722368 : ℝ)) ((22-20)+2*6-6) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((33439102748176391/2056589122535424 : ℝ)) ((22-20)+2*7-6) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-412963346704651303/296148833645101056 : ℝ)) ((22-20)+2*8-6) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((356624431433807509/3998009254208864256 : ℝ)) ((22-20)+2*9-6) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-13692029644271483/2998506940656648192 : ℝ)) ((22-20)+2*10-6) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((16911220892262683/95952222101012742144 : ℝ)) ((22-20)+2*11-6) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-948973981549615/215892499727278669824 : ℝ)) ((22-20)+2*12-6) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((76506878907493/1295354998363672018944 : ℝ)) ((22-20)+2*13-6) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-241881063457/647677499181836009472 : ℝ)) ((22-20)+2*14-6) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((7830818323/7772129990182032113664 : ℝ)) ((22-20)+2*15-6) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-1911013/1943032497545508028416 : ℝ)) ((22-20)+2*16-6) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((11819/52461877433728716767232 : ℝ)) ((22-20)+2*17-6) 0 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryReHighColumn77_20]

  ring


def boundaryReCoefficient77_21 (A B : ℕ) : ℝ :=
  (((((boundaryTermCoefficient77 ((-52125568405/25509168 : ℝ)) ((22-21)+2*3-6) 0 3 A B)) + (((boundaryTermCoefficient77 ((3541517122583/1836660096 : ℝ)) ((22-21)+2*4-6) 0 4 A B)) + ((boundaryTermCoefficient77 ((-38816024418325/66119763456 : ℝ)) ((22-21)+2*5-6) 0 5 A B)))) + ((((boundaryTermCoefficient77 ((55848590646085/528958107648 : ℝ)) ((22-21)+2*6-6) 0 6 A B)) + ((boundaryTermCoefficient77 ((-544701864665579/42845606719488 : ℝ)) ((22-21)+2*7-6) 0 7 A B))) + (((boundaryTermCoefficient77 ((1662459929233771/1542441841901568 : ℝ)) ((22-21)+2*8-6) 0 8 A B)) + ((boundaryTermCoefficient77 ((-10942077893885723/166583718925369344 : ℝ)) ((22-21)+2*9-6) 0 9 A B))))) + (((((boundaryTermCoefficient77 ((956688408399985/333167437850738688 : ℝ)) ((22-21)+2*10-6) 0 10 A B)) + ((boundaryTermCoefficient77 ((-3146705839806479/35982083287879778304 : ℝ)) ((22-21)+2*11-6) 0 11 A B))) + (((boundaryTermCoefficient77 ((250416060102239/143928333151519113216 : ℝ)) ((22-21)+2*12-6) 0 12 A B)) + ((boundaryTermCoefficient77 ((-8780817403579/431784999454557339648 : ℝ)) ((22-21)+2*13-6) 0 13 A B)))) + ((((boundaryTermCoefficient77 ((79807762975/647677499181836009472 : ℝ)) ((22-21)+2*14-6) 0 14 A B)) + ((boundaryTermCoefficient77 ((-24357643/71964166575759556608 : ℝ)) ((22-21)+2*15-6) 0 15 A B))) + (((boundaryTermCoefficient77 ((446395/1295354998363672018944 : ℝ)) ((22-21)+2*16-6) 0 16 A B)) + ((boundaryTermCoefficient77 ((-8669/104923754867457433534464 : ℝ)) ((22-21)+2*17-6) 0 17 A B))))))

theorem boundaryReCoefficient77_21_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryReCoefficient77_21 t v=boundaryReHighColumn77_21 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryReCoefficient77_21

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((-52125568405/25509168 : ℝ)) ((22-21)+2*3-6) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((3541517122583/1836660096 : ℝ)) ((22-21)+2*4-6) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-38816024418325/66119763456 : ℝ)) ((22-21)+2*5-6) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((55848590646085/528958107648 : ℝ)) ((22-21)+2*6-6) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-544701864665579/42845606719488 : ℝ)) ((22-21)+2*7-6) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((1662459929233771/1542441841901568 : ℝ)) ((22-21)+2*8-6) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-10942077893885723/166583718925369344 : ℝ)) ((22-21)+2*9-6) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((956688408399985/333167437850738688 : ℝ)) ((22-21)+2*10-6) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-3146705839806479/35982083287879778304 : ℝ)) ((22-21)+2*11-6) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((250416060102239/143928333151519113216 : ℝ)) ((22-21)+2*12-6) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-8780817403579/431784999454557339648 : ℝ)) ((22-21)+2*13-6) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((79807762975/647677499181836009472 : ℝ)) ((22-21)+2*14-6) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-24357643/71964166575759556608 : ℝ)) ((22-21)+2*15-6) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((446395/1295354998363672018944 : ℝ)) ((22-21)+2*16-6) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-8669/104923754867457433534464 : ℝ)) ((22-21)+2*17-6) 0 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryReHighColumn77_21]

  ring


def boundaryReCoefficient77_22 (A B : ℕ) : ℝ :=
  (((((boundaryTermCoefficient77 ((1301807104/531441 : ℝ)) ((22-22)+2*3-6) 0 3 A B)) + (((boundaryTermCoefficient77 ((-1303347200/1594323 : ℝ)) ((22-22)+2*4-6) 0 4 A B)) + ((boundaryTermCoefficient77 ((7741010944/43046721 : ℝ)) ((22-22)+2*5-6) 0 5 A B)))) + ((((boundaryTermCoefficient77 ((-2730161975915/99179645184 : ℝ)) ((22-22)+2*6-6) 0 6 A B)) + ((boundaryTermCoefficient77 ((10758161428625/3570467226624 : ℝ)) ((22-22)+2*7-6) 0 7 A B))) + (((boundaryTermCoefficient77 ((-122502146602415/514147280633856 : ℝ)) ((22-22)+2*8-6) 0 8 A B)) + ((boundaryTermCoefficient77 ((31394877020285/2313662762852352 : ℝ)) ((22-22)+2*9-6) 0 9 A B))))) + (((((boundaryTermCoefficient77 ((-1094746213523575/1999004627104432128 : ℝ)) ((22-22)+2*10-6) 0 10 A B)) + ((boundaryTermCoefficient77 ((45506594977039/2998506940656648192 : ℝ)) ((22-22)+2*11-6) 0 11 A B))) + (((boundaryTermCoefficient77 ((-1644097616381/5997013881313296384 : ℝ)) ((22-22)+2*12-6) 0 12 A B)) + ((boundaryTermCoefficient77 ((80437533983/26986562465909833728 : ℝ)) ((22-22)+2*13-6) 0 13 A B)))) + ((((boundaryTermCoefficient77 ((-940876055/53973124931819667456 : ℝ)) ((22-22)+2*14-6) 0 14 A B)) + ((boundaryTermCoefficient77 ((1277153/26986562465909833728 : ℝ)) ((22-22)+2*15-6) 0 15 A B))) + (((boundaryTermCoefficient77 ((-7765/161919374795459002368 : ℝ)) ((22-22)+2*16-6) 0 16 A B)) + ((boundaryTermCoefficient77 ((25/2185911559738696531968 : ℝ)) ((22-22)+2*17-6) 0 17 A B))))))

theorem boundaryReCoefficient77_22_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryReCoefficient77_22 t v=boundaryReHighColumn77_22 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryReCoefficient77_22

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((1301807104/531441 : ℝ)) ((22-22)+2*3-6) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-1303347200/1594323 : ℝ)) ((22-22)+2*4-6) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((7741010944/43046721 : ℝ)) ((22-22)+2*5-6) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-2730161975915/99179645184 : ℝ)) ((22-22)+2*6-6) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((10758161428625/3570467226624 : ℝ)) ((22-22)+2*7-6) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-122502146602415/514147280633856 : ℝ)) ((22-22)+2*8-6) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((31394877020285/2313662762852352 : ℝ)) ((22-22)+2*9-6) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-1094746213523575/1999004627104432128 : ℝ)) ((22-22)+2*10-6) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((45506594977039/2998506940656648192 : ℝ)) ((22-22)+2*11-6) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-1644097616381/5997013881313296384 : ℝ)) ((22-22)+2*12-6) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((80437533983/26986562465909833728 : ℝ)) ((22-22)+2*13-6) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-940876055/53973124931819667456 : ℝ)) ((22-22)+2*14-6) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((1277153/26986562465909833728 : ℝ)) ((22-22)+2*15-6) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-7765/161919374795459002368 : ℝ)) ((22-22)+2*16-6) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((25/2185911559738696531968 : ℝ)) ((22-22)+2*17-6) 0 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryReHighColumn77_22]

  ring


end

end HTGeometry.ThetaRatioInfinity
